use std::collections::{HashMap, HashSet};

use base64::{engine::general_purpose::STANDARD, Engine as _};
use reqwest::{
    header::{CONTENT_LENGTH, CONTENT_TYPE, COOKIE, REFERER, USER_AGENT},
    Url,
};
use std::time::{Duration, Instant};

use chaser_cf::core::BrowserManager;
use chaser_cf::{Cookie, ProxyConfig};
use chaser_oxide::auth::Credentials;
use chaser_oxide::cdp::browser_protocol::dom::{
    GetBoxModelParams, GetDocumentParams, Node, NodeId,
};
use chaser_oxide::cdp::browser_protocol::network;
use chaser_oxide::layout::Point;
use chaser_oxide::{ChaserPage, Page};

use crate::error::{FlareSolverError, Result};
use crate::models::{DownloadedImage, FetchResponse, RequestCookie, ResponseCookie};

#[cfg(feature = "server")]
use crate::session::SessionStore;
#[cfg(feature = "server")]
use std::sync::Arc;

/// Parse "scheme://[user:pass@]host:port" into a chaser_cf ProxyConfig.
pub fn parse_proxy_url(url: &str) -> Result<ProxyConfig> {
    let (scheme, rest) = url.split_once("://").ok_or_else(|| {
        FlareSolverError::Browser("proxy URL must include a scheme (e.g. http://host:port)".into())
    })?;

    let (creds, hostport) = if let Some(at) = rest.rfind('@') {
        (Some(&rest[..at]), &rest[at + 1..])
    } else {
        (None, rest)
    };

    let (host, port_str) = hostport
        .rsplit_once(':')
        .ok_or_else(|| FlareSolverError::Browser("proxy URL missing port".into()))?;
    let port = port_str
        .parse::<u16>()
        .map_err(|_| FlareSolverError::Browser("proxy URL has invalid port".into()))?;

    let mut cfg = ProxyConfig::new(host, port).with_scheme(scheme);
    if let Some(creds) = creds {
        if let Some((user, pass)) = creds.split_once(':') {
            cfg = cfg.with_auth(user, pass);
        }
    }
    Ok(cfg)
}

/// Convert a chaser_cf Cookie into a ResponseCookie.
pub fn chaser_cookie_to_response(c: Cookie) -> ResponseCookie {
    let is_session = c.expires.is_none();
    ResponseCookie {
        name: c.name,
        value: c.value,
        domain: c.domain.unwrap_or_default(),
        path: c.path.unwrap_or_else(|| "/".into()),
        expiry: c.expires,
        http_only: c.http_only.unwrap_or(false),
        secure: c.secure.unwrap_or(false),
        session: is_session,
        same_party: false,
        store_id: "0".into(),
    }
}

/// Map a CDP network cookie (from the live browser) onto a chaser_cf Cookie.
fn oxide_to_chaser_cookie(c: network::Cookie) -> Cookie {
    Cookie {
        name: c.name,
        value: c.value,
        domain: Some(c.domain),
        path: Some(c.path),
        // CDP reports -1 for "no expiry" (a session cookie); chaser_cf uses None.
        expires: if c.expires < 0.0 {
            None
        } else {
            Some(c.expires)
        },
        http_only: Some(c.http_only),
        secure: Some(c.secure),
        same_site: c.same_site.map(|s| format!("{s:?}")),
    }
}

pub const DEFAULT_UA: &str = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 \
     (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

/// Init script that makes `navigator.languages` consistent between the main
/// thread and Web Workers.
///
/// chaser-oxide's native profile applies a CDP `setUserAgentOverride` with
/// `accept_language` (e.g. `"en-US"`), which collapses the **main** thread's
/// `navigator.languages` to a single entry (`["en-US"]`). That override does
/// **not** reach worker contexts, where `navigator.languages` keeps Chrome's
/// natural expansion (`["en-US","en"]`). Fingerprint WAFs spawn a worker and
/// compare its `navigator` against the page's; the mismatch
/// (`hasInconsistentWorkerValues`) was the lone signal labelling the stealth
/// browser "a bot" on deviceandbrowserinfo.com.
///
/// We fix it on the **main thread only**: redefine `navigator.languages` to the
/// natural `[lang, base]` expansion the workers already report, so both sides
/// agree without touching any worker.
///
/// An earlier version wrapped `Worker` to inject the values into each worker via
/// a `blob:` script + `importScripts`. That broke WAF bypass: Cloudflare and
/// Turnstile challenge pages forbid `blob:` workers through a `worker-src` CSP,
/// so the wrapped worker was blocked and their proof-of-work never ran — the
/// challenges silently failed to solve. The main-thread override avoids all
/// worker tampering and so cannot break challenge pages.
const LANGUAGES_CONSISTENCY_JS: &str = r#"(function () {
  try {
    var lang = navigator.language || 'en-US';
    var base = lang.indexOf('-') > 0 ? lang.split('-')[0] : lang;
    var list = base === lang ? [lang] : [lang, base];
    Object.defineProperty(Navigator.prototype, 'languages', {
      get: function () { return list.slice(); },
      configurable: true
    });
  } catch (e) {}
})();"#;

/// Return true if a page title looks like a bot/WAF interstitial (Cloudflare,
/// PerimeterX, generic "access denied", etc.) rather than real content.
pub fn is_challenge_title(title: &str) -> bool {
    let t = title.to_ascii_lowercase();
    const MARKERS: [&str; 10] = [
        "just a moment",
        "attention required",
        "checking your browser",
        "are you a robot",
        "verifying you are human",
        "please wait",
        "access denied",
        "ddos",
        "one moment",
        "security check",
    ];
    MARKERS.iter().any(|m| t.contains(m))
}

/// Extract the trimmed `<title>` text from an HTML body, if present.
pub fn html_title(body: &str) -> Option<String> {
    let lower = body.to_ascii_lowercase();
    let open = lower.find("<title")?;
    let gt = lower[open..].find('>')? + open + 1;
    let end = lower[gt..].find("</title>")? + gt;
    Some(body[gt..end].trim().to_string())
}

/// True when a captured page body still looks like a WAF challenge (by its title).
/// Used to retry on a fresh context: the interstitial can clear on a new attempt
/// (new browser context, and a rotating proxy usually hands out a fresh exit IP).
pub fn body_is_challenge(body: &str) -> bool {
    html_title(body)
        .as_deref()
        .map(is_challenge_title)
        .unwrap_or(false)
}

/// True when a navigation error matches the proxy/auth failures a *cold* first
/// proxied request can produce: the initial proxied CONNECT can race ahead of
/// the CDP Fetch auth-interception that `authenticate()` enables, so Chrome
/// answers the proxy 407 with no credentials and the tunnel fails. These clear
/// on a second attempt (the handler is live by then), so [`fetch`] retries once.
pub fn is_proxy_retryable_error(msg: &str) -> bool {
    let m = msg.to_ascii_uppercase();
    [
        "ERR_TUNNEL_CONNECTION_FAILED",
        "ERR_PROXY_CONNECTION_FAILED",
        "ERR_INVALID_AUTH_CREDENTIALS",
        "ERR_PROXY_AUTH_REQUESTED",
        "ERR_NO_SUPPORTED_PROXIES",
    ]
    .iter()
    .any(|needle| m.contains(needle))
}

/// True for a transient proxy/network error worth retrying on a fresh context
/// (a flaky proxy drops/times out individual connections). Stable failures (DNS,
/// bad target) are excluded so they fail fast.
pub fn is_transient_fetch_error(msg: &str) -> bool {
    let m = msg.to_ascii_uppercase();
    [
        "ERR_EMPTY_RESPONSE",
        "ERR_CONNECTION_RESET",
        "ERR_CONNECTION_CLOSED",
        "ERR_CONNECTION_ABORTED",
        "ERR_CONNECTION_FAILED",
        "ERR_CONNECTION_TIMED_OUT",
        "ERR_TIMED_OUT",
        "ERR_TUNNEL_CONNECTION_FAILED",
        "ERR_PROXY_CONNECTION_FAILED",
        "ERR_INVALID_AUTH_CREDENTIALS",
        "ERR_PROXY_AUTH_REQUESTED",
        "ERR_NO_SUPPORTED_PROXIES",
        "ERR_SOCKS_CONNECTION_FAILED",
        "ERR_HTTP2_PROTOCOL_ERROR",
        "ERR_NETWORK_CHANGED",
        "ERR_ABORTED",
        "REQUEST TIMED OUT",
    ]
    .iter()
    .any(|needle| m.contains(needle))
}

/// Snapshot of the live page used to decide when a fetch has settled.
struct PageState {
    /// `document.readyState === 'complete'`.
    ready: bool,
    /// Page currently looks like a WAF challenge (by title or visible widget).
    challenge: bool,
    /// An interactive Cloudflare Turnstile widget is present.
    turnstile: bool,
    /// Milliseconds since the most recent network resource finished loading
    /// (large when nothing is in flight) — our network-idle signal.
    idle_ms: u64,
    /// Length of the serialized DOM; used to detect when rendering has stopped.
    dom_len: u64,
}

/// JS reporting raw page signals. Detection logic lives in Rust
/// ([`is_challenge_title`], [`page_settled`]) so it stays in one place and is
/// unit-testable. `idleMs` comes from the Resource Timing buffer (time since the
/// last resource's `responseEnd`); `domLen` is the serialized DOM length.
const PAGE_STATE_JS: &str = r#"(() => {
  const res = performance.getEntriesByType('resource');
  let last = 0;
  for (let i = 0; i < res.length; i++) { const e = res[i].responseEnd; if (e > last) last = e; }
  const de = document.documentElement;
  return {
    ready: document.readyState === 'complete',
    title: document.title || '',
    turnstile: !!document.querySelector('[name="cf-turnstile-response"], iframe[src*="challenges.cloudflare.com"], div.cf-turnstile'),
    px: !!document.querySelector('#px-captcha, [id^="px-captcha"], .px-captcha, #px-block'),
    idleMs: Math.round(performance.now() - last),
    domLen: de ? de.innerHTML.length : 0
  };
})()"#;

/// Read a non-negative integer field from a JS-returned object (numbers may come
/// back as floats).
fn json_u64(o: &serde_json::Value, key: &str) -> u64 {
    o.get(key)
        .and_then(|x| x.as_f64())
        .map(|f| f.max(0.0) as u64)
        .unwrap_or(0)
}

async fn read_page_state(chaser: &ChaserPage) -> PageState {
    let v = chaser.evaluate(PAGE_STATE_JS).await.ok().flatten();
    match v {
        Some(o) => {
            let title = o.get("title").and_then(|x| x.as_str()).unwrap_or("");
            let turnstile = o
                .get("turnstile")
                .and_then(|x| x.as_bool())
                .unwrap_or(false);
            let px = o.get("px").and_then(|x| x.as_bool()).unwrap_or(false);
            PageState {
                ready: o.get("ready").and_then(|x| x.as_bool()).unwrap_or(false),
                challenge: is_challenge_title(title) || turnstile || px,
                turnstile,
                idle_ms: json_u64(&o, "idleMs"),
                dom_len: json_u64(&o, "domLen"),
            }
        }
        None => PageState {
            ready: false,
            challenge: false,
            turnstile: false,
            idle_ms: 0,
            dom_len: 0,
        },
    }
}

/// Return true if the browser holds a `cf_clearance` cookie (CF challenge solved).
async fn has_clearance_cookie(page: &Page) -> bool {
    page.get_cookies()
        .await
        .map(|cs| cs.iter().any(|c| c.name == "cf_clearance"))
        .unwrap_or(false)
}

// ── settle thresholds ────────────────────────────────────────────────────────
/// No network resource has finished loading for this long ⇒ the network is idle.
const NET_IDLE_MS: u64 = 500;
/// Once the network is idle, the DOM must also be unchanged for this long.
const SETTLE_QUIET: Duration = Duration::from_millis(600);
/// Safety valve: settle when the DOM has been quiet this long even if the network
/// never goes idle (pages with persistent analytics / polling connections).
const MAX_QUIET: Duration = Duration::from_millis(2_500);

/// Decide whether a non-challenge page has rendered enough to capture.
///
/// `network_idle` — no network resource finished within [`NET_IDLE_MS`].
/// `quiet` — how long the serialized DOM has been unchanged.
///
/// Settles when the page is `ready`, not a challenge, and either the network is
/// idle with a brief DOM-quiet confirmation, or the DOM has been quiet long enough
/// on its own — which bounds the wait on pages whose network never goes idle.
pub fn page_settled(ready: bool, challenge: bool, network_idle: bool, quiet: Duration) -> bool {
    if !ready || challenge {
        return false;
    }
    (network_idle && quiet >= SETTLE_QUIET) || quiet >= MAX_QUIET
}

/// Wait (up to `max`) until the page settles on real content — `readyState=complete`,
/// not a challenge, network-idle with a stable DOM ([`page_settled`]) — so post-load
/// JS finishes before capture.
///
/// Cloudflare sets `cf_clearance` *before* reloading the interstitial to the real
/// page, so we don't capture on the cookie; it only bounds the post-clearance wait
/// ([`POST_CLEARANCE_MAX`]). Turnstile widgets are clicked only after a passive
/// window — clicking too early raises the bot score.
async fn solve_and_wait(page: &Page, chaser: &ChaserPage, max: Duration) {
    const PASSIVE_WAIT: Duration = Duration::from_millis(6_000);
    const CLICK_INTERVAL: Duration = Duration::from_millis(1_200);
    const POLL: Duration = Duration::from_millis(400);
    /// After `cf_clearance` appears, how long to wait for CF's reload-to-real-page
    /// before returning best-effort (covers slow proxied reloads).
    const POST_CLEARANCE_MAX: Duration = Duration::from_millis(10_000);

    let start = Instant::now();
    let mut last_click: Option<Instant> = None;
    let mut prev_dom: Option<u64> = None;
    let mut last_dom_change = start;
    let mut clearance_at: Option<Instant> = None;

    loop {
        if start.elapsed() >= max {
            return;
        }

        let st = read_page_state(chaser).await;

        if prev_dom != Some(st.dom_len) {
            prev_dom = Some(st.dom_len);
            last_dom_change = Instant::now();
        }

        // Note first cf_clearance; capture still waits for real content (below).
        if clearance_at.is_none() && has_clearance_cookie(page).await {
            clearance_at = Some(Instant::now());
            tracing::info!("cf_clearance obtained; waiting for the real page");
        }

        if page_settled(
            st.ready,
            st.challenge,
            st.idle_ms >= NET_IDLE_MS,
            last_dom_change.elapsed(),
        ) {
            return;
        }

        // Cleared but never settled within the window — return best-effort.
        if clearance_at.is_some_and(|t| t.elapsed() >= POST_CLEARANCE_MAX) {
            return;
        }

        if st.turnstile
            && start.elapsed() >= PASSIVE_WAIT
            && last_click.is_none_or(|t| t.elapsed() >= CLICK_INTERVAL)
        {
            tracing::info!("clicking Turnstile challenge widget");
            try_click_challenge(page).await;
            last_click = Some(Instant::now());
        }

        tokio::time::sleep(POLL).await;
    }
}

/// Full fetch attempts (initial + retries) on a transient proxy/network error.
const MAX_FETCH_ATTEMPTS: u32 = 3;
/// Only retry if at least this much timeout budget remains for a fresh attempt.
const MIN_RETRY_BUDGET: Duration = Duration::from_millis(20_000);

/// Drive a fetch through the browser, retrying transient proxy/network failures on
/// a fresh context (a flaky proxy's per-connection drops usually clear on retry).
/// Bounded by [`MAX_FETCH_ATTEMPTS`] and the remaining timeout budget, so a slow
/// challenge is never retried.
pub async fn fetch(
    browser: &BrowserManager,
    url: &str,
    is_post: bool,
    post_data: Option<&str>,
    proxy_url: Option<&str>,
    extra_cookies: &[RequestCookie],
    max_timeout_ms: u64,
) -> Result<FetchResponse> {
    fetch_with_download(
        browser, url, is_post, post_data, proxy_url,
        extra_cookies, max_timeout_ms, false,
    )
    .await
}

/// Like `fetch`, but optionally downloads rendered page <img> resources.
#[allow(clippy::too_many_arguments)]
pub async fn fetch_with_download(
    browser: &BrowserManager,
    url: &str,
    is_post: bool,
    post_data: Option<&str>,
    proxy_url: Option<&str>,
    extra_cookies: &[RequestCookie],
    max_timeout_ms: u64,
    download: bool,
) -> Result<FetchResponse> {
    let started = Instant::now();
    let deadline = started + Duration::from_millis(max_timeout_ms);
    let mut attempt = 0u32;
    loop {
        attempt += 1;
        let remaining = deadline.saturating_duration_since(Instant::now());
        match fetch_once(
            browser, url, is_post, post_data, proxy_url, extra_cookies, remaining, download,
        )
        .await
        {
            Ok(r) => {
                // A GET that came back still showing a challenge (e.g. an interactive
                // Turnstile that didn't resolve on a flagged proxy exit) is worth a
                // fresh attempt — a new context/exit usually draws an easier challenge.
                let budget_left = deadline.saturating_duration_since(Instant::now());
                if !is_post
                    && attempt < MAX_FETCH_ATTEMPTS
                    && budget_left >= MIN_RETRY_BUDGET
                    && body_is_challenge(&r.body)
                {
                    tracing::warn!(
                        "challenge still present after solve on attempt {attempt}, retrying on a fresh context"
                    );
                    continue;
                }
                tracing::info!(
                    "fetched {url} — {} bytes, {} cookies, attempt {attempt}, {}ms",
                    r.body.len(),
                    r.cookies.len(),
                    started.elapsed().as_millis()
                );
                return Ok(r);
            }
            Err(e) => {
                let budget_left = deadline.saturating_duration_since(Instant::now());
                if attempt < MAX_FETCH_ATTEMPTS
                    && budget_left >= MIN_RETRY_BUDGET
                    && is_transient_fetch_error(&e.to_string())
                {
                    tracing::warn!("transient fetch error on attempt {attempt}, retrying: {e}");
                    continue;
                }
                return Err(e);
            }
        }
    }
}

/// One full fetch attempt: navigate, solve any challenge, and return the rendered
/// DOM (GET) or an in-page POST response — all from the one stealth session that
/// passed the WAF. `max` bounds the settle/solve wait (the remaining timeout budget).
#[allow(clippy::too_many_arguments)]
async fn fetch_once(
    browser: &BrowserManager,
    url: &str,
    is_post: bool,
    post_data: Option<&str>,
    proxy_url: Option<&str>,
    extra_cookies: &[RequestCookie],
    max: Duration,
    download: bool,
) -> Result<FetchResponse> {
    let fetch_started = Instant::now();
    let proxy = proxy_url
        .filter(|p| !p.is_empty())
        .map(parse_proxy_url)
        .transpose()?;

    // Bound concurrent contexts; incognito context per proxied request, shared
    // default context otherwise (lets cf_clearance carry across requests).
    let _permit = browser
        .acquire_permit()
        .await
        .map_err(FlareSolverError::from)?;
    let ctx_id = browser
        .create_context(proxy.as_ref())
        .await
        .map_err(FlareSolverError::from)?;

    // Blank page first (applies the stealth profile), set proxy auth, then navigate.
    let (page, chaser) = browser
        .new_page(ctx_id, "about:blank")
        .await
        .map_err(FlareSolverError::from)?;

    // Align navigator.languages between the main thread and workers (best-effort,
    // main-thread only). Registered now, before navigation, so it runs on the
    // target document.
    let _ = page.add_init_script(LANGUAGES_CONSISTENCY_JS).await;

    if let Some(p) = &proxy {
        if let (Some(user), Some(pass)) = (&p.username, &p.password) {
            if let Err(e) = page
                .authenticate(Credentials {
                    username: user.clone(),
                    password: pass.clone(),
                })
                .await
            {
                let _ = page.close().await;
                return Err(FlareSolverError::Browser(format!("proxy auth: {e}")));
            }
        }
    }

    // First proxied CONNECT can race ahead of the CDP Fetch auth handler set up
    // above (ERR_TUNNEL_CONNECTION_FAILED / ERR_INVALID_AUTH_CREDENTIALS); retry
    // the navigation once for authenticated proxies.
    let proxy_auth = proxy
        .as_ref()
        .is_some_and(|p| p.username.is_some() && p.password.is_some());
    let mut goto_res = chaser.goto(url).await;
    if proxy_auth
        && goto_res
            .as_ref()
            .err()
            .is_some_and(|e| is_proxy_retryable_error(&e.to_string()))
    {
        goto_res = chaser.goto(url).await;
    }
    if let Err(e) = goto_res {
        let _ = page.close().await;
        return Err(FlareSolverError::Browser(e.to_string()));
    }

    // Seed caller-supplied cookies for this origin before settling.
    for c in extra_cookies {
        let pair = format!("{}={}", c.name, c.value);
        let js = format!("document.cookie = {}", serde_json::Value::from(pair));
        let _ = chaser.evaluate(&js).await;
    }

    solve_and_wait(&page, &chaser, max).await;

    let user_agent = chaser
        .evaluate("navigator.userAgent")
        .await
        .ok()
        .flatten()
        .and_then(|v| v.as_str().map(str::to_owned))
        .unwrap_or_else(|| DEFAULT_UA.to_string());

    let body = if is_post {
        match in_page_post(&chaser, url, post_data.unwrap_or("")).await {
            Ok(b) => b,
            Err(e) => {
                let _ = page.close().await;
                return Err(e);
            }
        }
    } else {
        match page.content().await {
            Ok(b) => b,
            Err(e) => {
                let _ = page.close().await;
                return Err(FlareSolverError::Browser(e.to_string()));
            }
        }
    };

    let final_url = chaser
        .url()
        .await
        .ok()
        .flatten()
        .unwrap_or_else(|| url.to_string());

    let cookies: Vec<ResponseCookie> = page
        .get_cookies()
        .await
        .unwrap_or_default()
        .into_iter()
        .map(|c| chaser_cookie_to_response(oxide_to_chaser_cookie(c)))
        .collect();

    // Preserve the Python customization: with download=true, retrieve each <img>
    // using a separate HTTP client, passing the page URL as Referer and applicable
    // browser cookies. The browser remains open until image URLs are collected.
    // The image fetches are bounded by the remaining request timeout.
    let downloaded = if download {
        let budget = max.saturating_sub(fetch_started.elapsed());
        let imgs = if budget.is_zero() {
            tracing::warn!("image download skipped: request timeout budget exhausted");
            Vec::new()
        } else {
            download_page_images(&chaser, &final_url, &cookies, &user_agent, proxy_url, budget)
                .await
        };
        tracing::info!("downloaded {} images from {final_url}", imgs.len());
        Some(imgs)
    } else {
        None
    };

    let _ = page.close().await;

    // Selenium/CDP doesn't surface the raw HTTP status or headers for a navigation;
    // like FlareSolverr-py we report 200 + empty headers and put the truth in `body`.
    Ok(FetchResponse {
        url: final_url,
        status: 200,
        headers: HashMap::new(),
        body,
        cookies,
        user_agent,
        download: downloaded,
    })
}


// ── Optional image download support (compatible with the customized Python API) ──
// Return at most 100 images to avoid unbounded API responses. Up to 8 MiB per
// image and 32 MiB of decoded bytes total (Base64 increases the JSON payload).
const MAX_IMAGES: usize = 100;
const MAX_IMAGE_BYTES: usize = 8 * 1024 * 1024;
const MAX_TOTAL_IMAGE_BYTES: usize = 32 * 1024 * 1024;

/// Enumerate <img> sources in the rendered document and fetch their bytes.
/// Like the original Python customization, these are **separate HTTP requests**;
/// browser challenge clearance is not guaranteed to work for every image host.
async fn download_page_images(
    chaser: &ChaserPage,
    page_url: &str,
    cookies: &[ResponseCookie],
    user_agent: &str,
    proxy_url: Option<&str>,
    budget: Duration,
) -> Vec<DownloadedImage> {
    let deadline = Instant::now() + budget;
    let mut builder = reqwest::Client::builder()
        .timeout(Duration::from_secs(10))
        .redirect(reqwest::redirect::Policy::limited(5));

    if let Some(url) = proxy_url.filter(|p| !p.is_empty()) {
        match reqwest::Proxy::all(url) {
            Ok(proxy) => builder = builder.proxy(proxy),
            Err(e) => {
                tracing::warn!("invalid image downloader proxy: {e}");
                return Vec::new();
            }
        }
    }

    let client = match builder.build() {
        Ok(client) => client,
        Err(e) => {
            tracing::warn!("image HTTP client could not be initialized: {e}");
            return Vec::new();
        }
    };

    // currentSrc handles srcset/picture; falling back to src matches Python.
    const IMAGE_SOURCES_JS: &str = r#"Array.from(document.images, img =>
        img.currentSrc || img.getAttribute('src') || img.getAttribute('data-src') || ''
    )"#;
    let sources = match tokio::time::timeout(
        deadline.saturating_duration_since(Instant::now()),
        chaser.evaluate(IMAGE_SOURCES_JS),
    )
    .await
    {
        Ok(Ok(Some(v))) => v,
        Ok(Ok(None)) => {
            tracing::warn!("page image enumeration returned no value");
            return Vec::new();
        }
        Ok(Err(e)) => {
            tracing::warn!("page image enumeration failed: {e}");
            return Vec::new();
        }
        Err(_) => {
            tracing::warn!("page image enumeration timed out");
            return Vec::new();
        }
    };
    let Some(items) = sources.as_array() else {
        tracing::warn!("page image enumeration did not return an array");
        return Vec::new();
    };
    let Ok(base_url) = Url::parse(page_url) else {
        tracing::warn!("cannot parse page URL for image downloads");
        return Vec::new();
    };

    let mut unique = HashSet::new();
    let mut results = Vec::new();
    let mut total_bytes: usize = 0;

    for value in items {
        let Some(src) = value.as_str().filter(|s| !s.is_empty()) else {
            continue;
        };
        let Ok(image_url) = base_url.join(src) else {
            continue;
        };
        if !matches!(image_url.scheme(), "http" | "https") {
            continue;
        }
        if !unique.insert(image_url.as_str().to_owned()) {
            continue;
        }
        if unique.len() > MAX_IMAGES || total_bytes >= MAX_TOTAL_IMAGE_BYTES {
            break;
        }

        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            tracing::warn!("image download time budget reached; returning partial results");
            break;
        }
        match tokio::time::timeout(
            remaining,
            download_one_image(&client, &image_url, page_url, cookies, user_agent),
        )
        .await
        {
            Ok(Some((image, byte_len))) => {
                if total_bytes + byte_len > MAX_TOTAL_IMAGE_BYTES {
                    tracing::warn!("image download total-size limit reached");
                    break;
                }
                total_bytes += byte_len;
                results.push(image);
            }
            Ok(None) => {} // Individual image failed; try the next one.
            Err(_) => {
                tracing::warn!("image download time budget reached; returning partial results");
                break;
            }
        }
    }
    results
}

/// Build a domain/path/HTTPS-scoped Cookie header so cookies from the page are
/// not sent indiscriminately to arbitrary third-party image hosts.
fn image_cookie_header(url: &Url, cookies: &[ResponseCookie]) -> String {
    let host = url.host_str().unwrap_or_default().to_ascii_lowercase();
    let path = url.path();
    cookies
        .iter()
        .filter(|c| {
            if c.secure && url.scheme() != "https" {
                return false;
            }
            if !path.starts_with(&c.path) {
                return false;
            }
            let domain = c.domain.to_ascii_lowercase();
            if let Some(suffix) = domain.strip_prefix('.') {
                host == suffix || host.ends_with(&format!(".{suffix}"))
            } else {
                !domain.is_empty() && host == domain
            }
        })
        .map(|c| format!("{}={}", c.name, c.value))
        .collect::<Vec<_>>()
        .join("; ")
}

async fn download_one_image(
    client: &reqwest::Client,
    image_url: &Url,
    page_url: &str,
    cookies: &[ResponseCookie],
    user_agent: &str,
) -> Option<(DownloadedImage, usize)> {
    let mut request = client
        .get(image_url.clone())
        .header(USER_AGENT, user_agent)
        .header(REFERER, page_url);

    let cookie_header = image_cookie_header(image_url, cookies);
    if !cookie_header.is_empty() {
        request = request.header(COOKIE, cookie_header);
    }

    let mut response = match request.send().await {
        Ok(r) => r,
        Err(e) => {
            tracing::warn!("image request failed for {image_url}: {e}");
            return None;
        }
    };
    if response.status() != reqwest::StatusCode::OK {
        tracing::debug!("image HTTP status {} for {image_url}", response.status());
        return None;
    }

    let mime_type = response
        .headers()
        .get(CONTENT_TYPE)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("application/octet-stream")
        .to_string();
    if !mime_type.to_ascii_lowercase().starts_with("image/") {
        tracing::debug!("image URL returned non-image content-type {mime_type}: {image_url}");
        return None;
    }

    if response
        .headers()
        .get(CONTENT_LENGTH)
        .and_then(|h| h.to_str().ok())
        .and_then(|s| s.parse::<usize>().ok())
        .is_some_and(|n| n > MAX_IMAGE_BYTES)
    {
        tracing::debug!("image too large: {image_url}");
        return None;
    }

    let mut data = Vec::new();
    loop {
        let chunk = match response.chunk().await {
            Ok(chunk) => chunk,
            Err(e) => {
                tracing::warn!("error reading image body {image_url}: {e}");
                return None;
            }
        };
        let Some(chunk) = chunk else { break };
        if data.len() + chunk.len() > MAX_IMAGE_BYTES {
            tracing::debug!("image exceeds size cap: {image_url}");
            return None;
        }
        data.extend_from_slice(&chunk);
    }
    if data.is_empty() {
        return None;
    }

    let filename = image_url
        .path_segments()
        .and_then(|segments| segments.last())
        .filter(|name| !name.is_empty())
        .unwrap_or("image")
        .to_string();
    let size = data.len();
    Some((
        DownloadedImage {
            url: image_url.to_string(),
            filename,
            mime_type,
            encoded_data: STANDARD.encode(data),
        },
        size,
    ))
}

/// POST from the page's own JS context — same cookies, origin, and TLS/fingerprint
/// as the navigation that cleared the WAF.
async fn in_page_post(chaser: &ChaserPage, url: &str, body: &str) -> Result<String> {
    let script = format!(
        "(async () => {{ const r = await fetch({}, {{ method: 'POST', \
         headers: {{ 'Content-Type': 'application/x-www-form-urlencoded' }}, \
         body: {}, credentials: 'include' }}); return await r.text(); }})()",
        serde_json::Value::from(url),
        serde_json::Value::from(body),
    );
    chaser
        .evaluate(&script)
        .await
        .map_err(|e| FlareSolverError::Browser(e.to_string()))?
        .and_then(|v| v.as_str().map(str::to_owned))
        .ok_or_else(|| FlareSolverError::Browser("POST returned no body".into()))
}

/// Click the Turnstile challenge element by traversing its closed shadow root via CDP.
///
/// Cloudflare's Turnstile widget lives inside a CLOSED shadow root invisible to JS;
/// CDP's `DOM.getDocument` with `pierce: true` exposes it. We move the mouse along a
/// human-like Bezier curve before clicking to avoid trivial bot detection. Adapted
/// from chaser-cf's internal solver (not exposed in its public API).
async fn try_click_challenge(page: &Page) {
    let doc = match page
        .execute(GetDocumentParams {
            depth: Some(-1),
            pierce: Some(true),
        })
        .await
    {
        Ok(r) => r,
        Err(_) => return,
    };

    let Some(target_id) = find_shadow_challenge_node(&doc.result.root) else {
        return;
    };

    let box_model = match page
        .execute(GetBoxModelParams {
            node_id: Some(target_id),
            backend_node_id: None,
            object_id: None,
        })
        .await
    {
        Ok(r) => r,
        Err(_) => return,
    };

    let content = box_model.result.model.content.inner();
    if content.len() < 8 {
        return;
    }

    let cx = (content[0] + content[2]) / 2.0;
    let cy = (content[1] + content[5]) / 2.0;

    // Compute all random values in a synchronous block so ThreadRng (which is !Send)
    // is dropped before any await point.
    let (tx, ty, curve_points, post_pause_ms) = {
        use rand::Rng as _;
        let mut rng = rand::rng();

        let tx = cx + rng.random_range(-5.0..=5.0_f64);
        let ty = cy + rng.random_range(-4.0..=4.0_f64);

        let p0x = tx + rng.random_range(-200.0..=-60.0_f64);
        let p0y = ty + rng.random_range(-120.0..=120.0_f64);
        let p1x = p0x + (tx - p0x) * rng.random_range(0.2..0.5_f64) + rng.random_range(-30.0..30.0);
        let p1y = p0y + (ty - p0y) * rng.random_range(0.1..0.4_f64) + rng.random_range(-40.0..40.0);
        let p2x = p0x + (tx - p0x) * rng.random_range(0.5..0.8_f64) + rng.random_range(-20.0..20.0);
        let p2y = p0y + (ty - p0y) * rng.random_range(0.5..0.9_f64) + rng.random_range(-20.0..20.0);

        let steps: u8 = rng.random_range(12..22);
        let mut points: Vec<(f64, f64, u64)> = Vec::with_capacity(steps as usize);
        for i in 1..=steps {
            let t = i as f64 / steps as f64;
            let u = 1.0 - t;
            let bx =
                u * u * u * p0x + 3.0 * u * u * t * p1x + 3.0 * u * t * t * p2x + t * t * t * tx;
            let by =
                u * u * u * p0y + 3.0 * u * u * t * p1y + 3.0 * u * t * t * p2y + t * t * t * ty;
            let speed = (4.0 * t * (1.0 - t)).max(0.1);
            let step_ms = (rng.random_range(8.0..22.0_f64) / speed) as u64;
            points.push((bx, by, step_ms.min(80)));
        }

        let post_pause_ms = rng.random_range(40..120_u64);
        (tx, ty, points, post_pause_ms)
    };

    for (bx, by, step_ms) in curve_points {
        let _ = page.move_mouse(Point::new(bx, by)).await;
        tokio::time::sleep(Duration::from_millis(step_ms)).await;
    }

    tokio::time::sleep(Duration::from_millis(post_pause_ms)).await;
    let _ = page.click(Point::new(tx, ty)).await;
}

/// Walk the CDP DOM tree and return the NodeId to click for a Turnstile challenge.
fn find_shadow_challenge_node(node: &Node) -> Option<NodeId> {
    let children = node.children.as_deref().unwrap_or(&[]);

    let is_shadow_host = children.iter().any(|child| {
        child
            .attributes
            .as_deref()
            .unwrap_or(&[])
            .chunks(2)
            .any(|p| p.len() == 2 && p[0] == "name" && p[1] == "cf-turnstile-response")
    });

    if is_shadow_host {
        if let Some(sr) = node.shadow_roots.as_ref().and_then(|srs| srs.first()) {
            for sr_child in sr.children.as_deref().unwrap_or(&[]) {
                let hidden = sr_child
                    .attributes
                    .as_deref()
                    .unwrap_or(&[])
                    .chunks(2)
                    .any(|p| p.len() == 2 && p[0] == "style" && p[1].contains("display: none"));
                if !hidden {
                    return Some(sr_child.node_id);
                }
            }
        }
    }

    for child in children {
        if let Some(id) = find_shadow_challenge_node(child) {
            return Some(id);
        }
    }
    for sr in node.shadow_roots.as_deref().unwrap_or(&[]) {
        for sr_child in sr.children.as_deref().unwrap_or(&[]) {
            if let Some(id) = find_shadow_challenge_node(sr_child) {
                return Some(id);
            }
        }
    }
    None
}

/// Return the first non-empty entry (trimmed) from `candidates` — used to pick
/// an effective proxy URL from an ordered list of candidate sources.
#[cfg(feature = "server")]
pub fn pick_proxy<I, S>(candidates: I) -> Option<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    candidates
        .into_iter()
        .map(|s| s.as_ref().trim().to_string())
        .find(|s| !s.is_empty())
}

/// Proxy environment variables honored for the fallback, in priority order
/// (HTTPS first, since we fetch https URLs).
#[cfg(feature = "server")]
const PROXY_ENV_VARS: [&str; 6] = [
    "HTTPS_PROXY",
    "https_proxy",
    "HTTP_PROXY",
    "http_proxy",
    "ALL_PROXY",
    "all_proxy",
];

/// The proxy configured via the process environment, resolved through `lookup`
/// (injected so the precedence is unit-testable without touching global env).
/// First non-empty of [`PROXY_ENV_VARS`] wins.
#[cfg(feature = "server")]
pub fn env_proxy_from<F>(lookup: F) -> Option<String>
where
    F: Fn(&str) -> Option<String>,
{
    pick_proxy(PROXY_ENV_VARS.iter().filter_map(|k| lookup(k)))
}

/// The proxy from the process environment (`HTTPS_PROXY` etc.), if any. Lets a
/// deployment set a global upstream proxy for requests without their own. Chrome
/// inherits these too but can't authenticate from the embedded `user:pass@`;
/// routing the value through [`fetch`]'s per-context proxy + CDP auth is what makes
/// an authenticated container proxy work (else: `net::ERR_INVALID_AUTH_CREDENTIALS`).
#[cfg(feature = "server")]
pub fn env_proxy() -> Option<String> {
    env_proxy_from(|k| std::env::var(k).ok())
}

/// The environment proxy fallback, validated: `None` (today's no-proxy behavior)
/// when unset or malformed, so a bad `HTTPS_PROXY` can't break every request.
/// Credential-safe to log: no URL is named and [`parse_proxy_url`] errors carry no value.
#[cfg(feature = "server")]
fn resolve_env_proxy() -> Option<String> {
    let ep = env_proxy()?;
    if let Err(e) = parse_proxy_url(&ep) {
        tracing::warn!("ignoring malformed environment proxy: {e}");
        return None;
    }
    tracing::info!("no request proxy; routing upstream via environment proxy");
    Some(ep)
}

/// Dispatch a FlareSolverr protocol command. Returns (status, message, Option<FetchResponse>).
#[cfg(feature = "server")]
#[allow(clippy::too_many_arguments)]
pub async fn dispatch(
    store: &Arc<SessionStore>,
    cmd: &str,
    url: Option<&str>,
    is_post: bool,
    post_data: Option<&str>,
    proxy_url: Option<&str>,
    session_id: Option<&str>,
    extra_cookies: &[RequestCookie],
    max_timeout_ms: u64,
) -> Result<(String, String, Option<FetchResponse>)> {
    dispatch_with_download(
        store, cmd, url, is_post, post_data, proxy_url,
        session_id, extra_cookies, max_timeout_ms, false,
    )
    .await
}

/// The /v1 HTTP API uses this entrypoint to preserve the Python download flag.
#[cfg(feature = "server")]
#[allow(clippy::too_many_arguments)]
pub async fn dispatch_with_download(
    store: &Arc<SessionStore>,
    cmd: &str,
    url: Option<&str>,
    is_post: bool,
    post_data: Option<&str>,
    proxy_url: Option<&str>,
    session_id: Option<&str>,
    extra_cookies: &[RequestCookie],
    max_timeout_ms: u64,
    download: bool,
) -> Result<(String, String, Option<FetchResponse>)> {
    match cmd {
        "request.get" | "request.post" => {
            let url = url.ok_or_else(|| FlareSolverError::MissingField("url".into()))?;
            // Proxy precedence: session-bound, then the request `proxy` field, then
            // the environment (`HTTPS_PROXY` etc.) — the last authenticated over CDP
            // so a container-wide proxy works.
            let effective_proxy: Option<String> = session_id
                .and_then(|id| store.registry.get_proxy(id))
                .or_else(|| proxy_url.map(str::to_string))
                .or_else(resolve_env_proxy);
            let browser = store.browser().await?;
            let resp = fetch_with_download(
                browser,
                url,
                is_post,
                post_data,
                effective_proxy.as_deref(),
                extra_cookies,
                max_timeout_ms,
                download,
            )
            .await?;
            Ok(("ok".into(), String::new(), Some(resp)))
        }
        "sessions.create" => {
            let id = store
                .registry
                .create(session_id.map(|s| s.to_string()), proxy_url)?;
            Ok(("ok".into(), format!("Session created: {id}"), None))
        }
        "sessions.list" => {
            let ids = store.registry.list();
            Ok((
                "ok".into(),
                serde_json::to_string(&ids).unwrap_or_default(),
                None,
            ))
        }
        "sessions.destroy" => {
            let id = session_id.ok_or_else(|| FlareSolverError::MissingField("session".into()))?;
            store.registry.destroy(id)?;
            Ok(("ok".into(), format!("Session destroyed: {id}"), None))
        }
        other => Err(FlareSolverError::UnsupportedCommand(other.to_string())),
    }
}