//! Root + housekeeping handlers.

use std::sync::Arc;

use axum::{
    body::Bytes,
    extract::{Multipart, State},
    http::{HeaderMap, StatusCode, header},
    response::{IntoResponse, Redirect, Response},
};

use crate::state::{AppState, TheoryOrigin};
use crate::theory_io;

/// `GET /` — Welcome page listing loaded theories.  Mirror Haskell's
/// `rootTpl` (`src/Web/Hamlet.hs:53-81`).
pub async fn get(State(state): State<Arc<AppState>>) -> Response {
    let html = render_index(&state);
    html_response(html)
}

/// `POST /` — File upload (multipart `uploadedTheory`).
pub async fn post(
    State(state): State<Arc<AppState>>,
    mut mp: Multipart,
) -> Response {
    let mut alert_msg: Option<String> = None;
    while let Some(field) = mp.next_field().await.unwrap_or(None) {
        if field.name() != Some("uploadedTheory") { continue; }
        let filename = field.file_name().unwrap_or("uploaded.spthy").to_string();
        let bytes: Bytes = match field.bytes().await {
            Ok(b) => b,
            Err(e) => { alert_msg = Some(format!("upload failed: {}", e)); break; }
        };
        if bytes.is_empty() {
            alert_msg = Some("No theory file given.".into());
            break;
        }
        let src = match std::str::from_utf8(&bytes) {
            Ok(s) => s.to_string(),
            Err(_) => { alert_msg = Some("upload was not valid UTF-8".into()); break; }
        };
        match theory_io::load_from_source(&src, TheoryOrigin::Upload(filename.clone())) {
            Ok(entry) => {
                let idx = state.store.insert(entry);
                tracing::info!(idx, file = %filename, "uploaded theory");
            }
            Err(e) => { alert_msg = Some(format!("Theory loading failed: {}", e)); }
        }
        break;
    }
    let mut html = render_index(&state);
    if let Some(msg) = alert_msg {
        // Render a banner above the index — match Haskell's
        // `setMessage` lift into the layout.
        html = html.replacen(
            "<body>",
            &format!("<body><p class=\"message\">{}</p>", html_escape(&msg)),
            1,
        );
    }
    html_response(html)
}

/// `GET /favicon.ico` — Redirect to `/static/img/favicon.ico` (mirror
/// Haskell's `getFaviconR`).
pub async fn favicon() -> impl IntoResponse {
    Redirect::permanent("/static/img/favicon.ico")
}

/// `GET /robots.txt` — Mirror Haskell's `getRobotsR`.
pub async fn robots() -> impl IntoResponse {
    (StatusCode::OK,
     [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
     "User-agent: *")
}

/// `GET /kill?path=<key>` — frontend uses this to cancel a
/// long-running search.  Haskell binds the `path` query parameter and
/// `invalidArgs` (400) when it's missing; on success it returns
/// `Canceled request!` as `text/plain`.
///
/// See `getKillThreadR` in `src/Web/Handler.hs:1422-1440`.
///
/// We don't yet wire a `tokio_util::sync::CancellationToken` registry,
/// so the "cancel" is a soft ack — but the 400-on-missing-path
/// semantics match Haskell exactly so frontend dispatch works.
pub async fn kill_thread(
    axum::extract::Query(q): axum::extract::Query<KillQuery>,
) -> impl IntoResponse {
    match q.path {
        Some(_key) => (
            StatusCode::OK,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            "Canceled request!",
        )
            .into_response(),
        None => (
            StatusCode::BAD_REQUEST,
            [(header::CONTENT_TYPE, "text/html; charset=utf-8")],
            "<!DOCTYPE html><html><head><title>Invalid Arguments</title></head>\
             <body><h1>Invalid Arguments</h1><ul><li>No path to kill specified!</li></ul></body></html>",
        )
            .into_response(),
    }
}

#[derive(Debug, serde::Deserialize)]
pub struct KillQuery {
    pub path: Option<String>,
}

// ---------------------------------------------------------------------
// HTML rendering for `/` — a plain-Rust port of `rootTpl + theoriesTpl
// + introTpl` from `Web.Hamlet`.  Same /static/* references so the
// existing CSS/JS plays.
// ---------------------------------------------------------------------
fn render_index(state: &AppState) -> String {
    let theories = state.store.list();
    let mut rows = String::new();
    if theories.is_empty() {
        rows.push_str("<p><strong>No theories loaded!</strong></p>\n");
    } else {
        rows.push_str(r#"<table>
<thead><tr><th>Theory name</th><th>Time</th><th>Version</th><th>Origin</th></tr></thead>
<tbody>"#);
        for t in &theories {
            let link = format!("/thy/trace/{}/overview/help", t.idx);
            let time = t.loaded_at.format("%T");
            let primary = if t.primary { "Original" } else { "<em>Modified</em>" };
            rows.push_str(&format!(
                "<tr><td><a href=\"{}\">{}</a></td><td>{}</td><td>{}</td><td>{}</td></tr>\n",
                html_escape(&link),
                html_escape(&t.name),
                time,
                primary,
                html_escape(&t.origin.label()),
            ));
        }
        rows.push_str("</tbody></table>\n");
    }

    format!(r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Tamarin prover (Rust port)</title>
<link rel="stylesheet" href="/static/css/tamarin-prover-ui.css">
<link rel="stylesheet" href="/static/css/jquery-contextmenu.css">
<link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css">
<script src="/static/js/jquery.js"></script>
<script src="/static/js/jquery-ui.js"></script>
<script src="/static/js/tamarin-prover-ui.js"></script>
</head>
<body>
<div id="introbar">
  <div id="header-info">
    Running <a href="/"><span class="tamarin">Tamarin</span></a> {version} (Rust port)
  </div>
</div>
<div id="logo"><p><img src="/static/img/tamarin-logo-3-0-0.png"></p></div>
<div class="intropage">
<noscript><div class="warning">JavaScript must be enabled for the Tamarin UI to function properly.</div></noscript>
<h2>Loaded theories</h2>
{rows}
<h2>Loading a new theory</h2>
<form class="root-form" enctype="multipart/form-data" action="/" method="POST">
  <label>Filename: <input type="file" name="uploadedTheory"></label>
  <div class="submit-form"><input type="submit" value="Load new theory"></div>
</form>
<p>Note: You can save a theory by downloading the source from the Actions menu.</p>
</div>
</body>
</html>
"#,
        version = env!("CARGO_PKG_VERSION"),
        rows = rows,
    )
}

fn html_response(html: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, "text/html; charset=utf-8".parse().unwrap());
    (StatusCode::OK, headers, html).into_response()
}

pub fn html_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}
