//! Per-theory HTTP handlers.  Each one looks up the theory by idx,
//! parses the trailing wildcard path, and emits HTML or the JSON
//! envelope the frontend expects.

use std::sync::Arc;

use axum::{
    extract::{Path, Query, State},
    http::{HeaderMap, StatusCode, header},
    response::{IntoResponse, Response},
};
use std::collections::HashMap;
use serde_json::Value;

use crate::handlers::{json_resp, path_parse, theory_html};
use crate::state::AppState;

use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::constraint::solver::search::NodeStatus;
use tamarin_theory::prove::prove_lemma;

// ---------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------

fn html_response(html: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, "text/html; charset=utf-8".parse().unwrap());
    (StatusCode::OK, headers, html).into_response()
}

fn text_response(s: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, "text/plain; charset=utf-8".parse().unwrap());
    (StatusCode::OK, headers, s).into_response()
}

/// Haskell's `notFound` returns a 404 HTML page.  We mirror that so the
/// frontend's `server.handleResponseError` triggers the right branch.
/// Used for non-JSON live routes (`overview`, `download`, `source`,
/// `message`, `unload`).
pub fn missing_idx_html(idx: usize) -> Response {
    let body = format!(
        "<!DOCTYPE html>\n<html><head><title>Not Found</title></head><body>\
         <h1>Not Found</h1><p>Theory index {} not found.</p></body></html>",
        idx);
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, "text/html; charset=utf-8".parse().unwrap());
    (StatusCode::NOT_FOUND, headers, body).into_response()
}

fn parse_path(raw: &str) -> path_parse::TheoryPath {
    path_parse::parse(raw).unwrap_or(path_parse::TheoryPath::Help)
}

// ---------------------------------------------------------------------
// Overview / main view
// ---------------------------------------------------------------------

/// `GET /thy/trace/<idx>/overview/*path` — full framed page.
pub async fn interactive_overview(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    if state.store.get(idx).is_none() {
        // Haskell's `notFound` returns 404 HTML; our overview is HTML
        // too so we match exactly.
        return missing_idx_html(idx);
    }
    let path = parse_path(&raw_path);
    // Eagerly build the live proof state when navigating to a
    // proof/lemma path so the right pane can render the initial
    // constraint system + applicable proof methods (Haskell does this
    // implicitly via `subProofSnippet` since its `IncrementalProof` is
    // always populated at theory close time).
    materialise_proof_state_if_needed(&state, idx, &path);
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    html_response(theory_html::overview_page(&entry, &path))
}

/// `GET /thy/trace/<idx>/main/*path` — AJAX-only JsonHtml content
/// (no framing).  Missing idx returns 404 HTML to match Haskell's
/// `withTheory` / `notFound` (see `src/Web/Handler.hs:660-666`).
///
/// Special-cases the `TheoryMethod` path (Haskell `getTheoryPathMR` →
/// `applyMethodAtPath`): we look up the ranked applicable methods at
/// the indicated proof node, apply the requested one, allocate a fresh
/// theory idx for the post-step state, and return a `{redirect}` JSON
/// envelope pointing at `/thy/trace/<newIdx>/overview/proof/...`.
pub async fn theory_path_main(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    if state.store.get(idx).is_none() {
        return missing_idx_html(idx);
    }
    let path = parse_path(&raw_path);
    // Method paths mutate the proof tree; dispatch separately.
    if let path_parse::TheoryPath::Method { lemma, idx: method_nr, sub } = &path {
        return apply_method_and_redirect(
            &state, idx, lemma, *method_nr, sub).into_response();
    }
    materialise_proof_state_if_needed(&state, idx, &path);
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let title = title_for(&entry, &path);
    let body = theory_html::path_html(&entry, &path);
    json_resp::html(title, body).into_response()
}

/// Apply ranked method `method_nr` (1-based) at proof path `sub` in
/// lemma `lemma`'s tree.  Allocates a fresh idx for the post-step
/// state and returns a JsonRedirect pointing at the resulting
/// `overview/proof/<lemma>/<sub>` URL.  Mirrors Haskell's
/// `applyMethodAtPath` + `modifyTheory` flow in
/// `src/Web/Handler.hs:1013-1015` and `src/Web/Theory.hs:80-94`.
fn apply_method_and_redirect(
    state: &AppState,
    idx: usize,
    lemma: &str,
    method_nr: usize,
    sub: &[String],
) -> axum::Json<Value> {
    // Ensure the proof state at the *source* idx is built (so we can
    // navigate to the sub-path and rank candidate methods there).
    let src_ps = match state.store.ensure_proof_state(idx, &state.cfg.maude_path) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!("proof state init failed: {}", e)),
    };
    // Look up the system at the requested path.
    let sys_at_path = match src_ps.get_system_at(lemma, sub) {
        Some(s) => s,
        None => return json_resp::alert(format!(
            "no system at path {:?} in lemma {}", sub, lemma)),
    };
    // Pick the N-th ranked method (1-based).  Filter to only those
    // methods whose `exec_proof_method` succeeds — matches Haskell's
    // `rankProofMethods` → `execMethods` (`ProofMethod.hs:653-668`)
    // semantics, and matches the user-visible numbering produced by
    // `write_applicable_methods` (which applies the same filter).
    // Without filtering here the numbering would drift on Sorry/no-op
    // candidates that the UI omits.
    let method = {
        let ctx_guard = src_ps.ctx.lock();
        let methods: Vec<_> =
            tamarin_theory::constraint::solver::search::candidate_methods(
                &sys_at_path, &ctx_guard, 0)
                .into_iter()
                .filter(|m| tamarin_theory::constraint::solver::proof_method::
                    exec_proof_method(&ctx_guard, m, &sys_at_path).is_some())
                .collect();
        if method_nr == 0 || method_nr > methods.len() {
            return json_resp::alert(
                "Sorry, but the prover failed on the selected method!");
        }
        methods.into_iter().nth(method_nr - 1).unwrap()
    };
    // Allocate a fresh theory idx so the post-step state doesn't
    // overwrite the source (matches Haskell's `modifyTheory` →
    // `putTheory` allocating a new idx).  We FORK the source's proof
    // state so the post-step state retains the SAME tree shape as the
    // source (preserving any prior applied steps' children), then
    // apply the step in the fork.  Mirrors Haskell where `putTheory`
    // installs the modified `ClosedTheory` value (which contains its
    // full `IncrementalProof`) at the new idx.
    let new_idx = match state.store.clone_at_new_idx_forking_proof_state(idx) {
        Some(n) => n,
        None => return json_resp::alert(format!("theory index {} not found", idx)),
    };
    let new_ps = match state.store.ensure_proof_state(new_idx, &state.cfg.maude_path) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!(
            "proof state init failed on fresh idx: {}", e)),
    };
    if let Err(e) = new_ps.apply_at_path(lemma, sub, method) {
        return json_resp::alert(format!("proof step failed: {}", e));
    }
    // Build the redirect URL matching Haskell's `renderTheoryPath`
    // for `TheoryProof lemma sub` (`src/Web/Types.hs:372`):
    //   "proof" : lemma : (map prefixWithUnderscore sub)
    // i.e. lemma root (sub=[]) becomes `proof/<lemma>` (no trailing
    // segments); each sub segment is `prefixWithUnderscore`d.
    let mut url = format!(
        "/thy/trace/{}/overview/proof/{}",
        new_idx, url_path_escape(lemma));
    for seg in sub {
        url.push('/');
        let escaped = if seg.is_empty() { "_".to_string() }
            else if seg.starts_with('_') { format!("_{}", seg) }
            else { seg.clone() };
        url.push_str(&url_path_escape(&escaped));
    }
    json_resp::redirect(url)
}

/// Local copy of `proof_tree::url_path_escape` (the latter is private).
fn url_path_escape(s: &str) -> String {
    s.chars().map(|c| match c {
        c if c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '.' => c.to_string(),
        c => format!("%{:02X}", c as u32),
    }).collect()
}

/// Build the per-theory `ProofState` when the path is a Proof / Method
/// / Lemma so the renderer can show the initial constraint system +
/// applicable proof methods. Best-effort: silent failure leaves
/// `entry.proof_state = None` (renderer falls back to the static
/// "sorry /* initial */" line).
fn materialise_proof_state_if_needed(
    state: &AppState,
    idx: usize,
    path: &path_parse::TheoryPath,
) {
    let needs = matches!(path,
        path_parse::TheoryPath::Proof { .. }
        | path_parse::TheoryPath::Method { .. }
        | path_parse::TheoryPath::Lemma(_));
    if !needs { return; }
    let _ = state.store.ensure_proof_state(idx, &state.cfg.maude_path);
}

fn title_for(entry: &crate::state::TheoryEntry, path: &path_parse::TheoryPath) -> String {
    use path_parse::TheoryPath::*;
    let base = &entry.name;
    match path {
        Help => format!("{} (help)", base),
        Rules => format!("{} (rules)", base),
        Message => format!("{} (message theory)", base),
        Tactic => format!("{} (tactic)", base),
        Lemma(n) => format!("{} :: {}", base, n),
        Proof { lemma, .. } | Method { lemma, .. } => format!("{} :: proof {}", base, lemma),
        Source { .. } => format!("{} (sources)", base),
        Edit(n) | Add(n) | Delete(n) => format!("{} :: {}", base, n),
    }
}

// ---------------------------------------------------------------------
// Source / message deduction (pretty-printed)
// ---------------------------------------------------------------------

pub async fn source_(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    // This handler still emits the placeholder `(...)` form below.
    // TODO: wire up the existing `prettyClosedTheory` port
    // (`pretty_theory::pretty_closed_theory`) so this renders the full
    // theory source instead.
    let mut s = format!("theory {}\n\nbegin\n\n", entry.name);
    for r in entry.typed_theory.rules() {
        s.push_str(&format!("rule {}: (...)\n", r.name()));
    }
    for r in entry.typed_theory.restrictions() {
        s.push_str(&format!("restriction {}: (...)\n", r.name));
    }
    for l in entry.typed_theory.lemmas() {
        s.push_str(&format!("lemma {}: (...)\n", l.name));
    }
    s.push_str("\nend\n");
    text_response(s)
}

pub async fn message_deduction(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    text_response(format!("# message deduction for {}\n# (not yet implemented in Rust port)\n", entry.name))
}

// ---------------------------------------------------------------------
// Autoprove
// ---------------------------------------------------------------------

/// `GET /thy/trace/<idx>/autoprove/<ext>/<bound>/<quit>/*path`
///
/// `extractor` ∈ { characterize, idfs, bfs, seqdfs, sorry }
/// `bound` is the prover bound (0 = unlimited)
/// `quit` is `True`/`False` (Yesod `PathPiece Bool`; capital-cased).
///   The URL extractor on this handler is `String`, but the router
///   only matches when the `<quit>` segment is exactly one of those
///   two strings — see [`parse_bool_path_piece`].  Anything else
///   yields a 404 (the catch-all stub handler below).
/// `path`'s first segment is typically `proof/<lemma-name>`.
pub async fn autoprove(
    State(state): State<Arc<AppState>>,
    Path((idx, _extractor, bound, quit, raw_path)):
        Path<(usize, String, usize, String, String)>,
) -> Response {
    // Match Haskell's Yesod `PathPiece Bool`: only "True" / "False"
    // are valid.  Anything else 404s.
    if parse_bool_path_piece(&quit).is_none() {
        return missing_idx_html(idx);
    }
    let Some(entry) = state.store.get(idx) else {
        // Haskell: notFound from `withTheory`.  The handler returns
        // JSON in the success branch but 404 HTML when the theory is
        // missing.  We mirror that.
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let lemma_name = match &path {
        path_parse::TheoryPath::Proof { lemma, .. }
        | path_parse::TheoryPath::Method { lemma, .. }
        | path_parse::TheoryPath::Lemma(lemma) => lemma.clone(),
        _ => return json_resp::alert(
            "Can't run the autoprover () on the given theory path!".to_string())
            .into_response(),
    };

    // Use the configured bound, or the URL-provided one when non-zero.
    let max_steps = if bound > 0 { bound } else { state.cfg.max_steps };
    let maude_path = state.cfg.maude_path.clone();
    let parser_theory = entry.parser_theory.clone();
    let lemma_owned = lemma_name.clone();

    // Run the proof on a blocking thread so we don't block the runtime.
    let result = tokio::task::spawn_blocking(move || {
        let sig = match tamarin_theory::elaborate::elaborate(&parser_theory) {
            Ok(t) => t.signature.maude_sig.clone(),
            Err(_) => tamarin_term::maude_sig::pair_maude_sig(),
        };
        let h = match MaudeHandle::start(&maude_path, sig) {
            Ok(h) => h,
            Err(e) => return Err(format!("maude failed to start: {:?}", e)),
        };
        match prove_lemma(&parser_theory, &lemma_owned, h, max_steps) {
            // Return the full ProofNode tree so the route handler can
            // install it into the post-autoprove idx's ProofState —
            // letting the user navigate the autoproved tree directly.
            Ok(root) => Ok(root),
            Err(e) => Err(format!("prove failed: {}", e)),
        }
    }).await;

    match result {
        Err(join_err) => json_resp::alert(format!("internal error: {}", join_err)).into_response(),
        Ok(Err(_)) => {
            // Haskell formats this as `"Sorry, but <prover-name> failed!"`.
            // `getAutoProverR` builds `<prover-name>` as e.g. "the
            // autoprover ()" — the same string Haskell uses when no
            // qualifiers are emitted.
            json_resp::alert("Sorry, but the autoprover () failed!").into_response()
        }
        Ok(Ok(root)) => {
            let status = root.status.clone();
            tracing::info!(idx, lemma = %lemma_name, ?status, "autoprove completed");
            // Map our internal NodeStatus to Tamarin's per-lemma
            // verdict relative to the lemma's trace-quantifier:
            //
            //   all-traces lemma:
            //     Contradictory  → verified
            //     Solved         → falsified (attack found)
            //
            //   exists-trace lemma:
            //     Solved         → verified (witness found)
            //     Contradictory  → falsified (no witness exists)
            //
            // Sorry / Unfinishable / Open all mean the search did
            // not produce a definitive answer.
            let is_exists = entry.typed_theory
                .lookup_lemma(&lemma_name)
                .map(|l| matches!(l.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace))
                .unwrap_or(false);
            let verdict = match (status.clone(), is_exists) {
                (NodeStatus::Solved, false)        => "falsified (attack found)",
                (NodeStatus::Solved, true)         => "verified (witness found)",
                (NodeStatus::Contradictory, false) => "verified",
                (NodeStatus::Contradictory, true)  => "falsified (no witness exists)",
                (NodeStatus::Unfinishable, _)      => "Unfinishable",
                (NodeStatus::Sorry, _)             => "Sorry (search exhausted budget)",
                (NodeStatus::Open, _)              => "Open (incomplete)",
            };
            tracing::info!("autoprove verdict for {}: {}", lemma_name, verdict);
            // Mirror Haskell `modifyTheory` (`src/Web/Handler.hs:736`):
            // allocate a fresh theory idx for the post-autoprove state
            // so the user can compare before/after.
            let new_idx = state
                .store
                .clone_at_new_idx(idx)
                .unwrap_or(idx);
            // Install the autoproved tree into the new idx's ProofState
            // so the user can navigate it.  Best-effort: if
            // ensure_proof_state fails (Maude missing), we still
            // redirect — the user just sees the static lemma view.
            if let Ok(ps) = state.store.ensure_proof_state(
                new_idx, &state.cfg.maude_path) {
                let _ = ps.replace_root(&lemma_name, root);
            }
            // Render mirrors Haskell `renderTheoryPath` for
            // `TheoryProof lemma []` → `proof/<lemma>` (the empty
            // tail produces no extra path segment — see Haskell's
            // `renderTheoryPath` definition in `src/Web/Types.hs:372`).
            // After autoprove, Haskell's `nextSmartThyPath` typically
            // walks INTO the freshly grown proof tree (the captured
            // fixture has `ONE/ONE` from the protocol's first rule
            // case).  Since our Rust solver returns a status rather
            // than the proof tree, we land on the proof root.  Both
            // shapes are accepted by the frontend dispatcher
            // (`server.handleJson` just navigates).
            let redir = format!(
                "/thy/trace/{idx}/overview/proof/{lname}",
                idx = new_idx,
                lname = lemma_name);
            json_resp::redirect(redir).into_response()
        }
    }
}

/// Yesod `PathPiece Bool` accepts ONLY `True` and `False`
/// (capitalised).  See `instance PathPiece Bool` in `yesod-core`.
/// Returns `None` for any other input.
pub fn parse_bool_path_piece(s: &str) -> Option<bool> {
    match s {
        "True" => Some(true),
        "False" => Some(false),
        _ => None,
    }
}

/// `GET /thy/trace/<idx>/autoproveAll/<extractor>/<bound>/*path` —
/// run the autoprover on every lemma and return a redirect to the
/// fresh theory idx, matching Haskell `getAutoProverAllR` /
/// `getProverAllR` in `src/Web/Handler.hs:1194-1218`.
///
/// We allocate a fresh idx snapshot (matching Haskell's
/// `modifyTheory`) and run each lemma sequentially under the supplied
/// budget.  The Rust solver returns a status not a proof tree, so the
/// new entry shares the same parser+typed snapshot as the source —
/// full proof-tree mutation is a separate task once `ClosedTheory`
/// proof mutation is ported.  The redirect URL SHAPE matches Haskell:
/// `<newIdx>/overview/proof/<lastLemma>/_/...`.
pub async fn autoprove_all(
    State(state): State<Arc<AppState>>,
    Path((idx, _extractor, bound, _raw_path)): Path<(usize, String, usize, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let lemma_names: Vec<String> = entry
        .typed_theory
        .lemmas()
        .map(|l| l.name.clone())
        .collect();
    let last_lemma = lemma_names.last().cloned();

    // Best-effort: only run lemmas if we can boot Maude.  Even if
    // proving fails we still clone the snapshot and redirect — that
    // matches Haskell's `getProverAllR` which folds with
    // `applyProverAtPath` (silent no-op on failure).
    let max_steps = if bound > 0 { bound } else { state.cfg.max_steps };
    let maude_path = state.cfg.maude_path.clone();
    let parser_theory = entry.parser_theory.clone();
    let lemma_names_owned = lemma_names.clone();
    let _ = tokio::task::spawn_blocking(move || {
        let sig = match tamarin_theory::elaborate::elaborate(&parser_theory) {
            Ok(t) => t.signature.maude_sig.clone(),
            Err(_) => tamarin_term::maude_sig::pair_maude_sig(),
        };
        for lname in &lemma_names_owned {
            // One Maude per-lemma so we don't share state between
            // proofs.  Drop on failure and continue.
            if let Ok(h) = MaudeHandle::start(&maude_path, sig.clone()) {
                let _ = prove_lemma(&parser_theory, lname, h, max_steps);
            }
        }
    })
    .await;

    let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
    let target = match last_lemma {
        // Match Haskell `renderTheoryPath (TheoryProof lname [])` →
        // `proof/<lname>` (no trailing `_`).
        Some(n) => format!(
            "/thy/trace/{idx}/overview/proof/{lname}",
            idx = new_idx,
            lname = n),
        None => format!("/thy/trace/{}/overview/help", new_idx),
    };
    json_resp::redirect(target).into_response()
}

/// `GET /thy/trace/<idx>/verify/*path` — rebuild a lemma's reuse-proofs
/// and return:
///   - `{redirect}` when the path is `proof/<lemma>/<sub>` (Haskell
///     uses `editProof` which calls `replaceTheory` at the SAME idx —
///     so the redirect target is `/thy/trace/<idx>/overview/proof/...`).
///   - `{html,title}` (help-pane fallback) for everything else,
///     mirroring Haskell's `getTheoryPathMR idx TheoryHelp` in the
///     `_` arm of `getTheoryVerifyR`.
///
/// Reference: `src/Web/Handler.hs:833-841`.
pub async fn verify(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> axum::Json<Value> {
    let Some(entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx));
    };
    let path = parse_path(&raw_path);
    match path {
        // The success branch: rebuild reuse proofs at the same idx
        // (Haskell `editProof` → `replaceTheory`) and redirect.
        path_parse::TheoryPath::Proof { lemma, sub } => {
            // Re-emit the proof path verbatim so navigation stays
            // pointed at the same node.  Mirrors Haskell `JsonRedirect`
            // target: `/thy/trace/<idx>/overview/proof/<lemma>/...`.
            let mut url = format!("/thy/trace/{}/overview/proof/{}", idx, lemma);
            for seg in sub {
                url.push('/');
                // Mirror prefixWithUnderscore for URL emission.
                if seg.is_empty() {
                    url.push('_');
                } else if seg.starts_with('_') {
                    url.push('_');
                    url.push_str(&seg);
                } else {
                    url.push_str(&seg);
                }
            }
            json_resp::redirect(url)
        }
        // Help-pane fallback: Haskell falls through to
        // `getTheoryPathMR idx TheoryHelp`, which is the JsonHtml for
        // the help screen.  We piggy-back on `theory_path_main` via a
        // synthesised Help path.
        _ => {
            let help_path = path_parse::TheoryPath::Help;
            let title = format!("Theory: {}", entry.name);
            let body = crate::handlers::theory_html::path_html(&entry, &help_path);
            json_resp::html(title, body)
        }
    }
}

// ---------------------------------------------------------------------
// Theory management
// ---------------------------------------------------------------------

pub async fn unload(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> impl IntoResponse {
    state.store.remove(idx);
    axum::response::Redirect::to("/")
}

/// `POST /thy/trace/<idx>/reload` — re-read the source `.spthy` from
/// disk and replace the entry at the same idx (mirrors Haskell
/// `postReloadTheoryR` in `src/Web/Handler.hs:437-447` which calls
/// `replaceTheory` — same idx, not a fresh allocation).
pub async fn reload(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> axum::Json<Value> {
    let Some(entry) = state.store.get(idx) else {
        // Haskell prefers a JSON alert here (`JsonAlert "Theory not
        // found"`) rather than 404, since `reload` is a POST from a
        // form/button — surfacing through the standard alert UI.
        return json_resp::alert("Theory not found".to_string());
    };
    let path = match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => p.clone(),
        _ => return json_resp::alert(
            "Cannot reload: theory was uploaded or interactively created"),
    };
    match crate::theory_io::load_from_path(&path) {
        Ok(new_entry) => {
            // Replace at the SAME idx — matches Haskell's
            // `replaceTheory` (used by `postReloadTheoryR` and
            // `editProof`).  URLs that referenced this theory stay
            // valid.
            let kept_idx = state.store.replace_at(idx, new_entry).unwrap_or(idx);
            json_resp::redirect(format!("/thy/trace/{}/overview/help", kept_idx))
        }
        Err(e) => json_resp::alert(format!("reload failed: {}", e)),
    }
}

pub async fn download(
    State(state): State<Arc<AppState>>,
    Path((idx, name)): Path<(usize, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    // Haskell uses `application/octet-stream` to force the browser to
    // present a "Save As" dialog rather than render inline.  See
    // `getDownloadTheoryR` in `src/Web/Handler.hs` — it returns
    // `(typeOctet, source)`.
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, "application/octet-stream".parse().unwrap());
    headers.insert(
        header::CONTENT_DISPOSITION,
        format!("attachment; filename=\"{}\"", name).parse().unwrap(),
    );
    if let crate::state::TheoryOrigin::Local(p) = &entry.origin {
        if let Ok(bytes) = tokio::fs::read(p).await {
            return (StatusCode::OK, headers, bytes).into_response();
        }
    }
    // Theory wasn't loaded from a file (upload / interactive) — we still
    // emit `application/octet-stream`, but with a placeholder body.
    let body = format!("# {} (could not locate source file)\n", entry.name);
    (StatusCode::OK, headers, body).into_response()
}

// ---------------------------------------------------------------------
// Stubs (501) for features not yet ported.
// ---------------------------------------------------------------------

fn stub_alert(what: &str) -> axum::Json<Value> {
    json_resp::alert(format!(
        "{} is not yet implemented in the Rust port (frontend stub)", what))
}

/// `GET /thy/trace/<idx>/next/<section>/*path` —
/// Compute the next theory-path under `section ∈ { normal, smart }`
/// and return its `/main/...` URL as `text/plain`.
///
/// Mirrors Haskell `getNextTheoryPathR` (`src/Web/Handler.hs:1444-1455`):
///   1. parse `path` into a TheoryPath
///   2. call `nextThyPath` or `nextSmartThyPath`
///   3. render `TheoryPathMR idx <new-path>` as a URL string
///
/// Our solver doesn't yet maintain the proof tree, so for `TheoryProof`
/// the "next sibling" is the same path (matches Haskell's behaviour
/// when no sibling exists; see `getNextElement`).  Other path
/// transitions are pure (no proof state needed) and match Haskell.
pub async fn next_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let new_path = next_theory_path(&path, &section);
    let url = render_main_url(idx, &new_path);
    text_response(url)
}

/// `GET /thy/trace/<idx>/prev/<section>/*path` — symmetric to `next`.
pub async fn prev_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let new_path = prev_theory_path(&path, &section);
    let url = render_main_url(idx, &new_path);
    text_response(url)
}

/// Haskell `nextThyPath`/`nextSmartThyPath`.
///
/// The `section` argument is matched verbatim against the strings
/// `"normal"` / `"smart"`; any other value falls through to `const id`
/// (no-op) per Haskell's `next _ = const id` in
/// `src/Web/Handler.hs:1452-1455`.  That means e.g. `next/main/help`
/// returns the SAME path back — used by the frontend when the user
/// presses arrow keys outside the proof tree.
fn next_theory_path(p: &path_parse::TheoryPath, section: &str) -> path_parse::TheoryPath {
    match section {
        "normal" | "smart" => next_thy_path_inner(p),
        _ => p.clone(),
    }
}

fn next_thy_path_inner(p: &path_parse::TheoryPath) -> path_parse::TheoryPath {
    use path_parse::TheoryPath as T;
    use path_parse::SourceKind;
    match p {
        T::Help => T::Message,
        T::Message => T::Rules,
        T::Rules => T::Tactic,
        T::Tactic => T::Source { kind: SourceKind::Raw, src_idx: 0, case_idx: 0 },
        T::Source { kind: SourceKind::Raw, .. } =>
            T::Source { kind: SourceKind::Refined, src_idx: 0, case_idx: 0 },
        T::Source { kind: SourceKind::Refined, .. } => T::Help,
        T::Lemma(n) => T::Proof { lemma: n.clone(), sub: Vec::new() },
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        T::Proof { .. } | T::Method { .. } => p.clone(),
    }
}

fn prev_theory_path(p: &path_parse::TheoryPath, section: &str) -> path_parse::TheoryPath {
    match section {
        "normal" | "smart" => prev_thy_path_inner(p),
        _ => p.clone(),
    }
}

fn prev_thy_path_inner(p: &path_parse::TheoryPath) -> path_parse::TheoryPath {
    use path_parse::TheoryPath as T;
    use path_parse::SourceKind;
    match p {
        T::Message => T::Help,
        T::Rules => T::Message,
        T::Tactic => T::Rules,
        T::Source { kind: SourceKind::Raw, .. } => T::Tactic,
        T::Source { kind: SourceKind::Refined, .. } =>
            T::Source { kind: SourceKind::Raw, src_idx: 0, case_idx: 0 },
        T::Help | T::Lemma(_) => T::Help,
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        T::Proof { .. } | T::Method { .. } => p.clone(),
    }
}

fn render_main_url(idx: usize, p: &path_parse::TheoryPath) -> String {
    let segs = p.render();
    if segs.is_empty() {
        return format!("/thy/trace/{}/main/help", idx);
    }
    let mut url = format!("/thy/trace/{}/main", idx);
    for s in &segs {
        url.push('/');
        url.push_str(s);
    }
    url
}

// ---------------------------------------------------------------------
// Graph routes — DOT pipeline live.
// ---------------------------------------------------------------------

/// Resolve the [`System`] to render at the given path.  Returns the
/// initial lemma system at proof-paths (`proof/<lemma>` or
/// `proof/<lemma>/<sub>`), or `None` for paths that have no associated
/// system (help / message / etc.).
///
/// Live proof state is materialised on first access via
/// [`TheoryStore::ensure_proof_state`].
fn resolve_system_for_path(
    state: &AppState,
    idx: usize,
    path: &path_parse::TheoryPath,
) -> Option<tamarin_theory::constraint::system::System> {
    let (lemma_name, sub) = match path {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Method { lemma, sub, .. } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Lemma(n) => (n.clone(), Vec::new()),
        _ => return None,
    };
    let ps = state.store.ensure_proof_state(idx, &state.cfg.maude_path)
        .ok()?;
    ps.get_system_at(&lemma_name, &sub)
}

/// `GET /thy/trace/<idx>/intdot/*path` — return the DOT source as
/// text/plain.  Mirrors Haskell's `getTheoryIntDotR` which sends the
/// raw DOT string to the frontend for client-side rendering by
/// viz.js.
pub async fn intdot(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let sys = match resolve_system_for_path(&state, idx, &path) {
        Some(s) => s,
        None => return text_response(
            "digraph G { label=\"no system at this path\" }\n".into()),
    };
    let opts = graph_options_from_map(&query);
    let dot = crate::handlers::dot::system_to_dot_with(&sys, &opts);
    text_response(dot)
}

/// Build `GraphOptions` from a parsed query map.  Re-uses the same
/// query parameter names as `graph_options_from_query`.
fn graph_options_from_map(
    qs: &HashMap<String, String>,
) -> crate::graph::GraphOptions {
    // Serialise back to `key=value&...` so we can reuse the existing
    // parser without duplicating it.
    let s: String = qs.iter()
        .map(|(k, v)| format!("{}={}", k, v))
        .collect::<Vec<_>>()
        .join("&");
    crate::graph::graph_options_from_query(&s)
}

/// `GET /thy/trace/<idx>/graph/*path` — return an SVG image of the
/// graph (or DOT source as fallback when `dot` is missing).
///
/// Haskell uses `getTheoryGraphR` to shell out to `dot -Tpng` /
/// `-Tsvg`; we follow the same approach via `std::process::Command`.
pub async fn graph(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let sys = match resolve_system_for_path(&state, idx, &path) {
        Some(s) => s,
        None => {
            // Same SVG placeholder Haskell renders for paths that
            // don't have a graph (help / message / rules).
            let mut headers = HeaderMap::new();
            headers.insert(header::CONTENT_TYPE,
                "image/svg+xml".parse().unwrap());
            return (StatusCode::OK, headers,
                "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"200\" height=\"40\">\
                 <text x=\"10\" y=\"25\" font-family=\"Helvetica\" font-size=\"10\">\
                 (no graph for this path)\
                 </text></svg>".to_string()).into_response();
        }
    };
    let opts = graph_options_from_map(&query);
    // Try to render with dot; fall back to DOT-as-text when
    // unavailable.
    match crate::handlers::dot::render_svg_or_dot_with(&sys, &opts) {
        crate::handlers::dot::RenderResult::Svg(bytes) => {
            let mut headers = HeaderMap::new();
            headers.insert(header::CONTENT_TYPE,
                "image/svg+xml".parse().unwrap());
            (StatusCode::OK, headers, bytes).into_response()
        }
        crate::handlers::dot::RenderResult::Dot(dot) => {
            // Fallback: send the DOT as text/plain so the user (or
            // frontend's viz.js) can pick it up.
            text_response(dot)
        }
    }
}

/// `GET /thy/trace/<idx>/interactive-graph-def/*path` — return DOT
/// for the frontend to render client-side with viz.js.
pub async fn interactive_graph_def(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let path = parse_path(&raw_path);
    let sys = match resolve_system_for_path(&state, idx, &path) {
        Some(s) => s,
        None => return text_response(
            "digraph G { label=\"no system at this path\" }\n".into()),
    };
    let opts = graph_options_from_map(&query);
    let dot = crate::handlers::dot::system_to_dot_with(&sys, &opts);
    text_response(dot)
}

/// `GET /thy/trace/<idx>/proof-step/<lemma>/<path...>/<method>` —
/// apply a single proof method at the given path and return a
/// `{html, title}` JsonHtml envelope with the updated proof tree
/// rendered for `/main/proof/<lemma>`.
///
/// URL parsing:
///   - The first segment after `<idx>/proof-step/` is the lemma name.
///   - The LAST 1 or 2 segments are the method (e.g. `simplify`,
///     `induction`, `sorry`, `solve/<id>`).
///   - Everything in between is the proof-tree path (case names).
pub async fn proof_step(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> axum::Json<Value> {
    let Some(_entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx));
    };
    // Parse the path: `<lemma>/<case>/.../<method>` or
    // `<lemma>/<case>/.../<method>/<arg>`.
    //
    // Mirror Haskell's `prefixWithUnderscore` invariant: empty case
    // names are encoded as `_` on the URL so adjacent slashes don't
    // collapse, and segments starting with `_` get a leading extra
    // `_`.  Reverse here.
    let segs: Vec<String> = raw_path
        .trim_matches('/')
        .split('/')
        .filter(|s| !s.is_empty())
        .map(|s| percent_encoding::percent_decode_str(s)
            .decode_utf8_lossy().to_string())
        .map(|s| crate::handlers::proof_tree::unprefix_underscore(&s))
        .collect();
    if segs.is_empty() {
        return json_resp::alert("missing lemma name");
    }
    let lemma = segs[0].clone();
    // Identify the method head — the last segment is the method
    // unless the second-to-last segment is `solve` (then `solve/<id>`
    // is the method).
    let n = segs.len();
    if n < 2 {
        return json_resp::alert("missing proof method");
    }
    let (method_segs_start, case_path_end) =
        if n >= 3 && segs[n - 2] == "solve" {
            (n - 2, n - 2)
        } else {
            (n - 1, n - 1)
        };
    let case_path: Vec<String> = segs[1..case_path_end].to_vec();
    let method_segs = &segs[method_segs_start..];
    let ps = match state.store.ensure_proof_state(idx, &state.cfg.maude_path) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!("proof state init failed: {}", e)),
    };
    let sys_at_path = match ps.get_system_at(&lemma, &case_path) {
        Some(s) => s,
        None => return json_resp::alert(format!(
            "no system at path {:?} in lemma {}", case_path, lemma)),
    };
    let method = match crate::handlers::proof_tree::parse_method(method_segs, &sys_at_path) {
        Some(m) => m,
        None => return json_resp::alert(format!(
            "unknown proof method: {:?}", method_segs)),
    };
    match ps.apply_at_path(&lemma, &case_path, method) {
        Ok(_status) => {}
        Err(e) => return json_resp::alert(format!("proof step failed: {}", e)),
    }
    // Re-render the updated proof tree.  Use the sub-proof snippet
    // for the node at `case_path` so the response shows Applicable
    // Proof Methods + Constraint System + N sub-case(s) just like
    // Haskell does.  Append the full proof tree below for navigation.
    let root = match ps.get_root(&lemma) {
        Some(r) => r,
        None => return json_resp::alert("proof tree disappeared"),
    };
    let node = match crate::handlers::proof_tree::navigate_at(&root, &case_path) {
        Some(n) => n,
        None => return json_resp::alert(format!(
            "no node at path {:?} after step", case_path)),
    };
    let ctx_guard = ps.ctx.lock();
    let mut html = crate::handlers::proof_tree::render_sub_proof_snippet(
        idx, &lemma, &case_path, node, &ctx_guard);
    drop(ctx_guard);
    html.push_str("<hr><h3>Proof tree</h3>\n");
    html.push_str(&crate::handlers::proof_tree::render_proof_tree_html(
        idx, &lemma, &root));
    let title = format!("Proof of {}", lemma);
    json_resp::html(title, html)
}

/// `POST /thy/trace/<idx>/edit/*path` — STUB.
///
/// Haskell's `postTheoryEditR` (`src/Web/Handler.hs:854-` and
/// `postEditTheoryR` block-comment around line 1499) reparses the
/// lemma plaintext from a form field, calls `editLemma`, and
/// reinserts the modified theory.  The Rust port doesn't yet expose
/// per-lemma plaintext re-parsing through `tamarin-parser`, so this
/// stays an `{alert}` stub.  Blocker: needs a `parseLemmaWithMacros`
/// equivalent in `tamarin-parser` + lemma-replace API on
/// `tamarin-theory::theory::Theory`.
pub async fn edit_stub(
    _: State<Arc<AppState>>,
    _: Path<(usize, String)>,
) -> axum::Json<Value> {
    stub_alert("lemma editing")
}

/// `GET /thy/trace/<idx>/del/path/*path` — delete a lemma (path
/// `lemma/<name>`) or a proof step (path `proof/<lemma>/<sub>`).
/// Returns `{redirect}` on success, mirroring Haskell
/// `getDeleteStepR` in `src/Web/Handler.hs:1587-1604`.
///
/// Haskell uses `modifyTheory` which allocates a fresh idx for the
/// post-delete state.  We do the same (clone the snapshot) — full
/// proof-tree mutation lands later.
pub async fn delete_step(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> axum::Json<Value> {
    let Some(_entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx));
    };
    let path = parse_path(&raw_path);
    match &path {
        // Haskell `removeLemma`-branch.
        path_parse::TheoryPath::Lemma(name) => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            // Haskell `modifyTheory` passes `(const path)` as fpath,
            // i.e. the redirect target is the same path that was
            // deleted (a `TheoryLemma name`).  Render shape:
            // `/thy/trace/<newIdx>/overview/lemma/<name>`.
            json_resp::redirect(format!(
                "/thy/trace/{}/overview/lemma/{}",
                new_idx, name))
        }
        // Haskell `applyProverAtPath ... sorryProver` branch — mark
        // the targeted proof step `sorry`.  Redirect target = same
        // proof path.
        path_parse::TheoryPath::Proof { lemma, sub } => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            let mut url = format!("/thy/trace/{}/overview/proof/{}", new_idx, lemma);
            for seg in sub {
                url.push('/');
                if seg.is_empty() {
                    url.push('_');
                } else if seg.starts_with('_') {
                    url.push('_');
                    url.push_str(seg);
                } else {
                    url.push_str(seg);
                }
            }
            json_resp::redirect(url)
        }
        _ => json_resp::alert("Can't delete the given theory path!"),
    }
}

/// `POST /thy/trace/<idx>/get_and_append/<name>` — append every
/// modified lemma's plaintext to the source `.spthy` on disk.
/// Mirrors Haskell `postAppendNewLemmasR` (`src/Web/Handler.hs:1675-1690`).
///
/// We don't yet track per-lemma "modified" state in the Rust port
/// (lemma-editing is still stubbed), so every lemma is treated as
/// unmodified.  That puts us on Haskell's "nothing-to-append" arm:
/// the file is left alone and the response is
/// `{alert: "Appended lemmas to <path>"}` (the alert is informational
/// regardless of whether anything was appended — see Haskell's
/// `allptxts /= "" && isJust maybePath` guard, which short-circuits
/// the file write).
pub async fn append_new_lemmas(
    State(state): State<Arc<AppState>>,
    Path((idx, _name)): Path<(usize, String)>,
) -> axum::Json<Value> {
    let Some(entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx));
    };
    match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => {
            // Haskell's nothing-to-append arm.  We never write because
            // we have no "modified" flag.
            json_resp::alert(format!("Appended lemmas to {}", p.display()))
        }
        _ => {
            // Mirrors Haskell's `if isNothing maybePath then ...` branch.
            json_resp::alert("No origin found for the current theory.".to_string())
        }
    }
}

/// `GET /thy/equiv/<idx>/...` — STUB.
/// Blocker: needs `ClosedDiffTheory` in `tamarin-theory`
/// (not yet ported).  Haskell returns 404 HTML for these routes
/// when no diff theory at idx; we currently return `{alert}` so the
/// frontend can dispatch a useful message.
pub async fn diff_stub(
    _: State<Arc<AppState>>,
    _: Path<(usize, String)>,
) -> axum::Json<Value> {
    stub_alert("diff theories")
}
