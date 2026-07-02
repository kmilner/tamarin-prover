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

/// Parse the trailing wildcard path.  Returns `None` on UNPARSEABLE
/// input, mirroring Haskell's Yesod `PathMultiPiece TheoryPath`
/// instance (`fromPathMultiPiece = parseTheoryPath`,
/// `src/Web/Types.hs:650-652`): when `parseTheoryPath` returns
/// `Nothing`, Yesod routing yields `notFound` (404) BEFORE the handler
/// runs, so a malformed path 404s on every theory route.  Callers must
/// map `None` to [`not_found_response`].  Note the legitimate help view
/// (`/help`) parses to `TheoryPath::Help`, so it is NOT affected.
fn parse_path(raw: &str) -> Option<path_parse::TheoryPath> {
    path_parse::parse(raw)
}

/// Generic 404 used when the trailing path doesn't parse.  Mirrors
/// Yesod's routing-level `notFound` (a plain 404) — matches the
/// already-fixed `graph` handler's `(StatusCode::NOT_FOUND, "Not
/// Found")` response.
fn not_found_response() -> Response {
    (StatusCode::NOT_FOUND, "Not Found").into_response()
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    // The full framed page ALWAYS renders the left-pane proof-state tree
    // (`proof_state`), whose rule count (incl. the ISend/IRecv intruder
    // members of `crProtocol`) and raw/refined source-case annotations come
    // from the closed-theory `ProofContext`.  HS has these at theory-close
    // time for every page; RS builds the context lazily, so we must ensure it
    // here regardless of the center path — otherwise a frame whose center
    // needs no proof state (help/edit/add/delete) would show `(0 cases)` and a
    // proto-only rule count.  Best-effort: a Maude failure leaves the counts
    // as-is (same as before).
    let _ = state.store.ensure_proof_state(idx, &state.cfg.maude_path);
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
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
        let mut ctx_guard = src_ps.ctx.lock();
        // Install this lemma's per-lemma `use_induction`/`heuristic` into the
        // shared ctx BEFORE ranking, so the method-index → method mapping
        // matches HS (and the numbering `write_applicable_methods` displays).
        // Without this the mapping ranks under `AvoidInduction`/`Smart`, so a
        // `[use_induction]` lemma's method `1` resolves to the wrong method.
        src_ps.install_lemma_settings(&mut ctx_guard, lemma);
        // Haskell `applyMethodAtPath` ranks with `useHeuristic heuristic
        // (length proofPath)` (Web/Theory.hs:84-89); the depth selects
        // which ranking of a multi-ranking heuristic is active
        // (`rankings !! (depth mod n)`, ProofMethod.hs:583-590).  Pass
        // the proof-path length, not a hardcoded 0.
        let methods: Vec<_> =
            tamarin_theory::constraint::solver::search::candidate_methods(
                &sys_at_path, &ctx_guard, sub.len())
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
    // Build the redirect URL.  Haskell's `getTheoryPathMR` for
    // `TheoryMethod` (`src/Web/Handler.hs:1013-1016`) advances the target
    // via `nextSmartThyPath newThy (TheoryProof lemma proofPath)`, i.e. it
    // walks INTO the freshly created child case of the grown tree.  We now
    // do the same: re-fetch the entry at `new_idx` (its `proof_state` Arc is
    // the one `apply_at_path` just grew) and run the shared
    // `next_thy_path_inner` (smart) over it.  For a `TheoryProof` input that
    // arm always yields another `TheoryProof` (child path, next-lemma root,
    // or same path when nothing follows), so we render the `overview/proof`
    // URL from its `(lemma, sub)`.  The URL SHAPE matches Haskell's
    // `renderTheoryPath` (`src/Web/Types.hs:372`): lemma root (sub=[]) →
    // `proof/<lemma>`; each sub segment is `prefixWithUnderscore`d.
    let Some(new_entry) = state.store.get(new_idx) else {
        return json_resp::alert(format!("theory index {} vanished", new_idx));
    };
    let src_path = path_parse::TheoryPath::Proof {
        lemma: lemma.to_string(), sub: sub.to_vec() };
    let (target_lemma, target_sub) = match next_thy_path_inner(&src_path, &new_entry, true) {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma, sub),
        // `nextSmartThyPath` of a `TheoryProof` never leaves the proof arm;
        // fall back to the applied node if that invariant ever breaks.
        _ => (lemma.to_string(), sub.to_vec()),
    };
    let mut url = format!(
        "/thy/trace/{}/overview/proof/{}",
        new_idx, path_parse::url_path_escape(&target_lemma));
    for seg in &target_sub {
        url.push('/');
        url.push_str(&path_parse::url_path_escape(&path_parse::prefix_with_underscore(seg)));
    }
    json_resp::redirect(url)
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
        | path_parse::TheoryPath::Lemma(_)
        // Message / Rules pages need the closed-theory intruder-rule
        // classification + injective facts; Source pages need the
        // precomputed raw/refined source cases.  All live in the
        // `ProofContext` behind the `ProofState`.
        | path_parse::TheoryPath::Message
        | path_parse::TheoryPath::Rules
        | path_parse::TheoryPath::Source { .. });
    if !needs { return; }
    let _ = state.store.ensure_proof_state(idx, &state.cfg.maude_path);
}

/// Mirror Haskell `titleThyPath` (`src/Web/Theory.hs:1586-1607`).
/// Titles are independent of the theory name EXCEPT `TheoryHelp`.
fn title_for(entry: &crate::state::TheoryEntry, path: &path_parse::TheoryPath) -> String {
    use path_parse::TheoryPath::*;
    use path_parse::SourceKind;
    match path {
        // TheoryHelp -> "Theory: " ++ thy._thyName
        Help => format!("Theory: {}", entry.name),
        // TheoryRules -> "Multiset rewriting rules and restrictions"
        Rules => "Multiset rewriting rules and restrictions".to_string(),
        // TheoryMessage -> "Message theory"
        Message => "Message theory".to_string(),
        // TheoryTactic -> "Tactics"
        Tactic => "Tactics".to_string(),
        // TheorySource RawSource _ _ -> "Raw sources"
        Source { kind: SourceKind::Raw, .. } => "Raw sources".to_string(),
        // TheorySource RefinedSource _ _ -> "Refined sources"
        Source { kind: SourceKind::Refined, .. } => "Refined sources".to_string(),
        // TheoryEdit l -> "Edit Lemma: " ++ l
        Edit(l) => format!("Edit Lemma: {}", l),
        // TheoryAdd _ -> "Add new Lemma"  (HS ignores its argument)
        Add(_) => "Add new Lemma".to_string(),
        // TheoryDelete l -> "Delete " ++ l
        Delete(l) => format!("Delete {}", l),
        // TheoryLemma l -> "Lemma: " ++ l
        Lemma(l) => format!("Lemma: {}", l),
        // TheoryProof l [] -> "Lemma: " ++ l
        Proof { lemma, sub } if sub.is_empty() => format!("Lemma: {}", lemma),
        // TheoryProof l p | null (last p) -> "Method: " ++ methodName l p
        //                 | otherwise     -> "Case: " ++ last p
        //
        //   methodName l p = case resolveProofPath thy l p of
        //     Nothing    -> "None"
        //     Just proof -> renderHtmlDoc . prettyProofMethod . psMethod
        //                     . root $ proof
        // i.e. render the proof method stored at the node the path resolves
        // to.  `resolveProofPath` here == `navigate_at` on the live tree;
        // `psMethod . root` == that node's `.method`; `prettyProofMethod`
        // == `method_label`.  (`renderHtmlDoc` wraps operators in `hl_*`
        // spans the parity gate unwraps, so plain `method_label` compares
        // equal.)  Falls back to "None" when the tree/path is unresolvable,
        // exactly as HS's `Nothing` arm does.
        Proof { lemma, sub } => match sub.last() {
            // null (last p): "Method: " ++ methodName l p
            Some(s) if s.is_empty() => {
                let name = entry
                    .proof_state
                    .as_ref()
                    .and_then(|ps| ps.get_root(lemma))
                    .and_then(|root| {
                        crate::handlers::proof_tree::navigate_at(&root, sub)
                            .map(|n| crate::handlers::proof_tree::method_label(&n.method))
                    })
                    .unwrap_or_else(|| "None".to_string());
                format!("Method: {}", name)
            }
            // otherwise: "Case: " ++ last p
            Some(s) => format!("Case: {}", s),
            None => unreachable!("sub is non-empty: the [] case is handled above"),
        },
        // TheoryMethod{} -> "Method Path: This title should not be shown. ..."
        Method { .. } =>
            "Method Path: This title should not be shown. Please file a bug".to_string(),
    }
}

// ---------------------------------------------------------------------
// Source / message deduction (pretty-printed)
// ---------------------------------------------------------------------

/// Render the full closed-theory source, mirroring HS `getTheorySourceR`
/// and `getTheoryMessageDeductionR` — both are `render . prettyClosedTheory
/// . theory` (`Web/Handler.hs:950,985`), i.e. identical output.
///
/// Lemmas whose proofs have not been built render `by sorry` (empty
/// `proved`); the `Generated from:` version/build lines are placeholders
/// (the interactive server does not carry the CLI build constants — the
/// web-parity gate normalizes them away, as does HS's own `--prove` gate).
/// Wellformedness: the `/* WARNING: ... */` (or `/* All ... successful. */`)
/// block is rendered from the theory's stored `wf_report` — computed at load
/// by the same pipeline `--prove` runs — via the shared `format_wf_block`,
/// so it matches HS byte-for-byte (empty report ⇒ the "all successful" block).
fn render_theory_source(entry: &crate::state::TheoryEntry) -> String {
    let build = tamarin_theory::pretty_theory::BuildInfo {
        tamarin_version: env!("CARGO_PKG_VERSION").to_string(),
        maude_version: String::new(),
        git_revision: String::new(),
        git_branch: String::new(),
        compiled_at: String::new(),
    };
    let wf_block = tamarin_theory::pretty_theory::format_wf_block(&entry.wf_report);
    let in_file = entry.origin.label();
    tamarin_theory::pretty_theory::pretty_closed_theory(
        &entry.parser_theory,
        &entry.typed_theory,
        &[],
        &wf_block,
        &build,
        &in_file,
        false,
    )
}

pub async fn source_(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    text_response(render_theory_source(&entry))
}

pub async fn message_deduction(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    text_response(render_theory_source(&entry))
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
    Path((idx, extractor, bound, quit, raw_path)):
        Path<(usize, String, usize, String, String)>,
) -> Response {
    // Match Haskell's Yesod `PathPiece SolutionExtractor`
    // (`src/Web/Types.hs:626-638`): only the five known extractor names
    // parse; any other value makes `fromPathPiece` return `Nothing`, so
    // Yesod routing yields `notFound` (404) before the handler runs.
    // `autoprover_name` returns `None` for an unrecognised extractor and
    // otherwise the exact `fullName` Haskell `getAutoProverR` builds.
    let Some(name) = autoprover_name(&extractor, bound) else {
        return not_found_response();
    };
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    let lemma_name = match &path {
        path_parse::TheoryPath::Proof { lemma, .. }
        | path_parse::TheoryPath::Method { lemma, .. }
        | path_parse::TheoryPath::Lemma(lemma) => lemma.clone(),
        // Haskell `getProverR` non-`TheoryProof` arm
        // (`src/Web/Handler.hs:1072-1073`):
        //   JsonAlert $ "Can't run " <> name <> " on the given theory path!"
        _ => return json_resp::alert(
            format!("Can't run {} on the given theory path!", name))
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
            // Haskell `getProverR` `TheoryProof` failure
            // (`src/Web/Handler.hs:1068`):
            //   JsonAlert $ "Sorry, but " <> name <> " failed!"
            // where `name` is the `fullName` built by `getAutoProverR`
            // from the extractor + bound (see `autoprover_name`).
            json_resp::alert(format!("Sorry, but {} failed!", name)).into_response()
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
            // allocate a fresh theory idx for the post-autoprove state.
            // Use the FORKING clone so the new idx PRESERVES the source
            // idx's already-proved lemmas (HS `modifyTheory` puts the
            // modified `ClosedTheory` — with its full `IncrementalProof`
            // — at the new idx, so proving lemma-by-lemma accumulates).
            // The non-forking `clone_at_new_idx` would reset the proof
            // state, leaving only the just-proved lemma at each idx.
            let new_idx = state
                .store
                .clone_at_new_idx_forking_proof_state(idx)
                .unwrap_or(idx);
            // Install the autoproved tree into the new idx's ProofState
            // so the user can navigate it.  Best-effort: if
            // ensure_proof_state fails (Maude missing), we still
            // redirect — the user just sees the static lemma view.
            if let Ok(ps) = state.store.ensure_proof_state(
                new_idx, &state.cfg.maude_path) {
                let _ = ps.replace_root(&lemma_name, root);
            }
            // Haskell `getAutoProverR` (`src/Web/Handler.hs`) redirects via
            // `nextSmartThyPath newThy (TheoryProof lemma proofPath)` over the
            // freshly autoproved tree.  For a fully-proved all-traces lemma
            // (no interesting `Sorry`/`Finished Solved`/`Unfinishable` step)
            // that walks to the NEXT lemma's root; for an exists-trace lemma
            // it lands on the `Finished Solved` witness node.  Re-fetch the
            // entry at `new_idx` (its `proof_state` Arc now holds the
            // installed tree) and run the shared smart traversal from the
            // proof path the autoprover was invoked at.
            let src_sub: Vec<String> = match &path {
                path_parse::TheoryPath::Proof { sub, .. } => sub.clone(),
                _ => Vec::new(),
            };
            let redir = match state.store.get(new_idx) {
                Some(new_entry) => {
                    let src_path = path_parse::TheoryPath::Proof {
                        lemma: lemma_name.clone(), sub: src_sub };
                    let (tl, ts) = match next_thy_path_inner(&src_path, &new_entry, true) {
                        path_parse::TheoryPath::Proof { lemma, sub } => (lemma, sub),
                        _ => (lemma_name.clone(), Vec::new()),
                    };
                    let mut u = format!(
                        "/thy/trace/{}/overview/proof/{}",
                        new_idx, path_parse::url_path_escape(&tl));
                    for seg in &ts {
                        u.push('/');
                        u.push_str(&path_parse::url_path_escape(
                            &path_parse::prefix_with_underscore(seg)));
                    }
                    u
                }
                None => format!(
                    "/thy/trace/{idx}/overview/proof/{lname}",
                    idx = new_idx,
                    lname = path_parse::url_path_escape(&lemma_name)),
            };
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

/// Build the prover display name exactly as Haskell `getAutoProverR` /
/// `getAutoProverAllR` (`src/Web/Handler.hs:1170-1218`):
///
/// ```text
/// fullName   = proverName <> " (" <> intercalate ", " qualifiers <> ")"
/// qualifiers = extractorQualifier ++ boundQualifier
/// ```
///
/// `extractor` is the URL `#SolutionExtractor` path piece; Yesod's
/// `instance PathPiece SolutionExtractor` (`src/Web/Types.hs:626-638`)
/// accepts only the five strings below — any other value makes
/// `fromPathPiece` return `Nothing`, which Yesod turns into a routing
/// `notFound` (404) BEFORE the handler runs.  We mirror that by
/// returning `None` here for an unrecognised extractor.
///
/// Note: the displayed name is computed from the RAW extractor, NOT the
/// quit-on-empty–adjusted cut.  HS's `apCut = if quitOnEmpty then
/// CutAfterSorry else extractor` only affects the prover, while
/// `fullName`'s `extractorQualfier` matches on the original `extractor`.
fn autoprover_name(extractor: &str, bound: usize) -> Option<String> {
    let (prover_name, extractor_qual): (&str, &[&str]) = match extractor {
        "characterize" => ("characterization", &["dfs"]),
        "idfs"         => ("the autoprover",   &[]),
        "bfs"          => ("the autoprover",   &["bfs"]),
        "seqdfs"       => ("the autoprover",   &["seqdfs"]),
        "sorry"        => ("the autoprover",   &["sorry"]),
        _ => return None,
    };
    let mut qualifiers: Vec<String> = extractor_qual.iter().map(|s| s.to_string()).collect();
    if bound > 0 {
        qualifiers.push(format!("bound {}", bound));
    }
    Some(format!("{} ({})", prover_name, qualifiers.join(", ")))
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
/// proof mutation is ported.  The emitted redirect URL is
/// `<newIdx>/overview/proof/<lastLemma>` (no trailing segments) — see
/// the inline comment at the redirect site.  This DIVERGES from
/// Haskell `getProverAllR` (`src/Web/Handler.hs:1085`), which advances
/// the target via `nextSmartThyPath thy (TheoryProof (last names) [])`
/// rather than re-emitting the last lemma's proof root.
pub async fn autoprove_all(
    State(state): State<Arc<AppState>>,
    Path((idx, extractor, bound, _raw_path)): Path<(usize, String, usize, String)>,
) -> Response {
    // Match Haskell's Yesod `PathPiece SolutionExtractor`
    // (`src/Web/Types.hs:626-638`): an unrecognised extractor makes
    // `fromPathPiece` return `Nothing`, so Yesod routing 404s before
    // `getAutoProverAllR` runs.  (`getProverAllR` never surfaces the
    // prover `name` to the user — it always redirects — so unlike
    // `autoprove` we only need the validation, not the display name.)
    if autoprover_name(&extractor, bound).is_none() {
        return not_found_response();
    }
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
            lname = path_parse::url_path_escape(&n)),
        None => format!("/thy/trace/{}/overview/help", new_idx),
    };
    json_resp::redirect(target).into_response()
}

/// `GET /thy/trace/<idx>/verify/*path` — returns:
///   - `{redirect}` when the path is `proof/<lemma>/<sub>`, re-pointing
///     navigation at the SAME idx/path.  NOTE: Haskell's
///     `getTheoryVerifyR` (`src/Web/Handler.hs:833-839`) calls
///     `editProof idx l`, which REBUILDS the lemma's proof via
///     `newProof`/`checkAndExtendProver` and `replaceTheory` before
///     redirecting.  The Rust port does NOT yet rebuild the proof; it
///     only re-emits the redirect URL.
///   - `{html,title}` (help-pane fallback) for everything else,
///     mirroring Haskell's `getTheoryPathMR idx TheoryHelp` in the
///     `_` arm of `getTheoryVerifyR`.
///
/// Reference: `src/Web/Handler.hs:833-841`.
pub async fn verify(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx))
            .into_response();
    };
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    match path {
        // The success branch: re-point navigation at the same idx and
        // redirect.  (Haskell `editProof` → `replaceTheory` rebuilds
        // the proof here; the Rust port only redirects — see the
        // handler doc above.)
        path_parse::TheoryPath::Proof { lemma, sub } => {
            // Re-emit the proof path so navigation stays pointed at the
            // same node.  Mirrors Haskell `JsonRedirect` target
            // `/thy/trace/<idx>/overview/proof/<lemma>/...`, which goes
            // through Yesod `getUrlRender` and so percent-encodes each
            // path segment.  Use the shared helpers, identical to
            // `apply_method_and_redirect` (this file): `url_path_escape`
            // on the lemma, `prefixWithUnderscore` + `url_path_escape`
            // on each sub segment.
            let mut url = format!(
                "/thy/trace/{}/overview/proof/{}",
                idx, path_parse::url_path_escape(&lemma));
            for seg in sub {
                url.push('/');
                url.push_str(&path_parse::url_path_escape(
                    &path_parse::prefix_with_underscore(&seg)));
            }
            json_resp::redirect(url).into_response()
        }
        // Help-pane fallback: Haskell falls through to
        // `getTheoryPathMR idx TheoryHelp`, which is the JsonHtml for
        // the help screen.  We piggy-back on `theory_path_main` via a
        // synthesised Help path.
        _ => {
            let help_path = path_parse::TheoryPath::Help;
            let title = format!("Theory: {}", entry.name);
            let body = crate::handlers::theory_html::path_html(&entry, &help_path);
            json_resp::html(title, body).into_response()
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
    // Mirror Haskell `checkReloadOrigin` (`src/Web/Handler.hs:385-388`):
    // two distinct JsonAlert strings for the two non-Local origins.
    let path = match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => p.clone(),
        crate::state::TheoryOrigin::Upload(_) => return json_resp::alert(
            "Cannot reload: theory was uploaded (no file path)"),
        crate::state::TheoryOrigin::Interactive => return json_resp::alert(
            "Cannot reload: theory was created interactively (no file path)"),
    };
    match crate::theory_io::load_from_path(&path, &state.cfg.maude_path) {
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
    // `getDownloadTheoryR` (`src/Web/Handler.hs:1669-1672`) — it
    // returns `(typeOctet, source)` where `source` is the RENDERED
    // in-memory theory (`render . prettyClosedTheory`, via
    // `getTheorySourceR`, `src/Web/Handler.hs:950-957`), so interactive
    // modifications are reflected.  NOTE: the Rust port intentionally
    // diverges here and serves the raw on-disk `.spthy` bytes instead
    // of re-rendering via `pretty_theory::pretty_closed_theory`; this
    // mirrors the sibling `source_` handler which is likewise not yet
    // wired up to render the full theory.
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
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    let new_path = next_theory_path(&path, &section, &entry);
    let url = render_main_url(idx, &new_path);
    text_response(url)
}

/// `GET /thy/trace/<idx>/prev/<section>/*path` — symmetric to `next`.
pub async fn prev_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    let new_path = prev_theory_path(&path, &section, &entry);
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
fn next_theory_path(
    p: &path_parse::TheoryPath,
    section: &str,
    entry: &crate::state::TheoryEntry,
) -> path_parse::TheoryPath {
    // HS `getNextTheoryPathR` (`Handler.hs:1452-1455`): `next "normal" =
    // nextThyPath`, `next "smart" = nextSmartThyPath`, everything else
    // `const id` (no-op).  The two differ ONLY in the `TheoryProof` arm.
    match section {
        "normal" => next_thy_path_inner(p, entry, false),
        "smart" => next_thy_path_inner(p, entry, true),
        _ => p.clone(),
    }
}

fn next_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> path_parse::TheoryPath {
    use path_parse::TheoryPath as T;
    use path_parse::SourceKind;
    let lemmas = lemma_names(entry);
    match p {
        T::Help => T::Message,
        T::Message => T::Rules,
        T::Rules => T::Tactic,
        T::Tactic => T::Source { kind: SourceKind::Raw, src_idx: 0, case_idx: 0 },
        T::Source { kind: SourceKind::Raw, .. } =>
            T::Source { kind: SourceKind::Refined, src_idx: 0, case_idx: 0 },
        // Haskell `nextThyPath` (Web/Theory.hs:1683): refined sources
        // advance to the FIRST lemma's proof root, falling back to Help
        // only when there are no lemmas.
        T::Source { kind: SourceKind::Refined, .. } => match lemmas.first() {
            Some(n) => T::Proof { lemma: n.clone(), sub: Vec::new() },
            None => T::Help,
        },
        T::Lemma(n) => T::Proof { lemma: n.clone(), sub: Vec::new() },
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        // HS `nextThyPath`/`nextSmartThyPath` TheoryProof arm
        // (Web/Theory.hs:1688-1691 / 1900-1903):
        //   | Just nextPath <- getNextPath l p -> TheoryProof l nextPath
        //   | Just nextLemma <- getNextLemma l -> TheoryProof nextLemma []
        //   | otherwise                        -> TheoryProof l p
        T::Proof { lemma, sub } => {
            let paths = lemma_proof_paths(entry, lemma);
            let next = if smart {
                next_smart_path(&paths, sub)
            } else {
                next_element_path(&paths, sub)
            };
            match next {
                Some(np) => T::Proof { lemma: lemma.clone(), sub: np },
                None => match next_after(&lemmas, lemma) {
                    Some(nl) => T::Proof { lemma: nl, sub: Vec::new() },
                    None => p.clone(),
                },
            }
        }
        // HS `path@TheoryMethod{} -> path` (no-op).
        T::Method { .. } => p.clone(),
    }
}

fn prev_theory_path(
    p: &path_parse::TheoryPath,
    section: &str,
    entry: &crate::state::TheoryEntry,
) -> path_parse::TheoryPath {
    match section {
        "normal" => prev_thy_path_inner(p, entry, false),
        "smart" => prev_thy_path_inner(p, entry, true),
        _ => p.clone(),
    }
}

fn prev_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> path_parse::TheoryPath {
    use path_parse::TheoryPath as T;
    use path_parse::SourceKind;
    let lemmas = lemma_names(entry);
    let refined_root = || T::Source { kind: SourceKind::Refined, src_idx: 0, case_idx: 0 };
    match p {
        T::Help => T::Help,
        T::Message => T::Help,
        T::Rules => T::Message,
        T::Tactic => T::Rules,
        T::Source { kind: SourceKind::Raw, .. } => T::Tactic,
        T::Source { kind: SourceKind::Refined, .. } =>
            T::Source { kind: SourceKind::Raw, src_idx: 0, case_idx: 0 },
        // HS `prevThyPath` (Web/Theory.hs:1781-1783):
        //   TheoryLemma l | Just prevLemma <- getPrevLemma l
        //                     -> TheoryProof prevLemma (lastPath prevLemma)
        //                 | otherwise -> TheorySource RefinedSource 0 0
        T::Lemma(n) => match prev_before(&lemmas, n) {
            Some(pl) => {
                let sub = last_path(&lemma_proof_paths(entry, &pl));
                T::Proof { lemma: pl, sub }
            }
            None => refined_root(),
        },
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        // HS `prevThyPath`/`prevSmartThyPath` TheoryProof arm
        // (Web/Theory.hs:1784-1787 / 2001-2005):
        //   | Just prevPath <- getPrevPath l p -> TheoryProof l prevPath
        //   | Just prevLemma <- getPrevLemma l ->
        //         TheoryProof prevLemma (lastPath prevLemma)
        //   | otherwise                        -> TheorySource RefinedSource 0 0
        T::Proof { lemma, sub } => {
            let paths = lemma_proof_paths(entry, lemma);
            let prev = if smart {
                prev_smart_path(&paths, sub)
            } else {
                prev_element_path(&paths, sub)
            };
            match prev {
                Some(pp) => T::Proof { lemma: lemma.clone(), sub: pp },
                None => match prev_before(&lemmas, lemma) {
                    Some(pl) => {
                        let sub = last_path(&lemma_proof_paths(entry, &pl));
                        T::Proof { lemma: pl, sub }
                    }
                    None => refined_root(),
                },
            }
        }
        // HS `path@TheoryMethod{} -> path` (no-op).
        T::Method { .. } => p.clone(),
    }
}

/// Lemma names in declaration order (HS `getLemmas thy`).
fn lemma_names(entry: &crate::state::TheoryEntry) -> Vec<String> {
    entry.typed_theory.lemmas().map(|l| l.name.clone()).collect()
}

/// The proof-path list for a lemma (HS `getProofPaths lemma._lProof`).  When
/// no proof state has been materialised yet (a freshly-loaded theory before
/// any autoprove), the lemma's proof is HS's initial `sorry` skeleton — a
/// single root path — which is exactly what the `next`/`prev` traversal needs
/// (an unproven lemma yields no in-tree next/prev step, only lemma jumps).
fn lemma_proof_paths(
    entry: &crate::state::TheoryEntry,
    lemma: &str,
) -> Vec<(Vec<String>, tamarin_theory::constraint::solver::proof_method::ProofMethod)> {
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    entry
        .proof_state
        .as_ref()
        .and_then(|ps| ps.get_root(lemma))
        .map(|root| crate::handlers::proof_tree::get_proof_paths(&root))
        .unwrap_or_else(|| vec![(Vec::new(), ProofMethod::Sorry(None))])
}

type PathList = [(Vec<String>, tamarin_theory::constraint::solver::proof_method::ProofMethod)];

/// HS `getNextElement (== path) (map fst paths)` — the path immediately after
/// the match; `None` if `sub` is absent or last.
fn next_element_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths.get(i + 1).map(|(p, _)| p.clone())
}

/// HS `nextSmartThyPath.getNextPath`: `dropWhile (/= path)`, then the first of
/// the REMAINING (after the match) whose method `isInterestingMethod`.
fn next_smart_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths[i + 1..]
        .iter()
        .find(|(_, m)| crate::handlers::proof_tree::is_interesting_method(m))
        .map(|(p, _)| p.clone())
}

/// HS `getPrevElement (== path) (map fst paths)` — the path immediately before
/// the match; `None` if `sub` is absent or first.
fn prev_element_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    i.checked_sub(1).map(|j| paths[j].0.clone())
}

/// HS `prevSmartThyPath.getPrevPath`: the LAST interesting-method path among
/// those STRICTLY BEFORE the match (`filter isInteresting . takeWhile (/=)`).
fn prev_smart_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths[..i]
        .iter()
        .rev()
        .find(|(_, m)| crate::handlers::proof_tree::is_interesting_method(m))
        .map(|(p, _)| p.clone())
}

/// HS `lastPath` = `last (map fst (getProofPaths ...))`.  The path list is
/// never empty (always contains the root `[]`), so this is total.
fn last_path(paths: &PathList) -> Vec<String> {
    paths.last().map(|(p, _)| p.clone()).unwrap_or_default()
}

/// HS `getNextElement (== l) names` — the lemma after `cur`.
fn next_after(names: &[String], cur: &str) -> Option<String> {
    let i = names.iter().position(|n| n == cur)?;
    names.get(i + 1).cloned()
}

/// HS `getPrevElement (== l) names` — the lemma before `cur`.
fn prev_before(names: &[String], cur: &str) -> Option<String> {
    let i = names.iter().position(|n| n == cur)?;
    i.checked_sub(1).map(|j| names[j].clone())
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
/// text/plain.  NOTE: the analogous Haskell `/intdot/*` route
/// (`InteractiveDotGraphR`, `src/Web/Types.hs:576`) is handled by
/// `getInteractiveDotGraphR` (`src/Web/Handler.hs:897-906`), which
/// returns an HTML wrapper (`<dot-graph-viz dotsrc=...>`) pointing at
/// the `interactive-graph-def` route, NOT the raw DOT.  Raw DOT is
/// served by `getTheoryInteractiveGraphR` at that
/// `interactive-graph-def` route (`src/Web/Handler.hs:1370-1375`,
/// `notFound` on `Nothing`).  The Rust port returns the raw DOT here
/// directly.
pub async fn intdot(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return missing_idx_html(idx);
    };
    // HS `getInteractiveDotGraphR` (`src/Web/Handler.hs:897`) returns the
    // HTML shell page `intdotLayout` (`src/Web/Types.hs:727-744`): a
    // `<dot-graph-viz>` custom element whose `dotsrc` points at the
    // `interactive-graph-def` route (which serves the raw DOT that the
    // bundled `intdot-graph.es.js` renders client-side).  It does NOT
    // resolve the constraint system itself — the shell is system-agnostic.
    let dotsrc = format!(
        "/thy/trace/{idx}/interactive-graph-def/{path}",
        idx = idx,
        path = raw_path,
    );
    let title = crate::handlers::root::html_escape(&format!("Theory: {}", entry.name));
    // Byte-for-byte reproduction of HS `intdotLayout` (`src/Web/Types.hs:727`),
    // including its doubled `</script></script>` Hamlet quirk — the stray end
    // tag shifts DOM nesting, so matching it verbatim is what makes the
    // semantic gate see the same tree.
    let html = format!(
        "<!DOCTYPE html>\n<html><head>\
         <meta charset=\"UTF-8\" />\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\" />\
         <title>{title}</title>\
         <style> body,html{{width: 100%; height: 100%; overflow: hidden; margin: 0; padding: 0; }}</style>\
         <link rel=\"stylesheet\" href=\"/static/css/intdot-style.css\">\
         <script type=\"module\" src=\"/static/js/intdot-graph.es.js\"></script></script>\
         </head><body><dot-graph-viz dotsrc=\"{dotsrc}\"></dot-graph-viz>\n</body></html>",
        title = title,
        dotsrc = dotsrc,
    );
    html_response(html)
}

/// Build `GraphOptions` from a parsed query map.  Re-uses the same
/// query parameter names as `graph_options_from_query`.
fn graph_options_from_map(
    qs: &HashMap<String, String>,
) -> crate::graph::GraphOptions {
    // Read the parsed map directly via the shared keyed-lookup helper,
    // avoiding a round-trip through a re-serialised `key=value&...` string.
    crate::graph::graph_options_from_params(qs)
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    let sys = match resolve_system_for_path(&state, idx, &path) {
        Some(s) => s,
        // Haskell `getTheoryGraphR` (`src/Web/Handler.hs`) returns a
        // generic `notFound` (404) when `imgThyPath` yields `Nothing` —
        // i.e. the path has no associated system (help / message / rules).
        // There is no placeholder SVG.  The theory `idx` itself exists
        // here, so this is a path-level 404, not a missing-theory page.
        None => return (StatusCode::NOT_FOUND, "Not Found").into_response(),
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
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
        .map(|s| path_parse::unprefix_underscore(&s))
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
    // Install this lemma's per-lemma `use_induction`/`heuristic` into the
    // shared ctx before ranking the re-rendered snippet (HS `getProofContext`).
    let mut ctx_guard = ps.ctx.lock();
    ps.install_lemma_settings(&mut ctx_guard, &lemma);
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
) -> Response {
    let Some(_entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx))
            .into_response();
    };
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found_response();
    };
    match &path {
        // Haskell `removeLemma`-branch.
        path_parse::TheoryPath::Lemma(name) => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            // Haskell `modifyTheory` passes `(const path)` as fpath,
            // i.e. the redirect target is the same path that was
            // deleted (a `TheoryLemma name`).  Render shape:
            // `/thy/trace/<newIdx>/overview/lemma/<name>`.  The URL goes
            // through Yesod `getUrlRender`, so percent-encode the name
            // exactly like `apply_method_and_redirect`'s lemma segment.
            json_resp::redirect(format!(
                "/thy/trace/{}/overview/lemma/{}",
                new_idx, path_parse::url_path_escape(name))).into_response()
        }
        // Haskell `applyProverAtPath ... sorryProver` branch — mark
        // the targeted proof step `sorry`.  Redirect target = same
        // proof path.
        path_parse::TheoryPath::Proof { lemma, sub } => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            // URL goes through Yesod `getUrlRender`; percent-encode each
            // segment via the shared helpers, identical to
            // `apply_method_and_redirect` (this file).
            let mut url = format!(
                "/thy/trace/{}/overview/proof/{}",
                new_idx, path_parse::url_path_escape(lemma));
            for seg in sub {
                url.push('/');
                url.push_str(&path_parse::url_path_escape(
                    &path_parse::prefix_with_underscore(seg)));
            }
            json_resp::redirect(url).into_response()
        }
        _ => json_resp::alert("Can't delete the given theory path!")
            .into_response(),
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
