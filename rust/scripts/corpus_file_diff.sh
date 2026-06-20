#!/usr/bin/env bash
# Full-FILE raw diff of HS vs RS `--prove <file>` (proves ALL lemmas in the
# file in one invocation — truest byte-identical metric, avoids per-lemma
# source recompute).  Reconstructed 2026-06-20 after the original untracked
# copy was lost; functionally equivalent.
#
# Two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): run HS on every allowlisted file, cache stripped stdout by
#                 sha256(content) under .hs_file_cache/.  JOBS concurrent,
#                 -N$HS_N cores each.  Timeout → .timeout marker; empty/no
#                 output (diff theory / include fragment / error) → .nohs.
#   Phase 2 (RS): run RS on every file, diff against the cached HS output.
#
# Env: FILE_TIMEOUT (per-file cap both sides, default 300s), JOBS (4),
#      HS_N (RTS cores/HS, 4), HS_MAXHEAP (GHC -M g, 11), DERIVCHECK_TIMEOUT
#      (30), CORPUS_ROOT, RESULTS_TSV, ALLOWLIST (file with one rel-path per
#      line; default = derive from $PREV_TSV column 1).
# Output TSV (5 col, tab-sep): relpath  status  HS_lines  RS_lines  diffcount
#   status ∈ MATCH | DIFF | SKIP_HS_TIMEOUT | SKIP_NO_HS | SKIP_RS_TIMEOUT
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
JOBS="${JOBS:-4}"
HS_N="${HS_N:-4}"
HS_MAXHEAP="${HS_MAXHEAP:-11}"
HS_RTS="${HS_RTS:--N$HS_N -M${HS_MAXHEAP}g}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/examples}"
CACHE="${CACHE:-$script_dir/.hs_file_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_file_diff.tsv}"
PREV_TSV="${PREV_TSV:-/tmp/corpus_file_diff.PREV.tsv}"
ALLOWLIST="${ALLOWLIST:-}"
mkdir -p "$CACHE"

find_hs_bin() {
    local root="$1" c
    for c in "$root"/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || { echo "no HS binary" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/rust/target/release/tamarin-prover}"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
export HS_PATH RS_PATH FILE_TIMEOUT DERIVCHECK_TIMEOUT HS_RTS CACHE CORPUS_ROOT

# Strip the volatile header lines from a tamarin run (Git rev / Compiled at /
# processing time / analyzed-path).  Stripping `analyzed:` on BOTH sides means
# no cache path-rewrite is needed.
strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
export -f strip_env

# --- file list (allowlist) ---
filelist() {
    if [ -n "$ALLOWLIST" ] && [ -f "$ALLOWLIST" ]; then
        cat "$ALLOWLIST"
    elif [ -f "$PREV_TSV" ]; then
        cut -f1 "$PREV_TSV"
    else
        echo "no ALLOWLIST and no $PREV_TSV to derive from" >&2; exit 2
    fi
}

# --- Phase 1: HS ---
hs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key out rc
    [ -f "$f" ] || return 0
    key=$(sha256sum "$f" | cut -d' ' -f1)
    [ -f "$CACHE/$key.full.gz" ] && return 0
    [ -f "$CACHE/$key.timeout" ] && return 0
    [ -f "$CACHE/$key.nohs" ] && return 0
    # Run HS to a temp file so we capture `timeout`'s OWN exit code (124 on
    # timeout) — piping straight into strip_env would make $? reflect grep's
    # exit, misclassifying timeouts as empty (SKIP_NO_HS).
    local tmp; tmp=$(mktemp)
    timeout "$FILE_TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS \
            --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$f" >"$tmp" 2>/dev/null
    rc=$?
    out=$(strip_env < "$tmp"); rm -f "$tmp"
    if [ "$rc" = "124" ]; then
        touch "$CACHE/$key.timeout"; echo "  HS TIMEOUT  $rel" >&2
    elif [ -z "$out" ]; then
        touch "$CACHE/$key.nohs"; echo "  HS EMPTY!   $rel" >&2
    else
        printf '%s' "$out" | gzip > "$CACHE/$key.full.gz"
    fi
}
export -f hs_one

# --- Phase 2: RS + diff ---
rs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key hs rs d rc
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; }
    key=$(sha256sum "$f" | cut -d' ' -f1)
    if [ -f "$CACHE/$key.timeout" ]; then printf '%s\tSKIP_HS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    if [ ! -f "$CACHE/$key.full.gz" ]; then printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; fi
    local tmp; tmp=$(mktemp)
    timeout "$FILE_TIMEOUT" "$RS_PATH" --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$f" >"$tmp" 2>/dev/null
    rc=$?
    rs=$(strip_env < "$tmp"); rm -f "$tmp"
    if [ "$rc" = "124" ]; then printf '%s\tSKIP_RS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    hs=$(zcat "$CACHE/$key.full.gz")
    local hsn rsn
    hsn=$(printf '%s\n' "$hs" | wc -l)
    rsn=$(printf '%s\n' "$rs" | wc -l)
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" = "0" ]; then printf '%s\tMATCH\t%s\t%s\t0\n' "$rel" "$hsn" "$rsn"
    else printf '%s\tDIFF\t%s\t%s\t%s\n' "$rel" "$hsn" "$rsn" "$d"; fi
}
export -f rs_one

N=$(filelist | grep -c .)
echo "corpus_file_diff: $N files, JOBS=$JOBS, -N$HS_N, FILE_TIMEOUT=${FILE_TIMEOUT}s, cache=$CACHE"
echo "=== PHASE 1: Haskell (all files first, no RS) ==="
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'hs_one "$@"' _ {}
echo "=== PHASE 2: Rust + diff ==="
: > "$RESULTS_TSV"
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'rs_one "$@"' _ {} >> "$RESULTS_TSV"
sort -o "$RESULTS_TSV" "$RESULTS_TSV"
echo "=== SUMMARY ==="
awk -F'\t' '{c[$2]++} END{for(k in c) printf "  %-18s %d\n", k, c[k]}' "$RESULTS_TSV"
echo "  results: $RESULTS_TSV"
echo "DONE_CORPUS_FILE_DIFF"
