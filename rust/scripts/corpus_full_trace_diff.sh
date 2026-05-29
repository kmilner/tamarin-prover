#!/bin/bash
# Diff the full canonicalized proof tree (Haskell vs Rust) for EVERY lemma
# across the WHOLE corpus, print a per-lemma diff-line count, and a summary.
#
# This generalizes corpus_diff_proof_trees.sh (which only sweeps a hand-picked
# 8 files / ~23 lemmas) to the full corpus (~118 comparable lemmas) using the
# SAME canonicalized-tree diff (canon_proof_tree.py) as diff_proof_tree.sh.
#
# Corpus enumeration mirrors EXACTLY the cargo test
#   corpus_proof_skeleton_match_probe  (oracle_solver.rs ~L828):
#     root  = /home/parallels/tamarin-prover/examples
#     dirs  = loops csf23-subterms experiments regression ccs15 classic
#             features related_work post17 cav13 jcs18 csf18-alethea
#             csf17 csf12 testParser
#     walk  = max-depth 2, skip /testParser/include/
#     skip files containing: diff(  |  macros:  |  predicates:  |  process:
#       |  (builtins: AND (diffie-hellman|multiset|xor|bilinear-pairing))
#
# Usage:
#   corpus_full_trace_diff.sh                 # full sweep (slow; run later)
#   corpus_full_trace_diff.sh --sample        # tiny built-in sample (validation)
#   corpus_full_trace_diff.sh file1 [file2..] # sweep only the given .spthy files
#
# Env:
#   TIMEOUT=<secs>   per-lemma wall-clock timeout (default 120)
#   JOBS=<n>         parallel lemma workers (default: nproc)
#   EXTRA_ENV="..."  extra env passed to the RS dump_proof binary
#
# Output (stdout): one line per lemma, then a SUMMARY block:
#   <file>::<lemma>: <status> ...
# where <status> is one of:
#   MATCH     diff == 0, both HS and RS produced a non-empty tree
#   DIFF N    diff == N > 0  (HS:H, RS:R)
#   SKIP_*    no HS skeleton / RS error / timeout / parse-empty (NOT a match)
#
# Pre-requisites:
#   - HS tamarin-prover built (auto-discovered, same as diff_proof_tree.sh).
#   - RS binary: rust/target/release/examples/dump_proof
#       (cargo build --example dump_proof --release)
#   - python3 in PATH.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
canon="$script_dir/canon_proof_tree.py"

TIMEOUT="${TIMEOUT:-120}"
JOBS="${JOBS:-$(nproc)}"
EXTRA_ENV="${EXTRA_ENV:-}"
CORPUS_ROOT="${CORPUS_ROOT:-/home/parallels/tamarin-prover/examples}"

# --- Locate the HS binary (first match wins; same logic as diff_proof_tree.sh).
hs_path=""
for c in "$repo_root"/.stack-work/install/*/*/*/bin/tamarin-prover \
         "$repo_root"/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover \
         tamarin-prover; do
    if command -v "$c" >/dev/null 2>&1 || [ -x "$c" ]; then hs_path="$c"; break; fi
done
if [ -z "$hs_path" ]; then
    echo "corpus_full_trace_diff.sh: no HS tamarin-prover binary found" >&2
    exit 2
fi

# --- Locate the RS dump_proof binary.
rs_path="$repo_root/rust/target/release/examples/dump_proof"
if [ ! -x "$rs_path" ]; then rs_path="$repo_root/rust/target/debug/examples/dump_proof"; fi
if [ ! -x "$rs_path" ]; then
    echo "corpus_full_trace_diff.sh: dump_proof not built; run \`cargo build --example dump_proof --release\` in rust/" >&2
    exit 2
fi

# --- Per-lemma worker. Emits ONE machine-parseable line on stdout:
#       <file>\t<lemma>\t<status>\t<hs_lines>\t<rs_lines>\t<diff>
#     status in {MATCH, DIFF, SKIP_NO_HS, SKIP_RS_ERR, SKIP_TIMEOUT}.
#     Designed to be invoked via xargs (one process per lemma) so it must be
#     self-contained and rely only on the exported env below.
worker() {
    local f="$1" lemma="$2"
    local tmp; tmp="$(mktemp -d)"
    # shellcheck disable=SC2064
    trap "rm -rf '$tmp'" RETURN

    # HS: prove just this lemma, slice its proof block out of the rendered theory.
    timeout "$TIMEOUT" "$HS_PATH" +RTS -N1 -RTS --prove="$lemma" "$f" 2>/dev/null > "$tmp/hs.out"
    local hs_rc=$?
    awk -v lem="^lemma ${lemma}( |\\[|:)" '$0 ~ lem {p=1} p && /^lemma / && !($0 ~ lem) {exit} p' \
        "$tmp/hs.out" | python3 "$CANON" > "$tmp/hs.canon" 2>/dev/null

    # RS: dump_proof emits only the proof tree for this lemma.
    timeout "$TIMEOUT" env $EXTRA_ENV "$RS_PATH" "$f" "$lemma" 2>/dev/null | python3 "$CANON" > "$tmp/rs.canon" 2>/dev/null
    local rs_rc=${PIPESTATUS[0]}

    # Count NON-EMPTY lines: the canonicalizer emits a single trailing empty
    # line for a degenerate/absent proof tree (e.g. HS rendered the theory but
    # no proof block, or RS errored), so `wc -l` would report 1, not 0. Using
    # `grep -c .` makes the "empty tree" detection robust.
    local hs_lines rs_lines d
    hs_lines=$(grep -c . "$tmp/hs.canon"); hs_lines=${hs_lines// /}
    rs_lines=$(grep -c . "$tmp/rs.canon"); rs_lines=${rs_lines// /}

    # Classify timeouts first (timeout exits 124).
    if [ "$hs_rc" -eq 124 ] || [ "$rs_rc" -eq 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "$hs_lines" "$rs_lines" "-"
        return 0
    fi
    # HS produced no proof skeleton => not comparable.
    if [ "$hs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_NO_HS" "$hs_lines" "$rs_lines" "-"
        return 0
    fi
    # RS produced nothing (errored / empty) but HS had a tree => RS failure.
    if [ "$rs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_RS_ERR" "$hs_lines" "$rs_lines" "-"
        return 0
    fi

    d=$(diff "$tmp/hs.canon" "$tmp/rs.canon" 2>/dev/null | wc -l); d=${d// /}
    if [ "$d" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "MATCH" "$hs_lines" "$rs_lines" "0"
    else
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "DIFF" "$hs_lines" "$rs_lines" "$d"
    fi
    return 0
}
export -f worker
export HS_PATH="$hs_path" RS_PATH="$rs_path" CANON="$canon" TIMEOUT EXTRA_ENV

# --- File-content filter (mirror corpus_proof_skeleton_match_probe exactly).
file_is_comparable() {
    local f="$1"
    grep -q 'diff('       "$f" 2>/dev/null && return 1
    grep -q 'macros:'     "$f" 2>/dev/null && return 1
    grep -q 'predicates:' "$f" 2>/dev/null && return 1
    grep -q 'process:'    "$f" 2>/dev/null && return 1
    if grep -q 'builtins:' "$f" 2>/dev/null; then
        if grep -Eq 'diffie-hellman|multiset|xor|bilinear-pairing' "$f" 2>/dev/null; then
            return 1
        fi
    fi
    return 0
}

# --- Build the list of candidate files.
declare -a files=()
case "${1:-}" in
    --sample)
        # Tiny built-in sample for validation: a 0-diff lemma file, a known
        # divergent lemma (Responder_secrecy in Typing_and_Destructors), and a
        # file that should be FILTERED OUT (contains builtins multiset/xor/etc).
        for cand in \
            "$CORPUS_ROOT/loops/Typing_and_Destructors.spthy" \
            "$CORPUS_ROOT/classic/NSPK3.spthy"; do
            [ -f "$cand" ] && files+=("$cand")
        done
        # Add one file we EXPECT to be filtered, to exercise the skip path.
        for cand in "$CORPUS_ROOT"/*/*.spthy; do
            if [ -f "$cand" ] && grep -q 'builtins:' "$cand" 2>/dev/null && \
               grep -Eq 'diffie-hellman|multiset|xor|bilinear-pairing' "$cand" 2>/dev/null; then
                files+=("$cand"); break
            fi
        done
        ;;
    "" )
        # Full corpus enumeration (dirs + depth + skip, per the cargo test).
        target_dirs=(loops csf23-subterms experiments regression ccs15 classic \
                     features related_work post17 cav13 jcs18 csf18-alethea \
                     csf17 csf12 testParser)
        for dir in "${target_dirs[@]}"; do
            dpath="$CORPUS_ROOT/$dir"
            [ -d "$dpath" ] || continue
            # max-depth 2 relative to dpath == the dir and one level below.
            while IFS= read -r cand; do
                case "$cand" in */testParser/include/*) continue;; esac
                files+=("$cand")
            done < <(find "$dpath" -maxdepth 2 -name '*.spthy' 2>/dev/null | sort)
        done
        ;;
    *)
        # Explicit file list.
        for cand in "$@"; do [ -f "$cand" ] && files+=("$cand"); done
        ;;
esac

# --- Emit the (file, lemma) task list to a temp file (one per line, TAB-sep),
#     applying the per-file content filter and robust lemma-name extraction.
tasklist="$(mktemp)"
filtered_files=0
total_files=0
for f in "${files[@]}"; do
    total_files=$((total_files+1))
    if ! file_is_comparable "$f"; then
        filtered_files=$((filtered_files+1))
        continue
    fi
    # Robust lemma-name extraction: handles "lemma Foo:", "lemma Foo :",
    # "lemma Foo [attrs]:" AND "lemma Foo[attrs]:" (no space before '[').
    while IFS= read -r lem; do
        [ -n "$lem" ] && printf '%s\t%s\n' "$f" "$lem" >> "$tasklist"
    done < <(grep '^lemma ' "$f" 2>/dev/null | sed -E 's/^lemma[[:space:]]+([A-Za-z0-9_]+).*/\1/')
done

n_tasks=$(wc -l < "$tasklist"); n_tasks=${n_tasks// /}
echo "# corpus_full_trace_diff: $n_tasks lemmas across $((total_files-filtered_files)) files (filtered out $filtered_files of $total_files), JOBS=$JOBS, TIMEOUT=${TIMEOUT}s" >&2

# --- Run all lemmas in parallel; collect raw TAB-separated results.
results="$(mktemp)"
trap "rm -f '$tasklist' '$results'" EXIT
# Feed "file<TAB>lemma" pairs; xargs -P runs `worker file lemma` in parallel.
# -d '\n' so filenames with spaces survive; -n 2 because each line has 2 fields
# already split on the TAB we convert to newline.
tr '\t' '\n' < "$tasklist" | xargs -d '\n' -P "$JOBS" -n 2 bash -c 'worker "$0" "$1"' > "$results"

# --- Sort results deterministically (by file then lemma) and print per-lemma.
sort -t$'\t' -k1,1 -k2,2 "$results" > "$results.sorted"

match=0; diffn=0; skip_no_hs=0; skip_rs_err=0; skip_timeout=0
declare -a divergent=()
while IFS=$'\t' read -r f lem status hs rs d; do
    case "$status" in
        MATCH)        match=$((match+1));        echo "$f::$lem: MATCH (HS:$hs, RS:$rs)";;
        DIFF)         diffn=$((diffn+1));         echo "$f::$lem: $d diff lines (HS:$hs, RS:$rs)"; divergent+=("$d"$'\t'"$f::$lem (HS:$hs, RS:$rs)");;
        SKIP_NO_HS)   skip_no_hs=$((skip_no_hs+1));   echo "$f::$lem: SKIP (no HS skeleton)";;
        SKIP_RS_ERR)  skip_rs_err=$((skip_rs_err+1)); echo "$f::$lem: SKIP (RS produced no tree; HS:$hs)";;
        SKIP_TIMEOUT) skip_timeout=$((skip_timeout+1)); echo "$f::$lem: SKIP (timeout ${TIMEOUT}s)";;
        *)            echo "$f::$lem: SKIP (unknown status '$status')"; skip_no_hs=$((skip_no_hs+1));;
    esac
done < "$results.sorted"
rm -f "$results.sorted"

total=$((match+diffn+skip_no_hs+skip_rs_err+skip_timeout))
echo ""
echo "================ SUMMARY ================"
echo "total lemmas enumerated : $total"
echo "  0 diff (MATCH)        : $match"
echo "  divergent (DIFF)      : $diffn"
echo "  skipped               : $((skip_no_hs+skip_rs_err+skip_timeout))"
echo "      no HS skeleton    : $skip_no_hs"
echo "      RS no tree/err    : $skip_rs_err"
echo "      timeout (${TIMEOUT}s)  : $skip_timeout"
if [ "${#divergent[@]}" -gt 0 ]; then
    echo ""
    echo "divergent lemmas (largest diff first):"
    printf '%s\n' "${divergent[@]}" | sort -t$'\t' -k1,1nr | sed 's/^/  /; s/\t/ diff lines: /'
fi
