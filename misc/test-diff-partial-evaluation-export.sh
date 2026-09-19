#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
examples="$repo_dir/examples/regression/trace"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-diff-partial-evaluation-export.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

check_verdicts() {
  log=$1
  # Include the side as well as the lemma name, but ignore proof-step counts.
  sed -n -E 's/^  ((LHS|RHS) : .*|DiffLemma: .*) \([0-9]+ steps\)$/\1/p' \
    "$log" | LC_ALL=C sort >"$tmp_dir/actual"
  LC_ALL=C sort "$tmp_dir/expected" >"$tmp_dir/sorted-expected"
  if ! diff -u "$tmp_dir/sorted-expected" "$tmp_dir/actual"; then
    cat "$log" >&2
    exit 1
  fi
}

run_tamarin() {
  run_label=$1
  run_input=$2
  shift 2
  case "$model" in
    unrelated-empty-*) set -- --bound=10 "$@" ;;
  esac
  if [ "$model" = explicit ]; then
    set -- --bound=6 "$@"
  fi
  if [ "$model" = auto-sources ]; then
    set -- --bound=6 --auto-sources "$@"
  fi
  if ! "$tamarin" "$run_input" --diff --quit-on-warning -d=0 "$@" \
    "-o=$tmp_dir/$run_label.spthy" >"$tmp_dir/$run_label.log" 2>&1; then
    cat "$tmp_dir/$run_label.log" >&2
    exit 1
  fi
}

analyze() {
  run_tamarin "$@"
  check_verdicts "$tmp_dir/$1.log"
}

for model in refinement variants explicit asymmetric singleton families auto-sources explicit-macros empty-left empty-right empty-both unrelated-empty-left unrelated-empty-right unrelated-empty-both; do
  input="$examples/soundness-diff-partial-evaluation-$model.spthy"
  case "$model" in
    unrelated-empty-*)
      input="$examples/diff-$model.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  setup (exists-trace): verified
RHS :  setup (exists-trace): verified
LHS :  finish (exists-trace): verified
RHS :  finish (exists-trace): verified
LHS :  dead (all-traces): verified
RHS :  dead (all-traces): verified
DiffLemma:  D : verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    explicit-macros)
      input="$examples/diff-explicit-side-macros.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  emitted (exists-trace): verified
RHS :  emitted (exists-trace): verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    empty-left)
      input="$examples/diff-empty-left-family.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
RHS :  output (exists-trace): verified
LHS :  no_output (all-traces): verified
DiffLemma:  Observational_equivalence : falsified - found trace
VERDICTS
      ;;
    empty-right)
      input="$examples/diff-empty-right-family.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  output (exists-trace): verified
RHS :  no_output (all-traces): verified
DiffLemma:  Observational_equivalence : falsified - found trace
VERDICTS
      ;;
    empty-both)
      input="$examples/diff-empty-both-families.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  no_output (all-traces): verified
RHS :  no_output (all-traces): verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    refinement)
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  both (exists-trace): verified
RHS :  both (exists-trace): verified
LHS :  annotations (exists-trace): verified
RHS :  annotations (exists-trace): verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    explicit)
      input="$examples/diff-explicit-variant-export.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  unreduced_secret (exists-trace): falsified - no trace found
RHS :  unreduced_secret (exists-trace): falsified - no trace found
LHS :  decrypted_reachable (exists-trace): verified
RHS :  decrypted_reachable (exists-trace): verified
LHS :  unreduced_reachable (exists-trace): verified
RHS :  unreduced_reachable (exists-trace): verified
DiffLemma:  Observational_equivalence : analysis incomplete
VERDICTS
      ;;
    asymmetric)
      input="$examples/diff-asymmetric-explicit-variants.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  unreduced_plain (exists-trace): falsified - no trace found
LHS :  decrypted_reachable (exists-trace): verified
LHS :  unreduced_reachable (exists-trace): verified
RHS :  echo_reachable (exists-trace): verified
DiffLemma:  Observational_equivalence : falsified - found trace
VERDICTS
      ;;
    variants)
      echo 'DiffLemma:  Observational_equivalence : falsified - found trace' >"$tmp_dir/expected"
      ;;
    singleton)
      input="$examples/diff-singleton-trivial-variants.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  both_reachable (exists-trace): verified
RHS :  both_reachable (exists-trace): verified
LHS :  left_reachable (exists-trace): verified
RHS :  left_reachable (exists-trace): verified
LHS :  right_reachable (exists-trace): verified
RHS :  right_reachable (exists-trace): verified
LHS :  automatic_reachable (exists-trace): verified
RHS :  automatic_reachable (exists-trace): verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    families)
      input="$examples/diff-variant-family-roundtrip.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  loop_reachable (exists-trace): verified
RHS :  loop_reachable (exists-trace): verified
LHS :  impossible_unreachable (all-traces): verified
RHS :  impossible_unreachable (all-traces): verified
LHS :  reduced_reachable (exists-trace): verified
RHS :  reduced_reachable (exists-trace): verified
LHS :  variant_action_reachable (exists-trace): verified
RHS :  variant_action_reachable (exists-trace): verified
DiffLemma:  Observational_equivalence : verified
VERDICTS
      ;;
    auto-sources)
      input="$examples/diff-auto-source-variable-alignment.spthy"
      cat >"$tmp_dir/expected" <<'VERDICTS'
LHS :  AUTO_typing_LHS (all-traces): analysis incomplete
RHS :  AUTO_typing_RHS (all-traces): analysis incomplete
DiffLemma:  Observational_equivalence : analysis incomplete
VERDICTS
      ;;
  esac
  analyze original "$input" --prove
  # Exercise ordinary printing as well as the partial-evaluation exporter.
  run_tamarin printed "$input"
  analyze printed-reloaded "$tmp_dir/printed.spthy" --prove
  analyze printed-replay "$tmp_dir/original.spthy"
  # Force analysis rendering on every shape. It preserves all compiled rules;
  # representative family and actual auto-source cases cover the full extra
  # proof/export/reload/replay sequence.
  run_tamarin unproved "$input" --partial-evaluation=summary
  case "$model" in
    families|auto-sources)
      analyze evaluated "$input" --partial-evaluation=summary --prove
      analyze reloaded "$tmp_dir/unproved.spthy" --prove
      analyze replay "$tmp_dir/evaluated.spthy"
      analyze reevaluated "$tmp_dir/unproved.spthy" --partial-evaluation=summary --prove
      ;;
  esac
done

echo 'Diff partial-evaluation export preserves all expected verdicts.'
