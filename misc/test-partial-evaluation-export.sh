#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-partial-evaluation-export.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

check_verdicts() {
  log=$1
  if [ "$test_case" = collision ]; then
    expected_verdicts='reachable (exists-trace): verified
false_safety (all-traces): falsified'
  else
    expected_verdicts='unreduced_secret (exists-trace): falsified
decrypted_reachable (exists-trace): verified
unreduced_reachable (exists-trace): verified
pruned_family_unreachable (exists-trace): falsified
first_specialization_reachable (exists-trace): verified
second_specialization_reachable (exists-trace): verified
existing_rule_reachable (exists-trace): verified
embedded_restriction_first (exists-trace): verified
embedded_restriction_second (exists-trace): falsified
embedded_restriction_repeated (exists-trace): verified'
  fi
  printf '%s\n' "$expected_verdicts" | while IFS= read -r expected; do
    if ! grep -Fq "$expected" "$log"; then
      echo "missing expected verdict in $log: $expected" >&2
      cat "$log" >&2
      exit 1
    fi
  done
}

run_tamarin() {
  label=$1
  input=$2
  shift 2
  if ! "$tamarin" "$input" --quit-on-warning -d=0 "$@" \
    "-o=$tmp_dir/$label.spthy" >"$tmp_dir/$label.log" 2>&1; then
    cat "$tmp_dir/$label.log" >&2
    exit 1
  fi
}

analyze() {
  run_tamarin "$@"
  check_verdicts "$tmp_dir/$1.log"
}

for test_case in export collision; do
  model="$repo_dir/examples/regression/trace/partial-evaluation-$test_case.spthy"
  analyze original "$model" --prove
  analyze evaluated "$model" --partial-evaluation=summary --prove
  # Export without proofs for a fresh search: --prove on a solved existential
  # proof would also search its remaining, unnecessary branches.
  run_tamarin unproved "$model" --partial-evaluation=summary
  analyze reloaded "$tmp_dir/unproved.spthy" --prove
  analyze replay "$tmp_dir/evaluated.spthy"
  analyze reevaluated "$tmp_dir/unproved.spthy" --partial-evaluation=summary --prove
done

echo "Partial-evaluation export preserves all expected verdicts."
