#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
model="$repo_dir/examples/regression/trace/partial-evaluation-export.spthy"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-partial-evaluation-export.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

check_verdicts() {
  log=$1
  for expected in \
    'unreduced_secret (exists-trace): falsified' \
    'decrypted_reachable (exists-trace): verified' \
    'unreduced_reachable (exists-trace): verified' \
    'specialized_rule_reachable (exists-trace): verified'; do
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

analyze original "$model" --prove
analyze evaluated "$model" --partial-evaluation=summary --prove
# Export without proofs for a fresh search: --prove on a solved existential
# proof would also search its remaining, unnecessary branches.
run_tamarin unproved "$model" --partial-evaluation=summary
analyze reloaded "$tmp_dir/unproved.spthy" --prove
analyze replay "$tmp_dir/evaluated.spthy"
analyze reevaluated "$tmp_dir/unproved.spthy" --partial-evaluation=summary --prove

echo "Partial-evaluation export preserves all expected verdicts."
