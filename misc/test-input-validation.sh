#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
examples="$repo_dir/examples/regression/trace"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-input-validation.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

# These examples are supposed to fail validation. A proof-result comparison
# cannot check that behavior, and an unrelated error must not count as a pass.
expect_rejection() {
  model=$1
  diagnostic=$2
  log_file="$tmp_dir/$model.log"
  if "$tamarin" "$examples/$model.spthy" --quit-on-warning -d=0 >"$log_file" 2>&1; then
    echo "expected validation to reject $model" >&2
    cat "$log_file" >&2
    exit 1
  fi
  if ! grep -Fq "$diagnostic" "$log_file"; then
    echo "missing expected diagnostic for $model: $diagnostic" >&2
    cat "$log_file" >&2
    exit 1
  fi
}

expect_rejection soundness-dh-action-multiplication \
  'The following rule is not multiplication restricted:'
expect_rejection soundness-dh-nested-action-multiplication \
  'The following rule is not multiplication restricted:'
expect_rejection soundness-manual-variants-incomplete \
  'cannot confirm manual variants:'

# A complete family in a different order, with added actions, remains valid.
if ! "$tamarin" "$examples/soundness-manual-variants-complete.spthy" \
  --quit-on-warning -d=0 >"$tmp_dir/complete.log" 2>&1; then
  echo 'expected the complete annotated variant family to be accepted' >&2
  cat "$tmp_dir/complete.log" >&2
  exit 1
fi

echo 'Input validation rejects the invalid examples and accepts the complete variant family.'
