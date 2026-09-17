#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
examples="$repo_dir/examples/regression/trace"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-sapic-input-validation.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

# These examples must fail validation. A nonzero exit alone could also mean
# an unrelated failure, so check the diagnostic for each rejected input.
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

expect_rejection soundness-sapic-destructor-nonvariable-result \
  'SAPIC destructor equations with non-variable right-hand sides'

echo 'SAPIC input validation rejects the invalid examples with the expected diagnostics.'

# Semantic proofs alone would also pass if pure-state optimization were
# disabled. Check that the supported fragment still uses its optimized fact.
"$tamarin" "$examples/soundness-sapic-state-supported.spthy" \
  --quit-on-warning -d=0 >"$tmp_dir/supported-state.log" 2>&1
# Ignore source-process and metadata comments so only emitted facts count.
awk '/\/\*/ { in_comment = 1 }
     !in_comment { sub(/\/\/.*/, ""); print }
     /\*\// { in_comment = 0 }' "$tmp_dir/supported-state.log" \
  >"$tmp_dir/supported-state-rules.log"
if ! grep -Fq 'L_PureState(' "$tmp_dir/supported-state-rules.log"; then
  echo 'supported SAPIC state did not emit L_PureState' >&2
  exit 1
fi
echo 'Supported SAPIC state emits L_PureState.'
