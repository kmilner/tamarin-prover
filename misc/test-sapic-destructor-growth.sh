#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
tamarin=${TAMARIN:-tamarin-prover}
tmp_file=$(mktemp "${TMPDIR:-/tmp}/tamarin-sapic-destructor-growth.XXXXXX")
trap 'rm -f "$tmp_file"' EXIT HUP INT TERM

# Eight root-pattern lets in successive else branches used to emit 2,299
# rules. Allow a generous linear budget (currently 36), independently of
# proof success, which alone would not detect continuation duplication.
"$tamarin" "$repo_dir/examples/regression/trace/soundness-sapic-destructor-failure-chain.spthy" \
  --quit-on-warning -d=0 >"$tmp_file"
rules=$(grep -c '^rule ' "$tmp_file")
if [ "$rules" -gt 52 ] || [ "$rules" -lt 8 ]; then
  echo "unexpected rule count for eight root-pattern lets: $rules (expected 8..52)" >&2
  exit 1
fi
echo "SAPIC root-pattern continuation growth: $rules rules (within linear budget)."

# Proper-subterm evaluations must share the same failure continuation too.
# Eight stages formerly exceeded a 50-second translation timeout.
"$tamarin" "$repo_dir/examples/regression/trace/soundness-sapic-nested-destructor-failure-chain.spthy" \
  --quit-on-warning -d=0 >"$tmp_file"
rules=$(grep -c '^rule ' "$tmp_file")
if [ "$rules" -gt 60 ] || [ "$rules" -lt 8 ]; then
  echo "unexpected rule count for eight nested-destructor lets: $rules (expected 8..60)" >&2
  exit 1
fi
echo "SAPIC nested-destructor continuation growth: $rules rules (within linear budget)."

# Unary chains need only the current intermediate result. Count fact arity,
# not just rules: retaining every old result has quadratic total payload.
# Keep depths small because inherited custom-function typing revisits children.
for depth in 4 8 10; do
  term="'ok'"
  n=0
  while [ "$n" -lt "$depth" ]; do
    term="d(c($term))"
    n=$((n + 1))
  done
  model="$tmp_file.spthy"
  trap 'rm -f "$tmp_file" "$tmp_file.spthy"' EXIT HUP INT TERM
  printf 'theory StageLiveness\nbegin\nfunctions: d/1 [destructor], c/1\nequations: d(c(x)) = x\nprocess: let x = %s in event Done(x) else event Fail()\nend\n' "$term" >"$model"
  "$tamarin" "$model" --quit-on-warning -d=0 >"$tmp_file"
  awk '
    /\/\*/ { comment = 1 }
    !comment {
      line = $0
      while (length(line)) {
        if (!level) {
          if (!match(line, /Let_[0-9]+\(/)) break
          line = substr(line, RSTART + RLENGTH)
          level = 1; arity = 1; facts++
        }
        ch = substr(line, 1, 1); line = substr(line, 2)
        if (ch == "(") level++
        if (ch == ")") level--
        if (ch == "," && level == 1) arity++
        if (!level && arity > maximum) maximum = arity
      }
    }
    /\*\// { comment = 0 }
    END {
      if (facts == 0 || maximum > 2) {
        print "unexpected unary Let fact arity: " maximum > "/dev/stderr"
        exit 1
      }
      print "SAPIC unary stage payload: maximum Let fact arity " maximum
    }' "$tmp_file"
done
