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
expect_rejection sapic-typed-binding-reuse 'Variable bound twice: y.'
expect_rejection sapic-nested-call-binding-reuse 'Variable bound twice: y.'

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

# Scope identity is shared by all occurrences, but every explicit annotation
# contributes to its type. Exercise all three pattern-binding constructs.
for construct in input let msr; do
  for pattern in 'x,x:alpha' 'x:alpha,x' 'x:alpha,x:alpha' 'x:alpha,x:beta' 'x:beta,x:alpha'; do
    model="$tmp_dir/annotations.spthy"
    case "$construct" in
      input) process="in(<$pattern>); out(x)" ;;
      let) process="in(y); let <$pattern> = y in out(x)" ;;
      msr) process="[In(<$pattern>)] --> [Out(x)]" ;;
    esac
    printf 'theory PatternAnnotations\nbegin\nprocess: %s\nend\n' "$process" >"$model"
    log_file="$tmp_dir/annotations.log"
    if [ "$construct" = input ]; then
      if "$tamarin" "$model" --output-module=spthytyped --quit-on-warning >"$log_file" 2>&1; then
        echo "accepted repeated input binder: $pattern" >&2
        exit 1
      fi
      grep -Fq 'Invalid pattern:' "$log_file" || { cat "$log_file" >&2; exit 1; }
      continue
    fi
    case "$pattern" in
      *beta*)
        if "$tamarin" "$model" --output-module=spthytyped --quit-on-warning >"$log_file" 2>&1; then
          echo "accepted incompatible $construct annotations: $pattern" >&2
          exit 1
        fi
        if ! grep -Fq 'Typing error: expected term ' "$log_file"; then
          cat "$log_file" >&2
          exit 1
        fi
        ;;
      *)
        "$tamarin" "$model" --output-module=spthytyped --quit-on-warning >"$log_file" 2>&1
        # All three x occurrences (two pattern positions and the output) must
        # carry alpha. Count occurrences, not lines, since pairs share a line.
        count=$(grep -o 'x\.[0-9][0-9]*:alpha' "$log_file" | wc -l)
        if [ "$count" -ne 3 ]; then
          echo "lost compatible $construct annotations: $pattern" >&2
          cat "$log_file" >&2
          exit 1
        fi
        ;;
    esac
  done
done
echo 'SAPIC pattern declarations preserve compatible types and reject conflicts.'

# Inputs retain their existing linear-pattern requirement. A distinct typed
# binder and untyped sibling remain supported in either order.
for pattern in 'x:alpha,y' 'y,x:alpha'; do
  printf 'theory LinearInput\nbegin\nprocess: in(<%s>); out(x)\nend\n' "$pattern" >"$tmp_dir/linear.spthy"
  "$tamarin" "$tmp_dir/linear.spthy" --output-module=spthytyped --quit-on-warning >"$tmp_dir/linear.log" 2>&1
  count=$(grep -o 'x\.[0-9][0-9]*:alpha' "$tmp_dir/linear.log" | wc -l)
  [ "$count" -eq 2 ] || { cat "$tmp_dir/linear.log" >&2; exit 1; }
done

# An annotation change must not disguise a match/bind collision.
for construct in input msr; do
  case "$construct" in
    input) process='in(<x:alpha,=x:beta>); out(x)' ;;
    msr) process='[In(<x:alpha,=x:beta>)] --> [Out(x)]' ;;
  esac
  printf 'theory MatchBindCollision\nbegin\nprocess: %s\nend\n' "$process" >"$tmp_dir/collision.spthy"
  if "$tamarin" "$tmp_dir/collision.spthy" --output-module=spthytyped --quit-on-warning >"$tmp_dir/collision.log" 2>&1; then
    echo "accepted $construct match/bind collision" >&2
    exit 1
  fi
  grep -Fq 'Invalid pattern' "$tmp_dir/collision.log" || { cat "$tmp_dir/collision.log" >&2; exit 1; }
done

# A binder must not make an otherwise unbound channel, lookup key, let RHS,
# or failure continuation well formed during uniqueness renaming. Check both
# exports: typed source runs the same binding/typing pipeline as translation.
for process in \
  'in(x,x); out(x)' \
  'lookup x as x in out(x)' \
  "lookup 'key' as x in out(x) else out(x)" \
  'let x = x in out(x)' \
  "let x = 'ok' in out(x) else out(x)"; do
  printf 'theory BinderScope\nbegin\nprocess: %s\nend\n' "$process" >"$tmp_dir/scope.spthy"
  for mode in spthytyped msr; do
    if "$tamarin" "$tmp_dir/scope.spthy" --output-module="$mode" --quit-on-warning -d=0 >"$tmp_dir/scope.log" 2>&1; then
      echo "accepted out-of-scope occurrence: $process ($mode)" >&2
      exit 1
    fi
    grep -Fq 'not bound' "$tmp_dir/scope.log" || { cat "$tmp_dir/scope.log" >&2; exit 1; }
  done
done

# Independent success/failure binders may reuse a spelling and have different
# types. Matching occurrences remain references to the outer typed variable.
for process in \
  'in(y); let x:alpha = y in out(x) else in(x:beta); out(x)' \
  "in(y); lookup 'key' as x in out(<x,y>) else in(x); out(<x,y>)" \
  "in(y:alpha); let <x,=y> = <'ok',y> in out(<x,y>) else in(x); out(<x,y>)" \
  "in(y:alpha); in(<x,=y>); out(<x,y>)"; do
  printf 'theory IndependentBinders\nbegin\nprocess: %s\nend\n' "$process" >"$tmp_dir/scoped.spthy"
  for mode in spthytyped msr; do
    "$tamarin" "$tmp_dir/scoped.spthy" --output-module="$mode" --quit-on-warning -d=0 >"$tmp_dir/scoped.log" 2>&1
  done
done
echo 'SAPIC uniqueness renaming preserves binder scope and independent branch types.'
