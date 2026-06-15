# tamarin-prover (Rust port)

In-progress Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/).
The Haskell sources under `../lib/` and `../src/` remain canonical; this
port mirrors them function-for-function, with the goal of **byte-identical
raw `--prove` output** against the Haskell prover.

```
utils → term → parser → theory → {sapic, accountability, export, server} → tamarin-prover
```

## Build

```
cd rust
cargo build --release    # → target/release/tamarin-prover
cargo test               # Rust unit + integration tests
```

The release profile uses `lto = "fat"` and `codegen-units = 1`. The parity
scripts under `scripts/` rebuild the binary themselves before measuring
(set `TAM_RS_NO_AUTO_BUILD=1` to opt out).

## Status

The correctness target is **byte-identical raw `--prove` stdout** (stripping
only the Git-revision, compiled-at, and processing-time lines). Earlier work
matched *canonicalised proof trees*; that metric was retired on 2026-06-10
in favour of raw output equality, which is stricter.

On the comparable-corpus sweep (1015 lemmas, `RS_TIMEOUT=30`,
`--derivcheck-timeout=30`), the latest baseline is **533 MATCH / 20 DIFF**
(2026-06-15); the rest are skipped because the Haskell side itself times out
at the wall-clock cap. The 20 remaining DIFFs are characterised residuals —
mostly cosmetic (variable-index / whitespace) or witness-trace ordering on
exists-trace lemmas — tracked individually; none is a verdict
(verified/falsified) disagreement on a comparable lemma.

## Performance

Figures from a 2026-06 pass on aarch64 Linux (GHC 9.6.7, Maude 3.5.1); they
predate recent solver changes but remain representative of the magnitudes:

- **Single-thread CPU:** ~3.5× faster than HS per thread (geometric mean,
  tiny→xlarge lemmas). Inductive lemmas benefit most — HS times out at 300s
  on `dnp3::authed_sessions_unique`, which RS finishes in ~31s.
- **Memory:** ~0.25× HS's peak RSS (geomean). Most lemmas stay within
  14–50 MB regardless of proof size — Rust frees closed proof branches
  deterministically and mimalloc returns memory to the OS aggressively.
- **Wall-clock (defaults):** RS (`--processors=num_cpus`,
  `--maude-processes=num_cpus/2`) is ~1.3× faster than HS (`+RTS -N`) at
  roughly half the total user CPU.

RS mirrors HS's `parList`/`parMap` sites with rayon (per-rule variants,
source saturation, per-item pretty-print), backed by a pool of independent
Maude subprocesses (`MaudePool`) so parallel calls don't serialise on one
Maude IPC mutex. The pool is an implementation optimisation with no semantic
effect — Maude is a stateless oracle. `--processors=N` sets the worker
count; `--maude-processes=M` sets the pool size.

## Implemented

- **Parser:** full `.spthy` grammar — `macros:`, `predicates:`, `equations:`,
  `restrictions:`, `tactics:`, `#define`/`#include` preprocessing, multi-line
  comments, Unicode symbols.
- **Elaborator:** rule signatures, lemma formulas → guarded form, macro
  expansion, restriction insertion, source-kind classification.
- **Builtins:** `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, `diffie-hellman`, `xor`,
  `bilinear-pairing`, `multiset`, `natural-numbers`, `subterm`,
  `locations-report`, plus custom functions and equations.
- **Solver:** full constraint-system port — simplification, source
  refinement/saturation, chain extension, contradiction detection,
  induction, the smart-rank heuristic and `tactic:` goal rankings, and
  AC-modulo unification via pooled Maude.
- **CLI:** `--prove`, `--lemma`, `--bound`, `--heuristic`, `--saturation`,
  `--open-chains`, `--derivcheck-timeout`, `--auto-sources`, `--oraclename`,
  `--partial-evaluation`, `--parse-only`, `--precompute-only`, `-O/--output`,
  `--quiet`, `-v/--verbose`, `--quit-on-warning`; exit codes and summary
  lines mirror HS.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH intruder-rule
  dump), `test` (install self-check).

## Not yet ported

- **`process:`** — the SAPiC frontend; only channel-rule / source-case
  helpers exist in `tamarin-sapic`, not the full compiler.
- **`predicates:`** — parsed, but typed-layer elaboration is incomplete.
- **`diff(...)` / `--diff`** — observational-equivalence mode.
- Low-severity CLI gaps: `--output-json`/`--output-dot` write stub files;
  `--output-module=proverif|deepsec|…` errors; `--replication-bound` is
  accepted without effect.

Files using these features are excluded from the parity corpus.

## Repository layout

```
crates/
  tamarin-utils/          fresh-ident state, small util types
  tamarin-term/           Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
  tamarin-parser/         .spthy AST + lexer + parser + #include resolver
  tamarin-theory/         elaborator, constraint system, solver, simplify, sources
  tamarin-sapic/          SAPiC channel / source-case helpers (no full frontend)
  tamarin-accountability/ accountability frontend (placeholder)
  tamarin-export/         ProVerif / DeepSec / SPDL export (placeholder)
  tamarin-server/         interactive HTTP server (Axum)
  tamarin-prover/         the binary: CLI parser + run dispatch
scripts/
  diff_proof_raw.sh       per-lemma raw HS↔RS --prove stdout diff (exit 0 = identical)
  corpus_raw_diff.sh      full-corpus raw parity sweep (shared HS cache + timing → RESULTS_TSV)
tests/                    cross-crate integration fixtures
```

## Testing

Parity against Haskell is the correctness gate:

```
cd rust
scripts/diff_proof_raw.sh ../examples/classic/NSPK3.spthy injective_agree   # one lemma
RESULTS_TSV=/tmp/sweep.tsv scripts/corpus_raw_diff.sh                        # full sweep
```

Both rebuild the binary first (set `TAM_RS_NO_AUTO_BUILD=1` to skip). `cargo
test` runs the Rust unit and integration suites.

Lock-step HS-vs-RS Maude command tracing:

```
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify \
  cargo run --release --bin tamarin-prover -- --prove <file>
```

See `crates/tamarin-term/src/maude_proc.rs` for the env-gated trace points.
