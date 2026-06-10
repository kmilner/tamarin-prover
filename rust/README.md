# tamarin-prover (Rust port)

In-progress Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/).
The Haskell sources under `../lib/` and `../src/` remain canonical;
this port mirrors them function-for-function so proof trees match
byte-for-byte after canonicalisation.

```
utils → term → theory → {sapic, accountability} → export → tamarin-prover
```

## Build

```
cd rust
cargo build --release       # produces target/release/tamarin-prover
cargo test                  # unit + integration tests
```

The release profile uses `lto = "fat"` and `codegen-units = 1`.
Note: `cargo build --release` does NOT rebuild cargo examples — the
measurement scripts depend on `target/release/examples/dump_proof` and
auto-build it themselves; build it explicitly
(`cargo build --release --example dump_proof`) when invoking it directly.

## Status

**Zero known proof-tree divergences against HS** (as of 2026-06-10).
Every comparable lemma produces a byte-identical canonicalised proof
tree, including both `all-traces` and `exists-trace` lemmas, across
all supported builtins — `xor` and `bilinear-pairing` included.

The last measured baseline on the old filtered corpus (276 lemmas,
17 directories) was 238 MATCH / 0 DIFF / 38 SKIP, where every skip is
either an HS-side timeout (heavy jcs18-class inductive proofs that HS
itself can't finish), an HS failure (missing heuristic-oracle file,
HS parse error on embedded proofs), or an HS process killed by memory
pressure. The corpus enumeration has since been expanded to the whole
`../examples/` tree — 11,621 lemmas across 597 comparable files — and
a new baseline sweep is in progress.

## Performance

Numbers below are from a 2026-06 measurement pass on aarch64 Linux
(GHC 9.6.7, Maude 3.5.1); they predate the latest solver changes but
the orders of magnitude hold.

Single-thread (HS `+RTS -N1`, RS `--processors=1`): geomean ~3.5×
faster per thread, ranging from ~2× on large csf17 lemmas to >9× on
dnp3-class inductive proofs (where HS times out at 5 min and RS
finishes in 31 s).

Default-vs-default wall-clock (each prover's out-of-the-box
parallelism, 16-core machine, wireguard benchmark): RS ~1.3× faster
than HS with about half the total user-CPU.

Memory: geomean peak RSS ~25% of HS's. Most lemmas sit at 14–50 MB
regardless of proof size (deterministic drops + mimalloc), where HS's
footprint scales with proof size (csf17::injectivity: 599 MB HS vs
48 MB RS).

### Parallelism

RS mirrors HS's `parList`/`parMap` sites via rayon (HS site → RS site):

- `Prover.hs:195` per-rule variant closure → `populate_rule_variants`
- `Sources.hs:471` saturate refinement → `saturate_sources_with_simp_opt`
- `TheoryObject.hs:744,752` per-item pretty-print → `pretty_closed_theory`

To stop the parallel sites serialising on one Maude subprocess's IPC
mutex, RS keeps a `MaudePool` of independent Maude subprocesses; each
has its own fresh-counter scope so output is byte-identical regardless
of which subprocess serves a call. Knobs: `--processors=N` (rayon
workers, default `num_cpus`) and `--maude-processes=M` (pool size,
default `max(1, processors/2)`; each subprocess holds ~30–100 MB).

## Implemented

- **Parser**: full `.spthy` grammar including `macros:`, `predicates:`,
  `equations:`, `restrictions:`, `tactics:`, `#define`/`#include`
  preprocessor, multi-line comments, Unicode symbols.
- **Elaborator**: rule signatures, lemma formulas → guarded form,
  macro expansion, restriction insertion, source-kind classification.
- **Builtins**: `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, `diffie-hellman`, `xor`,
  `bilinear-pairing`, `multiset`, `natural-numbers`, `subterm`,
  `locations-report`, custom function symbols and equations.
- **Solver**: full constraint-system port with simplify / source-application
  / chain-extension / contradiction-detection / induction.
  Smart-rank heuristic, source-kind reasoning, AC-modulo unification
  via pooled Maude subprocesses, deterministic case enumeration.
- **CLI**: `--prove`, `--lemma`, `--bound`, `--heuristic`, `--saturation`,
  `--open-chains`, `--derivcheck-timeout`, `--auto-sources`,
  `--oraclename`, `--partial-evaluation`, `--parse-only`,
  `--precompute-only`, `--output`/`-O`, `--with-maude`/`-dot`/`-json`,
  `--quiet`, `-v/--verbose`, `--quit-on-warning`, `--diff` (parsed),
  `--output-module` (parsed). Exit codes and summary lines mirror HS.
- **Subcommands**: `interactive` (HTTP server, image rendering),
  `variants` (DH intruder rule dump), `test` (install self-check).

## Not yet ported

- **`process:`** — SAPiC frontend (separate compiler producing rules).
- **`predicates:`** — typed-layer elaboration of predicate items.
- **`diff(...)` / `--diff`** — observational equivalence mode.

Files using these are excluded from the corpus sweep. CLI-level gaps
(low severity): `--output-json`/`--output-dot` write stub files;
`--output-module=proverif|deepsec|...` errors when selected;
`--replication-bound` has no effect; the `test` subcommand runs only
the Maude + GraphViz checks (the unit suite lives in `cargo test`).

## Repository layout

```
crates/
  tamarin-utils/         fresh-ident state, small util types
  tamarin-term/          Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
  tamarin-parser/        .spthy AST + lexer + parser + #include resolver
  tamarin-theory/        elaborator, constraint system, solver, simplify, sources
  tamarin-sapic/         SAPiC AST (no compilation pipeline yet)
  tamarin-accountability/ accountability frontends (placeholder)
  tamarin-export/        ProVerif / DeepSec / SPDL export (placeholder)
  tamarin-server/        interactive HTTP server (Axum)
  tamarin-prover/        the binary + CLI parser + run dispatch
scripts/
  diff_proof_tree.sh        per-lemma HS↔RS proof tree diff
  corpus_full_trace_diff.sh full-corpus parity sweep (HS canon cache + timing)
  canon_proof_tree.py       proof tree canonicaliser (strips display details)
tests/                      cross-crate integration fixtures
```

## Testing

The canonical correctness gate:

```
cd rust
cargo test --release --test oracle_solver corpus_proof_skeleton_match_probe
```

This compares structural proof trees against HS across the corpus.
`scripts/corpus_full_trace_diff.sh` extends it to the full
canonicalised proof text over the whole `../examples/` tree, with an
HS-side result cache and per-lemma timing; both it and
`diff_proof_tree.sh` rebuild `dump_proof` automatically before
measuring.

Per-lemma debugging:

```
scripts/diff_proof_tree.sh examples/classic/NSPK3.spthy injective_agree
```

HS-vs-RS Maude command tracing (lock-step):

```
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify \
  cargo run --release --example dump_proof -- <file> <lemma>
```

See `crates/tamarin-term/src/maude_proc.rs` for the available env-gated
trace points.
