# tamarin-prover (Rust port)

In-progress Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/).
The Haskell sources under `../lib/` and `../src/` remain canonical;
this port mirrors them function-for-function so that proof trees match
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
Note that `cargo build --release` does not rebuild cargo examples: the
measurement scripts depend on `target/release/examples/dump_proof` and
rebuild it themselves before measuring; when invoking the example
directly, build it explicitly with
`cargo build --release --example dump_proof`.

## Status

**Zero known proof-tree divergences against the Haskell prover**
(as of 2026-06-10). Every comparable lemma produces a byte-identical
canonicalised proof tree, for both `all-traces` and `exists-trace`
lemmas, across all supported builtins — including `xor` and
`bilinear-pairing`.

The most recent measured baseline, taken on the earlier filtered
corpus (276 lemmas across 17 directories), was 238 MATCH / 0 DIFF /
38 SKIP. Each skip is attributable to the Haskell side rather than to
a divergence: a timeout on heavy inductive proofs (jcs18-class lemmas
that HS itself cannot finish within the wall-clock cap), a hard
failure (a missing heuristic-oracle file; a parse error on embedded
proof scripts), or a process terminated under memory pressure. The
corpus enumeration has since been expanded to the entire
`../examples/` tree — 11,621 lemmas across 597 comparable files — and
a baseline sweep over the expanded corpus is in progress.

## Performance

The figures below are from a 2026-06 measurement pass on aarch64
Linux (GHC 9.6.7, Maude 3.5.1). They predate the most recent solver
changes and will be refreshed in a future pass; the orders of
magnitude remain representative.

### Single-thread (per-thread CPU efficiency)

HS was run with `+RTS -N1 -RTS`; RS with `--processors=1`. Times in
seconds; speedup = HS / RS.

| lemma | tier | HS `-N1` | RS `-p1` | speedup |
|---|---|---:|---:|---:|
| Tutorial::Client_session_key_secrecy | tiny | 0.19 | 0.02 | 9.5× |
| NSPK3::nonce_secrecy | small | 1.39 | 0.34 | 4.1× |
| NSLPK3::injective_agree | small | 1.22 | 0.23 | 5.4× |
| KAS2_eCK::eCK_key_secrecy | medium | 1.95 | 0.67 | 2.9× |
| KAS2_original::KAS_key_secrecy | medium | 3.39 | 1.42 | 2.4× |
| TESLA::authentic | medium | 2.66 | 0.78 | 3.4× |
| counter::counters_linear_order | medium | 0.21 | 0.07 | 3.1× |
| matching_detects_prior_misuse | large | 2.17 | 0.48 | 4.5× |
| csf17::detect_sound | large | 3.18 | 0.92 | 3.5× |
| csf17::count_unique | large | 4.21 | 1.36 | 3.1× |
| csf17::sessions_injective | large | 8.46 | 4.97 | 1.7× |
| csf17::injectivity | large | 19.05 | 9.69 | 2.0× |
| dnp3::countervalue_uniqueness | xlarge | 15.67 | 1.10 | 14.3× |
| dnp3::authed_sessions_unique | xlarge | TO(300s) | 31.34 | >9.6× |

The geometric mean of the speedups is approximately 3.5× per thread.
Inductive lemmas benefit the most: HS exceeds a five-minute timeout on
dnp3::authed_sessions_unique, which RS completes in 31 seconds.

### Default-vs-default (wall-clock)

Each prover was run with its default parallelism settings: HS uses
`+RTS -N` (all cores, parallel GC, the `parList` sites in
`lib/theory`); RS defaults to `--processors=num_cpus` workers backed
by `--maude-processes=max(1, num_cpus/2)` Maude subprocesses.
Measured on the wireguard benchmark (`--prove=exists_session`;
hashing and Diffie–Hellman, 10 rules, 8 lemmas) on a 16-core machine:

| | wall | user CPU |
|---|---:|---:|
| HS default (`+RTS -N`) | 8.8s | 17.1s |
| HS `+RTS -N1` | 11.3s | 10.4s |
| RS `--processors=1` | 8.9s | 8.4s |
| RS `--processors=4 --maude-processes=2` | 7.5s | 8.5s |
| RS `--processors=8 --maude-processes=4` | 6.9s | 8.6s |
| RS `--processors=16 --maude-processes=8` (default on 16 cores) | 6.8s | 8.7s |

The RS default is approximately 1.3× faster in wall-clock time than
the HS default, at roughly half the total user CPU. The scaling curve
flattens near `processors=8` on this benchmark because the protocol
exposes only enough parallel work (10 per-rule variant items, ~8
saturate items) to occupy about eight workers; larger theories scale
further.

### Memory

Peak resident set size on the same lemma set:

| lemma | tier | HS (MB) | RS (MB) | ratio |
|---|---|---:|---:|---:|
| NSPK3::nonce_secrecy | small | 65.3 | 13.1 | 0.20× |
| KAS2_eCK | medium | 109.4 | 17.3 | 0.16× |
| TESLA::authentic | medium | 125.3 | 14.8 | 0.12× |
| counter::counters_linear_order | medium | 45.4 | 13.7 | 0.30× |
| csf17::detect_sound | large | 107.3 | 18.0 | 0.17× |
| csf17::count_unique | large | 173.2 | 16.6 | 0.10× |
| csf17::sessions_injective | large | 455.4 | 30.0 | 0.07× |
| csf17::injectivity | large | 599.4 | 47.9 | 0.08× |
| dnp3::countervalue_uniqueness | xlarge | 391.5 | 34.9 | 0.09× |

The geometric mean of the ratios is approximately 0.25 — one quarter
of HS's peak. Most lemmas remain within 14–50 MB irrespective of
proof size, whereas HS's footprint grows with the proof: Rust frees
closed proof-tree branches deterministically, and mimalloc returns
memory to the operating system more aggressively than GHC's runtime,
which retains a contiguous heap by design.

### Parallelism

RS mirrors HS's `parList`/`parMap` evaluation sites with rayon
(HS site → RS site):

- `Prover.hs:195` per-rule variant closure → `populate_rule_variants`
- `Sources.hs:471` saturate refinement → `saturate_sources_with_simp_opt`
- `TheoryObject.hs:744,752` per-item pretty-print → `pretty_closed_theory`

To prevent these sites from serialising on a single Maude
subprocess's IPC mutex, RS maintains a pool of independent Maude
subprocesses (`MaudePool`); each subprocess carries its own
fresh-counter scope, so output is byte-identical regardless of which
subprocess serves a given call. The pool is a Rust-side implementation
optimisation with no semantic effect: Maude is a stateless query
oracle in HS as well.

Configuration: `--processors=N` sets the rayon worker count (default:
`num_cpus`); `--maude-processes=M` sets the pool size (default:
`max(1, processors/2)`). Each pooled subprocess holds roughly
30–100 MB resident on realistic protocols, so memory-constrained
deployments may wish to lower the pool size.

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
- **Solver**: full constraint-system port with simplification,
  source application, chain extension, contradiction detection, and
  induction; the smart-rank heuristic, source-kind reasoning,
  AC-modulo unification via pooled Maude subprocesses, and
  deterministic case enumeration.
- **CLI**: `--prove`, `--lemma`, `--bound`, `--heuristic`, `--saturation`,
  `--open-chains`, `--derivcheck-timeout`, `--auto-sources`,
  `--oraclename`, `--partial-evaluation`, `--parse-only`,
  `--precompute-only`, `--output`/`-O`, `--with-maude`/`-dot`/`-json`,
  `--quiet`, `-v/--verbose`, `--quit-on-warning`, `--diff` (parsed),
  `--output-module` (parsed). Exit codes and summary lines mirror HS.
- **Subcommands**: `interactive` (HTTP server, image rendering),
  `variants` (DH intruder rule dump), `test` (install self-check).

## Not yet ported

- **`process:`** — the SAPiC frontend (a separate compiler producing rules).
- **`predicates:`** — typed-layer elaboration of predicate items.
- **`diff(...)` / `--diff`** — observational-equivalence mode.

Files using these features are excluded from the corpus sweep.
CLI-level gaps of low severity: `--output-json`/`--output-dot` write
stub files; `--output-module=proverif|deepsec|...` errors when
selected; `--replication-bound` is accepted without effect; the
`test` subcommand runs only the Maude and GraphViz checks (the unit
suite is covered by `cargo test`).

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
`scripts/corpus_full_trace_diff.sh` extends the comparison to the full
canonicalised proof text over the entire `../examples/` tree, with an
HS-side result cache and per-lemma timing; both it and
`diff_proof_tree.sh` rebuild the `dump_proof` example automatically
before measuring.

Per-lemma debugging:

```
scripts/diff_proof_tree.sh examples/classic/NSPK3.spthy injective_agree
```

HS-vs-RS Maude command tracing (lock-step):

```
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify \
  cargo run --release --example dump_proof -- <file> <lemma>
```

See `crates/tamarin-term/src/maude_proc.rs` for the available
environment-gated trace points.
