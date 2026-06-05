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
cargo test                  # 437 unit + integration tests
```

The release profile uses `lto = "fat"` and `codegen-units = 1`;
expect ~40s for a clean release build.

## Status

Verified against the Haskell prover on 238 lemmas across the corpus
in `../examples/` (15 directories, 14 supported builtins):

```
classic       14/14   loops        40/45   csf12         6/9    cav13         0/1
regression    13/17   features     13/13   post17       11/12   testParser    7/7
csf17         50/50   ccs15         0/0    related_work 27/34   csf23-subterms 6/6
experiments    8/15   jcs18        43/70   csf18-alethea 0/1
                                           TOTAL    238 MATCH / 0 DIFF / 56 SKIP
```

Every comparable lemma is byte-identical (canonicalised) to HS's proof
tree. Both `all-traces` (safety) and `exists-trace` (witness) lemmas
are fully implemented — e.g. `NSPK3::session_key_setup_possible`
(exists-trace) matches HS at `verified (5 steps)` with identical
proof skeleton.

The 56 skips break down as:

- **24 timeouts at 900s** — HS itself times out on these
  (jcs18-class inductive proofs that HS can't finish in 15 min either).
- **17 filtered** by unsupported builtins (xor, bilinear-pairing,
  observational equivalence — see "Not yet ported" below).
- **15 "no HS skeleton"** — a mix of: lemmas inside `/* */` block
  comments that RS over-elaborates and HS skips (parser bug in RS);
  slow HS proofs categorised as "no skeleton" when HS emits a
  partial-but-unparseable output before the script's wall-clock cap;
  lemmas with wellformedness errors HS refuses to prove.  None are
  exists-trace specific.

## Performance

Two benchmark scenarios — single-thread per-thread CPU comparison
(HS `+RTS -N1` constrained), and default-vs-default wall-clock (each
prover with its out-of-the-box parallelism settings).

### Single-thread (per-thread CPU efficiency)

Measured on aarch64 Linux, GHC 9.6.7 + Maude 3.5.1. HS run with
`+RTS -N1 -RTS`; RS with `--processors=1`. Times in seconds; speedup
= HS / RS.

| lemma | tier | HS `-N1` | RS `-p1` | speedup |
|---|---|---:|---:|---:|
| Tutorial::Client_session_key_secrecy | tiny | 0.19 | 0.02 | **9.5×** |
| NSPK3::nonce_secrecy | small | 1.39 | 0.34 | **4.1×** |
| NSLPK3::injective_agree | small | 1.22 | 0.23 | **5.4×** |
| KAS2_eCK::eCK_key_secrecy | medium | 1.95 | 0.67 | **2.9×** |
| KAS2_original::KAS_key_secrecy | medium | 3.39 | 1.42 | **2.4×** |
| TESLA::authentic | medium | 2.66 | 0.78 | **3.4×** |
| counter::counters_linear_order | medium | 0.21 | 0.07 | **3.1×** |
| matching_detects_prior_misuse | large | 2.17 | 0.48 | **4.5×** |
| csf17::detect_sound | large | 3.18 | 0.92 | **3.5×** |
| csf17::count_unique | large | 4.21 | 1.36 | **3.1×** |
| csf17::sessions_injective | large | 8.46 | 4.97 | **1.7×** |
| csf17::injectivity | large | 19.05 | 9.69 | **2.0×** |
| dnp3::countervalue_uniqueness | xlarge | 15.67 | 1.10 | **14.3×** |
| dnp3::authed_sessions_unique | xlarge | TO(300s) | 31.34 | >9.6× |

Geomean ~3.5× faster per thread. Inductive lemmas favour RS most
(HS times out on dnp3 at 5 min where RS finishes in 31s).

### Default-vs-default (wall-clock as the user would experience)

HS uses `+RTS -N` by default (all cores + parallel GC + `parList`
sites in lib/theory). RS defaults to `--processors=min(num_cpus, 4)`,
mirroring HS's parallelism sites via rayon (rule-variant closure,
saturate refinement, per-item pretty-print — see "Parallelism" below).
Spot check on the parallelism-friendly wireguard benchmark
(`--prove=exists_session`, hashing + DH, 10 rules, 8 lemmas):

| | wall | user CPU |
|---|---:|---:|
| HS default (`+RTS -N`) | 8.8s | 17.1s |
| HS `+RTS -N1` | 11.3s | 10.4s |
| RS default (`--processors=4`) | **7.0s** | 8.6s |
| RS `--processors=1` | 8.9s | 8.4s |

RS default is ~1.25× faster wall-clock than HS default, with ~half
the total user-CPU. The gap widens on multi-lemma theories (parallel
rule-variant closure scales linearly with rule count) and narrows on
single-lemma theories (HS's gain there is parallel GC, which Rust
doesn't need).

### What drives the speedup

Stack of perf commits:

| | what | gain |
|---|---|---|
| 1 | empty-result cache for `match_eqs_const_subject` | 1.22–1.49× on AC-heavy lemmas |
| 2 | skip Maude when no AC operators present | another 1.07–1.28× (drives match calls to 0) |
| 3 | mimalloc global allocator (including the binary itself) | 1.5–2× across the board |
| 4 | fat LTO + codegen-units=1 | another 1.13–1.19× |
| 5 | drop System from ProofNodes after expand | wall-clock unchanged; memory: see below |
| 6 | hoist `ensure_saturated` out of per-variable deriv-check loop | 3.4× on deriv check (mirrors HS's once-per-theory `closeTheoryWithMaude`) |
| 7 | HS-faithful rayon parallelism at 3 sites (variants / saturate / pretty-print) | 1.25× on multi-rule theories at default `--processors=4` |

### Parallelism

RS mirrors HS's `using parList rdeepseq` and `parMap rdeepseq` sites via
rayon at three places (HS site → RS site):

- `Prover.hs:195` per-rule variant closure → `populate_rule_variants` in `run.rs`
- `Sources.hs:471` saturate refinement change detection → `saturate_sources_with_simp_opt`
- `TheoryObject.hs:744,752` per-item pretty-print → `pretty_closed_theory`

`Proof.hs:873`'s `parTraversable nfProofMethod` (forcing a `Map` of lazy
proof sub-trees in `cutOnSolvedDFS`) is skipped: RS's proof tree is
already strict, there's nothing to force in parallel.

Default worker count is `min(num_cpus, 4)`, configurable via
`--processors=N`. The cap is pragmatic: the parallel sites all
contend on a single Maude IPC mutex (`Arc<Mutex>` around the
subprocess), so empirically `N>4` gives diminishing returns. HS
defaults to `+RTS -N` (all cores) and burns proportional user-CPU
for it; capping at 4 trades a small wall-clock ceiling for a much
smaller user-CPU footprint. Output is byte-identical across all
worker counts.

### Memory

Peak RSS, same lemma set:

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

Geomean ~25% of HS's peak (4× less RAM). Most lemmas sit at 14-50 MB
regardless of complexity, where HS's footprint scales with proof size.
Two structural reasons:

1. GHC's GC retains heap residue between collections; Rust drops
   deterministically — closed proof-tree branches are freed
   immediately (`ProofNode.sys` is reset in `expand`).
2. mimalloc returns memory to the OS more aggressively than glibc
   or GHC's RTS (which holds a contiguous heap by design).

For parallel proving: a 16 GB machine fits ~300 RS workers on the
heaviest lemmas vs ~25 HS workers.

## Implemented

- **Parser**: full `.spthy` grammar including `macros:`, `predicates:`,
  `equations:`, `restrictions:`, `tactics:`, `#define`/`#include`
  preprocessor, multi-line comments, Unicode symbols.
- **Elaborator**: rule signatures, lemma formulas → guarded form,
  macro expansion, restriction insertion, source-kind classification.
- **Builtins**: `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, `diffie-hellman`, `multiset`,
  `natural-numbers`, `subterm`, `locations-report`, custom function
  symbols and equations.
- **Solver**: full constraint-system port with simplify / source-application
  / chain-extension / contradiction-detection / induction.
  Smart-rank heuristic, source-kind reasoning, AC-modulo unification
  via long-lived Maude subprocess, deterministic case enumeration.
- **CLI**: `--prove`, `--lemma`, `--bound`, `--heuristic`, `--saturation`,
  `--open-chains`, `--derivcheck-timeout`, `--auto-sources`,
  `--oraclename`, `--partial-evaluation`, `--parse-only`,
  `--precompute-only`, `--output`/`-O`, `--with-maude`/`-dot`/`-json`,
  `--quiet`, `-v/--verbose`, `--quit-on-warning`, `--diff` (parsed),
  `--output-module` (parsed). Exit codes and summary lines mirror HS.
- **Subcommands**: `interactive` (HTTP server, image rendering),
  `variants` (DH intruder rule dump), `test` (install self-check).

## Not yet ported

Lemmas using these builtins are filtered out of the corpus probe:

- **`builtins: xor`** — `^` operator + XOR AC theory.
- **`builtins: bilinear-pairing`** — `em`, `pmult` and the BP variants
  (would close the 53→125 gap in the `variants` subcommand).
- **`process:`** — SAPiC frontend (separate compiler producing rules).
- **`diff(...)` / `--diff`** — observational equivalence mode.

These are deeper functional gaps requiring substantial porting work,
not configuration choices.

CLI-level gaps (low severity, mostly export tooling):

- `--output-json` / `--output-dot` — accepts the flag and writes an
  empty stub file; full trace graph serialisation isn't ported.
- `--output-module=proverif|deepsec|spthytyped|msr|...` — accepted
  but errors when actually selected.
- `--replication-bound` — accepted, no effect.
- `test` subcommand omits HS's 55-case unit test suite; runs only the
  Maude + GraphViz reachability checks. `cargo test` covers the unit
  suite at build time.

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
  corpus_full_trace_diff.sh full-corpus parity sweep
  canon_proof_tree.py       proof tree canonicaliser (strips display details)
tests/                      cross-crate integration fixtures
```

## Testing

The canonical correctness gate:

```
cd rust
cargo test --release --test oracle_solver corpus_proof_skeleton_match_probe
```

This compares the structural proof tree against HS on the full corpus
(currently 191 lemmas at 0 divergent). The `corpus_full_trace_diff.sh`
script extends this to the full canonicalised proof text and runs the
broader 238-lemma sweep.

For per-lemma debugging:

```
scripts/diff_proof_tree.sh examples/classic/NSPK3.spthy injective_agree
```

For HS-vs-RS Maude command tracing (lock-step):

```
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify \
  cargo run --release --example dump_proof -- <file> <lemma>
```

See `crates/tamarin-term/src/maude_proc.rs` for the available env-gated
trace points.
