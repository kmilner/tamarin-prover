# tamarin-prover (Rust port)

In-progress Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/).
The Haskell sources under `../lib/` and `../src/` remain canonical; this port
mirrors them function-for-function, targeting **byte-identical raw `--prove`
output** against the Haskell prover.

```
utils → term → parser → theory → {sapic, accountability, export, server} → tamarin-prover
```

## Build

```
cd rust
cargo build --release    # → target/release/tamarin-prover
cargo test               # Rust unit + integration tests
```

The release profile uses `lto = "fat"` and `codegen-units = 1`.

## Status

The correctness target is **byte-identical raw `--prove` stdout** (stripping
only the Git-revision, compiled-at, and processing-time lines).

On the comparable corpus — the theory files for which the Haskell prover
produces a reference within the wall-clock cap — RS reproduces HS output
**byte-for-byte**. The per-file parity gate (273 files, `--derivcheck-timeout=30`)
stands at **197 MATCH with no proof-search or verdict (verified/falsified)
divergence remaining**. Every file that still differs needs a feature not yet
ported (`--diff` observational equivalence, SAPiC `--auto-sources`); the canonical
HS output for those is recorded in the cache so they re-compare automatically
once the feature lands. The rest are skipped because the Haskell side itself
exceeds the cap (genuinely hard or oracle-dependent searches).

## Performance

RS uses a fraction of HS's peak resident memory across the board, and is faster
in wall-clock across the representative workloads — including the Maude-bound
bilinear-pairing proofs, where per-Maude-call IPC dominates and the work is
essentially serial. Representative protocols (aarch64 Linux, GHC
9.6.7, Maude 3.5.1): `NSPK3` (classic, sub-second reference), `Joux` (bilinear
pairing — Maude-bound), `stateverif_left_right` (SAPiC), `wireguard` (deep proof
search, few rules), `CCITT_X509_3` (auto-sources + stored-proof replay, heaviest):

**1 core** — HS `+RTS -N1`, RS `--processors=1`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.9 s | 0.5 s | 66 MB | 17 MB |
| `Joux.spthy` | 6.9 s | 5.6 s | 264 MB | 46 MB |
| `stateverif_left_right.spthy` | 10.5 s | 7.8 s | 879 MB | 44 MB |
| `wireguard.spthy` | 40.0 s | 20.8 s | 1663 MB | 127 MB |
| `CCITT_X509_3.spthy` | 143.4 s | 72.1 s | 3386 MB | 636 MB |

**4 cores** — HS `+RTS -N4`, RS `--processors=4`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.5 s | 0.3 s | 94 MB | 26 MB |
| `Joux.spthy` | 5.9 s | 5.4 s | 287 MB | 50 MB |
| `stateverif_left_right.spthy` | 6.0 s | 5.0 s | 851 MB | 71 MB |
| `wireguard.spthy` | 22.3 s | 14.7 s | 1768 MB | 133 MB |
| `CCITT_X509_3.spthy` | 63.5 s | 24.5 s | 6014 MB | 671 MB |

**16 cores** — HS `+RTS -N16`, RS `--processors=16`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.5 s | 0.4 s | 144 MB | 34 MB |
| `Joux.spthy` | 6.6 s | 5.5 s | 343 MB | 59 MB |
| `stateverif_left_right.spthy` | 7.0 s | 5.0 s | 877 MB | 100 MB |
| `wireguard.spthy` | 21.2 s | 14.6 s | 1856 MB | 146 MB |
| `CCITT_X509_3.spthy` | 66.6 s | 10.4 s | 7961 MB | 777 MB |

Peak RSS is the prover **process** only — Maude runs as a separate subprocess on
both sides and is not counted (GHC-heap vs Rust-heap). The memory gap is large
and universal (e.g. `wireguard` ~0.15 GB vs ~1.9 GB; `CCITT_X509_3` ~0.8 GB vs
~8.0 GB). Wall-clock scales with cores only where the proof parallelises —
`CCITT_X509_3` drops 72 s → 10 s (RS, 1 → 16 cores), while Maude-bound `Joux` and
search-bound `wireguard` are largely serial and barely move. Regenerate the
tables with `rust/scripts/bench.sh`.

RS mirrors HS's `parList`/`parMap` sites with rayon (per-rule variants, source
saturation, per-item pretty-print), backed by a pool of independent Maude
subprocesses (`MaudePool`) so parallel calls don't serialise on one Maude IPC
mutex. The pool is a pure optimisation — Maude is a stateless oracle.
`--processors=N` sets the rayon worker count; `--maude-processes=M` the pool size
(default `max(1, N/2)`).

## Implemented

- **Parser:** full `.spthy` grammar — `macros:`, `predicates:`, `equations:`,
  `restrictions:`, `tactics:`, `heuristic:`, `#define`/`#include` preprocessing,
  multi-line comments, Unicode symbols.
- **Elaborator:** rule signatures, lemma formulas → guarded form, macro
  expansion, predicate → restriction expansion, restriction insertion,
  source-kind classification.
- **Builtins:** `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, `diffie-hellman`, `xor`, `bilinear-pairing`,
  `multiset`, `natural-numbers`, `subterm`, `locations-report`, plus custom
  functions and equations.
- **Solver:** full constraint-system port — simplification, source
  refinement/saturation, chain extension, contradiction detection, induction,
  stored-proof replay, and AC-modulo unification via pooled Maude.
- **Heuristics:** smart (`s`/`S`), goal-number (`C`/`c`), injective (`i`/`I`),
  SAPiC (`p`/`P`), oracle (`o`/`O`), and `tactic:` rankings — selected by the
  in-file `heuristic:`/`tactic:` annotation or per-lemma attribute, or overridden
  for every lemma by the CLI `--heuristic` (HS `selectHeuristic`).
- **CLI:** `--prove`/`--lemma`, `--bound`, `--heuristic`, `--oraclename`,
  `--oracle-only`, `--processors`, `--maude-processes`, `--derivcheck-timeout`,
  `-D` defines, `--parse-only`, `--precompute-only`, `-O/--output`, `--quiet`,
  `-v/--verbose`, `--quit-on-warning`; exit codes and summary lines mirror HS.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH intruder-rule
  dump), `test` (install self-check).

## Not yet ported

- **`process:`** — the SAPiC frontend (process-calculus compiler). Pre-translated
  SAPiC theories (multiset-rewrite rules) prove fine; the `process:` block itself
  is not compiled.
- **`diff(...)` / `--diff`** — observational-equivalence mode.
- **`--auto-sources`** — automatic sources-lemma generation.
- Other parse-only CLI flags: `--saturation`, `--open-chains`,
  `--partial-evaluation`, `--stop-on-trace` (RS already defaults to DFS, as HS
  does), `--replication-bound`; `--output-json`/`--output-dot` write stubs and
  `--output-module=proverif|deepsec|…` errors.

Files needing an unported feature sit outside the parity corpus; their canonical
HS output is recorded (`scripts/file_flags.tsv`) so they re-compare the moment
the feature lands.

## Repository layout

```
crates/
  tamarin-utils/          fresh-ident state, small util types
  tamarin-term/           Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
  tamarin-parser/         .spthy AST + lexer + parser + #include resolver
  tamarin-theory/         elaborator, constraint system, solver, simplify, sources, replay
  tamarin-sapic/          SAPiC channel / source-case helpers (no full frontend)
  tamarin-accountability/ accountability frontend (placeholder)
  tamarin-export/         ProVerif / DeepSec / SPDL export (placeholder)
  tamarin-server/         interactive HTTP server (Axum)
  tamarin-prover/         the binary: CLI parser + run dispatch
scripts/
  diff_proof_raw.sh       per-lemma raw HS↔RS --prove diff (exit 0 = identical)
  corpus_file_diff.sh     per-file corpus parity gate vs cached HS → RESULTS_TSV
  file_flags.tsv          canonical per-file flags for theories needing them
  bench.sh                RS-vs-HS wall-clock + peak-RSS tables
tests/                    cross-crate integration fixtures
```

## Testing

Parity against Haskell is the correctness gate:

```
cd rust
scripts/diff_proof_raw.sh ../examples/classic/NSPK3.spthy injective_agree   # one lemma
RESULTS_TSV=/tmp/gate.tsv ALLOWLIST=<filelist> scripts/corpus_file_diff.sh  # corpus gate (cached HS)
cargo test                                                                  # Rust unit + integration
```

`diff_proof_raw.sh` rebuilds the binary first (set `TAM_RS_NO_AUTO_BUILD=1` to
skip); the corpus gate runs the prebuilt binary against a content-keyed HS cache.

Lock-step HS-vs-RS Maude command tracing:

```
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify \
  target/release/tamarin-prover --prove <file>
```

See `crates/tamarin-term/src/maude_proc.rs` for the env-gated trace points.
