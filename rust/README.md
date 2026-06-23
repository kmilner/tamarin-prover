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
**byte-for-byte**. The per-file parity gate (275 files, `--derivcheck-timeout=30`)
stands at **200 MATCH with no proof-search or verdict (verified/falsified)
divergence remaining**. Every file that still differs needs a feature not yet
ported (`--diff` observational equivalence, SAPiC `--auto-sources`); the canonical
HS output for those is recorded in the cache so they re-compare automatically
once the feature lands. The rest are skipped because the Haskell side itself
exceeds the cap (genuinely hard or oracle-dependent searches).

## Performance

RS uses a fraction of HS's peak resident memory across the board, and is faster
in wall-clock across the representative workloads at the default multi-core
settings — including the Maude-bound bilinear-pairing proofs, where per-Maude-call
IPC dominates and the work is essentially serial. The one single-core exception
is the natural-numbers/multiset `gcm` proof: at one core RS trails HS by ~14 %, but
it parallelises far better (47 s → 19 s, vs HS 42 s → 30 s), so it leads from four
cores up. Representative protocols (aarch64 Linux, 16 cores, GHC 9.6.7, Maude
3.5.1): `NSPK3` (classic, sub-second reference), `Joux` (bilinear pairing —
Maude-bound), `stateverif_left_right` (SAPiC), `gcm` (key-wrapping, natural-numbers
+ multiset, deep constraint search), `wireguard` (deep proof search, few rules),
`CCITT_X509_3` (auto-sources + stored-proof replay, heaviest):

**1 core** — HS `+RTS -N1`, RS `--processors=1`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.9 s | 0.5 s | 66 MB | 17 MB |
| `Joux.spthy` | 6.6 s | 5.6 s | 253 MB | 46 MB |
| `stateverif_left_right.spthy` | 10.4 s | 7.8 s | 808 MB | 44 MB |
| `gcm.spthy` | 41.5 s | 47.4 s | 1332 MB | 103 MB |
| `wireguard.spthy` | 39.0 s | 18.3 s | 1659 MB | 123 MB |
| `CCITT_X509_3.spthy` | 148.5 s | 76.4 s | 3396 MB | 636 MB |

**4 cores** — HS `+RTS -N4`, RS `--processors=4`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.5 s | 0.3 s | 94 MB | 27 MB |
| `Joux.spthy` | 6.0 s | 5.5 s | 283 MB | 50 MB |
| `stateverif_left_right.spthy` | 6.5 s | 5.1 s | 780 MB | 69 MB |
| `gcm.spthy` | 32.4 s | 21.4 s | 1368 MB | 155 MB |
| `wireguard.spthy` | 23.2 s | 11.9 s | 1598 MB | 130 MB |
| `CCITT_X509_3.spthy` | 66.5 s | 24.0 s | 5589 MB | 668 MB |

**16 cores** — HS `+RTS -N16`, RS `--processors=16`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.6 s | 0.4 s | 143 MB | 33 MB |
| `Joux.spthy` | 6.7 s | 5.5 s | 321 MB | 59 MB |
| `stateverif_left_right.spthy` | 9.6 s | 5.0 s | 876 MB | 101 MB |
| `gcm.spthy` | 30.5 s | 19.2 s | 1365 MB | 228 MB |
| `wireguard.spthy` | 21.6 s | 11.5 s | 1748 MB | 143 MB |
| `CCITT_X509_3.spthy` | 66.1 s | 10.2 s | 8097 MB | 775 MB |

Peak RSS is the prover **process** only — Maude runs as a separate subprocess on
both sides and is not counted (GHC-heap vs Rust-heap). The memory gap is large
and universal (e.g. `wireguard` ~0.15 GB vs ~1.7 GB; `CCITT_X509_3` ~0.8 GB vs
~8.0 GB; `gcm` ~0.1–0.2 GB vs ~1.4 GB). Wall-clock scales with cores only where
the proof parallelises — `CCITT_X509_3` drops 76 s → 10 s and `gcm` 47 s → 19 s
(RS, 1 → 16 cores), while Maude-bound `Joux` and search-bound `wireguard` are
largely serial and barely move. Regenerate the
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
