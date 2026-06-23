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
in wall-clock across every representative workload at all core counts —
including the Maude-bound bilinear-pairing proofs, where per-Maude-call IPC
dominates and the work is essentially serial. The natural-numbers/multiset `gcm`
proof is a strong RS win (24 s vs 42 s at one core, 9 s vs 30 s at sixteen) after
a native ground-AC-equality match short-circuit eliminated ~500 K redundant Maude
round-trips. Representative protocols (aarch64 Linux, 16 cores, GHC 9.6.7, Maude
3.5.1): `NSPK3` (classic, sub-second reference), `Joux` (bilinear pairing —
Maude-bound), `stateverif_left_right` (SAPiC), `gcm` (key-wrapping, natural-numbers
+ multiset, deep constraint search), `wireguard` (deep proof search, few rules),
`CCITT_X509_3` (auto-sources + stored-proof replay, heaviest):

**1 core** — HS `+RTS -N1`, RS `--processors=1`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.9 s | 0.5 s | 66 MB | 17 MB |
| `Joux.spthy` | 6.6 s | 5.5 s | 252 MB | 48 MB |
| `stateverif_left_right.spthy` | 10.5 s | 7.9 s | 825 MB | 50 MB |
| `gcm.spthy` | 41.9 s | 24.4 s | 1336 MB | 103 MB |
| `wireguard.spthy` | 38.7 s | 18.0 s | 1659 MB | 124 MB |
| `CCITT_X509_3.spthy` | 143.6 s | 72.6 s | 3386 MB | 637 MB |

**4 cores** — HS `+RTS -N4`, RS `--processors=4`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.4 s | 0.3 s | 96 MB | 26 MB |
| `Joux.spthy` | 5.6 s | 5.3 s | 273 MB | 51 MB |
| `stateverif_left_right.spthy` | 6.3 s | 5.0 s | 887 MB | 71 MB |
| `gcm.spthy` | 31.8 s | 10.0 s | 1329 MB | 159 MB |
| `wireguard.spthy` | 22.4 s | 11.6 s | 1652 MB | 131 MB |
| `CCITT_X509_3.spthy` | 63.5 s | 24.0 s | 5970 MB | 672 MB |

**16 cores** — HS `+RTS -N16`, RS `--processors=16`

| File | HS wall | RS wall | HS peak RSS | RS peak RSS |
|------|--------:|--------:|------------:|------------:|
| `NSPK3.spthy` | 0.5 s | 0.4 s | 144 MB | 34 MB |
| `Joux.spthy` | 6.4 s | 5.4 s | 328 MB | 62 MB |
| `stateverif_left_right.spthy` | 6.6 s | 4.9 s | 833 MB | 96 MB |
| `gcm.spthy` | 30.2 s | 8.8 s | 1412 MB | 239 MB |
| `wireguard.spthy` | 21.2 s | 11.5 s | 1706 MB | 144 MB |
| `CCITT_X509_3.spthy` | 66.5 s | 10.2 s | 8364 MB | 774 MB |

Peak RSS is the prover **process** only — Maude runs as a separate subprocess on
both sides and is not counted (GHC-heap vs Rust-heap). The memory gap is large
and universal (e.g. `wireguard` ~0.15 GB vs ~1.7 GB; `CCITT_X509_3` ~0.8 GB vs
~8.0 GB; `gcm` ~0.1–0.2 GB vs ~1.4 GB). Wall-clock scales with cores only where
the proof parallelises — `CCITT_X509_3` drops 73 s → 10 s and `gcm` 24 s → 9 s
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
