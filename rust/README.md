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

The correctness criterion is byte-identical raw `--prove` output, ignoring the
volatile header lines (Git revision, compile time, processing time).

The parity gate (`scripts/corpus_file_diff.sh`) compares the Rust port against
the Haskell prover on a 275-file corpus: the theories under `examples/` that use
only ported features and that Haskell proves within a 300 s/lemma cap. This
spans `classic/`, `ake/`, `sp14/`, the `csf*/` series, `features/`, `loops/`,
`post17/`, `regression/`, and `related_work/`.

| Result | Files | Meaning |
|--------|------:|---------|
| MATCH | 200 | Rust output byte-identical to Haskell |
| DIFF  |   6 | needs an unported feature (`--diff`, `--auto-sources`); HS output is cached and re-compared automatically when the feature lands |
| SKIP  |  69 | no Haskell reference to compare against (HS exceeds the cap, or produces no/empty output) |

No proof-search or verdict (verified/falsified) divergence remains. Theories
outside the corpus require an unported frontend — SAPiC `process:`,
observational equivalence (`--diff`), or `--auto-sources` — or exercise searches
that Haskell itself does not finish.

## Performance

Wall-clock time and peak memory for both provers on six representative theories,
proving all lemmas (`--derivcheck-timeout=30`) on aarch64 Linux (GHC 9.6.7,
Maude 3.5.1). Haskell runs at `+RTS -N{1,4,16}`, the Rust port at
`--processors={1,4,16}`. The theories are `NSPK3` (classic protocol), `Joux`
(bilinear pairing), `stateverif_left_right` (SAPiC rules), `gcm` (key wrapping;
natural-numbers and multiset), `wireguard` (deep proof search), and
`CCITT_X509_3` (auto-sources with stored-proof replay).

**1 core**

| Theory | HS time | RS time | HS memory | RS memory |
|--------|--------:|--------:|----------:|----------:|
| `NSPK3` | 0.9 s | 0.5 s | 66 MB | 17 MB |
| `Joux` | 6.6 s | 5.5 s | 252 MB | 48 MB |
| `stateverif_left_right` | 10.5 s | 7.9 s | 825 MB | 50 MB |
| `gcm` | 41.9 s | 24.4 s | 1336 MB | 103 MB |
| `wireguard` | 38.7 s | 18.0 s | 1659 MB | 124 MB |
| `CCITT_X509_3` | 143.6 s | 72.6 s | 3386 MB | 637 MB |

**4 cores**

| Theory | HS time | RS time | HS memory | RS memory |
|--------|--------:|--------:|----------:|----------:|
| `NSPK3` | 0.4 s | 0.3 s | 96 MB | 26 MB |
| `Joux` | 5.6 s | 5.3 s | 273 MB | 51 MB |
| `stateverif_left_right` | 6.3 s | 5.0 s | 887 MB | 71 MB |
| `gcm` | 31.8 s | 10.0 s | 1329 MB | 159 MB |
| `wireguard` | 22.4 s | 11.6 s | 1652 MB | 131 MB |
| `CCITT_X509_3` | 63.5 s | 24.0 s | 5970 MB | 672 MB |

**16 cores**

| Theory | HS time | RS time | HS memory | RS memory |
|--------|--------:|--------:|----------:|----------:|
| `NSPK3` | 0.5 s | 0.4 s | 144 MB | 34 MB |
| `Joux` | 6.4 s | 5.4 s | 328 MB | 62 MB |
| `stateverif_left_right` | 6.6 s | 4.9 s | 833 MB | 96 MB |
| `gcm` | 30.2 s | 8.8 s | 1412 MB | 239 MB |
| `wireguard` | 21.2 s | 11.5 s | 1706 MB | 144 MB |
| `CCITT_X509_3` | 66.5 s | 10.2 s | 8364 MB | 774 MB |

Memory is the maximum resident set of the prover process; Maude runs as a
separate subprocess on both sides and is excluded. Across all theories and core
counts the Rust port is faster and uses roughly 4–16× less memory. Parallelism
is provided by rayon over a pool of Maude subprocesses: `--processors=N` sets the
worker-thread count and `--maude-processes=M` (default `⌈N/2⌉`) the pool size.
Regenerate the tables with `scripts/bench.sh`.

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

Theories using these features are tracked in `scripts/file_flags.tsv` and
re-enter the gate automatically once the feature lands.

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
  bench.sh                RS-vs-HS wall-clock + memory tables
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
