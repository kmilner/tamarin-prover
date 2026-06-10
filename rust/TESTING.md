# Testing the Rust port

Quick reference for the tests, probes, and scripts used to measure HS↔Rust
parity during the port.

All commands assume CWD is the repo root (`/home/parallels/tamarin-prover-2`)
unless noted.

## Build prerequisites

```bash
# Rust binaries (release build for probes; debug is fine for development)
cd rust
cargo build --release --bin tamarin-prover
cargo build --release --example dump_proof
cargo build --release --example probe_lemma   # for /tmp/probe_targets.sh
cd ..

# Haskell binary (one-time)
stack build
```

Auto-discovered Haskell paths: scripts walk
`.stack-work/install/*/*/*/bin/tamarin-prover` and
`.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover` first,
then fall through to `tamarin-prover` in `$PATH`.

## Primary metric: corpus proof-skeleton match probe

The canonical metric for HS↔Rust proof-tree parity. Walks the corpus dirs
under `/home/parallels/tamarin-prover/examples/`, proves each lemma with
both provers, and counts structural matches.

```bash
cd rust
cargo test --test oracle_solver corpus_proof_skeleton_match_probe --release -- --nocapture
```

Runtime ~40s. Default thread count is fine; the previously-required
`MALLOC_TRIM_THRESHOLD_=0 MALLOC_MMAP_THRESHOLD_=131072
RAYON_NUM_THREADS=2` workarounds are no longer needed.

Output format:

```
corpus structural-match: 110/117 (7 struct-divergent, 0 no-haskell-skel, 3 incomparable)
structural divergences:
  <file>::<lemma> — diverge line N: ours="..." theirs="..."
```

The numerator counts lemmas whose canonicalized Rust proof tree matches
HS's byte-for-byte. The `incomparable` bucket is lemmas where HS doesn't
emit a usable proof skeleton (timeouts, unsupported features). A
`[verdict: ours=X theirs=Y]` annotation flags wrong-verdict divergences.

## Per-lemma proof-tree diff

For investigating a single lemma's structural divergence:

```bash
rust/scripts/diff_proof_tree.sh <theory.spthy> <lemma_name>
```

Prints `<lemma>: N diff lines (HS: H, RS: R)`. `N=0` means byte-identical
canonicalized trees.

To pass env vars to the Rust run (useful for diagnostics):

```bash
rust/scripts/diff_proof_tree.sh <theory.spthy> <lemma> "TAM_RS_TRACE_N6=1"
```

To inspect the actual diff content:

```bash
rust/scripts/diff_proof_tree.sh examples/Tutorial.spthy Client_auth
diff /tmp/tmp.*/hs.canon /tmp/tmp.*/rs.canon   # (the temp dir is cleaned up — capture stdout to keep it)
```

Or use the canonicalizer directly:

```bash
rust/target/release/examples/dump_proof <theory.spthy> <lemma> | python3 rust/scripts/canon_proof_tree.py
```

## Local corpus sweep

A hand-picked corpus sweep around the lemma sets we use during port
development (Tutorial, KAS2, NSPK3, NSLPK3 variants, TESLA_Scheme1,
Minimal_Crypto_API):

```bash
rust/scripts/corpus_diff_proof_trees.sh
```

Prints `PASS: N` / `FAIL: N` plus the failing lemmas. Used for quick
local regression checks; the full corpus probe (above) is the canonical
metric.

## Byte-level trace comparison

For investigating exact divergence points within a single lemma. Both
provers emit a `[STATE]` line at every proof-method expand. Diffing
those lines pinpoints the first byte-of-divergence in the search.

```bash
# Capture HS trace:
TAM_HS_TRACE_STATE_EQS=1 tamarin-prover --prove=<lemma> <file> 2>&1 \
    | grep '^\[STATE\]' > /tmp/hs.trace

# Capture Rust trace:
TAM_RS_TRACE_STATE_EQS=1 rust/target/release/tamarin-prover \
    --prove=<lemma> <file> 2>&1 | grep '^\[STATE\]' > /tmp/rs.trace

# Compare:
diff /tmp/hs.trace /tmp/rs.trace | head -60
```

See `memory/project_byte_level_trace_investigation.md` for the worked
example (Responder_secrecy 54→10 diff lines).

## Useful env-var flags

Environment flags toggle HS-faithful vs legacy behavior, and enable
specific diagnostics. The big ones (current as of 2026-05-27):

### HS-faithful behavior toggles (mostly default-on)

| Variable | Effect |
|---|---|
| `TAM_RS_DISABLE_FLATTEN_UNIF=1` | revert flattenUnif in AC-free fast path |
| `TAM_RS_PER_STEP_RESET_LEGACY=1` | skip Maude counter reset per proof step |
| `TAM_RS_SOMEINST_LEGACY=1` | uniform-shift freshen instead of HS-faithful |
| `TAM_RS_DISABLE_PER_VARIANT_COUNTER_RESET=1` | apply_eq_store loop counter |
| `TAM_NO_PRECOMPUTE_VARIANTS=1` | variants AFTER precompute (legacy) |

### Diagnostic dumps (off by default)

| Variable | Effect |
|---|---|
| `TAM_DBG_REFINE=1` | source-case refine inputs/outputs |
| `TAM_DBG_VARIANTS=1` | protocol rule variants at theory load |
| `TAM_DBG_PERFORM_SPLIT=1` | perform_split's S.toList output |
| `TAM_DBG_BRANCH_DROP=1` | saturate branches dropped via contras |
| `TAM_DBG_AES_VARIANTS=1` | apply_eq_store variant before→after counts |
| `TAM_RS_DBG_APPLY_EQ_STORE=1` | applyEqStore IN/OUT (paired with HS's) |
| `TAM_RS_TRACE_N6=1` | N6 KD-conc/KU-act dump |
| `TAM_RS_TRACE_CHAIN_EXTEND=1` | chain extension fact unification |
| `TAM_DBG_DESTR=1` | destructor rule generation |
| `TAM_HS_DBG_APPLY_EQ_STORE=1` | HS-side applyEqStore trace |
| `TAM_HS_TRACE_CHAINS=1` | HS-side solveChain enter/extend |
| `TAM_HS_DBG_PERFORM_SPLIT=1` | HS-side perform_split |

`TAM_HS_*` flags only work with the HS binary; `TAM_RS_*` / `TAM_DBG_*`
with the Rust one.

## Files

- `rust/scripts/canon_proof_tree.py` — proof-tree canonicalizer
- `rust/scripts/diff_proof_tree.sh` — single-lemma HS↔Rust diff
- `rust/scripts/corpus_diff_proof_trees.sh` — hand-picked corpus sweep
- `rust/scripts/canonicalize_trace.py` — pre-existing trace canonicalizer
- `rust/scripts/diff_trace.py` — pre-existing trace diff helper
- `rust/crates/tamarin-theory/tests/oracle_solver.rs` — corpus probe test
