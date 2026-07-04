# HANDOVER — rust-port HS-faithfulness campaign (written 2026-07-04, machine move)

> **⚠️ DELETE THIS FILE once the work is picked up again** — it is a machine-move
> snapshot, not living documentation. Also delete the two cache tarballs after
> unpacking them (`rust/scripts/hs_file_cache.tgz`, `rust/scripts/web_hs_cache.tgz`).
> This branch gets cleaned up before upstreaming, so the tarball blobs in history
> are acceptable. `git rm HANDOVER.md rust/scripts/*.tgz` when done. 😄

## What this is

Rust port (`rust/`) of tamarin-prover vs the Haskell reference (`lib/` + `src/`).
**HS is the ORACLE; the goal is byte-identical RAW `--prove` stdout** (any byte
divergence is a bug regardless of verdict) plus **structural/semantic parity of
the interactive web UI** (byte parity NOT required there; root page `/` scoped out).
Fixes must be mechanism-faithful ports of HS behavior — no output post-processing,
no RS-only caps/timeouts, no opt-out env flags.

Long-term state (status, open threads, discipline, pattern catalog) lives in the
auto-memory at `~/.claude/projects/-home-parallels-tamarin-prover-2/memory/` on the
OLD machine (aarch64 VM). **Copy that whole directory across if possible** — it is
the index of everything; this doc only carries what is needed to resume the three
in-flight threads.

## State at handover

- Branch `production-cleanup`, HEAD = the "wrap-position family" commit (the last
  commit before the HANDOVER commit; see `git log`).
- **Batch corpus gate: 386 MATCH / 0 DIFF / 58 SKIP_HS_TIMEOUT / 10 SKIP_NO_HS**
  (fullgate15, zero transitions vs fullgate14). This is the crown jewel — keep it.
- Web campaign: all 5 original guard files fully MATCH (DH_example 78/78,
  JCS12 167/167, NSPK3 250/250, design-choices 92/92, RYY_PFS 99/0).
  A partial 59-file web sweep enumerated the wider corpus; the dominant ~7k-DIFF
  wrap-position family was just fixed (see HEAD commit). Remaining web work = the
  three threads below.
- Landed today (all individually full-gated 386/0): `c75385d1` (stale post-conjoin
  action, last guard-file DIFF), `ca3f8f42` (eCK web OOM = eager Union distribution
  in HughesPJ `above_nest`; exponential Doc blowup; NOT solver), and HEAD (wrap
  family). Detail in the commit messages — they carry HS citations.

## Thread 1 — web DIFF residuals after the wrap fix (task #20, in progress)

Post-fix per-file counts and their classified roots (all pre-existing families,
NOT wrap):

| file | DIFF | root family |
|---|---|---|
| ake/dh/UM_three_pass | 77 | ∃-witness index drift in eq-store `conj:` display (`~ex.14` vs `~ex.12`) — fresh-counter-threading family (cf. memory topic `counter-threading-root`, task-#18 history) |
| csf17/commitment-protocol | 64 | same witness drift + abbreviation-name index drift (`SI6` vs `SI5`) in dot pages |
| asiaccs20-POIDC/OIDC_Implicit | 8 | 2× lemma-set ORDER in cases panes (RS `cmp_guarded` vs HS `Ord LNGuarded` gap); 2× root method-list CONTENT (HS lists a 2nd method after `simplify` that RS's `exec_proof_method` filter drops); 4× refined-source COUNT "(29 cases)" vs "(25 cases)" — source-computation divergence, POTENTIALLY VERDICT-RELEVANT class, dig this one first |

Diff dumps: `/tmp/web_parity_diffs/<relpath>/` on the old machine (regenerate by
re-running web_parity on the file — cheap with the HS cache).

## Thread 2 — TAK1 web proof-page spin (task #21, pending)

PRE-EXISTING (reproduced on a pre-today baseline): after autoprove of
`ake/bilinear/TAK1_eCK_like.spthy`, GET `overview/proof/session_key_establish`
(+3 sibling proof pages) spins CPU-bound ≥20 min (83% CPU, RSS flat ~100MB); HS
serves the same page <60 s. Stack: `render_sub_proof_snippet →
write_applicable_methods → exec_proof_method → solve_unique_actions_pass →
solve_action_goal → solve_fact_eqs → solve_term_eqs → simp_with_fresh_avoiding →
subst_creates_non_normal_terms → maybe_not_nf_subterms` (contradictions.rs:299).
Batch `--prove` of the file is byte-MATCH — display-path only (the HS
`applicableProofMethods` equivalent on the post-autoprove tree). Causes TAK1's
119 MISSING_RS in web parity (crawler's 60 s timeout). Likely hits other eCK
siblings' proof pages too. Suggested angle: compare which methods HS's
`applicableProofMethods` actually executes vs RS's exec-everything approach, and
whether HS memoises/short-circuits `maybe_not_nf_subterms`-class checks.

## Thread 3 — resume the P5 full web sweep (task #6)

Sweep only the 386 gate-MATCH files (the 68 no-HS-baseline files each burn a 300 s
HS-boot timeout). Build the allowlist from the latest gate TSV:
`awk -F'\t' '$2=="MATCH"{print $1}' <fullgateN.tsv> > allow386.txt`

**Run each file in its OWN systemd scope** — one scope for the whole sweep dies on
the first per-file OOM, and OOM teardown overlapping the next boot poisons it with
a spurious SKIP_RS_FAIL (ports 3021/3022 linger). Driver (was
`scratchpad/dig/websweep_driver.sh`; recreate):

```bash
#!/usr/bin/env bash
set -u
ALLOW=allow386.txt; OUT=websweep_full.tsv; REPO=<repo-root>
: > "$OUT"; n=0; total=$(wc -l < "$ALLOW")
wait_ports_free() { local i=0; while ss -ltn | grep -qE ':(3021|3022) '; do
    i=$((i+1)); [ $i -gt 60 ] && break; sleep 1; done; }
while IFS= read -r f; do
    [ -n "$f" ] || continue; n=$((n+1))
    echo "=== [$n/$total] $f ===" >&2
    wait_ports_free
    one=$(mktemp); printf '%s\n' "$f" > "$one"; tsv=$(mktemp -u)
    systemd-run --user --scope -q -p MemoryMax=48G --unit="websweep-f$n-$$" \
        env RESULTS_TSV="$tsv" ALLOWLIST="$one" TAM_RS_NO_AUTO_BUILD=1 \
        "$REPO/rust/scripts/web_parity.sh" 2>&1
    rc=$?
    [ -f "$tsv" ] && cat "$tsv" >> "$OUT"
    [ $rc -ne 0 ] && printf '%s\t-\tSKIP_SCOPE_KILLED\t-\t-\trc=%d\n' "$f" "$rc" >> "$OUT"
    rm -f "$one" "$tsv"
done < "$ALLOW"
echo DONE >&2
```

Partial results from the killed 59-file run (old machine,
`scratchpad/dig/websweep_partial_59files.tsv`): ~12.6k MATCH / ~7k DIFF before the
wrap fix — expect the DIFF count to collapse on re-run; whatever remains buckets
into the Thread-1 families plus unknowns. The 13 former OOM files (Chen_Kudla*,
Joux*, TAK1*, NAXOS_eCK*, DHKEA_NAXOS_C_*, KEA_plus*) now serve their cases pages
(fixed by `ca3f8f42`) but TAK1-family proof pages still hang (Thread 2) →
expect MISSING_RS there until Thread 2 lands.

## Oracle caches (the two tarballs)

```
cd rust/scripts && tar -xzf hs_file_cache.tgz && tar -xzf web_hs_cache.tgz
# then delete the tarballs
```

- `.hs_file_cache/` (~2.4MB, 605 entries): stripped HS `--prove` stdout for the
  batch gate (`corpus_file_diff.sh`) — makes the full gate an RS-only run.
- `.web_hs_cache/` (~787MB unpacked, 73 manifests): HS web-crawl manifests for
  `web_parity.sh` — covers the guard sets + sweep files 1-59 (the expensive ones).
- **Keys are `sha256(<theory file content>)`** (+ a flags-hash salt for flagged
  batch entries) — NO binary hash, NO paths → they transfer across architectures
  unchanged. Theory files come from git, so keys hit as-is.
- **MANDATORY trust-but-verify on the new machine**: after rebuilding HS, pick 3
  cached files, re-run their HS side fresh (point `CACHE=` at a temp dir), and
  `cmp` fresh vs cached. Match ⇒ the caches are sound. Mismatch ⇒ environment
  drift (almost certainly Maude version — old machine ran **Maude 3.5.1**) →
  regenerate caches, do NOT patch them.

## New-machine prerequisites

1. `stack build` the HS reference (the gate tooling finds the binary via the
   arch-agnostic glob `.stack-work/install/*/*/*/bin/tamarin-prover`; do NOT use
   `~/.local/bin` — stale-binary trap).
2. Maude **3.5.1** on PATH; graphviz `dot` for web pages.
3. `cargo build --release` in `rust/`.
4. Sanity ladder before resuming work: (a) 3-file HS cache spot (above);
   (b) full gate `RESULTS_TSV=/tmp/gate.tsv ALLOWLIST=scripts/parity_corpus.txt
   rust/scripts/corpus_file_diff.sh` → expect 386/0 (run it inside
   `systemd-run --user --scope -p MemoryMax=48G`, JOBS≤6);
   (c) web guards: per-file `web_parity.sh` on DH_example, NSPK3, RYY_PFS →
   78/0, 250/0, 99/0.

## Discipline (non-negotiable, learned the hard way)

- **Full corpus gate before EVERY commit** that touches solver or printers; gate
  = patched RS vs cached HS (never build a PRE binary for RS-vs-RS). Check
  transitions between consecutive gate TSVs via `join` on col1, not the tallies.
- Web servers/probes ALWAYS inside `systemd-run --user --scope -p MemoryMax=...`
  (RS can OOM 17-50GB; setsid does NOT protect the host). Kill stale
  `tamarin-prover interactive` processes before booting a new one on the same
  port — a stale server silently serves the OLD binary (pkill may exit 144;
  ignore). ptrace is restricted (yama=1): to get stacks, launch the server as a
  child of gdb, not attach.
- Never rebuild the RS binary while a sweep/gate is running. Never two sweeps at
  once. `--processors=1` for any deterministic RS trace (run.rs's rayon pool
  ignores RAYON_NUM_THREADS). Reset stray edits with `git checkout -- <path>`,
  NEVER `git clean` (nukes the untracked caches + tooling).
- Sub-agents must NOT commit or run full sweeps; verify their diagnoses with
  instrumentation before landing (two of today's three fixes had their initial
  root-cause premise CORRECTED by measurement — "obvious" suspects refuted:
  saturation non-convergence, counter discipline, deriv-check deadline leak).
- Commit trailers:
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` and
  `Claude-Session: <session url>`.

## Useful probe (web OOM/hang reproducer, was scratchpad/w19/probe_bin.sh)

```bash
#!/usr/bin/env bash
# probe_bin.sh <binary> <tag> [<thydir>] — boot RS interactive on one theory in an
# 8G scope, request the raw-cases page, report survival + peak RSS.
set -u
BIN=$1; TAG=$2; THY=${3:-thy}; PORT=3199
systemctl --user reset-failed "w-$TAG.scope" 2>/dev/null
pkill -f "tamarin-prover interactive.*$PORT" 2>/dev/null; sleep 1
systemd-run --user --scope -q -p MemoryMax=8G --unit="w-$TAG" \
    env MAUDE_PATH=$(command -v maude) "$BIN" interactive "$THY" --port=$PORT \
    > "server_$TAG.log" 2>&1 &
for i in $(seq 1 90); do curl -sf -o /dev/null "http://127.0.0.1:$PORT/" && break; sleep 1; done
PID=$(ss -ltnp | grep ":$PORT " | grep -oP 'pid=\K[0-9]+' | head -1)
( MAX=0; while kill -0 "$PID" 2>/dev/null; do
    R=$(grep VmRSS /proc/$PID/status 2>/dev/null | grep -oP '[0-9]+') || break
    [ "$R" -gt "$MAX" ] && MAX=$R; echo "$MAX" > "rss_$TAG.max"; sleep 0.3; done ) &
HTTP=$(timeout 90 curl -s -o "cases_$TAG.html" -w '%{http_code}' \
    "http://127.0.0.1:$PORT/thy/trace/1/main/cases/raw/0/0")
ALIVE=no; kill -0 "$PID" 2>/dev/null && ALIVE=yes
echo "$TAG: http=$HTTP alive=$ALIVE peak_kb=$(cat rss_$TAG.max 2>/dev/null) bytes=$(wc -c < cases_$TAG.html 2>/dev/null)"
systemctl --user stop "w-$TAG.scope" 2>/dev/null
```

## Backlog beyond the three threads

`--diff` observational-equivalence prover (5 excluded files re-enter
parity_corpus.txt when ported); `--stop-on-trace` routing (parsed-not-routed in
cli.rs); the 58 SKIP_HS_TIMEOUT monsters; latent items indexed in memory
(`MEMORY.md` OPEN/LATENT section).
