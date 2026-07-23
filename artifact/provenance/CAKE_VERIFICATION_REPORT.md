# cake_lpr verification report — complete certificate

**Date:** 2026-07-23 (final layout; supersedes the 2026-07-22 run on the pre-consolidation tree)
**Verdict:** `98536 OK / 98536 checked — FAIL=0, MISSING=0, BADHASH=0`

## What was verified

All 98,536 LRAT certificates of the order-7 non-existence artifact: certificate
`proofs/i.lrat.zst` corresponds to line `i` (0-based) of `cubes_all.txt`. For each
index the runner (`cake_verify.sh`):

1. verified the compressed proof's SHA-256 against the pinned `SHA256SUMS` entry;
2. rebuilt the cube formula `F_i = o7.cnf + cube_i` from the embedded cube list;
3. decompressed the proof (`zstd`);
4. ran **cake_lpr through the shipped Apptainer image** (`cake_lpr.sif`, SHA-256 in
   `container/SIF_SHA256`) — — the LRAT/LPR checker formally verified in HOL4 down to
   machine code (Tan, Heule, Myreen) — accepting only the anchored verdict line
   `s VERIFIED UNSAT` (a substring match on `VERIFIED` was the historical gate
   bug; this run's gate self-test rejects an empty proof before any real work).

The checker binary was built locally from the upstream repository with its
`cake_lpr.S` matching the upstream-pinned SHA-256
(`2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a`).

Full per-cube log: `cake_report.txt` (98,536 `OK` lines, nothing else).

## Provenance note

52,263 proofs (the unit-propagation-refutable cubes) were regenerated on the
University of South Carolina HPC on 2026-07-21 after the original trimmed copies
were destroyed by an `lrat-trim` output bug on a full disk (fix submitted
upstream); the regeneration job gate-tested its checker against a known-empty
proof before running, and every regenerated proof passed both `lrat-check`
(anchored gate) and `lrat-trim --check` on the cluster. The delta was transferred
with per-file SHA-256 pinned on the cluster and re-verified byte-for-byte locally
before this run. The remaining 46,273 proofs are the original campaign's trimmed
certificates. All 98,536 share the same HPC solving provenance.

## Relation to the Lean development

`Conway_lean/ConwayO7/Final.lean` proves, in Lean 4 over mathlib:

> `no_aut_seven : (∀ s ∈ tilingSigns, CNF.Unsat (withCube o7cnf (cubeOfSigns
> tilingOrder s))) → ∀ srg(99,14,1,2) graph G, ¬ 7 ∣ |Aut G|`

where the tiling's exact coverage (prefix-free, full Kraft mass 2^200 over the
98,536 embedded cubes), the byte-identity of the embedded `o7.cnf`, and encoder
faithfulness (L4/L5) are all proved inside Lean. This report discharges the sole
remaining hypothesis with a formally verified external checker: every cube of the
tiling is UNSAT.

**Conclusion: no strongly regular graph with parameters (99, 14, 1, 2) admits an
automorphism of order 7.**
