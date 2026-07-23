# Provenance — not part of the verification path

Historical and reproduction material. Nothing in this folder is needed to verify
the result (see `../../REFEREE.md` for the verification protocol); it documents
where the artifact came from and how the authors verified it themselves.

## Superseded tools

- `conway_o7.py` — the Python encoder that originally generated `../o7.cnf`.
  Superseded as a trust element by the Lean byte-identity theorem
  (`Encoder.mkO7Cnf_eq`): Lean re-derives the CNF generation and proves the
  result equal to the embedded bytes. Kept so the formula's origin can be
  reproduced and compared.
- `lrat-check` — Biere's C LRAT checker, used during the solving campaign.
  Superseded by the formally verified cake_lpr. Kept as an independent second
  checker for the curious: it accepts exactly the same proofs
  (anchored gate `^c VERIFIED`, exit code 0).

## Checker image build record

The shipped image `../cake_lpr.sif` (SIF = Singularity Image Format,
Apptainer's single-file container format) was built:

- date: 2026-07-22; builder: Apptainer 1.5.3, WSL2 (Ubuntu 24.04 host)
- base image: docker://ubuntu:24.04
- definition: `../cake_lpr.def`, whose `%post` compiles cake_lpr from the
  upstream repository after verifying `cake_lpr.S` against the upstream-pinned
  SHA-256 (`2f3af32d…`, published by the cake_lpr authors).

The image's fingerprint is pinned, like every artifact file, in `../SHA256SUMS`
— the single source of truth for hashes.

## Authors' verification report (2026-07-23)

**Verdict:** `98536 OK / 98536 checked — FAIL=0, MISSING=0, BADHASH=0`, on the
final flattened layout, through the shipped container image.

For each index `i` the runner (`../cake_verify.sh`): verified the compressed
proof's SHA-256 against `../SHA256SUMS`; rebuilt `F_i = o7.cnf + cube_i` from
line `i` of `../cubes_all.txt`; decompressed `../proofs/i.lrat.zst`; and ran
cake_lpr — the LRAT/LPR checker formally verified in HOL4 down to machine code
(Tan, Heule, Myreen) — accepting only the anchored verdict `s VERIFIED UNSAT`.
(An unanchored substring match was the historical gate bug; the campaign-era
runs self-test their gate against a known-empty proof before any real work.)

**Repair history.** 52,263 proofs (the unit-propagation-refutable cubes) were
regenerated on the University of South Carolina HPC on 2026-07-21 after the
original trimmed copies were destroyed by an `lrat-trim` output bug on a full
disk (fix submitted upstream). The regeneration job gate-tested its checker
before running; every regenerated proof passed both `lrat-check` (anchored) and
`lrat-trim --check` on the cluster; the delta was transferred with per-file
SHA-256 pinned cluster-side and re-verified byte-for-byte locally. The remaining
46,273 proofs are the original campaign's trimmed certificates. All 98,536 share
the same HPC solving provenance.

**Relation to the Lean development.** `lean/ConwayO7/Final.lean` proves
that if every cube of the embedded tiling is UNSAT, then no srg(99,14,1,2)
admits an automorphism of order 7 — with the tiling's exact coverage, encoder
faithfulness, and byte identity of the embedded `o7.cnf` proved inside Lean.
The cake_lpr verdict above discharges that sole hypothesis externally; one cube
(index 4092) is additionally replayed inside Lean's kernel (`cube4093_unsat`).
