# Provenance — not part of the verification path

Historical/reproduction material. Nothing here is needed to verify the result:

- `conway_o7.py` — the Python encoder that originally generated `o7.cnf`.
  Superseded as a trust element by the Lean byte-identity theorem
  (`Encoder.mkO7Cnf_eq`): Lean re-derives the CNF and proves it equal to the
  embedded bytes. Kept so the formula's origin can be reproduced and compared.
- `lrat-check` — Biere's C LRAT checker, used during the solving campaign.
  Superseded by the formally verified cake_lpr (see `../REFEREE.md`). Kept as an
  independent second checker for the curious: it accepts exactly the same
  proofs (anchored gate: `^c VERIFIED`, exit 0).
- `SIF_BUILD_RECORD.md` — build environment of the shipped `../cake_lpr.sif`

  (its fingerprint lives in `../SHA256SUMS` like every other file).
