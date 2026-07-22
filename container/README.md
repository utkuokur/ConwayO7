# Container project — verified LRAT checking for the o7 certificate

Home of the Apptainer containerization of **cake_lpr** (the HOL4-verified
LRAT/LPR proof checker), giving referees a one-command, dependency-free way to
re-verify all 98,536 certificates of the order-7 non-existence artifact.

## Contents

- `cake_lpr.def` — Apptainer definition (mirrored in `../artifact/`): Ubuntu 24.04
  base, builds cake_lpr from the upstream repository after checking
  `cake_lpr.S` against the upstream-pinned SHA-256
  `2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a`.
- `cake_lpr.sif` — the built image (also in `../artifact/`); its SHA-256 is
  recorded in `SIF_SHA256` and in `../artifact/SHA256SUMS`.
- `SIF_SHA256` — hash + build environment record.

## Usage

```bash
apptainer build cake_lpr.sif cake_lpr.def          # or use the shipped .sif
apptainer exec ./cake_lpr.sif cake_lpr F.cnf p.lrat  # single check
CAKE="apptainer exec ./cake_lpr.sif cake_lpr" P=8 ../artifact/cake_verify.sh  # full run
```

See `../artifact/REFEREE.md` for the complete referee protocol and timings.
