# Build record — cake_lpr.sif

The shipped checker image `../cake_lpr.sif` (SIF = Singularity Image Format,
Apptainer's single-file container format) was built:

- date: 2026-07-22
- builder: Apptainer 1.5.3, WSL2 (Ubuntu 24.04 host)
- base image: docker://ubuntu:24.04
- definition: `../cake_lpr.def` — its `%post` step compiles cake_lpr from the
  upstream repository after verifying `cake_lpr.S` against the upstream-pinned
  SHA-256 (`2f3af32d…`, the value published by the cake_lpr authors)

The image's own fingerprint is pinned, like every artifact file, in
`../SHA256SUMS` (entry `./cake_lpr.sif`) — the single source of truth for hashes.
