# Referee guide — verifying the order-7 non-existence certificate

**Claim.** No strongly regular graph with parameters (99, 14, 1, 2) admits an
automorphism of order 7 (equivalently, `7 ∤ |Aut Γ|` for every such Γ).

Verification has two independent halves, meeting at one shared file:

- **Lean 4** proves: *if* every cube of the embedded tiling is UNSAT, the claim
  holds (`ConwayO7.no_aut_seven` in `../Conway_lean/`); coverage of the tiling,
  encoder faithfulness, and the byte-identity of the embedded `o7.cnf` are all
  proved inside Lean.
- **cake_lpr** (HOL4-verified LRAT checker) certifies: every cube *is* UNSAT —
  98,536 hash-pinned proofs, log in `cake_report.txt`.
- The two halves quantify over the *same* cubes because `cubes_all.txt` is both
  byte-embedded in Lean (`include_str`) and the input of the checker script,
  under one SHA-256 pin.

## What you must trust, and what you can check

| Element | Grade | Check |
|---|---|---|
| Lean statements say what the paper claims | referee reads | `Conway_lean/ConwayO7/Final.lean` (+ defs it references) |
| Lean kernel + mathlib | standard | `lake build` succeeds |
| 19 `native_decide` facts (Lean's compiled evaluator) | small | listed by `#print axioms ConwayO7.no_aut_seven`; each is a finite computation; one cube is replayed native-free in-kernel (`cube4093_unsat`) |
| cake_lpr verdicts | **must re-run** | steps below |
| HOL4/CakeML soundness | tiny | build uses upstream `cake_lpr.S`, SHA-256-pinned |

## Three-command verification

Requires: Apptainer (or Singularity), ~50 GB disk, any x86-64 Linux.

```bash
# 1. build the checker container from source (or use the shipped cake_lpr.sif)
apptainer build cake_lpr.sif cake_lpr.def

# 2. verify all 98,536 certificates (hash-pin -> rebuild formula -> cake_lpr)
CAKE="apptainer exec ./cake_lpr.sif cake_lpr" P=8 ./cake_verify.sh
# expect final line: "report: 98536 OK / 98536 checked ...; FAIL=0, MISSING=0, BADHASH=0"

# 3. check the Lean half (in ../Conway_lean; needs elan; mathlib cache included)
lake build && echo '#print axioms ConwayO7.no_aut_seven' | lake env lean --stdin
```

Spot-check a single cube end to end with `./check_one.sh <n>`.

### Timing (measured, cake_lpr step)

| Cores (`P=`) | Wall time |
|---|---|
| 4 | ≈ 2 days |
| 8 | ≈ 1 day |
| 14 | ≈ 12 h |

Memory: ~2 GB per parallel job. The run is resumable: re-invoking
`cake_verify.sh` skips everything already `OK` in `cake_report.txt`.
The Lean build is ~1–2 h (first run; native checks included).

## Integrity

`SHA256SUMS` pins every file in this artifact (201,777 entries); verify with
`sha256sum -c SHA256SUMS`. Repair/provenance history: `CAKE_VERIFICATION_REPORT.md`.
