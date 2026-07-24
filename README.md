# No order-7 automorphism of a Conway 99-graph

Certified proof that **no strongly regular graph with parameters (99, 14, 1, 2)
admits an automorphism of order 7** — equivalently, 7 does not divide |Aut Γ| for
any such Γ (Conway's 99-graph problem).

The result is a machine-checked composition of two halves that meet at one file:

- **Lean 4 / mathlib** (`lean/`): theorem `ConwayO7.no_aut_seven` proves
  the claim *assuming* every cube of an explicit 98,536-cube tiling is
  unsatisfiable. The tiling's exactness (prefix-free, full Kraft mass), the
  SAT encoder's faithfulness, and the byte identity of the embedded CNF are all
  proved inside Lean.
- **SAT certificates** (`artifact/`): one LRAT unsatisfiability proof per cube,
  each verified by **cake_lpr**, the LRAT checker formally verified in HOL4 down
  to machine code. Certificate `proofs/i.lrat.zst` corresponds to line `i` of
  `cubes_all.txt` — the same file Lean embeds byte-for-byte.

**Referees**: start at [`REFEREE.md`](REFEREE.md) — a
three-command verification protocol (Apptainer container included).

The proof archives (~77 GB) and the container image are distributed via the
Zenodo deposit (DOI in the paper), not this repository; everything needed to
*rebuild* them from the pinned sources is here.

