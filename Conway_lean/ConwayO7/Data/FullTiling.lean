/-
The FULL certified tiling — all 98,536 cubes of the artifact, embedded in Lean.

`cubes_all.txt` is the consolidated cube list: one cube per certificate, in
manifest order (it replaces the historical 18-file layout of `cubes.txt`,
`cubes4091.txt` and the nucleus queues; `manifest_all.tsv` maps line `i` to the
`i`-th proof file).  The file is embedded byte-for-byte (`include_str`) and parsed
in Lean, so no external preprocessing sits between the hash-pinned file and the
verified coverage check.

`o7Tiling_checkCover` runs the verified checker of `ConwayO7/CoverageCheck.lean`
on the actual 98,536 sign strings: they are a prefix-free family of full Kraft
mass at depth 200 — a perfect tiling of the whole search space.  This replaces
`check_coverage.py` in the trusted base, for the complete certificate.

(Coverage soundness does not depend on trusting the cube list's provenance: if
`cubes_all.txt` selected a wrong cube set, `checkCover` would fail — the file only
chooses WHICH certified tiling we verify.)
-/
import ConwayO7.Data.O7
import ConwayO7.Pipeline

namespace ConwayO7

open Std.Sat

/-! ### The embedded cube list -/

/-- `artifact/cubes_all.txt`: the 98,536 certified cubes, one per line, in
manifest order. -/
def cubesAllTxt : String := include_str "../../../artifact/cubes_all.txt"

/-- **The certified tiling**: one cube per certificate, 98,536 in all. -/
def tilingCubes : List Cube := Dimacs.parseCubes cubesAllTxt

/-- The tiling's branching order: DIMACS variables `15 … 214` (0-based `14 … 213`);
the deepest nucleus cubes fix 200 consecutive split variables. -/
def tilingOrder : List Nat := (List.range 200).map (14 + ·)

/-- The tiling as sign strings along `tilingOrder`. -/
def tilingSigns : List (List Bool) := tilingCubes.map (fun c ↦ c.map (·.2))

/-! ### The tiling, verified -/

/-- The sign-string model is faithful: every cube really is a sign pattern on
consecutive split variables starting at DIMACS 15. -/
theorem tilingSigns_eq : tilingSigns.map (cubeOfSigns tilingOrder) = tilingCubes := by
  native_decide

theorem tiling_count : tilingSigns.length = 98536 := by native_decide

/-- **Coverage of the complete certificate, computed**: the 98,536 certified cubes are
a prefix-free family of full Kraft mass `2^200` — an exact tiling of the entire
assignment space.  (The Lean replacement of `check_coverage.py`, on the real data.) -/
theorem o7Tiling_checkCover : checkCover tilingOrder.length tilingSigns = true := by
  native_decide

/-- **The pipeline on the complete certificate.**  Remaining obligations only: one
`Unsat` fact per certified cube (the hash-pinned LRAT files, checked by cake_lpr;
`cube4093_unsat` is one, replayed in Lean) and encoder faithfulness (L4/L5). -/
theorem no_aut_seven_of_tiling_certificates
    (hcubes : ∀ s ∈ tilingSigns,
    CNF.Unsat (withCube o7cnf (cubeOfSigns tilingOrder s)))
    (henc : EncodesInvariantSRG o7cnf)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) :=
  no_aut_seven_of_checked_certificates o7cnf tilingOrder tilingSigns
    o7Tiling_checkCover hcubes henc G hG

end ConwayO7
