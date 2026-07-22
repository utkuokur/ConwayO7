/-
The first-round tiling, verified on the concrete data.

`cubes.txt` splits on DIMACS variables 15–26 (0-based 14–25) — a full binary tree of
depth 12, i.e. 4096 cubes.  Here the verified coverage checker of
`ConwayO7/CoverageCheck.lean` runs on the actual embedded cube data
(`o7FirstRound_checkCover`), and `o7cubeSigns_eq` verifies that the sign-string model
used by theorem T1 reconstructs the parsed cubes exactly.

`no_aut_seven_of_firstRound_certificates` is then the fully concrete pipeline
instance: its only remaining hypotheses are the 4096 per-cube UNSAT facts (certified
externally by the hash-pinned LRAT files; `cube4093_unsat` is one of them, replayed
inside Lean) and encoder faithfulness (layer L4/L5).

Note: the artifact's final certificate certifies 4095 of these 4096 cubes directly;
the remaining one is refined further (`cubes4091.txt` and the `nucleus/` rounds,
98,536 leaves in total).  The full flattened tiling is checked with the same
machinery in `ConwayO7/Data/FullTiling.lean`, which is the authoritative version;
this file documents the simpler first-round instance.
-/
import ConwayO7.Data.O7
import ConwayO7.Pipeline

namespace ConwayO7

open Std.Sat

/-- The branching order of the cube split: DIMACS variables 15–26, i.e. 0-based
variables 14–25. -/
def cubeOrder : List Nat := (List.range 12).map (14 + ·)

/-- The first-round cubes as sign strings along `cubeOrder`. -/
def o7cubeSigns : List (List Bool) := o7cubes.map (fun c ↦ c.map (·.2))

/-- The sign-string model is faithful: rebuilding each cube from its sign string along
`cubeOrder` reproduces the parsed `cubes.txt` cubes exactly. -/
theorem o7cubeSigns_eq : o7cubeSigns.map (cubeOfSigns cubeOrder) = o7cubes := by
  native_decide

/-- **Coverage of the first-round tiling, computed**: the 4096 sign strings of
`cubes.txt` pass the verified coverage check (antichain with full Kraft mass at
depth 12). -/
theorem o7FirstRound_checkCover : checkCover cubeOrder.length o7cubeSigns = true := by
  native_decide

/-- **The pipeline on the concrete data.**  Remaining obligations only:
the 4096 per-cube UNSAT certificates and encoder faithfulness. -/
theorem no_aut_seven_of_firstRound_certificates
    (hcubes : ∀ s ∈ o7cubeSigns, CNF.Unsat (withCube o7cnf (cubeOfSigns cubeOrder s)))
    (henc : EncodesInvariantSRG o7cnf)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) :=
  no_aut_seven_of_checked_certificates o7cnf cubeOrder o7cubeSigns
    o7FirstRound_checkCover hcubes henc G hG

end ConwayO7
