/-
With encoder faithfulness (`encodes_o7`) proved,
the only remaining obligation of the whole development is one `Unsat`
fact per certified cube — delivered by the hash-pinned LRAT
certificates through cake_lpr
(with `cube4093_unsat` replayed inside Lean as a sample).
-/

import ConwayO7.Data.FullTiling
import ConwayO7.Complete

open Std.Sat

namespace ConwayO7

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Main theorem, modulo the LRAT certificates.** -/
theorem no_aut_seven
    (hcubes : ∀ s ∈ tilingSigns,
    CNF.Unsat (withCube o7cnf (cubeOfSigns tilingOrder s)))
    (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) :=
  no_aut_seven_of_tiling_certificates hcubes Encoder.encodes_o7 G hG

end ConwayO7
