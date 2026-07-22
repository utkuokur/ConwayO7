/-
In-Lean sample verification of a certified cube — the "zero translation gap" check.

`sample_4093.lrat` is the decompressed `artifact/proofs/4093.lrat.zst`
(SHA-256 of the compressed file:
  363f24557baaa735af8f6c311be92b940b4c16c1c2dbba271f5c261c1027c34c,
pinned in `SHA256SUMS`; manifest line: `proofs/4093.lrat  cubes.txt  4093`).

`cube4093_unsat` replays that certificate through Lean's own formally verified LRAT
checker (`Std.Tactic.BVDecide.LRAT.check_sound`) against `withCube o7cnf (cube 4093)`
— the formula built from the byte-identical embedded data by the same `withCube` the
T1 pipeline uses. A sign-flip, off-by-one, or clause-order mismatch anywhere in the
conventions would make this check fail loudly.

The `check … = true` fact is computed by `native_decide` (compiled execution of the
verified checker, carrying `Lean.ofReduceBool`), as in `bv_decide`'s own LRAT replay.
This is the calibration sample; bulk coverage of all 98,536 cubes stays with the
external checkers on the hash-pinned files.
-/
import ConwayO7.Data.FullTiling
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

namespace ConwayO7

open Std.Tactic.BVDecide

/-- The decompressed LRAT certificate for cube 4093. -/
def sampleLrat4093 : String := include_str "sample_4093.lrat"

/-- The parsed certificate (empty on parse failure, which would then fail `check`). -/
def sampleProof4093 : Array LRAT.IntAction :=
  match LRAT.parseLRATProof sampleLrat4093.toUTF8 with
  | .ok a => a
  | .error _ => #[]

/-- `F_4092 = o7.cnf + tiling cube 4092` (historically cube 4093 of the first-round
split), exactly as `check_one.sh` rebuilds it: base clauses in file order, then one
unit clause per cube literal in line order. -/
def F4093 : Std.Sat.CNF Nat := withCube o7cnf (tilingCubes.getD 4092 [])

/-- **Sample certificate, verified inside Lean**: cube 4093 of the artifact is
genuinely UNSAT, by the Lean-verified LRAT checker on the embedded bytes. -/
theorem cube4093_unsat : Std.Sat.CNF.Unsat F4093 :=
  LRAT.check_sound sampleProof4093 F4093 (by native_decide)

end ConwayO7
