/-
We show that the Lean generator reproduces `o7.cnf` exactly.
`mkO7Cnf_eq` verifies — inside Lean, over the embedded bytes — that the ported
generator of `ConwayO7/Encoder.lean` emits precisely the parsed `artifact/o7.cnf`:
same clauses, same order, same literals, same variable count.  Together with the
byte-identity theorem `o7cnf_bytes`, every structural fact we prove about
`Encoder.mkO7Cnf`'s gadgets transfers verbatim to the formula the LRAT certificates
refute.
-/
import ConwayO7.Encoder
import ConwayO7.Data.O7

namespace ConwayO7

/-- The generated variable count matches the DIMACS header. -/
theorem mkO7St_top : Encoder.mkO7St.top = 432882 := by native_decide

/-- **The generator is exact**: the Lean-emitted CNF *is* `o7.cnf`. -/
theorem mkO7Cnf_eq : Encoder.mkO7Cnf = o7cnf :=
  congrArg Std.Sat.CNF.mk (by native_decide : Encoder.mkO7Cnf.clauses = o7cnf.clauses)

end ConwayO7
