/-
Layer L0 over the standard library's `Std.Sat.CNF`, so that every statement here
is directly compatible with Lean's bundled formally verified LRAT checker
(`Std.Tactic.BVDecide.LRAT.check_sound : check … cnf → cnf.Unsat`).

`withCube F c` is the formula `F_i = o7.cnf + cube_i` that the artifact's
`verify_final.sh` rebuilds and cake_lpr certifies: the base CNF plus one unit
clause per cube literal.  The composition theorem `unsat_of_cubes` is the schema
of theorem T1 of the Conway order-7 certificate.
-/
import Std.Sat.CNF.Basic

open Std.Sat

namespace ConwayO7

/-- A cube: a conjunction of literals (a partial assignment).
`Std.Sat.CNF.Clause` is a *disjunction*, so cubes get their own evaluator. -/
abbrev Cube := List (Literal Nat)

/-- Conjunction semantics for cubes. -/
def Cube.eval (a : Nat → Bool) (c : Cube) : Bool := c.all fun l ↦ a l.1 == l.2

@[simp] theorem Cube.eval_nil (a : Nat → Bool) : Cube.eval a [] = true := rfl

@[simp] theorem Cube.eval_cons (a : Nat → Bool) (l : Literal Nat) (c : Cube) :
    Cube.eval a (l :: c) = ((a l.1 == l.2) && Cube.eval a c) := rfl

/-- Adjoin a cube to a CNF as unit clauses: the formula
`F_i = o7.cnf + cube_i` of `verify_final.sh`. -/
def withCube (F : CNF Nat) (c : Cube) : CNF Nat := c.foldl (fun G l ↦ G.add [l]) F

@[simp] theorem eval_withCube (a : Nat → Bool) (F : CNF Nat) (c : Cube) :
    CNF.eval a (withCube F c) = (CNF.eval a F && Cube.eval a c) := by
  induction c generalizing F with
  | nil => simp [withCube]
  | cons l c ih =>
    obtain ⟨v, p⟩ := l
    show CNF.eval a (withCube (F.add [(v, p)]) c) = (CNF.eval a F && Cube.eval a ((v, p) :: c))
    rw [ih]
    have hcl : CNF.Clause.eval a [(v, p)] = ((a v == p) || false) := rfl
    simp only [CNF.eval_add, hcl, Bool.or_false, Cube.eval_cons]
    cases a v == p <;> cases CNF.eval a F <;> cases Cube.eval a c <;> rfl

/-- **Cube-and-conquer composition.**  If the cubes cover assignment space and every
cube-augmented formula is unsatisfiable, the base formula is unsatisfiable.
The `Unsat (withCube F c)` hypotheses are exactly the facts certified externally by
cake_lpr (or internally by `Std.Tactic.BVDecide.LRAT.check_sound`) on the shipped files. -/
theorem unsat_of_cubes (F : CNF Nat) (cubes : List Cube)
    (hcov : ∀ a : Nat → Bool, ∃ c ∈ cubes, Cube.eval a c = true)
    (hunsat : ∀ c ∈ cubes, CNF.Unsat (withCube F c)) :
    CNF.Unsat F := by
  intro a
  obtain ⟨c, hc, hca⟩ := hcov a
  have h := hunsat c hc a
  simpa [hca] using h

end ConwayO7
