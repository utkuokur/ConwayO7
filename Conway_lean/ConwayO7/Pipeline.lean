/-

This file composes everything proved so far into the project's target statement,

  UNSAT(o7.cnf)  ⟹  every srg(99,14,1,2) has  7 ∤ |Aut Γ|,

with exactly ONE open obligation left, stated as `EncodesInvariantSRG`:

  L4/L5 (encoder faithfulness + symmetry-breaking completeness):
    every σ₀-invariant srg(99,14,1,2) on Fin 99 yields a satisfying
    assignment of the CNF.

Note the direction: only "graph ⟹ assignment" is needed for the headline theorem —
if the CNF were satisfiable-but-meaningless the conclusion would be vacuous, not wrong;
UNSAT does the refuting.  (The converse "assignment ⟹ graph" is what makes a SAT
answer meaningful, but no SAT answer is being claimed.)

`no_aut_seven_of_certificates` additionally inlines T1, so its hypotheses are exactly
the shipped artifact's obligations: the cube list's prefix-freeness and full Kraft mass
(to be discharged by `decide` on the concrete cube data), one `Unsat` fact per cube
(cake_lpr on hash-pinned files, or `Std.Tactic.BVDecide.LRAT.check_sound` in-kernel),
and `EncodesInvariantSRG o7cnf`.
-/
import ConwayO7.Main
import ConwayO7.Canonical
import ConwayO7.CoverageCheck

open Std.Sat

namespace ConwayO7

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The L4/L5 obligation**: whenever a σ₀-invariant
srg(99,14,1,2) exists on `Fin 99`, the formula `F` is satisfiable.
For `F = o7.cnf` this is the encoder-faithfulness theorem for
`tools/conway_o7.py` — orbit variables, cardinality counters,
and completeness of the symmetry-breaking clauses. -/
def EncodesInvariantSRG (F : CNF Nat) : Prop :=
  ∀ H : SimpleGraph (Fin 99), ∀ _ : DecidableRel H.Adj, H.IsSRGWith 99 14 1 2 →
    (∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v) → ∃ a, CNF.Sat a F

/-- **Conditional main theorem**: if `F` is unsatisfiable and `F` encodes
σ₀-invariant srg(99,14,1,2)s, then no srg(99,14,1,2) on any vertex type has
automorphism-group order divisible by 7. -/
theorem no_aut_seven_of_unsat {F : CNF Nat} (henc : EncodesInvariantSRG F)
    (hunsat : CNF.Unsat F) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) := by
  refine seven_not_dvd_card_aut_of_no_sigma0_invariant (fun H instH hH hinv ↦ ?_) hG
  obtain ⟨a, ha⟩ := henc H instH hH hinv
  rw [CNF.Sat, hunsat a] at ha
  exact Bool.false_ne_true ha

/-- **The complete certificate schema** — T1 composed with T2.  Its hypotheses are
exactly the artifact's remaining proof obligations:
* `hlen`, `hpf`, `hkraft`: the 98,536 sign strings are a prefix-free family of full
  Kraft mass;
* `hcubes`: each cube-augmented formula is UNSAT (certified by cake_lpr on the
  hash-pinned LRAT files, or in-kernel by `Std.Tactic.BVDecide.LRAT.check_sound`);
* `henc`: encoder faithfulness (layer L4/L5, open).
Conclusion: no strongly regular (99,14,1,2) graph admits 7 ∣ |Aut Γ| — in particular
a Conway 99-graph, if one exists, has no order-7 automorphism. -/
theorem no_aut_seven_of_certificates (F : CNF Nat) (order : List Nat) (S : List (List Bool))
    (hlen : ∀ s ∈ S, s.length ≤ order.length)
    (hpf : PrefixFree S)
    (hkraft : kraftWeight order.length S = 2 ^ order.length)
    (hcubes : ∀ s ∈ S, CNF.Unsat (withCube F (cubeOfSigns order s)))
    (henc : EncodesInvariantSRG F)
    (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) :=
  no_aut_seven_of_unsat henc (unsat_of_prefix_cover F order S hlen hpf hkraft hcubes) G hG

/-- `no_aut_seven_of_certificates` with the three coverage hypotheses replaced by the
single executable check of `ConwayO7/CoverageCheck.lean` — the form the concrete data
layer will discharge by computation. -/
theorem no_aut_seven_of_checked_certificates (F : CNF Nat) (order : List Nat)
    (S : List (List Bool))
    (hchk : checkCover order.length S = true)
    (hcubes : ∀ s ∈ S, CNF.Unsat (withCube F (cubeOfSigns order s)))
    (henc : EncodesInvariantSRG F)
    (hG : G.IsSRGWith 99 14 1 2) :
    ¬7 ∣ Nat.card (G ≃g G) :=
  no_aut_seven_of_unsat henc (unsat_of_checked_cover F order S hchk hcubes) G hG

end ConwayO7
