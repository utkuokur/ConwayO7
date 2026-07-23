/-
L4 — composing the proved sections.

The generator emits degrees, then common-neighbour gadgets, then the level-1
symmetry units, then the lex chains.  This file chains the three proved section
triples under the master invariant `PreLexInv` (14-regularity counts, μ-counts,
and the level-1 orbit values), transfers the CN section from its spec form to the
imperative emission via the computational glue (`cn_states_eq` — the two states are
*equal*, not merely equisatisfiable), and delivers `preLex_sat`:

    every assignment of the orbit block satisfying `PreLexInv` extends to a
    satisfying assignment of ALL generator clauses before the lex sections.

What remains for `EncodesInvariantSRG` after this file: the lex-chain triple and its
lex-leader completeness (L5), and the bridge from a σ₀-invariant srg to `PreLexInv`.
-/
import ConwayO7.DegSpec

namespace ConwayO7
namespace Encoder

open TotSpec MtoSpec

/-! ### The master pre-lex invariant -/

/-- All semantic conditions of the pre-lex sections. -/
def PreLexInv (a : Nat → Bool) : Prop := DegInv a ∧ CnInv a ∧ Sym1Holds a

theorem Sym1Holds_congr {a b : Nat → Bool} (h : ∀ v ≤ 693, b v = a v)
    (hi : Sym1Holds a) : Sym1Holds b := fun i hi14 ↦ by
  rw [h _ (sym1_var_lt i hi14)]
  exact hi i hi14

theorem PreLexInv_congr {a b : Nat → Bool} (h : ∀ v ≤ 693, b v = a v)
    (hi : PreLexInv a) : PreLexInv b :=
  ⟨DegInv_congr h hi.1, CnInv_congr h hi.2.1, Sym1Holds_congr h hi.2.2⟩

/-! ### The three sections under the master invariant -/

theorem deg_section_trip' :
    GTrip PreLexInv (fun s ↦ (List.finRange 99).foldl degreeStep s) PreLexInv :=
  deg_section_trip.adapt (fun _ hp ↦ hp.1) fun _ a' hag hp hq ↦
    ⟨hq, CnInv_congr hag hp.2.1, Sym1Holds_congr hag hp.2.2⟩

theorem cn_section_trip' :
    GTrip PreLexInv (fun s ↦ (List.range 693).foldl specCnStep s) PreLexInv :=
  cn_section_trip.adapt (fun _ hp ↦ hp.2.1) fun _ a' hag hp hq ↦
    ⟨DegInv_congr hag hp.1, hq, Sym1Holds_congr hag hp.2.2⟩

theorem sym1_section_trip' :
    GTrip PreLexInv (fun s ↦ (List.range 14).foldl sym1Step s) PreLexInv :=
  sym1_section_trip.adapt (fun _ hp ↦ hp.2.2) fun _ a' hag hp hq ↦
    ⟨DegInv_congr hag hp.1, CnInv_congr hag hp.2.1, hq⟩

set_option maxRecDepth 4000 in
/-- The composed spec-level pre-lex pipeline. -/
theorem preLexSpec_trip :
    GTrip PreLexInv
      (fun s ↦ (List.range 14).foldl sym1Step
        ((List.range 693).foldl specCnStep ((List.finRange 99).foldl degreeStep s)))
      PreLexInv :=
  deg_section_trip'.comp (cn_section_trip'.comp sym1_section_trip')

/-! ### From the spec CN section to the emitted one -/

theorem St.ext' {x y : St} (ht : x.top = y.top) (hc : x.cls = y.cls) : x = y := by
  cases x
  cases y
  simp_all

/-- The spec-level and imperative CN sections produce the *same state* on the
concrete pipeline. -/
theorem cn_states_eq :
    (List.range 693).foldl specCnStep afterDegrees
      = (List.range 693).foldl cnStep afterDegrees :=
  St.ext' cn_section_agrees.2 cn_section_agrees.1

/-- The generator state after degrees, CN and level-1 units (as emitted). -/
def preLexSt : St :=
  (List.range 14).foldl sym1Step ((List.range 693).foldl cnStep afterDegrees)

/-! ### The pre-lex satisfiability theorem -/

theorem WF_init : WF (⟨693, #[]⟩ : St) := by
  refine ⟨le_refl _, ?_⟩
  intro c hc
  simp at hc

/-- **Pre-lex satisfiability**: any orbit assignment with the three semantic
invariants extends (above variable 693) to satisfy every generator clause before
the lex sections. -/
theorem preLex_sat (a : Nat → Bool) (hp : PreLexInv a) :
    ∃ a', (∀ v ≤ 693, a' v = a v) ∧ SatAll a' preLexSt ∧ WF preLexSt ∧ PreLexInv a' := by
  obtain ⟨a', hag, hsat, hw, hq⟩ :=
    preLexSpec_trip.sat ⟨693, #[]⟩ a WF_init (satAll_init a 693) hp
  have heq : (List.range 14).foldl sym1Step
      ((List.range 693).foldl specCnStep ((List.finRange 99).foldl degreeStep ⟨693, #[]⟩))
      = preLexSt := by
    show (List.range 14).foldl sym1Step
      ((List.range 693).foldl specCnStep afterDegrees) = preLexSt
    rw [cn_states_eq]
    rfl
  rw [heq] at hsat hw
  exact ⟨a', hag, hsat, hw, hq⟩

end Encoder
end ConwayO7