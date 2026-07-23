/-
The bridge from a σ₀-invariant srg to the generator's semantic invariants.

`assignOfOrbits ω` places the orbit booleans on DIMACS variables `1 … 693`.  If
`graphOfOrbits ω` is an srg(99,14,1,2), then

  * `DegInv` holds: vertex `u`'s 98 orbit literals count its neighbours — exactly 14
    by regularity;
  * `CnInv` holds: orbit `o`'s product count plus its own adjacency is exactly 2 —
    the λ = 1 / μ = 2 identity (with μ − λ = 1 making both cases equal 2).

`Sym1Holds` (and later the lex conditions) are *not* consequences of being an srg:
they constrain WHICH representative of the isomorphism class is encoded, and are
supplied by the L5 lex-leader choice; here they remain hypotheses.
-/
import ConwayO7.SectionsCompose

namespace ConwayO7
namespace Encoder

open TotSpec MtoSpec

/-- The orbit assignment on the DIMACS variable block `1 … 693`. -/
def assignOfOrbits (ω : Nat → Bool) : Nat → Bool := fun v ↦ ω (v - 1)

theorem litSat_evarI (ω : Nat → Bool) (u v : Fin 99) :
    litSat (assignOfOrbits ω) (evarI u v) = ω (orbitOf (u, v)) := by
  unfold litSat evarI assignOfOrbits
  rw [if_neg (by omega : ¬((orbitOf (u, v) + 1 : Nat) : Int) < 0), Int.natAbs_natCast,
    Nat.add_sub_cancel]

/-- Counting over `finRange` equals `Finset` filter cardinality. -/
theorem countP_finRange_eq_card_filter {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    (List.finRange n).countP (fun v ↦ decide (p v)) = (Finset.univ.filter p).card := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

theorem filterMap_if_eq {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (g : α → β) :
    (l.filterMap fun v ↦ if p v then some (g v) else none)
      = (l.filter fun v ↦ decide (p v)).map g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x
    · rw [List.filterMap_cons, if_pos hx, List.filter_cons_of_pos (by simpa using hx),
        List.map_cons, ih]
    · rw [List.filterMap_cons, if_neg hx, List.filter_cons_of_neg (by simpa using hx), ih]

/-! ### Degree counts -/

/-- **Degree bridge**: 14-regularity gives `DegInv`. -/
theorem degInv_of_srg (ω : Nat → Bool)
    (hH : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    DegInv (assignOfOrbits ω) := by
  intro u
  unfold countT degLits
  rw [List.toList_toArray, filterMap_if_eq, List.countP_map, List.countP_filter]
  have hpred : ∀ v ∈ List.finRange 99,
      ((litSat (assignOfOrbits ω) ∘ fun v ↦ evarI u v) v && decide (v ≠ u)) = true
        ↔ decide ((graphOfOrbits ω).Adj u v) = true := by
    intro v _
    rw [Function.comp_apply, litSat_evarI, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq]
    exact ⟨fun ⟨hω, hvu⟩ ↦ ⟨fun h ↦ hvu h.symm, hω⟩,
      fun ⟨huv, hω⟩ ↦ ⟨hω, fun h ↦ huv h.symm⟩⟩
  calc ((List.finRange 99).countP fun v ↦
        (litSat (assignOfOrbits ω) ∘ fun v ↦ evarI u v) v && decide (v ≠ u))
      = (List.finRange 99).countP fun v ↦ decide ((graphOfOrbits ω).Adj u v) :=
        List.countP_congr hpred
    _ = (Finset.univ.filter ((graphOfOrbits ω).Adj u)).card :=
        countP_finRange_eq_card_filter _
    _ = (graphOfOrbits ω).degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.neighborFinset_eq_filter]
    _ = 14 := hH.regular u

/-! ### Common-neighbour counts -/

/-- **μ/λ bridge**: the srg identities give `CnInv` (both cases equal 2 because
μ − λ = 1). -/
theorem cnInv_of_srg (ω : Nat → Bool)
    (hH : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    CnInv (assignOfOrbits ω) := by
  intro o ho
  have hr := orbitRep_lt o ho
  set r := orbitRep o with hrdef
  have hrne : r.1 ≠ r.2 := Fin.ne_of_lt hr
  unfold cnCountR
  rw [← countP_eq_count_true]
  -- the product count over the candidates is the common-neighbour count
  have hcount : ((validW r).countP
      fun w ↦ litSat (assignOfOrbits ω) (evarI r.1 w) &&
        litSat (assignOfOrbits ω) (evarI r.2 w))
      = (Finset.univ.filter
          (fun w ↦ w ∈ (graphOfOrbits ω).commonNeighbors r.1 r.2)).card := by
    unfold validW
    rw [List.countP_filter]
    have hpred : ∀ w ∈ List.finRange 99,
        ((litSat (assignOfOrbits ω) (evarI r.1 w) &&
            litSat (assignOfOrbits ω) (evarI r.2 w)) &&
          decide (w ≠ r.1 ∧ w ≠ r.2)) = true
          ↔ decide (w ∈ (graphOfOrbits ω).commonNeighbors r.1 r.2) = true := by
      intro w _
      rw [litSat_evarI, litSat_evarI, Bool.and_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, decide_eq_true_eq,
        SimpleGraph.mem_commonNeighbors]
      constructor
      · rintro ⟨⟨hω1, hω2⟩, h1, h2⟩
        exact ⟨⟨fun h ↦ h1 h.symm, hω1⟩, ⟨fun h ↦ h2 h.symm, hω2⟩⟩
      · rintro ⟨⟨h1, hω1⟩, ⟨h2, hω2⟩⟩
        exact ⟨⟨hω1, hω2⟩, fun h ↦ h1 h.symm, fun h ↦ h2 h.symm⟩
    rw [List.countP_congr hpred, countP_finRange_eq_card_filter _]
  rw [hcount, litSat_evarI]
  -- the filter cardinality is the srg's common-neighbour count
  have hcard : (Finset.univ.filter
        (fun w ↦ w ∈ (graphOfOrbits ω).commonNeighbors r.1 r.2)).card
      = Fintype.card ((graphOfOrbits ω).commonNeighbors r.1 r.2) := by
    rw [← Fintype.card_subtype]
  rw [hcard]
  -- split on the representative pair's own adjacency
  by_cases hadj : (graphOfOrbits ω).Adj r.1 r.2
  · have hω : ω (orbitOf (r.1, r.2)) = true := hadj.2
    rw [hH.of_adj r.1 r.2 hadj, if_pos hω]
  · have hω : ¬ω (orbitOf (r.1, r.2)) = true := fun hω ↦ hadj ⟨hrne, hω⟩
    rw [hH.of_not_adj hrne hadj, if_neg hω]

/-- **The pre-lex bridge**: a σ₀-invariant srg (as an orbit assignment) satisfying the
level-1 symmetry choice satisfies all pre-lex semantic invariants. -/
theorem preLexInv_of_srg (ω : Nat → Bool)
    (hH : (graphOfOrbits ω).IsSRGWith 99 14 1 2)
    (hsym1 : Sym1Holds (assignOfOrbits ω)) :
    PreLexInv (assignOfOrbits ω) :=
  ⟨degInv_of_srg ω hH, cnInv_of_srg ω hH, hsym1⟩

end Encoder
end ConwayO7
