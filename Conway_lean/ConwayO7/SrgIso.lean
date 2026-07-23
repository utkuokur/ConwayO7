/-
Strong regularity transports across graph isomorphisms:
`IsSRGWith.of_iso`, used twice by the lex-leader
completeness layer: once for the abstract cycle relabeling that establishes the
level-1 symmetry choice, and once per lex generator during minimization.
-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace ConwayO7

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism carries common-neighbour sets to common-neighbour sets. -/
def isoCommonNeighbors (e : G ≃g H) (v w : V) :
    G.commonNeighbors v w ≃ H.commonNeighbors (e v) (e w) :=
  Equiv.subtypeEquiv e.toEquiv fun u ↦ by
    rw [mem_commonNeighbors, mem_commonNeighbors]
    exact and_congr (e.map_adj_iff).symm (e.map_adj_iff).symm

/-- **Strong regularity across an isomorphism.** -/
theorem IsSRGWith.of_iso [Fintype V] [Fintype W]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) {n k l m : ℕ} (h : H.IsSRGWith n k l m) : G.IsSRGWith n k l m where
  card := e.card_eq.trans h.card
  regular := fun v ↦ by
    rw [← card_neighborSet_eq_degree, Fintype.card_congr (e.mapNeighborSet v),
      card_neighborSet_eq_degree]
    exact h.regular (e v)
  of_adj := fun v w hadj ↦ by
    rw [Fintype.card_congr (isoCommonNeighbors e v w)]
    exact h.of_adj (e v) (e w) (e.map_adj_iff.mpr hadj)
  of_not_adj := fun v w hne hnadj ↦ by
    rw [Fintype.card_congr (isoCommonNeighbors e v w)]
    exact h.of_not_adj (fun hew ↦ hne (e.toEquiv.injective hew))
      (fun hadj ↦ hnadj (e.map_adj_iff.mp hadj))

end ConwayO7
