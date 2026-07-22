/-
The automorphism group of a graph and the Cauchy reduction.

`G ≃g G` is a group via mathlib's `RelIso` instance; `autToPerm` forgets an automorphism
to a vertex permutation.

Cauchy's theorem (`exists_prime_orderOf_dvd_card`) turns
`7 ∣ |Aut Γ|` into a single order-7 automorphism, to which the layer-L3 cycle-type lemma
(`ConwayO7/CycleType.lean`) applies:

  7 ∣ |Aut Γ|  ⟹  ∃ σ, orderOf σ = 7          (`exists_aut_orderOf_eq_seven`)
              ⟹  cycle type [1, 7¹⁴]           (`cycleType_autToPerm`)

so ruling out one order-7 automorphism — the job of L4/L5 + T1, via the canonical
σ₀ of `tools/conway_o7.py` — rules out all of `7 ∣ |Aut Γ|`
(`seven_not_dvd_card_aut`).

-/
import ConwayO7.CycleType
import Mathlib.Algebra.Order.Group.End

namespace ConwayO7

variable {V : Type*} (G : SimpleGraph V)

/-- The forgetful monoid homomorphism from graph automorphisms to vertex permutations. -/
def autToPerm : (G ≃g G) →* Equiv.Perm V :=
  MonoidHom.mk' (fun σ ↦ σ.toEquiv) fun _ _ ↦ rfl

theorem autToPerm_injective : Function.Injective (autToPerm G) := fun _ _ h ↦
  RelIso.ext fun v ↦ Equiv.ext_iff.mp h v

variable [Fintype V]

instance : Finite (G ≃g G) :=
  Finite.of_injective (autToPerm G) (autToPerm_injective G)

/-- **L2, Cauchy step**: if 7 divides the order of the automorphism group, some
automorphism has order exactly 7. -/
theorem exists_aut_orderOf_eq_seven (h : 7 ∣ Nat.card (G ≃g G)) :
    ∃ σ : G ≃g G, orderOf σ = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  haveI := Fintype.ofFinite (G ≃g G)
  rw [Nat.card_eq_fintype_card] at h
  exact exists_prime_orderOf_dvd_card 7 h

/-- **T2 outer reduction**: to refute `7 ∣ |Aut Γ|` it suffices to refute a single
order-7 automorphism — the hypothesis L4/L5 + T1 will discharge. -/
theorem seven_not_dvd_card_aut (hno : ∀ σ : G ≃g G, orderOf σ ≠ 7) :
    ¬7 ∣ Nat.card (G ≃g G) := fun h ↦
  let ⟨σ, hσ⟩ := exists_aut_orderOf_eq_seven G h
  hno σ hσ

variable [DecidableEq V] [DecidableRel G.Adj]

/-- **L2 + L3**: an order-7 automorphism of an srg(99,14,1,2) moves the 99 vertices in
one fixed vertex and fourteen 7-cycles — the canonical shape `σ₀` encoded by
`tools/conway_o7.py` is WLOG (up to the L4/L5 relabeling step). -/
theorem cycleType_autToPerm (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (hord : orderOf σ = 7) :
    (autToPerm G σ).cycleType = Multiset.replicate 14 7 :=
  cycleType_eq_replicate (fun _ _ ↦ σ.map_adj_iff) hG
    ((orderOf_injective (autToPerm G) (autToPerm_injective G) σ).trans hord)

end ConwayO7
