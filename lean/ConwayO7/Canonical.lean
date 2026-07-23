/-
Layer L3, Step 5 — WLOG the canonical σ₀.

`sigma0` is the exact permutation `build_sigma(99, fixed=1, cyc_len=7)` of
`tools/conway_o7.py`: vertex 0 fixed, the other 98 vertices in fourteen consecutive
blocks `[1+7i, …, 7+7i]`, each rotated cyclically.  Its cycle type `[1, 7¹⁴]` is
*computed* (`decide`), not assumed.

Main result (`exists_sigma0_invariant`): if any srg(99,14,1,2) on any vertex type
admits an order-7 automorphism, then some srg(99,14,1,2) on `Fin 99` is invariant
under `sigma0` itself.  Chain: transport the graph to `Fin 99` (`SimpleGraph.Iso.comap`),
push the automorphism through (`Equiv.permCongrHom`), apply the L3 cycle-type lemma,
conjugate onto `sigma0` (`Equiv.Perm.isConj_iff_cycleType_eq`), and relabel once more.

Together with L2 (`seven_not_dvd_card_aut_of_no_sigma0_invariant`), this reduces
`∀ Γ srg(99,14,1,2), 7 ∤ |Aut Γ|` to the single concrete statement

    no σ₀-invariant srg(99,14,1,2) exists on Fin 99

— which is exactly what `o7.cnf` encodes (layer L4) and T1 + cake_lpr refute.
-/
import ConwayO7.Aut

open Finset

namespace ConwayO7

/-! ### Transporting `IsSRGWith` along a graph isomorphism -/

section Transport

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Strong regularity is invariant under graph isomorphism. -/
theorem isSRGWith_of_iso (e : G ≃g H) {n k ℓ μ : ℕ} (hG : G.IsSRGWith n k ℓ μ) :
    H.IsSRGWith n k ℓ μ := by
  have hcn : ∀ u w : W, Fintype.card (H.commonNeighbors u w)
      = Fintype.card (G.commonNeighbors (e.symm u) (e.symm w)) := by
    intro u w
    refine Fintype.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun z ↦ ?_)
    simp only [SimpleGraph.mem_commonNeighbors]
    exact and_congr e.symm.map_adj_iff.symm e.symm.map_adj_iff.symm
  refine ⟨e.card_eq.symm.trans hG.card, fun w ↦ ?_, fun u w h ↦ ?_, fun u w hne h ↦ ?_⟩
  · rw [← SimpleGraph.card_neighborSet_eq_degree,
      Fintype.card_congr (e.symm.mapNeighborSet w), SimpleGraph.card_neighborSet_eq_degree]
    exact hG.regular _
  · rw [hcn]
    exact hG.of_adj _ _ (e.symm.map_adj_iff.mpr h)
  · rw [hcn]
    exact hG.of_not_adj (fun hc ↦ hne (e.symm.toEquiv.injective hc))
      (fun hc ↦ h (e.symm.map_adj_iff.mp hc))

end Transport

/-! ### Cycle type from a fixed-point count -/

/-- A permutation with `π ^ p = 1` (`p` prime), `π ≠ 1`, and `f` fixed points on a
type of size `f + p * m` has cycle type `[pᵐ]`. -/
theorem cycleType_eq_replicate_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) {p m f : ℕ} (hp : p.Prime) (hπ : π ^ p = 1) (hne : π ≠ 1)
    (hfix : #(univ.filter fun a ↦ π a = a) = f)
    (hcard : Fintype.card α = f + p * m) :
    π.cycleType = Multiset.replicate m p := by
  have horder : orderOf π = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hπ) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (horder ▸ hp : (orderOf π).Prime)
  rw [horder] at hn
  have htot := card_filter_fixed_add_card_support π
  rw [hfix, hcard] at htot
  have hsupp : #π.support = p * m := Nat.add_left_cancel htot
  have hsum := Equiv.Perm.sum_cycleType π
  rw [hn, Multiset.sum_replicate, smul_eq_mul, hsupp] at hsum
  have hm : n + 1 = m :=
    Nat.eq_of_mul_eq_mul_left hp.pos ((Nat.mul_comm p (n + 1)) ▸ hsum)
  rw [hn, hm]

/-! ### The canonical permutation σ₀ of `conway_o7.py` -/

/-- Underlying function of `sigma0`: vertex 0 is fixed; vertex `1 + 7*i + j`
(`0 ≤ j < 7`) maps to `1 + 7*i + (j+1) % 7`. -/
def sigma0Fun (v : Fin 99) : Fin 99 :=
  ⟨if (v : ℕ) = 0 then 0 else 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + 1) % 7, by
    have := v.isLt; split <;> omega⟩

/-- Inverse of `sigma0Fun`: rotate each block the other way. -/
def sigma0InvFun (v : Fin 99) : Fin 99 :=
  ⟨if (v : ℕ) = 0 then 0 else 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + 6) % 7, by
    have := v.isLt; split <;> omega⟩

theorem sigma0Fun_val (v : Fin 99) : (sigma0Fun v : ℕ)
    = if (v : ℕ) = 0 then 0
      else 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + 1) % 7 := rfl

theorem sigma0InvFun_val (v : Fin 99) : (sigma0InvFun v : ℕ)
    = if (v : ℕ) = 0 then 0
      else 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + 6) % 7 := rfl

theorem sigma0_leftInverse :
  ∀ v : Fin 99, sigma0InvFun (sigma0Fun v) = v := by
  intro v
  have hv := v.isLt
  apply Fin.ext
  rw [sigma0InvFun_val, sigma0Fun_val]
  by_cases h0 : (v : ℕ) = 0
  · rw [if_pos h0, if_pos rfl, h0]
  · have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    rw [if_neg h0, if_neg (by omega)]
    omega

theorem sigma0_rightInverse : ∀ v : Fin 99, sigma0Fun (sigma0InvFun v) = v := by
  intro v
  have hv := v.isLt
  apply Fin.ext
  rw [sigma0Fun_val, sigma0InvFun_val]
  by_cases h0 : (v : ℕ) = 0
  · rw [if_pos h0, if_pos rfl, h0]
  · have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    rw [if_neg h0, if_neg (by omega)]
    omega

/-- The canonical order-7 permutation `σ₀ = (0)(1 … 7)(8 … 14)…(92 … 98)` used by the
encoder `tools/conway_o7.py` (`build_sigma(99, fixed=1, cyc_len=7)`). -/
def sigma0 : Equiv.Perm (Fin 99) :=
  ⟨sigma0Fun, sigma0InvFun, sigma0_leftInverse, sigma0_rightInverse⟩

theorem sigma0_val (v : Fin 99) : ((sigma0 v : Fin 99) : ℕ)
    = if (v : ℕ) = 0 then 0
      else 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + 1) % 7 := rfl

/-- On a nonzero vertex, `k` applications of `σ₀` keep the block and advance the
position by `k` modulo `7`. -/
theorem sigma0_iterate_val (v : Fin 99) (h0 : (v : ℕ) ≠ 0) :
    ∀ k, (((⇑sigma0)^[k] v : Fin 99) : ℕ)
      = 1 + 7 * (((v : ℕ) - 1) / 7) + (((v : ℕ) - 1) % 7 + k) % 7
  | 0 => by
      have hv := v.isLt
      have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
      show (v : ℕ) = _
      omega
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      have ih := sigma0_iterate_val v h0 k
      have hv := v.isLt
      have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
      have hne : (((⇑sigma0)^[k] v : Fin 99) : ℕ) ≠ 0 := by
        rw [ih]; omega
      show (sigma0Fun ((⇑sigma0)^[k] v) : ℕ) = _
      rw [sigma0Fun_val, if_neg hne, ih]
      omega

theorem sigma0_iterate_seven : ∀ v : Fin 99, (⇑sigma0)^[7] v = v := by
  intro v
  by_cases h0 : (v : ℕ) = 0
  · have hfix : sigma0 v = v := Fin.ext (by rw [sigma0_val, if_pos h0, h0])
    exact Function.iterate_fixed hfix 7
  · apply Fin.ext
    rw [sigma0_iterate_val v h0 7]
    have hv := v.isLt
    have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    omega

theorem sigma0_pow_seven : sigma0 ^ 7 = 1 := by
  apply Equiv.ext
  intro v
  rw [← Equiv.Perm.iterate_eq_pow, Equiv.Perm.one_apply]
  exact sigma0_iterate_seven v

/-- The fixed points of `σ₀` are exactly vertex `0`: on a nonzero vertex the
position advances, and `(r+1) % 7 = r` is impossible. -/
theorem sigma0_fixed_iff (v : Fin 99) : sigma0 v = v ↔ (v : ℕ) = 0 := by
  constructor
  · intro h
    by_contra h0
    have hval := congrArg Fin.val h
    rw [sigma0_val, if_neg h0] at hval
    have hv := v.isLt
    have h7 : ((v : ℕ) - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    omega
  · intro h0
    exact Fin.ext (by rw [sigma0_val, if_pos h0, h0])

theorem sigma0_ne_one : sigma0 ≠ 1 := by
  intro h
  have h1 : sigma0 ⟨1, by omega⟩ = ⟨1, by omega⟩ := by rw [h]; rfl
  exact Nat.one_ne_zero ((sigma0_fixed_iff _).mp h1)

theorem sigma0_fixed_card :
  #{ v : Fin 99 | sigma0 v = v} = 1 := by
  have hset : ({v : Fin 99 | sigma0 v = v} : Finset _) = {0} := by
    ext v
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨_, hfix⟩ ↦ Fin.ext ((sigma0_fixed_iff v).mp hfix),
      fun h ↦ ⟨Finset.mem_univ _, (sigma0_fixed_iff v).mpr (congrArg Fin.val h)⟩⟩
  rw [hset, Finset.card_singleton]

/-- σ₀ has the cycle type `[1, 7¹⁴]` of the L3 lemma. -/
theorem sigma0_cycleType : sigma0.cycleType = Multiset.replicate 14 7 :=
  cycleType_eq_replicate_of_fixed sigma0 Nat.prime_seven sigma0_pow_seven sigma0_ne_one
    sigma0_fixed_card (by simp)

/-! ### Step 5: any order-7 automorphism relabels onto σ₀ -/

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **WLOG σ₀**: if some srg(99,14,1,2) admits an
order-7 automorphism, then some srg(99,14,1,2) on `Fin 99` is invariant
under the canonical `sigma0` — the statement whose refutation `o7.cnf` encodes. -/
theorem exists_sigma0_invariant (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (hord : orderOf σ = 7) :
    ∃ H : SimpleGraph (Fin 99), ∃ _ : DecidableRel H.Adj, H.IsSRGWith 99 14 1 2 ∧
      ∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v := by
  classical
  -- relabel the vertex type as Fin 99
  let e : V ≃ Fin 99 := Fintype.equivFinOfCardEq hG.card
  let H₁ : SimpleGraph (Fin 99) := G.comap e.symm.toEmbedding
  haveI : DecidableRel H₁.Adj := fun a b ↦ ‹DecidableRel G.Adj› _ _
  have iso₁ : H₁ ≃g G := SimpleGraph.Iso.comap e.symm G
  have hH₁ : H₁.IsSRGWith 99 14 1 2 := isSRGWith_of_iso iso₁.symm hG
  -- push the automorphism through the relabeling
  let π₁ : Equiv.Perm (Fin 99) := e.permCongrHom (autToPerm G σ)
  have hπ₁_apply : ∀ a, π₁ a = e (σ (e.symm a)) := fun a ↦ rfl
  have hadj₁ : ∀ a b, H₁.Adj (π₁ a) (π₁ b) ↔ H₁.Adj a b := by
    intro a b
    show G.Adj (e.symm (π₁ a)) (e.symm (π₁ b)) ↔ G.Adj (e.symm a) (e.symm b)
    rw [hπ₁_apply, hπ₁_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact σ.map_adj_iff
  have hord₁ : orderOf π₁ = 7 := by
    show orderOf (e.permCongrHom (autToPerm G σ)) = 7
    rw [MulEquiv.orderOf_eq, orderOf_injective (autToPerm G) (autToPerm_injective G) σ, hord]
  -- L3: π₁ has the cycle type of σ₀, hence is conjugate to it
  have hct : π₁.cycleType = sigma0.cycleType := by
    rw [cycleType_eq_replicate hadj₁ hH₁ hord₁, sigma0_cycleType]
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
  -- final relabeling by the conjugator
  refine ⟨H₁.comap (τ⁻¹ : Equiv.Perm (Fin 99)).toEmbedding,
    fun a b ↦ ‹DecidableRel H₁.Adj› _ _, isSRGWith_of_iso (SimpleGraph.Iso.comap _ H₁).symm hH₁,
    fun u v ↦ ?_⟩
  have key : ∀ w, τ⁻¹ (sigma0 w) = π₁ (τ⁻¹ w) := by
    intro w
    rw [← hτ]
    simp [Equiv.Perm.mul_apply]
  simp only [SimpleGraph.comap_adj, Equiv.toEmbedding_apply, key]
  exact hadj₁ _ _

/-- **reduced form**: if no σ₀-invariant srg(99,14,1,2) exists on `Fin 99`
(the fact `o7.cnf` encodes, to be discharged by cake_lpr), then
no srg(99,14,1,2) has 7 dividing its automorphism-group order. -/
theorem seven_not_dvd_card_aut_of_no_sigma0_invariant
    (hno : ∀ H : SimpleGraph (Fin 99),
    ∀ _ : DecidableRel H.Adj, H.IsSRGWith 99 14 1 2 →
      ¬∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v)
    (hG : G.IsSRGWith 99 14 1 2) : ¬7 ∣ Nat.card (G ≃g G) := by
  intro h
  let ⟨σ, hσ⟩ := exists_aut_orderOf_eq_seven G h
  obtain ⟨H, instH, hH, hinv⟩ := exists_sigma0_invariant hG σ hσ
  exact hno H instH hH hinv

end ConwayO7
