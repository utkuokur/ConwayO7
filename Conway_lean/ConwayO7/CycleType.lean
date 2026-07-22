/-
Layer L3 — the cycle-type lemma (Cesarz–Woldar, arXiv:2308.02978, Lemma 2.2):

  an order-7 automorphism of an srg(99,14,1,2) fixes exactly one vertex,
  hence has cycle type [1, 7¹⁴].

This is the step of T2 that makes the canonical σ₀ = (one fixed vertex + fourteen
7-cycles) of `tools/conway_o7.py` WLOG.  The proof follows `docs/L3_cycle_type.md`:

  Step 0  #Fix ≡ 99 ≡ 1 (mod 7), so a fixed vertex x exists            (`card_filter_fixed_modEq`)
  Step 1  λ = 1 gives a σ-equivariant perfect matching on N(x), so the
          number of fixed neighbours of x is even; mod 7 it is 0 or 14
  Step 2  rigidity: fixing x and all of N(x) pointwise forces σ = 1
          (each w ∉ N(x) ∪ {x} is determined by its μ = 2 common
          neighbours with x), killing the 14 case                      (`eq_one_of_fixes_neighbors`)
  Step 3  a second fixed vertex w ∉ N(x) would make σ swap the two
          common neighbours of {x, w}, so σ²(a) = a and σ = (σ²)⁴
          fixes a ∈ N(x) — contradiction
  Step 4  #Fix = 1, so #support = 98 and the cycle type is [7¹⁴]       (`cycleType_eq_replicate`)

-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.GroupTheory.Perm.Cycle.Type

open Finset

namespace ConwayO7

/-! ### Counting fixed points of a prime-order permutation on an invariant finset -/

section PermCounting

variable {α : Type*} [DecidableEq α]

section
variable [Fintype α]

/-- A permutation with `π ^ p = 1`, `p` prime, moves a multiple of `p` points
(its cycle type is a multiset of `p`s). -/
theorem card_support_of_pow_prime_eq_one (π : Equiv.Perm α) {p : ℕ} (hp : p.Prime)
    (hπ : π ^ p = 1) : ∃ m, #π.support = p * m := by
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hπ) with h | h
  · exact ⟨0, by simp [Equiv.Perm.support_eq_empty_iff.mpr (orderOf_eq_one_iff.mp h)]⟩
  · obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (h ▸ hp : (orderOf π).Prime)
    refine ⟨n + 1, ?_⟩
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, h, smul_eq_mul, Nat.mul_comm]

/-- Fixed points and support partition the ground type. -/
theorem card_filter_fixed_add_card_support (π : Equiv.Perm α) :
    #(univ.filter fun a ↦ π a = a) + #π.support = Fintype.card α := by
  have h : π.support = univ.filter fun a ↦ ¬π a = a := by
    ext a; simp [Equiv.Perm.mem_support]
  rw [h, card_filter_add_card_filter_not, card_univ]

end

/-- **Fixed-point congruence.**  If `π ^ p = 1` with `p` prime and the finset `s` is
`π`-invariant, then `#{a ∈ s | π a = a} ≡ #s [MOD p]`.  (Applied with `p = 7` to the
vertex set and to `N(x)`, and with `p = 2` to the matching involution of Step 1.) -/
theorem card_filter_fixed_modEq (π : Equiv.Perm α) {p : ℕ} (hp : p.Prime) (hπ : π ^ p = 1)
    (s : Finset α) (hs : ∀ a ∈ s, π a ∈ s) :
    #(s.filter fun a ↦ π a = a) ≡ #s [MOD p] := by
  -- upgrade invariance to a two-sided membership criterion
  have himg : s.image (fun a ↦ π a) = s :=
    eq_of_subset_of_card_le
      (fun b hb ↦ by
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
        exact hs a ha)
      (le_of_eq (card_image_of_injective s π.injective).symm)
  have hmem : ∀ a, π a ∈ s ↔ a ∈ s := by
    intro a
    refine ⟨fun h ↦ ?_, hs a⟩
    obtain ⟨b, hb, hba⟩ := mem_image.mp (himg ▸ h)
    exact π.injective hba ▸ hb
  -- restrict π to a permutation of the subtype ↥s
  set π' : Equiv.Perm {a // a ∈ s} := π.subtypePerm hmem with hπ'
  have hπ'p : π' ^ p = 1 := by
    ext a
    rw [hπ', Equiv.Perm.subtypePerm_pow]
    simp [hπ]
  obtain ⟨m, hm⟩ := card_support_of_pow_prime_eq_one π' hp hπ'p
  have htot := card_filter_fixed_add_card_support π'
  rw [Fintype.card_coe] at htot
  -- fixed points of the restriction are the fixed points inside s
  have hfix : #(univ.filter fun a : {a // a ∈ s} ↦ π' a = a) = #(s.filter fun a ↦ π a = a) := by
    refine card_bij (fun a _ ↦ a.1) ?_ ?_ ?_
    · rintro ⟨a, ha⟩ h
      rw [mem_filter] at h
      refine mem_filter.mpr ⟨ha, ?_⟩
      simpa [hπ', Equiv.Perm.subtypePerm_apply, Subtype.ext_iff] using h.2
    · rintro ⟨a, _⟩ _ ⟨b, _⟩ _ hab
      exact Subtype.ext hab
    · intro b hb
      rw [mem_filter] at hb
      refine ⟨⟨b, hb.1⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      simp [hπ', Equiv.Perm.subtypePerm_apply, hb.2]
  -- assemble:  #fixed = #s - p * m
  have hzero : p * m ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right p m)
  calc #(s.filter fun a ↦ π a = a)
      = #(s.filter fun a ↦ π a = a) + 0 := by rw [Nat.add_zero]
    _ ≡ #(s.filter fun a ↦ π a = a) + p * m [MOD p] := hzero.symm.add_left _
    _ = #s := by rw [← hfix, ← hm]; exact htot

end PermCounting

/-! ### srg(99, 14, 1, 2) combinatorics -/

variable {V : Type*} {G : SimpleGraph V}

section
variable [Fintype V] [DecidableRel G.Adj]

/-- λ = 1: every edge lies in a unique triangle. -/
theorem commonNeighbors_eq_singleton_of_adj (hG : G.IsSRGWith 99 14 1 2) {x u : V}
    (h : G.Adj x u) : ∃ w, G.commonNeighbors x u = {w} :=
  Set.ncard_eq_one.mp <|
    (Nat.card_coe_set_eq _).symm.trans <| Nat.card_eq_fintype_card.trans (hG.of_adj x u h)

/-- μ = 2: a nonadjacent pair has exactly two common neighbours. -/
theorem commonNeighbors_eq_pair_of_not_adj (hG : G.IsSRGWith 99 14 1 2) {x w : V}
    (hne : x ≠ w) (h : ¬G.Adj x w) :
    ∃ a b, a ≠ b ∧ G.commonNeighbors x w = {a, b} :=
  Set.ncard_eq_two.mp <|
    (Nat.card_coe_set_eq _).symm.trans <| Nat.card_eq_fintype_card.trans (hG.of_not_adj hne h)

/-- The Γ₂-labelling is injective (CW Lemma 2.1): a vertex nonadjacent to `x` is
determined by its common-neighbour set with `x`. -/
theorem eq_of_commonNeighbors_eq (hG : G.IsSRGWith 99 14 1 2) {x w w' : V}
    (hw : w ≠ x) (hw' : w' ≠ x) (hnadj : ¬G.Adj x w) (hnadj' : ¬G.Adj x w')
    (hcn : G.commonNeighbors x w = G.commonNeighbors x w') : w = w' := by
  obtain ⟨a, b, hab, hpair⟩ := commonNeighbors_eq_pair_of_not_adj hG (Ne.symm hw) hnadj
  have ha : a ∈ G.commonNeighbors x w := by rw [hpair]; exact Set.mem_insert a {b}
  have hb : b ∈ G.commonNeighbors x w := by rw [hpair]; exact Set.mem_insert_of_mem a rfl
  have ha' : a ∈ G.commonNeighbors x w' := hcn ▸ ha
  have hb' : b ∈ G.commonNeighbors x w' := hcn ▸ hb
  rw [SimpleGraph.mem_commonNeighbors] at ha hb ha' hb'
  -- the two labels are nonadjacent: an edge a–b would put the distinct x, w in its λ = 1 triangle
  have hnab : ¬G.Adj a b := by
    intro hadj
    obtain ⟨c, hc⟩ := commonNeighbors_eq_singleton_of_adj hG hadj
    have hxc : x = c := by
      have : x ∈ G.commonNeighbors a b := G.mem_commonNeighbors.mpr ⟨ha.1.symm, hb.1.symm⟩
      rwa [hc, Set.mem_singleton_iff] at this
    have hwc : w = c := by
      have : w ∈ G.commonNeighbors a b := G.mem_commonNeighbors.mpr ⟨ha.2.symm, hb.2.symm⟩
      rwa [hc, Set.mem_singleton_iff] at this
    exact hw (hwc.trans hxc.symm)
  -- {x, w} and {x, w'} both exhaust the two common neighbours of the nonadjacent pair {a, b}
  have hsub : ∀ v : V, G.Adj a v → G.Adj b v → v ∈ G.commonNeighbors a b := fun v h1 h2 ↦
    G.mem_commonNeighbors.mpr ⟨h1, h2⟩
  have hcard : (G.commonNeighbors a b).ncard = 2 :=
    (Nat.card_coe_set_eq _).symm.trans <| Nat.card_eq_fintype_card.trans (hG.of_not_adj hab hnab)
  have hxw : ({x, w} : Set V) = G.commonNeighbors a b := by
    refine Set.eq_of_subset_of_ncard_le ?_ (le_of_eq ?_) (Set.toFinite _)
    · rintro v (rfl | rfl)
      · exact hsub _ ha.1.symm hb.1.symm
      · exact hsub _ ha.2.symm hb.2.symm
    · rw [hcard, Set.ncard_pair (Ne.symm hw)]
  have hxw' : ({x, w'} : Set V) = G.commonNeighbors a b := by
    refine Set.eq_of_subset_of_ncard_le ?_ (le_of_eq ?_) (Set.toFinite _)
    · rintro v (rfl | rfl)
      · exact hsub _ ha'.1.symm hb'.1.symm
      · exact hsub _ ha'.2.symm hb'.2.symm
    · rw [hcard, Set.ncard_pair (Ne.symm hw')]
  have : w ∈ ({x, w'} : Set V) := by
    rw [hxw']; rw [← hxw]; exact Set.mem_insert_of_mem x rfl
  rcases this with h | h
  · exact absurd h hw
  · exact h

end

section Automorphism

variable {π : Equiv.Perm V} (hadj : ∀ u v, G.Adj (π u) (π v) ↔ G.Adj u v)

include hadj

/-- Equivariance of common neighbourhoods. -/
theorem mapsTo_commonNeighbors {u v w : V} (h : u ∈ G.commonNeighbors v w) :
    π u ∈ G.commonNeighbors (π v) (π w) := by
  rw [SimpleGraph.mem_commonNeighbors] at h ⊢
  exact ⟨(hadj v u).mpr h.1, (hadj w u).mpr h.2⟩

section
variable [Fintype V] [DecidableRel G.Adj]

/-- **Rigidity** (Step 2): an adjacency-preserving permutation of an srg(99,14,1,2) that
fixes a vertex and all its neighbours is the identity. -/
theorem eq_one_of_fixes_neighbors (hG : G.IsSRGWith 99 14 1 2) {x : V} (hx : π x = x)
    (hnbr : ∀ u, G.Adj x u → π u = u) : π = 1 := by
  have hadj_inv : ∀ u v, G.Adj (π⁻¹ u) (π⁻¹ v) ↔ G.Adj u v := fun u v ↦ by
    rw [← hadj (π⁻¹ u) (π⁻¹ v), Equiv.Perm.inv_def, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  ext v
  rw [Equiv.Perm.one_apply]
  by_cases hvx : v = x
  · rw [hvx, hx]
  by_cases hva : G.Adj x v
  · exact hnbr v hva
  -- the distance-2 case: π v has the same (pointwise fixed) label as v
  have hcn : G.commonNeighbors x (π v) = G.commonNeighbors x v := by
    ext u
    constructor
    · intro hu
      have hux : G.Adj x u := (G.mem_commonNeighbors.mp hu).1
      have huf : π⁻¹ u = u := by
        rw [Equiv.Perm.inv_def]
        exact (Equiv.symm_apply_eq π).mpr (hnbr u hux).symm
      have hxinv : π⁻¹ x = x := by
        rw [Equiv.Perm.inv_def]
        exact (Equiv.symm_apply_eq π).mpr hx.symm
      have hvinv : π⁻¹ (π v) = v := by
        rw [Equiv.Perm.inv_def]
        exact Equiv.symm_apply_apply π v
      have := mapsTo_commonNeighbors hadj_inv (G := G) hu
      rwa [huf, hxinv, hvinv] at this
    · intro hu
      have hux : G.Adj x u := (G.mem_commonNeighbors.mp hu).1
      have := mapsTo_commonNeighbors hadj (G := G) hu
      rwa [hnbr u hux, hx] at this
  refine eq_of_commonNeighbors_eq hG ?_ hvx ?_ hva hcn
  · intro h
    exact hvx (π.injective (h.trans hx.symm))
  · intro h
    rw [← hx] at h
    exact hva ((hadj x v).mp h)

variable [DecidableEq V]

/-- **L3, fixed-point count** (Cesarz–Woldar Lemma 2.2): an order-7 adjacency-preserving
permutation of an srg(99,14,1,2) fixes exactly one vertex. -/
theorem card_filter_fixed_eq_one
  (hG : G.IsSRGWith 99 14 1 2) (hord : orderOf π = 7) :
    #(univ.filter fun v ↦ π v = v) = 1 := by
  have hp7 : Nat.Prime 7 := by decide
  have h7 : π ^ 7 = 1 := by rw [← hord]; exact pow_orderOf_eq_one π
  -- Step 0: #Fix ≡ 99 ≡ 1 (mod 7) gives a fixed vertex x
  have hmod : #(univ.filter fun v ↦ π v = v) ≡ 99 [MOD 7] := by
    have h := card_filter_fixed_modEq π hp7 h7 univ (fun a _ ↦ mem_univ _)
    rwa [card_univ, hG.card] at h
  obtain ⟨x, hx⟩ : (univ.filter fun v ↦ π v = v).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rw [h, card_empty] at hmod
    exact absurd hmod (by decide)
  have hxfix : π x = x := (mem_filter.mp hx).2
  -- Step 1: the fixed neighbours of x, paired by the λ = 1 matching
  set s : Finset V := (G.neighborFinset x).filter (fun u ↦ π u = u) with hs
  have hmem_s : ∀ u, u ∈ s ↔ G.Adj x u ∧ π u = u := by
    intro u; rw [hs, mem_filter, SimpleGraph.mem_neighborFinset]
  -- the matching u ↦ unique common neighbour of the edge {x, u}, as a global involution
  have hsingle : ∀ u, G.Adj x u → ∃ w, G.commonNeighbors x u = {w} := fun u hu ↦
    commonNeighbors_eq_singleton_of_adj hG hu
  classical
  let f : V → V := fun u ↦ if h : G.Adj x u then (hsingle u h).choose else u
  have hfu_pos : ∀ u (h : G.Adj x u), f u = (hsingle u h).choose := fun u h ↦ dif_pos h
  have hfu_neg : ∀ u, ¬G.Adj x u → f u = u := fun u h ↦ dif_neg h
  have hchoose : ∀ u (h : G.Adj x u), (hsingle u h).choose ∈ G.commonNeighbors x u ∧
      ∀ w ∈ G.commonNeighbors x u, w = (hsingle u h).choose := fun u h ↦
    Set.eq_singleton_iff_unique_mem.mp (hsingle u h).choose_spec
  have hfmem : ∀ u (h : G.Adj x u), f u ∈ G.commonNeighbors x u := fun u h ↦ by
    rw [hfu_pos u h]; exact (hchoose u h).1
  have hfeq : ∀ u (h : G.Adj x u) w, w ∈ G.commonNeighbors x u → f u = w := fun u h w hw ↦ by
    rw [hfu_pos u h]; exact ((hchoose u h).2 w hw).symm
  have hfadj : ∀ u (h : G.Adj x u), G.Adj x (f u) ∧ G.Adj u (f u) := fun u h ↦
    G.mem_commonNeighbors.mp (hfmem u h)
  have hinv : Function.Involutive f := by
    intro u
    by_cases h : G.Adj x u
    · exact hfeq (f u) (hfadj u h).1 u (G.mem_commonNeighbors.mpr ⟨h, (hfadj u h).2.symm⟩)
    · rw [hfu_neg u h, hfu_neg u h]
  have hfne : ∀ u, G.Adj x u → f u ≠ u := fun u h heq ↦
    G.irrefl (heq ▸ (hfadj u h).2)
  -- f preserves s: the partner of a fixed neighbour is fixed (equivariance + uniqueness)
  have hfs : ∀ u ∈ s, f u ∈ s := by
    intro u hu
    obtain ⟨hadj_u, hfix_u⟩ := (hmem_s u).mp hu
    have h1 : π (f u) ∈ G.commonNeighbors (π x) (π u) :=
      mapsTo_commonNeighbors hadj (G := G) (hfmem u hadj_u)
    rw [hxfix, hfix_u] at h1
    have : f u = π (f u) := (hfeq u hadj_u _ h1)
    exact (hmem_s _).mpr ⟨(hfadj u hadj_u).1, this.symm⟩
  -- Step 1a: #s is even (fixed-point-free involution on s, p = 2)
  have heven : 2 ∣ #s := by
    have h2 : (hinv.toPerm f) ^ 2 = 1 := by
      ext a
      simp [sq, hinv a]
    have hmod2 := card_filter_fixed_modEq (hinv.toPerm f) (by decide) h2 s
      (fun a ha ↦ by rw [Function.Involutive.coe_toPerm]; exact hfs a ha)
    have hempty : (s.filter fun a ↦ (hinv.toPerm f) a = a) = ∅ := by
      rw [filter_eq_empty_iff]
      intro a ha
      rw [Function.Involutive.coe_toPerm]
      exact hfne a ((hmem_s a).mp ha).1
    rw [hempty, card_empty] at hmod2
    exact (Nat.modEq_zero_iff_dvd.mp hmod2.symm)
  -- Step 1b: #s ≡ 14 ≡ 0 (mod 7)
  have hseven : 7 ∣ #s := by
    have hinv_nbr : ∀ a ∈ G.neighborFinset x, π a ∈ G.neighborFinset x := by
      intro a ha
      rw [SimpleGraph.mem_neighborFinset] at ha ⊢
      rw [← hxfix]
      exact (hadj x a).mpr ha
    have h := card_filter_fixed_modEq π hp7 h7 (G.neighborFinset x) hinv_nbr
    rw [G.card_neighborFinset_eq_degree, hG.regular x] at h
    rw [← hs] at h
    exact Nat.modEq_zero_iff_dvd.mp (h.trans (by decide))
  have hsle : #s ≤ 14 := by
    calc #s ≤ #(G.neighborFinset x) := card_filter_le _ _
      _ = 14 := by rw [G.card_neighborFinset_eq_degree, hG.regular x]
  -- Step 2: #s = 14 would make π the identity, impossible for order 7
  have hs0 : #s = 0 := by
    rcases (by omega : #s = 0 ∨ #s = 14) with h | h
    · exact h
    · exfalso
      have hall : ∀ u, G.Adj x u → π u = u := by
        have hseq : s = G.neighborFinset x := by
          refine eq_of_subset_of_card_le (filter_subset _ _) ?_
          rw [G.card_neighborFinset_eq_degree, hG.regular x, h]
        intro u hu
        have hu' : u ∈ G.neighborFinset x := by rw [SimpleGraph.mem_neighborFinset]; exact hu
        rw [← hseq] at hu'
        exact ((hmem_s u).mp hu').2
      have : π = 1 := eq_one_of_fixes_neighbors hadj hG hxfix hall
      rw [this, orderOf_one] at hord
      exact absurd hord (by norm_num)
  -- Step 3: no fixed vertex outside {x} either
  have huniq : ∀ v, π v = v → v = x := by
    intro v hv
    by_contra hvx
    by_cases hva : G.Adj x v
    · have : v ∈ s := (hmem_s v).mpr ⟨hva, hv⟩
      rw [card_eq_zero] at hs0
      rw [hs0] at this
      exact absurd this (notMem_empty v)
    · obtain ⟨a, b, hab, hpair⟩ :=
        commonNeighbors_eq_pair_of_not_adj hG (fun h ↦ hvx h.symm) hva
      have hmema : a ∈ G.commonNeighbors x v := by rw [hpair]; exact Set.mem_insert a {b}
      have hmemb : b ∈ G.commonNeighbors x v := by rw [hpair]; exact Set.mem_insert_of_mem a rfl
      have hinv_cn : ∀ c, c ∈ G.commonNeighbors x v → π c ∈ G.commonNeighbors x v := by
        intro c hc
        have := mapsTo_commonNeighbors hadj (G := G) hc
        rwa [hxfix, hv] at this
      -- neither a nor b is fixed (they are neighbours of x, and s = ∅)
      have hnofix : ∀ c, c ∈ G.commonNeighbors x v → π c ≠ c := by
        intro c hc hcfix
        have : c ∈ s :=
          (hmem_s c).mpr ⟨(G.mem_commonNeighbors.mp hc).1, hcfix⟩
        rw [card_eq_zero] at hs0
        rw [hs0] at this
        exact absurd this (notMem_empty c)
      -- so π swaps a and b, hence π² fixes a, hence π = (π²)⁴ fixes a: contradiction
      have hπa : π a = b := by
        have := hinv_cn a hmema
        rw [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] at this
        rcases this with h | h
        · exact absurd h (hnofix a hmema)
        · exact h
      have hπb : π b = a := by
        have := hinv_cn b hmemb
        rw [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h (hnofix b hmemb)
      have hsq : (π ^ 2) a = a := by rw [sq, Equiv.Perm.mul_apply, hπa, hπb]
      have hpow : ∀ n : ℕ, ((π ^ 2) ^ n) a = a := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hsq]
      have h8 : π ^ 8 = π := by
        have : π ^ 8 = π ^ 7 * π := by rw [← pow_succ]
        rw [this, h7, one_mul]
      have : π a = a := by
        have h24 : ((π ^ 2) ^ 4) a = a := hpow 4
        rwa [← pow_mul, (by norm_num : 2 * 4 = 8), h8] at h24
      rw [hπa] at this
      exact hab this.symm
  -- conclusion: the fixed-point set is exactly {x}
  have : (univ.filter fun v ↦ π v = v) = {x} := by
    ext v
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨-, hv⟩; exact huniq v hv
    · rintro rfl; exact ⟨mem_univ _, hxfix⟩
  rw [this, card_singleton]

/-- **L3, cycle type**: an order-7 adjacency-preserving permutation of an srg(99,14,1,2)
has cycle type `[7¹⁴]` — one fixed vertex and fourteen 7-cycles, the canonical shape
encoded by `tools/conway_o7.py`. -/
theorem cycleType_eq_replicate (hG : G.IsSRGWith 99 14 1 2) (hord : orderOf π = 7) :
    π.cycleType = Multiset.replicate 14 7 := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by rw [hord]; decide : (orderOf π).Prime)
  rw [hord] at hn
  have hfix := card_filter_fixed_eq_one hadj hG hord
  have htot := card_filter_fixed_add_card_support π
  rw [hG.card, hfix] at htot
  have hsum := Equiv.Perm.sum_cycleType π
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have : n = 13 := by omega
  rw [hn, this]

end

end Automorphism

end ConwayO7
