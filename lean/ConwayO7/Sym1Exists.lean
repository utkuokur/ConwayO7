/-
The level-1 symmetry choice is achievable: every srg orbit assignment has a
cycle-relabeled companion satisfying `Sym1Holds`.

`sigma0` fixes vertex 0 and rotates fourteen 7-cycles; a permutation `σ` of the
cycle indices induces the vertex relabeling `cycleRelabel σ` (cycle `i`, position
`j` ↦ cycle `σ i`, position `j`), which commutes with `sigma0`.  Since the fixed
vertex is 14-regular and its neighbourhood is `sigma0`-closed, it consists of
exactly two full cycles; relabeling those to positions 0 and 1 gives the seed
assignment for the lex-leader minimization.
-/
import ConwayO7.Bridge
import ConwayO7.SrgIso

namespace ConwayO7
namespace Encoder

open Finset

/-! ### Cycle relabelings -/

/-- The cycle index of a nonzero vertex (junk value 0 at vertex 0). -/
def cycIdx (n : Nat) : Fin 14 := ⟨(n - 1) / 7 % 14, Nat.mod_lt _ (by omega)⟩

/-- Vertex relabeling induced by a permutation of the cycle indices. -/
def cycleRelabelVal (σ : Equiv.Perm (Fin 14)) (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + 7 * (σ (cycIdx n)).val + (n - 1) % 7

theorem cycleRelabelVal_lt (σ : Equiv.Perm (Fin 14)) (n : Nat) :
    cycleRelabelVal σ n < 99 := by
  unfold cycleRelabelVal
  have h14 := (σ (cycIdx n)).isLt
  have h7 : (n - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
  split <;> omega

theorem cycleRelabelVal_inj (σ : Equiv.Perm (Fin 14)) {a b : Nat}
    (ha : a < 99) (hb : b < 99)
    (h : cycleRelabelVal σ a = cycleRelabelVal σ b) : a = b := by
  unfold cycleRelabelVal at h
  by_cases h0a : a = 0 <;> by_cases h0b : b = 0
  · rw [h0a, h0b]
  · rw [if_pos h0a, if_neg h0b] at h
    omega
  · rw [if_neg h0a, if_pos h0b] at h
    omega
  · rw [if_neg h0a, if_neg h0b] at h
    have hma := (σ (cycIdx a)).isLt
    have hmb := (σ (cycIdx b)).isLt
    have h7a : (a - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    have h7b : (b - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    have hveq : (σ (cycIdx a)).val = (σ (cycIdx b)).val := by omega
    have hidx : cycIdx a = cycIdx b := σ.injective (Fin.ext hveq)
    have hidxval : (a - 1) / 7 % 14 = (b - 1) / 7 % 14 := congrArg Fin.val hidx
    omega

/-- The cycle relabeling, as a permutation of the vertices. -/
noncomputable def cycleRelabel (σ : Equiv.Perm (Fin 14)) : Equiv.Perm (Fin 99) :=
  Equiv.ofBijective (fun v ↦ ⟨cycleRelabelVal σ v.val, cycleRelabelVal_lt σ v.val⟩)
    (Finite.injective_iff_bijective.mp fun a b h ↦
      Fin.ext (cycleRelabelVal_inj σ a.isLt b.isLt (congrArg Fin.val h)))

theorem cycleRelabel_val (σ : Equiv.Perm (Fin 14)) (v : Fin 99) :
    (cycleRelabel σ v).val = cycleRelabelVal σ v.val := rfl

/-- `sigma0`'s underlying value map, at the `Nat` level. -/
def sigma0Val (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + 7 * ((n - 1) / 7) + ((n - 1) % 7 + 1) % 7

theorem sigma0_val_eq (v : Fin 99) : (sigma0 v).val = sigma0Val v.val := rfl

/-- The cycle relabeling commutes with the canonical rotation. -/
theorem cycleRelabelVal_comm (σ : Equiv.Perm (Fin 14)) (n : Nat) :
    cycleRelabelVal σ (sigma0Val n) = sigma0Val (cycleRelabelVal σ n) := by
  by_cases h0 : n = 0
  · subst h0
    rfl
  · have h7 : (n - 1) % 7 < 7 := Nat.mod_lt _ (by omega)
    have hm := (σ (cycIdx n)).isLt
    unfold sigma0Val cycleRelabelVal
    simp only [if_neg h0]
    rw [if_neg (by omega : ¬(1 + 7 * ((n - 1) / 7) + ((n - 1) % 7 + 1) % 7 = 0)),
      if_neg (by omega : ¬(1 + 7 * (σ (cycIdx n)).val + (n - 1) % 7 = 0))]
    have hidx : cycIdx (1 + 7 * ((n - 1) / 7) + ((n - 1) % 7 + 1) % 7) = cycIdx n := by
      apply Fin.ext
      show (1 + 7 * ((n - 1) / 7) + ((n - 1) % 7 + 1) % 7 - 1) / 7 % 14
        = (n - 1) / 7 % 14
      omega
    rw [hidx]
    omega

/-- The cycle relabeling commutes with the canonical rotation. -/
theorem cycleRelabel_comm (σ : Equiv.Perm (Fin 14)) (v : Fin 99) :
    cycleRelabel σ (sigma0 v) = sigma0 (cycleRelabel σ v) := by
  apply Fin.ext
  simp only [cycleRelabel_val, sigma0_val_eq]
  exact cycleRelabelVal_comm σ v.val

theorem cycleRelabelVal_cycle (σ : Equiv.Perm (Fin 14)) (i : Fin 14) :
    cycleRelabelVal σ (1 + 7 * i.val) = 1 + 7 * (σ i).val := by
  unfold cycleRelabelVal
  rw [if_neg (by omega)]
  have hidx : cycIdx (1 + 7 * i.val) = i := by
    apply Fin.ext
    show (1 + 7 * i.val - 1) / 7 % 14 = i.val
    have := i.isLt
    omega
  rw [hidx]
  omega

/-! ### The relabeled graph -/

theorem comap_invariant (σ : Equiv.Perm (Fin 14)) (ω : Nat → Bool) :
    ∀ u v, ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding).Adj
        (sigma0 u) (sigma0 v)
      ↔ ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding).Adj u v := by
  intro u v
  show (graphOfOrbits ω).Adj (cycleRelabel σ (sigma0 u)) (cycleRelabel σ (sigma0 v))
    ↔ (graphOfOrbits ω).Adj (cycleRelabel σ u) (cycleRelabel σ v)
  rw [cycleRelabel_comm, cycleRelabel_comm]
  exact graphOfOrbits_invariant ω _ _

/-! ### Concrete cycle facts (computed) -/

/-- Orbits of pairs `(0, v)` depend only on `v`'s cycle. -/
theorem orbit0_cyc : ∀ v : Fin 99, v.val ≠ 0 →
    orbitOf ((0 : Fin 99), v) = orbitOfN 0 (1 + 7 * ((v.val - 1) / 7 % 14)) := by
  native_decide

/-- Each cycle has exactly 7 vertices. -/
theorem cycle_fiber_card : ∀ c : Fin 14,
    (Finset.univ.filter fun v : Fin 99 ↦ v.val ≠ 0 ∧ (v.val - 1) / 7 % 14 = c.val).card
      = 7 := by
  native_decide

/-! ### The two neighbour cycles of the fixed vertex -/

/-- The adjacency bit of the fixed vertex towards cycle `c`. -/
def cycleBit (ω : Nat → Bool) (c : Fin 14) : Bool := ω (orbitOfN 0 (1 + 7 * c.val))

theorem adj_zero_iff (ω : Nat → Bool) (v : Fin 99) :
    (graphOfOrbits ω).Adj 0 v ↔ (v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true) := by
  constructor
  · rintro ⟨hne, hω⟩
    have hv0 : v.val ≠ 0 := fun h ↦ hne (Fin.ext h.symm)
    refine ⟨hv0, ?_⟩
    show ω (orbitOfN 0 (1 + 7 * ((v.val - 1) / 7 % 14))) = true
    rw [← orbit0_cyc v hv0]
    exact hω
  · rintro ⟨hv0, hbv⟩
    refine ⟨fun h ↦ hv0 (congrArg Fin.val h).symm, ?_⟩
    rw [orbit0_cyc v hv0]
    exact hbv

/-- Exactly two cycles carry the fixed vertex's neighbourhood. -/
theorem two_neighbor_cycles (ω : Nat → Bool)
    (hsrg : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    (Finset.univ.filter fun c : Fin 14 ↦ cycleBit ω c = true).card = 2 := by
  classical
  have hdeg : ((Finset.univ : Finset (Fin 99)).filter ((graphOfOrbits ω).Adj 0)).card
      = 14 := by
    rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
    exact hsrg.regular 0
  have hfilter : (Finset.univ : Finset (Fin 99)).filter ((graphOfOrbits ω).Adj 0)
      = Finset.univ.filter fun v : Fin 99 ↦ v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true :=
    Finset.filter_congr fun v _ ↦ adj_zero_iff ω v
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun v : Fin 99 ↦ v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true)
    (t := Finset.univ) (f := fun v ↦ cycIdx v.val) (fun x _ ↦ Finset.mem_univ _)
  have hfib : ∀ c : Fin 14,
      ((Finset.univ.filter fun v : Fin 99 ↦ v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true).filter
        fun v ↦ cycIdx v.val = c).card = if cycleBit ω c = true then 7 else 0 := by
    intro c
    rw [Finset.filter_filter]
    by_cases hbc : cycleBit ω c = true
    · rw [if_pos hbc]
      have he : Finset.univ.filter
            (fun v : Fin 99 ↦ (v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true) ∧ cycIdx v.val = c)
          = Finset.univ.filter fun v : Fin 99 ↦ v.val ≠ 0 ∧ (v.val - 1) / 7 % 14 = c.val := by
        refine Finset.filter_congr fun v _ ↦ ?_
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, congrArg Fin.val h3⟩
        · rintro ⟨h1, h2⟩
          have hc : cycIdx v.val = c := Fin.ext h2
          exact ⟨⟨h1, by rw [hc]; exact hbc⟩, hc⟩
      rw [he]
      exact cycle_fiber_card c
    · rw [if_neg hbc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro v _ ⟨⟨_, h2⟩, h3⟩
      exact hbc (h3 ▸ h2)
  have h14 : (Finset.univ.filter fun v : Fin 99 ↦
        v.val ≠ 0 ∧ cycleBit ω (cycIdx v.val) = true).card
      = ∑ c ∈ Finset.univ, if cycleBit ω c = true then 7 else 0 := by
    rw [hsum]
    exact Finset.sum_congr rfl fun c _ ↦ hfib c
  have hsum7 : (∑ c ∈ Finset.univ, if cycleBit ω c = true then 7 else 0)
      = (Finset.univ.filter fun c : Fin 14 ↦ cycleBit ω c = true).card * 7 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rw [hfilter] at hdeg
  omega

/-! ### The seed -/

/-- **Level-1 achievability**: every srg orbit assignment has a companion — a cycle
relabeling of the same graph — that is an srg satisfying the level-1 units. -/
theorem sym1_seed (ω : Nat → Bool) (hsrg : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    ∃ ω₀ : Nat → Bool, (graphOfOrbits ω₀).IsSRGWith 99 14 1 2 ∧
      Sym1Holds (assignOfOrbits ω₀) := by
  classical
  -- the two neighbour cycles, with the second nonzero
  obtain ⟨c₁, c₂, hne, hset⟩ := Finset.card_eq_two.mp (two_neighbor_cycles ω hsrg)
  have hbiff0 : ∀ c, cycleBit ω c = true ↔ c = c₁ ∨ c = c₂ := by
    intro c
    constructor
    · intro hbc
      have hmem : c ∈ Finset.univ.filter fun c : Fin 14 ↦ cycleBit ω c = true :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩
      rw [hset] at hmem
      simpa using hmem
    · intro h
      have hmem : c ∈ ({c₁, c₂} : Finset (Fin 14)) := by simpa using h
      rw [← hset] at hmem
      exact (Finset.mem_filter.mp hmem).2
  obtain ⟨d₁, d₂, hdne, hd0, hbiff⟩ : ∃ d₁ d₂ : Fin 14, d₁ ≠ d₂ ∧ d₂ ≠ 0 ∧
      ∀ c, cycleBit ω c = true ↔ c = d₁ ∨ c = d₂ := by
    rcases eq_or_ne c₂ 0 with h20 | h20
    · exact ⟨c₂, c₁, hne.symm, fun h ↦ hne (h.trans h20.symm),
        fun c ↦ (hbiff0 c).trans or_comm⟩
    · exact ⟨c₁, c₂, hne, h20, hbiff0⟩
  -- the relabeling sending cycles 0, 1 to the two neighbour cycles
  set σ : Equiv.Perm (Fin 14) := (Equiv.swap 1 d₂).trans (Equiv.swap 0 d₁) with hσdef
  have hσ0 : σ 0 = d₁ := by
    show (Equiv.swap 0 d₁) ((Equiv.swap 1 d₂) 0) = d₁
    rw [Equiv.swap_apply_of_ne_of_ne zero_ne_one (Ne.symm hd0)]
    exact Equiv.swap_apply_left 0 d₁
  have hσ1 : σ 1 = d₂ := by
    show (Equiv.swap 0 d₁) ((Equiv.swap 1 d₂) 1) = d₂
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hd0 hdne.symm
  have hinv := comap_invariant σ ω
  refine ⟨orbitFunOf ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding), ?_, ?_⟩
  · -- strong regularity, through the relabeling isomorphism
    refine IsSRGWith.of_iso ⟨Equiv.refl _, fun {a b} ↦ ?_⟩
      (IsSRGWith.of_iso (SimpleGraph.Iso.comap (cycleRelabel σ) (graphOfOrbits ω)) hsrg)
    rw [graphOfOrbits_orbitFunOf hinv]
    rfl
  · -- the level-1 units
    intro i hi
    show orbitFunOf ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding)
      (orbitOfN 0 (1 + 7 * i) + 1 - 1) = decide (i < 2)
    rw [Nat.add_sub_cancel]
    have hc14 := (σ ⟨i, hi⟩).isLt
    -- the unit's orbit is the orbit of the pair (0, first vertex of cycle i)
    have horb : orbitOfN 0 (1 + 7 * i)
        = orbitOf ((0 : Fin 99), (⟨1 + 7 * i, by omega⟩ : Fin 99)) := by
      unfold orbitOfN
      congr 1
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · show 0 % 99 = 0
        omega
      · show (1 + 7 * i) % 99 = 1 + 7 * i
        omega
    -- its value is the relabeled adjacency
    have hval : orbitFunOf ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding)
        (orbitOfN 0 (1 + 7 * i)) = true
        ↔ ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding).Adj 0
            ⟨1 + 7 * i, by omega⟩ := by
      constructor
      · intro h
        have hadj : (graphOfOrbits (orbitFunOf
            ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding))).Adj 0
              ⟨1 + 7 * i, by omega⟩ :=
          ⟨Fin.ne_of_val_ne (by show ¬(0 % 99 = 1 + 7 * i); omega),
            by rw [← horb]; exact h⟩
        rwa [graphOfOrbits_orbitFunOf hinv] at hadj
      · intro h
        have hadj : (graphOfOrbits (orbitFunOf
            ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding))).Adj 0
              ⟨1 + 7 * i, by omega⟩ := by
          rw [graphOfOrbits_orbitFunOf hinv]
          exact h
        rw [horb]
        exact hadj.2
    -- the relabeled adjacency is the cycle bit at σ i
    have hG0Adj : ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding).Adj 0
        ⟨1 + 7 * i, by omega⟩ ↔ cycleBit ω (σ ⟨i, hi⟩) = true := by
      show (graphOfOrbits ω).Adj (cycleRelabel σ 0) (cycleRelabel σ ⟨1 + 7 * i, by omega⟩)
        ↔ _
      have he0 : cycleRelabel σ 0 = (0 : Fin 99) := by
        apply Fin.ext
        rw [cycleRelabel_val]
        exact if_pos rfl
      have hev : cycleRelabel σ (⟨1 + 7 * i, by omega⟩ : Fin 99)
          = ⟨1 + 7 * (σ ⟨i, hi⟩).val, by omega⟩ := by
        apply Fin.ext
        rw [cycleRelabel_val]
        exact cycleRelabelVal_cycle σ ⟨i, hi⟩
      rw [he0, hev, adj_zero_iff]
      have hidx : cycIdx (1 + 7 * (σ ⟨i, hi⟩).val) = σ ⟨i, hi⟩ := by
        apply Fin.ext
        show (1 + 7 * (σ ⟨i, hi⟩).val - 1) / 7 % 14 = (σ ⟨i, hi⟩).val
        omega
      rw [hidx]
      exact ⟨fun h ↦ h.2, fun hb ↦ ⟨by show ¬(1 + 7 * (σ ⟨i, hi⟩).val = 0); omega, hb⟩⟩
    -- the cycle bit at σ i is exactly "i < 2"
    have hbit_iff : cycleBit ω (σ ⟨i, hi⟩) = true ↔ i < 2 := by
      rw [hbiff (σ ⟨i, hi⟩), ← hσ0, ← hσ1, σ.injective.eq_iff, σ.injective.eq_iff]
      constructor
      · rintro (h | h)
        · have hv : i = 0 % 14 := congrArg Fin.val h
          omega
        · have hv : i = 1 % 14 := congrArg Fin.val h
          omega
      · intro h2
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact Or.inl (Fin.ext rfl)
        · exact Or.inr (Fin.ext rfl)
    -- assemble
    have hiff := hval.trans (hG0Adj.trans hbit_iff)
    by_cases h2 : i < 2
    · rw [decide_eq_true h2]
      exact hiff.mpr h2
    · rw [decide_eq_false h2]
      cases hv : orbitFunOf ((graphOfOrbits ω).comap (cycleRelabel σ).toEmbedding)
          (orbitOfN 0 (1 + 7 * i)) with
      | false => rfl
      | true => exact absurd (hiff.mp hv) h2

end Encoder
end ConwayO7
