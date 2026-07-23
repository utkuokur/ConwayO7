/-
L4 gadget mathematics — satisfiability of the modulo-totalizer merge (`mto_MUA_A`).

Register semantics: a block with true-count `C` is represented by an *upper* unary
counter for `C / 9` and a *lower* unary counter for `C % 9` (`p = ⌊√98⌋ = 9` for every
degree constraint of `o7.cnf`, so the lemmas fix `p = 9` and all division arithmetic
stays inside `omega`'s literal-divisor fragment).  The merge introduces one fresh
carry variable `c` with witness value `9 ≤ Cf % 9 + Cs % 9`; then

    (Cf + Cs) / 9 = Cf / 9 + Cs / 9 + (if carry then 1 else 0)
    (Cf + Cs) % 9 = Cf % 9 + Cs % 9 − (if carry then 9 else 0)

make every φ₁ (lower merge) and φ₂ (upper merge) clause true.  The two capacity
hypotheses (`1 ≤ hs.size`, `(Cf + Cs) / 9 ≤ hs.size`) hold in every pipeline instance
because a node of `N ≥ 9` inputs allocates `N / 9 ≥ 1` upper registers and represents
counts up to `N`.

`muaA_main` proves satisfaction and literal bounds in a single walk over the seven
emitted clause families; `muaA_sat`, `muaA_wf`, `muaA_top` are the packaged faces.
-/
import ConwayO7.TotSpec

namespace ConwayO7
namespace MtoSpec

open Encoder TotSpec

/-! ### Plain unary-value semantics -/

/-- `arr` is a unary counter with value `k`: register `i` holds `i + 1 ≤ k`. -/
def UnaryOf (a : Nat → Bool) (arr : Array Int) (k : Nat) : Prop :=
  ∀ i, (h : i < arr.size) → litSat a arr[i] = decide (i + 1 ≤ k)

theorem unaryOf_congr {a a' : Nat → Bool} {arr : Array Int} {k t : Nat}
    (hag : ∀ v ≤ t, a' v = a v) (hb : ∀ l ∈ arr, l.natAbs ≤ t)
    (h : UnaryOf a arr k) : UnaryOf a' arr k := fun i hi ↦ by
  rw [litSat_congr (hag _ (hb _ (arr.getElem_mem hi))), h i hi]

theorem clauseSat_one {a : Nat → Bool} {l : Int} (h : litSat a l = true) :
    clauseSat a [l] = true := by
  unfold clauseSat
  simpa using h

/-- Extend an assignment with a unary counter of *value* `k` on the fresh block
`(base, base + m]`. -/
def extendUnaryVal (a : Nat → Bool) (base m k : Nat) : Nat → Bool :=
  fun v ↦ if base < v ∧ v ≤ base + m then decide (v - base ≤ k) else a v

theorem extendUnaryVal_agree (a : Nat → Bool) (base m k : Nat) :
    ∀ v ≤ base, extendUnaryVal a base m k v = a v := fun v hv ↦
  if_neg (by omega)

theorem unaryOfVal_extend (a : Nat → Bool) (s : St) (m k : Nat) :
    UnaryOf (extendUnaryVal a s.top m k) (freshMany s m).2 k := by
  intro i hi
  rw [freshMany_size] at hi
  rw [freshMany_get s m i hi]
  unfold litSat
  rw [if_neg (by omega : ¬((s.top + 1 + i : Nat) : Int) < 0), Int.natAbs_natCast]
  show (if s.top < s.top + 1 + i ∧ s.top + 1 + i ≤ s.top + m then
      decide (s.top + 1 + i - s.top ≤ k) else a (s.top + 1 + i)) = _
  rw [if_pos ⟨by omega, by omega⟩, show s.top + 1 + i - s.top = i + 1 from by omega]

/-! ### The merge -/

/-- **Satisfiability and literal bounds of `mto_MUA_A` at `p = 9`.**  The fresh carry
gets its semantic value; every emitted clause is then true, and every literal is
bounded by the new counter position. -/
theorem muaA_main (s : St) (a : Nat → Bool) (hs rs ff aa gg bb : Array Int)
    (Cf Cs : Nat)
    (hsat : SatAll a s)
    (hWs : WF s)
    (hhs : UnaryOf a hs ((Cf + Cs) / 9)) (hrs : UnaryOf a rs ((Cf + Cs) % 9))
    (hff : UnaryOf a ff (Cf / 9)) (haa : UnaryOf a aa (Cf % 9))
    (hgg : UnaryOf a gg (Cs / 9)) (hbb : UnaryOf a bb (Cs % 9))
    (hBhs : ∀ l ∈ hs, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hBrs : ∀ l ∈ rs, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hBff : ∀ l ∈ ff, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hBaa : ∀ l ∈ aa, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hBgg : ∀ l ∈ gg, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hBbb : ∀ l ∈ bb, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hrs_sz : rs.size = 8) (haa_sz : aa.size ≤ 8) (hbb_sz : bb.size ≤ 8)
    (hsig : 1 ≤ hs.size) (hcap : (Cf + Cs) / 9 ≤ hs.size) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧
      (∀ c ∈ (muaA s hs rs ff aa gg bb 9).cls,
        clauseSat a' c = true ∧ ∀ l ∈ c, l.natAbs ≤ s.top + 1) := by
  set cv : Bool := decide (9 ≤ Cf % 9 + Cs % 9) with hcv
  set a' : Nat → Bool := fun v ↦ if v = s.top + 1 then cv else a v with ha'
  set c0 : Int := ((s.top + 1 : Nat) : Int) with hc0
  have hag : ∀ v ≤ s.top, a' v = a v := fun v hv ↦ by
    rw [ha']
    exact if_neg (by omega)
  have hcv_iff : cv = true ↔ 9 ≤ Cf % 9 + Cs % 9 := by
    rw [hcv]
    simp
  have hc0_ne : c0 ≠ 0 := by rw [hc0]; omega
  have hc0_abs : c0.natAbs = s.top + 1 := by rw [hc0, Int.natAbs_natCast]
  have hcval : litSat a' c0 = cv := by
    unfold litSat
    rw [if_neg (by rw [hc0]; omega : ¬c0 < 0), hc0_abs, ha']
    simp
  have hncval : litSat a' (-c0) = !cv := by
    rw [litSat_neg a' hc0_ne, hcval]
  -- register values survive the one-variable extension
  have hhs' : UnaryOf a' hs ((Cf + Cs) / 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBhs l hl).2) hhs
  have hrs' : UnaryOf a' rs ((Cf + Cs) % 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBrs l hl).2) hrs
  have hff' : UnaryOf a' ff (Cf / 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBff l hl).2) hff
  have haa' : UnaryOf a' aa (Cf % 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBaa l hl).2) haa
  have hgg' : UnaryOf a' gg (Cs / 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBgg l hl).2) hgg
  have hbb' : UnaryOf a' bb (Cs % 9) :=
    unaryOf_congr hag (fun l hl ↦ (hBbb l hl).2) hbb
  have hsig0 : ¬hs.size = 0 := by omega
  -- helper: literal-negation values
  have hnval : ∀ {arr : Array Int} {k : Nat}, UnaryOf a' arr k →
      (∀ l ∈ arr, l ≠ 0 ∧ l.natAbs ≤ s.top) →
      ∀ i, (h : i < arr.size) → litSat a' (-arr[i]) = !decide (i + 1 ≤ k) := by
    intro arr k hu hB i hi
    rw [litSat_neg a' (hB _ (arr.getElem_mem hi)).1, hu i hi]
  refine ⟨a', hag, ?_⟩
  intro c hc
  simp only [muaA, emitFold_cls, push_cls, fresh_fst_cls, fresh_fst_top, fresh_snd,
    if_neg hsig0] at hc
  rw [← hc0] at hc
  -- the seven families
  rcases Array.mem_append.mp hc with hc | hc6
  rotate_left
  · -- φ₂ double loop
    rw [List.mem_toArray] at hc6
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc6
    rw [List.mem_range] at hi
    obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.mp hci
    rw [List.mem_range] at hj
    have hfv := hnval hff' hBff i hi
    have hgv := hnval hgg' hBgg j hj
    have hBf := hBff _ (ff.getElem_mem hi)
    have hBg := hBgg _ (gg.getElem_mem hj)
    rcases List.mem_cons.mp hcj with rfl | hcj
    · rw [getElem!_pos ff i hi, getElem!_pos gg j hj]
      by_cases hσ : i + j + 2 ≤ hs.size
      · rw [if_pos hσ, getElem!_pos hs (i + j + 1) (by omega)]
        constructor
        · refine SeqSpec.clauseSat_three ?_
          by_cases hfi : i + 1 ≤ Cf / 9
          · by_cases hgj : j + 1 ≤ Cs / 9
            · right; right
              rw [hhs' (i + j + 1) (by omega)]
              simp only [decide_eq_true_eq]
              omega
            · right; left
              rw [hgv]
              simp [hgj]
          · left
            rw [hfv]
            simp [hfi]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show i + j + 1 < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine SeqSpec.clauseSat_two ?_
          by_cases hfi : i + 1 ≤ Cf / 9
          · right
            rw [hgv]
            have : ¬j + 1 ≤ Cs / 9 := by
              intro hgj
              have h1 : i + j + 2 ≤ (Cf + Cs) / 9 := by omega
              omega
            simp [this]
          · left
            rw [hfv]
            simp [hfi]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            rw [Int.natAbs_neg]; omega
    · rw [List.mem_singleton] at hcj
      subst hcj
      rw [getElem!_pos ff i hi, getElem!_pos gg j hj]
      by_cases hσ : i + j + 2 < hs.size
      · rw [if_pos hσ, getElem!_pos hs (i + j + 2) (by omega)]
        constructor
        · refine clauseSat_four ?_
          by_cases hcvv : cv = true
          · by_cases hfi : i + 1 ≤ Cf / 9
            · by_cases hgj : j + 1 ≤ Cs / 9
              · right; right; right
                rw [hhs' (i + j + 2) (by omega)]
                have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                  have := hcv ▸ hcvv
                  simpa using this
                simp only [decide_eq_true_eq]
                omega
              · right; right; left
                rw [hgv]
                simp [hgj]
            · right; left
              rw [hfv]
              simp [hfi]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show i + j + 2 < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine SeqSpec.clauseSat_three ?_
          by_cases hcvv : cv = true
          · by_cases hfi : i + 1 ≤ Cf / 9
            · right; right
              rw [hgv]
              have : ¬j + 1 ≤ Cs / 9 := by
                intro hgj
                have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                  have := hcv ▸ hcvv
                  simpa using this
                have h1 : i + j + 3 ≤ (Cf + Cs) / 9 := by omega
                omega
              simp [this]
            · right; left
              rw [hfv]
              simp [hfi]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            rw [Int.natAbs_neg]; omega
  rcases Array.mem_append.mp hc with hc | hc5
  rotate_left
  · -- φ₂ first-half loop
    rw [List.mem_toArray] at hc5
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc5
    rw [List.mem_range] at hi
    have hfv := hnval hff' hBff i hi
    have hBf := hBff _ (ff.getElem_mem hi)
    rcases List.mem_cons.mp hci with rfl | hci
    · rw [getElem!_pos ff i hi]
      by_cases hσ : i + 1 ≤ hs.size
      · rw [if_pos hσ, getElem!_pos hs i (by omega)]
        constructor
        · refine SeqSpec.clauseSat_two ?_
          by_cases hfi : i + 1 ≤ Cf / 9
          · right
            rw [hhs' i (by omega)]
            simp only [decide_eq_true_eq]
            omega
          · left
            rw [hfv]
            simp [hfi]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show i < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine clauseSat_one ?_
          rw [hfv]
          have : ¬i + 1 ≤ Cf / 9 := by
            intro hfi
            have h1 : i + 1 ≤ (Cf + Cs) / 9 := by omega
            omega
          simp [this]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · simp at hl
    · rw [List.mem_singleton] at hci
      subst hci
      rw [getElem!_pos ff i hi]
      by_cases hσ : i + 1 < hs.size
      · rw [if_pos hσ, getElem!_pos hs (i + 1) (by omega)]
        constructor
        · refine SeqSpec.clauseSat_three ?_
          by_cases hcvv : cv = true
          · by_cases hfi : i + 1 ≤ Cf / 9
            · right; right
              rw [hhs' (i + 1) (by omega)]
              have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                have := hcv ▸ hcvv
                simpa using this
              simp only [decide_eq_true_eq]
              omega
            · right; left
              rw [hfv]
              simp [hfi]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show i + 1 < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine SeqSpec.clauseSat_two ?_
          by_cases hcvv : cv = true
          · right
            rw [hfv]
            have : ¬i + 1 ≤ Cf / 9 := by
              intro hfi
              have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                have := hcv ▸ hcvv
                simpa using this
              have h1 : i + 2 ≤ (Cf + Cs) / 9 := by omega
              omega
            simp [this]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · omega
          · rw [List.mem_singleton] at hl
            subst hl
            rw [Int.natAbs_neg]; omega
  rcases Array.mem_append.mp hc with hc | hc4
  rotate_left
  · -- φ₂ second-half loop
    rw [List.mem_toArray] at hc4
    obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.mp hc4
    rw [List.mem_range] at hj
    have hgv := hnval hgg' hBgg j hj
    have hBg := hBgg _ (gg.getElem_mem hj)
    rcases List.mem_cons.mp hcj with rfl | hcj
    · rw [getElem!_pos gg j hj]
      by_cases hσ : j + 1 ≤ hs.size
      · rw [if_pos hσ, getElem!_pos hs j (by omega)]
        constructor
        · refine SeqSpec.clauseSat_two ?_
          by_cases hgj : j + 1 ≤ Cs / 9
          · right
            rw [hhs' j (by omega)]
            simp only [decide_eq_true_eq]
            omega
          · left
            rw [hgv]
            simp [hgj]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show j < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine clauseSat_one ?_
          rw [hgv]
          have : ¬j + 1 ≤ Cs / 9 := by
            intro hgj
            have h1 : j + 1 ≤ (Cf + Cs) / 9 := by omega
            omega
          simp [this]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · simp at hl
    · rw [List.mem_singleton] at hcj
      subst hcj
      rw [getElem!_pos gg j hj]
      by_cases hσ : j + 1 < hs.size
      · rw [if_pos hσ, getElem!_pos hs (j + 1) (by omega)]
        constructor
        · refine SeqSpec.clauseSat_three ?_
          by_cases hcvv : cv = true
          · by_cases hgj : j + 1 ≤ Cs / 9
            · right; right
              rw [hhs' (j + 1) (by omega)]
              have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                have := hcv ▸ hcvv
                simpa using this
              simp only [decide_eq_true_eq]
              omega
            · right; left
              rw [hgv]
              simp [hgj]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          have hBh := hBhs _ (hs.getElem_mem (show j + 1 < hs.size by omega))
          rcases List.mem_cons.mp hl with rfl | hl
          · omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            omega
      · rw [if_neg hσ]
        constructor
        · refine SeqSpec.clauseSat_two ?_
          by_cases hcvv : cv = true
          · right
            rw [hgv]
            have : ¬j + 1 ≤ Cs / 9 := by
              intro hgj
              have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
                have := hcv ▸ hcvv
                simpa using this
              have h1 : j + 2 ≤ (Cf + Cs) / 9 := by omega
              omega
            simp [this]
          · left
            rw [hncval]
            simp [hcvv]
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · omega
          · rw [List.mem_singleton] at hl
            subst hl
            rw [Int.natAbs_neg]; omega
  rcases Array.mem_push.mp hc with hc | hcH
  rotate_left
  · -- the head clause  [-c, hs[0]]
    subst hcH
    rw [getElem!_pos hs 0 (by omega)]
    constructor
    · refine SeqSpec.clauseSat_two ?_
      by_cases hcvv : cv = true
      · right
        rw [hhs' 0 (by omega)]
        have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by
          have := hcv ▸ hcvv
          simpa using this
        simp only [decide_eq_true_eq]
        omega
      · left
        rw [hncval]
        simp [hcvv]
    · intro l hl
      have hBh := hBhs _ (hs.getElem_mem (show 0 < hs.size by omega))
      rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · rw [List.mem_singleton] at hl
        subst hl
        omega
  rcases Array.mem_append.mp hc with hc | hc3
  rotate_left
  · -- φ₁ double loop
    rw [List.mem_toArray] at hc3
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc3
    rw [List.mem_range] at hi
    obtain ⟨j, hj, hcj⟩ := List.mem_map.mp hci
    rw [List.mem_range] at hj
    subst hcj
    have hav := hnval haa' hBaa i hi
    have hbv := hnval hbb' hBbb j hj
    have hBa := hBaa _ (aa.getElem_mem hi)
    have hBb := hBbb _ (bb.getElem_mem hj)
    rw [getElem!_pos aa i hi, getElem!_pos bb j hj]
    rcases lt_trichotomy (i + j + 2) 9 with hlt | heq | hgt
    · rw [if_pos hlt, getElem!_pos rs (i + j + 1) (by omega)]
      constructor
      · refine clauseSat_four ?_
        by_cases hai : i + 1 ≤ Cf % 9
        · by_cases hbj : j + 1 ≤ Cs % 9
          · by_cases hcvv : cv = true
            · right; right; right
              rw [hcval, hcvv]
            · right; right; left
              rw [hrs' (i + j + 1) (by omega)]
              have hncv9 : ¬9 ≤ Cf % 9 + Cs % 9 := by
                intro h9
                exact hcvv (by rw [hcv]; simpa using h9)
              simp only [decide_eq_true_eq]
              omega
          · right; left
            rw [hbv]
            simp [hbj]
        · left
          rw [hav]
          simp [hai]
      · intro l hl
        have hBr := hBrs _ (rs.getElem_mem (show i + j + 1 < rs.size by omega))
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        rcases List.mem_cons.mp hl with rfl | hl
        · omega
        · rw [List.mem_singleton] at hl
          subst hl
          omega
    · rw [if_neg (by omega), if_neg (by omega)]
      constructor
      · refine SeqSpec.clauseSat_three ?_
        by_cases hai : i + 1 ≤ Cf % 9
        · by_cases hbj : j + 1 ≤ Cs % 9
          · right; right
            rw [hcval]
            have : cv = true := by
              rw [hcv]
              simp only [decide_eq_true_eq]
              omega
            rw [this]
          · right; left
            rw [hbv]
            simp [hbj]
        · left
          rw [hav]
          simp [hai]
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        · rw [List.mem_singleton] at hl
          subst hl
          omega
    · rw [if_neg (by omega), if_pos hgt,
        getElem!_pos rs ((i + j + 2) % 9 - 1) (by omega)]
      constructor
      · refine SeqSpec.clauseSat_three ?_
        by_cases hai : i + 1 ≤ Cf % 9
        · by_cases hbj : j + 1 ≤ Cs % 9
          · right; right
            rw [hrs' ((i + j + 2) % 9 - 1) (by omega)]
            have hcv9 : 9 ≤ Cf % 9 + Cs % 9 := by omega
            simp only [decide_eq_true_eq]
            omega
          · right; left
            rw [hbv]
            simp [hbj]
        · left
          rw [hav]
          simp [hai]
      · intro l hl
        have hBr := hBrs _ (rs.getElem_mem (show (i + j + 2) % 9 - 1 < rs.size by omega))
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]; omega
        · rw [List.mem_singleton] at hl
          subst hl
          omega
  rcases Array.mem_append.mp hc with hc | hc2
  rotate_left
  · -- φ₁ first-half loop  [-aa[i], rs[i], c]
    rw [List.mem_toArray] at hc2
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc2
    rw [List.mem_range] at hi
    rw [List.mem_singleton] at hci
    subst hci
    have hav := hnval haa' hBaa i hi
    have hBa := hBaa _ (aa.getElem_mem hi)
    rw [getElem!_pos aa i hi, getElem!_pos rs i (by omega)]
    constructor
    · refine SeqSpec.clauseSat_three ?_
      by_cases hai : i + 1 ≤ Cf % 9
      · by_cases hcvv : cv = true
        · right; right
          rw [hcval, hcvv]
        · right; left
          rw [hrs' i (by omega)]
          have hncv9 : ¬9 ≤ Cf % 9 + Cs % 9 := fun h9 ↦ hcvv (hcv_iff.mpr h9)
          simp only [decide_eq_true_eq]
          omega
      · left
        rw [hav]
        simp [hai]
    · intro l hl
      have hBr := hBrs _ (rs.getElem_mem (show i < rs.size by omega))
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]; omega
      rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · rw [List.mem_singleton] at hl
        subst hl
        omega
  rcases Array.mem_append.mp hc with hc | hc1
  · -- previously emitted clauses
    refine ⟨?_, fun l hl ↦ le_trans (hWs.2 c hc l hl) (by omega)⟩
    rw [clauseSat_congr (a := a') (b := a) fun l hl ↦ hag l.natAbs (hWs.2 c hc l hl)]
    exact hsat c hc
  · -- φ₁ second-half loop  [-bb[j], rs[j], c]
    rw [List.mem_toArray] at hc1
    obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.mp hc1
    rw [List.mem_range] at hj
    rw [List.mem_singleton] at hcj
    subst hcj
    have hbv := hnval hbb' hBbb j hj
    have hBb := hBbb _ (bb.getElem_mem hj)
    rw [getElem!_pos bb j hj, getElem!_pos rs j (by omega)]
    constructor
    · refine SeqSpec.clauseSat_three ?_
      by_cases hbj : j + 1 ≤ Cs % 9
      · by_cases hcvv : cv = true
        · right; right
          rw [hcval, hcvv]
        · right; left
          rw [hrs' j (by omega)]
          have hncv9 : ¬9 ≤ Cf % 9 + Cs % 9 := fun h9 ↦ hcvv (hcv_iff.mpr h9)
          simp only [decide_eq_true_eq]
          omega
      · left
        rw [hbv]
        simp [hbj]
    · intro l hl
      have hBr := hBrs _ (rs.getElem_mem (show j < rs.size by omega))
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]; omega
      rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · rw [List.mem_singleton] at hl
        subst hl
        omega

/-! ### Preparing a half-block -/

/-- **Satisfiability of `mtoPrepHalf`**: a short half gets a totalizer (upper counter
empty, `C / 9 = 0`); a long half gets fresh registers assigned `C / 9` and `C % 9`.
Either way the emitted state is satisfiable by fresh extension and the returned
registers carry the div/mod unary counters of the half's count. -/
theorem mtoPrepHalf_sat (t : St) (b : Nat → Bool) (xs : Array Int)
    (hw : WF t) (hs : SatAll b t)
    (hin : ∀ x ∈ xs, x ≠ 0 ∧ x.natAbs ≤ t.top) :
    ∃ b', (∀ v ≤ t.top, b' v = b v) ∧
      SatAll b' (mtoPrepHalf t xs 9).1 ∧ WF (mtoPrepHalf t xs 9).1 ∧
      t.top ≤ (mtoPrepHalf t xs 9).1.top ∧
      UnaryOf b' (mtoPrepHalf t xs 9).2.1 (countT b xs / 9) ∧
      UnaryOf b' (mtoPrepHalf t xs 9).2.2.1 (countT b xs % 9) ∧
      (∀ x ∈ (mtoPrepHalf t xs 9).2.1,
        x ≠ 0 ∧ x.natAbs ≤ (mtoPrepHalf t xs 9).1.top) ∧
      (∀ x ∈ (mtoPrepHalf t xs 9).2.2.1,
        x ≠ 0 ∧ x.natAbs ≤ (mtoPrepHalf t xs 9).1.top) ∧
      (mtoPrepHalf t xs 9).2.2.1.size ≤ 8 ∧
      (9 ≤ xs.size → (mtoPrepHalf t xs 9).2.1.size = xs.size / 9 ∧
        (mtoPrepHalf t xs 9).2.2.1.size = 8) ∧
      ((mtoPrepHalf t xs 9).2.2.2 = true ↔ 9 ≤ xs.size) := by
  by_cases hlt : xs.size < 9
  · -- short half: full totalizer
    have e1 : (mtoPrepHalf t xs 9).1 = (toTO t xs).1 := by
      unfold mtoPrepHalf
      rw [if_pos hlt]
    have e2 : (mtoPrepHalf t xs 9).2.1 = #[] := by
      unfold mtoPrepHalf
      rw [if_pos hlt]
    have e3 : (mtoPrepHalf t xs 9).2.2.1 = (toTO t xs).2 := by
      unfold mtoPrepHalf
      rw [if_pos hlt]
    have e4 : (mtoPrepHalf t xs 9).2.2.2 = false := by
      unfold mtoPrepHalf
      rw [if_pos hlt]
    rw [e1, e2, e3, e4]
    obtain ⟨b', hag, hsat', hw', htop', hun, hbnd, hsz⟩ := toTO_sat t xs b hw hs hin
    have hC9 : countT b xs < 9 := by
      have h1 : countT b xs ≤ xs.size := List.countP_le_length ..
      omega
    have hCmod : countT b xs % 9 = countT b xs := Nat.mod_eq_of_lt hC9
    have hCdiv : countT b xs / 9 = 0 := Nat.div_eq_of_lt hC9
    have hcnt' : countT b' xs = countT b xs :=
      countT_congr hag fun x hx ↦ (hin x hx).2
    refine ⟨b', hag, hsat', hw', htop', ?_, ?_, by simp, hbnd, by omega,
      by omega, by simp; omega⟩
    · intro i hi
      simp at hi
    · rw [hCmod]
      intro i hi
      rw [hun.2 i hi, hcnt']
  · -- long half: fresh div/mod registers
    have e1 : (mtoPrepHalf t xs 9).1 = (freshMany (freshMany t (xs.size / 9)).1 8).1 := by
      unfold mtoPrepHalf
      rw [if_neg hlt]
    have e2 : (mtoPrepHalf t xs 9).2.1 = (freshMany t (xs.size / 9)).2 := by
      unfold mtoPrepHalf
      rw [if_neg hlt]
    have e3 : (mtoPrepHalf t xs 9).2.2.1
        = (freshMany (freshMany t (xs.size / 9)).1 8).2 := by
      unfold mtoPrepHalf
      rw [if_neg hlt]
    have e4 : (mtoPrepHalf t xs 9).2.2.2 = true := by
      unfold mtoPrepHalf
      rw [if_neg hlt]
    rw [e1, e2, e3, e4]
    set m := xs.size / 9 with hm
    set t1 := (freshMany t m).1 with ht1
    have ht1top : t1.top = t.top + m := freshMany_top ..
    have ht1cls : t1.cls = t.cls := freshMany_cls ..
    set b1 := extendUnaryVal b t.top m (countT b xs / 9) with hb1
    have hag1 := extendUnaryVal_agree b t.top m (countT b xs / 9)
    set b2 := extendUnaryVal b1 t1.top 8 (countT b xs % 9) with hb2
    have hag2 := extendUnaryVal_agree b1 t1.top 8 (countT b xs % 9)
    have hag : ∀ v ≤ t.top, b2 v = b v := fun v hv ↦
      (hag2 v (by omega)).trans (hag1 v hv)
    have hunU : UnaryOf b2 (freshMany t m).2 (countT b xs / 9) := by
      refine unaryOf_congr (t := t1.top) hag2 ?_ (unaryOfVal_extend b t m (countT b xs / 9))
      intro x hx
      have := freshMany_mem t m x hx
      omega
    have hunL : UnaryOf b2 (freshMany t1 8).2 (countT b xs % 9) :=
      unaryOfVal_extend b1 t1 8 (countT b xs % 9)
    have hsat2 : SatAll b2 (freshMany t1 8).1 := by
      intro c hc
      rw [freshMany_cls, ht1cls] at hc
      exact satAll_of_agree hw hs hag c hc
    have hw2 : WF (freshMany t1 8).1 := by
      refine ⟨by rw [freshMany_top]; have := hw.1; omega, ?_⟩
      intro c hc l hl
      rw [freshMany_cls, ht1cls] at hc
      rw [freshMany_top]
      exact le_trans (hw.2 c hc l hl) (by omega)
    refine ⟨b2, hag, hsat2, hw2, by rw [freshMany_top]; omega, hunU, hunL, ?_, ?_,
      by rw [freshMany_size], fun _ ↦ ⟨freshMany_size .., freshMany_size ..⟩, by simp; omega⟩
    · intro x hx
      have := freshMany_mem t m x hx
      rw [freshMany_top]
      exact ⟨by omega, by omega⟩
    · intro x hx
      have := freshMany_mem t1 8 x hx
      rw [freshMany_top]
      exact ⟨by omega, by omega⟩

/-- The merge allocates exactly its carry variable. -/
theorem muaA_top (s : St) (hs rs ff aa gg bb : Array Int) (hσ : ¬hs.size = 0) :
    (muaA s hs rs ff aa gg bb 9).top = s.top + 1 := by
  simp only [muaA, emitFold_top, if_neg hσ, push_top, fresh_fst_top]

/-! ### The modulo-totalizer tree -/

/-- **Satisfiability of the `mto` tree at `p = 9`**: with parent registers carrying
the div/mod unary counters of the input count, all node clauses (carry allocation,
merge, recursive sub-blocks) are satisfiable by fresh extension. -/
theorem mtoNode_sat :
    ∀ (fuel : Nat) (ilst ulst llst : Array Int) (s : St) (a : Nat → Bool),
      ilst.size ≤ fuel → 9 ≤ ilst.size →
      WF s → SatAll a s →
      (∀ x ∈ ilst, x ≠ 0 ∧ x.natAbs ≤ s.top) →
      (∀ x ∈ ulst, x ≠ 0 ∧ x.natAbs ≤ s.top) →
      (∀ x ∈ llst, x ≠ 0 ∧ x.natAbs ≤ s.top) →
      1 ≤ ulst.size → llst.size = 8 →
      countT a ilst / 9 ≤ ulst.size →
      UnaryOf a ulst (countT a ilst / 9) →
      UnaryOf a llst (countT a ilst % 9) →
      ∃ a', (∀ v ≤ s.top, a' v = a v) ∧
        SatAll a' (mtoNode fuel s ilst ulst llst 9) ∧
        WF (mtoNode fuel s ilst ulst llst 9) ∧
        s.top ≤ (mtoNode fuel s ilst ulst llst 9).top := by
  intro fuel
  induction fuel with
  | zero =>
    intro ilst ulst llst s a hf h9 _ _ _ _ _ _ _ _ _ _
    exact absurd hf (by omega)
  | succ fuel ih =>
    intro ilst ulst llst s a hf h9 hw hs hin hBu hBl hu1 hl8 hcap hunU hunL
    have hn2 : 2 ≤ ilst.size := by omega
    have hf_sz : (ilst.extract 0 (ilst.size - ilst.size / 2)).size
        = ilst.size - ilst.size / 2 := by
      rw [Array.size_extract]
      omega
    have hs_sz : (ilst.extract (ilst.size - ilst.size / 2) ilst.size).size
        = ilst.size / 2 := by
      rw [Array.size_extract]
      omega
    have hin_f : ∀ x ∈ ilst.extract 0 (ilst.size - ilst.size / 2),
        x ≠ 0 ∧ x.natAbs ≤ s.top := fun x hx ↦ hin x (mem_of_mem_extract hx)
    have hin_s : ∀ x ∈ ilst.extract (ilst.size - ilst.size / 2) ilst.size,
        x ≠ 0 ∧ x.natAbs ≤ s.top := fun x hx ↦ hin x (mem_of_mem_extract hx)
    have hCsplit : countT a ilst
        = countT a (ilst.extract 0 (ilst.size - ilst.size / 2))
          + countT a (ilst.extract (ilst.size - ilst.size / 2) ilst.size) :=
      countT_extract_split a ilst (ilst.size - ilst.size / 2) (by omega)
    -- prepare the first half
    obtain ⟨a1, hag1, hsat1, hw1, htop1, hunU1, hunL1, hbU1, hbL1, hszL1, hbig1, hflag1⟩ :=
      mtoPrepHalf_sat s a (ilst.extract 0 (ilst.size - ilst.size / 2)) hw hs hin_f
    -- prepare the second half
    obtain ⟨a2, hag2, hsat2, hw2, htop2, hunU2, hunL2, hbU2, hbL2, hszL2, hbig2, hflag2⟩ :=
      mtoPrepHalf_sat (mtoPrepHalf s (ilst.extract 0 (ilst.size - ilst.size / 2)) 9).1
        a1 (ilst.extract (ilst.size - ilst.size / 2) ilst.size) hw1 hsat1
        (fun x hx ↦ ⟨(hin_s x hx).1, le_trans (hin_s x hx).2 htop1⟩)
    -- fold the two preparations
    set fstA := ilst.extract 0 (ilst.size - ilst.size / 2) with hfstA
    set sndA := ilst.extract (ilst.size - ilst.size / 2) ilst.size with hsndA
    set pf := mtoPrepHalf s fstA 9 with hpf
    set ps := mtoPrepHalf pf.1 sndA 9 with hps
    set Cf := countT a fstA with hCf
    set Cs := countT a sndA with hCs
    -- the second preparation counts under `a1` equal those under `a`
    have hcs1 : countT a1 sndA = Cs :=
      countT_congr hag1 fun x hx ↦ (hin_s x hx).2
    rw [hcs1] at hunU2 hunL2
    have hag2a : ∀ v ≤ s.top, a2 v = a v := fun v hv ↦
      (hag2 v (by omega)).trans (hag1 v hv)
    -- the merge
    have hσ0 : ¬ulst.size = 0 := by omega
    obtain ⟨a3, hag3, hfacts⟩ :=
      muaA_main ps.1 a2 ulst llst pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 Cf Cs
        hsat2 hw2
        (by
          refine unaryOf_congr (t := s.top) hag2a (fun x hx ↦ (hBu x hx).2) ?_
          rw [← hCsplit]
          exact hunU)
        (by
          refine unaryOf_congr (t := s.top) hag2a (fun x hx ↦ (hBl x hx).2) ?_
          rw [← hCsplit]
          exact hunL)
        (by
          refine unaryOf_congr (t := pf.1.top) hag2 (fun x hx ↦ (hbU1 x hx).2) ?_
          exact hunU1)
        (by
          refine unaryOf_congr (t := pf.1.top) hag2 (fun x hx ↦ (hbL1 x hx).2) ?_
          exact hunL1)
        hunU2 hunL2
        (fun x hx ↦ ⟨(hBu x hx).1, by have := (hBu x hx).2; omega⟩)
        (fun x hx ↦ ⟨(hBl x hx).1, by have := (hBl x hx).2; omega⟩)
        (fun x hx ↦ ⟨(hbU1 x hx).1, by have := (hbU1 x hx).2; omega⟩)
        (fun x hx ↦ ⟨(hbL1 x hx).1, by have := (hbL1 x hx).2; omega⟩)
        (fun x hx ↦ ⟨(hbU2 x hx).1, (hbU2 x hx).2⟩)
        (fun x hx ↦ ⟨(hbL2 x hx).1, (hbL2 x hx).2⟩)
        hl8 hszL1 hszL2 hu1
        (by rw [← hCsplit]; exact hcap)
    set s2 := muaA ps.1 ulst llst pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 9 with hs2
    have hsat3 : SatAll a3 s2 := fun c hc ↦ (hfacts c hc).1
    have hs2top : s2.top = ps.1.top + 1 := by
      rw [hs2]
      exact muaA_top ps.1 ulst llst pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 hσ0
    have hw3 : WF s2 := by
      refine ⟨by have := hw.1; omega, ?_⟩
      intro c hc l hl
      have := (hfacts c hc).2 l hl
      omega
    -- counts survive to `a3`
    have hag3a : ∀ v ≤ s.top, a3 v = a v := fun v hv ↦
      (hag3 v (by omega)).trans (hag2a v hv)
    have hcf3 : countT a3 fstA = Cf :=
      countT_congr hag3a fun x hx ↦ (hin_f x hx).2
    have hcs3 : countT a3 sndA = Cs :=
      countT_congr hag3a fun x hx ↦ (hin_s x hx).2
    -- recurse into the second half
    set s3 := (if ps.2.2.2 = true then mtoNode fuel s2 sndA ps.2.1 ps.2.2.1 9 else s2)
      with hs3
    have step3 : ∃ a4, (∀ v ≤ s2.top, a4 v = a3 v) ∧ SatAll a4 s3 ∧ WF s3 ∧
        s2.top ≤ s3.top := by
      by_cases hbs : ps.2.2.2 = true
      · rw [hs3, if_pos hbs]
        have h9s : 9 ≤ sndA.size := hflag2.mp hbs
        obtain ⟨hszU2, hszL2'⟩ := hbig2 h9s
        have hCs_le : Cs ≤ sndA.size := by
          rw [hCs]
          exact List.countP_le_length ..
        refine ih sndA ps.2.1 ps.2.2.1 s2 a3 (by omega) h9s hw3 hsat3
          (fun x hx ↦ ⟨(hin_s x hx).1, by have := (hin_s x hx).2; omega⟩)
          (fun x hx ↦ ⟨(hbU2 x hx).1, by have := (hbU2 x hx).2; omega⟩)
          (fun x hx ↦ ⟨(hbL2 x hx).1, by have := (hbL2 x hx).2; omega⟩)
          (by omega) hszL2' (by rw [hcs3]; omega) ?_ ?_
        · rw [hcs3]
          refine unaryOf_congr (t := ps.1.top) hag3 (fun x hx ↦ (hbU2 x hx).2) hunU2
        · rw [hcs3]
          refine unaryOf_congr (t := ps.1.top) hag3 (fun x hx ↦ (hbL2 x hx).2) hunL2
      · rw [hs3, if_neg hbs]
        exact ⟨a3, fun _ _ ↦ rfl, hsat3, hw3, le_refl _⟩
    obtain ⟨a4, hag4, hsat4, hw4, htop4⟩ := step3
    have hcf4 : countT a4 fstA = Cf := by
      rw [← hcf3]
      exact countT_congr hag4 fun x hx ↦ by have := (hin_f x hx).2; omega
    -- recurse into the first half
    set s4 := (if pf.2.2.2 = true then mtoNode fuel s3 fstA pf.2.1 pf.2.2.1 9 else s3)
      with hs4
    have step4 : ∃ a5, (∀ v ≤ s3.top, a5 v = a4 v) ∧ SatAll a5 s4 ∧ WF s4 ∧
        s3.top ≤ s4.top := by
      by_cases hbf : pf.2.2.2 = true
      · rw [hs4, if_pos hbf]
        have h9f : 9 ≤ fstA.size := hflag1.mp hbf
        obtain ⟨hszU1, hszL1'⟩ := hbig1 h9f
        have hCf_le : Cf ≤ fstA.size := by
          rw [hCf]
          exact List.countP_le_length ..
        refine ih fstA pf.2.1 pf.2.2.1 s3 a4 (by omega) h9f hw4 hsat4
          (fun x hx ↦ ⟨(hin_f x hx).1, by have := (hin_f x hx).2; omega⟩)
          (fun x hx ↦ ⟨(hbU1 x hx).1, by have := (hbU1 x hx).2; omega⟩)
          (fun x hx ↦ ⟨(hbL1 x hx).1, by have := (hbL1 x hx).2; omega⟩)
          (by omega) hszL1' (by rw [hcf4]; omega) ?_ ?_
        · rw [hcf4]
          refine unaryOf_congr (t := s2.top) hag4 ?_ ?_
          · intro x hx
            have := (hbU1 x hx).2
            omega
          · refine unaryOf_congr (t := ps.1.top) hag3
              (fun x hx ↦ le_trans (hbU1 x hx).2 htop2) ?_
            refine unaryOf_congr (t := pf.1.top) hag2 (fun x hx ↦ (hbU1 x hx).2) hunU1
        · rw [hcf4]
          refine unaryOf_congr (t := s2.top) hag4 ?_ ?_
          · intro x hx
            have := (hbL1 x hx).2
            omega
          · refine unaryOf_congr (t := ps.1.top) hag3
              (fun x hx ↦ le_trans (hbL1 x hx).2 htop2) ?_
            refine unaryOf_congr (t := pf.1.top) hag2 (fun x hx ↦ (hbL1 x hx).2) hunL1
      · rw [hs4, if_neg hbf]
        exact ⟨a4, fun _ _ ↦ rfl, hsat4, hw4, le_refl _⟩
    obtain ⟨a5, hag5, hsat5, hw5, htop5⟩ := step4
    have hbody : mtoNode (fuel + 1) s ilst ulst llst 9 = s4 := rfl
    rw [hbody]
    exact ⟨a5, fun v hv ↦ (hag5 v (by omega)).trans ((hag4 v (by omega)).trans
        (hag3a v hv)),
      hsat5, hw5, by omega⟩

/-! ### Wrapper, comparator, and the at-most dispatch -/

/-- **Satisfiability of `mtoMTO`** (long-input path, as used by every degree
constraint): the returned upper/lower registers carry `C / 9` and `C % 9`. -/
theorem mtoMTO_sat (s : St) (xs : Array Int) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s) (h9 : 9 ≤ xs.size)
    (hin : ∀ x ∈ xs, x ≠ 0 ∧ x.natAbs ≤ s.top) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧
      SatAll a' (mtoMTO s xs 9).1 ∧ WF (mtoMTO s xs 9).1 ∧
      s.top ≤ (mtoMTO s xs 9).1.top ∧
      UnaryOf a' (mtoMTO s xs 9).2.1 (countT a xs / 9) ∧
      UnaryOf a' (mtoMTO s xs 9).2.2 (countT a xs % 9) ∧
      (∀ x ∈ (mtoMTO s xs 9).2.1, x ≠ 0 ∧ x.natAbs ≤ (mtoMTO s xs 9).1.top) ∧
      (∀ x ∈ (mtoMTO s xs 9).2.2, x ≠ 0 ∧ x.natAbs ≤ (mtoMTO s xs 9).1.top) ∧
      (mtoMTO s xs 9).2.2.size = 8 := by
  have hnlt : ¬xs.size < 9 := by omega
  have e1 : (mtoMTO s xs 9).1
      = mtoNode xs.size (freshMany (freshMany s (xs.size / 9)).1 (9 - 1)).1 xs
        (freshMany s (xs.size / 9)).2 (freshMany (freshMany s (xs.size / 9)).1 (9 - 1)).2
        9 := by
    unfold mtoMTO
    rw [if_neg hnlt]
  have e2 : (mtoMTO s xs 9).2.1 = (freshMany s (xs.size / 9)).2 := by
    unfold mtoMTO
    rw [if_neg hnlt]
  have e3 : (mtoMTO s xs 9).2.2
      = (freshMany (freshMany s (xs.size / 9)).1 (9 - 1)).2 := by
    unfold mtoMTO
    rw [if_neg hnlt]
  rw [e1, e2, e3]
  set C := countT a xs with hC
  set m := xs.size / 9 with hm
  set t1 := (freshMany s m).1 with ht1
  have ht1top : t1.top = s.top + m := freshMany_top ..
  have ht1cls : t1.cls = s.cls := freshMany_cls ..
  set t2 := (freshMany t1 (9 - 1)).1 with ht2
  have ht2top : t2.top = t1.top + (9 - 1) := freshMany_top ..
  have ht2cls : t2.cls = t1.cls := freshMany_cls ..
  set b1 := extendUnaryVal a s.top m (C / 9) with hb1
  have hag1 := extendUnaryVal_agree a s.top m (C / 9)
  set b2 := extendUnaryVal b1 t1.top (9 - 1) (C % 9) with hb2
  have hag2 := extendUnaryVal_agree b1 t1.top (9 - 1) (C % 9)
  have hag : ∀ v ≤ s.top, b2 v = a v := fun v hv ↦
    (hag2 v (by omega)).trans (hag1 v hv)
  have hunU : UnaryOf b2 (freshMany s m).2 (C / 9) := by
    refine unaryOf_congr (t := t1.top) hag2 ?_ (unaryOfVal_extend a s m (C / 9))
    intro x hx
    have := freshMany_mem s m x hx
    omega
  have hunL : UnaryOf b2 (freshMany t1 (9 - 1)).2 (C % 9) :=
    unaryOfVal_extend b1 t1 (9 - 1) (C % 9)
  have hsat2 : SatAll b2 t2 := by
    intro c hc
    rw [ht2cls, ht1cls] at hc
    exact satAll_of_agree hw hs hag c hc
  have hw2 : WF t2 := by
    refine ⟨by have := hw.1; omega, ?_⟩
    intro c hc l hl
    rw [ht2cls, ht1cls] at hc
    exact le_trans (hw.2 c hc l hl) (by omega)
  have hBu : ∀ x ∈ (freshMany s m).2, x ≠ 0 ∧ x.natAbs ≤ t2.top := by
    intro x hx
    have := freshMany_mem s m x hx
    exact ⟨by omega, by omega⟩
  have hBl : ∀ x ∈ (freshMany t1 (9 - 1)).2, x ≠ 0 ∧ x.natAbs ≤ t2.top := by
    intro x hx
    have := freshMany_mem t1 (9 - 1) x hx
    exact ⟨by omega, by omega⟩
  have hcnt2 : countT b2 xs = C := by
    rw [hC]
    exact countT_congr hag fun x hx ↦ (hin x hx).2
  have hCle : C ≤ xs.size := by
    rw [hC]
    exact List.countP_le_length ..
  have hszU : (freshMany s m).2.size = m := freshMany_size ..
  have hszL : (freshMany t1 (9 - 1)).2.size = 9 - 1 := freshMany_size ..
  obtain ⟨a', hag', hsat', hw', htop'⟩ :=
    mtoNode_sat xs.size xs (freshMany s m).2 (freshMany t1 (9 - 1)).2 t2 b2
      (le_refl _) h9 hw2 hsat2
      (fun x hx ↦ ⟨(hin x hx).1, by have := (hin x hx).2; omega⟩)
      hBu hBl (by omega) (by omega)
      (by rw [hcnt2]; omega)
      (by rw [hcnt2]; exact hunU)
      (by rw [hcnt2]; exact hunL)
  refine ⟨a', fun v hv ↦ (hag' v (by omega)).trans (hag v hv), hsat', hw',
    by omega, ?_, ?_, ?_, ?_, by omega⟩
  · exact unaryOf_congr (t := t2.top) hag' (fun x hx ↦ (hBu x hx).2) hunU
  · exact unaryOf_congr (t := t2.top) hag' (fun x hx ↦ (hBl x hx).2) hunL
  · intro x hx
    have := hBu x hx
    exact ⟨this.1, by omega⟩
  · intro x hx
    have := hBl x hx
    exact ⟨this.1, by omega⟩

/-- The comparator adds no variables. -/
theorem mtoComparator_top (s : St) (upper lower : Array Int) (p k : Nat) :
    (mtoComparator s upper lower p k).top = s.top := by
  simp only [mtoComparator, emitFold_top]

/-- **Satisfiability of the comparator**: with the represented count at most `k`,
every emitted unit and binary clause holds (no fresh variables). -/
theorem mtoComparator_sat (s : St) (a : Nat → Bool) (upper lower : Array Int)
    (k C : Nat)
    (hsat : SatAll a s) (hw : WF s)
    (hu : UnaryOf a upper (C / 9)) (hl : UnaryOf a lower (C % 9))
    (hC : C ≤ k)
    (hBu : ∀ x ∈ upper, x ≠ 0 ∧ x.natAbs ≤ s.top)
    (hBl : ∀ x ∈ lower, x ≠ 0 ∧ x.natAbs ≤ s.top)
    (hl8 : lower.size = 8) :
    SatAll a (mtoComparator s upper lower 9 k) ∧
      WF (mtoComparator s upper lower 9 k) := by
  have huv : ∀ i, (h : i < upper.size) → litSat a (-upper[i]) = !decide (i + 1 ≤ C / 9) :=
    fun i hi ↦ by
      rw [litSat_neg a (hBu _ (upper.getElem_mem hi)).1, hu i hi]
  have hlv : ∀ i, (h : i < lower.size) → litSat a (-lower[i]) = !decide (i + 1 ≤ C % 9) :=
    fun i hi ↦ by
      rw [litSat_neg a (hBl _ (lower.getElem_mem hi)).1, hl i hi]
  have hmain : ∀ c ∈ (mtoComparator s upper lower 9 k).cls,
      clauseSat a c = true ∧ ∀ l ∈ c, l.natAbs ≤ s.top := by
    intro c hc
    simp only [mtoComparator, emitFold_cls] at hc
    rcases Array.mem_append.mp hc with hc | hc2
    · rcases Array.mem_append.mp hc with hc | hc1
      · exact ⟨hsat c hc, fun l hl ↦ hw.2 c hc l hl⟩
      · -- units killing out-of-range upper registers
        rw [List.mem_toArray] at hc1
        obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc1
        rw [List.mem_range'_1] at hi
        rw [List.mem_singleton] at hci
        subst hci
        have hi1 : i - 1 < upper.size := by omega
        rw [getElem!_pos upper (i - 1) hi1]
        refine ⟨clauseSat_one ?_, ?_⟩
        · rw [huv (i - 1) hi1]
          have : ¬i - 1 + 1 ≤ C / 9 := by omega
          simp [this]
        · intro l hl
          rw [List.mem_singleton] at hl
          subst hl
          rw [Int.natAbs_neg]
          exact (hBu _ (upper.getElem_mem hi1)).2
    · -- the lower guard
      rw [List.mem_toArray] at hc2
      obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc2
      rw [List.mem_range'_1] at hi
      have hi1 : i - 1 < lower.size := by omega
      by_cases hro : k / 9 > 0
      · rw [if_pos hro] at hci
        by_cases hru : k / 9 - 1 < upper.size
        · rw [if_pos hru, List.mem_singleton] at hci
          subst hci
          rw [getElem!_pos upper (k / 9 - 1) hru, getElem!_pos lower (i - 1) hi1]
          refine ⟨SeqSpec.clauseSat_two ?_, ?_⟩
          · by_cases hup : k / 9 ≤ C / 9
            · right
              rw [hlv (i - 1) hi1]
              have : ¬i - 1 + 1 ≤ C % 9 := by omega
              simp [this]
            · left
              rw [huv (k / 9 - 1) hru]
              have : ¬k / 9 - 1 + 1 ≤ C / 9 := by omega
              simp [this]
          · intro l hl
            rcases List.mem_cons.mp hl with rfl | hl
            · rw [Int.natAbs_neg]
              exact (hBu _ (upper.getElem_mem hru)).2
            · rw [List.mem_singleton] at hl
              subst hl
              rw [Int.natAbs_neg]
              exact (hBl _ (lower.getElem_mem hi1)).2
        · rw [if_neg hru] at hci
          exact absurd hci (List.not_mem_nil)
      · rw [if_neg hro, List.mem_singleton] at hci
        subst hci
        rw [getElem!_pos lower (i - 1) hi1]
        refine ⟨clauseSat_one ?_, ?_⟩
        · rw [hlv (i - 1) hi1]
          have : ¬i - 1 + 1 ≤ C % 9 := by omega
          simp [this]
        · intro l hl
          rw [List.mem_singleton] at hl
          subst hl
          rw [Int.natAbs_neg]
          exact (hBl _ (lower.getElem_mem hi1)).2
  refine ⟨fun c hc ↦ (hmain c hc).1, ⟨?_, fun c hc l hl ↦ ?_⟩⟩
  · rw [mtoComparator_top]
    exact hw.1
  · rw [mtoComparator_top]
    exact (hmain c hc).2 l hl

/-- **Satisfiability of `mtoAtMost`** on 98 literals (the degree shape): with at most
`k` of the inputs true, the whole modulo-totalizer plus comparator is satisfiable by
fresh extension. -/
theorem mtoAtMost_sat (s : St) (xs : Array Int) (a : Nat → Bool) (k : Nat)
    (hn : xs.size = 98) (hk : 0 < k) (hk' : k < 98)
    (hw : WF s) (hs : SatAll a s)
    (hin : ∀ x ∈ xs, x ≠ 0 ∧ x.natAbs ≤ s.top)
    (hC : countT a xs ≤ k) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧ SatAll a' (mtoAtMost s xs k) ∧
      WF (mtoAtMost s xs k) ∧ s.top ≤ (mtoAtMost s xs k).top := by
  have hp : max (Nat.sqrt xs.size) 2 = 9 := by
    have h1 : 9 ≤ Nat.sqrt 98 := Nat.le_sqrt.mpr (by norm_num)
    have h2 : Nat.sqrt 98 < 10 := Nat.sqrt_lt.mpr (by norm_num)
    rw [hn]
    omega
  have e1 : mtoAtMost s xs k
      = mtoComparator (mtoMTO s xs 9).1 (mtoMTO s xs 9).2.1 (mtoMTO s xs 9).2.2 9 k := by
    unfold mtoAtMost
    rw [if_neg (by omega), if_neg (by omega), hp]
  rw [e1]
  obtain ⟨a1, hag1, hsat1, hw1, htop1, hunU, hunL, hBu, hBl, hszL⟩ :=
    mtoMTO_sat s xs a hw hs (by omega) hin
  obtain ⟨hsatC, hwC⟩ :=
    mtoComparator_sat (mtoMTO s xs 9).1 a1 (mtoMTO s xs 9).2.1 (mtoMTO s xs 9).2.2
      k (countT a xs) hsat1 hw1 hunU hunL hC hBu hBl hszL
  refine ⟨a1, hag1, hsatC, hwC, ?_⟩
  rw [mtoComparator_top]
  exact htop1

/-! ### Unconditional top-monotonicity of the mto family -/

theorem muaA_top' (s : St) (hs rs ff aa gg bb : Array Int) (p : Nat) :
    (muaA s hs rs ff aa gg bb p).top = s.top + 1 := by
  simp only [muaA, emitFold_top]
  split <;> simp [emitFold_top, push_top, fresh_fst_top]

theorem mtoPrepHalf_top_le (s : St) (xs : Array Int) (p : Nat) :
    s.top ≤ (mtoPrepHalf s xs p).1.top := by
  unfold mtoPrepHalf
  split
  · exact toTO_top_le s xs
  · rw [freshMany_top, freshMany_top]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem mtoNode_top_le : ∀ (fuel : Nat) (s : St) (il ul ll : Array Int) (p : Nat),
    s.top ≤ (mtoNode fuel s il ul ll p).top := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ _ ↦ le_refl _
  | succ fuel ih =>
    intro s il ul ll p
    set ni := il.size with hni
    set half := ni - ni / 2 with hhalf
    set fstA := il.extract 0 half with hfstA
    set sndA := il.extract half ni with hsndA
    set pf := mtoPrepHalf s fstA p with hpf
    set ps := mtoPrepHalf pf.1 sndA p with hps
    set s2 := muaA ps.1 ul ll pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 p with hs2
    set s3 := (if ps.2.2.2 = true then mtoNode fuel s2 sndA ps.2.1 ps.2.2.1 p else s2)
      with hs3
    set s4 := (if pf.2.2.2 = true then mtoNode fuel s3 fstA pf.2.1 pf.2.2.1 p else s3)
      with hs4
    have hbody : mtoNode (fuel + 1) s il ul ll p = s4 := rfl
    rw [hbody]
    have h1 : s.top ≤ pf.1.top := by
      rw [hpf]
      exact mtoPrepHalf_top_le s fstA p
    have h2 : pf.1.top ≤ ps.1.top := by
      rw [hps]
      exact mtoPrepHalf_top_le pf.1 sndA p
    have h3 : s2.top = ps.1.top + 1 := by
      rw [hs2]
      exact muaA_top' ps.1 ul ll pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 p
    have h4 : s2.top ≤ s3.top := by
      rw [hs3]
      split
      · exact ih s2 sndA ps.2.1 ps.2.2.1 p
      · exact le_refl _
    have h5 : s3.top ≤ s4.top := by
      rw [hs4]
      split
      · exact ih s3 fstA pf.2.1 pf.2.2.1 p
      · exact le_refl _
    omega

theorem mtoMTO_top_le (s : St) (xs : Array Int) (p : Nat) :
    s.top ≤ (mtoMTO s xs p).1.top := by
  unfold mtoMTO
  split
  · exact toTO_top_le s xs
  · refine le_trans ?_ (mtoNode_top_le xs.size _ xs _ _ p)
    rw [freshMany_top, freshMany_top]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem foldl_pushNeg_top (xs : Array Int) (s : St) :
    (xs.foldl (fun s v ↦ push s [-v]) s).top = s.top := by
  rw [← Array.foldl_toList]
  induction xs.toList generalizing s with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem mtoAtMost_top_le (s : St) (xs : Array Int) (k : Nat) :
    s.top ≤ (mtoAtMost s xs k).top := by
  by_cases h1 : k ≥ xs.size
  · have e : mtoAtMost s xs k = s := by
      unfold mtoAtMost
      rw [if_pos h1]
    rw [e]
  · by_cases h2 : k = 0
    · have e : mtoAtMost s xs k = xs.foldl (fun s v ↦ push s [-v]) s := by
        unfold mtoAtMost
        rw [if_neg h1, if_pos h2]
      rw [e, foldl_pushNeg_top]
    · have e : mtoAtMost s xs k
          = mtoComparator (mtoMTO s xs (max (Nat.sqrt xs.size) 2)).1
            (mtoMTO s xs (max (Nat.sqrt xs.size) 2)).2.1
            (mtoMTO s xs (max (Nat.sqrt xs.size) 2)).2.2
            (max (Nat.sqrt xs.size) 2) k := by
        unfold mtoAtMost
        rw [if_neg h1, if_neg h2]
      rw [e, mtoComparator_top]
      exact mtoMTO_top_le s xs _

end MtoSpec
end ConwayO7
