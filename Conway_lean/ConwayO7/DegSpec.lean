/-
`degreeStep u` emits `CardEnc.equals(lits_u, 14, mtotalizer)`: an at-least-14
constraint (the mtotalizer at-most-84 over the *negated* 98 literals) followed by the
at-most-14 mtotalizer over the literals themselves.  With the degree invariant
`DegInv` — every vertex's 98 orbit-literals have exactly 14 true — both directions
are instances of `mtoAtMost_sat`, and the whole degree section composes by
`GTrip.foldl_inv`.
-/
import ConwayO7.CnSpec
import ConwayO7.MtoSpec

namespace ConwayO7
namespace Encoder

open TotSpec MtoSpec

/-- The 98 orbit literals of vertex `u`, exactly as `degreeStep` builds them. -/
def degLits (u : Fin 99) : Array Int :=
  ((List.finRange 99).filterMap fun v ↦ if v ≠ u then some (evarI u v) else none).toArray

theorem degreeStep_eq (s : St) (u : Fin 99) :
    degreeStep s u = encEquals s (degLits u) 14 .mto := rfl

/-- Each vertex has 98 candidate neighbour literals. -/
theorem degLits_size : ∀ u : Fin 99, (degLits u).size = 98 := by native_decide

theorem degLits_bounds (u : Fin 99) :
    ∀ x ∈ degLits u, x ≠ 0 ∧ x.natAbs ≤ 693 := by
  intro x hx
  rw [degLits, List.mem_toArray, List.mem_filterMap] at hx
  obtain ⟨v, _, hv⟩ := hx
  by_cases hvu : v ≠ u
  · rw [if_pos hvu, Option.some_inj] at hv
    subst hv
    exact ⟨evarI_ne_zero u v, evarI_natAbs_le (fun h ↦ hvu h.symm)⟩
  · rw [if_neg hvu] at hv
    exact absurd hv (by simp)

/-- The degree invariant: every vertex's orbit literals have exactly 14 true —
supplied by the srg's 14-regularity through the orbit encoding. -/
def DegInv (a : Nat → Bool) : Prop := ∀ u : Fin 99, countT a (degLits u) = 14

theorem DegInv_congr {a b : Nat → Bool} (h : ∀ v ≤ 693, b v = a v) (hi : DegInv a) :
    DegInv b := fun u ↦ by
  rw [countT_congr h fun x hx ↦ (degLits_bounds u x hx).2]
  exact hi u

/-- The `equals 14` degree gadget, satisfiable from the exact count. -/
theorem encEqualsDeg_sat (s : St) (u : Fin 99) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s) (hcnt : countT a (degLits u) = 14) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧ SatAll a' (encEquals s (degLits u) 14 .mto) ∧
      WF (encEquals s (degLits u) 14 .mto) ∧
      s.top ≤ (encEquals s (degLits u) 14 .mto).top := by
  have hsz := degLits_size u
  have hb := degLits_bounds u
  have h693 := hw.1
  -- route the dispatch: at-least via the negated literals, then at-most
  have e1 : encAtLeast s (degLits u) 14 .mto
      = mtoAtMost s ((degLits u).map (-·)) ((degLits u).size - 14) := by
    unfold encAtLeast encAtMost
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by rw [Array.size_map]; omega), if_neg (by rw [Array.size_map, hsz]; omega),
      if_neg (by omega)]
  have e2 : ∀ t : St, encAtMost t (degLits u) 14 .mto = mtoAtMost t (degLits u) 14 := by
    intro t
    unfold encAtMost
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have eEq : encEquals s (degLits u) 14 .mto
      = mtoAtMost (mtoAtMost s ((degLits u).map (-·)) ((degLits u).size - 14))
        (degLits u) 14 := by
    unfold encEquals
    rw [e1, e2]
  rw [eEq]
  -- the negated-literal facts
  have hbn : ∀ x ∈ (degLits u).map (-·), x ≠ 0 ∧ x.natAbs ≤ s.top := by
    intro x hx
    rw [Array.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hb y hy
    refine ⟨by omega, ?_⟩
    rw [Int.natAbs_neg]
    omega
  have hcn : countT a ((degLits u).map (-·)) = 84 := by
    unfold countT
    rw [Array.toList_map,
      countP_neg_map a (degLits u).toList
        (fun x hx ↦ (hb x (by simpa using hx)).1)]
    have h1 : (degLits u).toList.length = 98 := by
      rw [Array.length_toList, hsz]
    unfold countT at hcnt
    omega
  -- at-least direction (at most 84 negated literals true)
  obtain ⟨a1, hag1, hsat1, hw1, htop1⟩ :=
    mtoAtMost_sat s ((degLits u).map (-·)) a ((degLits u).size - 14)
      (by rw [Array.size_map, hsz]) (by omega) (by omega)
      hw hs hbn (by rw [hcn, hsz])
  -- at-most direction
  have hcnt1 : countT a1 (degLits u) = 14 := by
    rw [← hcnt]
    exact countT_congr hag1 fun x hx ↦ le_trans (hb x hx).2 (by omega)
  obtain ⟨a2, hag2, hsat2, hw2, htop2⟩ :=
    mtoAtMost_sat (mtoAtMost s ((degLits u).map (-·)) ((degLits u).size - 14))
      (degLits u) a1 14 hsz (by omega) (by omega) hw1 hsat1
      (fun x hx ↦ ⟨(hb x hx).1, by have := (hb x hx).2; omega⟩)
      (by rw [hcnt1])
  exact ⟨a2, fun v hv ↦ (hag2 v (by omega)).trans (hag1 v hv), hsat2, hw2, by omega⟩

/-! ### Unconditional top-monotonicity of the dispatchers -/

theorem foldl_push_top' (xs : Array Int) (f : Int → List Int) (s : St) :
    (xs.foldl (fun s v ↦ push s (f v)) s).top = s.top := by
  rw [← Array.foldl_toList]
  induction xs.toList generalizing s with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem encAtMost_top_le (t : St) (xs : Array Int) (k : Nat) :
    t.top ≤ (encAtMost t xs k .mto).top := by
  by_cases h1 : k ≥ xs.size
  · have e : encAtMost t xs k .mto = t := by
      unfold encAtMost
      rw [if_pos h1]
    rw [e]
  · by_cases h2 : k = xs.size - 1
    · have e : encAtMost t xs k .mto = push t (xs.toList.map (-·)) := by
        unfold encAtMost
        rw [if_neg h1, if_pos h2]
      rw [e, push_top]
    · by_cases h3 : k = 0
      · have e : encAtMost t xs k .mto = xs.foldl (fun s l ↦ push s [-l]) t := by
          unfold encAtMost
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [e, foldl_push_top']
      · have e : encAtMost t xs k .mto = mtoAtMost t xs k := by
          unfold encAtMost
          rw [if_neg h1, if_neg h2, if_neg h3]
        rw [e]
        exact mtoAtMost_top_le t xs k

theorem encAtLeast_top_le (t : St) (xs : Array Int) (k : Nat) :
    t.top ≤ (encAtLeast t xs k .mto).top := by
  by_cases h1 : k = 0
  · have e : encAtLeast t xs k .mto = t := by
      unfold encAtLeast
      rw [if_pos h1]
    rw [e]
  · by_cases h2 : k = 1
    · have e : encAtLeast t xs k .mto = push t xs.toList := by
        unfold encAtLeast
        rw [if_neg h1, if_pos h2]
      rw [e, push_top]
    · by_cases h3 : k = xs.size
      · have e : encAtLeast t xs k .mto = xs.foldl (fun s l ↦ push s [l]) t := by
          unfold encAtLeast
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [e, foldl_push_top']
      · have e : encAtLeast t xs k .mto
            = encAtMost t (xs.map (-·)) (xs.size - k) .mto := by
          unfold encAtLeast
          rw [if_neg h1, if_neg h2, if_neg h3]
        rw [e]
        exact encAtMost_top_le t (xs.map (-·)) (xs.size - k)

/-- **The degree-gadget triple.** -/
theorem degreeStep_trip (u : Fin 99) :
    GTrip DegInv (fun s ↦ degreeStep s u) DegInv := by
  refine ⟨fun s ↦ ?_, fun s a hw hs hp ↦ ?_⟩
  · -- monotonicity
    rw [degreeStep_eq]
    show s.top ≤ (encAtMost (encAtLeast s (degLits u) 14 .mto) (degLits u) 14 .mto).top
    exact le_trans (encAtLeast_top_le s (degLits u) 14) (encAtMost_top_le _ _ _)
  · rw [degreeStep_eq]
    obtain ⟨a', hag, hsat', hw', htop'⟩ := encEqualsDeg_sat s u a hw hs (hp u)
    refine ⟨a', hag, hsat', hw', ?_⟩
    exact DegInv_congr (fun v hv ↦ hag v (by have := hw.1; omega)) hp

/-- **The whole degree section, as one triple.** -/
theorem deg_section_trip :
    GTrip DegInv (fun s ↦ (List.finRange 99).foldl degreeStep s) DegInv :=
  GTrip.foldl_inv _ fun u _ ↦ degreeStep_trip u

end Encoder
end ConwayO7
