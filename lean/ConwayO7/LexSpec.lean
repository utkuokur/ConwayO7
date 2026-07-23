/-
L5 — the lex-chain gadget triple.

`addLexLeq X Y` emits, at each position where `X` and `Y` differ structurally, an
implication clause guarded by the running `z`-register ("all earlier difference
positions agree") and the register's defining clauses.  The spec fold `lexStep`
re-expresses the imperative loop position-by-position (`lexFirst` at the first
difference, `lexNext` afterwards); its state equality with the emitted section is
discharged computationally at assembly time, exactly as for the CN section.

Semantically the chain is satisfiable precisely from `LexLeq`: the literal values
of `X` are lexicographically ≤ those of `Y`.  The `z`-witnesses are the running
equality flags (`ZInvP`).  The 101 constraints of the section are collected in
`LexInv`, the last conjunct of the encoding's invariant.
-/
import ConwayO7.SectionsCompose

namespace ConwayO7
namespace Encoder

open SeqSpec

/-! ### Small helpers -/

theorem litSat_natCast (a : Nat → Bool) (k : Nat) : litSat a ((k : Nat) : Int) = a k := by
  unfold litSat
  rw [if_neg (by omega), Int.natAbs_natCast]

theorem WF_push {s : St} (hw : WF s) {c : List Int}
    (hc : ∀ l ∈ c, l.natAbs ≤ s.top) : WF (push s c) := by
  refine ⟨hw.1, fun d hd ↦ ?_⟩
  rcases Array.mem_push.mp hd with hd | rfl
  · exact hw.2 d hd
  · exact hc

theorem WF_raise {s : St} (hw : WF s) {t : Nat} (ht : s.top ≤ t) : WF (⟨t, s.cls⟩ : St) :=
  ⟨le_trans hw.1 ht, fun c hc l hl ↦ le_trans (hw.2 c hc l hl) ht⟩

theorem satAll_retop {a : Nat → Bool} {s : St} (hs : SatAll a s) (t : Nat) :
    SatAll a (⟨t, s.cls⟩ : St) := fun c hc ↦ hs c hc

theorem bool_eq_false {b : Bool} (h : ¬b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-! ### The spec-level lex step -/

/-- First structural difference: unguarded implication plus the register's
definition. -/
def lexFirst (s : St) (x y : Int) : St × Option Int :=
  (push (push (push (push (⟨s.top + 1, (push s [-x, y]).cls⟩ : St)
      [-((s.top + 1 : Nat) : Int), -x, y])
      [-((s.top + 1 : Nat) : Int), x, -y])
      [-x, -y, ((s.top + 1 : Nat) : Int)])
      [x, y, ((s.top + 1 : Nat) : Int)],
   some ((s.top + 1 : Nat) : Int))

/-- Later difference: implication and register definition guarded by the previous
register. -/
def lexNext (s : St) (zp x y : Int) : St × Option Int :=
  (push (push (push (push (push (⟨s.top + 1, (push s [-zp, -x, y]).cls⟩ : St)
      [-((s.top + 1 : Nat) : Int), zp])
      [-((s.top + 1 : Nat) : Int), -x, y])
      [-((s.top + 1 : Nat) : Int), x, -y])
      [-zp, -x, -y, ((s.top + 1 : Nat) : Int)])
      [-zp, x, y, ((s.top + 1 : Nat) : Int)],
   some ((s.top + 1 : Nat) : Int))

/-- One position of the lex chain (skips structurally equal positions). -/
def lexStep (X Y : Array Int) (acc : St × Option Int) (i : Nat) : St × Option Int :=
  if X[i]! = Y[i]! then acc
  else
    match acc.2 with
    | none => lexFirst acc.1 X[i]! Y[i]!
    | some zp => lexNext acc.1 zp X[i]! Y[i]!

/-- The spec-level `add_lex_leq`. -/
def specAddLexLeq (s0 : St) (X Y : Array Int) : St :=
  ((List.range X.size).foldl (lexStep X Y) (s0, none)).1

/-! ### Semantics -/

/-- The literal values of `X` are lexicographically ≤ those of `Y`. -/
def LexLeq (a : Nat → Bool) (X Y : Array Int) : Prop :=
  ∀ i, i < X.size → (∀ j, j < i → litSat a X[j]! = litSat a Y[j]!) →
    litSat a X[i]! = true → litSat a Y[i]! = true

/-- The `z`-register invariant after `n` positions: absent while no structural
difference occurred, otherwise a fresh variable recording "all positions so far
agree". -/
def ZInvP (a : Nat → Bool) (X Y : Array Int) (n : Nat) (t : Nat) (oz : Option Int) :
    Prop :=
  match oz with
  | none => ∀ j, j < n → X[j]! = Y[j]!
  | some z => ∃ zn : Nat, z = ((zn : Nat) : Int) ∧ 693 < zn ∧ zn ≤ t ∧
      (a zn = true ↔ ∀ j, j < n → litSat a X[j]! = litSat a Y[j]!)

/-! ### The two emitters, satisfied -/

/-- `lexFirst`, satisfiable from the unguarded implication. -/
theorem lexFirst_sat (s : St) (x y : Int) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s)
    (hx0 : x ≠ 0) (hxb : x.natAbs ≤ 693) (hy0 : y ≠ 0) (hyb : y.natAbs ≤ 693)
    (himp : litSat a x = true → litSat a y = true) :
    ∃ a2, (∀ v ≤ s.top, a2 v = a v) ∧ SatAll a2 (lexFirst s x y).1 ∧
      WF (lexFirst s x y).1 ∧ (lexFirst s x y).1.top = s.top + 1 ∧
      (lexFirst s x y).2 = some ((s.top + 1 : Nat) : Int) ∧
      a2 (s.top + 1) = (litSat a x == litSat a y) := by
  have h693 := hw.1
  set a2 : Nat → Bool := fun v ↦ if v = s.top + 1 then litSat a x == litSat a y else a v
    with ha2
  have hself : a2 (s.top + 1) = (litSat a x == litSat a y) := by simp [ha2]
  have hag : ∀ v ≤ s.top, a2 v = a v := fun v hv ↦ ha2 ▸ if_neg (by omega)
  have hax : litSat a2 x = litSat a x := litSat_congr (hag _ (by omega))
  have hay : litSat a2 y = litSat a y := litSat_congr (hag _ (by omega))
  have hz0 : ((s.top + 1 : Nat) : Int) ≠ 0 := by omega
  have hzval : litSat a2 ((s.top + 1 : Nat) : Int) = (litSat a x == litSat a y) := by
    rw [litSat_natCast]
    exact hself
  have hnegz : litSat a2 (-((s.top + 1 : Nat) : Int)) = !(litSat a x == litSat a y) := by
    rw [litSat_neg a2 hz0, hzval]
  have hnx : litSat a x = false → litSat a2 (-x) = true := fun h ↦ by
    rw [litSat_neg a2 hx0, hax, h]; rfl
  have hny : litSat a y = false → litSat a2 (-y) = true := fun h ↦ by
    rw [litSat_neg a2 hy0, hay, h]; rfl
  refine ⟨a2, hag, ?_, ?_, rfl, rfl, hself⟩
  · -- satisfaction of every clause
    refine satAll_push (satAll_push (satAll_push (satAll_push
      (satAll_retop (satAll_push (satAll_of_agree hw hs hag) ?_) _) ?_) ?_) ?_) ?_
    · -- [-x, y]
      by_cases hx : litSat a x = true
      · exact clauseSat_two (Or.inr (by rw [hay]; exact himp hx))
      · exact clauseSat_two (Or.inl (hnx (bool_eq_false hx)))
    · -- [-z, -x, y]
      by_cases hzv : (litSat a x == litSat a y) = true
      · have heq : litSat a x = litSat a y := by simpa using hzv
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inr (by rw [hay, ← heq]; exact hx)))
        · exact clauseSat_three (Or.inr (Or.inl (hnx (bool_eq_false hx))))
      · exact clauseSat_three (Or.inl (by rw [hnegz, bool_eq_false hzv]; rfl))
    · -- [-z, x, -y]
      by_cases hzv : (litSat a x == litSat a y) = true
      · have heq : litSat a x = litSat a y := by simpa using hzv
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inl (by rw [hax]; exact hx)))
        · exact clauseSat_three (Or.inr (Or.inr (hny (heq ▸ bool_eq_false hx))))
      · exact clauseSat_three (Or.inl (by rw [hnegz, bool_eq_false hzv]; rfl))
    · -- [-x, -y, z]
      by_cases hzv : (litSat a x == litSat a y) = true
      · exact clauseSat_three (Or.inr (Or.inr (by rw [hzval]; exact hzv)))
      · have hne : ¬litSat a x = litSat a y := by simpa using hzv
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inl (hny (bool_eq_false fun h ↦ hne (hx.trans h.symm)))))
        · exact clauseSat_three (Or.inl (hnx (bool_eq_false hx)))
    · -- [x, y, z]
      by_cases hzv : (litSat a x == litSat a y) = true
      · exact clauseSat_three (Or.inr (Or.inr (by rw [hzval]; exact hzv)))
      · have hne : ¬litSat a x = litSat a y := by simpa using hzv
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inl (by rw [hax]; exact hx))
        · have hy : litSat a y = true := by
            by_contra h
            exact hne ((bool_eq_false hx).trans (bool_eq_false h).symm)
          exact clauseSat_three (Or.inr (Or.inl (by rw [hay]; exact hy)))
  · -- well-formedness
    refine WF_push (WF_push (WF_push (WF_push
      (WF_raise (WF_push hw ?_) (Nat.le_succ _)) ?_) ?_) ?_) ?_ <;>
      (try simp only [push_top]) <;> intro l hl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> omega

/-- `lexNext`, satisfiable from the guarded implication. -/
theorem lexNext_sat (s : St) (zpn : Nat) (x y : Int) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s)
    (hzp693 : 693 < zpn) (hzpTop : zpn ≤ s.top)
    (hx0 : x ≠ 0) (hxb : x.natAbs ≤ 693) (hy0 : y ≠ 0) (hyb : y.natAbs ≤ 693)
    (himp : a zpn = true → litSat a x = true → litSat a y = true) :
    ∃ a2, (∀ v ≤ s.top, a2 v = a v) ∧
      SatAll a2 (lexNext s ((zpn : Nat) : Int) x y).1 ∧
      WF (lexNext s ((zpn : Nat) : Int) x y).1 ∧
      (lexNext s ((zpn : Nat) : Int) x y).1.top = s.top + 1 ∧
      (lexNext s ((zpn : Nat) : Int) x y).2 = some ((s.top + 1 : Nat) : Int) ∧
      a2 (s.top + 1) = (a zpn && (litSat a x == litSat a y)) := by
  have h693 := hw.1
  set a2 : Nat → Bool := fun v ↦
    if v = s.top + 1 then a zpn && (litSat a x == litSat a y) else a v with ha2
  have hself : a2 (s.top + 1) = (a zpn && (litSat a x == litSat a y)) := by simp [ha2]
  have hag : ∀ v ≤ s.top, a2 v = a v := fun v hv ↦ ha2 ▸ if_neg (by omega)
  have hax : litSat a2 x = litSat a x := litSat_congr (hag _ (by omega))
  have hay : litSat a2 y = litSat a y := litSat_congr (hag _ (by omega))
  have hz0 : ((s.top + 1 : Nat) : Int) ≠ 0 := by omega
  have hzp0 : ((zpn : Nat) : Int) ≠ 0 := by omega
  have hzpval : litSat a2 ((zpn : Nat) : Int) = a zpn := by
    rw [litSat_natCast]
    exact hag _ hzpTop
  have hzval : litSat a2 ((s.top + 1 : Nat) : Int)
      = (a zpn && (litSat a x == litSat a y)) := by
    rw [litSat_natCast]
    exact hself
  have hnegzp : litSat a2 (-((zpn : Nat) : Int)) = !a zpn := by
    rw [litSat_neg a2 hzp0, hzpval]
  have hnegz : litSat a2 (-((s.top + 1 : Nat) : Int))
      = !(a zpn && (litSat a x == litSat a y)) := by
    rw [litSat_neg a2 hz0, hzval]
  have hnx : litSat a x = false → litSat a2 (-x) = true := fun h ↦ by
    rw [litSat_neg a2 hx0, hax, h]; rfl
  have hny : litSat a y = false → litSat a2 (-y) = true := fun h ↦ by
    rw [litSat_neg a2 hy0, hay, h]; rfl
  refine ⟨a2, hag, ?_, ?_, rfl, rfl, hself⟩
  · refine satAll_push (satAll_push (satAll_push (satAll_push (satAll_push
      (satAll_retop (satAll_push (satAll_of_agree hw hs hag) ?_) _) ?_) ?_) ?_) ?_) ?_
    · -- [-zp, -x, y]
      by_cases hzp : a zpn = true
      · by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inr (by rw [hay]; exact himp hzp hx)))
        · exact clauseSat_three (Or.inr (Or.inl (hnx (bool_eq_false hx))))
      · exact clauseSat_three (Or.inl (by rw [hnegzp, bool_eq_false hzp]; rfl))
    · -- [-z, zp]
      by_cases hzv : (a zpn && (litSat a x == litSat a y)) = true
      · exact clauseSat_two (Or.inr (by rw [hzpval]; exact (Bool.and_eq_true _ _ |>.mp hzv).1))
      · exact clauseSat_two (Or.inl (by rw [hnegz, bool_eq_false hzv]; rfl))
    · -- [-z, -x, y]
      by_cases hzv : (a zpn && (litSat a x == litSat a y)) = true
      · have heq : litSat a x = litSat a y := by simpa using (Bool.and_eq_true _ _ |>.mp hzv).2
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inr (by rw [hay, ← heq]; exact hx)))
        · exact clauseSat_three (Or.inr (Or.inl (hnx (bool_eq_false hx))))
      · exact clauseSat_three (Or.inl (by rw [hnegz, bool_eq_false hzv]; rfl))
    · -- [-z, x, -y]
      by_cases hzv : (a zpn && (litSat a x == litSat a y)) = true
      · have heq : litSat a x = litSat a y := by simpa using (Bool.and_eq_true _ _ |>.mp hzv).2
        by_cases hx : litSat a x = true
        · exact clauseSat_three (Or.inr (Or.inl (by rw [hax]; exact hx)))
        · exact clauseSat_three (Or.inr (Or.inr (hny (heq ▸ bool_eq_false hx))))
      · exact clauseSat_three (Or.inl (by rw [hnegz, bool_eq_false hzv]; rfl))
    · -- [-zp, -x, -y, z]
      by_cases hzp : a zpn = true
      · by_cases hx : litSat a x = true
        · by_cases hy : litSat a y = true
          · refine clauseSat_four (Or.inr (Or.inr (Or.inr ?_)))
            rw [hzval, hzp, hx, hy]
            rfl
          · exact clauseSat_four (Or.inr (Or.inr (Or.inl (hny (bool_eq_false hy)))))
        · exact clauseSat_four (Or.inr (Or.inl (hnx (bool_eq_false hx))))
      · exact clauseSat_four (Or.inl (by rw [hnegzp, bool_eq_false hzp]; rfl))
    · -- [-zp, x, y, z]
      by_cases hzp : a zpn = true
      · by_cases hzv : (a zpn && (litSat a x == litSat a y)) = true
        · exact clauseSat_four (Or.inr (Or.inr (Or.inr (by rw [hzval]; exact hzv))))
        · have hne : ¬litSat a x = litSat a y := by
            intro heq
            exact hzv (by rw [hzp, heq]; simp)
          by_cases hx : litSat a x = true
          · exact clauseSat_four (Or.inr (Or.inl (by rw [hax]; exact hx)))
          · have hy : litSat a y = true := by
              by_contra h
              exact hne ((bool_eq_false hx).trans (bool_eq_false h).symm)
            exact clauseSat_four (Or.inr (Or.inr (Or.inl (by rw [hay]; exact hy))))
      · exact clauseSat_four (Or.inl (by rw [hnegzp, bool_eq_false hzp]; rfl))
  · -- well-formedness
    refine WF_push (WF_push (WF_push (WF_push (WF_push
      (WF_raise (WF_push hw ?_) (Nat.le_succ _)) ?_) ?_) ?_) ?_) ?_ <;>
      (try simp only [push_top]) <;> intro l hl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> omega

/-! ### Top monotonicity -/

theorem lexStep_top_le (X Y : Array Int) (acc : St × Option Int) (i : Nat) :
    acc.1.top ≤ (lexStep X Y acc i).1.top := by
  unfold lexStep
  by_cases hxy : X[i]! = Y[i]!
  · rw [if_pos hxy]
  · rw [if_neg hxy]
    cases hoz : acc.2 with
    | none => exact Nat.le_succ _
    | some zp => exact Nat.le_succ _

theorem specAddLexLeq_top_le (s0 : St) (X Y : Array Int) :
    s0.top ≤ (specAddLexLeq s0 X Y).top := by
  unfold specAddLexLeq
  have h : ∀ (l : List Nat) (acc : St × Option Int),
      acc.1.top ≤ (l.foldl (lexStep X Y) acc).1.top := by
    intro l
    induction l with
    | nil => intro acc; exact le_refl _
    | cons i l ih => intro acc; exact le_trans (lexStep_top_le X Y acc i) (ih _)
  exact h (List.range X.size) (s0, none)

/-! ### One position, satisfied -/

theorem lexStep_sat (X Y : Array Int) (n : Nat) (hn : n < X.size)
    (hbn : X[n]! ≠ 0 ∧ X[n]!.natAbs ≤ 693 ∧ Y[n]! ≠ 0 ∧ Y[n]!.natAbs ≤ 693)
    (hbz : ∀ j, j < n → X[j]!.natAbs ≤ 693 ∧ Y[j]!.natAbs ≤ 693)
    (acc : St × Option Int) (a : Nat → Bool)
    (hw : WF acc.1) (hs : SatAll a acc.1)
    (hz : ZInvP a X Y n acc.1.top acc.2)
    (hlexn : (∀ j, j < n → litSat a X[j]! = litSat a Y[j]!) →
      litSat a X[n]! = true → litSat a Y[n]! = true) :
    ∃ a2, (∀ v ≤ acc.1.top, a2 v = a v) ∧
      SatAll a2 (lexStep X Y acc n).1 ∧ WF (lexStep X Y acc n).1 ∧
      acc.1.top ≤ (lexStep X Y acc n).1.top ∧
      ZInvP a2 X Y (n + 1) (lexStep X Y acc n).1.top (lexStep X Y acc n).2 := by
  obtain ⟨hx0, hxb, hy0, hyb⟩ := hbn
  by_cases hxy : X[n]! = Y[n]!
  · -- structurally equal: nothing emitted
    have e : lexStep X Y acc n = acc := by
      unfold lexStep
      rw [if_pos hxy]
    rw [e]
    refine ⟨a, fun _ _ ↦ rfl, hs, hw, le_refl _, ?_⟩
    obtain ⟨s, oz⟩ := acc
    cases oz with
    | none =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact hz j h
      · exact hxy
    | some z =>
      obtain ⟨zn, rfl, h1, h2, hiff⟩ := hz
      refine ⟨zn, rfl, h1, h2, hiff.trans ⟨fun h j hj ↦ ?_, fun h j hj ↦ h j (by omega)⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
      · exact h j h'
      · rw [hxy]
  · obtain ⟨s, oz⟩ := acc
    cases oz with
    | none =>
      have hstruct : ∀ j, j < n → X[j]! = Y[j]! := hz
      have e : lexStep X Y (s, none) n = lexFirst s X[n]! Y[n]! := by
        unfold lexStep
        rw [if_neg hxy]
      rw [e]
      obtain ⟨a2, hag, hsat, hw2, htop, hsnd, hval⟩ :=
        lexFirst_sat s X[n]! Y[n]! a hw hs hx0 hxb hy0 hyb
          (hlexn fun j hj ↦ by rw [hstruct j hj])
      refine ⟨a2, hag, hsat, hw2, by rw [htop]; exact Nat.le_succ s.top, ?_⟩
      rw [htop, hsnd]
      have htr : ∀ j, j < n + 1 → litSat a2 X[j]! = litSat a X[j]! ∧
          litSat a2 Y[j]! = litSat a Y[j]! := by
        intro j hj
        have hbj : X[j]!.natAbs ≤ 693 ∧ Y[j]!.natAbs ≤ 693 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
          · exact hbz j h
          · exact ⟨hxb, hyb⟩
        exact ⟨litSat_congr (hag _ (le_trans hbj.1 hw.1)),
          litSat_congr (hag _ (le_trans hbj.2 hw.1))⟩
      refine ⟨s.top + 1, rfl, by have h693 : (693 : Nat) ≤ s.top := hw.1; omega, le_refl _, ?_, ?_⟩
      · intro hv j hj
        rw [(htr j hj).1, (htr j hj).2]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · rw [hstruct j h]
        · rw [hval] at hv
          simpa using hv
      · intro hall
        rw [hval]
        have h' := hall n (by omega)
        rw [(htr n (by omega)).1, (htr n (by omega)).2] at h'
        simp [h']
    | some z =>
      obtain ⟨zpn, rfl, hzp1, hzp2, hiff⟩ := hz
      have e : lexStep X Y (s, some ((zpn : Nat) : Int)) n
          = lexNext s ((zpn : Nat) : Int) X[n]! Y[n]! := by
        unfold lexStep
        rw [if_neg hxy]
      rw [e]
      obtain ⟨a2, hag, hsat, hw2, htop, hsnd, hval⟩ :=
        lexNext_sat s zpn X[n]! Y[n]! a hw hs hzp1 hzp2 hx0 hxb hy0 hyb
          (fun hzp hx ↦ hlexn (hiff.mp hzp) hx)
      refine ⟨a2, hag, hsat, hw2, by rw [htop]; exact Nat.le_succ s.top, ?_⟩
      rw [htop, hsnd]
      have htr : ∀ j, j < n + 1 → litSat a2 X[j]! = litSat a X[j]! ∧
          litSat a2 Y[j]! = litSat a Y[j]! := by
        intro j hj
        have hbj : X[j]!.natAbs ≤ 693 ∧ Y[j]!.natAbs ≤ 693 := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
          · exact hbz j h
          · exact ⟨hxb, hyb⟩
        exact ⟨litSat_congr (hag _ (le_trans hbj.1 hw.1)),
          litSat_congr (hag _ (le_trans hbj.2 hw.1))⟩
      refine ⟨s.top + 1, rfl, by have h693 : (693 : Nat) ≤ s.top := hw.1; omega, le_refl _, ?_, ?_⟩
      · intro hv j hj
        rw [(htr j hj).1, (htr j hj).2]
        rw [hval, Bool.and_eq_true] at hv
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact hiff.mp hv.1 j h
        · simpa using hv.2
      · intro hall
        rw [hval]
        have hzp : a zpn = true := hiff.mpr fun j hj ↦ by
          have h' := hall j (by omega)
          rw [(htr j (by omega)).1, (htr j (by omega)).2] at h'
          exact h'
        have h' := hall n (by omega)
        rw [(htr n (by omega)).1, (htr n (by omega)).2] at h'
        rw [hzp]
        simp [h']

/-! ### The whole chain, satisfied -/

theorem lexFold_sat (X Y : Array Int)
    (hb : ∀ i, i < X.size →
      X[i]! ≠ 0 ∧ X[i]!.natAbs ≤ 693 ∧ Y[i]! ≠ 0 ∧ Y[i]!.natAbs ≤ 693)
    (s0 : St) (a : Nat → Bool) (hw : WF s0) (hs : SatAll a s0) (hlex : LexLeq a X Y)
    (n : Nat) (hn : n ≤ X.size) :
    ∃ a1, (∀ v ≤ s0.top, a1 v = a v) ∧
      SatAll a1 ((List.range n).foldl (lexStep X Y) (s0, none)).1 ∧
      WF ((List.range n).foldl (lexStep X Y) (s0, none)).1 ∧
      s0.top ≤ ((List.range n).foldl (lexStep X Y) (s0, none)).1.top ∧
      ZInvP a1 X Y n ((List.range n).foldl (lexStep X Y) (s0, none)).1.top
        ((List.range n).foldl (lexStep X Y) (s0, none)).2 := by
  induction n with
  | zero =>
    exact ⟨a, fun _ _ ↦ rfl, hs, hw, le_refl _, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨a1, hag1, hs1, hw1, htop1, hz1⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have htr : ∀ j, j < X.size →
        litSat a1 X[j]! = litSat a X[j]! ∧ litSat a1 Y[j]! = litSat a Y[j]! := by
      intro j hj
      obtain ⟨_, hxb, _, hyb⟩ := hb j hj
      exact ⟨litSat_congr (hag1 _ (le_trans hxb hw.1)),
        litSat_congr (hag1 _ (le_trans hyb hw.1))⟩
    have hlexn : (∀ j, j < n → litSat a1 X[j]! = litSat a1 Y[j]!) →
        litSat a1 X[n]! = true → litSat a1 Y[n]! = true := by
      intro hpre hx
      rw [(htr n (by omega)).2]
      refine hlex n (by omega) (fun j hj ↦ ?_)
        (by rw [← (htr n (by omega)).1]; exact hx)
      have h' := hpre j hj
      rw [(htr j (by omega)).1, (htr j (by omega)).2] at h'
      exact h'
    obtain ⟨a2, hag2, hs2, hw2, htop2, hz2⟩ :=
      lexStep_sat X Y n (by omega)
        ⟨(hb n (by omega)).1, (hb n (by omega)).2.1,
          (hb n (by omega)).2.2.1, (hb n (by omega)).2.2.2⟩
        (fun j hj ↦ ⟨(hb j (by omega)).2.1, (hb j (by omega)).2.2.2⟩)
        _ a1 hw1 hs1 hz1 hlexn
    exact ⟨a2, fun v hv ↦ (hag2 v (le_trans hv htop1)).trans (hag1 v hv), hs2, hw2,
      le_trans htop1 htop2, hz2⟩

theorem specAddLexLeq_sat (X Y : Array Int)
    (hb : ∀ i, i < X.size →
      X[i]! ≠ 0 ∧ X[i]!.natAbs ≤ 693 ∧ Y[i]! ≠ 0 ∧ Y[i]!.natAbs ≤ 693)
    (s0 : St) (a : Nat → Bool) (hw : WF s0) (hs : SatAll a s0) (hlex : LexLeq a X Y) :
    ∃ a1, (∀ v ≤ s0.top, a1 v = a v) ∧ SatAll a1 (specAddLexLeq s0 X Y) ∧
      WF (specAddLexLeq s0 X Y) := by
  obtain ⟨a1, hag, hs1, hw1, _, _⟩ :=
    lexFold_sat X Y hb s0 a hw hs hlex X.size (le_refl _)
  exact ⟨a1, hag, hs1, hw1⟩

/-! ### The lex section -/

/-- The identity word: orbit variables in position order. -/
def lexXA : Array Int := .ofFn (n := 693) fun o ↦ ((o.val + 1 : Nat) : Int)

/-- The permuted word. -/
def lexYA (perm : Nat → Nat) : Array Int :=
  .ofFn (n := 693) fun o ↦ ((perm o.val + 1 : Nat) : Int)

/-- The spec-level `E ≤ E ∘ perm` constraint. -/
def specLexAgainst (s : St) (perm : Nat → Nat) : St := specAddLexLeq s lexXA (lexYA perm)

theorem lexXA_size : lexXA.size = 693 := by
  rw [lexXA, Array.size_ofFn]

theorem lexXA_get (i : Nat) (hi : i < 693) : lexXA[i]! = ((i + 1 : Nat) : Int) := by
  rw [lexXA, getElem!_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]

theorem lexYA_get (perm : Nat → Nat) (i : Nat) (hi : i < 693) :
    (lexYA perm)[i]! = ((perm i + 1 : Nat) : Int) := by
  rw [lexYA, getElem!_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]

/-- The generator images stay inside the orbit block (computed). -/
theorem lexPerms_length : lexPerms.length = 101 := by native_decide

theorem lexPerms_bound :
    ∀ k : Fin 101, ∀ o : Fin 693, orbitPerm (lexPerms[(k : Nat)]!) o.val < 693 := by
  native_decide

theorem orbitPerm_lt_of_mem {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) :
    ∀ o, o < 693 → orbitPerm ρ o < 693 := by
  intro o ho
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hρ
  have hk101 : k < 101 := lexPerms_length ▸ hk
  have h : orbitPerm (lexPerms[k]!) o < 693 := lexPerms_bound ⟨k, hk101⟩ ⟨o, ho⟩
  rw [getElem!_pos lexPerms k hk, hget] at h
  exact h

theorem lex_bounds {perm : Nat → Nat} (hp : ∀ o, o < 693 → perm o < 693) :
    ∀ i, i < lexXA.size →
      lexXA[i]! ≠ 0 ∧ lexXA[i]!.natAbs ≤ 693 ∧
      (lexYA perm)[i]! ≠ 0 ∧ (lexYA perm)[i]!.natAbs ≤ 693 := by
  intro i hi
  have hi' : i < 693 := by rw [lexXA_size] at hi; exact hi
  rw [lexXA_get i hi', lexYA_get perm i hi']
  have := hp i hi'
  refine ⟨by omega, ?_, by omega, ?_⟩
  · rw [Int.natAbs_natCast]; omega
  · rw [Int.natAbs_natCast]; omega

/-- The lex-leader invariant: the orbit word is ≤ its image under each of the 101
generator relabelings. -/
def LexInv (a : Nat → Bool) : Prop :=
  ∀ ρ ∈ lexPerms, LexLeq a lexXA (lexYA (orbitPerm ρ))

theorem LexInv_congr {a b : Nat → Bool} (h : ∀ v ≤ 693, b v = a v) (hi : LexInv a) :
    LexInv b := by
  intro ρ hρ
  have hbd := lex_bounds (orbitPerm_lt_of_mem hρ)
  intro i hi' hpre hx
  have htr : ∀ j, j < lexXA.size → litSat b lexXA[j]! = litSat a lexXA[j]! ∧
      litSat b (lexYA (orbitPerm ρ))[j]! = litSat a (lexYA (orbitPerm ρ))[j]! := by
    intro j hj
    obtain ⟨_, hxb, _, hyb⟩ := hbd j hj
    exact ⟨litSat_congr (h _ hxb), litSat_congr (h _ hyb)⟩
  rw [(htr i hi').2]
  refine hi ρ hρ i hi' (fun j hj ↦ ?_) (by rw [← (htr i hi').1]; exact hx)
  have h' := hpre j hj
  rw [(htr j (by omega)).1, (htr j (by omega)).2] at h'
  exact h'

/- Downstream files must treat the chain and its words as opaque: unfolding them
would make the elaborator evaluate the concrete 693-position fold. -/
attribute [irreducible] specAddLexLeq lexXA lexYA

end Encoder
end ConwayO7
