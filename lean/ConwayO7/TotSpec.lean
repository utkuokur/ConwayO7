/-
L4 gadget mathematics — satisfiability of the totalizer (`to_UA` / `to_TO`).

The witness semantics is unary counting: output register `i` of a node holds
"at least `i + 1` of the node's input literals are true" (`UnaryOut`).  `toUA_sat`
shows the merge clauses hold whenever parent and children all carry unary counts
(counts add across the two halves); `toTONode_sat` runs the tree recursion, assigning
each internal node's fresh registers (which `freshMany` allocates in closed form) by
`extendUnary`; `toTO_sat` packages the wrapper, with sub-2-input blocks handled by
`unaryOut_self` (a literal is its own unary counter).

These are the leaf blocks of the modulo-totalizer degree encoding; the modulo layer
(`muaA`, comparator) builds on the same `UnaryOut` interface.
-/
import ConwayO7.SeqSpec

namespace ConwayO7
namespace TotSpec

open Encoder

/-! ### Unary-count semantics -/

/-- Number of true literals of an array under `a`. -/
def countT (a : Nat → Bool) (ls : Array Int) : Nat := ls.toList.countP (litSat a)

/-- `outs` carries the unary count of `ins` under `a`. -/
def UnaryOut (a : Nat → Bool) (outs ins : Array Int) : Prop :=
  outs.size = ins.size ∧
    ∀ i, (h : i < outs.size) → litSat a outs[i] = decide (i + 1 ≤ countT a ins)

theorem countT_congr {a a' : Nat → Bool} {ls : Array Int} {t : Nat}
    (hag : ∀ v ≤ t, a' v = a v) (hb : ∀ l ∈ ls, l.natAbs ≤ t) :
    countT a' ls = countT a ls :=
  List.countP_congr fun l hl ↦ by
    rw [litSat_congr (hag l.natAbs (hb l (by simpa using hl)))]

theorem unaryOut_congr {a a' : Nat → Bool} {outs ins : Array Int} {t : Nat}
    (hag : ∀ v ≤ t, a' v = a v) (houts : ∀ l ∈ outs, l.natAbs ≤ t)
    (hins : ∀ l ∈ ins, l.natAbs ≤ t) (h : UnaryOut a outs ins) :
    UnaryOut a' outs ins := by
  refine ⟨h.1, fun i hi ↦ ?_⟩
  rw [litSat_congr (hag outs[i].natAbs (houts _ (outs.getElem_mem hi))),
    countT_congr hag hins, h.2 i hi]

/-- A block of fewer than two literals is its own unary counter. -/
theorem unaryOut_self {a : Nat → Bool} {xs : Array Int} (h : xs.size ≤ 1) :
    UnaryOut a xs xs := by
  refine ⟨rfl, fun i hi ↦ ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  have hx : xs.toList = [xs[0]] := by
    apply List.ext_getElem
    · rw [Array.length_toList]
      simp
      omega
    · intro i h1 h2
      have hi0 : i = 0 := by simp at h2; omega
      subst hi0
      simp
  unfold countT
  rw [hx]
  rw [List.countP_cons, List.countP_nil]
  cases hv : litSat a xs[0] <;> simp

/-! ### The merge clauses -/

/-- **Satisfiability of `to_UA`**: if the parent and both children registers carry
unary counts and the total count splits across the halves, every merge clause holds
(no fresh variables are involved). -/
theorem toUA_sat {a : Nat → Bool} {s : St} (hs : SatAll a s)
    {outl al bl fstIn sndIn : Array Int}
    (hal : UnaryOut a al fstIn) (hbl : UnaryOut a bl sndIn)
    {tot : Array Int} (houtl : UnaryOut a outl tot)
    (hcnt : countT a tot = countT a fstIn + countT a sndIn)
    (hsz : outl.size = al.size + bl.size)
    (hne : ∀ l ∈ al, l ≠ 0) (hne' : ∀ l ∈ bl, l ≠ 0) :
    SatAll a (toUA s outl al bl) := by
  intro c hc
  unfold toUA at hc
  rw [emitFold_cls, emitFold_cls, emitFold_cls] at hc
  rcases Array.mem_append.mp hc with hc | hc3
  · rcases Array.mem_append.mp hc with hc | hc2
    · rcases Array.mem_append.mp hc with hc | hc1
      · -- previously emitted clauses
        exact hs c hc
      · -- [-bl[j], outl[j]]
        rw [List.mem_toArray] at hc1
        obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.mp hc1
        rw [List.mem_range] at hj
        rw [List.mem_singleton] at hcj
        subst hcj
        rw [getElem!_pos bl j hj, getElem!_pos outl j (by omega)]
        refine SeqSpec.clauseSat_two ?_
        by_cases hjb : litSat a bl[j] = true
        · right
          rw [houtl.2 j (by omega)]
          have h2 := (hbl.2 j hj).symm.trans hjb
          simp only [decide_eq_true_eq] at h2 ⊢
          omega
        · left
          rw [litSat_neg a (hne' _ (bl.getElem_mem hj))]
          simpa using hjb
    · -- [-al[i], outl[i]]
      rw [List.mem_toArray] at hc2
      obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc2
      rw [List.mem_range] at hi
      rw [List.mem_singleton] at hci
      subst hci
      rw [getElem!_pos al i hi, getElem!_pos outl i (by omega)]
      refine SeqSpec.clauseSat_two ?_
      by_cases hia : litSat a al[i] = true
      · right
        rw [houtl.2 i (by omega)]
        have h1 := (hal.2 i hi).symm.trans hia
        simp only [decide_eq_true_eq] at h1 ⊢
        omega
      · left
        rw [litSat_neg a (hne _ (al.getElem_mem hi))]
        simpa using hia
  · -- ternary merge clauses
    rw [List.mem_toArray] at hc3
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc3
    rw [List.mem_range] at hi
    obtain ⟨j, hj, hcj⟩ := List.mem_map.mp hci
    rw [List.mem_range] at hj
    subst hcj
    rw [getElem!_pos al i hi, getElem!_pos bl j hj, getElem!_pos outl _ (by omega)]
    refine SeqSpec.clauseSat_three ?_
    by_cases hia : litSat a al[i] = true
    · by_cases hjb : litSat a bl[j] = true
      · right; right
        rw [houtl.2 (i + j + 1) (by omega)]
        have h1 := (hal.2 i hi).symm.trans hia
        have h2 := (hbl.2 j hj).symm.trans hjb
        simp only [decide_eq_true_eq] at h1 h2 ⊢
        omega
      · right; left
        rw [litSat_neg a (hne' _ (bl.getElem_mem hj))]
        simpa using hjb
    · left
      rw [litSat_neg a (hne _ (al.getElem_mem hi))]
      simpa using hia

/-! ### Fresh registers and the extension witness -/

theorem freshMany_top (s : St) (n : Nat) : (freshMany s n).1.top = s.top + n := rfl

theorem freshMany_cls (s : St) (n : Nat) : (freshMany s n).1.cls = s.cls := rfl

theorem freshMany_size (s : St) (n : Nat) : (freshMany s n).2.size = n := by
  simp [freshMany]

theorem freshMany_get (s : St) (n i : Nat) (h : i < n) :
    (freshMany s n).2[i]'(by rw [freshMany_size]; exact h)
      = ((s.top + 1 + i : Nat) : Int) := by
  simp [freshMany]

theorem freshMany_mem (s : St) (n : Nat) :
    ∀ l ∈ (freshMany s n).2, 0 < l ∧ s.top < l.natAbs ∧ l.natAbs ≤ s.top + n := by
  intro l hl
  simp only [freshMany, Array.mem_map] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  rw [Array.mem_range] at hi
  refine ⟨by exact_mod_cast (show 0 < s.top + 1 + i by omega), ?_, ?_⟩ <;>
    rw [Int.natAbs_natCast] <;> omega

/-- Extend an assignment with unary-count values on the register block
`(base, base + m]`. -/
def extendUnary (a : Nat → Bool) (base m : Nat) (ins : Array Int) : Nat → Bool :=
  fun v ↦ if base < v ∧ v ≤ base + m then decide (v - base ≤ countT a ins) else a v

theorem extendUnary_agree (a : Nat → Bool) (base m : Nat) (ins : Array Int) :
    ∀ v ≤ base, extendUnary a base m ins v = a v := fun v hv ↦
  if_neg (by omega)

/-- The freshly allocated registers carry the unary count under the extension. -/
theorem unaryOut_extend (a : Nat → Bool) (s : St) (ins : Array Int)
    (hins : ∀ l ∈ ins, l.natAbs ≤ s.top) :
    UnaryOut (extendUnary a s.top ins.size ins) (freshMany s ins.size).2 ins := by
  set a' := extendUnary a s.top ins.size ins with ha'
  have hcnt : countT a' ins = countT a ins :=
    countT_congr (extendUnary_agree a s.top ins.size ins) hins
  refine ⟨freshMany_size s ins.size, fun i hi ↦ ?_⟩
  rw [freshMany_size] at hi
  rw [freshMany_get s ins.size i hi]
  have hval : a' (s.top + 1 + i) = decide (i + 1 ≤ countT a ins) := by
    rw [ha']
    show (if s.top < s.top + 1 + i ∧ s.top + 1 + i ≤ s.top + ins.size then
        decide (s.top + 1 + i - s.top ≤ countT a ins) else a (s.top + 1 + i)) = _
    rw [if_pos ⟨by omega, by omega⟩,
      show s.top + 1 + i - s.top = i + 1 from by omega]
  unfold litSat
  rw [if_neg (by omega : ¬((s.top + 1 + i : Nat) : Int) < 0), Int.natAbs_natCast,
    hval, hcnt]

/-- `unaryOut_extend` with the register count given as a separate equation. -/
theorem unaryOut_extend' (a : Nat → Bool) (s : St) (m : Nat) (ins : Array Int)
    (hm : ins.size = m) (hins : ∀ l ∈ ins, l.natAbs ≤ s.top) :
    UnaryOut (extendUnary a s.top m ins) (freshMany s m).2 ins := by
  subst hm
  exact unaryOut_extend a s ins hins

/-! ### Splitting counts across the two halves -/

theorem mem_of_mem_extract {xs : Array Int} {b e : Nat} {l : Int}
    (h : l ∈ xs.extract b e) : l ∈ xs := by
  rw [Array.mem_def, Array.toList_extract, List.extract_eq_take_drop] at h
  rw [Array.mem_def]
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem countT_extract_split (a : Nat → Bool) (xs : Array Int) (h : Nat)
    :
    countT a xs = countT a (xs.extract 0 h) + countT a (xs.extract h xs.size) := by
  unfold countT
  rw [← List.countP_append]
  congr 1
  rw [Array.toList_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.extract_eq_take_drop]
  simp only [List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (l := xs.toList.drop h) (i := xs.size - h)
    (by rw [List.length_drop, Array.length_toList])]
  exact (List.take_append_drop h xs.toList).symm

/-! ### `toUA` bookkeeping -/

theorem toUA_top (s : St) (outl al bl : Array Int) : (toUA s outl al bl).top = s.top := by
  unfold toUA
  rw [emitFold_top, emitFold_top, emitFold_top]

theorem toUA_wf {s : St} (hw : WF s) {outl al bl : Array Int}
    (houtl : ∀ l ∈ outl, l.natAbs ≤ s.top)
    (hal : ∀ l ∈ al, l.natAbs ≤ s.top) (hbl : ∀ l ∈ bl, l.natAbs ≤ s.top)
    (hsz : outl.size = al.size + bl.size) :
    WF (toUA s outl al bl) := by
  refine ⟨by rw [toUA_top]; exact hw.1, ?_⟩
  intro c hc l hl
  rw [toUA_top]
  unfold toUA at hc
  rw [emitFold_cls, emitFold_cls, emitFold_cls] at hc
  have hout : ∀ i, (h : i < outl.size) → outl[i].natAbs ≤ s.top :=
    fun i h ↦ houtl _ (outl.getElem_mem h)
  rcases Array.mem_append.mp hc with hc | hc3
  · rcases Array.mem_append.mp hc with hc | hc2
    · rcases Array.mem_append.mp hc with hc | hc1
      · exact hw.2 c hc l hl
      · rw [List.mem_toArray] at hc1
        obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.mp hc1
        rw [List.mem_range] at hj
        rw [List.mem_singleton] at hcj
        subst hcj
        rw [getElem!_pos bl j hj, getElem!_pos outl j (by omega)] at hl
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [Int.natAbs_neg]
          exact hbl _ (bl.getElem_mem hj)
        · rw [List.mem_singleton] at hl
          subst hl
          exact hout j (by omega)
    · rw [List.mem_toArray] at hc2
      obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc2
      rw [List.mem_range] at hi
      rw [List.mem_singleton] at hci
      subst hci
      rw [getElem!_pos al i hi, getElem!_pos outl i (by omega)] at hl
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]
        exact hal _ (al.getElem_mem hi)
      · rw [List.mem_singleton] at hl
        subst hl
        exact hout i (by omega)
  · rw [List.mem_toArray] at hc3
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc3
    rw [List.mem_range] at hi
    obtain ⟨j, hj, hcj⟩ := List.mem_map.mp hci
    rw [List.mem_range] at hj
    subst hcj
    rw [getElem!_pos al i hi, getElem!_pos bl j hj,
      getElem!_pos outl _ (by omega)] at hl
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [Int.natAbs_neg]
      exact hal _ (al.getElem_mem hi)
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [Int.natAbs_neg]
      exact hbl _ (bl.getElem_mem hj)
    · rw [List.mem_singleton] at hl
      subst hl
      exact hout (i + j + 1) (by omega)

/-! ### The totalizer tree -/

/-- **Satisfiability of the totalizer tree**: if the parent registers already carry
the unary count of the inputs, all internal clauses can be satisfied by assigning the
(fresh) child registers their unary counts, recursively. -/
theorem toTONode_sat :
    ∀ (fuel : Nat) (ilst olst : Array Int) (s : St) (a : Nat → Bool),
      ilst.size ≤ fuel → 2 ≤ ilst.size →
      WF s → SatAll a s →
      (∀ l ∈ ilst, l ≠ 0 ∧ l.natAbs ≤ s.top) →
      (∀ l ∈ olst, l ≠ 0 ∧ l.natAbs ≤ s.top) →
      olst.size = ilst.size →
      UnaryOut a olst ilst →
      ∃ a', (∀ v ≤ s.top, a' v = a v) ∧
        SatAll a' (toTONode fuel s ilst olst) ∧
        WF (toTONode fuel s ilst olst) ∧
        s.top ≤ (toTONode fuel s ilst olst).top := by
  intro fuel
  induction fuel with
  | zero =>
    intro ilst olst s a hf h2 _ _ _ _ _ _
    exact absurd hf (by omega)
  | succ fuel ih =>
    intro ilst olst s a hf h2 hw hs hin hout hsz hun
    set n := ilst.size with hn
    set half := n - n / 2 with hhalf
    set fstA := ilst.extract 0 half with hfstA
    set sndA := ilst.extract half n with hsndA
    set sf := (if 2 ≤ half then freshMany s half else (s, fstA)) with hsf
    set ss := (if 2 ≤ n - half then freshMany sf.1 (n - half) else (sf.1, sndA)) with hss
    set s2 := toUA ss.1 olst sf.2 ss.2 with hs2
    set s3 := (if 2 ≤ n - half then toTONode fuel s2 sndA ss.2 else s2) with hs3
    set s4 := (if 2 ≤ half then toTONode fuel s3 fstA sf.2 else s3) with hs4
    have hbody : toTONode (fuel + 1) s ilst olst = s4 := rfl
    rw [hbody]
    -- arithmetic on the split
    have hn2 : 2 ≤ n := h2
    have hhalf1 : 1 ≤ half := by omega
    have hsplit_le : half ≤ n := by omega
    have hf_sz : fstA.size = half := by
      rw [hfstA, Array.size_extract]
      omega
    have hs_sz : sndA.size = n - half := by
      rw [hsndA, Array.size_extract]
      omega
    have hin_f : ∀ l ∈ fstA, l ≠ 0 ∧ l.natAbs ≤ s.top := by
      intro l hl
      rw [hfstA] at hl
      exact hin l (mem_of_mem_extract hl)
    have hin_s : ∀ l ∈ sndA, l ≠ 0 ∧ l.natAbs ≤ s.top := by
      intro l hl
      rw [hsndA] at hl
      exact hin l (mem_of_mem_extract hl)
    -- stage 1: first-half registers
    have step1 : ∃ a1 : Nat → Bool,
        (∀ v ≤ s.top, a1 v = a v) ∧
        sf.1.cls = s.cls ∧ s.top ≤ sf.1.top ∧
        UnaryOut a1 sf.2 fstA ∧
        (∀ l ∈ sf.2, l ≠ 0 ∧ l.natAbs ≤ sf.1.top) ∧
        sf.2.size = fstA.size := by
      by_cases hbf : 2 ≤ half
      · rw [hsf, if_pos hbf]
        refine ⟨extendUnary a s.top half fstA,
          extendUnary_agree a s.top half fstA, rfl, by rw [freshMany_top]; omega, ?_, ?_, ?_⟩
        · exact unaryOut_extend' a s half fstA hf_sz (fun l hl ↦ (hin_f l hl).2)
        · intro l hl
          have := freshMany_mem s half l hl
          rw [freshMany_top]
          exact ⟨by omega, by omega⟩
        · rw [freshMany_size, hf_sz]
      · rw [hsf, if_neg hbf]
        exact ⟨a, fun _ _ ↦ rfl, rfl, le_refl _,
          unaryOut_self (xs := fstA) (by omega),
          fun l hl ↦ ⟨(hin_f l hl).1, (hin_f l hl).2⟩, rfl⟩
    obtain ⟨a1, hag1, hcls1, htop1, hun1, hbnd1, hsz1⟩ := step1
    -- stage 2: second-half registers
    have step2 : ∃ a2 : Nat → Bool,
        (∀ v ≤ sf.1.top, a2 v = a1 v) ∧
        ss.1.cls = s.cls ∧ sf.1.top ≤ ss.1.top ∧
        UnaryOut a2 ss.2 sndA ∧
        (∀ l ∈ ss.2, l ≠ 0 ∧ l.natAbs ≤ ss.1.top) ∧
        ss.2.size = sndA.size := by
      by_cases hbs : 2 ≤ n - half
      · rw [hss, if_pos hbs]
        refine ⟨extendUnary a1 sf.1.top (n - half) sndA,
          extendUnary_agree a1 sf.1.top (n - half) sndA, hcls1,
          by rw [freshMany_top]; omega, ?_, ?_, ?_⟩
        · exact unaryOut_extend' a1 sf.1 (n - half) sndA hs_sz
            (fun l hl ↦ le_trans (hin_s l hl).2 htop1)
        · intro l hl
          have := freshMany_mem sf.1 (n - half) l hl
          rw [freshMany_top]
          exact ⟨by omega, by omega⟩
        · rw [freshMany_size, hs_sz]
      · rw [hss, if_neg hbs]
        exact ⟨a1, fun _ _ ↦ rfl, hcls1, le_refl _,
          unaryOut_self (xs := sndA) (by omega),
          fun l hl ↦ ⟨(hin_s l hl).1, le_trans (hin_s l hl).2 htop1⟩, rfl⟩
    obtain ⟨a2, hag2, hcls2, htop2, hun2, hbnd2, hsz2⟩ := step2
    have hag2a : ∀ v ≤ s.top, a2 v = a v := fun v hv ↦
      (hag2 v (le_trans hv htop1)).trans (hag1 v hv)
    -- the parent's merge clauses
    have hw2' : WF ss.1 := by
      refine ⟨le_trans hw.1 (le_trans htop1 htop2), ?_⟩
      intro c hc l hl
      rw [hcls2] at hc
      exact le_trans (hw.2 c hc l hl) (le_trans htop1 htop2)
    have hsat_ss : SatAll a2 ss.1 := fun c hc ↦ by
      rw [hcls2] at hc
      exact satAll_of_agree hw hs hag2a c hc
    have hun1' : UnaryOut a2 sf.2 fstA :=
      unaryOut_congr hag2 (fun l hl ↦ (hbnd1 l hl).2)
        (fun l hl ↦ le_trans (hin_f l hl).2 htop1) hun1
    have hunP : UnaryOut a2 olst ilst :=
      unaryOut_congr hag2a (fun l hl ↦ (hout l hl).2) (fun l hl ↦ (hin l hl).2) hun
    have hcnt2 : countT a2 ilst = countT a2 fstA + countT a2 sndA := by
      have := countT_extract_split a2 ilst half
      rw [← hn, ← hfstA, ← hsndA] at this
      exact this
    have hsat2 : SatAll a2 s2 := by
      rw [hs2]
      exact toUA_sat hsat_ss hun1' hun2 hunP hcnt2
        (by rw [hsz, hsz1, hsz2, hf_sz, hs_sz]; omega)
        (fun l hl ↦ (hbnd1 l hl).1) (fun l hl ↦ (hbnd2 l hl).1)
    have hw2 : WF s2 := by
      rw [hs2]
      exact toUA_wf hw2'
        (fun l hl ↦ le_trans (hout l hl).2 (le_trans htop1 htop2))
        (fun l hl ↦ le_trans (hbnd1 l hl).2 htop2)
        (fun l hl ↦ (hbnd2 l hl).2)
        (by rw [hsz, hsz1, hsz2, hf_sz, hs_sz]; omega)
    have hs2top : s2.top = ss.1.top := by
      rw [hs2]
      exact toUA_top ss.1 olst sf.2 ss.2
    -- stage 3: recurse into the second half
    have step3 : ∃ a3 : Nat → Bool,
        (∀ v ≤ s2.top, a3 v = a2 v) ∧ SatAll a3 s3 ∧ WF s3 ∧ s2.top ≤ s3.top := by
      by_cases hbs : 2 ≤ n - half
      · rw [hs3, if_pos hbs]
        exact ih sndA ss.2 s2 a2
          (by omega) (by omega : 2 ≤ sndA.size)
          hw2 hsat2
          (fun l hl ↦ ⟨(hin_s l hl).1,
            le_trans (hin_s l hl).2 (by omega)⟩)
          (fun l hl ↦ ⟨(hbnd2 l hl).1, by have := (hbnd2 l hl).2; omega⟩)
          (by omega) hun2
      · rw [hs3, if_neg hbs]
        exact ⟨a2, fun _ _ ↦ rfl, hsat2, hw2, le_refl _⟩
    obtain ⟨a3, hag3, hsat3, hw3, htop3⟩ := step3
    -- stage 4: recurse into the first half
    have step4 : ∃ a4 : Nat → Bool,
        (∀ v ≤ s3.top, a4 v = a3 v) ∧ SatAll a4 s4 ∧ WF s4 ∧ s3.top ≤ s4.top := by
      by_cases hbf : 2 ≤ half
      · rw [hs4, if_pos hbf]
        refine ih fstA sf.2 s3 a3 (by omega) (by omega : 2 ≤ fstA.size) hw3 hsat3
          (fun l hl ↦ ⟨(hin_f l hl).1,
            le_trans (hin_f l hl).2 (by omega)⟩)
          (fun l hl ↦ ⟨(hbnd1 l hl).1, by have := (hbnd1 l hl).2; omega⟩)
          (by omega) ?_
        refine unaryOut_congr (t := s2.top) hag3
          (fun l hl ↦ by have := (hbnd1 l hl).2; omega)
          (fun l hl ↦ by have := (hin_f l hl).2; omega) hun1'
      · rw [hs4, if_neg hbf]
        exact ⟨a3, fun _ _ ↦ rfl, hsat3, hw3, le_refl _⟩
    obtain ⟨a4, hag4, hsat4, hw4, htop4⟩ := step4
    exact ⟨a4, fun v hv ↦ (hag4 v (by omega)).trans
        ((hag3 v (by omega)).trans (hag2a v hv)),
      hsat4, hw4, by omega⟩

/-! ### Unconditional top-monotonicity -/

theorem toTONode_top_le : ∀ (fuel : Nat) (s : St) (il ol : Array Int),
    s.top ≤ (toTONode fuel s il ol).top := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ ↦ le_refl _
  | succ fuel ih =>
    intro s il ol
    set n := il.size with hn
    set half := n - n / 2 with hhalf
    set fstA := il.extract 0 half with hfstA
    set sndA := il.extract half n with hsndA
    set sf := (if 2 ≤ half then freshMany s half else (s, fstA)) with hsf
    set ss := (if 2 ≤ n - half then freshMany sf.1 (n - half) else (sf.1, sndA)) with hss
    set s2 := toUA ss.1 ol sf.2 ss.2 with hs2
    set s3 := (if 2 ≤ n - half then toTONode fuel s2 sndA ss.2 else s2) with hs3
    set s4 := (if 2 ≤ half then toTONode fuel s3 fstA sf.2 else s3) with hs4
    have hbody : toTONode (fuel + 1) s il ol = s4 := rfl
    rw [hbody]
    have h1 : s.top ≤ sf.1.top := by
      rw [hsf]
      split
      · rw [freshMany_top]; omega
      · exact le_refl _
    have h2 : sf.1.top ≤ ss.1.top := by
      rw [hss]
      split
      · rw [freshMany_top]; omega
      · exact le_refl _
    have h3 : s2.top = ss.1.top := by
      rw [hs2]
      exact toUA_top ss.1 ol sf.2 ss.2
    have h4 : s2.top ≤ s3.top := by
      rw [hs3]
      split
      · exact ih s2 sndA ss.2
      · exact le_refl _
    have h5 : s3.top ≤ s4.top := by
      rw [hs4]
      split
      · exact ih s3 fstA sf.2
      · exact le_refl _
    omega

theorem toTO_top_le (s : St) (xs : Array Int) : s.top ≤ (toTO s xs).1.top := by
  unfold toTO
  split
  · exact le_refl _
  · exact le_trans (by rw [freshMany_top]; omega) (toTONode_top_le xs.size _ xs _)

/-- **Satisfiability of `to_TO`**: the wrapper allocates the output registers, the
whole tree is satisfiable by fresh extension, and the outputs carry the unary count
of the inputs. -/
theorem toTO_sat (s : St) (ilst : Array Int) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s)
    (hin : ∀ l ∈ ilst, l ≠ 0 ∧ l.natAbs ≤ s.top) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧ SatAll a' (toTO s ilst).1 ∧
      WF (toTO s ilst).1 ∧ s.top ≤ (toTO s ilst).1.top ∧
      UnaryOut a' (toTO s ilst).2 ilst ∧
      (∀ l ∈ (toTO s ilst).2, l ≠ 0 ∧ l.natAbs ≤ (toTO s ilst).1.top) ∧
      (toTO s ilst).2.size = ilst.size := by
  by_cases hsm : ilst.size < 2
  · have h1 : (toTO s ilst).1 = s := by
      unfold toTO
      rw [if_pos hsm]
    have h2 : (toTO s ilst).2 = ilst := by
      unfold toTO
      rw [if_pos hsm]
    rw [h1, h2]
    exact ⟨a, fun _ _ ↦ rfl, hs, hw, le_refl _, unaryOut_self (xs := ilst) (by omega),
      hin, rfl⟩
  · have h1 : (toTO s ilst).1
        = toTONode ilst.size (freshMany s ilst.size).1 ilst (freshMany s ilst.size).2 := by
      unfold toTO
      rw [if_neg hsm]
    have h2 : (toTO s ilst).2 = (freshMany s ilst.size).2 := by
      unfold toTO
      rw [if_neg hsm]
    rw [h1, h2]
    set a1 := extendUnary a s.top ilst.size ilst with ha1
    have hag1 := extendUnary_agree a s.top ilst.size ilst
    have hun1 : UnaryOut a1 (freshMany s ilst.size).2 ilst :=
      unaryOut_extend a s ilst fun l hl ↦ (hin l hl).2
    have hft : (freshMany s ilst.size).1.top = s.top + ilst.size :=
      freshMany_top ..
    have hw1 : WF (freshMany s ilst.size).1 := by
      refine ⟨by rw [hft]; have := hw.1; omega, ?_⟩
      intro c hc l hl
      rw [freshMany_cls] at hc
      rw [hft]
      exact le_trans (hw.2 c hc l hl) (by omega)
    have hs1 : SatAll a1 (freshMany s ilst.size).1 := fun c hc ↦ by
      rw [freshMany_cls] at hc
      exact satAll_of_agree hw hs hag1 c hc
    obtain ⟨a2, hag2, hsat2, hw2, htop2⟩ :=
      toTONode_sat ilst.size ilst (freshMany s ilst.size).2 (freshMany s ilst.size).1
        a1 (le_refl _) (by omega) hw1 hs1
        (fun l hl ↦ ⟨(hin l hl).1, le_trans (hin l hl).2 (by rw [hft]; omega)⟩)
        (fun l hl ↦ by
          have := freshMany_mem s ilst.size l hl
          rw [hft]
          exact ⟨by omega, by omega⟩)
        (freshMany_size s ilst.size) hun1
    refine ⟨a2, fun v hv ↦ (hag2 v (by omega)).trans (hag1 v hv), hsat2, hw2,
      by omega, ?_, ?_, freshMany_size s ilst.size⟩
    · exact unaryOut_congr (t := (freshMany s ilst.size).1.top) hag2
        (fun l hl ↦ by have := freshMany_mem s ilst.size l hl; omega)
        (fun l hl ↦ le_trans (hin l hl).2 (by omega)) hun1
    · intro l hl
      have := freshMany_mem s ilst.size l hl
      exact ⟨by omega, by omega⟩

end TotSpec
end ConwayO7
