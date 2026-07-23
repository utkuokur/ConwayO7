/-
L4 — the common-neighbour section, in spec form.

`specCnStep` re-emits orbit `o`'s gadget with the two μ-counters produced by the
*structural* `SeqSpec.spec` (whose satisfiability is `SeqSpec.spec_sat`) instead of
the imperative `seqAtMost` port, with the fresh-variable bookkeeping in closed form.
`cn_section_agrees` verifies computationally that, starting from the concrete
post-degree state, the spec-level fold emits **exactly** the same clauses and top as
the imperative fold — so satisfiability proofs about `specCnStep` transfer verbatim
to the generator (and hence, through `mkO7Cnf_eq`, to `o7.cnf`).
-/
import ConwayO7.Encoder
import ConwayO7.SeqSpec

namespace ConwayO7
namespace Encoder

/-- The `CardEnc.equals(lits, k, seqcounter)` gadget in spec form: the at-least
counter (over negated literals, bound `n - k`) then the at-most counter, with the
closed-form top increments `tval * (n - tval)` each. -/
def specSeqEquals (s : St) (lits : Array Int) (k : Nat) : St :=
  let n := lits.size
  let t1 := n - k
  let s1 : St := ⟨s.top + t1 * (n - t1),
    s.cls ++ (SeqSpec.spec (lits.toList.map (-·)) t1 s.top).toArray⟩
  ⟨s1.top + k * (n - k),
    s1.cls ++ (SeqSpec.spec lits.toList k s1.top).toArray⟩

/-- Spec-level common-neighbour gadget for a representative pair `r`. -/
def specCnStepR (s : St) (r : Fin 99 × Fin 99) : St :=
  let sp := (List.finRange 99).foldl (prodStep r) (s, #[])
  specSeqEquals sp.1 (sp.2.push (evarI r.1 r.2)) 2

/-- Spec-level common-neighbour gadget for orbit `o`. -/
def specCnStep (s : St) (o : Nat) : St := specCnStepR s (orbitRep o)

/-- The concrete generator state after the degree section. -/
def afterDegrees : St := (List.finRange 99).foldl degreeStep ⟨693, #[]⟩

/-- **Glue**: on the concrete pipeline, the spec-level CN section coincides with the
imperative one — same clauses, same variable counter. -/
theorem cn_section_agrees :
    ((List.range 693).foldl specCnStep afterDegrees).cls
        = ((List.range 693).foldl cnStep afterDegrees).cls ∧
      ((List.range 693).foldl specCnStep afterDegrees).top
        = ((List.range 693).foldl cnStep afterDegrees).top := by
  native_decide

/-! ### Orbit-variable facts -/

theorem orbitOf_lt' {u v : Fin 99} (h : u ≠ v) : orbitOf (u, v) < 693 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact orbitOf_lt u v hlt
  · rw [orbitOf_swap]
    exact orbitOf_lt v u hlt

theorem evarI_pos (u v : Fin 99) : 0 < evarI u v := by
  unfold evarI
  exact_mod_cast Nat.succ_pos _

theorem evarI_ne_zero (u v : Fin 99) : evarI u v ≠ 0 := by
  have := evarI_pos u v
  omega

theorem evarI_natAbs_le {u v : Fin 99} (h : u ≠ v) : (evarI u v).natAbs ≤ 693 := by
  unfold evarI
  rw [Int.natAbs_natCast]
  have := orbitOf_lt' h
  omega

/-- The candidate common neighbours of the representative of orbit `o`. -/
def validW (r : Fin 99 × Fin 99) : List (Fin 99) :=
  (List.finRange 99).filter fun w ↦ decide (w ≠ r.1 ∧ w ≠ r.2)

/-- Representatives are normalized pairs (computed). -/
theorem orbitRep_lt : ∀ o < 693, (orbitRep o).1 < (orbitRep o).2 := by native_decide

/-- Each representative has 97 candidate common neighbours (computed). -/
theorem validW_length : ∀ o < 693, (validW (orbitRep o)).length = 97 := by native_decide

/-! ### The product fold: bookkeeping -/

theorem prodStep_top (r : Fin 99 × Fin 99) (sa : St × Array Int) (w : Fin 99) :
    (prodStep r sa w).1.top = sa.1.top ∨ (prodStep r sa w).1.top = sa.1.top + 1 := by
  unfold prodStep
  split
  · right; rfl
  · left; rfl

theorem prodFold_top_le (r : Fin 99 × Fin 99) (ws : List (Fin 99)) :
    ∀ (s : St) (acc : Array Int), s.top ≤ (ws.foldl (prodStep r) (s, acc)).1.top := by
  induction ws with
  | nil => exact fun _ _ ↦ le_refl _
  | cons w ws ih =>
    intro s acc
    rw [List.foldl_cons]
    have h0 : ((s, acc) : St × Array Int).1.top = s.top := rfl
    have h1 : s.top ≤ (prodStep r (s, acc) w).1.top := by
      rcases prodStep_top r (s, acc) w with h | h <;> omega
    have h2 := ih (prodStep r (s, acc) w).1 (prodStep r (s, acc) w).2
    have heta : ((prodStep r (s, acc) w).1, (prodStep r (s, acc) w).2)
        = prodStep r (s, acc) w := rfl
    rw [heta] at h2
    exact le_trans h1 h2

/-- Pure bookkeeping of the product fold: well-formedness, the variable counter,
array sizes and literal bounds. -/
theorem prodFold_book (r : Fin 99 × Fin 99) :
    ∀ (ws : List (Fin 99)) (s : St) (acc : Array Int),
      WF s → (∀ x ∈ acc, 0 < x ∧ x.natAbs ≤ s.top) →
      WF (ws.foldl (prodStep r) (s, acc)).1 ∧
        (ws.foldl (prodStep r) (s, acc)).1.top
          = s.top + (ws.filter fun w ↦ decide (w ≠ r.1 ∧ w ≠ r.2)).length ∧
        (ws.foldl (prodStep r) (s, acc)).2.size
          = acc.size + (ws.filter fun w ↦ decide (w ≠ r.1 ∧ w ≠ r.2)).length ∧
        (∀ x ∈ (ws.foldl (prodStep r) (s, acc)).2,
          0 < x ∧ x.natAbs ≤ (ws.foldl (prodStep r) (s, acc)).1.top) := by
  intro ws
  induction ws with
  | nil =>
    intro s acc hw hacc
    exact ⟨hw, by simp, by simp, hacc⟩
  | cons w ws ih =>
    intro s acc hw hacc
    by_cases hcond : w ≠ r.1 ∧ w ≠ r.2
    · -- one product variable is allocated
      have hstep : prodStep r (s, acc) w =
          (push (push (push { s with top := s.top + 1 } [-(s.top + 1 : Nat), evarI r.1 w])
              [-(s.top + 1 : Nat), evarI r.2 w])
            [((s.top + 1 : Nat) : Int), -evarI r.1 w, -evarI r.2 w],
            acc.push ((s.top + 1 : Nat) : Int)) := by
        unfold prodStep
        rw [if_pos hcond]
        rfl
      rw [List.foldl_cons, hstep]
      set s3 : St := push (push (push { s with top := s.top + 1 }
          [-(s.top + 1 : Nat), evarI r.1 w]) [-(s.top + 1 : Nat), evarI r.2 w])
          [((s.top + 1 : Nat) : Int), -evarI r.1 w, -evarI r.2 w] with hs3
      have htop3 : s3.top = s.top + 1 := rfl
      have hea := evarI_natAbs_le (u := r.1) (v := w) (fun h ↦ hcond.1 h.symm)
      have hec := evarI_natAbs_le (u := r.2) (v := w) (fun h ↦ hcond.2 h.symm)
      have h693 := hw.1
      have hw1 : WF s3 := by
        refine ⟨by omega, ?_⟩
        intro c hc l hl
        rw [hs3] at hc
        simp only [push] at hc
        rcases Array.mem_push.mp hc with hc | rfl
        · rcases Array.mem_push.mp hc with hc | rfl
          · rcases Array.mem_push.mp hc with hc | rfl
            · have := hw.2 c hc l hl
              omega
            · rcases List.mem_cons.mp hl with rfl | hl
              · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
              · rw [List.mem_singleton] at hl
                subst hl
                omega
          · rcases List.mem_cons.mp hl with rfl | hl
            · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
            · rw [List.mem_singleton] at hl
              subst hl
              omega
        · rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_natCast]; omega
          rcases List.mem_cons.mp hl with rfl | hl
          · rw [Int.natAbs_neg]; omega
          · rw [List.mem_singleton] at hl
            subst hl
            rw [Int.natAbs_neg]
            omega
      have hacc1 : ∀ x ∈ acc.push ((s.top + 1 : Nat) : Int),
          0 < x ∧ x.natAbs ≤ s3.top := by
        intro x hx
        rcases Array.mem_push.mp hx with hx | rfl
        · have := hacc x hx
          exact ⟨this.1, by omega⟩
        · refine ⟨by exact_mod_cast Nat.succ_pos _, ?_⟩
          rw [Int.natAbs_natCast]
          omega
      obtain ⟨hWF, htop, hsize, hbnd⟩ := ih s3 _ hw1 hacc1
      rw [List.filter_cons_of_pos (by simpa using hcond)]
      refine ⟨hWF, ?_, ?_, hbnd⟩
      · rw [htop, htop3, List.length_cons]
        omega
      · rw [hsize, Array.size_push, List.length_cons]
        omega
    · have hstep : prodStep r (s, acc) w = (s, acc) := by
        unfold prodStep
        rw [if_neg hcond]
      rw [List.foldl_cons, hstep,
        List.filter_cons_of_neg (by simpa using hcond)]
      exact ih s acc hw hacc

/-! ### The product fold: satisfiability and values -/

/-- Satisfiability of the product section: the fresh `p`-variables can be given their
semantic values `e(r₁,w) ∧ e(r₂,w)`, satisfying all product clauses and recording the
value list for the μ-counter. -/
theorem prodFold_sat (r : Fin 99 × Fin 99) :
    ∀ (ws : List (Fin 99)) (s : St) (acc : Array Int) (a : Nat → Bool),
      WF s → SatAll a s → (∀ x ∈ acc, 0 < x ∧ x.natAbs ≤ s.top) →
      ∃ a',
        (∀ v ≤ s.top, a' v = a v) ∧
        SatAll a' (ws.foldl (prodStep r) (s, acc)).1 ∧
        (ws.foldl (prodStep r) (s, acc)).2.toList.map (litSat a')
          = acc.toList.map (litSat a)
            ++ (ws.filter fun w ↦ decide (w ≠ r.1 ∧ w ≠ r.2)).map
                (fun w ↦ litSat a (evarI r.1 w) && litSat a (evarI r.2 w)) := by
  intro ws
  induction ws with
  | nil =>
    intro s acc a hw hs hacc
    exact ⟨a, fun _ _ ↦ rfl, hs, by simp⟩
  | cons w ws ih =>
    intro s acc a hw hs hacc
    by_cases hcond : w ≠ r.1 ∧ w ≠ r.2
    · have hstep : prodStep r (s, acc) w =
          (push (push (push { s with top := s.top + 1 } [-(s.top + 1 : Nat), evarI r.1 w])
              [-(s.top + 1 : Nat), evarI r.2 w])
            [((s.top + 1 : Nat) : Int), -evarI r.1 w, -evarI r.2 w],
            acc.push ((s.top + 1 : Nat) : Int)) := by
        unfold prodStep
        rw [if_pos hcond]
        rfl
      rw [List.foldl_cons, hstep]
      set ea : Int := evarI r.1 w with hea_def
      set ec : Int := evarI r.2 w with hec_def
      set p : Int := ((s.top + 1 : Nat) : Int) with hp_def
      set s3 : St := push (push (push { s with top := s.top + 1 } [-p, ea]) [-p, ec])
          [p, -ea, -ec] with hs3
      have htop3 : s3.top = s.top + 1 := rfl
      have h693 := hw.1
      have hea_abs : ea.natAbs ≤ 693 := evarI_natAbs_le (fun h ↦ hcond.1 h.symm)
      have hec_abs : ec.natAbs ≤ 693 := evarI_natAbs_le (fun h ↦ hcond.2 h.symm)
      have hea_ne : ea ≠ 0 := by rw [hea_def]; exact evarI_ne_zero r.1 w
      have hec_ne : ec ≠ 0 := by rw [hec_def]; exact evarI_ne_zero r.2 w
      have hp_ne : p ≠ 0 := by rw [hp_def]; omega
      -- the extension: give the fresh variable its semantic value
      set b : Nat → Bool :=
        fun v ↦ if v = s.top + 1 then litSat a ea && litSat a ec else a v with hb
      have hagree : ∀ v ≤ s.top, b v = a v := fun v hv ↦ by
        rw [hb]
        exact if_neg (by omega)
      have hlit_ea : litSat b ea = litSat a ea :=
        litSat_congr (hagree ea.natAbs (by omega))
      have hlit_ec : litSat b ec = litSat a ec :=
        litSat_congr (hagree ec.natAbs (by omega))
      have hlit_p : litSat b p = (litSat a ea && litSat a ec) := by
        unfold litSat
        rw [if_neg (by rw [hp_def]; omega : ¬p < 0), hp_def, Int.natAbs_natCast, hb]
        simp
        rfl
      -- the three product clauses hold under b
      have hsat3 : SatAll b s3 := by
        have hold : SatAll b s := satAll_of_agree hw hs hagree
        rw [hs3]
        refine satAll_push (satAll_push (satAll_push hold ?_) ?_) ?_
        · -- [-p, ea]
          refine SeqSpec.clauseSat_two ?_
          rw [litSat_neg b hp_ne, hlit_p, hlit_ea]
          cases hva : litSat a ea <;> cases hvc : litSat a ec <;> simp
        · -- [-p, ec]
          refine SeqSpec.clauseSat_two ?_
          rw [litSat_neg b hp_ne, hlit_p, hlit_ec]
          cases hva : litSat a ea <;> cases hvc : litSat a ec <;> simp
        · -- [p, -ea, -ec]
          refine SeqSpec.clauseSat_three ?_
          rw [litSat_neg b hea_ne, litSat_neg b hec_ne, hlit_p, hlit_ea, hlit_ec]
          cases hva : litSat a ea <;> cases hvc : litSat a ec <;> simp
      have hw3 : WF s3 := by
        have := (prodFold_book r [w] s acc hw hacc).1
        rw [List.foldl_cons, hstep] at this
        exact this
      have hacc3 : ∀ x ∈ acc.push p, 0 < x ∧ x.natAbs ≤ s3.top := by
        intro x hx
        rcases Array.mem_push.mp hx with hx | rfl
        · have := hacc x hx
          exact ⟨this.1, by omega⟩
        · refine ⟨by rw [hp_def]; exact_mod_cast Nat.succ_pos _, ?_⟩
          rw [hp_def, Int.natAbs_natCast]
          omega
      obtain ⟨a', hagree', hsat', hmap'⟩ := ih s3 (acc.push p) b hw3 hsat3 hacc3
      refine ⟨a', fun v hv ↦ (hagree' v (by omega)).trans (hagree v hv), hsat', ?_⟩
      rw [hmap', List.filter_cons_of_pos (by simpa using hcond), List.map_cons,
        Array.toList_push, List.map_append]
      have hmap_acc : acc.toList.map (litSat b) = acc.toList.map (litSat a) :=
        List.map_congr_left fun x hx ↦
          litSat_congr (hagree x.natAbs (by have := hacc x (by simpa using hx); omega))
      have hmap_ws :
          (ws.filter fun w' ↦ decide (w' ≠ r.1 ∧ w' ≠ r.2)).map
              (fun w' ↦ litSat b (evarI r.1 w') && litSat b (evarI r.2 w'))
            = (ws.filter fun w' ↦ decide (w' ≠ r.1 ∧ w' ≠ r.2)).map
              (fun w' ↦ litSat a (evarI r.1 w') && litSat a (evarI r.2 w')) := by
        refine List.map_congr_left fun w' hw' ↦ ?_
        have hw'mem := List.of_mem_filter hw'
        have hcond' : w' ≠ r.1 ∧ w' ≠ r.2 := by simpa using hw'mem
        rw [litSat_congr (hagree (evarI r.1 w').natAbs
            (by have := evarI_natAbs_le (u := r.1) (v := w') (fun h ↦ hcond'.1 h.symm); omega)),
          litSat_congr (hagree (evarI r.2 w').natAbs
            (by have := evarI_natAbs_le (u := r.2) (v := w') (fun h ↦ hcond'.2 h.symm); omega))]
      rw [hmap_acc, hmap_ws]
      simp only [List.map_cons, List.map_nil]
      rw [hlit_p]
      simp [hea_def, hec_def]
    · have hstep : prodStep r (s, acc) w = (s, acc) := by
        unfold prodStep
        rw [if_neg hcond]
      rw [List.foldl_cons, hstep, List.filter_cons_of_neg (by simpa using hcond)]
      exact ih s acc a hw hs hacc

/-! ### The semantic invariant of the CN section -/

/-- The count the μ-counter of a representative pair `r` checks: true products over
the candidate common neighbours, plus the pair's own adjacency. -/
def cnCountR (r : Fin 99 × Fin 99) (a : Nat → Bool) : Nat :=
  ((validW r).map fun w ↦ litSat a (evarI r.1 w) && litSat a (evarI r.2 w)).count true
    + (if litSat a (evarI r.1 r.2) = true then 1 else 0)

/-- The CN precondition (supplied by the srg counting identity, since μ − λ = 1):
every orbit's count is exactly 2. -/
def CnInv (a : Nat → Bool) : Prop := ∀ o < 693, cnCountR (orbitRep o) a = 2

theorem cnCountR_congr {r : Fin 99 × Fin 99} (hr : r.1 ≠ r.2) {a b : Nat → Bool}
    (h : ∀ v ≤ 693, b v = a v) : cnCountR r b = cnCountR r a := by
  have hlit : ∀ {u v : Fin 99}, u ≠ v → litSat b (evarI u v) = litSat a (evarI u v) :=
    fun {u v} huv ↦ litSat_congr (h _ (evarI_natAbs_le huv))
  have hmap : (validW r).map (fun w ↦ litSat b (evarI r.1 w) && litSat b (evarI r.2 w))
      = (validW r).map (fun w ↦ litSat a (evarI r.1 w) && litSat a (evarI r.2 w)) :=
    List.map_congr_left fun w hw ↦ by
      have hcond : w ≠ r.1 ∧ w ≠ r.2 := by
        simpa using List.of_mem_filter hw
      rw [hlit (fun hx ↦ hcond.1 hx.symm), hlit (fun hx ↦ hcond.2 hx.symm)]
  unfold cnCountR
  rw [hmap, hlit hr]

theorem CnInv_congr {a b : Nat → Bool} (h : ∀ v ≤ 693, b v = a v) (hi : CnInv a) :
    CnInv b := fun o ho ↦
  (cnCountR_congr (Fin.ne_of_lt (orbitRep_lt o ho)) h).trans (hi o ho)

/-! ### Satisfiability of the double counter -/

theorem cnt_full (xs : List Int) (a : Nat → Bool) :
    SeqSpec.cnt xs a xs.length = xs.countP (litSat a) := by
  unfold SeqSpec.cnt
  rw [List.take_length]

/-- Well-formedness of the spec-level `equals 2` gadget on 98 literals. -/
theorem specSeqEquals_wf (s : St) (lits : Array Int) (hw : WF s) (hn : lits.size = 98)
    (hlits : ∀ l ∈ lits, l ≠ 0 ∧ l.natAbs ≤ s.top) :
    WF (specSeqEquals s lits 2) ∧
      (specSeqEquals s lits 2).top = s.top + 384 := by
  have hlen : lits.toList.length = 98 := by rw [Array.length_toList, hn]
  have hlen' : (lits.toList.map (-·)).length = 98 := by rw [List.length_map, hlen]
  have hnt1 : SeqSpec.nt (lits.toList.map (-·)) (lits.size - 2) = 2 := by
    unfold SeqSpec.nt
    omega
  have hnt2 : SeqSpec.nt lits.toList 2 = 96 := by
    unfold SeqSpec.nt
    omega
  have hvars1 : ∀ l ∈ lits.toList.map (-·), l.natAbs ≤ s.top := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    rw [Int.natAbs_neg]
    exact (hlits x (by simpa using hx)).2
  have hvars2 : ∀ l ∈ lits.toList, l.natAbs ≤ s.top :=
    fun l hl ↦ (hlits l (by simpa using hl)).2
  have hb1 := SeqSpec.spec_vars (lits.toList.map (-·)) (lits.size - 2) s.top
    (by omega) (by omega) hvars1
  have hb2 := SeqSpec.spec_vars lits.toList 2
    (s.top + (lits.size - 2) * (lits.size - (lits.size - 2))) (by omega) (by omega)
    fun l hl ↦ le_trans (hvars2 l hl) (Nat.le_add_right ..)
  have htop1 : s.top + (lits.size - 2) * (lits.size - (lits.size - 2)) = s.top + 192 := by
    rw [hn]
  have hinc1 : (lits.size - 2) * SeqSpec.nt (lits.toList.map (-·)) (lits.size - 2) = 192 := by
    rw [hnt1, hn]
  have hinc2 : 2 * SeqSpec.nt lits.toList 2 = 192 := by
    rw [hnt2]
  constructor
  · constructor
    · have := hw.1
      show 693 ≤ s.top + (lits.size - 2) * (lits.size - (lits.size - 2)) + 2 * (lits.size - 2)
      omega
    · intro c hc l hl
      show l.natAbs ≤ s.top + (lits.size - 2) * (lits.size - (lits.size - 2)) + 2 * (lits.size - 2)
      have hgoal : s.top + (lits.size - 2) * (lits.size - (lits.size - 2)) + 2 * (lits.size - 2)
          = s.top + 384 := by
        rw [hn]
      rcases Array.mem_append.mp hc with hc | hc
      · rcases Array.mem_append.mp hc with hc | hc
        · have := hw.2 c hc l hl
          omega
        · have := hb1 c (by simpa using hc) l hl
          rw [hinc1] at this
          omega
      · have := hb2 c (by simpa using hc) l hl
        rw [hinc2, htop1] at this
        omega
  · show s.top + (lits.size - 2) * (lits.size - (lits.size - 2)) + 2 * (lits.size - 2)
      = s.top + 384
    rw [hn]

/-- Satisfiability of the spec-level `equals 2` gadget: with exactly two of the 98
literals true, both counters extend the assignment above `s.top`. -/
theorem specSeqEquals_sat (s : St) (lits : Array Int) (a : Nat → Bool)
    (hw : WF s) (hs : SatAll a s) (hn : lits.size = 98)
    (hlits : ∀ l ∈ lits, l ≠ 0 ∧ l.natAbs ≤ s.top)
    (hcount : lits.toList.countP (litSat a) = 2) :
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧ SatAll a' (specSeqEquals s lits 2) := by
  have hlen : lits.toList.length = 98 := by rw [Array.length_toList, hn]
  have hlen' : (lits.toList.map (-·)).length = 98 := by rw [List.length_map, hlen]
  have hne0 : ∀ l ∈ lits.toList, l ≠ 0 := fun l hl ↦ (hlits l (by simpa using hl)).1
  set t1 := lits.size - 2 with ht1
  set xs1 := lits.toList.map (-·) with hxs1
  set T := s.top with hT
  -- first counter: at-least 2, i.e. at most 96 negated literals true
  have hvars1 : ∀ l ∈ xs1, l ≠ 0 ∧ l.natAbs ≤ T := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    have := hlits x (by simpa using hx)
    exact ⟨by omega, by rw [Int.natAbs_neg]; exact this.2⟩
  have hcnt1 : SeqSpec.cnt xs1 a xs1.length ≤ t1 := by
    rw [cnt_full, hxs1, countP_neg_map a lits.toList hne0, hcount]
    omega
  have hspec1 := SeqSpec.spec_sat xs1 t1 T a (by omega) (by omega) hvars1 hcnt1
  set b1 := SeqSpec.wit xs1 t1 T a with hb1
  have hag1 : ∀ v ≤ T, b1 v = a v := SeqSpec.wit_agrees xs1 t1 T a
  set s1 : St := ⟨s.top + t1 * (lits.size - t1), s.cls ++ (SeqSpec.spec xs1 t1 s.top).toArray⟩
    with hs1
  have hsat1 : SatAll b1 s1 := by
    rw [hs1]
    exact satAll_append (satAll_of_agree hw hs hag1) hspec1
  have htop1 : s1.top = s.top + 192 := by
    rw [hs1]
    show s.top + t1 * (lits.size - t1) = s.top + 192
    rw [ht1, hn]
  have hw1 : WF s1 := by
    have hnt1 : SeqSpec.nt xs1 t1 = 2 := by
      unfold SeqSpec.nt
      omega
    have hb := SeqSpec.spec_vars xs1 t1 T (by omega) (by omega)
      fun l hl ↦ (hvars1 l hl).2
    refine ⟨by have := hw.1; omega, ?_⟩
    intro c hc l hl
    rw [hs1] at hc
    rcases Array.mem_append.mp hc with hc | hc
    · have := hw.2 c hc l hl
      omega
    · have := hb c (by simpa using hc) l hl
      rw [hnt1] at this
      omega
  -- second counter: at most 2 literals true
  have hvars2 : ∀ l ∈ lits.toList, l ≠ 0 ∧ l.natAbs ≤ s1.top := by
    intro l hl
    have := hlits l (by simpa using hl)
    exact ⟨this.1, by omega⟩
  have hcnt2 : SeqSpec.cnt lits.toList b1 lits.toList.length ≤ 2 := by
    rw [cnt_full]
    have : lits.toList.countP (litSat b1) = lits.toList.countP (litSat a) :=
      List.countP_congr fun l hl ↦ by
        rw [litSat_congr (hag1 l.natAbs ((hlits l (by simpa using hl)).2))]
    omega
  have hspec2 := SeqSpec.spec_sat lits.toList 2 s1.top b1 (by omega) (by omega) hvars2 hcnt2
  set b2 := SeqSpec.wit lits.toList 2 s1.top b1 with hb2
  have hag2 : ∀ v ≤ s1.top, b2 v = b1 v := SeqSpec.wit_agrees lits.toList 2 s1.top b1
  refine ⟨b2, fun v hv ↦ ((hag2 v (by omega)).trans (hag1 v hv)), ?_⟩
  show SatAll b2 ⟨s1.top + 2 * (lits.size - 2), s1.cls ++ (SeqSpec.spec lits.toList 2 s1.top).toArray⟩
  exact satAll_append (satAll_of_agree hw1 hsat1 hag2) hspec2

/-! ### The CN section triple -/

theorem specCnStepR_eq (s : St) (r : Fin 99 × Fin 99) :
    specCnStepR s r =
      specSeqEquals ((List.finRange 99).foldl (prodStep r) (s, #[])).1
        (((List.finRange 99).foldl (prodStep r) (s, #[])).2.push (evarI r.1 r.2)) 2 := rfl

theorem specSeqEquals_top_le (s : St) (lits : Array Int) (k : Nat) :
    s.top ≤ (specSeqEquals s lits k).top :=
  le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- **The CN gadget triple, generic in the representative pair** (kept symbolic so the
elaborator can never attempt to evaluate the concrete orbit table). -/
theorem specCnStepR_trip (r : Fin 99 × Fin 99) (hr : r.1 < r.2)
    (h97 : (validW r).length = 97) {P : (Nat → Bool) → Prop}
    (hPcount : ∀ a, P a → cnCountR r a = 2)
    (hPstable : ∀ {a a' : Nat → Bool}, (∀ v ≤ 693, a' v = a v) → P a → P a') :
    GTrip P (fun s ↦ specCnStepR s r) P := by
  have hrne : r.1 ≠ r.2 := Fin.ne_of_lt hr
  have hvalid : (List.finRange 99).filter
      (fun w ↦ decide (w ≠ r.1 ∧ w ≠ r.2)) = validW r := rfl
  refine ⟨fun s ↦ ?_, fun s a hw hs hp ↦ ?_⟩
  · -- monotonicity
    rw [specCnStepR_eq]
    exact le_trans (prodFold_top_le r (List.finRange 99) s #[]) (specSeqEquals_top_le _ _ _)
  · -- satisfiability (with well-formedness)
    rw [specCnStepR_eq]
    obtain ⟨hWFf, htopf, hsizef, hbndf⟩ :=
      prodFold_book r (List.finRange 99) s #[] hw (by simp)
    obtain ⟨a1, hag1, hsat1, hmap1⟩ :=
      prodFold_sat r (List.finRange 99) s #[] a hw hs (by simp)
    set F := (List.finRange 99).foldl (prodStep r) (s, #[]) with hF
    set ev : Int := evarI r.1 r.2 with hev
    have h0 : (#[] : Array Int).size = 0 := rfl
    have hsize98 : (F.2.push ev).size = 98 := by
      rw [Array.size_push, hF, hsizef, hvalid, h97, h0]
    have hlits : ∀ l ∈ F.2.push ev, l ≠ 0 ∧ l.natAbs ≤ F.1.top := by
      intro l hl
      rcases Array.mem_push.mp hl with hl | rfl
      · have := hbndf l hl
        exact ⟨by omega, this.2⟩
      · refine ⟨?_, by have := evarI_natAbs_le hrne; have := hWFf.1; omega⟩
        rw [hev]
        exact evarI_ne_zero r.1 r.2
    have hlit_ev : litSat a1 ev = litSat a ev := by
      refine litSat_congr (hag1 ev.natAbs ?_)
      have h1 : ev.natAbs ≤ 693 := by rw [hev]; exact evarI_natAbs_le hrne
      have := hw.1
      omega
    have hcount : (F.2.push ev).toList.countP (litSat a1) = 2 := by
      rw [Array.toList_push, List.countP_append, List.countP_cons, List.countP_nil]
      have hcP : F.2.toList.countP (litSat a1)
          = ((validW r).map fun w ↦
              litSat a (evarI r.1 w) && litSat a (evarI r.2 w)).count true := by
        rw [countP_eq_count_true, hmap1, hvalid]
        simp
      have h2 := hPcount a hp
      unfold cnCountR at h2
      rw [hcP, hlit_ev]
      rcases hlv : litSat a ev with _ | _
      · rw [hev] at hlv
        rw [hlv] at h2
        simp at h2 ⊢
        omega
      · rw [hev] at hlv
        rw [hlv] at h2
        simp at h2 ⊢
        omega
    obtain ⟨a2, hag2, hsat2⟩ :=
      specSeqEquals_sat F.1 (F.2.push ev) a1 hWFf hsat1 hsize98 hlits hcount
    have hstop : s.top ≤ F.1.top := by
      rw [hF]
      exact prodFold_top_le r (List.finRange 99) s #[]
    refine ⟨a2, fun v hv ↦ (hag2 v (by omega)).trans (hag1 v hv), hsat2,
      (specSeqEquals_wf F.1 (F.2.push ev) hWFf hsize98 hlits).1, ?_⟩
    refine hPstable (fun v hv ↦ ?_) hp
    have h693 := hw.1
    exact (hag2 v (by omega)).trans (hag1 v (by omega))

/-- The per-orbit instance of the generic triple. -/
theorem specCnStep_trip {o : Nat} (ho : o < 693) :
    GTrip CnInv (fun s ↦ specCnStep s o) CnInv :=
  specCnStepR_trip (orbitRep o) (orbitRep_lt o ho) (validW_length o ho)
    (fun _ hp ↦ hp o ho) (fun hag hp ↦ CnInv_congr hag hp)

/-- The whole CN section, as one triple. -/
theorem cn_section_trip :
    GTrip CnInv (fun s ↦ (List.range 693).foldl specCnStep s) CnInv :=
  GTrip.foldl_inv _ fun _ ho ↦ specCnStep_trip (List.mem_range.mp ho)

end Encoder
end ConwayO7
