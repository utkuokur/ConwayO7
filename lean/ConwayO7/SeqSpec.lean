/-
L4 gadget mathematics — satisfiability of the sequential counter.

`SeqSpec.spec xs tval T` is the clause family emitted by
`Encoder.seqAtMost` (Knuth's irredundant Sinz counter) for input literals `xs`,
bound `tval`, starting above variable `T` — with the register numbering
`idOf` in closed form (registers `(k, 0)` and `(k, 1)` interleave during the first
column, then columns of `tval` registers each; this matches the C++ allocation
order, to be checked computationally at the 693 + 99 concrete call sites).

The main theorem `spec_sat`: whenever at most `tval` of the input literals are
true, extending the assignment by the counting witness

    s(k, j)  :=  "at least k+1 of the first j+k+1 input literals are true"

satisfies every emitted clause, changing no variable ≤ T.  Both counter uses in
`o7.cnf` (the μ = 2 `atmost` and, applied to negated literals, the `atleast`)
are instances.
-/
import ConwayO7.SatFrame

namespace ConwayO7
namespace SeqSpec

open Encoder

/-! ### Literal-level helpers -/

theorem litSat_neg (a : Nat → Bool) {l : Int} (hl : l ≠ 0) :
    litSat a (-l) = !litSat a l := by
  unfold litSat
  rcases lt_trichotomy l 0 with h | h | h
  · rw [if_neg (by omega : ¬(-l) < 0), if_pos h, Int.natAbs_neg, Bool.not_not]
  · exact absurd h hl
  · rw [if_pos (by omega : (-l) < 0), if_neg (by omega : ¬l < 0), Int.natAbs_neg]

theorem clauseSat_two {a : Nat → Bool} {l₁ l₂ : Int}
    (h : litSat a l₁ = true ∨ litSat a l₂ = true) :
    clauseSat a [l₁, l₂] = true := by
  unfold clauseSat
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  exact h

theorem clauseSat_three {a : Nat → Bool} {l₁ l₂ l₃ : Int}
    (h : litSat a l₁ = true ∨ litSat a l₂ = true ∨ litSat a l₃ = true) :
    clauseSat a [l₁, l₂, l₃] = true := by
  unfold clauseSat
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  exact h

/-! ### The spec -/

variable (xs : List Int) (tval T : Nat)

/-- Number of counter columns. -/
def nt : Nat := xs.length - tval

/-- Closed-form register numbering (the C++ first-use allocation order). -/
def idOf (k j : Nat) : Nat :=
  if j = 0 then T + 2 * k + 1
  else if j = 1 then T + 2 * k + 2
  else T + 2 * tval + (j - 2) * tval + k + 1

/-- Register literal. -/
def sid (k j : Nat) : Int := (idOf tval T k j : Nat)

/-- The clauses of column `j`. -/
def clausesFor (j : Nat) : List (List Int) :=
  [[-xs[j]!, sid tval T 0 j]] ++
    ((List.range (tval - 1)).flatMap fun k ↦
      (if j < nt xs tval - 1 then [[-sid tval T k j, sid tval T k (j + 1)]] else []) ++
        [[-xs[j + k + 1]!, -sid tval T k j, sid tval T (k + 1) j]]) ++
    (if j < nt xs tval - 1 then
      [[-sid tval T (tval - 1) j, sid tval T (tval - 1) (j + 1)]] else []) ++
    [[-xs[j + tval]!, -sid tval T (tval - 1) j]]

/-- The full emitted clause family. -/
def spec : List (List Int) := (List.range (nt xs tval)).flatMap (clausesFor xs tval T)

/-! ### The counting witness -/

/-- Number of true literals among the first `m` inputs. -/
def cnt (a : Nat → Bool) (m : Nat) : Nat := (xs.take m).countP (litSat a)

/-- Registers are fresh: their ids exceed `T`. -/
theorem idOf_gt (k j : Nat) : T < idOf tval T k j := by
  unfold idOf
  split
  · omega
  · split <;> omega

/-- Decode a fresh-variable offset back into its register coordinates. -/
def decodeKJ (d : Nat) : Nat × Nat :=
  if d ≤ 2 * tval then
    (if d % 2 = 1 then ((d - 1) / 2, 0) else (d / 2 - 1, 1))
  else
    ((d - 2 * tval - 1) % tval, (d - 2 * tval - 1) / tval + 2)

/-- The witness: keep `a` at or below `T`; above `T`, decode `(k, j)` from the
register numbering and give the counting value. -/
def wit (a : Nat → Bool) (v : Nat) : Bool :=
  if v ≤ T then a v
  else
    decide ((decodeKJ tval (v - T)).1 + 1 ≤
      cnt xs a ((decodeKJ tval (v - T)).2 + (decodeKJ tval (v - T)).1 + 1))

theorem wit_le {a : Nat → Bool} {v : Nat} (h : v ≤ T) : wit xs tval T a v = a v :=
  if_pos h

/-- The decode inverts the register numbering. -/
theorem decode_encode {k j : Nat} (hk : k < tval) :
    decodeKJ tval (idOf tval T k j - T) = (k, j) := by
  unfold idOf decodeKJ
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl]
    have hd : T + 2 * k + 1 - T = 2 * k + 1 := by omega
    rw [hd, if_pos (by omega : 2 * k + 1 ≤ 2 * tval), if_pos (by omega : (2 * k + 1) % 2 = 1)]
    have h1 : (2 * k + 1 - 1) / 2 = k := by omega
    rw [h1]
  · by_cases hj1 : j = 1
    · subst hj1
      rw [if_neg hj0, if_pos rfl]
      have hd : T + 2 * k + 2 - T = 2 * k + 2 := by omega
      rw [hd, if_pos (by omega : 2 * k + 2 ≤ 2 * tval),
        if_neg (by omega : ¬(2 * k + 2) % 2 = 1)]
      have h1 : (2 * k + 2) / 2 - 1 = k := by omega
      rw [h1]
    · rw [if_neg hj0, if_neg hj1]
      rw [show T + 2 * tval + (j - 2) * tval + k + 1 - T
          = 2 * tval + ((j - 2) * tval + k) + 1 by omega]
      rw [if_neg (by omega : ¬2 * tval + ((j - 2) * tval + k) + 1 ≤ 2 * tval)]
      have h1 : 2 * tval + ((j - 2) * tval + k) + 1 - 2 * tval - 1 = (j - 2) * tval + k := by
        omega
      rw [h1]
      have htpos : 0 < tval := by omega
      have hmod : ((j - 2) * tval + k) % tval = k := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
      have hdiv : ((j - 2) * tval + k) / tval + 2 = j := by
        rw [Nat.mul_comm, Nat.mul_add_div htpos, Nat.div_eq_of_lt hk]
        omega
      rw [hmod, hdiv]

/-- Value of the witness on a register. -/
theorem wit_idOf (a : Nat → Bool) {k j : Nat} (hk : k < tval) :
    wit xs tval T a (idOf tval T k j) = decide (k + 1 ≤ cnt xs a (j + k + 1)) := by
  unfold wit
  rw [if_neg (by have := idOf_gt tval T k j; omega : ¬idOf tval T k j ≤ T),
    decode_encode tval T hk]

/-! ### Counting lemmas -/

theorem cnt_mono (a : Nat → Bool) {m m' : Nat} (h : m ≤ m') :
    cnt xs a m ≤ cnt xs a m' := by
  unfold cnt
  induction m' with
  | zero => simp_all
  | succ m' ih =>
    rcases Nat.lt_or_ge m (m' + 1) with hm | hm
    · calc (xs.take m).countP (litSat a) ≤ (xs.take m').countP (litSat a) := ih (by omega)
        _ ≤ (xs.take (m' + 1)).countP (litSat a) := by
          rw [List.take_add_one, List.countP_append]
          omega
    · have : m = m' + 1 := by omega
      subst this
      exact le_refl _

theorem cnt_succ_of_true (a : Nat → Bool) {m : Nat} (hm : m < xs.length)
    (h : litSat a xs[m]! = true) : cnt xs a m + 1 ≤ cnt xs a (m + 1) := by
  unfold cnt
  rw [List.take_add_one, List.countP_append]
  have : xs[m]?.toList = [xs[m]] := by
    rw [List.getElem?_eq_getElem hm]
    rfl
  rw [this]
  have hx : xs[m]! = xs[m] := by
    rw [getElem!_pos xs m hm]
  rw [hx] at h
  simp [h]

/-- Input literals evaluate identically under the witness. -/
theorem litSat_wit (a : Nat → Bool) {l : Int} (hl : l.natAbs ≤ T) :
    litSat (wit xs tval T a) l = litSat a l := by
  unfold litSat
  split <;> rw [wit_le xs tval T hl]

/-! ### The main theorem -/

/-- **Satisfiability of the sequential counter**: if at most `tval` of the input
literals are true under `a`, the counting witness satisfies every emitted clause
(and agrees with `a` at or below `T`). -/
theorem spec_sat (a : Nat → Bool)
    (htv : 1 ≤ tval) (hnt : tval + 2 ≤ xs.length)
    (hvars : ∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ T)
    (hbound : cnt xs a xs.length ≤ tval) :
    ∀ c ∈ spec xs tval T, clauseSat (wit xs tval T a) c = true := by
  intro c hc
  set b := wit xs tval T a with hb
  have habs : ∀ l ∈ xs, l.natAbs ≤ T := fun l hl ↦ (hvars l hl).2
  have hlit : ∀ {m : Nat}, m < xs.length → litSat b xs[m]! = litSat a xs[m]! := by
    intro m hm
    rw [hb, litSat_wit]
    rw [getElem!_pos xs m hm]
    exact habs _ (List.getElem_mem hm)
  have hne : ∀ {m : Nat}, m < xs.length → xs[m]! ≠ 0 := by
    intro m hm
    rw [getElem!_pos xs m hm]
    exact (hvars _ (List.getElem_mem hm)).1
  have hsidv : ∀ {k j : Nat}, k < tval →
      litSat b (sid tval T k j) = decide (k + 1 ≤ cnt xs a (j + k + 1)) := by
    intro k j hk
    unfold sid litSat
    rw [if_neg (by have := idOf_gt tval T k j; omega : ¬((idOf tval T k j : Nat) : Int) < 0),
      Int.natAbs_natCast, hb, wit_idOf xs tval T a hk]
  -- unpack membership in the spec
  simp only [spec, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, hcj⟩ := hc
  have hjlen : j + tval < xs.length := by
    have : nt xs tval = xs.length - tval := rfl
    omega
  simp only [clausesFor, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hcj
  rcases hcj with ((rfl | ⟨k, hk, hkc⟩) | hlast) | rfl
  · -- column head: xs[j] → s(0, j)
    refine clauseSat_two (by
      by_cases hx : litSat a xs[j]! = true
      · right
        rw [hsidv (by omega)]
        simp only [decide_eq_true_eq]
        calc 0 + 1 ≤ cnt xs a j + 1 := by omega
          _ ≤ cnt xs a (j + 1) := cnt_succ_of_true xs a (by omega) hx
      · left
        rw [litSat_neg b (hne (by omega)), hlit (by omega)]
        simp only [Bool.not_eq_true'] at hx ⊢
        exact Bool.not_eq_true _ ▸ (by simpa using hx))
  · -- the k-loop clauses
    rcases hkc with hshift | hstep
    · -- shift: s(k, j) → s(k, j+1)
      have hj' : j < nt xs tval - 1 := by
        by_contra h
        rw [if_neg h] at hshift
        exact absurd hshift (List.not_mem_nil)
      rw [if_pos hj'] at hshift
      rw [List.mem_singleton] at hshift
      subst hshift
      refine clauseSat_two ?_
      by_cases hs : litSat b (sid tval T k j) = true
      · right
        rw [hsidv (by omega)] at hs ⊢
        simp only [decide_eq_true_eq] at hs ⊢
        exact le_trans hs (cnt_mono xs a (by omega))
      · left
        rw [litSat_neg b (by
          unfold sid
          have := idOf_gt tval T k j
          omega)]
        simpa using hs
    · -- step: xs[j+k+1] ∧ s(k, j) → s(k+1, j)
      subst hstep
      refine clauseSat_three ?_
      by_cases hx : litSat b xs[j + k + 1]! = true
      · by_cases hs : litSat b (sid tval T k j) = true
        · right; right
          rw [hsidv (by omega)] at hs ⊢
          simp only [decide_eq_true_eq] at hs ⊢
          have hxa : litSat a xs[j + k + 1]! = true := by
            rw [← hlit (show j + k + 1 < xs.length by omega)]
            exact hx
          calc k + 1 + 1 ≤ cnt xs a (j + k + 1) + 1 := by omega
            _ ≤ cnt xs a (j + k + 1 + 1) := cnt_succ_of_true xs a (m := j + k + 1) (by omega) hxa
            _ = cnt xs a (j + (k + 1) + 1) := by ring_nf
        · right; left
          rw [litSat_neg b (by
            unfold sid
            have := idOf_gt tval T k j
            omega)]
          simpa using hs
      · left
        rw [litSat_neg b (hne (by omega))]
        simpa using hx
  · -- top-register shift
    have hj' : j < nt xs tval - 1 := by
      by_contra h
      rw [if_neg h] at hlast
      exact absurd hlast (List.not_mem_nil)
    rw [if_pos hj'] at hlast
    rw [List.mem_singleton] at hlast
    subst hlast
    refine clauseSat_two ?_
    by_cases hs : litSat b (sid tval T (tval - 1) j) = true
    · right
      rw [hsidv (by omega)] at hs ⊢
      simp only [decide_eq_true_eq] at hs ⊢
      exact le_trans hs (cnt_mono xs a (by omega))
    · left
      rw [litSat_neg b (by
        unfold sid
        have := idOf_gt tval T (tval - 1) j
        omega)]
      simpa using hs
  · -- overflow guard: ¬(xs[j+tval] ∧ s(tval-1, j))
    refine clauseSat_two ?_
    by_cases hx : litSat b xs[j + tval]! = true
    · right
      rw [litSat_neg b (by
        unfold sid
        have := idOf_gt tval T (tval - 1) j
        omega)]
      rw [hsidv (by omega)]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_le]
      by_contra h
      have h' : tval ≤ cnt xs a (j + (tval - 1) + 1) := by omega
      have hstepc := cnt_succ_of_true xs a hjlen (by rw [← hlit hjlen]; exact hx)
      have h2 : j + (tval - 1) + 1 = j + tval := by omega
      rw [h2] at h'
      have : tval + 1 ≤ cnt xs a (j + tval + 1) := by
        calc tval + 1 ≤ cnt xs a (j + tval) + 1 := by omega
          _ ≤ cnt xs a (j + tval + 1) := hstepc
      have := le_trans this (cnt_mono xs a (by omega : j + tval + 1 ≤ xs.length))
      omega
    · left
      rw [litSat_neg b (hne hjlen)]
      simpa using hx

/-- Packaging: the witness changes nothing at or below `T`. -/
theorem wit_agrees (a : Nat → Bool) : ∀ v ≤ T, wit xs tval T a v = a v :=
  fun _ hv ↦ wit_le xs tval T hv

/-! ### Variable bounds (for well-formedness) -/

theorem idOf_le {k j : Nat} (hnt2 : 2 ≤ nt xs tval) (hk : k < tval) (hj : j < nt xs tval) :
    idOf tval T k j ≤ T + tval * nt xs tval := by
  unfold idOf
  have h2 : tval * 2 ≤ tval * nt xs tval := Nat.mul_le_mul_left _ hnt2
  split
  · omega
  · split
    · omega
    · rename_i hj0 hj1
      have hj2 : 2 ≤ j := by omega
      have h1 : (j - 2 + 3) * tval ≤ nt xs tval * tval :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.mul_comm (nt xs tval) tval] at h1
      omega

/-- Every literal in the emitted family is bounded by the final counter position. -/
theorem spec_vars (htv : 1 ≤ tval) (hnt : tval + 2 ≤ xs.length)
    (hvars : ∀ l ∈ xs, l.natAbs ≤ T) :
    ∀ c ∈ spec xs tval T, ∀ l ∈ c, l.natAbs ≤ T + tval * nt xs tval := by
  intro c hc
  have hnt2 : 2 ≤ nt xs tval := by
    have : nt xs tval = xs.length - tval := rfl
    omega
  have hsid : ∀ {k j : Nat}, k < tval → j < nt xs tval →
      (sid tval T k j).natAbs ≤ T + tval * nt xs tval := by
    intro k j hk hj
    unfold sid
    rw [Int.natAbs_natCast]
    exact idOf_le xs tval T hnt2 hk hj
  have hx : ∀ {m : Nat}, m < xs.length → (xs[m]!).natAbs ≤ T + tval * nt xs tval := by
    intro m hm
    rw [getElem!_pos xs m hm]
    exact le_trans (hvars _ (List.getElem_mem hm)) (by omega)
  simp only [spec, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, hcj⟩ := hc
  have hjlen : j + tval < xs.length := by
    have : nt xs tval = xs.length - tval := rfl
    omega
  simp only [clausesFor, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hcj
  rcases hcj with ((rfl | ⟨k, hk, hkc⟩) | hlast) | rfl
  · -- [-xs[j], s(0,j)]
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [Int.natAbs_neg]; exact hx (by omega)
    · rw [List.mem_singleton] at hl
      subst hl
      exact hsid htv hj
  · rcases hkc with hshift | hstep
    · -- [-s(k,j), s(k,j+1)]
      have hj' : j < nt xs tval - 1 := by
        by_contra h
        rw [if_neg h] at hshift
        exact absurd hshift (List.not_mem_nil)
      rw [if_pos hj', List.mem_singleton] at hshift
      subst hshift
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]; exact hsid (by omega) (by omega)
      · rw [List.mem_singleton] at hl
        subst hl
        exact hsid (by omega) (by omega)
    · -- [-xs[j+k+1], -s(k,j), s(k+1,j)]
      subst hstep
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]; exact hx (by omega)
      rcases List.mem_cons.mp hl with rfl | hl
      · rw [Int.natAbs_neg]; exact hsid (by omega) hj
      · rw [List.mem_singleton] at hl
        subst hl
        exact hsid (by omega) hj
  · -- [-s(tval-1,j), s(tval-1,j+1)]
    have hj' : j < nt xs tval - 1 := by
      by_contra h
      rw [if_neg h] at hlast
      exact absurd hlast (List.not_mem_nil)
    rw [if_pos hj', List.mem_singleton] at hlast
    subst hlast
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [Int.natAbs_neg]; exact hsid (by omega) (by omega)
    · rw [List.mem_singleton] at hl
      subst hl
      exact hsid (by omega) (by omega)
  · -- [-xs[j+tval], -s(tval-1,j)]
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [Int.natAbs_neg]; exact hx (by omega)
    · rw [List.mem_singleton] at hl
      subst hl
      rw [Int.natAbs_neg]
      exact hsid (by omega) hj

end SeqSpec
end ConwayO7
