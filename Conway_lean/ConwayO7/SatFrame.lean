/-
L4 witness framework — satisfiability-by-construction over the generator.

`EncodesInvariantSRG o7cnf` needs: from a σ₀-invariant srg, an assignment satisfying
`o7.cnf`.  With `mkO7Cnf_eq` the target is the *generator's* output, so satisfaction
can be proved gadget-by-gadget in the order clauses are emitted.  This file provides
the plumbing:

  * `SatAll` — DIMACS-level satisfaction of a generator state's clauses;
  * `GTrip P f Q` — a Hoare triple: whenever the clauses so far are satisfied and `P`
    holds, the gadget `f`'s clauses can be satisfied by changing only variables above
    `s.top` (its fresh ones), establishing `Q`; with sequential (`comp`) and fold
    (`foldl_inv`) composition;
  * the bridge `sat_mkO7Cnf_of_satAll` from `SatAll` to `Std.Sat.CNF.Sat` (via the
    generator's no-zero-literal fact, checked computationally);
  * the first gadget instance: the symmetry-level-1 unit clauses.

Remaining gadget triples (degree mtotalizer, products, μ-counters, lex chains) slot
into this framework one family at a time.
-/
import ConwayO7.Encoder

namespace ConwayO7
namespace Encoder

/-! ### DIMACS-level semantics -/

/-- Satisfaction of a 1-based signed DIMACS literal. -/
def litSat (a : Nat → Bool) (l : Int) : Bool :=
  if l < 0 then !a l.natAbs else a l.natAbs

/-- Satisfaction of a clause (disjunction). -/
def clauseSat (a : Nat → Bool) (c : List Int) : Bool := c.any (litSat a)

/-- All clauses of a generator state are satisfied. -/
def SatAll (a : Nat → Bool) (s : St) : Prop := ∀ c ∈ s.cls, clauseSat a c = true

theorem satAll_init (a : Nat → Bool) (t : Nat) : SatAll a ⟨t, #[]⟩ := by
  intro c hc
  simp at hc

theorem satAll_push {a : Nat → Bool} {s : St} {c : List Int} (hs : SatAll a s)
    (hc : clauseSat a c = true) : SatAll a (push s c) := by
  intro d hd
  rcases Array.mem_push.mp hd with h | rfl
  · exact hs d h
  · exact hc

theorem litSat_congr {a b : Nat → Bool} {l : Int} (h : a l.natAbs = b l.natAbs) :
    litSat a l = litSat b l := by
  unfold litSat
  split <;> rw [h]

theorem litSat_neg (a : Nat → Bool) {l : Int} (hl : l ≠ 0) :
    litSat a (-l) = !litSat a l := by
  unfold litSat
  rcases lt_trichotomy l 0 with h | h | h
  · rw [if_neg (by omega : ¬(-l) < 0), if_pos h, Int.natAbs_neg, Bool.not_not]
  · exact absurd h hl
  · rw [if_pos (by omega : (-l) < 0), if_neg (by omega : ¬l < 0), Int.natAbs_neg]

/-- Clause satisfaction only depends on the assignment at the clause's variables. -/
theorem clauseSat_congr {a b : Nat → Bool} {c : List Int}
    (h : ∀ l ∈ c, a l.natAbs = b l.natAbs) : clauseSat a c = clauseSat b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    unfold clauseSat at *
    simp only [List.any_cons]
    rw [ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]
    congr 1
    unfold litSat
    split <;> rw [h l (List.mem_cons_self ..)]

/-! ### Hoare triples over gadgets -/

/-- Well-formed generator state: the variable counter dominates the orbit-variable
block and every literal of every clause emitted so far. -/
def WF (s : St) : Prop :=
  693 ≤ s.top ∧ ∀ c ∈ s.cls, ∀ l ∈ c, l.natAbs ≤ s.top

/-- Gadget triple: on well-formed states, from `P` (and all earlier clauses
satisfied), `f`'s clauses can be satisfied by changing only variables above `s.top`,
preserving well-formedness and establishing `Q`. -/
structure GTrip (P : (Nat → Bool) → Prop) (f : St → St) (Q : (Nat → Bool) → Prop) :
    Prop where
  mono : ∀ s, s.top ≤ (f s).top
  sat : ∀ s a, WF s → SatAll a s → P a →
    ∃ a', (∀ v ≤ s.top, a' v = a v) ∧ SatAll a' (f s) ∧ WF (f s) ∧ Q a'

theorem GTrip.comp {P Q R : (Nat → Bool) → Prop} {f g : St → St}
    (hf : GTrip P f Q) (hg : GTrip Q g R) : GTrip P (fun s ↦ g (f s)) R := by
  refine ⟨fun s ↦ le_trans (hf.mono s) (hg.mono (f s)), fun s a hw hs hp ↦ ?_⟩
  obtain ⟨a1, hag1, hs1, hw1, hq⟩ := hf.sat s a hw hs hp
  obtain ⟨a2, hag2, hs2, hw2, hr⟩ := hg.sat (f s) a1 hw1 hs1 hq
  exact ⟨a2, fun v hv ↦ (hag2 v (le_trans hv (hf.mono s))).trans (hag1 v hv), hs2,
    hw2, hr⟩

/-- A gadget that changes nothing is a triple for any stable condition. -/
theorem GTrip.id {P : (Nat → Bool) → Prop} : GTrip P (fun s ↦ s) P :=
  ⟨fun _ ↦ le_refl _, fun _ a hw hs hp ↦ ⟨a, fun _ _ ↦ rfl, hs, hw, hp⟩⟩

/-- On a well-formed state, satisfaction transfers along agreement up to `top`. -/
theorem satAll_of_agree {a b : Nat → Bool} {s : St} (hw : WF s) (hs : SatAll a s)
    (h : ∀ v ≤ s.top, b v = a v) : SatAll b s := fun c hc ↦ by
  rw [clauseSat_congr fun l hl ↦ h _ (hw.2 c hc l hl)]
  exact hs c hc

theorem clauseSat_four {a : Nat → Bool} {l₁ l₂ l₃ l₄ : Int}
    (h : litSat a l₁ = true ∨ litSat a l₂ = true ∨ litSat a l₃ = true ∨
      litSat a l₄ = true) :
    clauseSat a [l₁, l₂, l₃, l₄] = true := by
  unfold clauseSat
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  exact h

/-! ### The emitters as clause-list concatenation -/

@[simp] theorem push_cls (s : St) (c : List Int) : (push s c).cls = s.cls.push c := rfl

@[simp] theorem push_top (s : St) (c : List Int) : (push s c).top = s.top := rfl

@[simp] theorem fresh_fst_top (s : St) : (fresh s).1.top = s.top + 1 := rfl

@[simp] theorem fresh_fst_cls (s : St) : (fresh s).1.cls = s.cls := rfl

@[simp] theorem fresh_snd (s : St) : (fresh s).2 = ((s.top + 1 : Nat) : Int) := rfl

theorem pushMany_cls (s : St) (cs : List (List Int)) :
    (pushMany s cs).cls = s.cls ++ cs.toArray := by
  induction cs generalizing s with
  | nil => simp [pushMany]
  | cons c cs ih =>
    show (pushMany (push s c) cs).cls = _
    rw [ih]
    simp [push]

theorem pushMany_top (s : St) (cs : List (List Int)) : (pushMany s cs).top = s.top := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    show (pushMany (push s c) cs).top = _
    rw [ih]
    rfl

theorem emitFold_cls {α : Type} (s : St) (l : List α) (f : α → List (List Int)) :
    (emitFold s l f).cls = s.cls ++ (l.flatMap f).toArray := by
  induction l generalizing s with
  | nil => simp [emitFold]
  | cons x l ih =>
    show (emitFold (pushMany s (f x)) l f).cls = _
    rw [ih, pushMany_cls]
    simp

theorem emitFold_top {α : Type} (s : St) (l : List α) (f : α → List (List Int)) :
    (emitFold s l f).top = s.top := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    show (emitFold (pushMany s (f x)) l f).top = _
    rw [ih, pushMany_top]

/-- Satisfaction of a state extended by a clause list (any new top). -/
theorem satAll_append {a : Nat → Bool} {s : St} {new : List (List Int)} {t : Nat}
    (hold : ∀ c ∈ s.cls, clauseSat a c = true)
    (hnew : ∀ c ∈ new, clauseSat a c = true) :
    SatAll a ⟨t, s.cls ++ new.toArray⟩ := by
  intro c hc
  rcases Array.mem_append.mp hc with h | h
  · exact hold c h
  · exact hnew c (by simpa using h)

theorem countP_eq_count_true {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = (l.map p).count true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.countP_cons, List.map_cons, List.count_cons, ih]
    cases hx : p x <;> simp

theorem countP_neg_map (a : Nat → Bool) (l : List Int) (h0 : ∀ x ∈ l, x ≠ 0) :
    (l.map (-·)).countP (litSat a) = l.length - l.countP (litSat a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx0 : x ≠ 0 := h0 x (List.mem_cons_self ..)
    have hle := List.countP_le_length (p := litSat a) (l := l)
    rw [List.map_cons, List.countP_cons, List.countP_cons,
      ih fun y hy ↦ h0 y (List.mem_cons_of_mem _ hy), litSat_neg a hx0]
    cases hlx : litSat a x <;> simp <;> omega

/-- Adapt a triple to a stronger pre/post pair: the precondition projects onto `P`,
and the postcondition is rebuilt from the old one plus any ≤ 693-stable leftovers of
the precondition (every gadget extension fixes the orbit block). -/
theorem GTrip.adapt {P P' Q Q' : (Nat → Bool) → Prop} {f : St → St}
    (h : GTrip P f Q) (hPP : ∀ a, P' a → P a)
    (hQQ : ∀ a a', (∀ v ≤ 693, a' v = a v) → P' a → Q a' → Q' a') :
    GTrip P' f Q' := by
  refine ⟨h.mono, fun s a hw hs hp' ↦ ?_⟩
  obtain ⟨a', hag, hsat, hw', hq⟩ := h.sat s a hw hs (hPP a hp')
  exact ⟨a', hag, hsat, hw',
    hQQ a a' (fun v hv ↦ hag v (le_trans hv hw.1)) hp' hq⟩

/-- Fold composition with a uniform invariant. -/
theorem GTrip.foldl_inv {α : Type*} {Inv : (Nat → Bool) → Prop} {step : St → α → St}
    (l : List α) (h : ∀ x ∈ l, GTrip Inv (fun s ↦ step s x) Inv) :
    GTrip Inv (fun s ↦ l.foldl step s) Inv := by
  induction l with
  | nil => exact GTrip.id
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have hl := ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    exact hx.comp hl

/-! ### Bridge to `Std.Sat.CNF` -/

theorem clauseSat_eq_eval (a : Nat → Bool) (c : List Int) (h0 : ∀ l ∈ c, l ≠ 0) :
    clauseSat a c =
      Std.Sat.CNF.Clause.eval (fun v ↦ a (v + 1)) (c.map Dimacs.litOfInt) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hl : l ≠ 0 := h0 l (List.mem_cons_self ..)
    have habs : l.natAbs - 1 + 1 = l.natAbs := by
      have : l.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hl
      omega
    have ih' := ih fun x hx ↦ h0 x (List.mem_cons_of_mem _ hx)
    simp only [clauseSat, List.any_cons, List.map_cons, Std.Sat.CNF.Clause.eval_cons]
    rw [← ih']
    congr 1
    unfold litSat Dimacs.litOfInt
    split <;> simp [habs]

/-- Generic bridge: a state with no zero literals is `SatAll`-satisfied iff its
converted CNF is satisfied by the index-shifted assignment. -/
theorem satAll_iff_cnfSat (a : Nat → Bool) (s : St)
    (h0 : ∀ c ∈ s.cls, ∀ l ∈ c, l ≠ 0) :
    SatAll a s ↔
      Std.Sat.CNF.Sat (fun v ↦ a (v + 1)) ⟨s.cls.map fun c ↦ c.map Dimacs.litOfInt⟩ := by
  unfold Std.Sat.CNF.Sat Std.Sat.CNF.eval
  simp only [Array.all_map, Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h c hc
    rw [Function.comp_apply, ← clauseSat_eq_eval a c (h0 c hc)]
    exact h c hc
  · intro h c hc
    have := h c hc
    rwa [Function.comp_apply, ← clauseSat_eq_eval a c (h0 c hc)] at this

/-- The generator emits no zero literals (checked computationally, in `Bool` form
for an efficient compiled run). -/
theorem mkO7_no_zero_bool : (mkO7St.cls.all fun c ↦ c.all fun l ↦ !(l == 0)) = true := by
  native_decide

/-- The generator emits no zero literals. -/
theorem mkO7_no_zero : ∀ c ∈ mkO7St.cls, ∀ l ∈ c, l ≠ 0 := by
  intro c hc l hl
  have h1 := Array.all_eq_true_iff_forall_mem.mp mkO7_no_zero_bool c hc
  have h2 := List.all_eq_true.mp h1 l hl
  simpa using h2

/-- **The bridge**: any assignment satisfying every generator clause yields a
satisfying assignment of the generated CNF. -/
theorem sat_mkO7Cnf_of_satAll {a : Nat → Bool} (h : SatAll a mkO7St) :
    ∃ b, Std.Sat.CNF.Sat b mkO7Cnf :=
  ⟨fun v ↦ a (v + 1), (satAll_iff_cnfSat a mkO7St mkO7_no_zero).mp h⟩

/-! ### First gadget instance: the symmetry-level-1 units -/

/-- The level-1 symmetry condition on the orbit variables: the fixed vertex is
adjacent to exactly cycles 0 and 1 (the WLOG choice L5 will justify). -/
def Sym1Holds (a : Nat → Bool) : Prop :=
  ∀ i < 14, a (orbitOfN 0 (1 + 7 * i) + 1) = decide (i < 2)

/-- The level-1 unit variables sit inside the orbit block (computed). -/
theorem sym1_var_lt : ∀ i < 14, orbitOfN 0 (1 + 7 * i) + 1 ≤ 693 := by native_decide

theorem sym1Step_trip {i : Nat} (hi : i < 14) :
    GTrip Sym1Holds (fun s ↦ sym1Step s i) Sym1Holds := by
  refine ⟨fun s ↦ le_refl _,
    fun s a hw hs hp ↦ ⟨a, fun _ _ ↦ rfl, ?_, ⟨hw.1, fun c hc l hl ↦ ?_⟩, hp⟩⟩
  rotate_left
  · -- well-formedness: the unit literal is an orbit variable
    rcases Array.mem_push.mp hc with h | rfl
    · exact hw.2 c h l hl
    · have hb := sym1_var_lt i hi
      have hnat : l.natAbs ≤ 693 := by
        by_cases h2 : i < 2
        · rw [if_pos h2, List.mem_singleton] at hl
          subst hl
          rw [Int.natAbs_natCast]
          exact hb
        · rw [if_neg h2, List.mem_singleton] at hl
          subst hl
          rw [Int.natAbs_neg, Int.natAbs_natCast]
          exact hb
      have h693 := hw.1
      have htop : (sym1Step s i).top = s.top := rfl
      omega
  refine satAll_push hs ?_
  have hv := hp i hi
  set n : Nat := orbitOfN 0 (1 + 7 * i) + 1 with hn
  by_cases h2 : i < 2
  · rw [if_pos h2]
    simp only [clauseSat, List.any_cons, List.any_nil, Bool.or_false, litSat]
    rw [if_neg (by omega : ¬((n : Int) < 0)), Int.natAbs_natCast, hv]
    simp [h2]
  · rw [if_neg h2]
    simp only [clauseSat, List.any_cons, List.any_nil, Bool.or_false, litSat]
    rw [if_pos (by omega : (-(n : Int)) < 0), Int.natAbs_neg, Int.natAbs_natCast, hv]
    simp [h2]

/-- The whole level-1 section, as one triple. -/
theorem sym1_section_trip :
    GTrip Sym1Holds (fun s ↦ (List.range 14).foldl sym1Step s) Sym1Holds :=
  GTrip.foldl_inv _ fun _ hi ↦ sym1Step_trip (List.mem_range.mp hi)

end Encoder
end ConwayO7
