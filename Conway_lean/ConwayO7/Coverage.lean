/-
Layer L1 — coverage: the 98,536 cubes tile the whole assignment space.

The artifact's cubes are sign *prefixes* along one fixed branching order of
variables (every `deepen.py` split is the binary  x  vs  ¬x  on the next
variable), so a cube is a `List Bool` of signs and coverage is a purely
combinatorial fact about binary strings:

  a prefix-free family with full Kraft mass  Σ 2^(D − |s|) = 2^D
  is a *maximal* antichain: every length-D string extends some member.

This layer replaces `check_coverage.py` in the trusted base: the antichain and
mass-1 facts it checks numerically are here *proved* to imply coverage
(`covers_of_prefixFree_kraft`, now sorry-free), and will be *computed*
(`decide`/`native_decide`) on the concrete cube data in a later data layer.
If the concrete cubes ever fail the prefix-model check, the computation fails
loudly — the model is verified against the data, never assumed.
-/
import ConwayO7.Semantics

open Std.Sat

namespace ConwayO7

/-! ### Sign-prefix cubes -/

/-- The cube of a sign string `s` along the branching `order` — literally the zip,
since `Std.Sat.Literal Nat = Nat × Bool`. -/
def cubeOfSigns (order : List Nat) (s : List Bool) : Cube := order.zip s

/-- A cube of signs is satisfied by `a` iff its sign string is a prefix of the
branch word `order.map a`. -/
theorem cubeOfSigns_eval_iff (order : List Nat) (s : List Bool) (a : Nat → Bool)
    (hlen : s.length ≤ order.length) :
    Cube.eval a (cubeOfSigns order s) = true ↔ s <+: order.map a := by
  induction s generalizing order with
  | nil => simp [cubeOfSigns]
  | cons b s ih =>
    cases order with
    | nil => simp at hlen
    | cons v order =>
      have hlen' : s.length ≤ order.length := by simpa using hlen
      have ih' := ih order hlen'
      simp only [cubeOfSigns] at ih'
      simp only [cubeOfSigns, List.zip_cons_cons, Cube.eval_cons, Bool.and_eq_true, beq_iff_eq,
        List.map_cons, List.cons_prefix_cons, ih']
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1.symm, h2⟩⟩

/-! ### Kraft weight and prefix-freeness -/

/-- Total (integer) Kraft weight of a family of sign strings at depth `D`:
`Σ_{s ∈ S} 2^(D − |s|)`.  Full coverage corresponds to weight `2^D`
(the exact-arithmetic `mass = 1` fact of `check_coverage.py`). -/
def kraftWeight (D : Nat) (S : List (List Bool)) : Nat :=
  (S.map fun s ↦ 2 ^ (D - s.length)).sum

/-- Prefix-freeness: no sign string in the family is a prefix of another.
(`List.Pairwise` also forces the family to be duplicate-free, since `s <+: s`.) -/
def PrefixFree (S : List (List Bool)) : Prop :=
  S.Pairwise fun s t ↦ ¬ s <+: t ∧ ¬ t <+: s

theorem kraftWeight_zero (S : List (List Bool)) : kraftWeight 0 S = S.length := by
  induction S with
  | nil => rfl
  | cons s S ih => simp [kraftWeight] at ih ⊢; omega

/-- A prefix-free family containing the empty string is exactly `[[]]`
(the empty string is a prefix of everything). -/
theorem prefixFree_eq_of_nil_mem {S : List (List Bool)} (hpf : PrefixFree S)
    (h : [] ∈ S) : S = [[]] := by
  cases S with
  | nil => cases h
  | cons s S =>
    obtain ⟨hs, hS⟩ := List.pairwise_cons.mp hpf
    rcases List.mem_cons.mp h with h | h
    · subst h
      cases S with
      | nil => rfl
      | cons t T => exact absurd List.nil_prefix (hs t (by simp)).1
    · exact absurd List.nil_prefix (hs [] h).2

/-! ### Splitting a family by its first bit -/

/-- The tail of `s` if it starts with bit `b`, else `none`. -/
def branchTail? (b : Bool) : List Bool → Option (List Bool)
  | [] => none
  | c :: t => if c = b then some t else none

theorem branchTail?_eq_some {b : Bool} {s t : List Bool} :
    branchTail? b s = some t ↔ s = b :: t := by
  cases s with
  | nil => simp [branchTail?]
  | cons c u =>
    by_cases hc : c = b
    · subst hc; simp [branchTail?]
    · simp [branchTail?, hc]

/-- The tails of the members of `S` that start with bit `b`. -/
def branchTails (b : Bool) (S : List (List Bool)) : List (List Bool) :=
  S.filterMap (branchTail? b)

theorem mem_branchTails {b : Bool} {S : List (List Bool)} {t : List Bool} :
    t ∈ branchTails b S ↔ b :: t ∈ S := by
  simp [branchTails, List.mem_filterMap, branchTail?_eq_some]

theorem length_le_of_mem_branchTails {b : Bool} {S : List (List Bool)} {D : Nat}
    (hlen : ∀ s ∈ S, s.length ≤ D + 1) : ∀ t ∈ branchTails b S, t.length ≤ D := by
  intro t ht
  have := hlen (b :: t) (mem_branchTails.mp ht)
  simpa using this

theorem prefixFree_branchTails (b : Bool) {S : List (List Bool)} (hpf : PrefixFree S) :
    PrefixFree (branchTails b S) := by
  refine List.Pairwise.filterMap (branchTail? b) ?_ hpf
  intro s s' hss' t ht t' ht'
  rw [branchTail?_eq_some] at ht ht'
  subst ht; subst ht'
  exact ⟨fun hp ↦ hss'.1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩),
         fun hp ↦ hss'.2 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)⟩

/-- The Kraft weight at depth `D + 1` splits exactly across the two branches. -/
theorem kraftWeight_split (D : Nat) {S : List (List Bool)} (hnil : [] ∉ S) :
    kraftWeight (D + 1) S
      = kraftWeight D (branchTails false S) + kraftWeight D (branchTails true S) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    have hnil' : [] ∉ S := fun h ↦ hnil (List.mem_cons_of_mem _ h)
    have hIH := ih hnil'
    cases s with
    | nil => exact absurd (by simp) hnil
    | cons c t =>
      cases c with
      | false =>
        have h0 : branchTails false ((false :: t) :: S) = t :: branchTails false S := by
          simp [branchTails, branchTail?]
        have h1 : branchTails true ((false :: t) :: S) = branchTails true S := by
          simp [branchTails, branchTail?]
        rw [h0, h1]
        simp only [kraftWeight, List.map_cons, List.sum_cons, List.length_cons,
          Nat.add_sub_add_right] at hIH ⊢
        omega
      | true =>
        have h0 : branchTails false ((true :: t) :: S) = branchTails false S := by
          simp [branchTails, branchTail?]
        have h1 : branchTails true ((true :: t) :: S) = t :: branchTails true S := by
          simp [branchTails, branchTail?]
        rw [h0, h1]
        simp only [kraftWeight, List.map_cons, List.sum_cons, List.length_cons,
          Nat.add_sub_add_right] at hIH ⊢
        omega

/-! ### Kraft's inequality and the coverage theorem -/

/-- **Kraft's inequality**: a prefix-free family of strings of length ≤ D has
Kraft weight at most `2 ^ D`. -/
theorem kraftWeight_le (D : Nat) : ∀ S : List (List Bool),
    (∀ s ∈ S, s.length ≤ D) → PrefixFree S → kraftWeight D S ≤ 2 ^ D := by
  induction D with
  | zero =>
    intro S hlen hpf
    cases S with
    | nil => simp [kraftWeight]
    | cons s S' =>
      have hs : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen s (by simp)))
      subst hs
      rw [prefixFree_eq_of_nil_mem hpf (by simp)]
      simp [kraftWeight]
  | succ D ih =>
    intro S hlen hpf
    by_cases hnil : [] ∈ S
    · rw [prefixFree_eq_of_nil_mem hpf hnil]
      simp [kraftWeight]
    · rw [kraftWeight_split D hnil]
      have h0 := ih (branchTails false S) (length_le_of_mem_branchTails hlen)
        (prefixFree_branchTails false hpf)
      have h1 := ih (branchTails true S) (length_le_of_mem_branchTails hlen)
        (prefixFree_branchTails true hpf)
      have hpow : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
      omega

/-- **Kraft-mass coverage** (the mathematical heart of T1, replacing
`check_coverage.py`): a prefix-free family of sign strings of length ≤ D with
full Kraft mass `2 ^ D` covers every length-D string. -/
theorem covers_of_prefixFree_kraft (S : List (List Bool)) (D : Nat)
    (hlen : ∀ s ∈ S, s.length ≤ D)
    (hpf : PrefixFree S)
    (hkraft : kraftWeight D S = 2 ^ D) :
    ∀ x : List Bool, x.length = D → ∃ s ∈ S, s <+: x := by
  induction D generalizing S with
  | zero =>
    intro x hx
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp (by simpa [kraftWeight_zero] using hkraft)
    have hs : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen s (by simp)))
    subst hs
    have hx' : x = [] := List.length_eq_zero_iff.mp hx
    subst hx'
    exact ⟨[], by simp, List.nil_prefix⟩
  | succ D ih =>
    intro x hx
    by_cases hnil : [] ∈ S
    · exact ⟨[], hnil, List.nil_prefix⟩
    · have hsplit := kraftWeight_split D hnil
      have h0le := kraftWeight_le D (branchTails false S)
        (length_le_of_mem_branchTails hlen) (prefixFree_branchTails false hpf)
      have h1le := kraftWeight_le D (branchTails true S)
        (length_le_of_mem_branchTails hlen) (prefixFree_branchTails true hpf)
      have hpow : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
      have h0 : kraftWeight D (branchTails false S) = 2 ^ D := by omega
      have h1 : kraftWeight D (branchTails true S) = 2 ^ D := by omega
      cases x with
      | nil => simp at hx
      | cons b x' =>
        have hx' : x'.length = D := by simpa using hx
        obtain ⟨t, ht, hpre⟩ := ih (branchTails b S)
          (length_le_of_mem_branchTails hlen) (prefixFree_branchTails b hpf)
          (by cases b with | false => exact h0 | true => exact h1) x' hx'
        exact ⟨b :: t, mem_branchTails.mp ht, List.cons_prefix_cons.mpr ⟨rfl, hpre⟩⟩

/-- Coverage in assignment space: every assignment satisfies some cube of the family. -/
theorem cube_cover_of_signs (order : List Nat) (S : List (List Bool))
    (hlen : ∀ s ∈ S, s.length ≤ order.length)
    (hpf : PrefixFree S)
    (hkraft : kraftWeight order.length S = 2 ^ order.length) (a : Nat → Bool) :
    ∃ s ∈ S, Cube.eval a (cubeOfSigns order s) = true := by
  obtain ⟨s, hs, hpre⟩ := covers_of_prefixFree_kraft S order.length hlen hpf hkraft
    (order.map a) (by simp)
  exact ⟨s, hs, (cubeOfSigns_eval_iff order s a (hlen s hs)).mpr hpre⟩

end ConwayO7
