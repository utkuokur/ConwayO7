/-
The 693-bit orbit word as a big-endian number.

Minimizing `wordVal` over a set of words closed under the lex generators yields a
word that is lexicographically ≤ all its generator images — `lex_of_val_le` is the
only fact needed: value order refines the prefix order position by position.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ConwayO7
namespace Encoder

/-- The orbit word read as a big-endian 693-bit number. -/
def wordVal (ω : Nat → Bool) : Nat :=
  ∑ i ∈ Finset.range 693, if ω i then 2 ^ (692 - i) else 0

theorem sum_two_pow (n : Nat) : ∑ t ∈ Finset.range n, 2 ^ t = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- Value order refines lexicographic order: if `u`'s value is not larger and the
words agree strictly before `i`, then `u` cannot beat `w` at `i`. -/
theorem lex_of_val_le {u w : Nat → Bool} (h : wordVal u ≤ wordVal w) :
    ∀ i, i < 693 → (∀ j, j < i → u j = w j) → u i = true → w i = true := by
  intro i hi hpre hui
  by_contra hwi
  -- decompose both values at position i
  have hsplit : ∀ b : Nat → Bool,
      wordVal b = (∑ j ∈ Finset.range i, if b j then 2 ^ (692 - j) else 0) +
        ((if b i then 2 ^ (692 - i) else 0) +
          ∑ j ∈ Finset.Ico (i + 1) 693, if b j then 2 ^ (692 - j) else 0) := by
    intro b
    rw [wordVal, ← Finset.sum_range_add_sum_Ico _ (by omega : i + 1 ≤ 693),
      Finset.sum_range_succ, add_assoc]
  -- the prefixes agree
  have hpref : (∑ j ∈ Finset.range i, if u j then 2 ^ (692 - j) else 0)
      = ∑ j ∈ Finset.range i, if w j then 2 ^ (692 - j) else 0 :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hpre j (Finset.mem_range.mp hj)]
  -- the tail of `w` is dominated by the bit at `i`
  have htail : (∑ j ∈ Finset.Ico (i + 1) 693, if w j then 2 ^ (692 - j) else 0)
      ≤ 2 ^ (692 - i) - 1 := by
    calc (∑ j ∈ Finset.Ico (i + 1) 693, if w j then 2 ^ (692 - j) else 0)
        ≤ ∑ j ∈ Finset.Ico (i + 1) 693, 2 ^ (692 - j) :=
          Finset.sum_le_sum fun j _ ↦ by split <;> simp
      _ = ∑ t ∈ Finset.range (692 - i), 2 ^ (692 - (i + 1 + t)) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have : 693 - (i + 1) = 692 - i := by omega
          rw [this]
      _ = ∑ t ∈ Finset.range (692 - i), 2 ^ (692 - i - 1 - t) :=
          Finset.sum_congr rfl fun t _ ↦ by
            have : 692 - (i + 1 + t) = 692 - i - 1 - t := by omega
            rw [this]
      _ = ∑ t ∈ Finset.range (692 - i), 2 ^ t := Finset.sum_range_reflect _ _
      _ = 2 ^ (692 - i) - 1 := sum_two_pow _
  -- assemble the contradiction
  have hu := hsplit u
  have hw' := hsplit w
  rw [if_pos hui] at hu
  rw [if_neg hwi] at hw'
  have hpos : 1 ≤ 2 ^ (692 - i) := Nat.one_le_two_pow
  omega

end Encoder
end ConwayO7