/-
L5 — lex-leader completeness, and encoder faithfulness unconditionally.

Each lex generator `ρ` acts on vertices (`permVertex`), compatibly with the orbit
structure (computed facts below); precomposition with `orbitPerm ρ` therefore
relabels the graph by a vertex permutation, preserving strong regularity, and maps
the level-1 unit orbits among themselves preserving their prescribed values.

Starting from the level-1 seed (`sym1_seed`) and minimizing the big-endian word
value over the words reachable by generator precomposition (`Reach`, well-ordering
of `ℕ`), the minimum satisfies every lex constraint (`lex_of_val_le`): its image
under any single generator is again reachable, hence of no smaller value.

This discharges `LexLeaderComplete`, and with it `EncodesInvariantSRG o7cnf`.
-/
import ConwayO7.Assembly
import ConwayO7.Sym1Exists
import ConwayO7.LexVal

namespace ConwayO7
namespace Encoder

/-! ### The generators act on vertices (computed facts) -/

/-- The vertex map of a lex generator. -/
def permVertex (ρ : Nat → Nat) (v : Fin 99) : Fin 99 :=
  ⟨ρ v.val % 99, Nat.mod_lt _ (by omega)⟩

theorem lexPerms_orbit_compat :
    ∀ k : Fin 101, ∀ u v : Fin 99, u ≠ v →
      orbitPerm (lexPerms[(k : Nat)]!) (orbitOf (u, v))
        = orbitOf (permVertex (lexPerms[(k : Nat)]!) u,
            permVertex (lexPerms[(k : Nat)]!) v) := by
  native_decide

theorem lexPerms_vertex_inj :
    ∀ k : Fin 101, ∀ u v : Fin 99,
      permVertex (lexPerms[(k : Nat)]!) u = permVertex (lexPerms[(k : Nat)]!) v →
        u = v := by
  native_decide

theorem lexPerms_sym1 :
    ∀ k : Fin 101, ∀ i : Fin 14, ∃ i' : Fin 14,
      orbitPerm (lexPerms[(k : Nat)]!) (orbitOfN 0 (1 + 7 * i.val))
          = orbitOfN 0 (1 + 7 * i'.val)
        ∧ decide (i'.val < 2) = decide (i.val < 2) := by
  native_decide

theorem mem_lexPerms_index {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) :
    ∃ k : Fin 101, lexPerms[(k : Nat)]! = ρ := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hρ
  have hk101 : k < 101 := lexPerms_length ▸ hk
  refine ⟨⟨k, hk101⟩, ?_⟩
  rw [getElem!_pos lexPerms k hk]
  exact hget

theorem orbit_compat_of_mem {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) :
    ∀ u v : Fin 99, u ≠ v →
      orbitPerm ρ (orbitOf (u, v)) = orbitOf (permVertex ρ u, permVertex ρ v) := by
  obtain ⟨k, hk⟩ := mem_lexPerms_index hρ
  rw [← hk]
  exact lexPerms_orbit_compat k

theorem vertex_inj_of_mem {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) :
    Function.Injective (permVertex ρ) := by
  obtain ⟨k, hk⟩ := mem_lexPerms_index hρ
  rw [← hk]
  exact fun u v h ↦ lexPerms_vertex_inj k u v h

theorem sym1_of_mem {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) (i : Fin 14) :
    ∃ i' : Fin 14, orbitPerm ρ (orbitOfN 0 (1 + 7 * i.val)) = orbitOfN 0 (1 + 7 * i'.val)
      ∧ decide (i'.val < 2) = decide (i.val < 2) := by
  obtain ⟨k, hk⟩ := mem_lexPerms_index hρ
  rw [← hk]
  exact lexPerms_sym1 k i

/-! ### One generator step preserves the semantic side conditions -/

theorem step_srg {ω : Nat → Bool} {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms)
    (h : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    (graphOfOrbits fun o ↦ ω (orbitPerm ρ o)).IsSRGWith 99 14 1 2 := by
  have hinj := vertex_inj_of_mem hρ
  refine isSRGWith_of_iso (SimpleGraph.Iso.symm
    ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), fun {u v} ↦ ?_⟩) h
  show ((permVertex ρ u ≠ permVertex ρ v) ∧
      ω (orbitOf (permVertex ρ u, permVertex ρ v)) = true)
    ↔ (u ≠ v ∧ ω (orbitPerm ρ (orbitOf (u, v))) = true)
  by_cases huv : u = v
  · subst huv
    simp
  · rw [orbit_compat_of_mem hρ u v huv]
    exact ⟨fun ⟨_, hω⟩ ↦ ⟨huv, hω⟩, fun ⟨_, hω⟩ ↦ ⟨fun hc ↦ huv (hinj hc), hω⟩⟩

theorem step_sym1 {ω : Nat → Bool} {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms)
    (h : Sym1Holds (assignOfOrbits ω)) :
    Sym1Holds (assignOfOrbits fun o ↦ ω (orbitPerm ρ o)) := by
  intro i hi
  obtain ⟨i', heq, hdec⟩ := sym1_of_mem hρ ⟨i, hi⟩
  have heq' : orbitPerm ρ (orbitOfN 0 (1 + 7 * i)) = orbitOfN 0 (1 + 7 * i'.val) := heq
  show (fun o ↦ ω (orbitPerm ρ o)) (orbitOfN 0 (1 + 7 * i) + 1 - 1) = decide (i < 2)
  rw [Nat.add_sub_cancel]
  show ω (orbitPerm ρ (orbitOfN 0 (1 + 7 * i))) = decide (i < 2)
  have hbase : ω (orbitOfN 0 (1 + 7 * i'.val) + 1 - 1) = decide (i'.val < 2) :=
    h i'.val i'.isLt
  rw [Nat.add_sub_cancel] at hbase
  rw [heq', hbase]
  exact hdec

/-! ### Reachability and value minimization -/

/-- Words reachable by precomposing lex-generator orbit permutations. -/
inductive Reach (ω : Nat → Bool) : (Nat → Bool) → Prop
  | base : Reach ω ω
  | step {ω' : Nat → Bool} {ρ : Nat → Nat} (h : Reach ω ω') (hρ : ρ ∈ lexPerms) :
      Reach ω fun o ↦ ω' (orbitPerm ρ o)

theorem reach_srg {ω ω' : Nat → Bool} (h : Reach ω ω')
    (hsrg : (graphOfOrbits ω).IsSRGWith 99 14 1 2) :
    (graphOfOrbits ω').IsSRGWith 99 14 1 2 := by
  induction h with
  | base => exact hsrg
  | step _ hρ ih => exact step_srg hρ ih

theorem reach_sym1 {ω ω' : Nat → Bool} (h : Reach ω ω')
    (hs : Sym1Holds (assignOfOrbits ω)) : Sym1Holds (assignOfOrbits ω') := by
  induction h with
  | base => exact hs
  | step _ hρ ih => exact step_sym1 hρ ih

/-- A reachable word of minimal value exists (well-ordering of `ℕ`). -/
theorem exists_min_reach (ω : Nat → Bool) :
    ∃ ωm, Reach ω ωm ∧ ∀ ω', Reach ω ω' → wordVal ωm ≤ wordVal ω' := by
  have hne : {n : Nat | ∃ ω', Reach ω ω' ∧ wordVal ω' = n}.Nonempty :=
    ⟨wordVal ω, ω, Reach.base, rfl⟩
  obtain ⟨ωm, hm, hval⟩ := Nat.sInf_mem hne
  refine ⟨ωm, hm, fun ω' h' ↦ ?_⟩
  rw [hval]
  exact Nat.sInf_le ⟨ω', h', rfl⟩

/-! ### From word order to the encoded lex constraints -/

theorem lexLeq_of_word (ω : Nat → Bool) (p : Nat → Nat)
    (hword : ∀ i, i < 693 → (∀ j, j < i → ω j = ω (p j)) →
      ω i = true → ω (p i) = true) :
    LexLeq (assignOfOrbits ω) lexXA (lexYA p) := by
  have hX : ∀ j, j < 693 → litSat (assignOfOrbits ω) lexXA[j]! = ω j := by
    intro j hj
    rw [lexXA_get j hj, litSat_natCast]
    show ω (j + 1 - 1) = ω j
    rw [Nat.add_sub_cancel]
  have hY : ∀ j, j < 693 → litSat (assignOfOrbits ω) (lexYA p)[j]! = ω (p j) := by
    intro j hj
    rw [lexYA_get p j hj, litSat_natCast]
    show ω (p j + 1 - 1) = ω (p j)
    rw [Nat.add_sub_cancel]
  intro i hi hpre hx
  have hi' : i < 693 := by rw [lexXA_size] at hi; exact hi
  rw [hY i hi']
  refine hword i hi' (fun j hj ↦ ?_) (by rw [← hX i hi']; exact hx)
  have h' := hpre j hj
  rw [hX j (by omega), hY j (by omega)] at h'
  exact h'

/-! ### The completeness theorem -/

/-- **Lex-leader completeness.** -/
theorem lexLeaderComplete : LexLeaderComplete := by
  intro ω hsrg
  obtain ⟨ω₀, hsrg₀, hsym₀⟩ := sym1_seed ω hsrg
  obtain ⟨ωm, hreach, hmin⟩ := exists_min_reach ω₀
  refine ⟨ωm, reach_srg hreach hsrg₀, reach_sym1 hreach hsym₀, ?_⟩
  intro ρ hρ
  exact lexLeq_of_word ωm (orbitPerm ρ)
    (lex_of_val_le (hmin _ (Reach.step hreach hρ)))

/-- **Encoder faithfulness**, unconditionally: `o7.cnf` is satisfiable whenever a
σ₀-invariant srg(99,14,1,2) exists. -/
theorem encodes_o7 : EncodesInvariantSRG o7cnf :=
  encodes_of_lexLeader lexLeaderComplete

end Encoder
end ConwayO7