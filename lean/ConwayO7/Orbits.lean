/-
The orbit reduction.

`sigma0` acts on the `99 choose 2 = 4851` unordered vertex pairs of `Fin 99`.  The encoder
(`tools/conway_o7.py`, `pair_orbits`) walks the pairs in lexicographic order and
numbers the orbits `0, 1, 2, …`; one CNF variable per orbit replaces one variable per
pair.  This file reproduces that computation *exactly* (`orbitOf`, `orbitRep`,
`numOrbits`) and proves, on the concrete data:

  * there are 693 orbits, each of size 7 (no pair is fixed — `pairStep_ne`);
  * `orbitOf` is `sigma0`-invariant and every pair is reachable from its orbit's
    representative in < 7 steps.

On top sits the semantic **orbit reduction** (`invariant_iff_exists_orbitFun`):
a graph on `Fin 99` is `sigma0`-invariant  ⟺  it is `graphOfOrbits ω` for some
assignment `ω` of the 693 orbit booleans.  This is the encoder's variable reduction,
verified; the CNF layer will connect `ω o` to DIMACS variable `o + 1`.

The concrete facts are established by `native_decide`; the bridge theorems are structural.
-/
import ConwayO7.Canonical

namespace ConwayO7

/-! ### The pair action -/

/-- Normalize an unordered pair: smaller component first. -/
def normalizePair (p : Fin 99 × Fin 99) : Fin 99 × Fin 99 :=
  if p.1 ≤ p.2 then p else (p.2, p.1)

/-- One `sigma0` step on normalized pairs — the map `cur ↦ norm(σ(cur))` of
`pair_orbits` in `conway_o7.py`. -/
def pairStep (p : Fin 99 × Fin 99) : Fin 99 × Fin 99 :=
  normalizePair (sigma0 p.1, sigma0 p.2)

/-- All normalized pairs `(u, v)`, `u < v`, in the encoder's lexicographic order. -/
def allPairs : List (Fin 99 × Fin 99) :=
  (List.finRange 99).flatMap fun u ↦
    ((List.finRange 99).filter fun v ↦ u < v).map fun v ↦ (u, v)

/-- Flat index of a pair into the orbit table. -/
def pairIdx (p : Fin 99 × Fin 99) : Nat := p.1.val * 99 + p.2.val

/-- The orbit table and representative list, built exactly like `pair_orbits`:
scan `allPairs` in order; each unassigned pair opens a new orbit, whose 7 iterates
under `pairStep` all receive the next orbit id, and the opening pair becomes the
orbit's representative. -/
def orbitBuild : Array (Option Nat) × Array (Fin 99 × Fin 99) :=
  allPairs.foldl
    (fun (st : Array (Option Nat) × Array (Fin 99 × Fin 99)) p ↦
      if (st.1.getD (pairIdx p) none).isSome then st
      else
        (((List.range 7).map fun k ↦ pairStep^[k] p).foldl
            (fun t q ↦ t.set! (pairIdx q) (some st.2.size)) st.1,
          st.2.push p))
    (Array.replicate (99 * 99) none, #[])

/-- The encoder's orbit id of a pair. -/
def orbitOf (p : Fin 99 × Fin 99) : Nat :=
  (orbitBuild.1.getD (pairIdx (normalizePair p)) none).getD 100000000

/-- The representative of orbit `o`. -/
def orbitRep (o : Nat) : Fin 99 × Fin 99 := orbitBuild.2.getD o (0, 0)

/-- The number of pair-orbits. -/
def numOrbits : Nat := orbitBuild.2.size

/-! ### The concrete orbit facts (computed over all 4851 pairs) -/

/-- 4851 pairs fall into 693 orbits — the encoder's variable count. -/
theorem numOrbits_eq : numOrbits = 693 := by native_decide

/-- **No pair is fixed** (the soundness remark of `conway_o7.py`): every orbit has
size exactly 7, so the orbit reduction loses nothing. -/
theorem pairStep_ne : ∀ u v : Fin 99, u < v → pairStep (u, v) ≠ (u, v) := by
  native_decide

/-- `orbitOf` is invariant under the pair action. -/
theorem orbitOf_pairStep : ∀ u v : Fin 99, u < v →
    orbitOf (pairStep (u, v)) = orbitOf (u, v) := by native_decide

theorem orbitOf_lt : ∀ u v : Fin 99, u < v → orbitOf (u, v) < 693 := by native_decide

/-- Every pair is reached from its orbit's representative within 7 steps. -/
theorem orbitRep_reaches : ∀ u v : Fin 99, u < v →
    ∃ k ∈ Finset.range 7, pairStep^[k] (orbitRep (orbitOf (u, v))) = (u, v) := by
  native_decide

/-! ### Normalization lemmas -/

theorem normalizePair_swap (u v : Fin 99) : normalizePair (u, v) = normalizePair (v, u) := by
  unfold normalizePair
  rcases le_total u v with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp
    · rw [if_pos h, if_neg (not_le.mpr hlt)]
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp
    · rw [if_neg (not_le.mpr hlt), if_pos h]

theorem normalizePair_lt {u v : Fin 99} (h : u ≠ v) :
    (normalizePair (u, v)).1 < (normalizePair (u, v)).2 := by
  unfold normalizePair
  rcases le_total u v with hle | hle
  · rw [if_pos hle]; exact lt_of_le_of_ne hle h
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne hle (Ne.symm h)))]
    exact lt_of_le_of_ne hle (Ne.symm h)

theorem orbitOf_swap (u v : Fin 99) : orbitOf (u, v) = orbitOf (v, u) := by
  unfold orbitOf
  rw [normalizePair_swap]

theorem normalizePair_idem (p : Fin 99 × Fin 99) :
    normalizePair (normalizePair p) = normalizePair p := by
  by_cases h : p.1 ≤ p.2
  · have h1 : normalizePair p = p := if_pos h
    rw [h1]
    exact h1
  · have h1 : normalizePair p = (p.2, p.1) := if_neg h
    rw [h1]
    exact if_pos (le_of_lt (lt_of_not_ge h))

theorem orbitOf_normalizePair (p : Fin 99 × Fin 99) : orbitOf (normalizePair p) = orbitOf p := by
  unfold orbitOf
  rw [normalizePair_idem]

/-- `orbitOf` is `sigma0`-invariant on arbitrary (not necessarily normalized) pairs. -/
theorem orbitOf_sigma0 (u v : Fin 99) (h : u ≠ v) :
    orbitOf (sigma0 u, sigma0 v) = orbitOf (u, v) := by
  have key : ∀ a b : Fin 99, a < b → orbitOf (sigma0 a, sigma0 b) = orbitOf (a, b) := by
    intro a b hab
    have h1 := orbitOf_pairStep a b hab
    rw [show pairStep (a, b) = normalizePair (sigma0 a, sigma0 b) from rfl,
      orbitOf_normalizePair] at h1
    exact h1
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact key u v hlt
  · rw [orbitOf_swap, orbitOf_swap u v]
    exact key v u hlt

/-! ### The orbit reduction (semantic bridge) -/

/-- The graph on `Fin 99` determined by an assignment of the orbit booleans. -/
def graphOfOrbits (ω : Nat → Bool) : SimpleGraph (Fin 99) where
  Adj u v := u ≠ v ∧ ω (orbitOf (u, v)) = true
  symm := by
    intro u v ⟨hne, hω⟩
    exact ⟨hne.symm, by rwa [orbitOf_swap v u]⟩
  loopless := ⟨fun u h ↦ h.1 rfl⟩

instance (ω : Nat → Bool) : DecidableRel (graphOfOrbits ω).Adj :=
  fun _ _ ↦ instDecidableAnd

/-- `graphOfOrbits ω` is always `sigma0`-invariant. -/
theorem graphOfOrbits_invariant (ω : Nat → Bool) (u v : Fin 99) :
    (graphOfOrbits ω).Adj (sigma0 u) (sigma0 v) ↔ (graphOfOrbits ω).Adj u v := by
  show (sigma0 u ≠ sigma0 v ∧ _) ↔ (u ≠ v ∧ _)
  by_cases h : u = v
  · subst h; simp
  · have hσ : sigma0 u ≠ sigma0 v := fun hc ↦ h (sigma0.injective hc)
    rw [orbitOf_sigma0 u v h]
    exact ⟨fun ⟨_, hω⟩ ↦ ⟨h, hω⟩, fun ⟨_, hω⟩ ↦ ⟨hσ, hω⟩⟩

section Converse

variable {H : SimpleGraph (Fin 99)}

theorem adj_normalizePair (p : Fin 99 × Fin 99) :
    H.Adj (normalizePair p).1 (normalizePair p).2 ↔ H.Adj p.1 p.2 := by
  unfold normalizePair
  split
  · exact Iff.rfl
  · exact H.adj_comm _ _

theorem adj_pairStep (hinv : ∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v)
    (p : Fin 99 × Fin 99) :
    H.Adj (pairStep p).1 (pairStep p).2 ↔ H.Adj p.1 p.2 := by
  unfold pairStep
  rw [adj_normalizePair]
  exact hinv p.1 p.2

theorem adj_pairStep_iterate (hinv : ∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v)
    (p : Fin 99 × Fin 99) (k : ℕ) :
    H.Adj (pairStep^[k] p).1 (pairStep^[k] p).2 ↔ H.Adj p.1 p.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', adj_pairStep hinv, ih]

/-- The orbit assignment read off an invariant graph: the value of orbit `o` is the
adjacency of its representative pair. -/
def orbitFunOf (H : SimpleGraph (Fin 99)) [DecidableRel H.Adj] : Nat → Bool :=
  fun o ↦ decide (H.Adj (orbitRep o).1 (orbitRep o).2)

/-- **Faithfulness of the orbit reduction**: an invariant graph is reconstructed
exactly from its 693 orbit booleans. -/
theorem graphOfOrbits_orbitFunOf [DecidableRel H.Adj]
    (hinv : ∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v) :
    graphOfOrbits (orbitFunOf H) = H := by
  ext u v
  show (u ≠ v ∧ orbitFunOf H (orbitOf (u, v)) = true) ↔ H.Adj u v
  by_cases h : u = v
  · subst h
    simp
  · -- reduce to the normalized pair
    have hnorm : H.Adj (normalizePair (u, v)).1 (normalizePair (u, v)).2 ↔ H.Adj u v :=
      adj_normalizePair (u, v)
    have hlt : (normalizePair (u, v)).1 < (normalizePair (u, v)).2 := normalizePair_lt h
    obtain ⟨k, -, hk⟩ := orbitRep_reaches _ _ hlt
    -- re-type `hk` through pair eta so it speaks about `normalizePair (u, v)` itself
    have hk' : pairStep^[k] (orbitRep (orbitOf (normalizePair (u, v)))) = normalizePair (u, v) :=
      hk
    have hrep := adj_pairStep_iterate hinv (orbitRep (orbitOf (normalizePair (u, v)))) k
    rw [hk'] at hrep
    -- hrep : H.Adj (normalizePair (u, v)).1 (normalizePair (u, v)).2
    --      ↔ H.Adj (orbitRep _).1 (orbitRep _).2
    have hkey : orbitFunOf H (orbitOf (u, v)) = true ↔ H.Adj u v := by
      rw [← orbitOf_normalizePair (u, v)]
      constructor
      · intro hω
        exact hnorm.mp (hrep.mpr (of_decide_eq_true hω))
      · intro hadj
        exact decide_eq_true (hrep.mp (hnorm.mpr hadj))
    exact ⟨fun ⟨_, hω⟩ ↦ hkey.mp hω, fun hadj ↦ ⟨h, hkey.mpr hadj⟩⟩

end Converse

/-- **The orbit reduction, packaged**: a graph on `Fin 99` is `sigma0`-invariant iff it
is the graph of an orbit assignment.  This is the encoder's reduction from 4851 edge
variables to 693 orbit variables, verified. -/
theorem invariant_iff_exists_orbitFun (H : SimpleGraph (Fin 99)) [DecidableRel H.Adj] :
    (∀ u v, H.Adj (sigma0 u) (sigma0 v) ↔ H.Adj u v) ↔
      ∃ ω : Nat → Bool, graphOfOrbits ω = H := by
  constructor
  · intro hinv
    exact ⟨orbitFunOf H, graphOfOrbits_orbitFunOf hinv⟩
  · rintro ⟨ω, rfl⟩
    exact graphOfOrbits_invariant ω

end ConwayO7
