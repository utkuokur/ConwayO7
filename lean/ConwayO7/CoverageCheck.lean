/-
Layer L1½ — a verified O(n log n) coverage checker.

The concrete tiling has 98,536 cubes, so checking `PrefixFree` literally
(`List.Pairwise`, ~5·10⁹ pairs) is infeasible.  `checkCover` instead sorts the sign
strings lexicographically and checks *adjacent pairs only*; `cover_of_checkCover`
proves this sound.  The key order-theoretic fact (`prefix_of_lexLe_of_lexLe`): in
lexicographic order everything between a string `s` and an extension of `s` is itself
an extension of `s`.  Hence if any prefix relation existed in the family, one would
already occur between sorted neighbours.

`unsat_of_checked_cover` packages T1 with the computable check: the coverage
obligations of `unsat_of_prefix_cover` reduce to a single `checkCover … = true`
computation on the concrete cube data.
-/
import ConwayO7.Main

namespace ConwayO7

/-! ### Executable lexicographic order on sign strings -/

/-- Lexicographic `≤` on sign strings, with `false < true` and `[] ≤ s`. -/
def lexLe : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if a = b then lexLe s t else !a && b

theorem lexLe_total : ∀ s t : List Bool, lexLe s t || lexLe t s
  | [], t => by simp [lexLe]
  | _ :: _, [] => by simp [lexLe]
  | a :: s, b :: t => by
    by_cases h : a = b
    · subst h
      simpa [lexLe] using lexLe_total s t
    · cases a <;> cases b <;> simp_all [lexLe]

theorem lexLe_trans : ∀ s t u : List Bool, lexLe s t → lexLe t u → lexLe s u
  | [], _, _ => by simp [lexLe]
  | _ :: _, [], _ => by simp [lexLe]
  | _ :: _, _ :: _, [] => by simp [lexLe]
  | a :: s, b :: t, c :: u => by
    intro h1 h2
    by_cases hab : a = b <;> by_cases hbc : b = c
    · subst hab; subst hbc
      simp only [lexLe] at h1 h2 ⊢
      exact lexLe_trans s t u h1 h2
    · subst hab
      cases a <;> cases c <;> simp_all [lexLe]
    · subst hbc
      cases a <;> cases b <;> simp_all [lexLe]
    · cases a <;> cases b <;> cases c <;> simp_all [lexLe]

theorem lexLe_antisymm : ∀ s t : List Bool, lexLe s t → lexLe t s → s = t
  | [], [], _, _ => rfl
  | [], _ :: _, _, h2 => by simp [lexLe] at h2
  | _ :: _, [], h1, _ => by simp [lexLe] at h1
  | a :: s, b :: t, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      simp only [lexLe] at h1 h2
      rw [lexLe_antisymm s t h1 h2]
    · cases a <;> cases b <;> simp_all [lexLe]

theorem lexLe_of_prefix : ∀ {s t : List Bool}, s <+: t → lexLe s t = true := by
  intro s
  induction s with
  | nil => intro t _; rfl
  | cons a s ih =>
    intro t hpre
    cases t with
    | nil => exact absurd (List.prefix_nil.mp hpre) (by simp)
    | cons b t =>
      obtain ⟨rfl, hpre'⟩ := List.cons_prefix_cons.mp hpre
      simpa [lexLe] using ih hpre'

/-- **The block property of lexicographic order**: everything between `s` and an
extension of `s` is itself an extension of `s`. -/
theorem prefix_of_lexLe_of_lexLe : ∀ {s t u : List Bool},
    s <+: t → lexLe s u → lexLe u t → s <+: u
  | [], _, _, _, _, _ => List.nil_prefix
  | _ :: _, _, [], _, h1, _ => by simp [lexLe] at h1
  | s@(_ :: _), [], _, hpre, _, _ => absurd (List.prefix_nil.mp hpre) (by simp)
  | a :: s, b :: t, c :: u, hpre, h1, h2 => by
    obtain ⟨rfl, hpre'⟩ := List.cons_prefix_cons.mp hpre
    by_cases hac : a = c
    · subst hac
      simp only [lexLe] at h1 h2
      exact List.cons_prefix_cons.mpr ⟨rfl, prefix_of_lexLe_of_lexLe hpre' h1 h2⟩
    · cases a <;> cases c <;> simp_all [lexLe]

/-! ### The adjacent-pairs check and its soundness -/

/-- One pass over a (sorted) family: no member is a prefix of its successor. -/
def adjacentOk : List (List Bool) → Bool
  | s :: t :: r => !s.isPrefixOf t && adjacentOk (t :: r)
  | _ => true

/-- On a lex-sorted family, the adjacent check implies full pairwise prefix-freeness. -/
theorem pairwise_of_sorted_adjacent : ∀ {l : List (List Bool)},
    l.Pairwise (fun s t ↦ lexLe s t = true) → adjacentOk l = true →
    l.Pairwise fun s t ↦ ¬s <+: t ∧ ¬t <+: s := by
  intro l
  induction l with
  | nil => exact fun _ _ ↦ List.Pairwise.nil
  | cons s l ih =>
    intro hsort hadj
    cases l with
    | nil => simp
    | cons t r =>
      obtain ⟨hs, hsort'⟩ := List.pairwise_cons.mp hsort
      obtain ⟨hst, hadj'⟩ : s.isPrefixOf t = false ∧ adjacentOk (t :: r) = true := by
        simpa [adjacentOk] using hadj
      refine List.pairwise_cons.mpr ⟨?_, ih hsort' hadj'⟩
      intro u hu
      have hnpre : ¬s <+: u := by
        intro hpre
        have h1 : lexLe s t = true := hs t (by simp)
        have h2 : lexLe t u = true := by
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact lexLe_of_prefix (List.prefix_refl _)
          · exact (List.pairwise_cons.mp hsort').1 u hu'
        have : s <+: t := prefix_of_lexLe_of_lexLe hpre h1 h2
        rw [← List.isPrefixOf_iff_prefix, hst] at this
        exact Bool.false_ne_true this
      refine ⟨hnpre, fun hpre ↦ ?_⟩
      have heq : s = u := lexLe_antisymm s u (hs u hu) (lexLe_of_prefix hpre)
      exact hnpre (heq ▸ List.prefix_refl s)

/-! ### The full check -/

/-- **The executable coverage check** replacing `check_coverage.py` in the trusted base:
all sign strings fit the branching depth, the lex-sorted family has no adjacent prefix
pair (hence is an antichain), and the exact Kraft mass is `2^D` (hence the antichain is
maximal: every assignment is covered). -/
def checkCover (D : Nat) (S : List (List Bool)) : Bool :=
  S.all (fun s ↦ decide (s.length ≤ D)) &&
    adjacentOk (S.mergeSort lexLe) &&
    decide (kraftWeight D S = 2 ^ D)

/-- Soundness of `checkCover`: it implies the three coverage hypotheses of
`unsat_of_prefix_cover`. -/
theorem cover_of_checkCover {D : Nat} {S : List (List Bool)} (h : checkCover D S = true) :
    (∀ s ∈ S, s.length ≤ D) ∧ PrefixFree S ∧ kraftWeight D S = 2 ^ D := by
  obtain ⟨⟨h1, h2⟩, h3⟩ :
      ((∀ s ∈ S, s.length ≤ D) ∧ adjacentOk (S.mergeSort lexLe) = true) ∧
        kraftWeight D S = 2 ^ D := by
    simpa [checkCover, Bool.and_eq_true] using h
  refine ⟨h1, ?_, h3⟩
  have hsorted := List.pairwise_mergeSort (le := lexLe) lexLe_trans lexLe_total S
  have hpw := pairwise_of_sorted_adjacent hsorted h2
  exact ((S.mergeSort_perm lexLe).pairwise_iff fun h ↦ ⟨h.2, h.1⟩).mp hpw

/-- **T1, fully computable form**: the coverage side of the certificate reduces to one
`checkCover` computation on the concrete cube data. -/
theorem unsat_of_checked_cover (F : Std.Sat.CNF Nat) (order : List Nat)
    (S : List (List Bool)) (hchk : checkCover order.length S = true)
    (hunsat : ∀ s ∈ S, Std.Sat.CNF.Unsat (withCube F (cubeOfSigns order s))) :
    Std.Sat.CNF.Unsat F := by
  obtain ⟨h1, h2, h3⟩ := cover_of_checkCover hchk
  exact unsat_of_prefix_cover F order S h1 h2 h3 hunsat

end ConwayO7
