/-
The target architecture of the Lean side of the Conway order-7 certificate.

  T1 (coverage, THIS FILE — schema fully proved):
      (∀ i ≤ 98536, Unsat (withCube o7cnf cubeᵢ))  →  Unsat o7cnf

  T2 (encoding faithfulness, IN PROGRESS — mathlib layer):
      Unsat o7cnf  →  ¬ ∃ (G : SimpleGraph (Fin 99)) (_ : G.IsSRGWith 99 14 1 2)
                          (σ : G.Aut), orderOf σ = 7
      and, via Cauchy's theorem (`exists_prime_orderOf_dvd_card`):
      …  →  ∀ G, G.IsSRGWith 99 14 1 2 → ¬ (7 ∣ Nat.card G.Aut)

  External hypothesis discharge:  cake_lpr (HOL4-verified LRAT checker) certifies
      Unsat (withCube o7cnf cubeᵢ)   for every manifest entry i,
  on files whose SHA-256 hashes must equal those of the data embedded here
  (the "glue": an auditable byte-identity, recorded in the artifact's SHA256SUMS).
  Alternatively, `Std.Tactic.BVDecide.LRAT.check_sound` can discharge sampled
  cubes fully inside Lean, with zero translation gap — the statements below are
  over the standard library's `Std.Sat.CNF`.

  Trusted base once both theorems land: cake_lpr + the Lean kernel + this file's
  *statements* (which a human must read) + the hash comparison.  In particular
  `check_coverage.py` and all solver-side tooling leave the trusted base.

T2's roadmap (per the encoder `conway_o7.py`):
  L2  statement layer      — mathlib: `IsSRGWith`, graph automorphisms, Cauchy.
                             DONE (sorry-free): ConwayO7/Aut.lean
  L3  cycle-type lemma     — an order-7 automorphism of an srg(99,14,1,2) has
                             exactly one fixed vertex; conjugacy ⟹ WLOG the
                             canonical σ = [1, 7¹⁴].  Published as Cesarz–Woldar
                             (arXiv:2308.02978) Lemma 2.2; proof in
                             docs/L3_cycle_type.md.
                             DONE (sorry-free): ConwayO7/CycleType.lean
                             (`card_filter_fixed_eq_one`, `cycleType_autToPerm`);
                             Step 5 (WLOG the encoder's σ₀, incl. `sigma0` itself)
                             DONE (sorry-free): ConwayO7/Canonical.lean
                             (`exists_sigma0_invariant`,
                              `seven_not_dvd_card_aut_of_no_sigma0_invariant`)
  L4  encoder faithfulness — orbit variables + cardinality constraints:
                             satisfying assignment ⟺ σ-invariant srg             (medium–hard)
  L5  symmetry breaking    — the sym-level-3 clauses are *complete*: every
                             solution class has a representative satisfying
                             them (the soundness-critical step)                   (hardest)
-/
import ConwayO7.Coverage

open Std.Sat

namespace ConwayO7

/-- **T1, certificate schema — sorry-free.**  If the cube family is a prefix-free
family of sign strings along a branching order with full Kraft mass (the facts
`check_coverage.py` checks numerically previously),
and every cube-augmented formula is unsatisfiable (the facts
cake_lpr certifies), then the base CNF is unsatisfiable. -/
theorem unsat_of_prefix_cover (F : CNF Nat) (order : List Nat) (S : List (List Bool))
    (hlen : ∀ s ∈ S, s.length ≤ order.length)
    (hpf : PrefixFree S)
    (hkraft : kraftWeight order.length S = 2 ^ order.length)
    (hunsat : ∀ s ∈ S, CNF.Unsat (withCube F (cubeOfSigns order s))) :
    CNF.Unsat F := by
  refine unsat_of_cubes F (S.map (cubeOfSigns order)) ?_ ?_
  · intro a
    obtain ⟨s, hs, hsat⟩ := cube_cover_of_signs order S hlen hpf hkraft a
    exact ⟨cubeOfSigns order s, List.mem_map.mpr ⟨s, hs, rfl⟩, hsat⟩
  · intro c hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact hunsat s hs

end ConwayO7
