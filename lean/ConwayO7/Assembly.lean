/-

The master invariant `FullInv` joins the pre-lex semantics (`PreLexInv`: degree
counts, μ-counts, level-1 units) with the lex-leader conditions (`LexInv`).  The
four proved section triples compose into `fullSpec_trip`; the spec-level state is
identified with the emitted `mkO7St` computationally (`specLex_states_agree`, the
same device as `cn_states_eq`).  Every assignment of the orbit block satisfying
`FullInv` therefore extends to a satisfying assignment of the whole generated CNF —
and hence of `o7.cnf` itself, through `mkO7Cnf_eq`.

`encodes_of_lexLeader` then discharges `EncodesInvariantSRG o7cnf` from the one
remaining obligation, lex-leader completeness (`Complete.lean`): every orbit
assignment whose graph is an srg(99,14,1,2) has a companion assignment — a
relabeled copy of the same graph — that is an srg satisfying the level-1 choice
and all 101 lex constraints.
-/
import ConwayO7.LexTrip
import ConwayO7.Bridge
import ConwayO7.Pipeline
import ConwayO7.Data.EncoderMatch

namespace ConwayO7
namespace Encoder

open SeqSpec

/-! ### The master invariant -/

/-- All semantic conditions of the four generator sections. -/
def FullInv (a : Nat → Bool) : Prop := PreLexInv a ∧ LexInv a

theorem deg_section_tripF :
    GTrip FullInv (fun s ↦ (List.finRange 99).foldl degreeStep s) FullInv :=
  deg_section_trip.adapt (fun _ hp ↦ hp.1.1) fun _ _ hag hp hq ↦
    ⟨⟨hq, CnInv_congr hag hp.1.2.1, Sym1Holds_congr hag hp.1.2.2⟩, LexInv_congr hag hp.2⟩

theorem cn_section_tripF :
    GTrip FullInv (fun s ↦ (List.range 693).foldl specCnStep s) FullInv :=
  cn_section_trip.adapt (fun _ hp ↦ hp.1.2.1) fun _ _ hag hp hq ↦
    ⟨⟨DegInv_congr hag hp.1.1, hq, Sym1Holds_congr hag hp.1.2.2⟩, LexInv_congr hag hp.2⟩

theorem sym1_section_tripF :
    GTrip FullInv (fun s ↦ (List.range 14).foldl sym1Step s) FullInv :=
  sym1_section_trip.adapt (fun _ hp ↦ hp.1.2.2) fun _ _ hag hp hq ↦
    ⟨⟨DegInv_congr hag hp.1.1, CnInv_congr hag hp.1.2.1, hq⟩, LexInv_congr hag hp.2⟩

theorem lex_section_tripF :
    GTrip FullInv
      (fun s ↦ lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ)) s) FullInv :=
  lex_section_trip.adapt (fun _ hp ↦ hp.2) fun _ _ hag hp hq ↦
    ⟨PreLexInv_congr hag hp.1, hq⟩

set_option maxRecDepth 8000 in
/-- The composed spec-level pipeline of all four sections. -/
theorem fullSpec_trip :
    GTrip FullInv
      (fun s ↦ lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ))
        ((List.range 14).foldl sym1Step
          ((List.range 693).foldl specCnStep
            ((List.finRange 99).foldl degreeStep s))))
      FullInv :=
  deg_section_tripF.comp (cn_section_tripF.comp
    (sym1_section_tripF.comp lex_section_tripF))

/-! ### From the spec lex section to the emitted one -/

/-- The spec-level and imperative lex sections produce the same state on the
concrete pipeline (computed). -/
theorem specLex_states_agree :
    (lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ)) preLexSt).cls
        = mkO7St.cls ∧
      (lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ)) preLexSt).top
        = mkO7St.top := by
  native_decide

/-! ### Full-generator satisfiability -/

/-- **Generator satisfiability**: any orbit assignment with all four semantic
invariants extends (above variable 693) to satisfy every clause of the generated
CNF. -/
theorem mkO7St_sat (a : Nat → Bool) (hp : FullInv a) :
    ∃ a', (∀ v ≤ 693, a' v = a v) ∧ SatAll a' mkO7St := by
  obtain ⟨a', hag, hsat, _, _⟩ :=
    fullSpec_trip.sat ⟨693, #[]⟩ a WF_init (satAll_init a 693) hp
  have heq : lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ))
      ((List.range 14).foldl sym1Step
        ((List.range 693).foldl specCnStep
          ((List.finRange 99).foldl degreeStep ⟨693, #[]⟩)))
      = mkO7St := by
    show lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ))
      ((List.range 14).foldl sym1Step
        ((List.range 693).foldl specCnStep afterDegrees)) = mkO7St
    rw [cn_states_eq]
    exact St.ext' specLex_states_agree.2 specLex_states_agree.1
  rw [heq] at hsat
  exact ⟨a', hag, hsat⟩

/-! ### Encoder faithfulness, modulo lex-leader completeness -/

/-- **Lex-leader completeness** (the last open layer, `Complete.lean`): every orbit
assignment whose graph is an srg(99,14,1,2) admits a companion assignment that is
still such an srg and satisfies the level-1 choice and all 101 lex constraints. -/
def LexLeaderComplete : Prop :=
  ∀ ω : Nat → Bool, (graphOfOrbits ω).IsSRGWith 99 14 1 2 →
    ∃ ω' : Nat → Bool, (graphOfOrbits ω').IsSRGWith 99 14 1 2 ∧
      Sym1Holds (assignOfOrbits ω') ∧ LexInv (assignOfOrbits ω')

/-- **Encoder faithfulness** from lex-leader completeness: `o7.cnf` is satisfiable
whenever a σ₀-invariant srg(99,14,1,2) exists. -/
theorem encodes_of_lexLeader (hcomplete : LexLeaderComplete) :
    EncodesInvariantSRG o7cnf := by
  intro H instH hH hinv
  letI := instH
  obtain ⟨ω, heq⟩ := (invariant_iff_exists_orbitFun H).mp hinv
  have hsrg : (graphOfOrbits ω).IsSRGWith 99 14 1 2 :=
    isSRGWith_of_iso
      (SimpleGraph.Iso.symm ⟨Equiv.refl _, fun {a b} ↦ by rw [heq]; exact Iff.rfl⟩) hH
  obtain ⟨ω', hsrg', hsym1, hlex⟩ := hcomplete ω hsrg
  have hpre := preLexInv_of_srg ω' hsrg' hsym1
  obtain ⟨a', _, hsat⟩ := mkO7St_sat (assignOfOrbits ω') ⟨hpre, hlex⟩
  obtain ⟨b, hb⟩ := sat_mkO7Cnf_of_satAll hsat
  rw [mkO7Cnf_eq] at hb
  exact ⟨b, hb⟩

end Encoder
end ConwayO7
