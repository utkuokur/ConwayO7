/-
L5 — the lex section triples (split from `LexSpec` so its computed facts cache).

The gadget triple is proved for *abstract* word arrays and only then instantiated
at `lexXA`/`lexYA`: applying the `GTrip` constructor at the concrete words would
make the elaborator normalize `(specAddLexLeq s lexXA …).top` through the whole
693-position fold.  Instantiation by application never projects, so the concrete
words stay opaque.
-/
import ConwayO7.LexSpec

namespace ConwayO7
namespace Encoder

/-- **The lex-chain triple, for abstract words.** -/
theorem specAddLexLeq_trip (X Y : Array Int)
    (hb : ∀ i, i < X.size →
      X[i]! ≠ 0 ∧ X[i]!.natAbs ≤ 693 ∧ Y[i]! ≠ 0 ∧ Y[i]!.natAbs ≤ 693)
    (P : (Nat → Bool) → Prop)
    (hPle : ∀ a, P a → LexLeq a X Y)
    (hPcongr : ∀ {a b : Nat → Bool}, (∀ v ≤ 693, b v = a v) → P a → P b) :
    GTrip P (fun s ↦ specAddLexLeq s X Y) P := by
  refine ⟨fun s ↦ specAddLexLeq_top_le s X Y, fun s a hw hs hp ↦ ?_⟩
  obtain ⟨a1, hag, hs1, hw1⟩ := specAddLexLeq_sat X Y hb s a hw hs (hPle a hp)
  exact ⟨a1, hag, hs1, hw1, hPcongr (fun v hv ↦ hag v (le_trans hv hw.1)) hp⟩

/-- **The per-generator lex triple** (instantiation by application only). -/
theorem specLexAgainst_trip {ρ : Nat → Nat} (hρ : ρ ∈ lexPerms) :
    GTrip LexInv (fun s ↦ specLexAgainst s (orbitPerm ρ)) LexInv :=
  specAddLexLeq_trip lexXA (lexYA (orbitPerm ρ)) (lex_bounds (orbitPerm_lt_of_mem hρ))
    LexInv (fun _ hp ↦ hp ρ hρ) (fun hag hp ↦ LexInv_congr hag hp)

/-- **The whole lex section, as one triple.** -/
theorem lex_section_trip :
    GTrip LexInv
      (fun s ↦ lexPerms.foldl (fun s ρ ↦ specLexAgainst s (orbitPerm ρ)) s) LexInv :=
  GTrip.foldl_inv _ fun _ hρ ↦ specLexAgainst_trip hρ

end Encoder
end ConwayO7
