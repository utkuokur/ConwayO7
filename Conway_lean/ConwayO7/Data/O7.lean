/-
The concrete data layer: `o7.cnf`, embedded byte-for-byte.

`include_str` copies the artifact files into this module at compile time, so `o7cnf`
is a term built from the *exact bytes* of the file whose SHA-256 hash
are pinned below (and recorded in the artifact's `SHA256SUMS`) — the same files
`verify_final.sh` / `check_one.sh` feed to the LRAT checkers.

The `_bytes` theorems close the byte gap: serializing the parsed terms reproduces the
embedded strings *exactly*.  So the only remaining translation trust is the ~60-line
convention in `ConwayO7/Dimacs.lean`, which a referee reads directly.

These theorems are established by `native_decide` — the check runs as compiled code,
so they carry the `Lean.ofReduceBool` axiom (trusting Lean's compiler for these
computations), exactly as Lean's own `bv_decide` does for its LRAT replay.  The rest
of the development (T1, L2, L3, Step 5, pipeline) remains on the three standard axioms.
-/
import ConwayO7.Dimacs

namespace ConwayO7

/-- The bytes of `artifact/o7.cnf` (SHA-256 `o7DimacsSha256`, pinned in `SHA256SUMS`). -/
def o7Dimacs : String := include_str "../../../artifact/o7.cnf"

/-- SHA-256 of `artifact/o7.cnf`, the file cake_lpr / lrat-check consumed.
Recompute with `sha256sum artifact/o7.cnf` and compare with `artifact/SHA256SUMS`. -/
def o7DimacsSha256 : String :=
  "0cfe0a7e5d673989bfaf25cfdd8d88028bd792bd35406e248f480cde1655e908"

/-- **The formula.**  `o7.cnf` as a `Std.Sat.CNF Nat`, clause `i` of the file at
index `i-1` — the clause numbering the LRAT certificates refer to. -/
def o7cnf : Std.Sat.CNF Nat := Dimacs.parseDimacs o7Dimacs

/-! ### Byte-identity and header sanity (the "glue", machine-checked) -/

/-- **Byte identity for the formula**: re-serializing `o7cnf` reproduces `o7.cnf`
exactly, including its header.  Lean's theorems and the LRAT certificates are about
the same bytes. -/
theorem o7cnf_bytes : Dimacs.serializeDimacs 432882 1131708 o7cnf = o7Dimacs := by
  native_decide

/-- The header's clause count matches the parsed term. -/
theorem o7cnf_size : o7cnf.clauses.size = 1131708 := by native_decide

end ConwayO7
