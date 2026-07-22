/-
DIMACS ↔ `Std.Sat.CNF` — the audited byte-level convention.

This file fixes, once, the translation between the artifact's text files and the Lean
terms the theorems talk about.  It is deliberately tiny: a human referee reads THIS
file, and the byte-identity theorems in `ConwayO7/Data/O7.lean` (checked by running
the code below over the actual artifact bytes) do the rest.

The convention:

  DIMACS token        Lean term (`Std.Sat.Literal Nat = Nat × Bool`)
  ------------        ----------------------------------------------
  `704`               `(703, true)`      -- variable 704 asserted true
  `-730`              `(729, false)`     -- variable 730 asserted false

DIMACS variable `v` (1-based) becomes the Lean variable `v - 1` (0-based).  This is the
same convention `bv_decide` uses, and the one `Std.Tactic.BVDecide.LRAT.check` expects:
its `CNF.lift` shifts formula variables by `+1` to recover the 1-based numbers the LRAT
certificate's literals carry.  A `.cnf` clause line is
`l₁ l₂ … lₖ 0`; a `cubes.txt` line is `l₁ l₂ … lₖ` (no terminating 0).  Header (`p …`)
and comment (`c …`) lines carry no clause content and are skipped; the header's two
counts are re-checked against the parsed term in `ConwayO7/Data/O7.lean`.

`serializeDimacs`/`serializeCubes` invert the parsers *byte-for-byte* on the artifact
files (single-space separation, one clause per `\n`-terminated line), which is what
makes the round-trip theorems in `ConwayO7/Data/O7.lean` an identity check between the
Lean terms and the exact bytes cake_lpr / lrat-check consumed.
-/
import ConwayO7.Semantics

namespace ConwayO7
namespace Dimacs

open Std.Sat

/-- The literal convention: `704 ↦ (703, true)`, `-730 ↦ (729, false)` —
DIMACS 1-based signed integers to 0-based `(variable, polarity)` pairs. -/
def litOfInt (i : Int) : Literal Nat :=
  if i < 0 then (i.natAbs - 1, false) else (i.natAbs - 1, true)

/-- Inverse rendering of `litOfInt`. -/
def litToString (l : Literal Nat) : String :=
  if l.2 then toString (l.1 + 1) else "-" ++ toString (l.1 + 1)

/-- Parse a DIMACS clause line `l₁ l₂ … lₖ 0`. -/
def parseClauseLine (line : String) : CNF.Clause Nat :=
  (((line.splitOn " ").filterMap String.toInt?).takeWhile (· ≠ 0)).map litOfInt

/-- Clause-content lines are the ones that are neither empty nor header/comment. -/
def isClauseLine (line : String) : Bool :=
  !line.isEmpty && !line.startsWith "p" && !line.startsWith "c"

/-- Parse a DIMACS file into a `Std.Sat.CNF Nat`, in file order (clause `i` of the
file, 1-based, becomes entry `i-1` of `clauses` — the numbering LRAT hints use). -/
def parseDimacs (s : String) : CNF Nat :=
  ⟨(((s.splitOn "\n").filter isClauseLine).map parseClauseLine).toArray⟩

/-- Render one clause as a DIMACS line (no newline). -/
def clauseToLine (c : CNF.Clause Nat) : String :=
  String.intercalate " " (c.map litToString ++ ["0"])

/-- Serialize a CNF back to DIMACS text, with the header counts passed explicitly
(they are re-checked against the term separately). Byte-inverse of `parseDimacs`
on the artifact file. -/
def serializeDimacs (nvars nclauses : Nat) (F : CNF Nat) : String :=
  s!"p cnf {nvars} {nclauses}\n" ++ String.join (F.clauses.toList.map (clauseToLine · ++ "\n"))

/-- Parse a `cubes.txt` line `l₁ l₂ … lₖ` (no terminating 0) as a cube. -/
def parseCubeLine (line : String) : Cube :=
  ((line.splitOn " ").filterMap String.toInt?).map litOfInt

/-- Parse `cubes.txt`: one cube per line. -/
def parseCubes (s : String) : List Cube :=
  ((s.splitOn "\n").filter (fun l ↦ !l.isEmpty)).map parseCubeLine

/-- Render one cube as a `cubes.txt` line (no newline). -/
def cubeToLine (c : Cube) : String :=
  String.intercalate " " (c.map litToString)

/-- Byte-inverse of `parseCubes` on the artifact file. -/
def serializeCubes (cs : List Cube) : String :=
  String.join (cs.map (cubeToLine · ++ "\n"))

end Dimacs
end ConwayO7
