/-
The exact CNF generator, in Lean.

A faithful port of the `o7.cnf` generation pipeline:
`tools/conway_o7.py::encode(99,14,1,2, build_sigma(99,1,7), fixed=1, cyc=7,
sym_level=3)` under `CONWAY_DEG_ENC=mtotalizer`, including byte-exact ports of the
pysat 1.9.dev5 cardinality encoders it invokes:

  * `cardenc/mto.hh`        — modulo-totalizer (`to_TO`/`to_UA`/`MTO_A`/`MUA_A`/
                              comparator), used for the 99 degree-14 constraints;
  * `cardenc/seqcounter.hh` — Knuth's irredundant sequential counter, used for the
                              693 common-neighbour (μ = 2) counters;
  * `cardenc/card.hh`       — the atmost/atleast/equals dispatch (special cases and
                              the negate-and-complement reduction of `atleast`);

plus the encoder's own product clauses and the three symmetry-breaking levels
(orbit units, and lex-leader chains for cycle swaps, rotations and multipliers).

This port was cross-validated against a dependency-free Python reimplementation
that reproduces `artifact/o7.cnf` byte-for-byte; the Lean theorem
`ConwayO7/Data/EncoderMatch.lean : mkO7Cnf_eq` re-checks the identity in Lean.
Clause and fresh-variable emission ORDER is part of the specification: variables are
allocated by a single running counter exactly as pysat's `IDPool` does here (the
encoder never calls `occupy`, so the pool is sequential).

Imperative stacks in the C++ are rendered as fuel-bounded recursions with the same
LIFO processing order (parent clauses, then second half, then first half).
-/
import ConwayO7.Orbits
import ConwayO7.Dimacs

namespace ConwayO7
namespace Encoder

/-- Emission state: the last allocated DIMACS variable and the clauses so far. -/
structure St where
  top : ℕ
  cls : Array (List ℤ)

@[inline] def push (s : St) (c : List ℤ) : St := { s with cls := s.cls.push c }

@[inline] def fresh (s : St) : St × ℤ :=
  ({ s with top := s.top + 1 }, (s.top + 1 : ℕ))

/-- Push a list of clauses in order. -/
def pushMany (s : St) (cs : List (List ℤ)) : St := cs.foldl push s

/-- Emit clauses generated per item of a list, in order — the proof-friendly loop
shape shared by all gadget emitters. -/
def emitFold {α : Type} (s : St) (l : List α) (f : α → List (List ℤ)) : St :=
  l.foldl (fun s x ↦ pushMany s (f x)) s

/-! ### Totalizer (`to_TO` / `to_UA`), used by mto for short blocks -/

def toUA (s : St) (outl al bl : Array ℤ) : St :=
  let s := emitFold s (List.range bl.size) fun j ↦ [[-bl[j]!, outl[j]!]]
  let s := emitFold s (List.range al.size) fun i ↦ [[-al[i]!, outl[i]!]]
  emitFold s (List.range al.size) fun i ↦
    (List.range bl.size).map fun j ↦ [-al[i]!, -bl[j]!, outl[i + j + 1]!]

/-- Allocate `n` fresh variables (in closed form: `top+1 … top+n`). -/
def freshMany (s : St) (n : ℕ) : St × Array ℤ :=
  ({ s with top := s.top + n }, (Array.range n).map fun i ↦ ((s.top + 1 + i : ℕ) : ℤ))

/-- One totalizer tree node: allocate child outputs (first half, then second),
emit the parent's `to_UA` clauses, then process the second half, then the first
(the C++ stack pops in LIFO order). -/
def toTONode (fuel : ℕ) (s : St) (ilst olst : Array ℤ) : St :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    let n := ilst.size
    let half := n - n / 2
    let fst := ilst.extract 0 half
    let snd := ilst.extract half n
    let sf := if 2 ≤ half then freshMany s half else (s, fst)
    let ss := if 2 ≤ n - half then freshMany sf.1 (n - half) else (sf.1, snd)
    let s2 := toUA ss.1 olst sf.2 ss.2
    let s3 := if 2 ≤ n - half then toTONode fuel s2 snd ss.2 else s2
    if 2 ≤ half then toTONode fuel s3 fst sf.2 else s3

/-- `to_TO`: returns the output variables (the inputs themselves when `n < 2`). -/
def toTO (s : St) (invars : Array ℤ) : St × Array ℤ :=
  if invars.size < 2 then (s, invars)
  else
    let so := freshMany s invars.size
    (toTONode invars.size so.1 invars so.2, so.2)

/-! ### Modulo totalizer (`mto_MUA_A` / `mto_MTO_A` / comparator) -/

def muaA (s0 : St) (hs rs ff aa gg bb : Array ℤ) (p : ℕ) : St :=
  let sigma := hs.size
  let sc := fresh s0
  let c := sc.2
  -- phi 1
  let s := emitFold sc.1 (List.range bb.size) fun j ↦ [[-bb[j]!, rs[j]!, c]]
  let s := emitFold s (List.range aa.size) fun i ↦ [[-aa[i]!, rs[i]!, c]]
  let s := emitFold s (List.range aa.size) fun i ↦
    (List.range bb.size).map fun j ↦
      if i + j + 2 < p then [-aa[i]!, -bb[j]!, rs[i + j + 1]!, c]
      else if i + j + 2 > p then [-aa[i]!, -bb[j]!, rs[((i + j + 2) % p) - 1]!]
      else [-aa[i]!, -bb[j]!, c]
  -- phi 2
  let s := if sigma = 0 then push s [-c] else push s [-c, hs[0]!]
  let s := emitFold s (List.range gg.size) fun j ↦
    [if j + 1 ≤ sigma then [-gg[j]!, hs[j]!] else [-gg[j]!],
      if j + 1 < sigma then [-c, -gg[j]!, hs[j + 1]!] else [-c, -gg[j]!]]
  let s := emitFold s (List.range ff.size) fun i ↦
    [if i + 1 ≤ sigma then [-ff[i]!, hs[i]!] else [-ff[i]!],
      if i + 1 < sigma then [-c, -ff[i]!, hs[i + 1]!] else [-c, -ff[i]!]]
  emitFold s (List.range ff.size) fun i ↦
    (List.range gg.size).flatMap fun j ↦
      [if i + j + 2 ≤ sigma then [-ff[i]!, -gg[j]!, hs[i + j + 1]!]
       else [-ff[i]!, -gg[j]!],
        if i + j + 2 < sigma then [-c, -ff[i]!, -gg[j]!, hs[i + j + 2]!]
        else [-c, -ff[i]!, -gg[j]!]]

/-- Prepare one half inside an `MTO_A` node: short halves get an immediate
totalizer; long halves get fresh upper/lower registers and a pending job. -/
def mtoPrepHalf (s : St) (halfLits : Array ℤ) (p : ℕ) :
    St × Array ℤ × Array ℤ × Bool :=
  if halfLits.size < p then
    let sl := toTO s halfLits
    (sl.1, #[], sl.2, false)
  else
    let su := freshMany s (halfLits.size / p)
    let sl := freshMany su.1 (p - 1)
    (sl.1, su.2, sl.2, true)

def mtoNode (fuel : ℕ) (s : St) (ilst ulst llst : Array ℤ) (p : ℕ) : St :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    let ni := ilst.size
    let half := ni - ni / 2
    let fst := ilst.extract 0 half
    let snd := ilst.extract half ni
    let pf := mtoPrepHalf s fst p
    let ps := mtoPrepHalf pf.1 snd p
    let s2 := muaA ps.1 ulst llst pf.2.1 pf.2.2.1 ps.2.1 ps.2.2.1 p
    let s3 := if ps.2.2.2 then mtoNode fuel s2 snd ps.2.1 ps.2.2.1 p else s2
    if pf.2.2.2 then mtoNode fuel s3 fst pf.2.1 pf.2.2.1 p else s3

/-- `mto_MTO_A` (with `k = -1`, as `mto_encode_atmostN` calls it). -/
def mtoMTO (s : St) (is_ : Array ℤ) (p : ℕ) : St × Array ℤ × Array ℤ :=
  if is_.size < p then
    let sl := toTO s is_
    (sl.1, #[], sl.2)
  else
    let su := freshMany s (is_.size / p)
    let sl := freshMany su.1 (p - 1)
    (mtoNode is_.size sl.1 is_ su.2 sl.2 p, su.2, sl.2)

def mtoComparator (s : St) (upper lower : Array ℤ) (p k : ℕ) : St :=
  let ro := k / p
  let nu := k % p
  let s := emitFold s (List.range' (ro + 1) (upper.size - ro)) fun i ↦ [[-upper[i - 1]!]]
  emitFold s (List.range' (nu + 1) (p - (nu + 1))) fun i ↦
    if ro > 0 then
      if ro - 1 < upper.size then [[-upper[ro - 1]!, -lower[i - 1]!]] else []
    else [[-lower[i - 1]!]]

def mtoAtMost (s : St) (vars : Array ℤ) (k : ℕ) : St :=
  let n := vars.size
  if k ≥ n then s
  else if k = 0 then vars.foldl (fun s v ↦ push s [-v]) s
  else
    let p := max (Nat.sqrt n) 2
    let mt := mtoMTO s vars p
    mtoComparator mt.1 mt.2.1 mt.2.2 p k

/-! ### Sequential counter (Knuth's irredundant variant) -/
def seqAtMost (s0 : St) (xs : Array ℤ) (tval : ℕ) : St := Id.run do
  let n := xs.size
  let nt := n - tval
  -- the (k, j) register table, allocated on first use
  let mut tbl : Array (Option ℤ) := Array.replicate (tval * nt) none
  let mut s := s0
  let mk := fun (s : St) (tbl : Array (Option ℤ)) (k j : ℕ) ↦
    match tbl[k * nt + j]! with
    | some v => (s, tbl, v)
    | none =>
      let (s, v) := fresh s
      (s, tbl.set! (k * nt + j) (some v), v)
  for j in [0:nt] do
    let (s1, t1, s0j) := mk s tbl 0 j
    s := s1; tbl := t1
    s := push s [-xs[j]!, s0j]
    for k in [0:tval - 1] do
      let (s1, t1, skj) := mk s tbl k j
      s := s1; tbl := t1
      if j < nt - 1 then
        let (s2, t2, skj1) := mk s tbl k (j + 1)
        s := s2; tbl := t2
        s := push s [-skj, skj1]
      let (s3, t3, sk1j) := mk s tbl (k + 1) j
      s := s3; tbl := t3
      s := push s [-xs[j + k + 1]!, -skj, sk1j]
    let (s4, t4, stj) := mk s tbl (tval - 1) j
    s := s4; tbl := t4
    if j < nt - 1 then
      let (s5, t5, stj1) := mk s tbl (tval - 1) (j + 1)
      s := s5; tbl := t5
      s := push s [-stj, stj1]
    s := push s [-xs[j + tval]!, -stj]
  return s

/-! ### `card.hh` dispatch (the paths o7.cnf exercises) -/

inductive Enc | mto | seq

def encAtMost (s : St) (lits : Array ℤ) (rhs : ℕ) (enc : Enc) : St :=
  let n := lits.size
  if rhs ≥ n then s
  else if rhs = n - 1 then push s (lits.toList.map (-·))
  else if rhs = 0 then lits.foldl (fun s l ↦ push s [-l]) s
  else match enc with
    | .mto => mtoAtMost s lits rhs
    | .seq => seqAtMost s lits rhs

def encAtLeast (s : St) (lits : Array ℤ) (rhs : ℕ) (enc : Enc) : St :=
  if rhs = 0 then s
  else if rhs = 1 then push s lits.toList
  else if rhs = lits.size then lits.foldl (fun s l ↦ push s [l]) s
  else encAtMost s (lits.map (-·)) (lits.size - rhs) enc

def encEquals (s : St) (lits : Array ℤ) (k : ℕ) (enc : Enc) : St :=
  encAtMost (encAtLeast s lits k enc) lits k enc

/-! ### The o7 instance -/

/-- DIMACS id of the edge-orbit variable of the pair `{u, v}` (`u ≠ v`). -/
def evarI (u v : Fin 99) : ℤ := (orbitOf (u, v) + 1 : ℕ)

/-- ℕ-level vertex relabeling helpers for the symmetry generators
(`fixed = 1`, `cyc = 7`). -/
def rhoSwap (i j u : ℕ) : ℕ :=
  if u = 0 then 0
  else
    let ci := (u - 1) / 7
    let ph := (u - 1) % 7
    let ci' := if ci = i then j else if ci = j then i else ci
    1 + 7 * ci' + ph

def rhoRot (i r u : ℕ) : ℕ :=
  if u = 0 then 0
  else
    let ci := (u - 1) / 7
    let ph := (u - 1) % 7
    if ci = i then 1 + 7 * ci + (ph + r) % 7 else u

def rhoMul (a u : ℕ) : ℕ :=
  if u = 0 then 0
  else
    let ci := (u - 1) / 7
    let ph := (u - 1) % 7
    1 + 7 * ci + (a * ph) % 7

/-- Orbit id of a ℕ pair (values < 99). -/
def orbitOfN (a b : ℕ) : ℕ :=
  orbitOf (⟨a % 99, Nat.mod_lt a (by omega)⟩, ⟨b % 99, Nat.mod_lt b (by omega)⟩)

/-- The image orbit of orbit `o` under a vertex relabeling `rho`
(`perm[o] = orbit_of[norm(rho(rep))]` in the encoder). -/
def orbitPerm (rho : ℕ → ℕ) (o : ℕ) : ℕ :=
  let r := orbitRep o
  orbitOfN (rho r.1.val) (rho r.2.val)

/-- `add_lex_leq`: the soundness-critical lex-chain clauses, with `z`-registers
allocated on the fly (skipping structurally equal positions). -/
def addLexLeq (s0 : St) (X Y : Array ℤ) : St := Id.run do
  let mut s := s0
  let mut zPrev : Option ℤ := none
  for i in [0:X.size] do
    let x := X[i]!
    let y := Y[i]!
    if x ≠ y then
      match zPrev with
      | none => s := push s [-x, y]
      | some zp => s := push s [-zp, -x, y]
      let (s', z) := fresh s
      s := s'
      if let some zp := zPrev then
        s := push s [-z, zp]
      s := push s [-z, -x, y]
      s := push s [-z, x, -y]
      match zPrev with
      | none =>
        s := push s [-x, -y, z]
        s := push s [x, y, z]
      | some zp =>
        s := push s [-zp, -x, -y, z]
        s := push s [-zp, x, y, z]
      zPrev := some z
  return s

/-- The lex constraint `E ≤ E ∘ perm` over all 693 orbit variables. -/
def lexAgainst (s : St) (perm : ℕ → ℕ) : St :=
  let X : Array ℤ := .ofFn (n := 693) fun o ↦ ((o : ℕ) + 1 : ℕ)
  let Y : Array ℤ := .ofFn (n := 693) fun o ↦ ((perm o.val) + 1 : ℕ)
  addLexLeq s X Y

/-! The generator, as explicit folds of named steps (proof-friendly shape). -/

/-- Degree gadget for vertex `u`: exactly 14 neighbours (mtotalizer). -/
def degreeStep (s : St) (u : Fin 99) : St :=
  let lits : Array ℤ :=
    ((List.finRange 99).filterMap fun v ↦ if v ≠ u then some (evarI u v) else none).toArray
  encEquals s lits 14 .mto

/-- Product gadget: `p ↔ e(r₁,w) ∧ e(r₂,w)` for one candidate common neighbour `w`. -/
def prodStep (r : Fin 99 × Fin 99) (acc : St × Array ℤ) (w : Fin 99) : St × Array ℤ :=
  if w ≠ r.1 ∧ w ≠ r.2 then
    let a := evarI r.1 w
    let c := evarI r.2 w
    let (s, p) := fresh acc.1
    let s := push s [-p, a]
    let s := push s [-p, c]
    let s := push s [p, -a, -c]
    (s, acc.2.push p)
  else acc

/-- Common-neighbour gadget for orbit `o`: products, then the μ = 2 counter
(seqcounter). -/
def cnStep (s : St) (o : ℕ) : St :=
  let r := orbitRep o
  let (s, prods) := (List.finRange 99).foldl (prodStep r) (s, #[])
  encEquals s (prods.push (evarI r.1 r.2)) 2 .seq

/-- Symmetry level 1, unit `i`: the fixed vertex is adjacent to cycles 0 and 1 only. -/
def sym1Step (s : St) (i : ℕ) : St :=
  let v : ℤ := (orbitOfN 0 (1 + 7 * i) + 1 : ℕ)
  push s (if i < 2 then [v] else [-v])

/-- The 101 lex-leader generators, in emission order: adjacent cycle swaps
(level 2), then per-cycle rotations and multipliers (level 3). -/
def lexPerms : List (ℕ → ℕ) :=
  (rhoSwap 0 1 :: (List.range' 2 11).map fun m ↦ rhoSwap m (m + 1)) ++
    ((List.range 14).flatMap fun i ↦ (List.range' 1 6).map fun r ↦ rhoRot i r) ++
    (List.range' 2 5).map fun a ↦ rhoMul a

/-- **The generator**: all 1,131,708 clauses of `o7.cnf`, in file order. -/
def mkO7St : St :=
  let s : St := ⟨693, #[]⟩
  let s := (List.finRange 99).foldl degreeStep s
  let s := (List.range 693).foldl cnStep s
  let s := (List.range 14).foldl sym1Step s
  lexPerms.foldl (fun s ρ ↦ lexAgainst s (orbitPerm ρ)) s

/-- The generated CNF, in the 0-based `Std.Sat.CNF` convention of
`ConwayO7/Dimacs.lean`. -/
def mkO7Cnf : Std.Sat.CNF ℕ :=
  ⟨mkO7St.cls.map fun c ↦ c.map Dimacs.litOfInt⟩

end Encoder
end ConwayO7
