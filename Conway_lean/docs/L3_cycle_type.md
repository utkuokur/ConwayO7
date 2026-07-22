# L3 — The cycle-type lemma: why σ = [1, 7¹⁴] is WLOG

**Status: SOLVED.** The lemma is published, with an elementary proof, as
**Lemma 2.2 of Cesarz–Woldar**, *On the automorphism group of a putative Conway
99-graph*, arXiv:2308.02978 (Algebraic Combinatorics draft, 2023). An
independent derivation (different route, same conclusion) is in the appendix
below, giving a cross-check. Both proofs are elementary — finite counting only,
no eigenvalue/character theory — hence directly formalizable in Lean/mathlib.

## The statement

> **L3.** Let Γ be an srg(99,14,1,2) and σ ∈ Aut(Γ) with ord(σ) = 7. Then σ
> fixes **exactly one** vertex, and its cycle type is [1, 7¹⁴]. Consequently,
> after relabeling vertices (conjugation in Sym(99)), σ is the canonical
> permutation σ₀ = one fixed vertex + fourteen 7-cycles used by
> `tools/conway_o7.py`.

Position in the chain T2:

```
7 ∣ |Aut Γ|            (assumption toward contradiction)
  ⟹ ∃ σ, ord σ = 7     [Cauchy: mathlib exists_prime_orderOf_dvd_card]
  ⟹ cycle type [1,7¹⁴] [L3, this document]
  ⟹ WLOG σ = σ₀        [cycle-type conjugacy + relabeling]
  ⟹ o7.cnf satisfiable [L4: encoder faithfulness, "graph → assignment" direction]
  ⟹ contradiction with UNSAT(o7.cnf)  [T1 + cake_lpr]
  ⟹ 7 ∤ |Aut Γ|. ∎
```

## The Cesarz–Woldar proof (the one to formalize)

Setup: 99 ≡ 1 (mod 7) forces at least one fixed vertex x (orbits have size 1
or 7). Root Γ at x; let Γ₁ = N(x) (14 vertices), Γ₂ = the other 84.

**Step 1 (λ = 1 matching, parity).** Each edge {x, u}, u ∈ Γ₁ lies in a unique
triangle, so Γ₁ carries a perfect matching u ↦ partner(u) (7 pairs; the paper's
{iL, iR}). partner is σ-equivariant, and u is fixed iff partner(u) is fixed
(the partner is the unique common neighbor of the fixed pair {x, u} — a
singleton σ-invariant set). Hence #fixed(Γ₁) is **even**. Orbit sizes on Γ₁
are 1 or 7, so #fixed(Γ₁) ∈ {0, 7, 14}; evenness leaves {0, 14}.

**Step 2 (rigidity; CW Lemma 2.1).** The two Γ₁-neighbors of any w ∈ Γ₂ are
nonadjacent (if they were adjacent, λ = 1 would be violated: x and w would both
be common neighbors), and by μ = 2 the pair {x, w} has exactly those two common
neighbors. Conversely each nonadjacent pair in Γ₁ has exactly one common
neighbor besides x. This labels the 84 vertices of Γ₂ **injectively** by the 84
nonadjacent pairs of Γ₁. So: if σ fixes x and all of Γ₁ pointwise, it fixes
every label, hence every vertex of Γ₂ — i.e. σ = id. Since ord(σ) = 7 ≠ 1,
#fixed(Γ₁) = 14 is impossible. Conclusion: **σ has no fixed vertex in Γ₁**
(orbit structure [7²] there).

**Step 3 (no fixed vertex in Γ₂).** Suppose w ∈ Γ₂ is fixed. The 2-element set
C = {common neighbors of x and w} ⊆ Γ₁ is σ-invariant. By Step 2, σ has no
fixed points in Γ₁, so σ must swap the two elements of C: σ(a) = b, σ(b) = a.
Then σ²(a) = a, and since σ = (σ²)⁴ (because σ⁸ = σ⁷·σ = σ), also σ(a) = a —
contradiction. So Γ₂ has no fixed vertex.

**Step 4 (conclusion).** The unique fixed vertex is x; the remaining 98
vertices fall into 98/7 = 14 orbits of size 7. Cycle type [1, 7¹⁴]. ∎

**Step 5 (WLOG canonical σ₀).** Two permutations of Sym(99) with equal cycle
type are conjugate: τστ⁻¹ = σ₀. Relabeling Γ by τ gives an isomorphic
srg(99,14,1,2) invariant under σ₀. Hence "some srg admits an order-7
automorphism" ⟺ "some srg is σ₀-invariant" — the statement o7.cnf encodes.
[mathlib: `Equiv.Perm.isConj_iff_cycleType_eq`.]

## Lean/mathlib mapping

| Step | Key mathlib ingredients |
|---|---|
| Cauchy | `exists_prime_orderOf_dvd_card` |
| orbits size 1 or 7 | `MulAction.card_orbit_dvd_card` (⟨σ⟩ ≅ ZMod 7), or elementary: orbit of x under σ with σ⁷ = 1 |
| Step 1 | `SimpleGraph.IsSRGWith` field for λ; matching as the map u ↦ unique common nbr of x,u |
| Step 2 | μ-field of `IsSRGWith`; injectivity by uniqueness of 2-element common-neighbor sets |
| Step 3 | pure computation σ = (σ²)⁴ from σ⁷ = 1 — no group theory needed |
| Step 5 | `Equiv.Perm.isConj_iff_cycleType_eq`, `SimpleGraph.Iso` transport of `IsSRGWith` |

Estimated size: a few hundred lines; no spectral/character theory anywhere.

## Literature context (for the paper's related-work section)

- **Makhnev–Minakova 2004** (*On automorphisms of strongly regular graphs with
  parameters λ=1, μ=2*, Discrete Math. Appl. 14(2)): |Aut Γ| divides
  2·3³·7·11; if even, it divides 42.
- **Cesarz–Woldar 2023** (arXiv:2308.02978): if 7 ∣ |Aut Γ| then Aut Γ ≅ ℤ₇.
  Their Lemma 2.2 is exactly L3. Crucially, their elimination of Frob(21) is a
  **GAP/GRAPE computer search** (2,916 iterations; Section 6), about which they
  write: *"We would of course welcome independent verification of this fact,
  and we'd be delighted if a computer-free proof could be furnished."*
- **This project** strictly strengthens the above: **7 ∤ |Aut Γ|** (no order-7
  automorphism at all), via 98,536 LRAT certificates that are machine-checked
  by independent (and formally verified) checkers — a substantially stronger
  evidence standard than an unverified GAP run. Combined with the prior
  results, a putative Conway 99-graph now has |Aut Γ| dividing 3³·11, and
  dividing 6 if even.

## Appendix — independent derivation (cross-check; not the one to formalize)

Let f = #fixed. Fixed-subgraph route: (i) f ≡ 1 (mod 7). (ii) Invariant sets
of size ≤ 2 are pointwise fixed, so all common neighbors of two fixed vertices
are fixed; the induced subgraph Δ on Fix(σ) therefore inherits "adjacent ⟹
exactly 1, nonadjacent ⟹ exactly 2 common neighbors *inside Δ*". (iii) For
fixed u, N(u) is invariant, so deg_Δ(u) = |N(u) ∩ Fix| ≡ 14 ≡ 0 (mod 7):
degrees ∈ {0,7,14}. (iv) If f ≥ 2, degree 0 is impossible (a second fixed
vertex forces 1 or 2 fixed common neighbors). (v) Walk identity: in any graph
with the (1,2) common-neighbor property, Σ_{v∼u} deg v = 2(n−1) for every u.
(vi) All-7: 49 = 2(f−1), parity contradiction. All-14: 196 = 2(f−1) ⟹ f = 99 ⟹
σ = id. Mixed: the identity forces f = 50 and a bipartition (7-vertices adjacent
only to 14-vertices and vice versa), whence an edge between the classes has no
possible common neighbor — contradiction with λ = 1. Hence f = 1. ∎
