#!/usr/bin/env python3
"""Prescribed-automorphism search for srg(v,k,1,2): does one exist admitting a
given cyclic automorphism sigma?  (Conway's 99-graph: order-7, sigma = [1, 7^14].)

WHY THIS IS SOUND (unlike adding sigma-clauses to smsg).
  smsg only ever accepts the lex-min (canonical) representative of each isomorphism
  class.  A sigma-invariant graph's canonical isomorph is invariant under a *conjugate*
  of sigma, not necessarily sigma itself, so "smsg + sigma-clauses" can wrongly report
  UNSAT.  Here we instead REDUCE to one boolean per sigma-orbit of vertex-pairs and
  solve with a PLAIN complete SAT solver (Cadical via PySAT) -- no canonicity pruning,
  so SAT <=> a sigma-invariant graph exists, UNSAT <=> none does.  Every model is then
  re-verified from scratch against the srg definition (the s2651/Conway discipline).

REDUCTION.  sigma of prime order p partitions the C(v,2) pairs into orbits of size 1
  or p; for p prime with one fixed vertex and no 2-cycles there are NO size-1 orbits,
  so the C(99,2)=4851 edge variables collapse to exactly 4851/7 = 693 orbit variables.

ENCODING (mu - lam == 1, as in conway_sms.py):
  degree     : each vertex has exactly k incident edges;
  common nbr : for each pair {u,v}, sum_w (e_uw & e_vw) + e_uv == mu.
  Edge literals use the orbit variable of their pair, so the model is sigma-invariant
  by construction.  Degree sums list one entry per actual neighbour (orbit vars may
  repeat -> the cardinality counter counts each occurrence, which is correct).

Runs in the workspace satvenv (PySAT).  Examples:
  python conway_o7.py --n 9  --k 4  --lam 1 --mu 2 --fixed 0 --cyc 3   # SAT (rook's graph)
  python conway_o7.py --n 9  --k 4  --lam 1 --mu 2 --fixed 9 --cyc 1   # SAT (no symmetry)
  python conway_o7.py --n 99 --k 14 --lam 1 --mu 2 --fixed 1 --cyc 7   # the order-7 search
"""
import argparse
import time

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

# degree-constraint cardinality encoding (idea #3 lever: mtotalizer ~2.7x leaner than seqcounter).
# Override via env CONWAY_DEG_ENC=mtotalizer|seqcounter|totalizer before importing.
import os as _os
_DEG_ENC = {"seqcounter": EncType.seqcounter, "totalizer": EncType.totalizer,
            "mtotalizer": EncType.mtotalizer}.get(_os.environ.get("CONWAY_DEG_ENC", "seqcounter"),
                                                  EncType.seqcounter)


def build_sigma(n, fixed, cyc_len):
    """Permutation of 0..n-1: vertices 0..fixed-1 fixed, the rest in cycles of cyc_len."""
    sigma = list(range(n))
    pts = list(range(fixed, n))
    assert len(pts) % cyc_len == 0, f"{len(pts)} moved points not divisible by {cyc_len}"
    for i in range(0, len(pts), cyc_len):
        blk = pts[i:i + cyc_len]
        for j in range(cyc_len):
            sigma[blk[j]] = blk[(j + 1) % cyc_len]
    return sigma


def pair_orbits(n, sigma):
    """Map each unordered pair (u,v) u<v to an orbit id under <sigma>. Returns (orbit_of, n_orbits)."""
    def norm(a, b):
        return (a, b) if a < b else (b, a)
    orbit_of = {}
    oid = 0
    for u in range(n):
        for v in range(u + 1, n):
            if (u, v) in orbit_of:
                continue
            cur, seen = (u, v), set()
            while True:
                p = norm(*cur)
                if p in seen:
                    break
                seen.add(p)
                orbit_of[p] = oid
                cur = (sigma[p[0]], sigma[p[1]])
            oid += 1
    return orbit_of, oid


def break_symmetry_clauses(n, k, fixed, cyc, orbit_of, evar):
    """SOUND symmetry-breaking for the [fixed=1, cyc-cycles] prescribed automorphism.

    The c = (n-1)/cyc cycles are interchangeable (the normalizer of <sigma> contains
    S_c permuting them).  The fixed vertex is adjacent to whole cycles only (each
    {0, cycle i} pair-orbit is a single boolean), and degree k forces exactly k/cyc of
    them true.  WLOG (relabelling cycles) those adjacent cycles are 0..k/cyc-1, so we
    fix the c infinity-cycle booleans -> a C(c, k/cyc)-fold reduction with zero risk
    (every solution has a relabelling meeting it).  Returns a list of unit clauses.
    """
    if fixed != 1:
        return []
    c = (n - fixed) // cyc
    nadj = k // cyc
    if nadj * cyc != k:
        return []  # fixed vertex not adjacent to whole cycles -> structure n/a
    inf = [evar[orbit_of[(0, fixed + cyc * i)]] for i in range(c)]
    return [[inf[i]] if i < nadj else [-inf[i]] for i in range(c)]


def add_lex_leq(cnf, vpool, X, Y, tag):
    """Append clauses enforcing bit-vectors X <=_lex Y (MSB first). Brute-force validated
    in _lextest.py.  SOUNDNESS-critical: z_i may be TRUE only if the prefix is truly equal."""
    z_prev = None  # 'all earlier positions equal'; None == constant TRUE (z_0)
    n = len(X)
    for i in range(n):
        x, y = X[i], Y[i]
        if x == y:          # structurally equal position: x<=y trivial, prefix-eq unchanged
            continue
        if z_prev is None:
            cnf.append([-x, y])
        else:
            cnf.append([-z_prev, -x, y])
        z = vpool.id((tag, "z", i))
        if z_prev is not None:
            cnf.append([-z, z_prev])
        cnf.append([-z, -x, y])
        cnf.append([-z, x, -y])
        if z_prev is None:
            cnf.append([-x, -y, z]); cnf.append([x, y, z])
        else:
            cnf.append([-z_prev, -x, -y, z]); cnf.append([-z_prev, x, y, z])
        z_prev = z


def cycle_swap_orbit_perm(n, fixed, cyc, i, j, orbit_of):
    """Permutation of pair-orbits induced by swapping cycles i,j (phase 0) -- an element of
    the normaliser of <sigma>, so it maps sigma-orbits to sigma-orbits. dict: orbit_id->orbit_id."""
    def rho(u):
        if u < fixed:
            return u
        ci, ph = divmod(u - fixed, cyc)
        ci = j if ci == i else (i if ci == j else ci)
        return fixed + cyc * ci + ph

    def norm(a, b):
        return (a, b) if a < b else (b, a)
    reps = {}
    for (a, b), o in orbit_of.items():
        reps.setdefault(o, (a, b))
    return {o: orbit_of[norm(rho(a), rho(b))] for o, (a, b) in reps.items()}


def cycle_rotate_orbit_perm(n, fixed, cyc, i, r, orbit_of):
    """Pair-orbit permutation induced by rotating cycle i by r ((i,j)->(i,j+r)); others fixed.
    This commutes with sigma (centraliser), so it maps sigma-orbits to sigma-orbits."""
    def rho(u):
        if u < fixed:
            return u
        ci, ph = divmod(u - fixed, cyc)
        if ci == i:
            ph = (ph + r) % cyc
        return fixed + cyc * ci + ph

    def norm(a, b):
        return (a, b) if a < b else (b, a)
    reps = {}
    for (a, b), o in orbit_of.items():
        reps.setdefault(o, (a, b))
    return {o: orbit_of[norm(rho(a), rho(b))] for o, (a, b) in reps.items()}


def multiplier_orbit_perm(n, fixed, cyc, a, orbit_of):
    """Pair-orbit permutation induced by the multiplier x->a*x on every cycle ((i,j)->(i,a*j)),
    a a unit mod cyc.  It conjugates sigma to sigma^a (normaliser), so maps sigma-orbits to orbits."""
    def rho(u):
        if u < fixed:
            return u
        ci, ph = divmod(u - fixed, cyc)
        return fixed + cyc * ci + (a * ph) % cyc

    def norm(p, q):
        return (p, q) if p < q else (q, p)
    reps = {}
    for (p, q), o in orbit_of.items():
        reps.setdefault(o, (p, q))
    return {o: orbit_of[norm(rho(p), rho(q))] for o, (p, q) in reps.items()}


def encode(n, k, lam, mu, sigma, one_constraint_per_orbit=True,
           break_sym=False, fixed=0, cyc=1, sym_level=None):
    assert mu - lam == 1, "encoder assumes mu - lam == 1"
    orbit_of, norb = pair_orbits(n, sigma)
    vpool = IDPool()
    evar = {o: vpool.id(("e", o)) for o in range(norb)}

    def e(u, v):
        return evar[orbit_of[(u, v) if u < v else (v, u)]]

    cnf = CNF()
    # degree: exactly k incident edges per vertex
    for u in range(n):
        lits = [e(u, v) for v in range(n) if v != u]
        cnf.extend(CardEnc.equals(lits, k, vpool=vpool, encoding=_DEG_ENC).clauses)

    # common-neighbour count per pair: sum_w (e_uw & e_vw) + e_uv == mu.
    # sigma-symmetric constraints are redundant across an orbit; impose one rep per orbit.
    done = set()
    for u in range(n):
        for v in range(u + 1, n):
            o = orbit_of[(u, v)]
            if one_constraint_per_orbit and o in done:
                continue
            done.add(o)
            prods = []
            for w in range(n):
                if w == u or w == v:
                    continue
                a, c = e(u, w), e(v, w)
                p = vpool.id(("p", u, v, w))
                cnf.append([-p, a])
                cnf.append([-p, c])
                cnf.append([p, -a, -c])
                prods.append(p)
            cnf.extend(CardEnc.equals(prods + [e(u, v)], mu, vpool=vpool,
                                      encoding=EncType.seqcounter).clauses)

    if sym_level is None:
        sym_level = 1 if break_sym else 0
    if sym_level >= 1:   # fix WHICH cycles the fixed vertex is adjacent to (C(c,k/cyc)-fold)
        for cl in break_symmetry_clauses(n, k, fixed, cyc, orbit_of, evar):
            cnf.append(cl)
    if sym_level >= 2 and fixed == 1:   # lex-leader under cycle swaps: breaks S_(inf) x S_(non-inf)
        c = (n - fixed) // cyc
        nadj = k // cyc
        order = list(range(norb))
        swaps = [(m, m + 1) for m in range(0, max(0, nadj - 1))]        # S_nadj on inf-cycles
        swaps += [(m, m + 1) for m in range(nadj, c - 1)]               # S_(c-nadj) on the rest
        for (i, j) in swaps:
            perm = cycle_swap_orbit_perm(n, fixed, cyc, i, j, orbit_of)
            X = [evar[o] for o in order]
            Y = [evar[perm[o]] for o in order]
            add_lex_leq(cnf, vpool, X, Y, f"lex{i}_{j}")
    if sym_level >= 3 and fixed == 1:   # break per-cycle rotations (Z_cyc^(c-1)) and multiplier (Z_(cyc-1))
        c = (n - fixed) // cyc
        order = list(range(norb))
        gens = []
        for i in range(c):
            for r in range(1, cyc):     # rotate cycle i by r  (full Z_cyc per cycle)
                gens.append((f"rot{i}_{r}", cycle_rotate_orbit_perm(n, fixed, cyc, i, r, orbit_of)))
        for a in range(2, cyc):         # multiplier x->a*x (cyc prime => every a in 2..cyc-1 is a unit)
            gens.append((f"mul{a}", multiplier_orbit_perm(n, fixed, cyc, a, orbit_of)))
        for tag, perm in gens:
            X = [evar[o] for o in order]
            Y = [evar[perm[o]] for o in order]
            add_lex_leq(cnf, vpool, X, Y, tag)
    return cnf, evar, orbit_of, e, norb


def verify(n, k, lam, mu, adj, sigma):
    """Independent re-check of the srg definition AND sigma-invariance."""
    for u in range(n):
        if sum(adj[u]) != k:
            return False, f"degree of {u} is {sum(adj[u])} != {k}"
    for u in range(n):
        for v in range(n):
            if u == v:
                continue
            common = sum(1 for w in range(n) if adj[u][w] and adj[v][w])
            want = lam if adj[u][v] else mu
            if common != want:
                return False, f"|N({u})cap N({v})|={common} != {want} (adjacent={adj[u][v]})"
    for u in range(n):
        for v in range(n):
            if adj[u][v] != adj[sigma[u]][sigma[v]]:
                return False, f"not sigma-invariant at ({u},{v})"
    return True, "verified srg + sigma-invariant"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--lam", type=int, required=True)
    ap.add_argument("--mu", type=int, required=True)
    ap.add_argument("--fixed", type=int, default=1, help="number of fixed points of sigma")
    ap.add_argument("--cyc", type=int, default=7, help="cycle length of the moved points")
    ap.add_argument("--timeout", type=int, default=0, help="solver timeout seconds (0 = none)")
    ap.add_argument("--break-sym", action="store_true",
                    help="add sound symmetry-breaking (fix the fixed-vertex's adjacent cycles)")
    ap.add_argument("--sym-level", type=int, default=None,
                    help="0=none, 1=infinity-fix, 2=+lex-leader cycle ordering (overrides --break-sym)")
    ap.add_argument("--out", default=None, help="write found graph (edge list) here")
    a = ap.parse_args()

    sigma = build_sigma(a.n, a.fixed, a.cyc)
    cyc_struct = f"[{a.fixed} fixed, {(a.n - a.fixed)//a.cyc} x {a.cyc}-cycles]"
    print(f"srg({a.n},{a.k},{a.lam},{a.mu}) with prescribed sigma of order {a.cyc}, "
          f"orbits {cyc_struct}", flush=True)

    t0 = time.time()
    cnf, evar, orbit_of, e, norb = encode(a.n, a.k, a.lam, a.mu, sigma,
                                          break_sym=a.break_sym, fixed=a.fixed, cyc=a.cyc,
                                          sym_level=a.sym_level)
    print(f"encoded: {norb} orbit (edge) vars, {cnf.nv} total vars, {len(cnf.clauses)} clauses "
          f"({time.time()-t0:.1f}s)", flush=True)

    solver = Cadical195(bootstrap_with=cnf)
    t1 = time.time()
    if a.timeout:
        # PySAT cadical lacks a wall timeout knob here; we rely on outer `timeout` wrapper.
        sat = solver.solve()
    else:
        sat = solver.solve()
    dt = time.time() - t1
    print(f"solve: {'SAT' if sat else 'UNSAT'} ({dt:.1f}s)", flush=True)

    if not sat:
        print(f"*** NO srg({a.n},{a.k},{a.lam},{a.mu}) admits an order-{a.cyc} automorphism "
              f"of type {cyc_struct}  =>  proves {a.cyc} does not divide |Aut| for this type ***")
        return

    model = set(l for l in solver.get_model() if l > 0)
    adj = [[0] * a.n for _ in range(a.n)]
    for u in range(a.n):
        for v in range(u + 1, a.n):
            if e(u, v) in model:
                adj[u][v] = adj[v][u] = 1
    ok, msg = verify(a.n, a.k, a.lam, a.mu, adj, sigma)
    print(f"INDEPENDENT VERIFY: {ok} -- {msg}", flush=True)
    if ok:
        print(f"*** FOUND a sigma-invariant srg({a.n},{a.k},{a.lam},{a.mu}) ***")
        if a.out:
            with open(a.out, "w") as fh:
                for u in range(a.n):
                    for v in range(u + 1, a.n):
                        if adj[u][v]:
                            fh.write(f"{u} {v}\n")
            print(f"edge list -> {a.out}")
    else:
        raise SystemExit("MODEL FAILED INDEPENDENT VERIFICATION -- encoding bug, do not trust")


if __name__ == "__main__":
    main()
