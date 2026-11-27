# AQIDA_CONSTITUTIONAL_SCOPE: gate | CLAIM_BOUNDARY: release packaging of already recorded results; states nothing new | FALSIFICATION_TESTS: lake build, check_axioms.sh, verify_certificates.py
"""
Standalone verifier for the certificates three_point_cert_t{10..16}_proj.json
(Theorem "cert" of Section "Linear bounds for small t" of the paper).

Uses only the Python standard library (fractions, json, itertools, math, os, sys).
Imports nothing from the project. All arithmetic is exact (Python integers and Fractions).

WHAT IS CHECKED, for each certificate file:
  1. Every row names one of the blocks "vertex", "Fano", "star<m>" (m = (t-1)//2) and carries an
     integer test vector u of the right length. Rows without a block are rejected.
  2. The cut of the row is RE-DERIVED from the definitions below: a_k = u^T M_k u for each unknown
     x = (d, w1, w3, Ts, Tk, Tp, Td) and b = u^T M_const u, where M(x) = M_const + sum_k x_k M_k is the
     block. The re-derived (a, b) must equal the stored (a, b).
  3. Every multiplier is a strictly positive rational number.
  4. sum_i y_i a_i = (1, 0, 0, 0, 0, 0, 0), i.e. the weighted sum of the cuts is the inequality
     d + sum_i y_i b_i >= 0, that is d - beta >= 0 with beta = -sum_i y_i b_i.
  5. beta equals the stored rational "bound".
  Then it prints beta exactly, its decimal value, and ceil(beta), the integer lower bound it implies for
  an integer dimension (vectors: r = 1, so the cost d = D is an integer).

WHAT IS NOT CHECKED here: that each block is positive semidefinite for every projective representation.
That is the mathematical argument of the paper (Section "Linear bounds for small t"): for a positive
semidefinite operator g and X_0 = 1, X_B = P_B, the matrix [L(X_i^* g X_j)] is positive semidefinite,
with L(X) = tr(X)/r, W_AB = L(P_A P_B), T_ABC = Re L(P_A P_B P_C), symmetrised over the symmetric group.

DEFINITIONS (re-derived here, from the paper):
  Triples: the 3-subsets of {0, ..., t-1}, in the order of itertools.combinations(range(t), 3).
  Two triples are adjacent when they share exactly one element.
  W(X, Y), as a linear form in (const, d, w1, w3, Ts, Tk, Tp, Td):
     |X & Y| = 3 -> 1 ; = 2 -> w1 ; = 0 -> w3 ; = 1 -> 0 (adjacent pair).
  T(A, B, C):
     0 if one of the three pairs is adjacent;
     if A = B = C: 1; if exactly two distinct triples X, Y: W(X, Y);
     three distinct triples, n2 = number of pairs sharing two elements:
        n2 = 3 and |A & B & C| = 2 -> Ts (three triples through a common pair);
        n2 = 3 and |A | B | C| = 4 -> Tk (three triples in a 4-set);
        n2 = 1 -> Tp (two triples share a pair, the third is disjoint from both);
        n2 = 0 -> Td (three pairwise disjoint triples).
  Vertex block (g = P_A with A = {0, 1, 2}): rows and columns indexed by the triples B with
     |A & B| != 1 (A itself included), entry T(A, B, C).
  Clique block (g = 1 - sum_{A in K} P_A, K a set of pairwise adjacent triples): index 0 for X_0 = 1, then
     the triples not in K. Entry (0, 0) = d - |K|; entry (0, B) = 1 - sum_{A in K} W(A, B);
     entry (B, C) = W(B, C) - sum_{A in K} T(A, B, C).
     K = Fano: the lines {0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}.
     K = star<m>: {0, 2i+1, 2i+2} for i = 0..m-1, m = (t-1)//2.

Usage: python verify_certificates.py [directory]   (default: the directory of this script)
Exit code 0 if and only if all seven certificates pass.
"""
import itertools
import json
import math
import os
import sys
from fractions import Fraction

NAMES = ["d", "w1", "w3", "Ts", "Tk", "Tp", "Td"]
NC = 8  # coordinates: 0 const, 1 d, 2 w1, 3 w3, 4 Ts, 5 Tk, 6 Tp, 7 Td
FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
TS = list(range(10, 17))
# Integer bounds stated in Theorem "cert" of the paper, used only as a comparison at the end.
PAPER_INTEGER_BOUNDS = {10: 11, 11: 14, 12: 16, 13: 17, 14: 19, 15: 21, 16: 23}


def unit(k):
    f = [0] * NC
    f[k] = 1
    return tuple(f)


ZERO = tuple([0] * NC)
ONE = unit(0)


def W(X, Y):
    k = len(X & Y)
    if k == 3:
        return ONE
    if k == 2:
        return unit(2)
    if k == 0:
        return unit(3)
    return ZERO  # k == 1: adjacent pair


def T(A, B, C):
    if len(A & B) == 1 or len(A & C) == 1 or len(B & C) == 1:
        return ZERO
    distinct = []
    for X in (A, B, C):
        if X not in distinct:
            distinct.append(X)
    if len(distinct) == 1:
        return ONE
    if len(distinct) == 2:
        return W(distinct[0], distinct[1])
    n2 = sum(1 for X, Y in ((A, B), (A, C), (B, C)) if len(X & Y) == 2)
    if n2 == 3:
        if len(A & B & C) == 2:
            return unit(4)
        if len(A | B | C) == 4:
            return unit(5)
        raise ValueError("unexpected configuration with n2 = 3")
    if n2 == 1:
        return unit(6)
    if n2 == 0:
        return unit(7)
    raise ValueError("impossible configuration n2 = %d" % n2)


def triples(t):
    return [frozenset(c) for c in itertools.combinations(range(t), 3)]


def block_entry_function(t, name):
    """Return (size, entry) where entry(i, j) is the linear form of the (i, j) entry of the block."""
    trs = triples(t)
    if name == "vertex":
        A = trs[0]
        rows = [B for B in trs if len(A & B) != 1]
        return len(rows), (lambda i, j: T(A, rows[i], rows[j]))
    if name == "Fano":
        K = [frozenset(l) for l in FANO]
    elif name.startswith("star"):
        m = int(name[4:])
        if m != (t - 1) // 2:
            raise ValueError("star size %d does not match t = %d" % (m, t))
        K = [frozenset((0, 2 * i + 1, 2 * i + 2)) for i in range(m)]
    else:
        raise ValueError("unknown block " + repr(name))
    for X, Y in itertools.combinations(K, 2):
        if len(X & Y) != 1:
            raise ValueError("K is not a set of pairwise adjacent triples")
    rest = [B for B in trs if B not in K]

    def sub(f, g):
        return tuple(x - y for x, y in zip(f, g))

    def entry(i, j):
        if i == 0 and j == 0:
            f = [0] * NC
            f[0] = -len(K)
            f[1] = 1
            return tuple(f)
        if i == 0 or j == 0:
            B = rest[(j if i == 0 else i) - 1]
            f = ONE
            for A in K:
                f = sub(f, W(A, B))
            return f
        B, C = rest[i - 1], rest[j - 1]
        f = W(B, C)
        for A in K:
            f = sub(f, T(A, B, C))
        return f

    return len(rest) + 1, entry


def quadratic_form(size, entry, u):
    """u^T M u for every coordinate, exact integers. Uses the symmetry of M (checked on the support)."""
    supp = [i for i in range(size) if u[i] != 0]
    tot = [0] * NC
    for a_idx, i in enumerate(supp):
        ui = u[i]
        e = entry(i, i)
        for k in range(NC):
            if e[k]:
                tot[k] += ui * ui * e[k]
        for j in supp[a_idx + 1:]:
            e = entry(i, j)
            if e != entry(j, i):
                raise ValueError("block is not symmetric at (%d, %d)" % (i, j))
            c = 2 * ui * u[j]
            for k in range(NC):
                if e[k]:
                    tot[k] += c * e[k]
    return tot


def ceil_fraction(q):
    return -((-q.numerator) // q.denominator)


def check(path, t):
    print("=" * 78)
    print("t = %d   file: %s" % (t, os.path.basename(path)))
    with open(path, "r", encoding="utf-8") as fh:
        c = json.load(fh)
    ok = True
    if c.get("t") != t or c.get("variant") != "proj":
        print("  FAIL: header t/variant is %r/%r" % (c.get("t"), c.get("variant")))
        ok = False
    cache = {}
    tot = [Fraction(0)] * 7
    totb = Fraction(0)
    for n, r in enumerate(c["rows"], 1):
        y = Fraction(r["multiplier"])
        line_ok = True
        if not y > 0:
            print("  row %d: FAIL multiplier not positive: %s" % (n, y))
            line_ok = False
        if "block" not in r or "u" not in r:
            print("  row %d: FAIL row without a block and test vector (not supported)" % n)
            ok = False
            continue
        bn = r["block"]
        if bn not in cache:
            cache[bn] = block_entry_function(t, bn)
        size, entry = cache[bn]
        u = [int(x) for x in r["u"]]
        if len(u) != size:
            print("  row %d: FAIL len(u) = %d, block %s has size %d" % (n, len(u), bn, size))
            ok = False
            continue
        vals = quadratic_form(size, entry, u)
        a_new, b_new = vals[1:], vals[0]
        match = (a_new == list(r["a"]) and b_new == int(r["b"]))
        if not match:
            line_ok = False
        print("  row %d: block %-6s size %3d  re-derived cut equals stored cut: %s  multiplier > 0: %s"
              % (n, bn, size, match, y > 0))
        print("         cut: %s + %d >= 0" % (" + ".join("%d*%s" % (x, nm) for x, nm in zip(a_new, NAMES)), b_new))
        ok &= line_ok
        # combine the RE-DERIVED cut (equal to the stored one when match is True)
        tot = [s + y * x for s, x in zip(tot, a_new)]
        totb += y * b_new
    e0 = [Fraction(1)] + [Fraction(0)] * 6
    combo = (tot == e0)
    beta = -totb
    stored = Fraction(c["bound"])
    print("  sum of multiplier * cut = 1*d + 0*w1 + ... + 0*Td: %s" % combo)
    if not combo:
        print("  combined coefficients: %s" % [str(x) for x in tot])
    print("  weighted sum is the inequality d - beta >= 0 with")
    print("    beta (exact) = %s" % beta)
    print("    beta (decimal, 12 digits) = %.12f" % (beta.numerator / beta.denominator))
    print("    beta equals stored bound: %s" % (beta == stored))
    ib = ceil_fraction(beta)
    print("    integer bound implied: d >= ceil(beta) = %d" % ib)
    ok &= combo and beta == stored and beta > 0
    print("t = %d: certificate %s" % (t, "PASS" if ok else "FAIL"))
    return ok, beta, ib


def main():
    here = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    print("verify_certificates.py: standalone exact re-check (Python %s)" % sys.version.split()[0])
    results = {}
    all_ok = True
    for t in TS:
        path = os.path.join(here, "three_point_cert_t%d_proj.json" % t)
        ok, beta, ib = check(path, t)
        results[t] = (ok, beta, ib)
        all_ok &= ok
    print("=" * 78)
    print("SUMMARY")
    print("  t   status  beta (decimal)    integer bound   paper's integer bound")
    for t in TS:
        ok, beta, ib = results[t]
        same = ib == PAPER_INTEGER_BOUNDS[t]
        all_ok &= same
        print("  %2d  %-6s  %.9f    %3d             %3d  %s"
              % (t, "PASS" if ok else "FAIL", beta.numerator / beta.denominator, ib,
                 PAPER_INTEGER_BOUNDS[t], "(same)" if same else "(DIFFERENT)"))
    print("OVERALL: %s" % ("ALL SEVEN CERTIFICATES PASS" if all_ok else "FAIL"))
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
