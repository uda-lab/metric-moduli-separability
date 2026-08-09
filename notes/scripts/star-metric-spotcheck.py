#!/usr/bin/env python3
"""Numerical spot-check of the star construction of report/report-ja.md §3.2.

Written for the Issue #10 independent review (see notes/proof-audit.md).  This
is a *finite model* of the construction: the index set omega_1 is replaced by a
handful of anchors a in A and the spoke index n ranges over 1..N instead of all
of N.  Report §3.8 establishes that (C1)-(C5) never use the cardinality of the
index set -- every verification is local (at most three points, or one point
against its complement) -- so a finite model exercises exactly the same
inequalities that the proofs rely on.  It cannot *prove* anything; it is a
falsification attempt that failed, recorded as evidence.

What is checked, per report §3.3-§3.7:
  (C1) positivity and the triangle inequality, over all ordered triples;
  (C2) the isolation radius delta(u) > 0 for every u when t not in A, using the
       exact infimum inf_n s_n(alpha,t) = min(1, |t - a_alpha|) rather than the
       truncated one;
  (C3) delta(y_beta) = 0 when t = a_beta in A, i.e. compatibility fails;
  (C4) the bi-Lipschitz bounds |t-s| <= rho(d_t,d_s) <= 2|t-s|.

Run: python3 notes/scripts/star-metric-spotcheck.py
"""

import itertools
import random

# ---------------------------------------------------------------- finite model
A = [0.1, 0.37, 0.62, 0.9]   # stands in for {a_alpha : alpha < omega_1}
N = 6                        # spoke index n = 1..N stands in for n >= 1
TOL = 1e-12

points = [("p",), ("q",)]
for a in A:
    points.append(("y", a))
    for n in range(1, N + 1):
        points.append(("x", a, n))


def s(a, t, n):
    """s_n(alpha, t) = min(1, |t - a_alpha| + 1/n)."""
    return min(1.0, abs(t - a) + 1.0 / n)


def block(u):
    """Which block of the partition D = {p,q} + stars the point lies in."""
    return "anchor" if u[0] in ("p", "q") else u[1]


def d(t, u, v):
    """The distance table of report §3.2."""
    if u == v:
        return 0.0
    if block(u) != block(v):
        return 1.0                       # cross-block pairs
    if block(u) == "anchor":
        return 1.0 + t                   # the reference pair {p,q}
    a = block(u)

    def radius(w):
        return 0.0 if w[0] == "y" else s(a, t, w[2])

    return radius(u) + radius(v)         # centre-spoke and spoke-spoke


# ------------------------------------------------------- (C1) metric axioms
def check_c1(ts):
    tri_fail = pos_fail = 0
    for t in ts:
        for u, v, w in itertools.permutations(points, 3):
            if d(t, u, w) > d(t, u, v) + d(t, v, w) + TOL:
                tri_fail += 1
                print("  TRIANGLE FAIL", t, u, v, w)
        for u, v in itertools.permutations(points, 2):
            if d(t, u, v) <= 0.0:
                pos_fail += 1
                print("  POSITIVITY FAIL", t, u, v)
    print(f"(C1) triangle violations: {tri_fail}, positivity violations: {pos_fail}")
    assert tri_fail == 0 and pos_fail == 0, "(C1) failed -- see the violations above"


# ------------------------------------------- (C2)/(C3) isolation radius delta
def delta_exact(t, u):
    """delta(u) = inf_{v != u} d(t,u,v), using the true infimum over all n >= 1.

    For a centre y_alpha the infimum over spokes is inf_n s_n(alpha,t)
    = min(1, |t - a_alpha|), which is *not* attained; the finite model would
    otherwise report a spuriously positive value.
    """
    if u[0] == "y":
        return min(1.0, min(1.0, abs(t - u[1])))
    return min(d(t, u, v) for v in points if v != u)


def check_c2_c3():
    for t in (0.5, 0.25, 0.0, 1.0):
        worst = min(delta_exact(t, u) for u in points)
        print(f"(C2) t={t!r:<5} not in A: min_u delta(u) = {worst:.6f} > 0 -> discrete")
        assert worst > 0.0
    for a in A:
        worst = min(delta_exact(a, u) for u in points)
        centre = delta_exact(a, ("y", a))
        print(f"(C3) t={a!r:<5} in A:     delta(y_a) = {centre:.6f}, min_u delta(u) = {worst:.6f}")
        assert centre == 0.0


# ------------------------------------------------------- (C4) bi-Lipschitz
def rho(t, u):
    return max(abs(d(t, x, y) - d(u, x, y)) for x in points for y in points)


def check_c4(samples=4000):
    random.seed(0)
    lo, hi = float("inf"), float("-inf")
    for _ in range(samples):
        t, u = random.random(), random.random()
        gap = abs(t - u)
        if gap == 0.0:
            continue
        ratio = rho(t, u) / gap
        lo, hi = min(lo, ratio), max(hi, ratio)
    print(f"(C4) rho(d_t,d_s)/|t-s| over {samples} random pairs: [{lo:.6f}, {hi:.6f}]")
    assert lo >= 1.0 - 1e-9 and hi <= 2.0 + 1e-9


if __name__ == "__main__":
    grid = [i / 200 for i in range(201)]
    check_c1(grid)
    check_c2_c3()
    check_c4()
    print("all spot-checks passed")
