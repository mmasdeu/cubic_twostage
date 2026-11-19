# SPDX-License-Identifier: GPL-3.0-or-later
r"""
Independent verification of covering certificates.

A certificate is a list of tuples ``(m, depth, class, g)``: the dyadic box
`2^{-depth}(m + [0,1]^n)` of the fundamental domain `[0,1]^n` (lattice coordinates) lies in
the region `|\mathrm{Nm}(x - c)| < 1/n_c` of the centre `c = class[0] + g`, where
``class = (coords, n_c, alpha, r)`` with `c \equiv r/\alpha \pmod{O_K}`.
:func:`verify_certificate` checks, independently of the search:

(i) every box lies in `[0,1]^n`, the boxes are pairwise distinct and non-nested, and their
    volumes add up to exactly 1 (so they tile the fundamental domain);
(ii) every centre class has `|\mathrm{Nm}(\alpha)| = n_c`, ``coords`` `= r/\alpha` modulo
     `\ZZ^n`, and `r` is congruent modulo `\alpha` to a unit (so `c = [q_1, q_2]` modulo
     `O_K` with `|\mathrm{Nm}(q_2)| = n_c`);
(iii) every (box, centre) inequality, with interval arithmetic;

and computes continued fractions of random elements with the certificate, checking them
exactly.

Command line (``python -m cubic_twostage.verify``)::

    python -m cubic_twostage.verify [certificate_dir] [--shard i/n]

checks every ``cert_*.pkl`` in the directory (default ``data/certificates``).
"""

import glob
import pickle
import random
import sys

from sage.all import QQ, ZZ, Integer, vector

from .twostage import TwoStage, evaluate_cf


def _in_image(S, I, r):
    """``True`` iff ``r`` is congruent modulo ``I`` to a unit: closes ``{1}`` under
    multiplication by the generators of the unit group modulo ``I`` (written independently of
    :meth:`TwoStage.unit_residues`, which produced the centres)."""
    target = tuple(I.reduce(r).list())
    one = I.reduce(S.K(1))
    seen = {tuple(one.list())}
    todo = [one]
    while todo:
        u = todo.pop()
        if tuple(u.list()) == target:
            return True
        for g in S.unit_gens:
            v = I.reduce(u * g)
            k = tuple(v.list())
            if k not in seen:
                seen.add(k)
                todo.append(v)
    return False


def _sup_norm(S, m, d, b):
    """Interval upper bound of |Nm(x - b)| on the box 2^-d (m + [0,1]^n) (written
    independently of :meth:`TwoStage.certify`; uses only the interval embedding ``S.Mi``).
    """
    RIF, n = S.RIF, S.n
    I = [RIF(QQ(m[j]) / 2**d - b[j], QQ(m[j] + 1) / 2**d - b[j]) for j in range(n)]
    A = [RIF(sum(S.Mi[i][j] * I[j] for j in range(n)).abs().upper()) for i in range(n)]
    v = RIF(1)
    for i in range(S.r1):
        v *= A[i]
    for k in range(S.r2):
        v *= A[S.r1 + 2 * k] ** 2 + A[S.r1 + 2 * k + 1] ** 2
    return v


def verify_certificate(poly, cert, n_cf=20, seed=7):
    r"""
    Verify a covering certificate; raise ``AssertionError`` if a check fails.

    INPUT:

    - ``poly`` -- defining polynomial of the field (or a :class:`TwoStage`)
    - ``cert`` -- the certificate (list of ``(m, depth, class, g)``)
    - ``n_cf`` -- number of random continued fractions to check

    OUTPUT: a dictionary with the number of boxes, centre classes and the level `N`.

    EXAMPLES::

        sage: from cubic_twostage import TwoStage, verify_certificate
        sage: S = TwoStage("x^2 - 14"); S.find_covering()
        2
        sage: verify_certificate(S, S.cert)
        {'N': 2, 'boxes': ..., 'classes': 2}

    A certificate with a box removed is rejected::

        sage: verify_certificate(S, S.cert[1:])
        Traceback (most recent call last):
        ...
        AssertionError: volume
    """
    S = poly if isinstance(poly, TwoStage) else TwoStage(poly)
    K, n = S.K, S.n
    rnd = random.Random(seed)
    # (i) boxes
    keys = [(c[1],) + tuple(c[0]) for c in cert]
    assert all(len(k) == n + 1 for k in keys), "dimension"
    assert all(0 <= mi < 2**d for d, *m in keys for mi in m), "box outside the domain"
    kset = set(keys)
    assert len(kset) == len(keys), "duplicate box"
    assert sum(QQ(1) / 2 ** (n * d) for d, *m in keys) == 1, "volume"
    assert not any(
        (e,) + tuple(mi >> (d - e) for mi in m) in kset
        for d, *m in kset
        for e in range(d)
    ), "nested boxes"
    # (ii) centre classes
    seen = set()
    for m, d, ci, g in cert:
        key = (tuple(ci[0]), ci[1], tuple(ci[2].list()), tuple(ci[3].list()))
        if key in seen:
            continue
        al, r = K(list(ci[2].list())), K(list(ci[3].list()))
        assert abs(al.norm()) == ci[1], "norm of alpha"
        assert S.coords(r / al) - vector(QQ, ci[0]) in ZZ**n, "class"
        assert ci[1] == 1 or _in_image(S, K.ideal(al), r), "r is not a unit residue"
        seen.add(key)
    # (iii) every (box, centre) inequality with interval arithmetic
    for m, d, ci, g in cert:
        b = [ci[0][j] + Integer(g[j]) for j in range(n)]
        assert _sup_norm(S, m, d, b) < S.RIF(1) / ci[1], ("box", m, d)
    # continued fractions of random elements
    S.build_lookup(cert)
    t = K.gen()
    for _ in range(n_cf):
        num = sum(rnd.randint(-999, 999) * t**i for i in range(n))
        den = 0
        while den == 0:
            den = sum(rnd.randint(-99, 99) * t**i for i in range(n))
        x = num / den
        qs = S.continued_fraction(x)
        assert evaluate_cf(qs) == x and all(
            q.is_integral() for q in qs
        ), "continued fraction"
    return dict(boxes=len(cert), classes=len(seen), N=max(c[2][1] for c in cert))


def main(args=None):
    """Command line entry point: verify every certificate in a directory."""
    import sage.all  # noqa: F401  (needed before unpickling)

    args = list(sys.argv[1:] if args is None else args)
    shard = (0, 1)
    if "--shard" in args:
        k = args.index("--shard")
        i, n = args[k + 1].split("/")
        shard = (int(i), int(n))
        del args[k : k + 2]
    cdir = args[0] if args else "data/certificates"
    files = sorted(glob.glob(cdir + "/cert_*.pkl"))
    ok = 0
    for p in files[shard[0] :: shard[1]]:
        with open(p, "rb") as fi:
            f, cert = pickle.load(fi)
        try:
            res = verify_certificate(f, cert)
        except AssertionError as e:
            print("FAILED", p, e, flush=True)
            continue
        ok += 1
        print("ok", p, res["boxes"], "boxes", res["classes"], "classes", flush=True)
    print("verified", ok, "of", len(files[shard[0] :: shard[1]]), "certificates")
    return ok == len(files[shard[0] :: shard[1]])


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
