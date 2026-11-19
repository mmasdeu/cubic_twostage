# SPDX-License-Identifier: GPL-3.0-or-later
"""Coverings and continued fractions in a real quadratic, a complex cubic and a totally real
cubic field.

Run:   python3 examples/fields.py        (needs the package: pip install .)"""
from sage.all import QQ, NumberField, PolynomialRing

from cubic_twostage import TwoStage, evaluate_cf, verify_certificate

x = PolynomialRing(QQ, "x").gen()
for f, name in [
    (x**2 - 14, "real quadratic Q(sqrt 14) (not norm-Euclidean)"),
    (x**3 - x**2 - 2 * x - 3, "complex cubic, d = -327 (not norm-Euclidean)"),
    (x**3 - x**2 - 6 * x + 1, "totally real cubic, d = 985"),
]:
    K = NumberField(f, "a")
    S = TwoStage(K)
    N = S.find_covering()
    print(f"{name}: covering of level N = {N}, {len(S.cert)} boxes,",
          "verified:", verify_certificate(S, S.cert))
    a = K.gen()
    for y in [(3 + 5 * a) / (2 - 7 * a), (1 + a + a**2) / 11]:
        qs = S.continued_fraction(y)
        assert evaluate_cf(qs) == y and all(q.is_integral() for q in qs)
        print(f"   {y} = {qs}")
