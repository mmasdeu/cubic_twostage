# SPDX-License-Identifier: GPL-3.0-or-later
"""Continued fractions in the field of discriminant -327 using a stored covering certificate.

Run from the repository root (with the package installed):   python3 examples/continued_fraction.py
Needs samples/certificates/cert_327_-1_-2_-3.pkl (included)."""
import os, sys, pickle
import sage.all                      # must be imported before unpickling certificates
from cubic_twostage import TwoStage, evaluate_cf

poly, cert = pickle.load(open("samples/certificates/cert_327_-1_-2_-3.pkl", "rb"))
S = TwoStage(poly)                   # K = Q(t), t^3 - t^2 - 2t - 3 = 0, d = -327
t = S.K.gen()
S.build_lookup(cert)                 # dyadic-box dictionary from the certificate

x = (2 + 3*t + 5*t**2) / (7 - t)     # = (194 + 223 t + 268 t^2)/277
qs = S.continued_fraction(x)
print("x  =", x)
print("CF =", qs)                    # [t^2 + t, 1, t^2 - 3t, 1, -t^2 + t, t]
assert evaluate_cf(qs) == x and all(q.is_integral() for q in qs)
print("evaluates back to x; all partial quotients are algebraic integers")
