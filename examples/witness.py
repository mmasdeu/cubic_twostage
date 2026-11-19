# SPDX-License-Identifier: GPL-3.0-or-later
"""Exact test that the field of discriminant -327 is not norm-Euclidean (Section 6 of the paper).

x0 = 2/33 + 20/33 t + 5/11 t^2 satisfies min_g |Nm(x0 - g)| >= 1 (in fact 101/99).
Run from the repository root (with the package installed):   python3 examples/witness.py"""
import os, sys
from sage.all import QQ
from cubic_twostage import TwoStage
from cubic_twostage.witness_orbit import OrbitWitness

S = TwoStage("x^3 - x^2 - 2*x - 3")
O = OrbitWitness(S)                                  # translate set D, unit-orbit machinery
a = [2, 20, 15]                                      # x0 = a/33 in lattice coordinates
print("x0 =", S.elt([QQ(c) / 33 for c in a]))
print("witness (fast search):", O.verify(a, 33))
# rigorous re-check with a provably complete translate set
from cubic_twostage.certify_lower import RigorousLower
R = RigorousLower(S)
print("witness (rigorous check):", R.uncovered(a, 33, 1)[0], "| |D| =", len(R.D))
