# SPDX-License-Identifier: GPL-3.0-or-later
r"""
cubic_twostage: certified 2-stage Euclidean coverings and continued fractions in number fields
of degree 2 and 3 (real quadratic, complex cubic and totally real cubic fields).
"""

from .twostage import TwoStage, continued_fraction, ellipsoid_points, evaluate_cf
from .verify import verify_certificate

__version__ = "1.0"
