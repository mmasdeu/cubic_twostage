==============
cubic_twostage
==============

For installation and basic usage instructions please see the main GitHub repository
(https://github.com/mmasdeu/cubic_twostage).

A ring of integers `O_K` is *2-stage Euclidean* if every pair `\alpha, \beta \in O_K`,
`\beta \neq 0`, has a decreasing division chain of length at most two:
`\alpha = q_1 \beta + r_1`, `\beta = q_2 r_1 + r_2` with `|\mathrm{Nm}(r_2)| < |\mathrm{Nm}(\beta)|`
(or `r_1 = 0`, or already `|\mathrm{Nm}(r_1)| < |\mathrm{Nm}(\beta)|`).  Then every element of
`K` has a finite continued fraction expansion with partial quotients in `O_K`.

The **cubic_twostage** package proves that a given number field is 2-stage Euclidean, by
computing a certified covering of a fundamental domain of `O_K` in `K \otimes \mathbb{R}`
by the regions `\{x : |\mathrm{Nm}(x - [q_1, q_2])| < 1/|\mathrm{Nm}(q_2)|\}`, and then
computes continued fractions with it.  It generalizes the algorithm of [GM]_ for real
quadratic fields to every signature; it is tested for real quadratic fields, complex cubic
fields (the subject of [M]_, where all 550 complex cubic fields of class number one with
`|d| < 5000` are proved to be 2-stage Euclidean) and totally real cubic fields.

For complex cubic fields it also contains exact tests that a field is not norm-Euclidean,
and lower bounds for the *smooth level* (the largest norm of the denominators `q_2` needed).

Quick example::

    sage: from cubic_twostage import TwoStage, evaluate_cf
    sage: S = TwoStage("x^3 - x^2 - 2*x - 3")    # complex cubic, d = -327
    sage: S.find_covering()                       # level N of the covering found
    3
    sage: t = S.K.gen()
    sage: S.continued_fraction((2 + 3*t + 5*t^2) / (7 - t))  # random (depends on the covering)
    [t^2 + t, 1, t^2 - 3*t, 1, -t^2 + t, t]

.. [GM] X. Guitart, M. Masdeu. *Continued fractions in 2-stage Euclidean quadratic fields*.
   Mathematics of Computation 82 (2013). arXiv:1106.0856.
.. [M] M. Masdeu. *Two-stage Euclidean algorithms and continued fractions in complex cubic
   fields*. Draft, in this repository (``writeup/``).

The code is licensed under the GNU General Public License, version 3 or (at your option) any
later version.

.. toctree::
   :maxdepth: 2

   highlevel
   witnesses

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
