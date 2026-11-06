# Strategy outline: Guitart–Masdeu (arXiv:1106.0856) in degree 3 and 4

Paper: X. Guitart, M. Masdeu, "Continued fractions in 2-stage euclidean quadratic fields"
(Math. Comp.). Source in ../paper/. Main theorem: an algorithm that covers the fundamental
domain D of a real quadratic field by hyperbolic regions
V(q) = {x : |Nm(x - q)| < 1/|Nm(q2)|}, q = [q1, q2]; it terminates iff F is 2-stage euclidean,
and the covering computes continued fractions.

## Setting
F of degree n = 3, 4, signature (r, s), class number 1. Unit rank r+s-1 >= 1, so
Cooke–Vaserstein applies. Replace R^2 by Minkowski space R^r x C^s,
Nm(x) = prod |x_v|^{e_v}; D = parallelotope spanned by an integral basis.

## Carries over verbatim
- Cooke's criterion (Prop 2.1): r2 = beta * q2 * ([q1,q2] - alpha/beta) — pure algebra.
- Reduction to compact D (Prop 2.2), termination theorem (compactness).
- Lemma 4.3: CF2(m) ⊂ (1/t) O_F, t = lcm(1..m); norm now scales by t^n.

## Needs changes
1. Box lemma: |Nm(x-q)| is a product of per-place functions; sup over a box (intervals at
   real places, squares at complex ones) = product of per-factor maxima -> one coordinatewise
   "farthest corner" test, O(n) instead of 2^n corners.
2. Boxes in lattice coordinates a in [0,1]^n with interval bounds per embedding (no wasted
   R0 ⊃ D). Termination via Lebesgue-number argument. Ball/interval arithmetic for rigour.
3. Centres: [q1,q2] mod O_F = u/alpha, u a unit mod alpha -> image of O_F^* in
   (O_F/alpha)^*, not all of alpha^{-1}O_F/O_F. Residue degree f primes give radius ~ p^{-f}.
4. Translates: one slab bounds gamma at one place only; T must bound gamma in all directions.
5. Symmetry: u*[q1,q2] = [u q1, u^{-1} q2] — covering is invariant under O_F ⋊ O_F^*.

## Finiteness theorem (Thm 4.1) needs M(F) -> infinity
Known for unit rank 1 (complex cubic (1,1), totally complex quartic (0,2): Davenport) and
cyclic cubics (Heilbronn). Open for (3,0), (2,1), (4,0) — related to Littlewood /
Cassels–Swinnerton-Dyer. So "finitely many m-smooth euclidean fields" is conditional there.

## Check
Cooke–Weinberger (GRH) bounded-stage euclideanity: verify whether the stage bound is 2 in
every signature before conjecturing 2-stage euclideanity for all class-number-1 cubics/quartics.
