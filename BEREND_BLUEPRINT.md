# Completed Berend blueprint

## 1. Final results

This blueprint describes the completed canonical Berend plan, not a proposed
route. Every declaration below is proved and included by `CubicTwoStage.lean`.

| Result | Declaration |
|---|---|
| Canonical Stage I | `CubicTwoStage.BerendStageIAssembly.zeroNonisolatedFull_canonical` |
| Full multi-invariance | `CubicTwoStage.BerendStageIAssembly.dichotomy_canonical` |
| Canonical Theorem 3.6 | `CubicTwoStage.NumberFieldCubic.thm_uncovered_canonical` |
| Generic corrected uncovered theorem | `CubicTwoStage.thm_uncovered` and `thm_uncovered_field` |
| Generic corrected introduction theorem | `CubicTwoStage.thm_intro_equiv` |

The false literal `berend_multi_invariance` axiom has been removed. The generic
uncovered and introduction theorems use a corrected proposition `H`, supplied
by `BerendMultiInvarianceCorrected`; the canonical theorem constructs `H` from
the proved dynamics and coprime Proposition IV.1.

## 2. Normalized arc placement and Stage I

### Corrected residual

`BerendDichotomy.ZeroNonisolatedFull D.torusAct` says that every closed
forward-invariant set `Y` with `0 ∈ closure (Y \ {0})` is the whole torus.
The scalar and lattice densities reduce this to accumulation through
`(mk' L)⁻¹'(Y \ {0}) ∩ cplxPlane`.

### Backward orbit and phase lattice

`BerendComplexBackwardOrbit` constructs a backward orbit from accumulation at
zero. Its normalized samples `c^(-⌊jα⌋) d^j` remain in the forward-invariant
planar lift. Here
`α = log ‖d‖ / log ‖c‖`, `β = phaseOf c`, and `δ = phaseOf d - αβ`.

Corrected B3 proves non-torsion of
`normalizedPoint α δ : (ℝ/ℤ)²`. Compact closure of the lift of this cyclic
point, together with the integral-functional separation theorem, provides a
nonzero integral direction whose real line is in the compact cyclic closure.
A positive radial coefficient is obtained in the irrational-rate case.

### Rational and irrational arcs

In the irrational-rate branch, convergence of normalized samples on this line
places a positive-length spiral in the closed invariant set. In the rational
branch, clearing denominators produces an elliptic arc; the denominator change
preserves multiplicative independence. The phase-density predicates are not
assumed in either branch.

`exists_normalizedArc_canonical` packages these constructions with the expanding
member already produced from the unit/prime arithmetic. Its unrestricted
exponential rate is
`l₁ log ‖c‖ + 2πi(l₂ + l₁β)`. Rescaling by a suitable natural `N` puts the
imaginary part in the principal logarithm branch, so
`log (exp (z/N)) = z/N`. `exists_arcThrough_of_normalizedArc_mem` therefore
places an exact `arcThrough` arc on a positive interval.

### Ray closure and Proposition 4.2

The expanding tangent-net produces arbitrarily long segment approximations and
a whole ray. Its closure is a closed additive subgroup in the compact torus.
The compact-semigroup argument proves inverses: forward times yield return
sequences, whose predecessors converge to negatives. Preconnectedness and
nonzero lattice direction prove that this subgroup is infinite. Its translate
by the limiting torus basepoint lies in the closed invariant set. This gives
Proposition 4.2 without requiring a planar basepoint or subgroup invariance.

## 3. Canonical B1 and Proposition 4.3

Canonical B1 is constructed in `exists_canonical_B1_intLact`. If `π` and `επ`
both had positive rational powers, absolute norms would give cubes `±p` for
both, forcing `ε⁶ = 1`, contradicting `hεpow`. One of `(1,1)` and `(ε,1)` is
therefore a B1 witness. Lattice-basis transport and absence of rational roots
show that every positive power has irreducible integral characteristic
polynomial.

The characterwise Proposition 4.3 has four parts:

1. An integral lattice-character group and equivalence with the integral dual.
2. Infinite `H` gives its annihilator infinite index, hence strict rank drop.
3. Rationalization, covector independence following from B1, and finite
   van der Waerden coloring rule out a finite family whose iterates cover every
   positive time in the annihilator.
4. Encoded prefixes select a sequence on which every nonzero character is
   eventually nontrivial. Normalized Haar measures on the closed image groups,
   Stone--Weierstrass density of the character algebra, and finite ball covers
   then produce one iterate that is an arbitrary fine net.

The final `exists_canonical_unitPrime_net` gives this net for every infinite
closed `H`. No invariance of `H` is assumed.

`eq_univ_of_iterate_net_translate` fills the last gap. For each `x`, apply the
net at `x - σ^n b`; then the iterate of `b + H` meets every ball around `x`.
Since it is contained in the closed invariant set, `x` belongs there. Therefore
`Y = univ`, completing Propositions 4.2 and 4.3.

## 4. Coprime Proposition IV.1 and the full dichotomy

For distinct rational primes `p,q`, `propIV1_unitPrime'_canonical` gives coprime
Proposition IV.1 from the absolute norm of `π`. It uses the degree-one
unramified-prime arithmetic already developed in the repository: ideal norm and
comaximality, quotient representatives, coprime saturation on the relevant
multiplicative levels, and injectivity for unit-prime multipliers.

The expanding margin gives finite kernels and finite torsion. Together with
Stage I, this closes all §5 propagation and returns
`BerendStageIAssembly.dichotomy_canonical`.

Canonical Theorem 3.6 uses `p.Prime`, required by coprime IV.1. It chooses a
larger auxiliary prime `q`, constructs the full Berend proposition, and applies
the generic corrected uncovered theorem. This makes the primality assumption
explicit; a composite absolute norm is not treated as prime.

## 5. Generic corrected paper statements

`thm_uncovered` and `thm_uncovered_field` transport the corrected
`BerendMultiInvarianceCorrected` proposition `H` through the closure-of-orbits,
periodic-orbit, and representative arguments. `thm_intro_equiv` assembles the
same uncovered representation with the geometric two-stage equivalence.

For the canonical complex cubic model, `H` is no longer an external assumption:
`thm_uncovered_canonical` constructs it from Stage I and Proposition IV.1.

## 6. Trust boundary and validation

Every Berend-facing public theorem above audits with only
`propext`, `Classical.choice`, and `Quot.sound`. The old Berend axiom and its
legacy consumers have been removed. No `sorry` or replacement axiom was added.

The only custom axioms left in the project are the independent
`thm_main_computational_input` and `thm_smooth_computational_input` in
`Main.lean`. They are outside the Berend proof and are not presented as proved
mathematics here. An arbitrary-family version of the corrected Berend theorem
is also outside the canonical scope completed by this blueprint.

Verification used repeated module and worker audits, an independent rebuild of
all normalized-arc/Proposition-4.3 sources, and the final full project build
`jmw9uaao4`, which completed every module and `CubicTwoStage.lean` with exit
status zero. Reproduce with:

```sh
export LEAN_PATH="$PWD:$LEAN_PATH"
./check.sh
```
