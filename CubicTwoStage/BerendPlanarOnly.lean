/-
# Stage I for the canonical complex cubic: only the planar case remains

Swarm `smw97otfd`, member `m2`, direction `d2`.  This file is the **composition**
of the two proved arithmetic densities of Stage I for the block model of
`CubicTwoStage/BerendStageIBlockAxis.lean`:

* `hscal` — density of the real multipliers `{μ_{u π^j} 0}` in `ℝ`; proved by
  member `m1`, direction (A), in `BerendStageIScalar.lean`
  (`BerendStageIScalar.dense_range_mult_zero`), and
* `haxis` — density of `coord {0} + lattice`; proved by member `m2`,
  direction (B), in `AxisLattice.lean`
  (`BerendAxisLattice.haxis_canonicalFieldModel`).

The result is that `BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar`
for `canonicalFieldModel K h` needs **neither** of the two densities any more:
Stage I for the canonical complex cubic is reduced to

* the prime/unit arithmetic data (`hεpow`, `p` prime, `Nm π = p`, `|σ₁ ε| > 1`),
  which are hypotheses about the number field, not about the dynamics, and
* `hplanar`, the accumulation case on the complex plane.

`hplanar` is the genuine remaining Stage I obligation (direction (C)/(D));
nothing about it is assumed here beyond its explicit statement.

Axiom audit at the end: only `propext`, `Classical.choice`, `Quot.sound`.
The scalar predicates in this file use the repaired non-isolated accumulation of
`Y \ {0}`.
-/
import CubicTwoStage.BerendAxisLattice
import CubicTwoStage.BerendStageIScalar

open Set Filter Topology
open scoped Pointwise NumberField

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendStageIPlanarOnly

/-- **Stage I for the canonical complex cubic, planar case only.**

Both arithmetic densities of `BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar`
are discharged: `hscal` by `BerendStageIScalar.dense_range_mult_zero` and `haxis`
by `BerendAxisLattice.haxis_canonicalFieldModel`.  What remains as the named
residual is `hplanar`. -/
theorem zeroNonisolatedFull_canonical_planarOnly {K : Type*} [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hε1 : 1 < |(NumberFieldCubic.canonicalFieldModel K h).σ
      (((ε : numberFieldO K) : K)) 0|)
    (hplanar : ∀ Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice),
      IsClosed Y →
      (∀ i, ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct
        i '' Y ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
        (NumberFieldCubic.canonicalFieldModel K h).lattice) ⁻¹' (Y \ {0}) ∩
          {x : Pt | x 0 = 0}) →
      Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar
    (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0 hε1
    (BerendStageIScalar.dense_range_mult_zero (NumberFieldCubic.canonicalFieldModel K h)
      ε π hπO hπ0 hεpow p hp hπN)
    (BerendAxisLattice.haxis_canonicalFieldModel h) hplanar

/-- The same statement with the `FieldModel` kept abstract: if the complex
projection of the lattice is dense and the multiplier set is dense, only the
planar case is left. -/
theorem zeroNonisolatedFull_fieldModel_planarOnly {K : Type*} [Field K]
    {𝒪 : Subring K} {Nm : AbsNorm K} (FM : FieldModel K 𝒪 Nm)
    (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → ((ε : 𝒪) : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (hε1 : 1 < |FM.σ (((ε : 𝒪) : K)) 0|)
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hplanar : ∀ Y : Set (Torus FM.lattice), IsClosed Y →
      (∀ i, (FM.toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk' FM.lattice) ⁻¹' (Y \ {0}) ∩
        {x : Pt | x 0 = 0}) → Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull (FM.toModel ε π hπO hπ0).torusAct :=
  BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar FM ε π hπO hπ0 hε1
    (BerendStageIScalar.dense_range_mult_zero FM ε π hπO hπ0 hεpow p hp hπN)
    haxis hplanar

/-- **The same, with no expansive-direction hypothesis at all.**  Only
`|σ₁ ε| ≠ 1` is kept (which the arithmetic supplies from `hεpow`, see
`BerendUnitNoncritical`); the proof runs on `ε` or on `ε⁻¹`, both of which are
valid unit indices. -/
theorem zeroNonisolatedFull_canonical_planarOnly' {K : Type*} [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεne1 : |(NumberFieldCubic.canonicalFieldModel K h).σ
      (((ε : numberFieldO K) : K)) 0| ≠ 1)
    (hplanar : ∀ Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice),
      IsClosed Y →
      (∀ i, ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct
        i '' Y ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
        (NumberFieldCubic.canonicalFieldModel K h).lattice) ⁻¹' (Y \ {0}) ∩
          {x : Pt | x 0 = 0}) →
      Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  BerendStageIScalar.zeroNonisolatedFull_fieldModel_of_planar_choice
    (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp hπN hεne1
    (BerendAxisLattice.haxis_canonicalFieldModel h) hplanar

end BerendStageIPlanarOnly
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendStageIPlanarOnly.zeroNonisolatedFull_canonical_planarOnly
#print axioms CubicTwoStage.BerendStageIPlanarOnly.zeroNonisolatedFull_fieldModel_planarOnly
#print axioms CubicTwoStage.BerendStageIPlanarOnly.zeroNonisolatedFull_canonical_planarOnly'
#print axioms CubicTwoStage.BerendStageIScalar.dense_range_mult_zero
#print axioms CubicTwoStage.BerendAxisLattice.haxis_canonicalFieldModel
