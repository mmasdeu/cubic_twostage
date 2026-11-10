/-
# Canonical unit-prime dichotomy after Stage I

This closes the existing §5 wrapper with the completed canonical Stage I and the
coprime Proposition IV.1 input.  The old multi-invariance axiom is not used.
-/
import CubicTwoStage.BerendCompleteStageI
import CubicTwoStage.BerendAssembly
import CubicTwoStage.BerendIV1Arith

set_option linter.style.haveILetI false

open Set

namespace CubicTwoStage
namespace BerendStageIAssembly

/--
Full Berend dichotomy for the canonical complex-cubic unit-prime model.
`q` is an auxiliary prime distinct from `p`, as used by the coprime level
argument; no separate dynamical hypothesis remains.
-/
theorem dichotomy_canonical
    {K : Type*} [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    BerendDichotomy.Dichotomy
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct := by
  let D := (NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K h).lattice) :=
    NumberFieldCubic.discreteTopology_canonicalFieldModel_lattice K h
  letI : IsZLattice ℝ (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K h).lattice) :=
    NumberFieldCubic.isZLattice_canonicalFieldModel_lattice K h
  obtain ⟨u, j, _hj, ha, hC⟩ :=
    BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
      (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0 hεpow p
      (by exact_mod_cast hp.one_lt) hπN
  exact BerendAssembly.dichotomy_unitPrime D (u, j) ha hC
    (zeroNonisolatedFull_canonical h ε π hπO hπ0 hεpow p hp hπN)
    (BerendIV1Arith.propIV1_unitPrime'_canonical
      h ε π hπO hπ0 hεpow p q hp hq hpq hπN)

end BerendStageIAssembly
end CubicTwoStage

#print axioms CubicTwoStage.BerendStageIAssembly.dichotomy_canonical
