/-
# Completed Stage I for the canonical complex-cubic unit-prime model

The normalized backward-orbit arc is converted to `arcThrough` in
`BerendNormalizedArcIntegration`.  Proposition 4.2 is supplied by the tangent
ray/subgroup chain, and Proposition 4.3 plus canonical B1 by
`BerendStageIProp43` and `BerendCanonicalB1`.  No arc, density, annulus, or
additional B1 hypothesis remains.  The old `berend_multi_invariance` axiom is
not used.
-/
import CubicTwoStage.BerendCanonicalNormalizedArc
import CubicTwoStage.BerendNormalizedArcIntegration
import CubicTwoStage.BerendStageIProp43
import CubicTwoStage.BerendCanonicalB1
import CubicTwoStage.BerendPlanarOnly

open Set Filter Topology
open scoped Pointwise NumberField

namespace CubicTwoStage
namespace BerendStageIAssembly

open BerendPlanarArc BerendNormalizedCompactArc BerendStageIAssembly

/-- **Stage I for the canonical complex-cubic unit-prime model**, from the
paper's arithmetic hypotheses.  Every analytic and arithmetic dependency is
proved, including normalized arc placement, B1, and Proposition 4.3. -/
theorem zeroNonisolatedFull_canonical
    {K : Type*} [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : p.Prime) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    BerendDichotomy.ZeroNonisolatedFull
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct := by
  apply BerendStageIPlanarOnly.zeroNonisolatedFull_canonical_planarOnly'
    h ε π hπO hπ0 hεpow p hp.one_lt hπN
  · simpa only [lamAbs_zero_eq_abs] using
      (BerendUnitNoncritical.lamAbs_real_ne_one
        (NumberFieldCubic.canonicalFieldModel K h) ε hεpow)
  · intro Y hY hinv hacc
    obtain ⟨a, w₀, l, t', ha, hw₀, hl, _hl0, ht', hinva, harc⟩ :=
      exists_normalizedArc_canonical
        h ε π hπO hπ0 hεpow p hp.one_lt hπN hY hinv hacc
    have hc : cplxOf a ≠ 0 := by
      rw [← norm_ne_zero_iff]
      linarith
    have hlog : Real.log ‖cplxOf a‖ ≠ 0 := ne_of_gt (Real.log_pos ha)
    obtain ⟨w₁, d, T, hw₁, hd0, hd1, hT, harcd⟩ :=
      exists_arcThrough_of_normalizedArc_mem hc hlog hl hw₀ ht' harc
    exact BerendStageIProp43.eq_univ_canonical_of_arcThrough
      h ε π hπO hπ0 hp hπN hεpow hY hinv hw₁ hd0 hd1 hT harcd

end BerendStageIAssembly
end CubicTwoStage

#print axioms CubicTwoStage.BerendStageIAssembly.zeroNonisolatedFull_canonical
