import CubicTwoStage.BerendPhaseArc
import CubicTwoStage.BerendRaySubgroup
import CubicTwoStage.BerendAxisLattice
import CubicTwoStage.BerendUnitNoncritical

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1200000

namespace CubicTwoStage
namespace BerendModulusOneArc

open BerendPlanarArc BerendPhaseArc BerendBlockLastMile

/-- The imaginary-unit flow stays on the unit circle. -/
theorem scaleFlow_I_mem_unitCircle (t : ℝ) :
    scaleFlow Complex.I t ∈ unitCircle := by
  rw [mem_unitCircle, norm_scaleFlow _ (by simp), Complex.norm_I, Real.one_rpow]

/-- Any circle through `w₀` in a lift contains the normalized `arcThrough` arc
parametrized by the imaginary-unit flow. -/
theorem arcThrough_I_mem_of_circle {L : AddSubgroup Pt} {Y : Set (Torus L)}
    {w₀ : ℂ}
    (hcircle : ∀ μ ∈ unitCircle,
      (QuotientAddGroup.mk' L) (ofCplx (μ * w₀)) ∈ Y) (t : ℝ) :
    (QuotientAddGroup.mk' L) (BerendTangentNet.arcThrough w₀ Complex.I t) ∈ Y := by
  simpa [BerendTangentNet.arcThrough, mul_comm] using
    hcircle (scaleFlow Complex.I t) (scaleFlow_I_mem_unitCircle t)

/-- The principal-logarithm conjugation identity applies to the normalized arc:
`I` is off the negative real branch cut. -/
theorem arcThrough_I_conj (w₀ : ℂ) (t : ℝ) :
    BerendTangentNet.conjPt (BerendTangentNet.arcThrough w₀ Complex.I t) =
      BerendTangentNet.arcThrough (starRingEnd ℂ w₀) (starRingEnd ℂ Complex.I) t := by
  apply BerendTangentNet.arcThrough_conj
  rw [Complex.arg_I]
  intro h
  nlinarith [Real.pi_pos]

/-- At integer times the normalized arc interpolates powers of `I`. -/
theorem arcThrough_I_nat (w₀ : ℂ) (n : ℕ) :
    BerendTangentNet.arcThrough w₀ Complex.I n = ofCplx (w₀ * Complex.I ^ n) := by
  exact BerendTangentNet.arcThrough_nat w₀ Complex.I (by simp) n

/-- Explicit normalized exponential formula, with positive angular rate `π/2`. -/
theorem scaleFlow_I_eq_exp (t : ℝ) :
    scaleFlow Complex.I t = Complex.exp (((t * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [scaleFlow, Complex.log_I]
  push_cast
  ring_nf

/-- The placed arc is the explicit normalized exponential arc. -/
theorem arcThrough_I_eq_exp (w₀ : ℂ) (t : ℝ) :
    BerendTangentNet.arcThrough w₀ Complex.I t =
      ofCplx (w₀ * Complex.exp (((t * Real.pi / 2 : ℝ) : ℂ) * Complex.I)) := by
  rw [BerendTangentNet.arcThrough, scaleFlow_I_eq_exp]

/-- The angular rate of the normalized arc is positive. -/
theorem I_arc_rate_pos : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)

/-- The normalized arc has a nonzero planar tangent whenever its base is
nonzero. -/
theorem arcTangent_I_mem_plane_and_ne_zero {w₀ : ℂ} (hw₀ : w₀ ≠ 0) :
    BerendTangentNet.arcTangent w₀ Complex.I ∈ cplxPlane ∧
      BerendTangentNet.arcTangent w₀ Complex.I ≠ 0 := by
  constructor
  · exact ofCplx_mem _
  · intro h
    change ofCplx (w₀ * Complex.log Complex.I) = 0 at h
    have hc := congrArg cplxOf h
    rw [cplxOf_ofCplx] at hc
    have hzero : w₀ * Complex.log Complex.I = 0 := by
      exact hc.trans (by apply Complex.ext <;> rfl)
    have hlog : Complex.log Complex.I ≠ 0 := by
      apply BerendTangentNet.log_ne_zero (by simp)
      intro hi
      have him := congrArg Complex.im hi
      norm_num at him
    exact (mul_ne_zero hw₀ hlog) hzero

/-- A nonzero point of the complex plane has nonzero complex coordinate. -/
theorem cplxOf_ne_zero_of_mem_plane {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0) :
    cplxOf x ≠ 0 := by
  intro h
  apply hx0
  rw [← eq_ofCplx_cplxOf hx, h]
  funext i
  fin_cases i <;> simp [ofCplx]

/-- The corrected residual supplies an honest nonzero planar lift point. -/
theorem exists_planar_point_of_residual {L : AddSubgroup Pt} {Y : Set (Torus L)}
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    ∃ x : Pt, x ∈ cplxPlane ∧ x ≠ 0 ∧ (QuotientAddGroup.mk' L) x ∈ Y := by
  have hne : ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane).Nonempty := by
    rcases Set.eq_empty_or_nonempty ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane) with h | h
    · rw [h, closure_empty] at hacc
      exact absurd hacc (by simp)
    · exact h
  obtain ⟨x, ⟨hxY, hx0⟩, hxplane⟩ := hne
  refine ⟨x, hxplane, ?_, hxY⟩
  intro h
  apply hx0
  simp [h]

section UnitPrime

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The exact modulus-one branch places the normalized arc in the lift, for all
real parameters and hence in particular on the positive-length interval `[0,1]`. -/
theorem arcThrough_I_in_lift_of_modulus_one (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hB3 : MultIndepPair (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (D.unit_image u)‖ ^ l *
      ‖cplxOf (D.prime_image D.prime)‖ ^ k = 1)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) (t : ℝ) :
    (QuotientAddGroup.mk' L)
      (BerendTangentNet.arcThrough (cplxOf x) Complex.I t) ∈ Y := by
  apply arcThrough_I_mem_of_circle
  exact circle_in_lift_of_modulus_one D u hY hinv hB3 hlk hmod hx hx0 hxY

/-- Arc placement from the corrected planar residual.  The basepoint is the
complex coordinate of a nonzero point in the residual's planar lift. -/
theorem exists_arcThrough_I_of_modulus_one (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hB3 : MultIndepPair (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (D.unit_image u)‖ ^ l *
      ‖cplxOf (D.prime_image D.prime)‖ ^ k = 1)
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    ∃ w₀ : ℂ, w₀ ≠ 0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (QuotientAddGroup.mk' L) (BerendTangentNet.arcThrough w₀ Complex.I t) ∈ Y := by
  obtain ⟨x, hxplane, hx0, hxY⟩ := exists_planar_point_of_residual hacc
  refine ⟨cplxOf x, cplxOf_ne_zero_of_mem_plane hxplane hx0, ?_⟩
  intro t _ht
  exact arcThrough_I_in_lift_of_modulus_one D u hY hinv hB3 hlk hmod hxplane hx0 hxY t

/-- Proposition 4.2 in the exact modulus-one branch: arc placement, an expanding
member, and its forward invariance produce an infinite closed subgroup with a
translate contained in `Y`. -/
theorem exists_translate_raySubgroup_of_modulus_one (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hB3 : MultIndepPair (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (D.unit_image u)‖ ^ l *
      ‖cplxOf (D.prime_image D.prime)‖ ^ k = 1)
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane))
    {a : Pt} (hρ : 1 < ‖cplxOf a‖)
    (hinva : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y) :
    ∃ (b : Torus L) (e : Pt) (H : AddSubgroup (Torus L)),
      e ∈ cplxPlane ∧ e ≠ 0 ∧ Infinite H ∧ IsClosed (H : Set (Torus L)) ∧
      (∀ s : ℝ, 0 ≤ s → (QuotientAddGroup.mk' L) (s • e) ∈ H) ∧
      (∀ h ∈ H, b + h ∈ Y) := by
  obtain ⟨w₀, hw₀, harc⟩ :=
    exists_arcThrough_I_of_modulus_one D u hY hinv hB3 hlk hmod hacc
  apply BerendRaySubgroup.exists_translate_raySubgroup_of_arc hY hρ hw₀
    (c := Complex.I) (t' := 1) (by simp) ?_ zero_lt_one hinva harc
  intro h
  have him := congrArg Complex.im h
  norm_num at him

end UnitPrime

/-! ## Canonical unit/prime arithmetic for the exact branch -/

section Canonical

variable {K : Type*} [Field K] [NumberField K]

/-- Corrected B3, read on the two complex multipliers of the canonical model.
The proof uses injectivity of the complex field embedding, the unit norm, and
the prime absolute norm; it does not invoke the old multi-invariance axiom. -/
theorem multIndepPair_canonicalFieldModel (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    MultIndepPair
      (cplxOf (((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).unit_image ε))
      (cplxOf (((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).prime_image π)) := by
  intro l k hmul
  let φ := NumberFieldCubic.complexEmbedding K h
  have hmul' : φ ((((ε : numberFieldO K) : K) ^ l) * π ^ k) = φ 1 := by
    rw [map_mul, map_zpow₀, map_zpow₀, map_one]
    exact hmul
  have hK : (((ε : numberFieldO K) : K) ^ l) * π ^ k = 1 := φ.injective hmul'
  have hN : numberFieldAbsNorm K ((((ε : numberFieldO K) : K) ^ l) * π ^ k) = 1 := by
    rw [hK, map_one]
  rw [map_mul, map_zpow₀, map_zpow₀,
    (NumberFieldCubic.canonicalFieldModel K h).Nm_unit, one_zpow, one_mul, hπN] at hN
  have hR : ((p : ℝ)) ^ k = 1 := by
    convert congrArg (fun x : ℚ≥0 => (x : ℝ)) hN
    push_cast
    all_goals norm_num
  have hk : k = 0 := by
    by_contra hk
    exact absurd hR (zpow_ne_one_of_gt_one (a := (p : ℝ)) (by exact_mod_cast hp) hk)
  refine ⟨?_, hk⟩
  refine zpow_eq_one_imp_eq_zero (a := (((ε : numberFieldO K) : K))) hεpow ?_
  simpa [hk] using hK

/-- Canonical exact-modulus-one Proposition 4.2.  Both corrected B3 and the
expanding family member are obtained from the unit/prime arithmetic. -/
theorem exists_translate_raySubgroup_of_modulus_one_canonical (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    {Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice)}
    (hY : IsClosed Y)
    (hinv : ∀ i, ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct
      i '' Y ⊆ Y)
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).unit_image ε)‖ ^ l *
      ‖cplxOf (((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).prime_image π)‖ ^ k = 1)
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
      (NumberFieldCubic.canonicalFieldModel K h).lattice) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    ∃ (b : Torus (NumberFieldCubic.canonicalFieldModel K h).lattice) (e : Pt)
      (H : AddSubgroup (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice)),
      e ∈ cplxPlane ∧ e ≠ 0 ∧ Infinite H ∧ IsClosed (H : Set
        (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice)) ∧
      (∀ s : ℝ, 0 ≤ s → (QuotientAddGroup.mk'
        (NumberFieldCubic.canonicalFieldModel K h).lattice) (s • e) ∈ H) ∧
      (∀ h ∈ H, b + h ∈ Y) := by
  let D := (NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0
  have hB3 : MultIndepPair (cplxOf (D.unit_image ε))
      (cplxOf (D.prime_image D.prime)) :=
    multIndepPair_canonicalFieldModel h ε π hπO hπ0 hεpow p hp hπN
  obtain ⟨v, j, _hj, _ha, hC⟩ :=
    BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
      (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0 hεpow p
      (by exact_mod_cast hp) hπN
  have hρ : 1 < ‖cplxOf (D.mult v j)‖ :=
    lt_of_lt_of_le (by norm_num) (BerendBlockLastMile.two_le_norm_cplxOf_of_normC hC)
  have hinva : ∀ x : Pt,
      (QuotientAddGroup.mk' (NumberFieldCubic.canonicalFieldModel K h).lattice) x ∈ Y →
      (QuotientAddGroup.mk' (NumberFieldCubic.canonicalFieldModel K h).lattice)
        (ptMul (D.mult v j) x) ∈ Y := by
    intro x hx
    have hm := hinv (v, j) (Set.mem_image_of_mem (D.torusAct (v, j)) hx)
    rwa [D.torusAct_mk', D.family_act_eq_ptMul] at hm
  exact exists_translate_raySubgroup_of_modulus_one D ε hY hinv hB3 hlk hmod hacc hρ hinva

end Canonical

end BerendModulusOneArc
end CubicTwoStage

#print axioms CubicTwoStage.BerendModulusOneArc.scaleFlow_I_mem_unitCircle
#print axioms CubicTwoStage.BerendModulusOneArc.arcThrough_I_mem_of_circle
#print axioms CubicTwoStage.BerendModulusOneArc.arcThrough_I_conj
#print axioms CubicTwoStage.BerendModulusOneArc.arcThrough_I_nat
#print axioms CubicTwoStage.BerendModulusOneArc.scaleFlow_I_eq_exp
#print axioms CubicTwoStage.BerendModulusOneArc.arcThrough_I_eq_exp
#print axioms CubicTwoStage.BerendModulusOneArc.arcTangent_I_mem_plane_and_ne_zero
#print axioms CubicTwoStage.BerendModulusOneArc.cplxOf_ne_zero_of_mem_plane
#print axioms CubicTwoStage.BerendModulusOneArc.exists_planar_point_of_residual
#print axioms CubicTwoStage.BerendModulusOneArc.arcThrough_I_in_lift_of_modulus_one
#print axioms CubicTwoStage.BerendModulusOneArc.exists_arcThrough_I_of_modulus_one
#print axioms CubicTwoStage.BerendModulusOneArc.exists_translate_raySubgroup_of_modulus_one
#print axioms CubicTwoStage.BerendModulusOneArc.multIndepPair_canonicalFieldModel
#print axioms CubicTwoStage.BerendModulusOneArc.exists_translate_raySubgroup_of_modulus_one_canonical
