import CubicTwoStage.BerendNormalizedCompactArc
import CubicTwoStage.BerendRaySubgroup

open Set Filter Topology

namespace CubicTwoStage
namespace BerendStageIAssembly

open BerendPlanarArc BerendPhaseArc BerendNormalizedCompactArc BerendTangentNet
open BerendBlockLastMile

/-- The unrestricted complex logarithmic rate of a normalized arc. -/
noncomputable def normalizedRate (c : ℂ) (β : ℝ) (l : ℤ × ℤ) : ℂ :=
  ((((l.1 : ℝ) * Real.log ‖c‖ : ℝ)) : ℂ) +
    ((((l.2 : ℝ) + (l.1 : ℝ) * β : ℝ)) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I)

/-- The normalized spiral is an exponential with an unrestricted rate. -/
theorem normalizedSpiral_eq_exp_rate {c : ℂ} (hc : c ≠ 0) (β : ℝ)
    (l : ℤ × ℤ) (t : ℝ) :
    normalizedSpiral c β l t = Complex.exp ((t : ℂ) * normalizedRate c β l) := by
  have hrad : ((‖c‖ ^ ((l.1 : ℝ) * t) : ℝ) : ℂ) =
      Complex.exp (((((l.1 : ℝ) * t) * Real.log ‖c‖ : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.rpow_def_of_pos (norm_pos_iff.mpr hc)]
    congr 1
    ring
  unfold normalizedSpiral phaseArc
  rw [hrad, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold normalizedRate
  push_cast
  ring

/-- The full normalized arc has the same exponential form. -/
theorem normalizedArc_eq_exp_rate {c : ℂ} (hc : c ≠ 0) (β : ℝ)
    (l : ℤ × ℤ) (w₀ : ℂ) (t : ℝ) :
    normalizedArc c β l w₀ t = w₀ * Complex.exp ((t : ℂ) * normalizedRate c β l) := by
  rw [normalizedArc, normalizedSpiral_eq_exp_rate hc]
  ring

/-- Every unrestricted exponential arc is a rescaling of the project's
`scaleFlow` arc.  Rescaling puts the logarithm's imaginary part in (-π, π]. -/
theorem exists_reparam_scaleFlow_exp (z : ℂ) (hz : z ≠ 0) :
    ∃ (d : ℂ) (κ : ℝ), d ≠ 0 ∧ d ≠ 1 ∧ 0 < κ ∧
      ∀ t : ℝ, scaleFlow d (κ * t) = Complex.exp ((t : ℂ) * z) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|z.im| / Real.pi)
  have hNp : 0 < N := by
    by_contra hn
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    have hnonneg : 0 ≤ |z.im| / Real.pi :=
      div_nonneg (abs_nonneg _) Real.pi_pos.le
    norm_num at hN
    linarith
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNp)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hmul : |z.im| < (N : ℝ) * Real.pi := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hN
    simpa [mul_comm] using h
  have hdiv : |z.im / (N : ℝ)| < Real.pi := by
    rw [abs_div, abs_of_pos hNr]
    apply (div_lt_iff₀ hNr).mpr
    simpa [mul_comm] using hmul
  have him : (z / (N : ℂ)).im = z.im / (N : ℝ) := by simp
  have hdiv' : |(z / (N : ℂ)).im| < Real.pi := by rwa [him]
  have hlog : Complex.log (Complex.exp (z / (N : ℂ))) = z / (N : ℂ) :=
    Complex.log_exp (abs_lt.mp hdiv').1 (le_of_lt (abs_lt.mp hdiv').2)
  refine ⟨Complex.exp (z / (N : ℂ)), (N : ℝ), Complex.exp_ne_zero _, ?_,
    by exact_mod_cast hNp, ?_⟩
  · intro hd
    apply hz
    have hzero : z / (N : ℂ) = 0 := by
      rw [← hlog, hd, Complex.log_one]
    simpa [hNc] using hzero
  · intro t
    unfold scaleFlow
    rw [hlog]
    congr 1
    push_cast
    field_simp [hNc]

/-- With a nontrivial integer direction and nonzero log-modulus, the
unrestricted rate is nonzero. -/
theorem normalizedRate_ne_zero {c : ℂ} (hlogc : Real.log ‖c‖ ≠ 0)
    {β : ℝ} {l : ℤ × ℤ} (hl : l ≠ 0) : normalizedRate c β l ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  have hr' : (l.1 : ℝ) * Real.log ‖c‖ = 0 := by
    simpa [normalizedRate, Complex.mul_re] using hr
  have hi' : ((l.2 : ℝ) + (l.1 : ℝ) * β) * (2 * Real.pi) = 0 := by
    simpa [normalizedRate, Complex.mul_im] using hi
  have hB : (l.2 : ℝ) + (l.1 : ℝ) * β = 0 := by
    rcases mul_eq_zero.mp hi' with h | h
    · exact h
    · exact False.elim ((mul_ne_zero (by norm_num) Real.pi_ne_zero) h)
  by_cases hl1 : l.1 = 0
  · rw [hl1] at hB
    simp only [Int.cast_zero, zero_mul, add_zero] at hB
    have hl2 : l.2 = 0 := by exact_mod_cast hB
    exact hl (Prod.ext hl1 hl2)
  · have hl1R : (l.1 : ℝ) ≠ 0 := by exact_mod_cast hl1
    exact hl1R ((mul_eq_zero.mp hr').resolve_right hlogc)

/-- The project’s named `arcThrough` really does include the normalized arc,
after rescaling time. -/
theorem exists_arcThrough_reparam_normalizedArc {c : ℂ} (hc : c ≠ 0)
    (hlogc : Real.log ‖c‖ ≠ 0) {β : ℝ} {l : ℤ × ℤ} (hl : l ≠ 0) (w₀ : ℂ) :
    ∃ (d : ℂ) (κ : ℝ), d ≠ 0 ∧ d ≠ 1 ∧ 0 < κ ∧ ∀ t : ℝ,
      arcThrough w₀ d (κ * t) = ofCplx (normalizedArc c β l w₀ t) := by
  obtain ⟨d, κ, hd0, hd1, hκ, hflow⟩ :=
    exists_reparam_scaleFlow_exp (normalizedRate c β l)
      (normalizedRate_ne_zero hlogc hl)
  refine ⟨d, κ, hd0, hd1, hκ, fun t => ?_⟩
  rw [arcThrough, hflow, normalizedArc_eq_exp_rate hc]

/-- Transport normalized-arc membership in any torus lift to the exact
`arcThrough` input of the tangent net and ray-subgroup assembly. -/
theorem exists_arcThrough_of_normalizedArc_mem
    {L : AddSubgroup Pt} {Y : Set (Torus L)} {c : ℂ} (hc : c ≠ 0)
    (hlogc : Real.log ‖c‖ ≠ 0) {β : ℝ} {l : ℤ × ℤ} (hl : l ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ≠ 0) {t' : ℝ} (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      (QuotientAddGroup.mk' L) (ofCplx (normalizedArc c β l w₀ t)) ∈ Y) :
    ∃ (w₁ d : ℂ) (κ : ℝ), w₁ ≠ 0 ∧ d ≠ 0 ∧ d ≠ 1 ∧ 0 < κ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) κ, arcThrough w₁ d s ∈
        (QuotientAddGroup.mk' L) ⁻¹' Y := by
  obtain ⟨d, κ, hd0, hd1, hκpos, hflow⟩ :=
    exists_arcThrough_reparam_normalizedArc hc hlogc hl w₀
  let T : ℝ := κ * t'
  have hT : 0 < T := mul_pos hκpos ht'
  refine ⟨w₀, d, T, hw₀, hd0, hd1, hT, ?_⟩
  intro s hs
  let t : ℝ := s / κ
  have ht : t ∈ Set.Icc (0 : ℝ) t' := by
    constructor
    · exact div_nonneg hs.1 hκpos.le
    · exact (div_le_iff₀ hκpos).mpr (by simpa [T, mul_comm] using hs.2)
  change (QuotientAddGroup.mk' L) (arcThrough w₀ d s) ∈ Y
  have hs_eq : s = κ * t := by
    dsimp [t]
    field_simp
  rw [hs_eq, hflow]
  exact harc t ht

end BerendStageIAssembly
end CubicTwoStage

#print axioms CubicTwoStage.BerendStageIAssembly.normalizedSpiral_eq_exp_rate
#print axioms CubicTwoStage.BerendStageIAssembly.normalizedArc_eq_exp_rate
#print axioms CubicTwoStage.BerendStageIAssembly.exists_reparam_scaleFlow_exp
#print axioms CubicTwoStage.BerendStageIAssembly.normalizedRate_ne_zero
#print axioms CubicTwoStage.BerendStageIAssembly.exists_arcThrough_reparam_normalizedArc
#print axioms CubicTwoStage.BerendStageIAssembly.exists_arcThrough_of_normalizedArc_mem
