import CubicTwoStage.BerendComplexBackwardOrbit
import CubicTwoStage.BerendModulusOneArc

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1200000

namespace CubicTwoStage
namespace BerendNormalizedCompactArc

open BerendPlanarArc BerendPhaseArc BerendBlockLastMile NumberFieldCubic

section UnitPrime

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- Torus invariance gives multiplier invariance of the complex planar lift. -/
def planarLift (L : AddSubgroup Pt) (Y : Set (Torus L)) : Set ℂ :=
  {z : ℂ | (QuotientAddGroup.mk' L) (ofCplx z) ∈ Y}

theorem isClosed_planarLift {Y : Set (Torus L)} (hY : IsClosed Y) :
    IsClosed (planarLift L Y) := by
  exact hY.preimage (continuous_quotient_mk'.comp ofCplx_continuous)

theorem planarLift_mul_mem (D : UnitPrimeModel L 𝒪) {Y : Set (Torus L)}
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y) (u : 𝒪ˣ) (j : ℕ)
    {z : ℂ} (hz : z ∈ planarLift L Y) :
    cplxOf (D.mult u j) * z ∈ planarLift L Y := by
  have hm := hinv (u, j) (Set.mem_image_of_mem (D.torusAct (u, j)) hz)
  rw [D.torusAct_mk', D.family_act_eq_ptMul] at hm
  change (QuotientAddGroup.mk' L) (ptMul (D.mult u j) (ofCplx z)) ∈ Y at hm
  rw [ptMul_ofCplx] at hm
  change (QuotientAddGroup.mk' L) (ofCplx (cplxOf (D.mult u j) * z)) ∈ Y
  exact hm

/-- The corrected residual becomes ordinary nonzero accumulation in the complex lift. -/
theorem zero_mem_closure_planarLift {Y : Set (Torus L)}
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    (0 : ℂ) ∈ closure (planarLift L Y \ {0}) := by
  obtain ⟨x, hx, hxt⟩ := mem_closure_iff_seq_limit.mp hacc
  have hcplx : Continuous cplxOf := by
    have heq : cplxOf = fun x : Pt => ((x 1 : ℂ) + (x 2 : ℂ) * Complex.I) := by
      funext z
      apply Complex.ext <;> simp [cplxOf]
    rw [heq]
    fun_prop
  have hz0 : cplxOf 0 = 0 := rfl
  have hzt : Tendsto (fun n => cplxOf (x n)) atTop (𝓝 0) := by
    have h := (hcplx.tendsto (0 : Pt)).comp hxt
    simpa only [Function.comp_def, hz0] using h
  refine mem_closure_iff_seq_limit.mpr ⟨fun n => cplxOf (x n), ?_, hzt⟩
  intro n
  have hxi := hx n
  rcases hxi with ⟨⟨hxY, hx0⟩, hxplane⟩
  have hof : ofCplx (cplxOf (x n)) = x n := eq_ofCplx_cplxOf hxplane
  refine ⟨?_, ?_⟩
  · change (QuotientAddGroup.mk' L) (ofCplx (cplxOf (x n))) ∈ Y
    rw [hof]
    exact hxY
  · intro hz
    have hz' : cplxOf (x n) = 0 := by simpa using hz
    apply hx0
    rw [← hof, hz']
    simp [ofCplx]
    have hzpt : (![0, 0, 0] : Pt) = 0 := by
      funext i
      fin_cases i <;> simp
    rw [hzpt]
    exact L.zero_mem

end UnitPrime

section Canonical

variable {K : Type*} [Field K] [NumberField K]

/-- A positive-prime-exponent family member is rationally independent of the unit at the
complex place. -/
theorem multIndepPair_mult_unit_canonical (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (v : Units (numberFieldO K)) {j : ℕ} (hj : 0 < j) :
    let D := (canonicalFieldModel K h).toModel ε π hπO hπ0
    MultIndepPair (cplxOf (D.mult v j)) (cplxOf (D.unit_image ε)) := by
  dsimp only
  let D := (canonicalFieldModel K h).toModel ε π hπO hπ0
  let φ := complexEmbedding K h
  intro l k hmul
  change (cplxOf ((D.unit_image v) ⋆ powC (D.prime_image D.prime) j)) ^ l *
    (cplxOf (D.unit_image ε)) ^ k = 1 at hmul
  rw [cplxOf_mulC, cplxOf_powC] at hmul
  have hpow : φ ((((v : numberFieldO K) : K) * π ^ j) ^ l * (ε : K) ^ k) = φ 1 := by
    simp only [map_mul, map_zpow₀, map_pow, map_one]
    exact hmul
  have hfield : (((v : numberFieldO K) : K) * π ^ j) ^ l * (ε : K) ^ k = 1 :=
    φ.injective hpow
  have hN : numberFieldAbsNorm K
      ((((v : numberFieldO K) : K) * π ^ j) ^ l * (ε : K) ^ k) = 1 := by
    rw [hfield, map_one]
  simp only [map_mul, map_zpow₀, map_pow, map_one, (canonicalFieldModel K h).Nm_unit,
    one_zpow, one_mul, hπN] at hN
  have hN' : ((p : ℚ≥0)) ^ ((j : ℤ) * l) = 1 := by
    simpa [zpow_mul] using hN
  have hR : ((p : ℝ)) ^ ((j : ℤ) * l) = 1 := by
    have hcast := congrArg (fun x : ℚ≥0 => (x : ℝ)) hN'
    convert hcast using 1 <;> norm_num
  have hjl : (j : ℤ) * l = 0 := by
    by_contra hne
    exact absurd hR (zpow_ne_one_of_gt_one (a := (p : ℝ)) (by exact_mod_cast hp) hne)
  have hl : l = 0 := by
    have hj0 : (j : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
    exact (mul_eq_zero.mp hjl).resolve_left hj0
  refine ⟨hl, ?_⟩
  apply zpow_eq_one_imp_eq_zero hεpow
  simpa [hl] using hfield

/-- Multiplying the second member by a power of the first preserves independence. -/
theorem multIndepPair_mul_left_pow {c d : ℂ} (hc : c ≠ 0)
    (hB3 : MultIndepPair c d) (m : ℕ) : MultIndepPair c (c ^ m * d) := by
  intro l k heq
  have hpow : c ^ (l + (m : ℤ) * k) * d ^ k = 1 := by
    calc
      c ^ (l + (m : ℤ) * k) * d ^ k = c ^ l * (c ^ m * d) ^ k := by
        rw [mul_zpow, ← zpow_natCast, ← zpow_mul, zpow_add₀ hc]
        ring
      _ = 1 := heq
  obtain ⟨hl, hk⟩ := hB3 (l + (m : ℤ) * k) k hpow
  refine ⟨?_, hk⟩
  simpa [hk] using hl

/-- A power of an expanding multiplier can always bring a nonzero second multiplier outside
the unit disc as well. -/
theorem exists_nat_pow_mul_expanding {c d : ℂ} (hc : 1 < ‖c‖) (hd : d ≠ 0) :
    ∃ m : ℕ, 1 < ‖c‖ ^ m * ‖d‖ := by
  have hlogc : 0 < Real.log ‖c‖ := Real.log_pos hc
  obtain ⟨m, hm⟩ := exists_nat_gt (-Real.log ‖d‖ / Real.log ‖c‖)
  refine ⟨m, ?_⟩
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    norm_num at hc
  rw [← Real.log_pos_iff (mul_nonneg (pow_nonneg (norm_nonneg c) m) (norm_nonneg d))]
  rw [Real.log_mul (pow_ne_zero m (norm_ne_zero_iff.mpr hc0)) (norm_ne_zero_iff.mpr hd),
    Real.log_pow]
  have hm' : -Real.log ‖d‖ < (m : ℝ) * Real.log ‖c‖ :=
    (div_lt_iff₀ hlogc).mp hm
  linarith

/-- Canonical normalized arc in the full torus lift, with the expanding margin multiplier
explicitly named for the later tangent-net step. -/
theorem exists_normalizedArc_canonical (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    {Y : Set (Torus (canonicalFieldModel K h).lattice)}
    (hY : IsClosed Y)
    (hinv : ∀ i, ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y)
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
      (canonicalFieldModel K h).lattice) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    ∃ (a : Pt) (w₀ : ℂ) (l : ℤ × ℤ) (t' : ℝ),
      1 < ‖cplxOf a‖ ∧ w₀ ≠ 0 ∧ l ≠ 0 ∧ 0 ≤ l.1 ∧ 0 < t' ∧
      (∀ x : Pt, (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) x ∈ Y →
        (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) (ptMul a x) ∈ Y) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t',
        (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice)
          (ofCplx (normalizedArc (cplxOf a) (phaseOf (cplxOf a)) l w₀ t)) ∈ Y := by
  let D := (canonicalFieldModel K h).toModel ε π hπO hπ0
  obtain ⟨v, j, hj, _ha0, hC⟩ :=
    BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
      (canonicalFieldModel K h) ε π hπO hπ0 hεpow p (by exact_mod_cast hp) hπN
  have hc : 1 < ‖cplxOf (D.mult v j)‖ :=
    lt_of_lt_of_le (by norm_num) (BerendBlockLastMile.two_le_norm_cplxOf_of_normC hC)
  have hc0 : cplxOf (D.mult v j) ≠ 0 := by
    rw [← norm_ne_zero_iff]
    linarith
  have hB3base := multIndepPair_mult_unit_canonical h ε π hπO hπ0 hεpow p hp hπN v hj
  have hd0 : cplxOf (D.unit_image ε) ≠ 0 :=
    cplxOf_ne_zero_of_mulC_eq_one (D.unit_inv_mul ε)
  obtain ⟨m, hm⟩ := exists_nat_pow_mul_expanding hc hd0
  have hB3 : MultIndepPair (cplxOf (D.mult v j))
      (cplxOf (D.mult v j) ^ m * cplxOf (D.unit_image ε)) :=
    multIndepPair_mul_left_pow hc0 hB3base m
  have hd : cplxOf (D.mult v j) ^ m * cplxOf (D.unit_image ε) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_mul, norm_pow]
    exact ne_of_gt (lt_trans zero_lt_one hm)
  have hα0 : 0 ≤ Real.log ‖cplxOf (D.mult v j) ^ m * cplxOf (D.unit_image ε)‖ /
      Real.log ‖cplxOf (D.mult v j)‖ := by
    rw [norm_mul, norm_pow]
    exact div_nonneg (Real.log_nonneg hm.le) (Real.log_pos hc).le
  have hcinv : ∀ z ∈ planarLift (canonicalFieldModel K h).lattice Y,
      cplxOf (D.mult v j) * z ∈ planarLift (canonicalFieldModel K h).lattice Y := by
    intro z hz
    exact planarLift_mul_mem D hinv v j hz
  have hdinv : ∀ z ∈ planarLift (canonicalFieldModel K h).lattice Y,
      (cplxOf (D.mult v j) ^ m * cplxOf (D.unit_image ε)) * z ∈
        planarLift (canonicalFieldModel K h).lattice Y := by
    intro z hz
    have hpow : ∀ w ∈ planarLift (canonicalFieldModel K h).lattice Y,
        (cplxOf (D.mult v j) ^ m) * w ∈ planarLift (canonicalFieldModel K h).lattice Y := by
      intro w hw
      exact pow_mul_left_mem (fun w hw => hcinv w hw) m hw
    have hu := planarLift_mul_mem D hinv ε 0 (hpow z hz)
    simpa only [D.mult_zero, mul_assoc, mul_comm, mul_left_comm] using hu
  obtain ⟨w₀, hw₀, l, t', hl0ne, hl0, ht', harc⟩ :=
    exists_normalizedArc_complex_of_acc (isClosed_planarLift hY) hc hd hB3 rfl rfl rfl hα0
      hcinv hdinv (zero_mem_closure_planarLift hacc)
  have hpt : ∀ x : Pt, (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) x ∈ Y →
      (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) (ptMul (D.mult v j) x) ∈ Y := by
    intro x hx
    have hm := hinv (v, j) (Set.mem_image_of_mem (D.torusAct (v, j)) hx)
    rwa [D.torusAct_mk', D.family_act_eq_ptMul] at hm
  exact ⟨D.mult v j, w₀, l, t', hc, hw₀, hl0ne, hl0, ht', hpt, harc⟩

end Canonical

end BerendNormalizedCompactArc
end CubicTwoStage
