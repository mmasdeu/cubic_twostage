/-
# Stage I, axis branch: the real-scalar density `hscal` for the unit–prime model

Swarm `smw97otfd`, member `m1`, direction `d1`.

`BerendStageIBlockAxis.eq_univ_of_nonplanar_acc` reduces the non-planar branch of
Stage I to two arithmetic inputs about the actual model:

* `hscal : Dense (range fun i : 𝒪ˣ × ℕ => (D.mult i.1 i.2) 0)`;
* `haxis : Dense (coord {0} + L)`.

This file **proves `hscal`** for the field model `D = FM.toModel ε π`, i.e. for
the multiplier family `σ(u π^j)`, `u ∈ 𝒪ˣ`, `j : ℕ`, whose real part is

  `(D.mult u j) 0 = σ₁(u) · σ₁(π)^j`   (`σ₁ = sigmaReal FM`).

## The arithmetic

`σ₁` is a ring homomorphism out of a field, hence injective.  So a real modulus
relation `|σ₁(ε^a π^b)| = 1` is a *field* relation `σ₁(ε^a π^b) = ±1`, hence
`ε^a π^b = ±1`, not merely a real coincidence.  Taking absolute norms gives
`p^b = 1`, so `b = 0` (`Nm π = p > 1`), and then `ε^a = ±1` gives `a = 0` from
the infinite order of `ε`.  Hence

  `BerendModulus.MulIndep |σ₁ ε| |σ₁ π|`,

the corrected (B3) read on the archimedean moduli (`mulIndep_abs`).

## The density

Choose the unit `u₀ = ε` or `u₀ = ε⁻¹` so that `|σ₁ u₀| > 1`; `ε⁻¹` *is* a valid
unit index, so no inverse prime index is ever needed.  Then split on the size of
`μ = |σ₁ π|`:

* `μ < 1`:  `c = |σ₁ u₀| > 1` is expansive and `d = μ` contractive, both with
  *natural* exponents (`u₀ ^ m` and `π ^ k`);
* `μ > 1`:  `c = μ` expansive with natural exponent, `d = |σ₁ u₀|⁻¹` contractive
  with exponent `k : ℤ`, realised by the unit `(u₀⁻¹) ^ k`
  (`exists_abs_sigma_unit_zpow`).

In both cases the absolute values `{c ^ m d ^ k}` are dense in `(0, ∞)` at the
level of the available indices — this is the arithmetic content of Berend's
Lemma 4.4, `BerendRankTwo.exists_pow_mul_pow_near`, which is exactly the engine
of `BerendAxis.dense_range_signed_pow_mul`.  The *sign* is supplied by the unit
`-1 ∈ 𝒪ˣ` (`neg_mult_apply_zero`), so the two-sided range is dense
(`dense_range_of_dense_abs`).

No `sorry`, no new axiom, no use of `berend_multi_invariance`.
-/
import CubicTwoStage.BerendStageIBlockAxis
import CubicTwoStage.BerendUnitNoncritical
import CubicTwoStage.BerendCorrected
import CubicTwoStage.ComplexCubicCorrected

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendStageIScalar

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-! ## 1. The real coordinate of `σ`: powers, units, nonzero -/

/-- The zeroth coordinate of `σ` on a natural power. -/
theorem sigma_zero_pow (FM : FieldModel K 𝒪 Nm) (a : K) (m : ℕ) :
    (FM.σ (a ^ m)) 0 = ((FM.σ a) 0) ^ m :=
  map_pow (BerendCofinality.sigmaReal FM) a m

/-- The zeroth coordinate of `σ` on an integer power. -/
theorem sigma_zero_zpow (FM : FieldModel K 𝒪 Nm) (a : K) (l : ℤ) :
    (FM.σ (a ^ l)) 0 = ((FM.σ a) 0) ^ l :=
  map_zpow₀ (BerendCofinality.sigmaReal FM) a l

/-- A nonzero element of `K` has nonzero real coordinate. -/
theorem sigma_zero_ne_zero_of_ne_zero (FM : FieldModel K 𝒪 Nm) {b : K} (hb : b ≠ 0) :
    (FM.σ b) 0 ≠ 0 := by
  intro h
  have h1 : BerendCofinality.sigmaReal FM b = 0 := by simpa using h
  refine hb (BerendCofinality.sigmaReal_injective FM ?_)
  rw [h1, map_zero]

/-- The real coordinate of a unit of `𝒪` is nonzero. -/
theorem sigma_zero_unit_ne_zero (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) :
    (FM.σ (((u : 𝒪) : K))) 0 ≠ 0 := by
  intro h
  have h1 : BerendCofinality.sigmaReal FM (((u : 𝒪) : K)) = 0 := by simpa using h
  have h2 : (((u : 𝒪) : K)) = 0 := by
    refine BerendCofinality.sigmaReal_injective FM ?_
    rw [h1, map_zero]
  have h3 : Nm (((u : 𝒪) : K)) = 0 := by rw [h2, map_zero]
  rw [FM.Nm_unit u] at h3
  exact one_ne_zero h3

/-- The real modulus of a natural power of a unit. -/
theorem abs_sigma_unit_pow (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) (m : ℕ) :
    |(FM.σ ((((u ^ m : 𝒪ˣ) : 𝒪) : K))) 0| = |(FM.σ (((u : 𝒪) : K))) 0| ^ m := by
  have hcoe : ((((u ^ m : 𝒪ˣ) : 𝒪) : K)) = (((u : 𝒪) : K)) ^ m := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (𝒪.subtype) ((u : 𝒪)) m
  rw [hcoe, sigma_zero_pow, abs_pow]

/-- The real modulus of the inverse of a unit. -/
theorem abs_sigma_unit_inv (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) :
    |(FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K))) 0| = (|(FM.σ (((u : 𝒪) : K))) 0|)⁻¹ := by
  rw [FieldModel.coe_units_inv]
  have h2 : (FM.σ ((((u : 𝒪) : K))⁻¹)) 0 = ((FM.σ (((u : 𝒪) : K))) 0)⁻¹ :=
    map_inv₀ (BerendCofinality.sigmaReal FM) (((u : 𝒪) : K))
  rw [h2, abs_inv]

/-- For every integer exponent there is a *unit* whose real modulus is the
corresponding integer power: positive exponents use `u ^ m`, negative ones the
inverse unit `(u⁻¹) ^ m`, so no `ℤ`-power inside `𝒪` is needed. -/
theorem exists_abs_sigma_unit_zpow (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) (k : ℤ) :
    ∃ v : 𝒪ˣ, |(FM.σ (((v : 𝒪) : K))) 0| = |(FM.σ (((u : 𝒪) : K))) 0| ^ k := by
  by_cases hk : 0 ≤ k
  · refine ⟨u ^ k.toNat, ?_⟩
    rw [abs_sigma_unit_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]
  · have hk' : k < 0 := not_le.mp hk
    refine ⟨(u⁻¹) ^ (-k).toNat, ?_⟩
    rw [abs_sigma_unit_pow, abs_sigma_unit_inv]
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow, zpow_neg, inv_inv]

/-! ## 2. The multiplier's real coordinate -/

/-- The real coordinate of the unit–prime multiplier. -/
theorem mult_apply_zero (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (u : 𝒪ˣ) (j : ℕ) :
    ((FM.toModel ε π hπO hπ0).mult u j) 0 =
      (FM.σ (((u : 𝒪) : K))) 0 * ((FM.σ π) 0) ^ j := by
  rw [FM.toModel_mult]
  simp only [FieldModel.mult, mulC_apply_zero, BerendStageIBlock.powC_apply_zero]

/-- The real modulus of the unit–prime multiplier. -/
theorem abs_mult_apply_zero (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (u : 𝒪ˣ) (j : ℕ) :
    |((FM.toModel ε π hπO hπ0).mult u j) 0| =
      |(FM.σ (((u : 𝒪) : K))) 0| * |(FM.σ π) 0| ^ j := by
  rw [mult_apply_zero, abs_mul, abs_pow]

/-- The unit `-1` negates the real multiplier, so the range of the multipliers is
symmetric about zero. -/
theorem neg_mult_apply_zero (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (i : 𝒪ˣ × ℕ) :
    ∃ i' : 𝒪ˣ × ℕ,
      ((FM.toModel ε π hπO hπ0).mult i'.1 i'.2) 0 =
        -((FM.toModel ε π hπO hπ0).mult i.1 i.2) 0 := by
  refine ⟨(-i.1, i.2), ?_⟩
  have hcoe : ((((-i.1 : 𝒪ˣ) : 𝒪) : K)) = -(((i.1 : 𝒪) : K)) := by
    rw [Units.val_neg]
    push_cast
    ring
  rw [mult_apply_zero, mult_apply_zero, hcoe, FM.σ_neg]
  simp

/-! ## 3. The arithmetic core: multiplicative independence of the moduli

`|σ₁ ε|` and `|σ₁ π|` are multiplicatively independent.  The proof is the
injectivity of `σ₁`: a real modulus relation `|σ₁(ε^a π^b)| = 1` is a *field*
relation `ε^a π^b = ±1`, whose absolute norm is `p^b`. -/

theorem mulIndep_abs (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπ0 : π ≠ 0) (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0)) :
    BerendModulus.MulIndep |(FM.σ (((ε : 𝒪) : K))) 0| |(FM.σ π) 0| := by
  classical
  have hinj := BerendCofinality.sigmaReal_injective FM
  have hε0 : (((ε : 𝒪) : K)) ≠ 0 := by
    intro h
    have h1 : Nm (((ε : 𝒪) : K)) = 0 := by rw [h, map_zero]
    rw [FM.Nm_unit ε] at h1
    exact one_ne_zero h1
  have hπmu : (FM.σ π) 0 ≠ 0 := sigma_zero_ne_zero_of_ne_zero FM hπ0
  intro m n hmn
  -- `a = ε^m π^{-n}` has real modulus one
  set a : K := (((ε : 𝒪) : K)) ^ m * π ^ (-n) with hadef
  have habs : |(FM.σ a) 0| = 1 := by
    have h1 : (FM.σ a) 0 = ((FM.σ (((ε : 𝒪) : K))) 0) ^ m * ((FM.σ π) 0) ^ (-n) := by
      rw [hadef]
      show BerendCofinality.sigmaReal FM _ = _
      rw [map_mul, map_zpow₀, map_zpow₀]
      rfl
    rw [h1, abs_mul, abs_zpow, abs_zpow, hmn, ← zpow_add₀ (abs_ne_zero.mpr hπmu),
      add_neg_cancel, zpow_zero]
  -- hence `a = ±1`
  have ha : a = 1 ∨ a = -1 := by
    rcases (abs_eq zero_le_one).mp habs with h | h
    · left
      refine hinj ?_
      show (FM.σ a) 0 = (FM.σ (1 : K)) 0
      rw [h, FM.σ_one]
      rfl
    · right
      refine hinj ?_
      show (FM.σ a) 0 = (FM.σ (-1 : K)) 0
      rw [h, FM.σ_neg, FM.σ_one]
      simp
  have hsqa : a * a = 1 := by rcases ha with h | h <;> simp [h]
  -- the norm of `a` is `p^{-n}`
  have hNm : Nm a = ((p : ℚ≥0)) ^ (-n) := by
    rw [hadef, map_mul, map_zpow₀, map_zpow₀, FM.Nm_unit, one_zpow, one_mul, hπN]
  have hsq : ((p : ℚ≥0)) ^ (-n) * ((p : ℚ≥0)) ^ (-n) = 1 := by
    rw [← hNm, ← map_mul, hsqa, map_one]
  have hsqR : ((p : ℝ)) ^ (-n) * ((p : ℝ)) ^ (-n) = 1 := by
    have h := congrArg (fun x : ℚ≥0 => (x : ℝ)) hsq
    simpa using h
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hn : n = 0 := by
    by_contra hn
    have hx1 : ((p : ℝ)) ^ (-n) = 1 := by
      rcases mul_self_eq_one_iff.mp hsqR with h | h
      · exact h
      · have hpos : 0 < ((p : ℝ)) ^ (-n) := zpow_pos hppos _
        linarith
    exact CubicTwoStage.zpow_ne_one_of_gt_one (a := (p : ℝ))
      (by exact_mod_cast hp) (by omega : -n ≠ 0) hx1
  -- with `n = 0`, `a = ε^m` has square one, so `m = 0` by infinite order
  have hm : m = 0 := by
    have ham : a = (((ε : 𝒪) : K)) ^ m := by
      rw [hadef, hn]
      simp
    have h2 : (((ε : 𝒪) : K)) ^ m * (((ε : 𝒪) : K)) ^ m = 1 := by
      rw [← ham]; exact hsqa
    have h3 : (((ε : 𝒪) : K)) ^ (m + m) = 1 := by
      rw [zpow_add₀ hε0]
      exact h2
    have h4 : m + m = 0 :=
      CubicTwoStage.zpow_eq_one_imp_eq_zero (a := (((ε : 𝒪) : K))) hεpow h3
    omega
  exact ⟨hm, hn⟩

/-! ## 4. Density transfer: a symmetric range with dense absolute values -/

/-- A function whose range is symmetric and whose absolute-value range is dense
in `[0, ∞)` has dense range. -/
theorem dense_range_of_dense_abs {κ : Type*} {f : κ → ℝ}
    (h : ∀ x : ℝ, 0 ≤ x → ∀ r : ℝ, 0 < r → ∃ i, |x - (|f i|)| < r)
    (hneg : ∀ i, ∃ i', f i' = -f i) : Dense (Set.range f) := by
  have hpos : ∀ i, |f i| ∈ Set.range f := by
    intro i
    rcases le_total 0 (f i) with h1 | h1
    · exact ⟨i, by rw [abs_of_nonneg h1]⟩
    · obtain ⟨i', hi'⟩ := hneg i
      exact ⟨i', by rw [hi', abs_of_nonpos h1]⟩
  have hnegv : ∀ i, -|f i| ∈ Set.range f := by
    intro i
    rcases le_total 0 (f i) with h1 | h1
    · obtain ⟨i', hi'⟩ := hneg i
      exact ⟨i', by rw [hi', abs_of_nonneg h1]⟩
    · exact ⟨i, by rw [abs_of_nonpos h1, neg_neg]⟩
  rw [Metric.dense_iff]
  intro x r hr
  rcases lt_or_ge x 0 with hx | hx
  · obtain ⟨i, hi⟩ := h (-x) (by linarith) r hr
    refine ⟨_, ?_, hnegv i⟩
    rw [Metric.mem_ball, Real.dist_eq, show -|f i| - x = -x - |f i| by ring]
    exact hi
  · obtain ⟨i, hi⟩ := h x hx r hr
    exact ⟨_, by rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact hi, hpos i⟩

/-! ## 5. `hscal`: density of the real multipliers -/

/-- **The real multipliers of the unit–prime family are dense in `ℝ`.** -/
theorem dense_range_mult_zero (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0)) :
    Dense (Set.range fun i : 𝒪ˣ × ℕ =>
      ((FM.toModel ε π hπO hπ0).mult i.1 i.2) 0) := by
  classical
  set lam : ℝ := |(FM.σ (((ε : 𝒪) : K))) 0|
  set mu : ℝ := |(FM.σ π) 0|
  have hpi_ne : (FM.σ π) 0 ≠ 0 := sigma_zero_ne_zero_of_ne_zero FM hπ0
  have hu_ne : (FM.σ (((ε : 𝒪) : K))) 0 ≠ 0 := sigma_zero_unit_ne_zero FM ε
  have hmu_pos : 0 < mu := by
    rw [show mu = |(FM.σ π) 0| from rfl]; exact abs_pos.mpr hpi_ne
  have hlam_pos : 0 < lam := by
    rw [show lam = |(FM.σ (((ε : 𝒪) : K))) 0| from rfl]; exact abs_pos.mpr hu_ne
  have hlam_eq : lam = |(FM.σ (((ε : 𝒪) : K))) 0| := rfl
  have hmu_eq : mu = |(FM.σ π) 0| := rfl
  -- `lam ≠ 1` from infinite order of `ε`
  have hεne1 : (((ε : 𝒪) : K)) ≠ 1 := fun h => hεpow 1 one_pos (by simpa using h)
  have hlam_ne1 : lam ≠ 1 := by
    intro h
    have hinj := BerendCofinality.sigmaReal_injective FM
    rw [hlam_eq] at h
    rcases (abs_eq zero_le_one).mp h with h1 | h1
    · refine hεne1 (hinj ?_)
      show (FM.σ (((ε : 𝒪) : K))) 0 = (FM.σ (1 : K)) 0
      rw [h1, FM.σ_one]
      rfl
    · have h2 : (((ε : 𝒪) : K)) = -1 := by
        refine hinj ?_
        show (FM.σ (((ε : 𝒪) : K))) 0 = (FM.σ (-1 : K)) 0
        rw [h1, FM.σ_neg, FM.σ_one]
        simp
      have h3 : (((ε : 𝒪) : K)) ^ 2 = 1 := by rw [h2]; norm_num
      exact hεpow 2 (by norm_num) h3
  -- `mu ≠ 1` from `Nm π = p > 1`
  have hmu_ne1 : mu ≠ 1 := by
    intro h
    have hinj := BerendCofinality.sigmaReal_injective FM
    rw [hmu_eq] at h
    have h1 : Nm π = 1 := by
      rcases (abs_eq zero_le_one).mp h with h2 | h2
      · have hπ1 : π = 1 := by
          refine hinj ?_
          show (FM.σ π) 0 = (FM.σ (1 : K)) 0
          rw [h2, FM.σ_one]
          rfl
        rw [hπ1, map_one]
      · have hπ1 : π = -1 := by
          refine hinj ?_
          show (FM.σ π) 0 = (FM.σ (-1 : K)) 0
          rw [h2, FM.σ_neg, FM.σ_one]
          simp
        rw [hπ1, AbsNorm.abs_neg, map_one]
    rw [hπN] at h1
    have h2 : p = 1 := by
      have h3 : (p : ℚ≥0) = ((1 : ℕ) : ℚ≥0) := by simpa using h1
      exact Nat.cast_injective h3
    omega
  have hbase : BerendModulus.MulIndep lam mu := mulIndep_abs FM ε π hπ0 hεpow p hp hπN
  -- the unit `ε` or its inverse, whichever expands
  set u₀ : 𝒪ˣ := if 1 < lam then ε else ε⁻¹
  have hlam₀_eq : |(FM.σ (((u₀ : 𝒪) : K))) 0| = if 1 < lam then lam else lam⁻¹ := by
    by_cases h : 1 < lam
    · have hu₀ : u₀ = ε := by simp only [show u₀ = if 1 < lam then ε else ε⁻¹ from rfl, h,
        if_true]
      rw [hu₀, hlam_eq, if_pos h]
    · have hu₀ : u₀ = ε⁻¹ := by simp only [show u₀ = if 1 < lam then ε else ε⁻¹ from rfl, h,
        if_false]
      rw [hu₀, abs_sigma_unit_inv, hlam_eq, if_neg h]
  have hlam₀1 : 1 < |(FM.σ (((u₀ : 𝒪) : K))) 0| := by
    rw [hlam₀_eq]
    by_cases h : 1 < lam
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      have hlt : lam < 1 := lt_of_le_of_ne (le_of_not_gt h) hlam_ne1
      exact (one_lt_inv₀ hlam_pos).mpr hlt
  have hind₀ : BerendModulus.MulIndep |(FM.σ (((u₀ : 𝒪) : K))) 0| mu := by
    rw [hlam₀_eq]
    by_cases h : 1 < lam
    · rw [if_pos h]; exact hbase
    · rw [if_neg h]
      intro m n hmn
      have h2 : lam ^ (-m) = mu ^ n := by
        rw [← hmn, inv_zpow, zpow_neg]
      obtain ⟨h1, h2'⟩ := hbase (-m) n h2
      exact ⟨by omega, h2'⟩
  -- density of the absolute values, split on the size of the prime modulus
  have habs : ∀ x : ℝ, 0 ≤ x → ∀ r : ℝ, 0 < r →
      ∃ i : 𝒪ˣ × ℕ, |x - (|((FM.toModel ε π hπO hπ0).mult i.1 i.2) 0|)| < r := by
    intro x hx r hr
    rcases lt_or_gt_of_ne hmu_ne1 with hmu1 | hmu1
    · -- `mu < 1`: the expansive factor is the unit `u₀`, the contractive one `mu`
      have hirr : Irrational (Real.log |(FM.σ (((u₀ : 𝒪) : K))) 0| / Real.log mu) :=
        BerendRankTwo.irrational_log_div_log_of_indep (lt_trans zero_lt_one hlam₀1)
          hmu_pos hind₀
      rcases lt_or_eq_of_le hx with hxpos | hx0
      · obtain ⟨m, k, hmk⟩ :=
          BerendRankTwo.exists_pow_mul_pow_near hlam₀1 hmu_pos hmu1 hirr hxpos hr
        refine ⟨(u₀ ^ m, k), ?_⟩
        rw [abs_mult_apply_zero, abs_sigma_unit_pow, ← hmu_eq]
        exact hmk
      · subst hx0
        obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr hmu1
        refine ⟨(u₀ ^ 0, k), ?_⟩
        rw [abs_mult_apply_zero, abs_sigma_unit_pow, pow_zero, one_mul, ← hmu_eq]
        simpa [abs_of_pos (pow_pos hmu_pos k)] using hk
    · -- `1 < mu`: the expansive factor is the prime, the contractive one `u₀⁻¹`
      set dd : ℝ := (|(FM.σ (((u₀ : 𝒪) : K))) 0|)⁻¹
      have hdd_eq : dd = (|(FM.σ (((u₀ : 𝒪) : K))) 0|)⁻¹ := rfl
      have hd0 : 0 < dd := by
        rw [hdd_eq]; exact inv_pos.mpr (lt_trans zero_lt_one hlam₀1)
      have hd1 : dd < 1 := by
        rw [hdd_eq]; exact inv_lt_one_of_one_lt₀ hlam₀1
      have hindcd : BerendModulus.MulIndep mu dd := by
        rw [hdd_eq]
        intro m n hmn
        have h2 : mu ^ m = (|(FM.σ (((u₀ : 𝒪) : K))) 0|) ^ (-n) := by
          rw [hmn, inv_zpow, zpow_neg]
        obtain ⟨h1, h2'⟩ := hind₀ (-n) m h2.symm
        exact ⟨h2', by omega⟩
      have hirr : Irrational (Real.log mu / Real.log dd) :=
        BerendRankTwo.irrational_log_div_log_of_indep hmu_pos hd0 hindcd
      rcases lt_or_eq_of_le hx with hxpos | hx0
      · obtain ⟨m, k, hmk⟩ :=
          BerendRankTwo.exists_pow_mul_pow_near hmu1 hd0 hd1 hirr hxpos hr
        obtain ⟨v, hv⟩ := exists_abs_sigma_unit_zpow FM u₀ (-(k : ℤ))
        refine ⟨(v, m), ?_⟩
        rw [abs_mult_apply_zero, hv]
        have hk1 : dd ^ k = (|(FM.σ (((u₀ : 𝒪) : K))) 0|) ^ (-(k : ℤ)) := by
          rw [hdd_eq, ← zpow_natCast, inv_zpow, zpow_neg]
        rw [← hk1, ← hmu_eq]
        simpa [mul_comm] using hmk
      · subst hx0
        obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr hd1
        obtain ⟨v, hv⟩ := exists_abs_sigma_unit_zpow FM u₀ (-(k : ℤ))
        refine ⟨(v, 0), ?_⟩
        rw [abs_mult_apply_zero, hv]
        have hk1 : dd ^ k = (|(FM.σ (((u₀ : 𝒪) : K))) 0|) ^ (-(k : ℤ)) := by
          rw [hdd_eq, ← zpow_natCast, inv_zpow, zpow_neg]
        rw [← hk1]
        simpa [abs_of_pos (pow_pos hd0 k)] using hk
  exact dense_range_of_dense_abs habs (fun i => neg_mult_apply_zero FM ε π hπO hπ0 i)


/-! ## 6. Stage I non-planar branch with `hscal` discharged -/

/-- **Stage I, non-planar accumulation, with `hscal` proved.**  This is
`BerendStageIBlock.eq_univ_of_nonplanar_acc` with the real-scalar density
hypothesis replaced by the paper's arithmetic (`hεpow`, `Nm π = p > 1`). -/
theorem eq_univ_of_nonplanar_acc' (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (hε1 : 1 < |(FM.σ (((ε : 𝒪) : K))) 0|)
    {Y : Set (Torus FM.lattice)} (hY : IsClosed Y)
    (hinv : ∀ i, (FM.toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y)
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' FM.lattice) ⁻¹' Y ∩ {x | x 0 ≠ 0})) :
    Y = univ :=
  BerendStageIBlock.eq_univ_of_nonplanar_acc (FM.toModel ε π hπO hπ0) ε hε1
    (FM.abs_normR_unit ε) hY hinv
    (dense_range_mult_zero FM ε π hπO hπ0 hεpow p hp hπN) haxis hacc

/-- **Stage I reduces to the planar case only**, with `hscal` discharged: the
remaining inputs are the complex-projection density `haxis` and the planar
accumulation statement `hplanar`. -/
theorem zeroNonisolatedFull_fieldModel_of_planar' (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (hε1 : 1 < |(FM.σ (((ε : 𝒪) : K))) 0|)
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hplanar : ∀ Y : Set (Torus FM.lattice), IsClosed Y →
      (∀ i, (FM.toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk' FM.lattice) ⁻¹' (Y \ {0}) ∩ {x | x 0 = 0}) →
      Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull (FM.toModel ε π hπO hπ0).torusAct :=
  BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar FM ε π hπO hπ0 hε1
    (dense_range_mult_zero FM ε π hπO hπ0 hεpow p hp hπN) haxis hplanar

/-- **The expansive direction is not an assumption.**  The hypothesis
`|σ₁ ε| ≠ 1` (which `BerendUnitNoncritical.lamAbs_real_ne_one` supplies from
`hεpow`) suffices: the proof runs on `ε` or on the unit `ε⁻¹`, and the family
`μ_{u π^j}` — hence `torusAct` — is unchanged because the unit image of
`toModel` does not depend on the chosen unit. -/
theorem zeroNonisolatedFull_fieldModel_of_planar_choice (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ)
    (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (hεne1 : |(FM.σ (((ε : 𝒪) : K))) 0| ≠ 1)
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hplanar : ∀ Y : Set (Torus FM.lattice), IsClosed Y →
      (∀ i, (FM.toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk' FM.lattice) ⁻¹' (Y \ {0}) ∩ {x | x 0 = 0}) →
      Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull (FM.toModel ε π hπO hπ0).torusAct := by
  have hpos : 0 < |(FM.σ (((ε : 𝒪) : K))) 0| := abs_pos.mpr (sigma_zero_unit_ne_zero FM ε)
  set ε' : 𝒪ˣ := if 1 < |(FM.σ (((ε : 𝒪) : K))) 0| then ε else ε⁻¹
  have hε'1 : 1 < |(FM.σ (((ε' : 𝒪) : K))) 0| := by
    by_cases h : 1 < |(FM.σ (((ε : 𝒪) : K))) 0|
    · have h' : ε' = ε := by
        simp only [show ε' = if 1 < |(FM.σ (((ε : 𝒪) : K))) 0| then ε else ε⁻¹ from rfl, h,
          if_true]
      rw [h']; exact h
    · have hlt : |(FM.σ (((ε : 𝒪) : K))) 0| < 1 := lt_of_le_of_ne (le_of_not_gt h) hεne1
      have h' : ε' = ε⁻¹ := by
        simp only [show ε' = if 1 < |(FM.σ (((ε : 𝒪) : K))) 0| then ε else ε⁻¹ from rfl, h,
          if_false]
      rw [h', abs_sigma_unit_inv]
      exact (one_lt_inv₀ hpos).mpr hlt
  have hεpow' : ∀ n : ℕ, 0 < n → (ε' : K) ^ n ≠ 1 := by
    intro n hn
    by_cases h : 1 < |(FM.σ (((ε : 𝒪) : K))) 0|
    · have h' : ε' = ε := by
        simp only [show ε' = if 1 < |(FM.σ (((ε : 𝒪) : K))) 0| then ε else ε⁻¹ from rfl, h,
          if_true]
      rw [h']
      exact hεpow n hn
    · have h' : ε' = ε⁻¹ := by
        simp only [show ε' = if 1 < |(FM.σ (((ε : 𝒪) : K))) 0| then ε else ε⁻¹ from rfl, h,
          if_false]
      rw [h', FieldModel.coe_units_inv, inv_pow]
      exact fun hcon => hεpow n hn (inv_eq_one.mp hcon)
  exact BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar FM ε' π hπO hπ0 hε'1
    (dense_range_mult_zero FM ε' π hπO hπ0 hεpow' p hp hπN) haxis hplanar

end BerendStageIScalar

namespace BerendStageIScalarCanonical

/-! ## 7. The canonical complex cubic model -/

open CubicTwoStage.BerendStageIScalar (dense_range_mult_zero
  zeroNonisolatedFull_fieldModel_of_planar_choice)

/-- **`hscal` for the canonical complex cubic field.** -/
theorem dense_range_mult_zero_canonical (K : Type*) [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    Dense (Set.range fun i : Units (numberFieldO K) × ℕ =>
      (((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2) 0) :=
  dense_range_mult_zero (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0
    hεpow p hp hπN

/-- **Stage I for the canonical complex cubic reduces to the planar case**:
the real-scalar density is discharged, so the remaining named obligations are
`haxis` (the complex projection of `𝒪_K` is dense in `ℂ`) and `hplanar` (the
planar accumulation statement). -/
theorem zeroNonisolatedFull_canonical_of_planar (K : Type*) [Field K] [NumberField K]
    (h : IsComplexCubic K) (ε : Units (numberFieldO K)) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεne1 : |(NumberFieldCubic.canonicalFieldModel K h).σ
      (((ε : numberFieldO K) : K)) 0| ≠ 1)
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) +
      ((NumberFieldCubic.canonicalFieldModel K h).lattice : Set Pt)))
    (hplanar : ∀ Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K h).lattice),
      IsClosed Y →
      (∀ i, ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i '' Y
        ⊆ Y) →
      (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
        (NumberFieldCubic.canonicalFieldModel K h).lattice) ⁻¹' (Y \ {0}) ∩ {x | x 0 = 0}) →
      Y = univ) :
    BerendDichotomy.ZeroNonisolatedFull
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  zeroNonisolatedFull_fieldModel_of_planar_choice (NumberFieldCubic.canonicalFieldModel K h)
    ε π hπO hπ0 hεpow p hp hπN hεne1 haxis hplanar

end BerendStageIScalarCanonical
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendStageIScalar.sigma_zero_pow
#print axioms CubicTwoStage.BerendStageIScalar.abs_sigma_unit_pow
#print axioms CubicTwoStage.BerendStageIScalar.abs_sigma_unit_inv
#print axioms CubicTwoStage.BerendStageIScalar.exists_abs_sigma_unit_zpow
#print axioms CubicTwoStage.BerendStageIScalar.mult_apply_zero
#print axioms CubicTwoStage.BerendStageIScalar.abs_mult_apply_zero
#print axioms CubicTwoStage.BerendStageIScalar.neg_mult_apply_zero
#print axioms CubicTwoStage.BerendStageIScalar.mulIndep_abs
#print axioms CubicTwoStage.BerendStageIScalar.dense_range_of_dense_abs
#print axioms CubicTwoStage.BerendStageIScalar.dense_range_mult_zero
#print axioms CubicTwoStage.BerendStageIScalar.eq_univ_of_nonplanar_acc'
#print axioms CubicTwoStage.BerendStageIScalar.zeroNonisolatedFull_fieldModel_of_planar'
#print axioms CubicTwoStage.BerendStageIScalar.zeroNonisolatedFull_fieldModel_of_planar_choice
#print axioms CubicTwoStage.BerendStageIScalarCanonical.dense_range_mult_zero_canonical
#print axioms CubicTwoStage.BerendStageIScalarCanonical.zeroNonisolatedFull_canonical_of_planar
