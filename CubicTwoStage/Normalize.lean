/-
**Lemma 6.1** (normalization) and **Lemma 8.4** (its form in arbitrary degree).
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

open Finset

/-- Every real number is within `1/2` of an integer. -/
theorem exists_int_abs_sub_le_half (x : ℝ) : ∃ z : ℤ, |x - z| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- The arithmetic content of Lemma 6.1, in logarithmic coordinates.

The condition `|Nm(y)| < 1` is `s + 2t < 0`; the unit acts by the translation
`(s,t) ↦ (s + σ, t - σ/2)` with `σ = log λ`, and every orbit meets the strip
`|s - t| ≤ (3/4) log λ`, whose part in the half-plane lies in
`{s < σ/2, t < σ/4}`. -/
theorem lem_normalize_core {s t σ : ℝ} (hσ : 0 < σ) (hst : s + 2 * t < 0) :
    ∃ k : ℤ, s + (k : ℝ) * σ < σ / 2 ∧ t - (k : ℝ) * (σ / 2) < σ / 4 := by
  have hc : 0 < 3 * σ / 2 := by linarith
  obtain ⟨m, hm⟩ := exists_int_abs_sub_le_half ((s - t) / (3 * σ / 2))
  have hkey : |(s - t) + ((-m : ℤ) : ℝ) * (3 * σ / 2)| ≤ (3 * σ / 2) / 2 := by
    have h1 : (s - t) / (3 * σ / 2) - (m : ℝ)
        = ((s - t) + ((-m : ℤ) : ℝ) * (3 * σ / 2)) / (3 * σ / 2) := by
      field_simp
      push_cast
      ring
    rw [h1, abs_div, abs_of_pos hc] at hm
    have := (div_le_iff₀ hc).mp hm
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hkey
  have e3 : 3 * (s + ((-m : ℤ) : ℝ) * σ)
      = (s + 2 * t) + 2 * ((s - t) + ((-m : ℤ) : ℝ) * (3 * σ / 2)) := by
    push_cast; ring
  have e4 : 3 * (t - ((-m : ℤ) : ℝ) * (σ / 2))
      = (s + 2 * t) - ((s - t) + ((-m : ℤ) : ℝ) * (3 * σ / 2)) := by
    push_cast; ring
  refine ⟨-m, ?_, ?_⟩
  · linarith [hst, hhi, e3]
  · linarith [hst, hhi, e4]

/-- **Lemma 6.1**.  Let `y = (u,w) ∈ ℝ × ℂ` have `|u|, |w| > 0` and
`|Nm(y)| = |u||w|² < 1`.  Then some power of the fundamental unit brings `y` into
the box `{|u'| < λ^{1/2}, |w'| < λ^{1/4}}`, where `λ = max(|σ₁ε|, |σ₁ε|⁻¹) > 1`.

The unit `ε` scales `u` by `λ^{±1}` and `w` by `λ^{∓1/2}`; as `k` ranges over
`ℤ` the two sign choices give the same set of multipliers, so the statement below
uses `|u| λ^k` and `|w| λ^{-k/2}` without loss of generality. -/
theorem lem_normalize {lam : ℝ} (hlam : 1 < lam) {u w : ℝ} (hu : u ≠ 0) (hw : w ≠ 0)
    (hnm : |u| * |w| ^ 2 < 1) :
    ∃ k : ℤ, |u| * lam ^ ((k : ℝ)) < lam ^ ((1 : ℝ) / 2) ∧
      |w| * lam ^ (-((k : ℝ)) / 2) < lam ^ ((1 : ℝ) / 4) := by
  have hlam0 : 0 < lam := by linarith
  have ha : 0 < |u| := abs_pos.mpr hu
  have hb : 0 < |w| := abs_pos.mpr hw
  have hσ : 0 < Real.log lam := Real.log_pos hlam
  have hst : Real.log |u| + 2 * Real.log |w| < 0 := by
    have hpos : 0 < |u| * |w| ^ 2 := by positivity
    have h1 : Real.log (|u| * |w| ^ 2) < 0 := by
      have h2 := Real.log_lt_log hpos hnm
      rwa [Real.log_one] at h2
    rw [Real.log_mul ha.ne' (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  obtain ⟨k, hk1, hk2⟩ := lem_normalize_core hσ hst
  refine ⟨k, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hlam0, Real.rpow_def_of_pos hlam0, ← Real.exp_log ha,
      ← Real.exp_add]
    refine Real.exp_lt_exp.mpr ?_
    have : Real.log lam * ((1 : ℝ) / 2) = Real.log lam / 2 := by ring
    rw [this]
    linarith
  · rw [Real.rpow_def_of_pos hlam0, Real.rpow_def_of_pos hlam0, ← Real.exp_log hb,
      ← Real.exp_add]
    refine Real.exp_lt_exp.mpr ?_
    have : Real.log lam * ((1 : ℝ) / 4) = Real.log lam / 4 := by ring
    rw [this]
    linarith

/-- **Lemma 8.4** (normalization in arbitrary degree), in logarithmic form.

Let `ρ` be the unit rank, `m = r₁ + r₂` the number of places, `Lε i j` the
`j`-th coordinate of `L(ε_i)`, and suppose the logarithmic coordinates of `y` are
`s j = ∑_i t_i Lε i j + N δ_j` with `N = log|Nm y| < 0` and `δ_j > 0`.  Then
translating by the integer vector nearest to `t` puts `y` in the box
`{|y_j| < e^{c_j}}` (`e^{c_j/2}` for a complex place), where
`c_j = (1/2) ∑_i |Lε i j|`. -/
theorem lem_gen_normalize_core {ρ m : ℕ} (Lε : Fin ρ → Fin m → ℝ) (t : Fin ρ → ℝ)
    (δ : Fin m → ℝ) (hδ : ∀ j, 0 < δ j) {N : ℝ} (hN : N < 0) :
    ∃ k' : Fin ρ → ℤ, ∀ j,
      (∑ i, (t i - (k' i : ℝ)) * Lε i j) + N * δ j
        < (1 / 2) * ∑ i, |Lε i j| := by
  choose k' hk' using fun i => exists_int_abs_sub_le_half (t i)
  refine ⟨k', fun j => ?_⟩
  have h1 : ∑ i, (t i - (k' i : ℝ)) * Lε i j ≤ ∑ i, |Lε i j| / 2 := by
    refine sum_le_sum (fun i _ => ?_)
    calc (t i - (k' i : ℝ)) * Lε i j ≤ |(t i - (k' i : ℝ)) * Lε i j| := le_abs_self _
      _ = |t i - (k' i : ℝ)| * |Lε i j| := abs_mul _ _
      _ ≤ (1 / 2) * |Lε i j| :=
          mul_le_mul_of_nonneg_right (hk' i) (abs_nonneg _)
      _ = |Lε i j| / 2 := by ring
  have h2 : N * δ j < 0 := mul_neg_of_neg_of_pos hN (hδ j)
  have hsum : ∑ i, |Lε i j| / 2 = (1 / 2) * ∑ i, |Lε i j| := by
    have h : ∑ i, |Lε i j| / 2 = ∑ i, (1 / 2) * |Lε i j| :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [h, Finset.mul_sum]
  linarith

end CubicTwoStage
