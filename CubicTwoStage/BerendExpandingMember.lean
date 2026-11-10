/-
# The expanding member of the unit–prime family: the producer side

Swarm `smw92j8g1`, member m3, direction d8.

The accepted module `BerendInteriorFull` proves the *interior step* of Furstenberg's
Proposition IV.1 from an expansion estimate: if `A` preserves the lattice, has a
right inverse `A'` with `‖A' x‖ ≤ λ⁻¹‖x‖` (`λ > 1`), and a closed invariant set
has non-empty interior, then it is everything.  It leaves open the *producer*
question: does the unit–prime family of the project contain such an `A`?

This file answers it, with no ergodicity and no measure theory.  In the model
algebra `Pt = ℝ × ℂ`, multiplication by `a` acts as `x 0 ↦ a 0 * x 0` on the real
coordinate and as `z ↦ (a 1 + i a 2) z` on the complex one, so its inverse contracts
the sup norm as soon as the two moduli `|a 0|` and `|a 1 + i a 2|` are both large:

* `abs_apply_le_norm`, `norm_ptMul_le` — the operator bound
  `‖b ⋆ x‖ ≤ max |b 0| (|b 1| + |b 2|) * ‖x‖`;
* `lamAbs_zero_eq_abs`, `lamAbs_one_sq` — `lamAbs a 0 = |a 0|` and
  `(lamAbs a 1)^2 = normC a`, the dictionary between the eigen-moduli of
  `BerendEigenBridge` and the sup-norm coordinates;
* `invC_coord_bound`, `norm_ptMul_invC_le_half` — if `4 ≤ |a 0|` and
  `16 ≤ normC a` then `‖invC a ⋆ x‖ ≤ 2⁻¹ ‖x‖`: the inverse is a strict
  contraction with the constant `λ = 2` used by `BerendInteriorFull`.

The arithmetic existence of a family member with those two lower bounds is proved
separately below (`exists_mult_margin`), because it is where the trace-norm
relations `|Nm ε| = 1` and `|Nm π| = p` are used.
-/
import CubicTwoStage.BerendEigenBridge
import CubicTwoStage.BerendDichotomy
import CubicTwoStage.BerendInteriorFull

open Set

set_option maxHeartbeats 1000000

namespace CubicTwoStage

/-! ## 1. The sup-norm operator bound for multiplication -/

/-- Coordinates are bounded by the sup norm. -/
theorem abs_apply_le_norm (x : Pt) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  simpa using norm_le_pi_norm x i

/-- **Multiplication in `ℝ × ℂ` is bounded by `max (|a 0|) (|a 1| + |a 2|)` in the
sup norm.**  The real coordinate is scaled by `|a 0|`; the complex one by
`a 1 + i a 2`, whose matrix `!![a 1, -a 2; a 2, a 1]` has sup-norm operator norm at
most `|a 1| + |a 2|`. -/
theorem norm_ptMul_le (b x : Pt) :
    ‖ptMul b x‖ ≤ max (|b 0|) (|b 1| + |b 2|) * ‖x‖ := by
  set M := max (|b 0|) (|b 1| + |b 2|) with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (b 0)) (le_max_left _ _)
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  have hx0 : |x 0| ≤ ‖x‖ := abs_apply_le_norm x 0
  have hx1 : |x 1| ≤ ‖x‖ := abs_apply_le_norm x 1
  have hx2 : |x 2| ≤ ‖x‖ := abs_apply_le_norm x 2
  have hMl : |b 0| ≤ M := le_max_left (|b 0|) (|b 1| + |b 2|)
  have hMr : |b 1| + |b 2| ≤ M := le_max_right (|b 0|) (|b 1| + |b 2|)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM0 hxn)).mpr ?_
  intro i
  fin_cases i
  · show ‖ptMul b x 0‖ ≤ M * ‖x‖
    rw [ptMul_apply, mulC_apply_zero, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hMl hx0 (abs_nonneg _) hM0
  · show ‖ptMul b x 1‖ ≤ M * ‖x‖
    rw [ptMul_apply, mulC_apply_one, Real.norm_eq_abs]
    have h1 : |b 1 * x 1 - b 2 * x 2| ≤ |b 1 * x 1| + |b 2 * x 2| :=
      abs_sub _ _
    have h2 : |b 1 * x 1| + |b 2 * x 2| = |b 1| * |x 1| + |b 2| * |x 2| := by
      rw [abs_mul, abs_mul]
    have h3 : |b 1| * |x 1| + |b 2| * |x 2| ≤ |b 1| * ‖x‖ + |b 2| * ‖x‖ := by
      have e1 := mul_le_mul_of_nonneg_left hx1 (abs_nonneg (b 1))
      have e2 := mul_le_mul_of_nonneg_left hx2 (abs_nonneg (b 2))
      linarith
    have h4 : |b 1| * ‖x‖ + |b 2| * ‖x‖ = (|b 1| + |b 2|) * ‖x‖ := by ring
    have h5 : |b 1| * |x 1| + |b 2| * |x 2| ≤ M * ‖x‖ := by
      rw [h4] at h3
      exact le_trans h3 (mul_le_mul_of_nonneg_right hMr hxn)
    linarith
  · show ‖ptMul b x 2‖ ≤ M * ‖x‖
    rw [ptMul_apply, mulC_apply_two, Real.norm_eq_abs]
    have h1 : |b 1 * x 2 + b 2 * x 1| ≤ |b 1 * x 2| + |b 2 * x 1| := abs_add_le _ _
    have h2 : |b 1 * x 2| + |b 2 * x 1| = |b 1| * |x 2| + |b 2| * |x 1| := by
      rw [abs_mul, abs_mul]
    have h3 : |b 1| * |x 2| + |b 2| * |x 1| ≤ |b 1| * ‖x‖ + |b 2| * ‖x‖ := by
      have e1 := mul_le_mul_of_nonneg_left hx2 (abs_nonneg (b 1))
      have e2 := mul_le_mul_of_nonneg_left hx1 (abs_nonneg (b 2))
      linarith
    have h4 : |b 1| * ‖x‖ + |b 2| * ‖x‖ = (|b 1| + |b 2|) * ‖x‖ := by ring
    have h5 : |b 1| * |x 2| + |b 2| * |x 1| ≤ M * ‖x‖ := by
      rw [h4] at h3
      exact le_trans h3 (mul_le_mul_of_nonneg_right hMr hxn)
    linarith

/-! ## 2. The eigen-moduli in sup-norm coordinates -/

/-- The real eigen-modulus is `|a 0|`. -/
theorem lamAbs_zero_eq_abs (a : Pt) : lamAbs a 0 = |a 0| := by
  simp only [lamAbs, lamVec_zero]
  exact norm_realC (a 0)

/-- The complex eigen-modulus squared is `normC a = (a 1)^2 + (a 2)^2`. -/
theorem lamAbs_one_sq (a : Pt) : (lamAbs a 1) ^ 2 = normC a := by
  simp only [lamAbs, lamVec_one, normC, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The nonnegativity of the complex eigen-modulus. -/
theorem lamAbs_one_nonneg (a : Pt) : 0 ≤ lamAbs a 1 := norm_nonneg _

/-! ## 3. The inverse is a strict contraction when both moduli are large -/

/-- Coordinates of the inverse, bounded by the two moduli of `a`. -/
theorem invC_coord_bound (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) :
    max (|invC a 0|) (|invC a 1| + |invC a 2|)
      ≤ max (|a 0|)⁻¹ (2 / lamAbs a 1) := by
  have hden : (0 : ℝ) < a 1 ^ 2 + a 2 ^ 2 :=
    lt_of_le_of_ne (by positivity) h1.symm
  have hNpos : 0 < lamAbs a 1 := by
    have hsq : (lamAbs a 1) ^ 2 = a 1 ^ 2 + a 2 ^ 2 := by
      rw [lamAbs_one_sq]; rfl
    nlinarith [lamAbs_one_nonneg a]
  have hsq : (lamAbs a 1) ^ 2 = a 1 ^ 2 + a 2 ^ 2 := by rw [lamAbs_one_sq]; rfl
  have hre : |a 1| ≤ lamAbs a 1 := by
    have h := Complex.abs_re_le_norm (lamVec a 1)
    simpa [lamAbs, lamVec] using h
  have him : |a 2| ≤ lamAbs a 1 := by
    have h := Complex.abs_im_le_norm (lamVec a 1)
    simpa [lamAbs, lamVec] using h
  have hb1 : |invC a 1| ≤ 1 / lamAbs a 1 := by
    rw [invC_apply_one, abs_div, abs_of_pos hden, ← hsq]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (lamAbs a 1) ^ 2)]
    have h1 : 1 / lamAbs a 1 * (lamAbs a 1) ^ 2 = lamAbs a 1 := by
      field_simp
    rw [h1]
    exact hre
  have hb2 : |invC a 2| ≤ 1 / lamAbs a 1 := by
    rw [invC_apply_two, abs_div, abs_neg, abs_of_pos hden, ← hsq]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (lamAbs a 1) ^ 2)]
    have h1 : 1 / lamAbs a 1 * (lamAbs a 1) ^ 2 = lamAbs a 1 := by
      field_simp
    rw [h1]
    exact him
  have hb0 : |invC a 0| ≤ (|a 0|)⁻¹ := by
    rw [invC_apply_zero, abs_inv]
  refine max_le ?_ ?_
  · exact le_trans hb0 (le_max_left (|a 0|)⁻¹ (2 / lamAbs a 1))
  · refine le_trans (add_le_add hb1 hb2) ?_
    rw [← add_div]
    have h2 : ((1:ℝ) + 1) / lamAbs a 1 = 2 / lamAbs a 1 := by norm_num
    rw [h2]
    exact le_max_right (|a 0|)⁻¹ (2 / lamAbs a 1)

/-- **The inverse contracts the sup norm by `1/2`.**  If the real modulus is at
least `4` and the squared complex modulus at least `16`, then multiplication by
`invC a` is a contraction with constant `1/2`. -/
theorem norm_ptMul_invC_le_half (a : Pt) (ha0 : 4 ≤ |a 0|) (hC : 16 ≤ normC a) (x : Pt) :
    ‖ptMul (invC a) x‖ ≤ (2 : ℝ)⁻¹ * ‖x‖ := by
  have hden : (0 : ℝ) < a 1 ^ 2 + a 2 ^ 2 := by
    have h : (0:ℝ) < normC a := by linarith
    have h' : normC a = a 1 ^ 2 + a 2 ^ 2 := rfl
    rwa [h'] at h
  have h0 : a 0 ≠ 0 := by
    intro h; rw [h, abs_zero] at ha0; linarith
  have hN : 4 ≤ lamAbs a 1 := by
    have hsq : (lamAbs a 1) ^ 2 = normC a := lamAbs_one_sq a
    nlinarith [lamAbs_one_nonneg a]
  have hmax : max (|a 0|)⁻¹ (2 / lamAbs a 1) ≤ (2 : ℝ)⁻¹ := by
    refine max_le ?_ ?_
    · have h1 : (|a 0|)⁻¹ ≤ (4:ℝ)⁻¹ := inv_anti₀ (by norm_num) ha0
      have h2 : (4:ℝ)⁻¹ ≤ (2:ℝ)⁻¹ := by norm_num
      linarith
    · rw [div_le_iff₀ (by linarith : (0:ℝ) < lamAbs a 1)]
      have h2 : (2:ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [h2]
      linarith
  calc ‖ptMul (invC a) x‖
      ≤ max (|invC a 0|) (|invC a 1| + |invC a 2|) * ‖x‖ := norm_ptMul_le _ _
    _ ≤ (2 : ℝ)⁻¹ * ‖x‖ := by
        have hb := invC_coord_bound a h0 (ne_of_gt hden)
        have hx : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
        calc max (|invC a 0|) (|invC a 1| + |invC a 2|) * ‖x‖
            ≤ max (|a 0|)⁻¹ (2 / lamAbs a 1) * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right hb hx
          _ ≤ (2 : ℝ)⁻¹ * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right hmax hx

/-! ## 4. A family member whose inverse contracts, as a torus endomorphism -/

/-- Multiplication by `a` as a continuous linear map of `Pt`. -/
noncomputable def ptMulCL (a : Pt) : Pt →L[ℝ] Pt :=
  LinearMap.toContinuousLinearMap (ptMul a)

@[simp] lemma ptMulCL_apply (a x : Pt) : ptMulCL a x = a ⋆ x := rfl

/-- **`a` and `invC a` are mutually inverse** in the model algebra. -/
theorem mulC_invC (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) :
    a ⋆ invC a = oneC := by
  rw [mulC_comm]
  exact invC_mulC a h0 h1

/-- The two non-vanishing hypotheses are implied by the margin hypotheses. -/
theorem margin_nonvanishing (a : Pt) (ha0 : 4 ≤ |a 0|) (hC : 16 ≤ normC a) :
    a 0 ≠ 0 ∧ a 1 ^ 2 + a 2 ^ 2 ≠ 0 := by
  have hden : (0 : ℝ) < a 1 ^ 2 + a 2 ^ 2 := by
    have h : (0:ℝ) < normC a := by linarith
    simpa [normC] using h
  refine ⟨?_, ne_of_gt hden⟩
  intro h
  rw [h, abs_zero] at ha0
  linarith

/-- **The interior step with an explicit unit–prime multiplier.**

Let `D` be a unit–prime model and `a = D.mult u j` a family multiplier with
`4 ≤ |a 0|` and `16 ≤ normC a`.  Then every closed subset of the torus
`Pt ⧸ L` invariant under the torus endomorphism `D.torusAct (u, j)` and containing
a ball is the whole torus.

This is `BerendInteriorFull.eq_univ_of_expanding_of_interior` with the expansion
estimate *produced*: the right inverse of `ptMul a` is `ptMul (invC a)`, and it
contracts the sup norm by `1/2` (`norm_ptMul_invC_le_half`).  Neither ergodicity
nor Haar measure is used, and `ptMul a` need not be injective on the torus. -/
theorem eq_univ_of_torusAct_of_margin {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j))
    [CompactSpace (Pt ⧸ L)]
    {E : Set (Pt ⧸ L)} (hE : IsClosed E)
    (hinv : D.torusAct (u, j) '' E ⊆ E)
    (hint : ∃ x₀ : Pt, ∃ r : ℝ, 0 < r ∧ (QuotientAddGroup.mk' L) '' Metric.ball x₀ r ⊆ E) :
    E = univ := by
  obtain ⟨h0, h1⟩ := margin_nonvanishing (D.mult u j) ha0 hC
  have hAA' : ∀ x : Pt, ptMulCL (D.mult u j) (ptMulCL (invC (D.mult u j)) x) = x := by
    intro x
    show D.mult u j ⋆ (invC (D.mult u j) ⋆ x) = x
    rw [← mulC_assoc, mulC_invC (D.mult u j) h0 h1, oneC_mulC]
  have hexp : ∀ x : Pt, ‖ptMulCL (invC (D.mult u j)) x‖ ≤ (2 : ℝ)⁻¹ * ‖x‖ :=
    fun x => norm_ptMul_invC_le_half (D.mult u j) ha0 hC x
  have hL : ∀ g ∈ L, ptMulCL (D.mult u j) g ∈ L := by
    intro g hg
    have h := D.lattice u j g hg
    simpa [ptMulCL, ptMul_apply, UnitPrimeModel.mult] using h
  have hL' : L ≤ AddSubgroup.comap (ptMulCL (D.mult u j)).toAddMonoidHom L := hL
  have hmap : (QuotientAddGroup.map L L (ptMulCL (D.mult u j)).toAddMonoidHom hL')
      = (D.torusAct (u, j) : Torus L → Torus L) := by
    funext z
    induction z using QuotientAddGroup.induction_on with
    | _ x => rw [QuotientAddGroup.map_mk, UnitPrimeModel.torusAct_mk]; rfl
  have hinv' : (QuotientAddGroup.map L L (ptMulCL (D.mult u j)).toAddMonoidHom hL') '' E ⊆ E := by
    rw [hmap]
    exact hinv
  exact BerendInteriorFull.eq_univ_of_expanding_of_interior (L := L)
    (ptMulCL (D.mult u j)) (ptMulCL (invC (D.mult u j)))
    hAA' (lam := 2) (by norm_num) hexp hL' hE hinv' hint

/-! ## 5. The arithmetic: a multiplier with margin

The trace-norm relations of `BerendEigenBridge` say that for the unit `ε` the three
archimedean moduli `U = lamAbs (σ ε)` satisfy `U 0 * (U 1)^2 = 1`, and for the prime
`π` they satisfy `P 0 * (P 1)^2 = p > 1`.  Consequently the moduli of `ε^N π^j` are

  `(U 0 ^ N * P 0 ^ j, U 1 ^ N * P 1 ^ j, U 1 ^ N * P 1 ^ j)`,

and the *product* of the two numbers `U 0 ^ N * P 0 ^ j` and `U 1 ^ N * P 1 ^ j` is
`p ^ j`, which grows without bound in `j`.  That is exactly what makes the window

  `4 <= U 0 ^ N * P 0 ^ j` and `16 <= (U 1 ^ N * P 1 ^ j) ^ 2`

non-empty for large `j`, and it can be hit by a power of `U 0` because consecutive
powers differ by the factor `U 0 > 1`.  These are the two lower bounds consumed by
`norm_ptMul_invC_le_half`.
-/

/-- **A power of `U > 1` in a window `[A, B)` of ratio bigger than `U`.** -/
theorem exists_pow_between (U A B : ℝ) (hU : 1 < U) (hA : 0 < A) (hB : 1 < B)
    (hAB : A * U < B) : ∃ N : ℕ, A ≤ U ^ N ∧ U ^ N < B := by
  by_cases hA1 : A ≤ 1
  · exact ⟨0, by simpa using hA1, by simpa using hB⟩
  · push_neg at hA1
    have hex : ∃ n : ℕ, A ≤ U ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt A hU
      exact ⟨n, le_of_lt hn⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · exfalso
        have hspec := Nat.find_spec hex
        rw [h] at hspec
        simp only [pow_zero] at hspec
        linarith
      · exact h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ (A ≤ U ^ m) := Nat.find_min hex (by omega)
    have hUp : 0 < U := by linarith
    have hpow : U ^ (Nat.find hex) = U ^ m * U := by rw [hm, pow_succ]
    have hlt' : U ^ m < A := not_le.mp hlt
    have : U ^ m * U < A * U := by
      have := mul_lt_mul_of_pos_right hlt' hUp
      linarith
    linarith [hpow]

/-- **Case `P 1 > 1`.**  Some nonnegative power of the unit, times a power of the
prime, has real modulus `≥ 4` and squared complex modulus `≥ 16`, using only
nonnegative powers of `ε`. -/
theorem exists_window_expand (U Q R p : ℝ) (hU : 1 < U) (hQ : 0 < Q) (hR : 1 < R)
    (hp : 1 < p) (hQR : Q * R ^ 2 = p) :
    ∃ (N j : ℕ), 0 < j ∧ 4 ≤ U ^ N * Q ^ j ∧ 16 ≤ R ^ (2 * j) / U ^ N := by
  have hR2 : 1 < R ^ 2 := by nlinarith
  obtain ⟨j1, hj1⟩ := pow_unbounded_of_one_lt (64 * U) hp
  obtain ⟨j2, hj2⟩ := pow_unbounded_of_one_lt (16 : ℝ) hR2
  set j : ℕ := j1 + j2 + 1 with hjdef
  have hj1' : j1 ≤ j := by omega
  have hj2' : j2 ≤ j := by omega
  have hpj : 64 * U < p ^ j := by
    have hle : p ^ j1 ≤ p ^ j := pow_le_pow_right₀ hp.le hj1'
    linarith
  have hR16 : 16 < R ^ (2 * j) := by
    have h1 : R ^ (2 * j) = (R ^ 2) ^ j := by ring_nf
    rw [h1]
    have hle : (R ^ 2) ^ j2 ≤ (R ^ 2) ^ j := pow_le_pow_right₀ hR2.le hj2'
    linarith
  have hQj : (0:ℝ) < Q ^ j := pow_pos hQ j
  have hQRj : Q ^ j * R ^ (2 * j) = p ^ j := by
    have h1 : R ^ (2 * j) = (R ^ 2) ^ j := by ring_nf
    rw [h1, ← mul_pow, hQR]
  obtain ⟨N, hN1, hN2⟩ :=
    exists_pow_between U (4 / Q ^ j) (R ^ (2 * j) / 16) hU (by positivity) (by linarith) (by
      have hQj : (0:ℝ) < Q ^ j := pow_pos (by linarith : (0:ℝ) < Q) j
      have hRpos : (0:ℝ) < R ^ (2 * j) := pow_pos (by linarith : (0:ℝ) < R) (2 * j)
      rw [div_mul_eq_mul_div]
      field_simp
      nlinarith)
  refine ⟨N, j, by omega, ?_, ?_⟩
  · rw [div_le_iff₀ hQj] at hN1
    linarith
  · rw [le_div_iff₀ (pow_pos (by linarith : (0:ℝ) < U) N)]
    linarith

/-- **Case `P 1 ≤ 1`.**  Here the prime expands at the real place and contracts at
the complex one, so only a *negative* power of `ε` works; equivalently, a
nonnegative power of the inverse unit `ε⁻¹`.  The window lemma is applied to the
reciprocals. -/
theorem exists_window_shrink (U Q R p : ℝ) (hU : 1 < U) (hQ : 1 < Q) (hR : 0 < R) (hR1 : R ≤ 1)
    (hp : 1 < p) (hQR : Q * R ^ 2 = p) :
    ∃ (N j : ℕ), 0 < j ∧ 4 ≤ Q ^ j / U ^ N ∧ 16 ≤ U ^ N * R ^ (2 * j) := by
  have hR2le : R ^ 2 ≤ 1 := pow_le_one₀ hR.le hR1
  obtain ⟨j1, hj1⟩ := pow_unbounded_of_one_lt (64 * U) hp
  obtain ⟨j2, hj2⟩ := pow_unbounded_of_one_lt (4 : ℝ) hQ
  set j : ℕ := j1 + j2 + 1 with hjdef
  have hj1' : j1 ≤ j := by omega
  have hj2' : j2 ≤ j := by omega
  have hpj : 64 * U < p ^ j := by
    have hle : p ^ j1 ≤ p ^ j := pow_le_pow_right₀ hp.le hj1'
    linarith
  have hQ4 : 4 < Q ^ j := by
    have hle : Q ^ j2 ≤ Q ^ j := pow_le_pow_right₀ hQ.le hj2'
    linarith
  have hRpos : (0:ℝ) < R ^ (2 * j) := pow_pos hR (2 * j)
  have hQRj : Q ^ j * R ^ (2 * j) = p ^ j := by
    have h1 : R ^ (2 * j) = (R ^ 2) ^ j := by ring_nf
    rw [h1, ← mul_pow, hQR]
  obtain ⟨N, hN1, hN2⟩ :=
    exists_pow_between U (16 / R ^ (2 * j)) (Q ^ j / 4) hU (by positivity) (by linarith) (by
      have hQj : (0:ℝ) < Q ^ j := pow_pos (by linarith : (0:ℝ) < Q) j
      have hRpos' : (0:ℝ) < R ^ (2 * j) := pow_pos hR (2 * j)
      rw [div_mul_eq_mul_div]
      field_simp
      nlinarith)
  refine ⟨N, j, by omega, ?_, ?_⟩
  · have hUN : (0:ℝ) < U ^ N := pow_pos (by linarith : (0:ℝ) < U) N
    rw [le_div_iff₀ hUN]
    nlinarith [hN2]
  · rw [div_le_iff₀ hRpos] at hN1
    linarith

/-! ## 6. Transfer to the unit–prime model

The eigen-moduli of a family element are `lamAbs (mult u j) i = U i * (P i)^j`, and
the moduli of a power of a unit are the powers of its moduli.  With the two cases of
§5 this produces, for every unit `ε` expanding at the real place, a family element
with the margin of §3. -/

section Model

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The eigenvalue vector of the model unit is `1` at every place. -/
theorem lamVec_oneC : lamVec oneC = fun _ => (1 : ℂ) := by
  funext i
  fin_cases i <;> (apply Complex.ext <;> simp [lamVec, oneC])

theorem lamAbs_oneC (i : Fin 3) : lamAbs oneC i = 1 := by
  simp [lamAbs, lamVec_oneC]

/-- The moduli of a power in the model algebra are the powers of the moduli. -/
theorem lamAbs_powC (a : Pt) (n : ℕ) (i : Fin 3) :
    lamAbs (powC a n) i = (lamAbs a i) ^ n := by
  induction n with
  | zero => simpa using lamAbs_oneC i
  | succ n ih =>
      rw [powC_succ, lamAbs_mulC]
      change lamAbs a i * lamAbs (powC a n) i = (lamAbs a i) ^ (n + 1)
      rw [ih, pow_succ]
      ring

/-- The moduli of a power of a unit of `𝒪` are the powers of its moduli. -/
theorem lamAbs_unit_pow (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (n : ℕ) (i : Fin 3) :
    lamAbs (D.unit_image (u ^ n)) i = (lamAbs (D.unit_image u) i) ^ n := by
  induction n with
  | zero => rw [pow_zero, D.unit_one]; exact lamAbs_oneC i
  | succ n ih =>
      rw [pow_succ, D.unit_mul, lamAbs_mulC]
      change lamAbs (D.unit_image (u ^ n)) i * lamAbs (D.unit_image u) i
        = (lamAbs (D.unit_image u) i) ^ (n + 1)
      rw [ih, pow_succ, mul_comm]

/-- The moduli of a family multiplier: `τ(u π^j)`. -/
theorem lamAbs_mult_family (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (i : Fin 3) :
    lamAbs (D.mult u j) i
      = lamAbs (D.unit_image u) i * (lamAbs (D.prime_image D.prime) i) ^ j := by
  show lamAbs (D.unit_image u ⋆ powC (D.prime_image D.prime) j) i = _
  rw [lamAbs_mulC]
  change lamAbs (D.unit_image u) i * lamAbs (powC (D.prime_image D.prime) j) i = _
  rw [lamAbs_powC]

/-- A unit and its inverse have reciprocal moduli. -/
theorem lamAbs_unit_inv_mul (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (i : Fin 3) :
    lamAbs (D.unit_image u⁻¹) i * lamAbs (D.unit_image u) i = 1 := by
  have h2 : lamAbs (D.unit_image u⁻¹ ⋆ D.unit_image u) i = lamAbs oneC i := by
    rw [← D.unit_mul, inv_mul_cancel, D.unit_one]
  rw [lamAbs_mulC, lamAbs_oneC] at h2
  exact h2

/-- A unit and its inverse have reciprocal moduli, in the form used below. -/
theorem lamAbs_unit_inv (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (i : Fin 3) :
    lamAbs (D.unit_image u⁻¹) i = (lamAbs (D.unit_image u) i)⁻¹ := by
  have h := lamAbs_unit_inv_mul D u i
  exact eq_inv_of_mul_eq_one_left h

/-- The moduli of the inverse of a power of a unit: the reciprocal powers. -/
theorem lamAbs_unit_inv_pow (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (n : ℕ) (i : Fin 3) :
    lamAbs (D.unit_image ((u ^ n)⁻¹)) i = ((lamAbs (D.unit_image u) i) ^ n)⁻¹ := by
  rw [lamAbs_unit_inv, lamAbs_unit_pow]

/-- `(x ^ n) ^ 2 = (x ^ 2) ^ n`. -/
theorem sq_pow (x : ℝ) (n : ℕ) : (x ^ n) ^ 2 = (x ^ 2) ^ n := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The transfer lemma.**  If the unit expands at the real place and the two
product relations `U 0 * (U 1)^2 = 1`, `P 0 * (P 1)^2 = p > 1` hold, then some
family multiplier has real modulus `≥ 4` and squared complex modulus `≥ 16`. -/
theorem exists_mult_margin_lamAbs (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hU0 : 1 < lamAbs (D.unit_image ε) 0)
    (hU : lamAbs (D.unit_image ε) 0 * (lamAbs (D.unit_image ε) 1) ^ 2 = 1)
    (p : ℝ) (hp : 1 < p)
    (hP : lamAbs (D.prime_image D.prime) 0 * (lamAbs (D.prime_image D.prime) 1) ^ 2 = p) :
    ∃ (u : 𝒪ˣ) (j : ℕ), 0 < j ∧ 4 ≤ lamAbs (D.mult u j) 0 ∧
      16 ≤ (lamAbs (D.mult u j) 1) ^ 2 := by
  set U0 := lamAbs (D.unit_image ε) 0 with hU0def
  set U1 := lamAbs (D.unit_image ε) 1 with hU1def
  set Q := lamAbs (D.prime_image D.prime) 0 with hQdef
  set R := lamAbs (D.prime_image D.prime) 1 with hRdef
  have hU0' : 1 < U0 := by rw [hU0def]; exact hU0
  have hU' : U0 * U1 ^ 2 = 1 := by rw [hU0def, hU1def]; exact hU
  have hP' : Q * R ^ 2 = p := by rw [hQdef, hRdef]; exact hP
  have hU0pos : 0 < U0 := by linarith
  have hQnn : (0:ℝ) ≤ Q := by rw [hQdef]; exact lamAbs_nonneg _ _
  have hRnn : (0:ℝ) ≤ R := by rw [hRdef]; exact lamAbs_nonneg _ _
  have hQpos : 0 < Q := by
    rcases lt_or_eq_of_le hQnn with h | h
    · exact h
    · exfalso; rw [← h] at hP'; simp at hP'; linarith
  have hRpos : 0 < R := by
    rcases lt_or_eq_of_le hRnn with h | h
    · exact h
    · exfalso; rw [← h] at hP'; simp at hP'; linarith
  have hU1sq : U1 ^ 2 = 1 / U0 := by
    rw [eq_div_iff (ne_of_gt hU0pos)]
    linarith
  by_cases hR1 : 1 < R
  · -- the prime expands at the complex place: use nonnegative powers of `ε`
    obtain ⟨N, j, hj, h1, h2⟩ := exists_window_expand U0 Q R p hU0' hQpos hR1 hp hP'
    refine ⟨ε ^ N, j, hj, ?_, ?_⟩
    · rw [lamAbs_mult_family, lamAbs_unit_pow]
      exact h1
    · rw [lamAbs_mult_family, lamAbs_unit_pow]
      have hsq : (U1 ^ N) ^ 2 = 1 / U0 ^ N := by
        rw [sq_pow, hU1sq, div_pow]
        simp
      have hmain : (U1 ^ N * R ^ j) ^ 2 = R ^ (2 * j) / U0 ^ N := by
        rw [mul_pow, hsq, sq_pow]
        have h2j : R ^ (2 * j) = (R ^ 2) ^ j := by ring_nf
        rw [h2j, div_mul_eq_mul_div, one_mul]
      rw [hmain]
      exact h2
  · -- the prime contracts at the complex place: use the inverse unit
    push_neg at hR1
    have hQ1 : 1 < Q := by
      have hR2le : R ^ 2 ≤ 1 := pow_le_one₀ hRpos.le hR1
      nlinarith
    obtain ⟨N, j, hj, h1, h2⟩ := exists_window_shrink U0 Q R p hU0' hQ1 hRpos hR1 hp hP'
    refine ⟨(ε ^ N)⁻¹, j, hj, ?_, ?_⟩
    · rw [lamAbs_mult_family, lamAbs_unit_inv_pow]
      rw [div_eq_inv_mul] at h1
      exact h1
    · rw [lamAbs_mult_family, lamAbs_unit_inv_pow]
      have hsq : ((U1 ^ N)⁻¹) ^ 2 = U0 ^ N := by
        rw [inv_pow, sq_pow, hU1sq, div_pow]
        simp
      have hmain : ((U1 ^ N)⁻¹ * R ^ j) ^ 2 = U0 ^ N * R ^ (2 * j) := by
        rw [mul_pow, hsq, sq_pow]
        have h2j : R ^ (2 * j) = (R ^ 2) ^ j := by ring_nf
        rw [h2j]
      rw [hmain]
      exact h2

/-- The margin in the form consumed by `norm_ptMul_invC_le_half`. -/
theorem exists_mult_margin (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hU0 : 1 < lamAbs (D.unit_image ε) 0)
    (hU : lamAbs (D.unit_image ε) 0 * (lamAbs (D.unit_image ε) 1) ^ 2 = 1)
    (p : ℝ) (hp : 1 < p)
    (hP : lamAbs (D.prime_image D.prime) 0 * (lamAbs (D.prime_image D.prime) 1) ^ 2 = p) :
    ∃ (u : 𝒪ˣ) (j : ℕ), 0 < j ∧ 4 ≤ |D.mult u j 0| ∧ 16 ≤ normC (D.mult u j) := by
  obtain ⟨u, j, hj, h1, h2⟩ := exists_mult_margin_lamAbs D ε hU0 hU p hp hP
  exact ⟨u, j, hj, by rwa [lamAbs_zero_eq_abs] at h1, by rwa [← lamAbs_one_sq]⟩

end Model

/-! ## 7. The expanding member for the `FieldModel` instance -/

section FieldModelInstance

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- The product relations `U 0 * (U 1)^2 = 1` and `P 0 * (P 1)^2 = p` for the
unit–prime model attached to a `FieldModel`, read off the trace-norm relations
`prod_lamAbs_unit` and `prod_lamAbs_prime`. -/
theorem toModel_unit_product (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) :
    lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0 *
      (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 1) ^ 2 = 1 := by
  have h := prod_lamAbs_unit FM ε
  have h12 := lamAbs_one_eq_two (FM.σ (((ε : 𝒪) : K)))
  rw [Fin.prod_univ_three] at h
  rw [← h12] at h
  simpa [pow_two, mul_assoc] using h

/-- The same for the prime. -/
theorem toModel_prime_product (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (p : ℕ) (hπN : Nm π = (p : ℚ≥0)) :
    lamAbs ((FM.toModel ε π hπO hπ0).prime_image (FM.toModel ε π hπO hπ0).prime) 0 *
      (lamAbs ((FM.toModel ε π hπO hπ0).prime_image
        (FM.toModel ε π hπO hπ0).prime) 1) ^ 2 = (p : ℝ) := by
  have h := prod_lamAbs_prime FM π p hπN
  have h12 := lamAbs_one_eq_two (FM.σ π)
  rw [Fin.prod_univ_three] at h
  rw [← h12] at h
  simpa [pow_two, mul_assoc] using h

/-- **The expanding member exists in the unit–prime model.**  If the unit expands at
the real place and `Nm π = p > 1`, then some multiplier `μ_{uπ^j}` has
`|μ_{uπ^j} 0| ≥ 4` and `normC μ_{uπ^j} ≥ 16`: exactly the margin which makes
`ptMul (μ_{uπ^j})⁻¹` a contraction of constant `1/2`. -/
theorem exists_mult_margin_fieldModel (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < (p : ℝ))
    (hπN : Nm π = (p : ℚ≥0)) (hε : 1 < lamAbs (FM.σ (((ε : 𝒪) : K))) 0) :
    ∃ (u : 𝒪ˣ) (j : ℕ), 0 < j ∧
      4 ≤ |(FM.toModel ε π hπO hπ0).mult u j 0| ∧
      16 ≤ normC ((FM.toModel ε π hπO hπ0).mult u j) := by
  have hp' : (1 : ℝ) < (p : ℝ) := hp
  exact exists_mult_margin (FM.toModel ε π hπO hπ0) ε (by simpa using hε)
    (toModel_unit_product FM ε π hπO hπ0) (p : ℝ) hp'
    (by simpa using toModel_prime_product FM ε π hπO hπ0 p hπN)

/-- **The interior step of Proposition IV.1 for the unit–prime model, with the
expanding member produced.**  Every closed subset of the torus invariant under the
whole family `Σ = {μ_{uπ^j}}` and containing a ball is the whole torus.

No ergodicity, no Haar measure, no injectivity: the expansion comes from an explicit
family member provided by `exists_mult_margin_fieldModel`, and the ball growth from
`BerendInteriorFull.eq_univ_of_expanding_of_interior`. -/
theorem eq_univ_of_interior_fieldModel (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < (p : ℝ))
    (hπN : Nm π = (p : ℚ≥0)) (hε : 1 < lamAbs (FM.σ (((ε : 𝒪) : K))) 0)
    [CompactSpace (Pt ⧸ FM.lattice)]
    {E : Set (Torus FM.lattice)} (hE : IsClosed E)
    (hinv : ∀ i : 𝒪ˣ × ℕ, (FM.toModel ε π hπO hπ0).torusAct i '' E ⊆ E)
    (hint : ∃ x₀ : Pt, ∃ r : ℝ, 0 < r ∧
      (QuotientAddGroup.mk' FM.lattice) '' Metric.ball x₀ r ⊆ E) :
    E = univ := by
  obtain ⟨u, j, hj, h1, h2⟩ := exists_mult_margin_fieldModel FM ε π hπO hπ0 p hp hπN hε
  exact eq_univ_of_torusAct_of_margin (FM.toModel ε π hπO hπ0) u j h1 h2 hE (hinv (u, j)) hint

end FieldModelInstance

/-! ## 7½. Powers of the expanding member

Step (c) of Proposition IV.1 applies the expanding member inside the congruence
subsemigroup `Σ^(n) = {σ : σ ≡ 1 mod q^n}`, so the margin must survive taking a
power — moreover the power must again be a *family* element.  Both hold:
`powC (mult u j) m = mult (u ^ m) (j * m)` (`powC_mult`) and the margin is monotone
under positive powers (`powC_margin`).  Consequently, for any finite quotient
carrying a group structure (e.g. `GL_3(ℤ/q^nℤ)`) some positive power of the
expanding multiplier is the identity there, and the interior step still applies.
-/

section Powers

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The real coordinate of a power of a model element. -/
theorem powC_apply_zero (a : Pt) (m : ℕ) : powC a m 0 = (a 0) ^ m := by
  induction m with
  | zero => simp [powC, oneC]
  | succ m ih => rw [powC_succ, mulC_apply_zero, ih, pow_succ, mul_comm]

/-- Powers add in the model algebra. -/
theorem powC_add (a : Pt) (m n : ℕ) : powC a (m + n) = powC a m ⋆ powC a n := by
  have h1 : powC a (m + n) = (mulC a)^[m + n] oneC := rfl
  have h2 : (mulC a)^[m + n] oneC = (mulC a)^[m] ((mulC a)^[n] oneC) := by
    rw [Function.iterate_add_apply]
  have h3 : powC a m ⋆ powC a n = (mulC a)^[m] ((mulC a)^[n] oneC) :=
    powC_mulC a (powC a n) m
  rw [h1, h2, h3]

/-- The complex block of a power: the moduli multiply. -/
theorem normC_powC (a : Pt) (m : ℕ) : normC (powC a m) = (normC a) ^ m := by
  induction m with
  | zero => simp [powC, normC, oneC]
  | succ m ih => rw [powC_succ, normC_mulC, ih, pow_succ, mul_comm]

/-- **The margin is preserved by positive powers.** -/
theorem powC_margin (a : Pt) (ha0 : 4 ≤ |a 0|) (hC : 16 ≤ normC a) {m : ℕ} (hm : 0 < m) :
    4 ≤ |powC a m 0| ∧ 16 ≤ normC (powC a m) := by
  have hann : (0:ℝ) ≤ |a 0| := abs_nonneg _
  have hCnn : (0:ℝ) ≤ normC a := le_trans (by norm_num) hC
  constructor
  · rw [powC_apply_zero, abs_pow]
    calc (4:ℝ) ≤ |a 0| := ha0
      _ = |a 0| ^ 1 := (pow_one _).symm
      _ ≤ |a 0| ^ m := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ |a 0|) hm
  · rw [normC_powC]
    calc (16:ℝ) ≤ normC a := hC
      _ = (normC a) ^ 1 := (pow_one _).symm
      _ ≤ (normC a) ^ m := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ normC a) hm

/-- Multipliers multiply, and the index adds. -/
theorem mult_mul (D : UnitPrimeModel L 𝒪) (u v : 𝒪ˣ) (j l : ℕ) :
    D.mult u j ⋆ D.mult v l = D.mult (u * v) (j + l) := by
  show (D.unit_image u ⋆ powC (D.prime_image D.prime) j) ⋆
      (D.unit_image v ⋆ powC (D.prime_image D.prime) l)
    = D.unit_image (u * v) ⋆ powC (D.prime_image D.prime) (j + l)
  rw [D.unit_mul, powC_add, mulC_mul_mul_comm]

/-- **A power of a family multiplier is again a family multiplier.** -/
theorem powC_mult (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j m : ℕ) :
    powC (D.mult u j) m = D.mult (u ^ m) (j * m) := by
  induction m with
  | zero =>
      show powC (D.mult u j) 0 = D.mult (u ^ 0) (j * 0)
      rw [powC_zero, pow_zero, Nat.mul_zero]
      show oneC = D.mult 1 0
      rw [show D.mult 1 0 = D.unit_image 1 ⋆ powC (D.prime_image D.prime) 0 from rfl,
        D.unit_one, powC_zero, mulC_oneC]
  | succ m ih =>
      rw [powC_succ, ih, mult_mul, pow_succ, Nat.mul_succ]
      rw [mul_comm u (u ^ m), Nat.add_comm j (j * m)]

end Powers

#print axioms CubicTwoStage.powC_margin
#print axioms CubicTwoStage.powC_mult

/-- **The interior step with the expanding member taken inside a subsemigroup.**

If `a = D.mult u j` has the margin, then so does every positive power, and the
power is again a family multiplier: `(D.mult u j)^m = D.mult (u^m) (j*m)`.  Hence
the closed-invariant-set-with-interior conclusion holds with `torusAct (u^m, j*m)`
in place of `torusAct (u, j)`.  This is the form needed in step (c) of Proposition
IV.1, where the expanding element has to lie in the congruence subsemigroup
`Σ^(n)` — take `m` to be a positive power killing the class of `(u, j)` in the
finite quotient `GL_3(ℤ/q^nℤ)` (e.g. `m` a multiple of the order of that class). -/
theorem eq_univ_of_interior_of_pow_margin {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j))
    [CompactSpace (Pt ⧸ L)] {E : Set (Pt ⧸ L)} (hE : IsClosed E)
    {m : ℕ} (hm : 0 < m)
    (hinv : D.torusAct (u ^ m, j * m) '' E ⊆ E)
    (hint : ∃ x₀ : Pt, ∃ r : ℝ, 0 < r ∧ (QuotientAddGroup.mk' L) '' Metric.ball x₀ r ⊆ E) :
    E = univ := by
  obtain ⟨h1, h2⟩ := powC_margin (D.mult u j) ha0 hC hm
  rw [powC_mult] at h1 h2
  exact eq_univ_of_torusAct_of_margin D (u ^ m) (j * m) h1 h2 hE hinv hint

#print axioms CubicTwoStage.eq_univ_of_interior_of_pow_margin

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- Reciprocation preserves the product relation `x * y^2 = 1`. -/
theorem inv_mul_inv_sq (x y : ℝ) (h : x * y ^ 2 = 1) : x⁻¹ * (y⁻¹) ^ 2 = 1 := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hy : y ≠ 0 := by rintro rfl; simp at h
  field_simp
  linarith

/-- **The margin from a non-critical unit.**  It is enough that the unit is not
critical at the real place (`lamAbs (σ ε) 0 ≠ 1`): if it contracts there, the same
argument is run with `ε⁻¹`.  This is the form in which the arithmetic input of the
model is available — a unit of infinite order (`hεpow`) has some conjugate of modulus
`≠ 1`, so it is not critical. -/
theorem exists_mult_margin_fieldModel_of_ne_one (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < (p : ℝ))
    (hπN : Nm π = (p : ℚ≥0)) (hε : lamAbs (FM.σ (((ε : 𝒪) : K))) 0 ≠ 1) :
    ∃ (u : 𝒪ˣ) (j : ℕ), 0 < j ∧
      4 ≤ |(FM.toModel ε π hπO hπ0).mult u j 0| ∧
      16 ≤ normC ((FM.toModel ε π hπO hπ0).mult u j) := by
  rcases lt_or_gt_of_ne hε with hlt | hgt
  · -- the unit contracts at the real place: use `ε⁻¹`
    have hab : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0 *
        (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 1) ^ 2 = 1 :=
      toModel_unit_product FM ε π hπO hπ0
    have hUpos : 0 < lamAbs (FM.σ (((ε : 𝒪) : K))) 0 := by
      have hnn : (0:ℝ) ≤ lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0 :=
        lamAbs_nonneg _ 0
      have hne : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0 ≠ 0 := by
        intro hzero
        rw [hzero] at hab
        simp at hab
      exact lt_of_le_of_ne hnn (Ne.symm hne)
    have hprod : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 0 *
        (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 1) ^ 2 = 1 := by
      have h := hab
      have e0 : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 0
          = (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0)⁻¹ :=
        lamAbs_unit_inv _ _ _
      have e1 : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 1
          = (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 1)⁻¹ :=
        lamAbs_unit_inv _ _ _
      rw [e0, e1]
      exact inv_mul_inv_sq _ _ h
    have hle : 1 < lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 0 := by
      have e0 : lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε⁻¹) 0
          = (lamAbs ((FM.toModel ε π hπO hπ0).unit_image ε) 0)⁻¹ :=
        lamAbs_unit_inv _ _ _
      rw [e0]
      exact one_lt_inv_iff₀.mpr ⟨hUpos, hlt⟩
    exact exists_mult_margin (FM.toModel ε π hπO hπ0) ε⁻¹ hle hprod (p : ℝ) hp
      (by simpa using toModel_prime_product FM ε π hπO hπ0 p hπN)
  · exact exists_mult_margin_fieldModel FM ε π hπO hπ0 p hp hπN hgt

#print axioms CubicTwoStage.exists_mult_margin_fieldModel_of_ne_one

/-! ## 8. Axiom audit -/

#print axioms CubicTwoStage.norm_ptMul_invC_le_half
#print axioms CubicTwoStage.eq_univ_of_torusAct_of_margin
#print axioms CubicTwoStage.exists_window_expand
#print axioms CubicTwoStage.exists_window_shrink
#print axioms CubicTwoStage.exists_mult_margin
#print axioms CubicTwoStage.exists_mult_margin_fieldModel
#print axioms CubicTwoStage.eq_univ_of_interior_fieldModel

end CubicTwoStage
