/-
**Proposition 3.1** (Cooke's criterion) and its two remarks.
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-- **Proposition 3.1** (Cooke, Corollary 1; cf. Guitart–Masdeu, Proposition 2.1).

The pair `(α, β)` with `α, β ∈ 𝒪` and `β ≠ 0` has a 2-stage decreasing chain
with quotients and remainders in `𝒪` if and only if

  `|Nm(α/β - [q₁,q₂])| < 1/|Nm q₂|`   for some `q₁, q₂ ∈ 𝒪` with `q₂ ≠ 0`.

In that case `q₁, q₂` are the quotients of such a chain.

Note.  The paper states this for chains of length `k ≤ 2`.  The equivalence
proved here is exactly the 2-stage one, which is what the proof gives and what
Theorem 3.3 uses; the 1-stage case corresponds to chains whose denominator `q₂`
is a unit (see `hasOneStageChain_of_unit_denominator` and
`hasTwoStageChain_of_oneStage`). -/
theorem prop_cooke (𝒪 : Subring K) (N : AbsNorm K) {α β : K}
    (hα : α ∈ 𝒪) (hβ : β ∈ 𝒪) (hβ0 : β ≠ 0) :
    HasTwoStageChain 𝒪 N α β ↔
      ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (α / β - (q1 + q2⁻¹)) < (N q2)⁻¹ := by
  have hβn : N β ≠ 0 := (AbsNorm.ne_zero_iff N).mpr hβ0
  constructor
  · rintro ⟨q1, hq1, q2, hq2, r1, hr1, r2, hr2, hA, hB, hlt⟩
    have hq2ne : q2 ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_add] at hB
      rw [← hB] at hlt
      exact lt_irrefl _ hlt
    refine ⟨q1, hq1, q2, hq2, hq2ne, ?_⟩
    have hq2n : N q2 ≠ 0 := (AbsNorm.ne_zero_iff N).mpr hq2ne
    have hEq : α / β - (q1 + q2⁻¹) = -r2 / (q2 * β) := by
      have hr1 : r1 = α - q1 * β := by rw [hA]; ring
      have hr2' : r2 = β - q2 * r1 := by rw [hB]; ring
      rw [hr2', hr1]
      field_simp
      ring
    have hN : N (α / β - (q1 + q2⁻¹)) = N r2 / (N q2 * N β) := by
      rw [hEq, AbsNorm.div, map_mul, AbsNorm.abs_neg]
    rw [hN, div_lt_iff₀ (by
      exact mul_pos (zero_lt_iff.mpr hq2n) (zero_lt_iff.mpr hβn))]
    calc N r2 < N β := hlt
      _ = (N q2)⁻¹ * (N q2 * N β) := by
          rw [← mul_assoc, inv_mul_cancel₀ hq2n, one_mul]
  · rintro ⟨q1, hq1, q2, hq2, hq2ne, hineq⟩
    have hq2n : N q2 ≠ 0 := (AbsNorm.ne_zero_iff N).mpr hq2ne
    refine ⟨q1, hq1, q2, hq2, α - q1 * β, 𝒪.sub_mem hα (𝒪.mul_mem hq1 hβ),
      β - q2 * (α - q1 * β), 𝒪.sub_mem hβ (𝒪.mul_mem hq2 (𝒪.sub_mem hα (𝒪.mul_mem hq1 hβ))),
      by ring, by ring, ?_⟩
    have hr2 : β - q2 * (α - q1 * β) = -(q2 * β * (α / β - (q1 + q2⁻¹))) := by
      field_simp
      ring
    have hNB : N (β - q2 * (α - q1 * β))
        = (N q2 * N β) * N (α / β - (q1 + q2⁻¹)) := by
      rw [hr2, AbsNorm.abs_neg, map_mul, map_mul]
    rw [hNB]
    have hval : (N q2 * N β) * (N q2)⁻¹ = N β := by
      calc (N q2 * N β) * (N q2)⁻¹ = N β * (N q2 * (N q2)⁻¹) := by ring
        _ = N β := by rw [mul_inv_cancel₀ hq2n, mul_one]
    calc (N q2 * N β) * N (α / β - (q1 + q2⁻¹)) < (N q2 * N β) * (N q2)⁻¹ := by
          apply mul_lt_mul_of_pos_left hineq
          exact mul_pos (zero_lt_iff.mpr hq2n) (zero_lt_iff.mpr hβn)
      _ = N β := hval

/-- Paper, proof of Proposition 3.1: if the denominator `q₂` of a 2-stage chain
is a **unit** of `𝒪`, the chain can be shortened to a 1-stage chain.

`hvn` records that the norm of a unit of `𝒪` is `1`; for `N = |Nm_{K/ℚ}|` this
holds because every unit of `𝒪_K` has norm `±1`. -/
theorem hasOneStageChain_of_unit_denominator (𝒪 : Subring K) (N : AbsNorm K)
    {α β q1 r1 r2 : K} (hq1 : q1 ∈ 𝒪) (v : 𝒪ˣ)
    (hr2 : r2 ∈ 𝒪) (hA : α = q1 * β + r1) (hB : β = ((v : 𝒪) : K) * r1 + r2)
    (hlt : N r2 < N β) (hvn : N (((v : 𝒪) : K)) = 1) :
    HasOneStageChain 𝒪 N α β := by
  have hvK : (((v : 𝒪) : K)) ≠ 0 := by
    intro h
    have h0 : N (((v : 𝒪) : K)) = 0 := by rw [h, map_zero]
    rw [hvn] at h0
    exact zero_ne_one h0.symm
  have hvu : ((((v⁻¹ : 𝒪ˣ) : 𝒪) : K)) = ((((v : 𝒪) : K)))⁻¹ := by
    have h : (((v⁻¹ : 𝒪ˣ) : 𝒪) : K) * (((v : 𝒪) : K)) = 1 := by
      calc (((v⁻¹ : 𝒪ˣ) : 𝒪) : K) * (((v : 𝒪) : K))
          = (((((v⁻¹ : 𝒪ˣ) : 𝒪) * (v : 𝒪)) : 𝒪) : K) := (map_mul 𝒪.subtype _ _).symm
        _ = 1 := by rw [Units.inv_mul]; exact map_one 𝒪.subtype
    exact eq_inv_of_mul_eq_one_left h
  have hwO : ((((v⁻¹ : 𝒪ˣ) : 𝒪) : K)) ∈ 𝒪 := ((v⁻¹ : 𝒪ˣ) : 𝒪).2
  refine ⟨q1 + (((v⁻¹ : 𝒪ˣ) : 𝒪) : K), 𝒪.add_mem hq1 hwO,
    -(r2 * (((v⁻¹ : 𝒪ˣ) : 𝒪) : K)), 𝒪.neg_mem (𝒪.mul_mem hr2 hwO), ?_, ?_⟩
  · have hr1 : r1 = (β - r2) * (((v : 𝒪) : K))⁻¹ := by
      rw [hB]; field_simp; ring
    rw [hA, hr1, hvu]
    field_simp
    ring
  · rw [AbsNorm.abs_neg, map_mul, hvu, AbsNorm.inv, hvn, inv_one, mul_one]
    exact hlt

/-- If `(α,β)` has a 1-stage chain `α = q₁β + r₁` and `(β,r₁)` has a 1-stage
chain `β = q₂r₁ + r₂`, then `(α,β)` has a 2-stage chain.  This is why a field in
which every pair has a 1-stage chain is 2-stage Euclidean, i.e. why the `k ≤ 2`
of Proposition 3.1 may be read as "2-stage". -/
theorem hasTwoStageChain_of_oneStage (𝒪 : Subring K) (N : AbsNorm K)
    {α β q1 r1 q2 r2 : K} (hq1 : q1 ∈ 𝒪) (hq2 : q2 ∈ 𝒪) (hr1 : r1 ∈ 𝒪) (hr2 : r2 ∈ 𝒪)
    (hA : α = q1 * β + r1) (hB : β = q2 * r1 + r2)
    (h1 : N r1 < N β) (h2 : N r2 < N r1) :
    HasTwoStageChain 𝒪 N α β :=
  ⟨q1, hq1, q2, hq2, r1, hr1, r2, hr2, hA, hB, lt_trans h2 h1⟩

end CubicTwoStage
