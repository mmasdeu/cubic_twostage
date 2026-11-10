/-
Formalization companion to

  M. Masdeu, *Two-stage Euclidean algorithms and continued fractions in complex
  cubic fields*.

This file sets up the two objects that everything else is phrased in:

* the algebraic side: an absolute norm on a number field, the continued
  fraction `[q₁,q₂] = q₁ + 1/q₂`, decreasing division chains, `2`-stage
  Euclideanity;
* the geometric side: the model space `ℝ × ℂ ≅ ℝ³` with `Nm(u,w) = u|w|²`, the
  open regions `V(q)`, and the fundamental domain of the ring of integers.

Reference labels of the paper are recorded in the docstrings, e.g. `(3.1)`.
-/
import Mathlib

open MeasureTheory

namespace CubicTwoStage

/-! ## The algebraic side -/

variable {K : Type*}

/-- An **absolute norm** on a field `K`: a multiplicative map to `ℚ≥0` sending
`0` to `0` and `1` to `1`.  For a number field `K` the intended instance is
`x ↦ |Nm_{K/ℚ} x|`. -/
abbrev AbsNorm (K : Type*) [Field K] := K →*₀ ℚ≥0

namespace AbsNorm

variable [Field K] (N : AbsNorm K)

/-- An absolute norm vanishes exactly on zero.  This is *not* an extra axiom:
it follows from multiplicativity and `N 1 = 1`. -/
theorem eq_zero_iff {a : K} : N a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra ha
  have h1 : N a * N a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem ne_zero_iff {a : K} : N a ≠ 0 ↔ a ≠ 0 := by
  rw [Ne, eq_zero_iff]

@[simp] theorem abs_neg (a : K) : N (-a) = N a := by
  have h : N (-1 : K) * N (-1 : K) = 1 := by
    rw [← map_mul]; norm_num
  have hpos : N (-1 : K) = 1 := by
    have hR : ((N (-1 : K) : ℚ≥0) : ℝ) * ((N (-1 : K) : ℚ≥0) : ℝ) = 1 := by
      have := congrArg (fun x : ℚ≥0 => (x : ℝ)) h
      simpa using this
    have h0 : (0 : ℝ) ≤ ((N (-1 : K) : ℚ≥0) : ℝ) := by positivity
    have h1 : ((N (-1 : K) : ℚ≥0) : ℝ) = 1 := by nlinarith
    exact NNRat.coe_inj.mp (by exact_mod_cast h1)
  rw [show (-a) = (-1) * a by ring, map_mul, hpos, one_mul]

theorem div (a b : K) : N (a / b) = N a / N b := map_div₀ N a b

theorem inv (a : K) : N a⁻¹ = (N a)⁻¹ := map_inv₀ N a

end AbsNorm

/-- `[q₁,q₂] = q₁ + 1/q₂`, the length-two continued fraction.  (Paper: §3.) -/
noncomputable def cf {K : Type*} [Field K] (q1 q2 : K) : K := q1 + q2⁻¹

scoped notation "[" q₁ ", " q₂ "]" => cf q₁ q₂

section Chain

variable [Field K]

/-- A **2-stage decreasing chain** for the pair `(α,β)`, with all quotients and
remainders in the subring `𝒪`:

  `α = q₁β + r₁`,  `β = q₂r₁ + r₂`,  `|Nm r₂| < |Nm β|`.

Setting `q₂` to a unit of `𝒪` recovers a 1-stage chain (paper, proof of 3.1). -/
def HasTwoStageChain (𝒪 : Subring K) (N : AbsNorm K) (α β : K) : Prop :=
  ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, ∃ r1 ∈ 𝒪, ∃ r2 ∈ 𝒪,
    α = q1 * β + r1 ∧ β = q2 * r1 + r2 ∧ N r2 < N β

/-- A **1-stage decreasing chain** for `(α,β)`: `α = q₁β + r₁` with
`|Nm r₁| < |Nm β|`. -/
def HasOneStageChain (𝒪 : Subring K) (N : AbsNorm K) (α β : K) : Prop :=
  ∃ q1 ∈ 𝒪, ∃ r1 ∈ 𝒪, α = q1 * β + r1 ∧ N r1 < N β

/-- The field is **2-stage Euclidean**: every pair `α, β ∈ 𝒪` with `β ≠ 0` has a
2-stage decreasing chain.  (Paper: §1.) -/
def IsTwoStageEuclidean (𝒪 : Subring K) (N : AbsNorm K) : Prop :=
  ∀ α ∈ 𝒪, ∀ β ∈ 𝒪, β ≠ 0 → HasTwoStageChain 𝒪 N α β

end Chain

/-! ## The geometric side -/

/-- The model space `ℝ × ℂ`, written as `ℝ³` through real and imaginary parts.
The first coordinate is the real embedding `σ₁`, the last two are the real and
imaginary parts of the complex embedding `σ₂`. -/
abbrev Pt := Fin 3 → ℝ

/-- The extended norm `Nm(u,w) = u|w|²` on `ℝ × ℂ`. -/
def normR (x : Pt) : ℝ := x 0 * (x 1 ^ 2 + x 2 ^ 2)

theorem continuous_normR : Continuous normR := by
  unfold normR
  fun_prop

theorem normR_sub (x c : Pt) :
    normR (x - c) = (x 0 - c 0) * ((x 1 - c 1) ^ 2 + (x 2 - c 2) ^ 2) := rfl

/-- The open region `V(c,ρ) = {x : |Nm(x - c)| < ρ}` with centre `c` and radius
`ρ = 1/|Nm(q₂)|`.  (Paper: §3.) -/
def V (c : Pt) (ρ : ℝ) : Set Pt := {x | |normR (x - c)| < ρ}

/-- `V(q)` for a centre `σ(q)` and denominator norm `n = |Nm q₂|`. -/
def Vq (σq : Pt) (n : ℚ≥0) : Set Pt := V σq ((n : ℝ))⁻¹

/-- A set `S` is covered by a family of regions indexed by `ι`. -/
def CoveredBy {ι : Type*} (S : Set Pt) (F : ι → Set Pt) : Prop := S ⊆ ⋃ i, F i

/-- The closed fundamental domain `D̄` of `𝒪` in the model space, in lattice
coordinates: the closed unit cube. -/
def unitCube : Set Pt := Set.Icc 0 1

theorem isCompact_unitCube : IsCompact (unitCube : Set Pt) := isCompact_Icc

theorem volume_unitCube : MeasureTheory.volume (unitCube : Set Pt) = 1 := by
  show MeasureTheory.volume (Set.Icc (0 : Pt) 1) = 1
  rw [Real.volume_Icc_pi]
  simp

end CubicTwoStage
