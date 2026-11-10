/-
# Theorem 3.6 for the canonical complex cubic model, corrected (B3), from `H`

The canonical-model form of the plan's item E.4:
`NumberFieldCubic.thm_uncovered_canonical` with the corrected (B3) — which is
*proved* by `rational_independence_corrected` — and with Berend's theorem
supplied as the explicit proposition `H` instead of the axiom
`berend_multi_invariance`.
-/
import CubicTwoStage.ComplexCubic
import CubicTwoStage.Theorem36Corrected

open scoped TensorProduct

set_option linter.unusedVariables false

namespace CubicTwoStage
namespace NumberFieldCubic

variable (K : Type*) [Field K] [NumberField K]

/-- **Theorem 3.6 for the canonical complex cubic model.**  The full-lattice and
compactness inputs are derived from the number field; only the arithmetic inputs
of the paper remain as hypotheses. -/
theorem thm_uncovered_canonical_corrected (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (m : ℕ)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : numberFieldO K), ∃ k : ℕ, ∃ h ∈ numberFieldO K,
      (1 + π ^ m * ((g : numberFieldO K) : K)) - ((ε : numberFieldO K) : K) ^ k =
        π ^ (m + j) * h)
    (B1 : ∃ i : Units (numberFieldO K) × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly (
        (((canonicalFieldModel K h).toModel ε π hπO hπ0).lact i) ^ n)))
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : Units (numberFieldO K) × ℕ → ℂ), x ≠ 0 →
      (∀ i : Units (numberFieldO K) × ℕ,
        LinearMap.baseChange ℂ
          (((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt) x =
            μ i • x) →
      ∃ i : Units (numberFieldO K) × ℕ, 1 < ‖μ i‖)
    (H : BerendMultiInvarianceCorrected (Units (numberFieldO K) × ℕ)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam
      (canonicalFieldModel K h).lattice
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_preserves
      (isZLattice_canonicalFieldModel_lattice K h) B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp hπN)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_comm) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered (numberFieldO K) (numberFieldAbsNorm K)
      (canonicalFieldModel K h).σ, ∃ c ∈ F,
        (∃ y : K, c = (canonicalFieldModel K h).σ y) ∧
          x - c ∈ (canonicalFieldModel K h).lattice :=
  thm_uncovered_field_corrected (canonicalFieldModel K h) ε π m hπO hπ0 hεpow hpadic
    (isZLattice_canonicalFieldModel_lattice K h) B1 p hp hπN B2 H

end NumberFieldCubic
end CubicTwoStage
