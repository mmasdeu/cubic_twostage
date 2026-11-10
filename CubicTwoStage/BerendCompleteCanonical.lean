/-
# Completed canonical Theorem 3.6

The Stage-I and coprime-Proposition-IV.1 inputs used here are both proved.
The arithmetic uses a genuine rational prime `p`, as required by the coprime
argument, rather than treating a composite absolute norm as prime.
-/
import CubicTwoStage.BerendCompleteDichotomy
import CubicTwoStage.BerendAssemblyCapstone

open scoped TensorProduct

namespace CubicTwoStage
namespace NumberFieldCubic

variable (K : Type*) [Field K] [NumberField K]

set_option linter.style.haveILetI false

/-- **Theorem 3.6 for the canonical complex cubic model, with the corrected
Berend proposition constructed from Stage I and Proposition IV.1.** -/
theorem thm_uncovered_canonical (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (m : ℕ)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : numberFieldO K), ∃ k : ℕ, ∃ hh ∈ numberFieldO K,
      (1 + π ^ m * ((g : numberFieldO K) : K)) - ((ε : numberFieldO K) : K) ^ k =
        π ^ (m + j) * hh)
    (B1 : ∃ i : Units (numberFieldO K) × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly (
        (((canonicalFieldModel K h).toModel ε π hπO hπ0).lact i) ^ n)))
    (p : ℕ) (hp : p.Prime) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : Units (numberFieldO K) × ℕ → ℂ), x ≠ 0 →
      (∀ i : Units (numberFieldO K) × ℕ,
        LinearMap.baseChange ℂ
          (((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt) x =
            μ i • x) →
      ∃ i : Units (numberFieldO K) × ℕ, 1 < ‖μ i‖) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered (numberFieldO K) (numberFieldAbsNorm K)
      (canonicalFieldModel K h).σ, ∃ c ∈ F,
        (∃ y : K, c = (canonicalFieldModel K h).σ y) ∧
          x - c ∈ (canonicalFieldModel K h).lattice := by
  obtain ⟨q, hpq, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hpqne : p ≠ q := by omega
  obtain ⟨u, j, _hj, h4, h16⟩ :=
    BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
      (canonicalFieldModel K h) ε π hπO hπ0 hεpow p
      (by exact_mod_cast hp.one_lt) hπN
  exact BerendAssembly.thm_uncovered_canonical_of_stageI
    h ε π m hπO hπ0 hεpow hpadic p hπN B1 B2 q hq hp hpqne (u, j) h4 h16
      (BerendStageIAssembly.zeroNonisolatedFull_canonical
        h ε π hπO hπ0 hεpow p hp hπN)

end NumberFieldCubic
end CubicTwoStage

#print axioms CubicTwoStage.NumberFieldCubic.thm_uncovered_canonical
