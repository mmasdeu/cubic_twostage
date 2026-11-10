/-
# Finite-character obstruction in Berend's Proposition 4.3

This file assembles the finite coloring, rank bound, and polynomial
singularity argument at the level of linear algebra over a field.  There is no
assumption of invariance of any subgroup: `W` is just a low-dimensional
subspace of the dual, later to be the rational span of `Ann(H)`.
-/
import CubicTwoStage.BerendProp43Algebra
import CubicTwoStage.BerendProp43Coloring

open Polynomial Module

namespace CubicTwoStage
namespace BerendProp43Finite

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Powers of a surjective endomorphism are surjective. -/
theorem surjective_pow {f : V →ₗ[K] V} (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (f ^ n) := by
  induction n with
  | zero =>
      intro x
      exact ⟨x, by simp⟩
  | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp]
      simpa only [LinearMap.coe_comp] using ih.comp hf

/-- The index calculation turning an arithmetic progression `a + j*d` into
iterates of `f^d` starting from the shifted covector `φ ∘ f^a`. -/
theorem comp_pow_shift (φ : V →ₗ[K] K) (f : V →ₗ[K] V) (a d j : ℕ) :
    (φ.comp (f ^ a)).comp ((f ^ d) ^ j) = φ.comp (f ^ (a + j * d)) := by
  rw [LinearMap.comp_assoc]
  congr 1
  rw [← Module.End.mul_eq_comp, ← pow_mul, ← pow_add, Nat.mul_comm d j]

/-- **Berend's finite-character contradiction.**  Let `f` satisfy the
irreducibility condition for every positive power, and let `W` be a subspace of
the dual of dimension below the ambient dimension.  For no finite collection
of nonzero covectors `γ i` can the covectors `γ i ∘ f^m`, with `i` depending on
`m`, cover all positive integers inside `W`.

This is precisely the algebraic portion of Proposition 4.3 before identifying
`W` with the rational span of the annihilator of the infinite subgroup. -/
theorem not_finite_cover_comp_pow_mem {κ : Type*} [Finite κ]
    (f : V →ₗ[K] V) (hsurj : Function.Surjective f)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (f ^ n)))
    (γ : κ → (V →ₗ[K] K)) (hγ : ∀ i, γ i ≠ 0)
    (W : Submodule K (V →ₗ[K] K))
    (hr : Module.finrank K W < Module.finrank K V)
    (hcover : ∀ m : ℕ, 0 < m → ∃ i, (γ i).comp (f ^ m) ∈ W) : False := by
  let N : κ → Set ℕ := fun i => {m | (γ i).comp (f ^ m) ∈ W}
  obtain ⟨i, a, d, ha, hd, hprog⟩ :=
    BerendProp43Coloring.exists_arithmeticProgression_mem_of_finite_cover N hcover
      (Module.finrank K V)
  let φ : V →ₗ[K] K := (γ i).comp (f ^ a)
  have hφ : φ ≠ 0 := by
    have hex : ∃ x, γ i x ≠ 0 := by
      by_contra h
      apply hγ i
      ext x
      simp only [LinearMap.zero_apply]
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hex
    obtain ⟨y, hy⟩ := surjective_pow hsurj a x
    intro hzero
    have h := LinearMap.congr_fun hzero y
    dsimp [φ] at h
    rw [hy] at h
    exact hx h
  apply BerendProp43Algebra.not_forall_comp_pow_mem_of_finrank_lt
    (f ^ d) (hB1 d hd) hφ W hr
  intro j
  have hmem : (γ i).comp (f ^ (a + (j : ℕ) * d)) ∈ W := by
    exact hprog (j : ℕ) j.isLt
  have hcomp := comp_pow_shift (γ i) f a d (j : ℕ)
  change ((γ i).comp (f ^ a)).comp ((f ^ d) ^ (j : ℕ)) ∈ W
  rw [hcomp]
  exact hmem

end BerendProp43Finite
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Finite.surjective_pow
#print axioms CubicTwoStage.BerendProp43Finite.comp_pow_shift
#print axioms CubicTwoStage.BerendProp43Finite.not_finite_cover_comp_pow_mem
