/-
# Algebraic core of Berend's Proposition 4.3

The polynomial input to Proposition 4.3 is isolated here over an arbitrary
field.  Irreducibility of the characteristic polynomial makes every nonzero
polynomial of smaller degree invertible on the underlying finite-dimensional
space.  Dually, the first `finrank` iterates of any nonzero covector are
linearly independent.  This is exactly the contradiction to the rank bound on
`Ann(H)` in Berend's proof.
-/
import CubicTwoStage.BerendAlgebra

open Polynomial Module

namespace CubicTwoStage
namespace BerendProp43Algebra

set_option maxHeartbeats 800000

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A nonzero polynomial of degree below the characteristic degree acts
injectively when the characteristic polynomial is irreducible. -/
theorem injective_aeval_of_irreducible_charpoly [Nontrivial V] (f : V →ₗ[K] V)
    (hirr : Irreducible (LinearMap.charpoly f)) {p : K[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree < (LinearMap.charpoly f).natDegree) :
    Function.Injective (aeval f p) := by
  rw [← LinearMap.ker_eq_bot]
  have hinv : ∀ x ∈ LinearMap.ker (aeval f p),
      f x ∈ LinearMap.ker (aeval f p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    calc
      aeval f p (f x) = (aeval f (p * X)) x := by
        rw [map_mul, aeval_X]
        rfl
      _ = (aeval f (X * p)) x := by rw [mul_comm]
      _ = f (aeval f p x) := by
        rw [map_mul, aeval_X]
        rfl
      _ = 0 := by rw [hx, map_zero]
  rcases submodule_eq_bot_or_top_of_irreducible_charpoly f hirr
      (LinearMap.ker (aeval f p)) hinv with hbot | htop
  · exact hbot
  · exfalso
    have hzero : aeval f p = 0 := by
      ext x
      have hx : x ∈ LinearMap.ker (aeval f p) := by rw [htop]; trivial
      exact LinearMap.mem_ker.mp hx
    have hmin : LinearMap.charpoly f = minpoly K f :=
      minpoly.eq_of_irreducible_of_monic hirr
        (LinearMap.aeval_self_charpoly f) (LinearMap.charpoly_monic f)
    have hdvd : LinearMap.charpoly f ∣ p := by
      rw [hmin]
      exact minpoly.dvd K f hzero
    exact (not_le_of_gt hdeg) (Polynomial.natDegree_le_of_dvd hdvd hp)

/-- If a covector kills a lower-degree polynomial in `f`, then either that
polynomial or the covector is zero. -/
theorem eq_zero_or_eq_zero_of_comp_aeval_eq_zero [Nontrivial V] (f : V →ₗ[K] V)
    (hirr : Irreducible (LinearMap.charpoly f)) {p : K[X]}
    (hdeg : p.natDegree < (LinearMap.charpoly f).natDegree) {φ : V →ₗ[K] K}
    (hcomp : φ.comp (aeval f p) = 0) : p = 0 ∨ φ = 0 := by
  by_cases hp : p = 0
  · exact Or.inl hp
  right
  have hinj := injective_aeval_of_irreducible_charpoly f hirr hp hdeg
  have hsurj := LinearMap.surjective_of_injective hinj
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  have h := LinearMap.congr_fun hcomp y
  simpa using h

/-- The first `finrank` iterates of a nonzero covector under an endomorphism
with irreducible characteristic polynomial are linearly independent. -/
theorem linearIndependent_comp_pow_of_irreducible_charpoly (f : V →ₗ[K] V)
    (hirr : Irreducible (LinearMap.charpoly f)) {φ : V →ₗ[K] K} (hφ : φ ≠ 0) :
    LinearIndependent K
      (fun j : Fin (Module.finrank K V) => φ.comp (f ^ (j : ℕ))) := by
  have hex : ∃ x, φ x ≠ 0 := by
    by_contra h
    apply hφ
    ext x
    simp only [LinearMap.zero_apply]
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  haveI : Nontrivial V := ⟨⟨x, 0, fun h => hx (by rw [h]; simp)⟩⟩
  rw [Fintype.linearIndependent_iff]
  intro c hrel j
  let p : K[X] := ∑ i : Fin (Module.finrank K V), monomial (i : ℕ) (c i)
  have hpdeg_le : p.natDegree ≤ Module.finrank K V - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    dsimp [p]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    have hiN : (i : ℕ) ≠ N := by omega
    simp [Polynomial.coeff_monomial, hiN]
  have hr : 0 < Module.finrank K V := by
    have hj := j.isLt
    omega
  have hpdeg : p.natDegree < (LinearMap.charpoly f).natDegree := by
    rw [LinearMap.charpoly_natDegree]
    omega
  have hcomp : φ.comp (aeval f p) = 0 := by
    have heval : aeval f p = ∑ i : Fin (Module.finrank K V), c i • f ^ (i : ℕ) := by
      dsimp [p]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.aeval_monomial]
      change (algebraMap K (V →ₗ[K] V)) (c i) * f ^ (i : ℕ) = c i • f ^ (i : ℕ)
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [heval]
    ext x
    have h := LinearMap.congr_fun hrel x
    simpa [LinearMap.comp_apply, map_sum] using h
  have hp : p = 0 := (eq_zero_or_eq_zero_of_comp_aeval_eq_zero f hirr hpdeg hcomp).resolve_right hφ
  have hcoeff := congrArg (fun q : K[X] => q.coeff (j : ℕ)) hp
  rw [Polynomial.coeff_zero] at hcoeff
  rw [← hcoeff]
  symm
  dsimp [p]
  rw [Polynomial.finsetSum_coeff]
  classical
  calc
    (∑ b : Fin (Module.finrank K V),
        ((monomial (b : ℕ) (c b)).coeff (j : ℕ))) =
        ((monomial (j : ℕ) (c j)).coeff (j : ℕ)) := by
      apply Fintype.sum_eq_single j
      intro b hbj
      have hne : (b : ℕ) ≠ (j : ℕ) := by
        intro h
        exact hbj (Fin.ext h)
      simp [Polynomial.coeff_monomial, hne]
    _ = c j := by simp

/-- Vectors in a subspace of dimension smaller than their number have a
nontrivial linear relation. -/
theorem exists_relation_of_finrank_lt {r : ℕ} (W : Submodule K V)
    (v : Fin r → V) (hv : ∀ j, v j ∈ W) (hr : Module.finrank K W < r) :
    ∃ c : Fin r → K, (∑ j, c j • v j) = 0 ∧ ∃ j, c j ≠ 0 := by
  rw [← Fintype.not_linearIndependent_iff]
  intro hli
  let w : Fin r → W := fun j => ⟨v j, hv j⟩
  have hliw : LinearIndependent K w := by
    apply LinearIndependent.of_comp W.subtype
    simpa [w, Function.comp_def] using hli
  have hcard := hliw.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **The rank/polynomial contradiction in Berend's Proposition 4.3.**
A subspace of the dual having dimension below the ambient dimension cannot
contain the first `finrank` iterates of a nonzero covector. -/
theorem not_forall_comp_pow_mem_of_finrank_lt (f : V →ₗ[K] V)
    (hirr : Irreducible (LinearMap.charpoly f)) {φ : V →ₗ[K] K} (hφ : φ ≠ 0)
    (W : Submodule K (V →ₗ[K] K))
    (hr : Module.finrank K W < Module.finrank K V)
    (hmem : ∀ j : Fin (Module.finrank K V), φ.comp (f ^ (j : ℕ)) ∈ W) : False := by
  have hli := linearIndependent_comp_pow_of_irreducible_charpoly f hirr hφ
  obtain ⟨c, hsum, j, hcj⟩ := exists_relation_of_finrank_lt W
    (fun j : Fin (Module.finrank K V) => φ.comp (f ^ (j : ℕ))) hmem hr
  have hnli : ¬ LinearIndependent K
      (fun j : Fin (Module.finrank K V) => φ.comp (f ^ (j : ℕ))) :=
    Fintype.not_linearIndependent_iff.mpr ⟨c, hsum, j, hcj⟩
  exact hnli hli

end BerendProp43Algebra
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Algebra.injective_aeval_of_irreducible_charpoly
#print axioms CubicTwoStage.BerendProp43Algebra.eq_zero_or_eq_zero_of_comp_aeval_eq_zero
#print axioms CubicTwoStage.BerendProp43Algebra.linearIndependent_comp_pow_of_irreducible_charpoly
#print axioms CubicTwoStage.BerendProp43Algebra.exists_relation_of_finrank_lt
#print axioms CubicTwoStage.BerendProp43Algebra.not_forall_comp_pow_mem_of_finrank_lt
