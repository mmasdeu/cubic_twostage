/-
# Integer rank and rational span of the character annihilator

This file connects the finite-index formulation of Berend's Proposition 4.3
with the finite-dimensional hypothesis used by the polynomial argument.
The main comparison is an equality, not merely an upper bound: the dimension
over `ℚ` of the rational span of an integer subgroup equals its integer
finrank.  A full-rank subgroup has finite quotient by rank-nullity and
finiteness of a finitely generated torsion abelian group.
-/
import CubicTwoStage.BerendProp43Annihilator
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

noncomputable section

open Module Set

namespace CubicTwoStage
namespace BerendProp43Rank

/-- Full integer rank forces finite quotient. -/
theorem finite_quotient_of_finrank_eq {M : Type*} [AddCommGroup M]
    [Module.Finite ℤ M] (A : AddSubgroup M)
    (hr : finrank ℤ A = finrank ℤ M) : Finite (M ⧸ A) := by
  let N := A.toIntSubmodule
  have hn := N.finrank_quotient_add_finrank
  have hN : finrank ℤ N = finrank ℤ M := hr
  have hq0 : finrank ℤ (M ⧸ N) = 0 := by omega
  have ht : Module.IsTorsion ℤ (M ⧸ N) :=
    (Module.finrank_eq_zero_iff_isTorsion).mp hq0
  have hfin : Finite (M ⧸ N) := Module.finite_of_fg_torsion _ ht
  exact hfin

/-- Infinite index forces the integer rank to drop strictly below the ambient
rank. -/
theorem finrank_lt_of_not_finite_quotient {M : Type*} [AddCommGroup M]
    [Module.Finite ℤ M] (A : AddSubgroup M) (hA : ¬ Finite (M ⧸ A)) :
    finrank ℤ A < finrank ℤ M := by
  have hle : finrank ℤ A ≤ finrank ℤ M := A.toIntSubmodule.finrank_le
  have hne : finrank ℤ A ≠ finrank ℤ M := by
    intro heq
    exact hA (finite_quotient_of_finrank_eq A heq)
  omega

variable {d : Type*} [Fintype d]

/-- Pointwise integer-to-rational cast, as a `ℤ`-linear map. -/
def intCastPi : (d → ℤ) →ₗ[ℤ] (d → ℚ) where
  toFun x i := (x i : ℚ)
  map_add' := by
    intro x y
    funext i
    simp
  map_smul' := by
    intro z x
    funext i
    simp [Pi.smul_apply]

@[simp] theorem intCastPi_apply (x : d → ℤ) (i : d) :
    intCastPi x i = (x i : ℚ) := rfl

theorem intCastPi_injective : Function.Injective (intCastPi (d := d)) := by
  intro x y h
  funext i
  have hi := congrFun h i
  exact Int.cast_injective hi

/-- The inclusion of an integer subgroup, with the canonical integer-module
structure on its subtype. -/
def intIncl (A : AddSubgroup (d → ℤ)) : A →ₗ[ℤ] (d → ℤ) :=
  AddMonoidHom.toIntLinearMap A.subtype

/-- The inclusion of an integer subgroup into the rational character space. -/
def ratIncl (A : AddSubgroup (d → ℤ)) : A →ₗ[ℤ] (d → ℚ) :=
  intCastPi.comp (intIncl A)

@[simp] theorem ratIncl_apply (A : AddSubgroup (d → ℤ)) (x : A) (i : d) :
    ratIncl A x i = ((x : d → ℤ) i : ℚ) := rfl

theorem ratIncl_injective (A : AddSubgroup (d → ℤ)) :
    Function.Injective (ratIncl A) := by
  intro x y hxy
  apply Subtype.ext
  apply intCastPi_injective
  exact hxy

/-- The rational span of an integer subgroup of the character lattice. -/
def rationalSpan (A : AddSubgroup (d → ℤ)) : Submodule ℚ (d → ℚ) :=
  Submodule.span ℚ (Set.range (ratIncl A))

/-- The cast of an integral basis is a rational basis of `rationalSpan`. -/
theorem finrank_rationalSpan (A : AddSubgroup (d → ℤ)) :
    finrank ℚ (rationalSpan A) = finrank ℤ A := by
  classical
  letI : Module.Finite ℤ A := by
    change Module.Finite ℤ A.toIntSubmodule
    infer_instance
  letI : Module.Free ℤ A := by
    change Module.Free ℤ A.toIntSubmodule
    infer_instance
  let b := Module.Free.chooseBasis ℤ A
  have hliZ : LinearIndependent ℤ (fun i => ratIncl A (b i)) := by
    have hb := b.linearIndependent.map' (ratIncl A)
      (LinearMap.ker_eq_bot.mpr (ratIncl_injective A))
    simpa [Function.comp_def] using hb
  have hliQ : LinearIndependent ℚ (fun i => ratIncl A (b i)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ
      (Set.range (fun i => ratIncl A (b i))) = rationalSpan A := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, rfl⟩
    · rw [rationalSpan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      apply Submodule.sum_mem
      intro i hi
      rw [map_smul]
      exact (Submodule.span ℚ
        (Set.range (fun i => ratIncl A (b i)))).toAddSubgroup.zsmul_mem
        (Submodule.subset_span ⟨i, rfl⟩) _
  rw [← hspan, finrank_span_eq_card hliQ]
  exact (Module.finrank_eq_card_basis b).symm

/-- The rational span of an infinite-index subgroup has dimension strictly
below the ambient rational dimension. -/
theorem finrank_rationalSpan_lt_of_not_finite_quotient (A : AddSubgroup (d → ℤ))
    (hA : ¬ Finite ((d → ℤ) ⧸ A)) :
    finrank ℚ (rationalSpan A) < finrank ℚ (d → ℚ) := by
  have hr := finrank_lt_of_not_finite_quotient A hA
  rw [Module.finrank_pi, ← Module.finrank_pi ℤ]
  rw [finrank_rationalSpan]
  exact hr

/-- For an infinite closed (indeed, arbitrary) subgroup of the standard torus,
its rational character annihilator has dimension strictly below the ambient
dimension. -/
theorem finrank_rationalSpan_characterAnnihilator_lt
    [DecidableEq d] (H : AddSubgroup (UnitAddTorus d))
    (hH : (H : Set (UnitAddTorus d)).Infinite) :
    finrank ℚ (rationalSpan (BerendProp43Annihilator.characterAnnihilator H)) <
      finrank ℚ (d → ℚ) := by
  apply finrank_rationalSpan_lt_of_not_finite_quotient
  exact BerendProp43Annihilator.not_finite_quotient_of_infinite H hH

end BerendProp43Rank
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Rank.finite_quotient_of_finrank_eq
#print axioms CubicTwoStage.BerendProp43Rank.finrank_lt_of_not_finite_quotient
#print axioms CubicTwoStage.BerendProp43Rank.intCastPi_injective
#print axioms CubicTwoStage.BerendProp43Rank.finrank_rationalSpan
#print axioms CubicTwoStage.BerendProp43Rank.finrank_rationalSpan_lt_of_not_finite_quotient
#print axioms CubicTwoStage.BerendProp43Rank.finrank_rationalSpan_characterAnnihilator_lt
