/-
# Rational span versus integer finrank

For an additive subgroup of a rational vector space, the dimension of its
rational span is exactly its integer finrank.  The proof casts a chosen
integral basis and uses `LinearIndependent.iff_fractionRing`; spanning follows
from the basis representation and closure under integer scalar multiples.
-/
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.IndexNSmul

noncomputable section

open Module Set

namespace CubicTwoStage
namespace BerendProp43RationalSpan

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- Inclusion of an additive subgroup into the ambient rational vector space,
with the canonical integer-module structure on the subtype. -/
def incl (A : AddSubgroup U) : A →ₗ[ℤ] U :=
  AddMonoidHom.toIntLinearMap A.subtype

theorem incl_injective (A : AddSubgroup U) : Function.Injective (incl A) := by
  intro x y h
  exact Subtype.ext h

/-- Rational span of an additive subgroup. -/
def ratSpan (A : AddSubgroup U) : Submodule ℚ U :=
  Submodule.span ℚ (Set.range (incl A))

/-- **Integer finrank equals rational dimension of the span.** -/
theorem finrank_ratSpan (A : AddSubgroup U) [Module.Free ℤ A] [Module.Finite ℤ A] :
    finrank ℚ (ratSpan A) = finrank ℤ A := by
  classical
  let b := Module.Free.chooseBasis ℤ A
  have hliZ : LinearIndependent ℤ (fun i => incl A (b i)) := by
    have hb := b.linearIndependent.map' (incl A)
      (LinearMap.ker_eq_bot.mpr (incl_injective A))
    simpa [Function.comp_def] using hb
  have hliQ : LinearIndependent ℚ (fun i => incl A (b i)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ (Set.range (fun i => incl A (b i))) = ratSpan A := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, rfl⟩
    · rw [ratSpan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      apply Submodule.sum_mem
      intro i hi
      rw [map_smul]
      exact (Submodule.span ℚ
        (Set.range (fun i => incl A (b i)))).toAddSubgroup.zsmul_mem
        (Submodule.subset_span ⟨i, rfl⟩) _
  rw [← hspan, finrank_span_eq_card hliQ]
  exact (Module.finrank_eq_card_basis b).symm

end BerendProp43RationalSpan
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43RationalSpan.incl_injective
#print axioms CubicTwoStage.BerendProp43RationalSpan.finrank_ratSpan
