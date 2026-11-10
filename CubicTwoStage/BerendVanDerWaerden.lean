/-
# The arithmetic-progression input of Berend's Proposition 4.3

Berend colors positive integers by the members of a finite set of characters
whose successive powers annihilate an infinite closed subgroup.  His next step
is a monochromatic arithmetic progression of prescribed finite length.

Mathlib's Hales--Jewett development already proves the required generalization
of van der Waerden's theorem as `Combinatorics.exists_mono_homothetic_copy`.
This module records the exact natural-number corollary used in that argument;
it does not construct the character coloring or prove subgroup convergence.
-/
import Mathlib.Combinatorics.HalesJewett

open Set

namespace CubicTwoStage
namespace BerendVanDerWaerden

/-- A finite coloring of a commutative additive monoid contains a
monochromatic homothetic copy of every finite set. -/
theorem exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M)
    [Finite κ] (C : M → κ) :
    ∃ d > 0, ∃ (a : M) (c : κ), ∀ s ∈ S, C (d • s + a) = c :=
  Combinatorics.exists_mono_homothetic_copy S C

/-- **Van der Waerden, progression form.**  Every finite coloring of `ℕ`
contains a monochromatic progression of an arbitrary prescribed finite length,
with positive common difference. -/
theorem exists_arithmeticProgression {κ : Type*} [Finite κ] (C : ℕ → κ) (r : ℕ) :
    ∃ d > 0, ∃ (a : ℕ) (c : κ), ∀ j < r, C (a + j * d) = c := by
  obtain ⟨d, hd, a, c, h⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range r) C
  refine ⟨d, hd, a, c, fun j hj => ?_⟩
  have hj' := h j (Finset.mem_range.mpr hj)
  simpa [Nat.nsmul_eq_mul, mul_comm, add_comm] using hj'

/-- The same statement with the basepoint written as the first term and
iteration by `+ d`. -/
theorem exists_arithmeticProgression_list {κ : Type*} [Finite κ]
    (C : ℕ → κ) (r : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∃ c : κ, ∀ j < r, C (a + j * d) = c := by
  obtain ⟨d, hd, a, c, h⟩ := exists_arithmeticProgression C r
  exact ⟨a, d, hd, c, h⟩

end BerendVanDerWaerden
end CubicTwoStage

#print axioms CubicTwoStage.BerendVanDerWaerden.exists_mono_homothetic_copy
#print axioms CubicTwoStage.BerendVanDerWaerden.exists_arithmeticProgression
#print axioms CubicTwoStage.BerendVanDerWaerden.exists_arithmeticProgression_list
