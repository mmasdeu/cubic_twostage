/-
# The finite-coloring step of Berend's Proposition 4.3

This module turns a finite cover of the positive integers into a
monochromatic arithmetic progression of prescribed length, with positive
initial term and positive common difference.  The shift by one common
difference is necessary because the general Hales--Jewett corollary allows an
arithmetic progression to start at zero.
-/
import CubicTwoStage.BerendVanDerWaerden

open Set

namespace CubicTwoStage
namespace BerendProp43Coloring

/-- A coloring of the positive integers by the sets `N i` has a progression of
any prescribed finite length in one color, with positive start and difference. -/
theorem exists_arithmeticProgression_mem_of_coloring {κ : Type*} [Finite κ]
    (N : κ → Set ℕ) (C : ℕ → κ) (hC : ∀ m, 0 < m → m ∈ N (C m)) (r : ℕ) :
    ∃ (i : κ) (a d : ℕ), 0 < a ∧ 0 < d ∧ ∀ j < r, a + j * d ∈ N i := by
  obtain ⟨d, hd, a, c, h⟩ := BerendVanDerWaerden.exists_arithmeticProgression C (r + 1)
  refine ⟨c, a + d, d, by omega, hd, ?_⟩
  intro j hj
  have hm : 0 < a + (j + 1) * d := by
    have hmul : 0 < (j + 1) * d := Nat.mul_pos (by omega) hd
    omega
  have hmem := hC (a + (j + 1) * d) hm
  rw [h (j + 1) (by omega)] at hmem
  have heq : a + d + j * d = a + (j + 1) * d := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rwa [heq]

/-- **Berend's finite-character coloring step.**  Any finite cover of the
positive integers contains a set with an arithmetic progression of prescribed
length, whose initial term and common difference are positive. -/
theorem exists_arithmeticProgression_mem_of_finite_cover {κ : Type*} [Finite κ]
    (N : κ → Set ℕ) (hcover : ∀ m, 0 < m → ∃ i, m ∈ N i) (r : ℕ) :
    ∃ (i : κ) (a d : ℕ), 0 < a ∧ 0 < d ∧ ∀ j < r, a + j * d ∈ N i := by
  classical
  let i₀ : κ := (hcover 1 (by omega)).choose
  let C : ℕ → κ := fun m => if hm : 0 < m then (hcover m hm).choose else i₀
  have hC : ∀ m, 0 < m → m ∈ N (C m) := by
    intro m hm
    dsimp [C]
    rw [dif_pos hm]
    exact (hcover m hm).choose_spec
  exact exists_arithmeticProgression_mem_of_coloring N C hC r

end BerendProp43Coloring
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Coloring.exists_arithmeticProgression_mem_of_coloring
#print axioms CubicTwoStage.BerendProp43Coloring.exists_arithmeticProgression_mem_of_finite_cover
