/-
# Annihilator of a subgroup of the standard torus

An elementary proof of the rank input in Berend's Proposition 4.3: if the
character annihilator of `H` has finite index in the integer character group,
then `H` is contained in a finite product of coordinate torsion sets.  Hence
an infinite subgroup has annihilator of infinite index.  No classification of
closed torus subgroups is needed.
-/
import Mathlib.Analysis.Fourier.AddCircleMulti

noncomputable section

open Set Filter Topology

namespace CubicTwoStage
namespace BerendProp43Annihilator

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Integer characters vanishing on a subgroup `H` of the standard torus. -/
def characterAnnihilator (H : AddSubgroup (UnitAddTorus d)) :
    AddSubgroup (d → ℤ) where
  carrier := {γ | ∀ x : UnitAddTorus d, x ∈ H → UnitAddTorus.mFourier γ x = 1}
  zero_mem' := by
    intro x hx
    simp [UnitAddTorus.mFourier_zero]
  add_mem' := by
    intro γ δ hγ hδ x hx
    rw [UnitAddTorus.mFourier_add, hγ x hx, hδ x hx, mul_one]
  neg_mem' := by
    intro γ hγ x hx
    rw [UnitAddTorus.mFourier_neg, hγ x hx]
    simp

/-- Multiplicativity of Fourier characters in the integer coefficient. -/
theorem mFourier_nsmul_apply (n : ℕ) (γ : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier (n • γ) x = (UnitAddTorus.mFourier γ x) ^ n := by
  induction n with
  | zero => simp [UnitAddTorus.mFourier_zero]
  | succ n ih => rw [succ_nsmul, UnitAddTorus.mFourier_add, ih, pow_succ]

/-- If a positive multiple of a coordinate character annihilates `H`, then the
corresponding coordinate on `H` lies in the finite `n`-torsion set. -/
theorem nsmul_coordinate_eq_zero (H : AddSubgroup (UnitAddTorus d))
    {n : ℕ} {i : d} (hn : n • (Pi.single i (1 : ℤ)) ∈ characterAnnihilator H)
    {x : UnitAddTorus d} (hx : x ∈ H) : n • x i = 0 := by
  have hone : UnitAddTorus.mFourier (n • (Pi.single i (1 : ℤ))) x = 1 := hn x hx
  rw [mFourier_nsmul_apply, UnitAddTorus.mFourier_single, fourier_one,
    ← Circle.coe_pow, ← AddCircle.toCircle_nsmul] at hone
  have hc : (n • x i).toCircle = 1 := by
    apply Subtype.ext
    exact hone
  apply AddCircle.injective_toCircle one_ne_zero
  simpa using hc

/-- The set of torus points killed in each coordinate by a prescribed positive
integer is finite. -/
theorem finite_coordinateTorsion (n : d → ℕ) (hn : ∀ i, 0 < n i) :
    {x : UnitAddTorus d | ∀ i, n i • x i = 0}.Finite := by
  refine (Set.Finite.pi (fun i => AddCircle.finite_torsion (1 : ℝ) (hn i))).subset ?_
  intro x hx i hi
  exact hx i

/-- Every element in a finite quotient is killed by its positive additive
order.  In particular, a finite-index annihilator contains a positive multiple
of each standard coordinate character. -/
theorem exists_coordinate_nsmul_mem_of_finite_quotient
    (A : AddSubgroup (d → ℤ)) [Finite ((d → ℤ) ⧸ A)] (i : d) :
    ∃ n : ℕ, 0 < n ∧ n • (Pi.single i (1 : ℤ)) ∈ A := by
  let q : (d → ℤ) ⧸ A := QuotientAddGroup.mk' A (Pi.single i (1 : ℤ))
  refine ⟨addOrderOf q, addOrderOf_pos q, ?_⟩
  rw [← QuotientAddGroup.eq_zero_iff]
  change (QuotientAddGroup.mk' A)
    (addOrderOf q • (Pi.single i (1 : ℤ) : d → ℤ)) = 0
  rw [map_nsmul]
  change addOrderOf q • q = 0
  exact addOrderOf_nsmul_eq_zero q

/-- **Finite-index annihilator implies finite subgroup.** -/
theorem finite_carrier_of_finite_quotient (H : AddSubgroup (UnitAddTorus d))
    [Finite ((d → ℤ) ⧸ characterAnnihilator H)] : (H : Set (UnitAddTorus d)).Finite := by
  classical
  have hex : ∀ i : d, ∃ n : ℕ, 0 < n ∧
      n • (Pi.single i (1 : ℤ)) ∈ characterAnnihilator H :=
    fun i => exists_coordinate_nsmul_mem_of_finite_quotient (characterAnnihilator H) i
  choose n hn hnmem using hex
  apply (finite_coordinateTorsion n hn).subset
  intro x hx i
  exact nsmul_coordinate_eq_zero H (hnmem i) hx

/-- In type-theoretic form, `H` is a finite type whenever its character
annihilator has finite quotient. -/
theorem finite_of_finite_quotient (H : AddSubgroup (UnitAddTorus d))
    [Finite ((d → ℤ) ⧸ characterAnnihilator H)] : Finite H := by
  apply Set.finite_coe_iff.mpr
  exact finite_carrier_of_finite_quotient H

/-- **The annihilator rank input, contrapositive form.**  An infinite subgroup
of the standard torus cannot have a finite-index character annihilator. -/
theorem not_finite_quotient_of_infinite (H : AddSubgroup (UnitAddTorus d))
    (hH : (H : Set (UnitAddTorus d)).Infinite) :
    ¬ Finite ((d → ℤ) ⧸ characterAnnihilator H) := by
  intro hfin
  letI := hfin
  exact hH (finite_carrier_of_finite_quotient H)

end BerendProp43Annihilator
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Annihilator.mFourier_nsmul_apply
#print axioms CubicTwoStage.BerendProp43Annihilator.nsmul_coordinate_eq_zero
#print axioms CubicTwoStage.BerendProp43Annihilator.finite_coordinateTorsion
#print axioms CubicTwoStage.BerendProp43Annihilator.exists_coordinate_nsmul_mem_of_finite_quotient
#print axioms CubicTwoStage.BerendProp43Annihilator.finite_carrier_of_finite_quotient
#print axioms CubicTwoStage.BerendProp43Annihilator.finite_of_finite_quotient
#print axioms CubicTwoStage.BerendProp43Annihilator.not_finite_quotient_of_infinite
