import CubicTwoStage.BerendProp43Bridge
import CubicTwoStage.BerendLatticeDensity
import CubicTwoStage.BerendProp43Rank
import CubicTwoStage.BerendProp43RationalSpan

noncomputable section

open Set Filter Topology Module

namespace CubicTwoStage
namespace BerendProp43Canonical
namespace CanonicalProp43

open BerendLatticeDensity

section Definitions

variable {L : AddSubgroup Pt}

/-- Characters of the project torus which annihilate `H`. -/
def latticeCharacterAnnihilator (H : AddSubgroup (Torus L)) :
    AddSubgroup (latticeCharacters L) where
  carrier := {χ | ∀ h ∈ H, characterOf χ h = 0}
  zero_mem' := by
    intro h hh
    change characterHom 0 h = 0
    simp
  add_mem' := by
    intro χ ψ hχ hψ h hh
    change characterHom (χ + ψ) h = 0
    rw [map_add]
    change characterOf χ h + characterOf ψ h = 0
    rw [hχ h hh, hψ h hh, add_zero]
  neg_mem' := by
    intro χ hχ h hh
    change characterHom (-χ) h = 0
    rw [map_neg]
    change -characterOf χ h = 0
    rw [hχ h hh, neg_zero]

@[simp] theorem mem_latticeCharacterAnnihilator {H : AddSubgroup (Torus L)}
    {χ : latticeCharacters L} :
    χ ∈ latticeCharacterAnnihilator H ↔ ∀ h ∈ H, characterOf χ h = 0 := Iff.rfl

/-- A positive multiple in a finite quotient annihilates its representative. -/
theorem exists_nsmul_mem_of_finite_quotient {M : Type*} [AddCommGroup M]
    (A : AddSubgroup M) [Finite (M ⧸ A)] (x : M) :
    ∃ n : ℕ, 0 < n ∧ n • x ∈ A := by
  let q : M ⧸ A := QuotientAddGroup.mk' A x
  refine ⟨addOrderOf q, addOrderOf_pos q, ?_⟩
  rw [← QuotientAddGroup.eq_zero_iff]
  change (QuotientAddGroup.mk' A) (addOrderOf q • x) = 0
  rw [map_nsmul]
  exact addOrderOf_nsmul_eq_zero q

end Definitions

section BasisCoordinates

variable {L : AddSubgroup Pt}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
variable {ι : Type*} [Fintype ι]
variable (b : Basis ι ℤ (AddSubgroup.toIntSubmodule L))

include b

/-- The standard torus coordinates supplied by a lattice dual basis. -/
noncomputable def standardCoordinates (z : Torus L) : UnitAddTorus ι :=
  fun i => characterOf (coordCharacter b i) z

@[simp] theorem standardCoordinates_apply (z : Torus L) (i : ι) :
    standardCoordinates b z i = characterOf (coordCharacter b i) z := rfl

@[simp] theorem standardCoordinates_mk' (x : Pt) (i : ι) :
    standardCoordinates b ((QuotientAddGroup.mk' L) x) i =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        ((coordCharacter b i).1 x) := by
  exact characterOf_mk' _ _

/-- Dual-basis coordinates are injective on the project torus. -/
theorem standardCoordinates_injective : Function.Injective (standardCoordinates b) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply mem_lattice_of_forall_coord_int b
  intro i
  have hi := congrFun hxy i
  change characterOf (coordCharacter b i) ((QuotientAddGroup.mk' L) x) =
    characterOf (coordCharacter b i) ((QuotientAddGroup.mk' L) y) at hi
  rw [characterOf_mk', characterOf_mk'] at hi
  have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hi
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  change (coordCharacter b i).1 (x - y) = (m : ℝ)
  rw [map_sub, ← hm, Int.smul_one_eq_cast]

@[simp] theorem standardCoordinates_nsmul_character (n : ℕ) (i : ι) (z : Torus L) :
    characterOf (n • coordCharacter b i) z = n • standardCoordinates b z i := by
  change characterHom (n • coordCharacter b i) z = n • standardCoordinates b z i
  rw [map_nsmul]
  rfl

/-- Finite index of the canonical character annihilator forces finiteness of
its subgroup, via a finite product of coordinate-torsion sets. -/
theorem finite_carrier_of_finite_quotient [DecidableEq ι]
    (H : AddSubgroup (Torus L))
    [Finite ((latticeCharacters L) ⧸ latticeCharacterAnnihilator H)] :
    (H : Set (Torus L)).Finite := by
  choose n hn hnmem using fun i =>
    exists_nsmul_mem_of_finite_quotient (latticeCharacterAnnihilator H) (coordCharacter b i)
  apply Set.Finite.of_finite_image (f := standardCoordinates b) ?_
    (standardCoordinates_injective b).injOn
  apply (BerendProp43Annihilator.finite_coordinateTorsion n hn).subset
  rintro _ ⟨h, hh, rfl⟩
  intro i
  have hz := hnmem i h hh
  rw [standardCoordinates_nsmul_character] at hz
  exact hz

theorem not_finite_quotient_of_infinite [DecidableEq ι]
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite) :
    ¬ Finite ((latticeCharacters L) ⧸ latticeCharacterAnnihilator H) := by
  intro hfin
  letI := hfin
  exact hH (finite_carrier_of_finite_quotient b H)

end BasisCoordinates

section CanonicalRank

variable {L : AddSubgroup Pt}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

local instance : Module.Free ℤ (latticeCharacters L) :=
  Module.Free.of_equiv (latticeCharacterDualEquiv (L := L)).symm

local instance : Module.Finite ℤ (latticeCharacters L) :=
  Module.Finite.equiv (latticeCharacterDualEquiv (L := L)).symm

/-- The integer character group of the project 3-torus has rank three. -/
theorem finrank_latticeCharacters : Module.finrank ℤ (latticeCharacters L) = 3 := by
  calc
    Module.finrank ℤ (latticeCharacters L) =
        Module.finrank ℤ (Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) :=
      (latticeCharacterDualEquiv (L := L)).finrank_eq
    _ = Module.finrank ℤ (AddSubgroup.toIntSubmodule L) := by
      let b := Module.Free.chooseBasis ℤ (AddSubgroup.toIntSubmodule L)
      letI : Fintype (Module.Free.ChooseBasisIndex ℤ (AddSubgroup.toIntSubmodule L)) :=
        Module.Free.ChooseBasisIndex.fintype ℤ (AddSubgroup.toIntSubmodule L)
      rw [Module.finrank_eq_card_basis b.dualBasis, Module.finrank_eq_card_basis b]
    _ = 3 := by
      rw [ZLattice.rank ℝ (AddSubgroup.toIntSubmodule L)]
      simp

/-- The annihilator of an infinite subgroup has rank strictly below three. -/
theorem finrank_latticeCharacterAnnihilator_lt
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite) :
    Module.finrank ℤ (latticeCharacterAnnihilator H) < 3 := by
  have hr := BerendProp43Rank.finrank_lt_of_not_finite_quotient
    (latticeCharacterAnnihilator H)
    (not_finite_quotient_of_infinite (latticeDualBasis (L := L)) H hH)
  rwa [finrank_latticeCharacters] at hr

/-- Values of a lattice character on the rational span are rational. -/
theorem exists_rat_apply_of_mem_ratSpan (χ : latticeCharacters L) {x : Pt}
    (hx : x ∈ ratSpan (AddSubgroup.toIntSubmodule L)) : ∃ q : ℚ, χ.1 x = q := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨z, hz⟩ := χ.property y hy
      exact ⟨(z : ℚ), by simpa using hz⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [ha, hb]⟩
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ := ih
      exact ⟨a * b, by simp [map_smul, hb, Rat.smul_def]⟩

/-- The rational value of a lattice character on the rational span. -/
noncomputable def ratifyValue (χ : latticeCharacters L)
    (x : ratSpan (AddSubgroup.toIntSubmodule L)) : ℚ :=
  (exists_rat_apply_of_mem_ratSpan χ x.property).choose

@[simp] theorem ratifyValue_spec (χ : latticeCharacters L)
    (x : ratSpan (AddSubgroup.toIntSubmodule L)) :
    χ.1 x = (ratifyValue χ x : ℝ) :=
  (exists_rat_apply_of_mem_ratSpan χ x.property).choose_spec

/-- Rationalize a lattice character as a covector on the rational span. -/
noncomputable def ratify (χ : latticeCharacters L) :
    Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L)) where
  toFun := ratifyValue χ
  map_add' := by
    intro x y
    apply Rat.cast_injective (α := ℝ)
    rw [← ratifyValue_spec χ (x + y), Rat.cast_add]
    change χ.1 ((x : Pt) + (y : Pt)) = _
    rw [map_add, ratifyValue_spec χ x, ratifyValue_spec χ y]
  map_smul' := by
    intro q x
    apply Rat.cast_injective (α := ℝ)
    rw [← ratifyValue_spec χ (q • x)]
    simp only [RingHom.id_apply, Rat.smul_def, Rat.cast_mul]
    change χ.1 (q • (x : Pt)) = ((q : ℝ) * (ratifyValue χ x : ℝ))
    rw [← Rat.cast_smul_eq_qsmul ℝ q (x : Pt), map_smul, smul_eq_mul, ratifyValue_spec χ x]

@[simp] theorem ratify_value (χ : latticeCharacters L)
    (x : ratSpan (AddSubgroup.toIntSubmodule L)) :
    χ.1 x = (ratify χ x : ℝ) :=
  ratifyValue_spec χ x

/-- Rationalization as an integer-linear map. -/
noncomputable def ratifyLinear :
    (latticeCharacters L) →ₗ[ℤ]
      Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L)) :=
  ({ toFun := ratify
     map_zero' := by
       apply LinearMap.ext
       intro x
       apply Rat.cast_injective (α := ℝ)
       rw [← ratify_value]
       simp
     map_add' := by
       intro χ ψ
       apply LinearMap.ext
       intro x
       apply Rat.cast_injective (α := ℝ)
       rw [← ratify_value (χ + ψ) x, LinearMap.add_apply, Rat.cast_add,
         ← ratify_value χ x, ← ratify_value ψ x]
       rfl } : (latticeCharacters L) →+
      Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L))).toIntLinearMap

@[simp] theorem ratifyLinear_apply (χ : latticeCharacters L) :
    ratifyLinear χ = ratify χ := rfl

/-- Rationalization is injective on lattice characters. -/
theorem ratifyLinear_injective : Function.Injective (ratifyLinear (L := L)) := by
  intro χ ψ h
  apply Subtype.ext
  apply (latticeRealBasis (L := L)).ext
  intro i
  let x : ratSpan (AddSubgroup.toIntSubmodule L) :=
    ⟨((latticeDualBasis (L := L) i : AddSubgroup.toIntSubmodule L) : Pt),
      Submodule.subset_span (latticeDualBasis (L := L) i).property⟩
  have hreal := congrArg (fun q : ℚ => (q : ℝ))
    (congrArg (fun q : Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L)) => q x) h)
  change (ratify χ x : ℝ) = (ratify ψ x : ℝ) at hreal
  rw [← ratify_value, ← ratify_value] at hreal
  rw [latticeRealBasis_apply]
  exact hreal

/-- The rational span of the image of the character annihilator. -/
noncomputable def rationalAnnihilator (H : AddSubgroup (Torus L)) :
    AddSubgroup (Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L))) :=
  (latticeCharacterAnnihilator H).map ratifyLinear.toAddMonoidHom

noncomputable def rationalAnnihilatorSpan (H : AddSubgroup (Torus L)) :
    Submodule ℚ (Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L))) :=
  BerendProp43RationalSpan.ratSpan (rationalAnnihilator H)

/-- The rationalized annihilator has dimension strictly below the ambient
rational character space. -/
theorem finrank_rationalAnnihilatorSpan_lt
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite) :
    Module.finrank ℚ (rationalAnnihilatorSpan H) < 3 := by
  letI : Module.Free ℤ (latticeCharacterAnnihilator H) := by
    change Module.Free ℤ (latticeCharacterAnnihilator H).toIntSubmodule
    infer_instance
  letI : Module.Finite ℤ (latticeCharacterAnnihilator H) := by
    change Module.Finite ℤ (latticeCharacterAnnihilator H).toIntSubmodule
    infer_instance
  let e := (latticeCharacterAnnihilator H).equivMapOfInjective
    ratifyLinear.toAddMonoidHom ratifyLinear_injective
  letI : Module.Free ℤ (rationalAnnihilator H) :=
    Module.Free.of_equiv e.toIntLinearEquiv
  letI : Module.Finite ℤ (rationalAnnihilator H) :=
    Module.Finite.equiv e.toIntLinearEquiv
  rw [rationalAnnihilatorSpan, BerendProp43RationalSpan.finrank_ratSpan]
  calc
    Module.finrank ℤ (rationalAnnihilator H) =
        Module.finrank ℤ (latticeCharacterAnnihilator H) := e.toIntLinearEquiv.finrank_eq.symm
    _ < 3 := finrank_latticeCharacterAnnihilator_lt H hH

/-- The ambient rational character space also has dimension three. -/
theorem finrank_dual_ratSpan :
    Module.finrank ℚ (Module.Dual ℚ (ratSpan (AddSubgroup.toIntSubmodule L))) = 3 := by
  rw [Subspace.dual_finrank_eq, finrank_ratSpan_eq_three]

end CanonicalRank

section CanonicalEquivariance

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- Rationalization identifies canonical precomposition with the dual rational
lattice action. -/
theorem ratifyLinear_dualCharacterAct
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) :
    ratifyLinear (dualCharacterAct D i χ) =
      (ratAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt)
        (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)).dualMap (ratifyLinear χ) := by
  apply LinearMap.ext
  intro x
  apply Rat.cast_injective (α := ℝ)
  change (ratify (dualCharacterAct D i χ) x : ℝ) =
    ((ratify χ) ((ratAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt)
      (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)) x) : ℝ)
  rw [← ratify_value, ← ratify_value]
  rfl

/-- The rational action is surjective: it is injective on a finite-dimensional
rational vector space. -/
theorem surjective_ratAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Function.Surjective (ratAct (AddSubgroup.toIntSubmodule L)
      (D.linFam i : Pt →ₗ[ℝ] Pt)
      (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)) := by
  apply LinearMap.surjective_of_injective
  intro x y hxy
  apply Subtype.ext
  apply (D.linFam i).injective
  exact congrArg Subtype.val hxy

end CanonicalEquivariance

end CanonicalProp43
end BerendProp43Canonical
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.standardCoordinates_injective
#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.finite_carrier_of_finite_quotient
#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.not_finite_quotient_of_infinite
