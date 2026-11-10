import CubicTwoStage.BerendAlgebra
import CubicTwoStage.BerendCorrected

open Polynomial Module

namespace CubicTwoStage
namespace BerendProp43Canonical

section Dual
variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- The characteristic polynomial is unchanged by dualizing. -/
theorem charpoly_dualMap (f : V →ₗ[K] V) :
    LinearMap.charpoly f.dualMap = LinearMap.charpoly f := by
  classical
  let b := Module.Free.chooseBasis K V
  letI : Fintype (Module.Free.ChooseBasisIndex K V) :=
    Module.Free.ChooseBasisIndex.fintype K V
  calc
    LinearMap.charpoly f.dualMap =
        (LinearMap.toMatrix b.dualBasis b.dualBasis f.dualMap).charpoly :=
      (LinearMap.charpoly_toMatrix f.dualMap b.dualBasis).symm
    _ = (LinearMap.toMatrix b b f).transpose.charpoly := by
      rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
    _ = (LinearMap.toMatrix b b f).charpoly := Matrix.charpoly_transpose _
    _ = LinearMap.charpoly f := LinearMap.charpoly_toMatrix f b

omit [Module.Free K V] [Module.Finite K V] in
/-- Dualizing commutes with natural powers. -/
theorem dualMap_pow (f : V →ₗ[K] V) (n : ℕ) :
    (f ^ n).dualMap = f.dualMap ^ n := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_eq_id] using
      (LinearMap.dualMap_id (R := K) (M₁ := V))
  | succ n ih =>
      rw [pow_succ', pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.dualMap_comp_dualMap, ih]

/-- B1 passes from an endomorphism to its dual. -/
theorem irreducible_charpoly_dualMap_of_b1 (f : V →ₗ[K] V)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (f ^ n))) :
    ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (f.dualMap ^ n)) := by
  intro n hn
  rw [← dualMap_pow, charpoly_dualMap]
  exact hB1 n hn

end Dual

section RationalLattice

variable {K V W : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Conjugation by a linear equivalence commutes with natural powers. -/
theorem conj_pow (e : V ≃ₗ[K] W) (f : V →ₗ[K] V) (n : ℕ) :
    e.conj (f ^ n) = (e.conj f) ^ n := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]
  | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp, ih]

end RationalLattice

section RatAct

variable (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
  (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)

/-- Characteristic polynomials of all powers, transported from the integral
lattice endomorphism to its restriction on the rational span. -/
theorem charpoly_ratAct_pow (n : ℕ) :
    LinearMap.charpoly ((ratAct M f hf) ^ n) =
      (LinearMap.charpoly ((intAct M f hf) ^ n)).map (Int.castRingHom ℚ) := by
  let e := tensorEquivRatSpan M
  let g := (intAct M f hf).baseChange ℚ
  have hpow : e.conj (g ^ n) = (ratAct M f hf) ^ n := by
    rw [conj_pow]
    exact congrArg (· ^ n) (tensorEquivRatSpan_conj M f hf)
  calc
    LinearMap.charpoly ((ratAct M f hf) ^ n) = LinearMap.charpoly (e.conj (g ^ n)) := by
      rw [hpow]
    _ = LinearMap.charpoly (g ^ n) := LinearEquiv.charpoly_conj _ _
    _ = LinearMap.charpoly (((intAct M f hf) ^ n).baseChange ℚ) := by
      rw [LinearMap.baseChange_pow]
    _ = (LinearMap.charpoly ((intAct M f hf) ^ n)).map (Int.castRingHom ℚ) :=
      charpoly_baseChange_rat _

/-- Berend's B1, for every positive power, on the rational-span endomorphism. -/
theorem irreducible_charpoly_ratAct_of_b1
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((intAct M f hf) ^ n))) :
    ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((ratAct M f hf) ^ n)) := by
  intro n hn
  rw [charpoly_ratAct_pow]
  exact (irreducible_map_rat_iff (LinearMap.charpoly_monic _)).2 (hB1 n hn)

/-- B1 on the dual rational-span endomorphism.  This is the endomorphism which
acts on torus characters by precomposition. -/
theorem irreducible_charpoly_dual_ratAct_of_b1
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((intAct M f hf) ^ n))) :
    ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((ratAct M f hf).dualMap ^ n)) :=
  irreducible_charpoly_dualMap_of_b1 _ (irreducible_charpoly_ratAct_of_b1 M f hf hB1)

end RatAct

section UnitPrime

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The canonical unit-prime B1 hypothesis supplies B1 for the dual integral
lattice endomorphism.  Its action on a character is precomposition. -/
theorem UnitPrimeModel.exists_irreducible_charpoly_dual_intLact
    (D : UnitPrimeModel L 𝒪) [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i).dualMap ^ n)) := by
  obtain ⟨i, hi⟩ := B1
  exact ⟨i, irreducible_charpoly_dualMap_of_b1 _ hi⟩

@[simp] theorem dualMap_pow_apply {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] (f : V →ₗ[R] V) (χ : Module.Dual R V) (x : V) (n : ℕ) :
    (f.dualMap ^ n) χ x = χ ((f ^ n) x) := by
  rw [← dualMap_pow]
  rfl

/-- The canonical unit-prime B1 hypothesis supplies B1 for the dual rational
endomorphism used in Berend's characterwise Proposition 4.3. -/
theorem UnitPrimeModel.exists_irreducible_charpoly_dual_ratAct
    (D : UnitPrimeModel L 𝒪) [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((ratAct (AddSubgroup.toIntSubmodule L)
        (D.linFam i : Pt →ₗ[ℝ] Pt)
        (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)).dualMap ^ n)) := by
  obtain ⟨i, hi⟩ := B1
  exact ⟨i, irreducible_charpoly_dual_ratAct_of_b1 _ _ _ hi⟩

end UnitPrime

section TorusCharacters

variable {L : AddSubgroup Pt}

/-- Real-linear functionals which take integral values on the lattice.  They
are precisely the additive-circle characters of the quotient torus, via the
quotient lift below. -/
def latticeCharacters (L : AddSubgroup Pt) : AddSubgroup (Pt →ₗ[ℝ] ℝ) where
  carrier := {χ | ∀ x ∈ L, ∃ z : ℤ, χ x = z}
  zero_mem' := by
    intro x hx
    exact ⟨0, by simp⟩
  add_mem' := by
    intro χ ψ hχ hψ x hx
    obtain ⟨m, hm⟩ := hχ x hx
    obtain ⟨n, hn⟩ := hψ x hx
    exact ⟨m + n, by simp [hm, hn]⟩
  neg_mem' := by
    intro χ hχ x hx
    obtain ⟨m, hm⟩ := hχ x hx
    exact ⟨-m, by simp [hm]⟩

/-- A lattice character induces an additive-circle character of the quotient. -/
noncomputable def characterOf (χ : latticeCharacters L) :
    (Pt ⧸ L) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift L
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp χ.1.toAddMonoidHom)
    (by
      intro x hx
      obtain ⟨z, hz⟩ := χ.property x hx
      change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (χ.1 x) = 0
      rw [hz]
      exact (QuotientAddGroup.eq_zero_iff ((z : ℝ))).2
        (AddSubgroup.intCast_mem_zmultiples_one z))

@[simp] theorem characterOf_mk' (χ : latticeCharacters L) (x : Pt) :
    characterOf χ ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (χ.1 x) := by
  exact QuotientAddGroup.lift_mk' _ _ _

/-- Quotient characters induced by lattice characters are continuous. -/
theorem continuous_characterOf (χ : latticeCharacters L) : Continuous (characterOf χ) := by
  refine (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr ?_
  have h : (characterOf χ : (Pt ⧸ L) → AddCircle (1 : ℝ)) ∘
      (QuotientAddGroup.mk : Pt → Pt ⧸ L) =
      (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) ∘ χ.1 := by
    funext x
    exact characterOf_mk' χ x
  rw [h]
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp χ.1.continuous_of_finiteDimensional

/-- The induced map on characters, packaged additively. -/
noncomputable def characterHom : (latticeCharacters L) →+ ((Pt ⧸ L) →+ AddCircle (1 : ℝ)) where
  toFun := characterOf
  map_zero' := by
    refine AddMonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    change characterOf (0 : latticeCharacters L) ((QuotientAddGroup.mk' L) x) = 0
    rw [characterOf_mk']
    simp
  map_add' := by
    intro χ ψ
    refine AddMonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    change characterOf (χ + ψ) ((QuotientAddGroup.mk' L) x) =
      characterOf χ ((QuotientAddGroup.mk' L) x) + characterOf ψ ((QuotientAddGroup.mk' L) x)
    simp only [characterOf_mk']
    change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (χ.1 x + ψ.1 x) = _
    rw [map_add]

/-- A nonzero lattice functional induces a nontrivial circle character: if the
latter were zero, all values of the functional would be integers, contradicting
surjectivity of a nonzero real-linear functional. -/
theorem characterOf_ne_zero {χ : latticeCharacters L} (hχ : χ ≠ 0) :
    characterOf χ ≠ 0 := by
  intro hzero
  have hχ0 : χ.1 ≠ 0 := by
    intro h
    exact hχ (Subtype.ext h)
  obtain ⟨x, hx⟩ := LinearMap.surjective hχ0 (1 / 2 : ℝ)
  have hz : characterOf χ ((QuotientAddGroup.mk' L) x) = 0 := by
    rw [hzero]
    rfl
  rw [characterOf_mk'] at hz
  change ((χ.1 x : ℝ) : AddCircle (1 : ℝ)) = 0 at hz
  rw [hx] at hz
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (1 / 2 : ℝ))).mp hz
  have hnreal : (n : ℝ) = 1 / 2 := by
    simpa [zsmul_eq_mul] using hn
  have hnint : 2 * n = 1 := by
    have hr : (2 : ℝ) * (n : ℝ) = 1 := by rw [hnreal]; norm_num
    exact_mod_cast hr
  omega

end TorusCharacters

section UnitPrimeCharacters

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- Precomposition with a unit-prime action on the lattice characters. -/
noncomputable def dualCharacterAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (latticeCharacters L) →+ (latticeCharacters L) where
  toFun χ := ⟨χ.1.comp (D.linFam i : Pt →ₗ[ℝ] Pt), by
    intro x hx
    exact χ.property (D.family.act i x) (D.lattice_linFam i hx)⟩
  map_zero' := by
    ext x
    rfl
  map_add' := by
    intro χ ψ
    ext x
    rfl

@[simp] theorem dualCharacterAct_apply
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (x : Pt) :
    (dualCharacterAct D i χ).1 x = χ.1 (D.family.act i x) := rfl

/-- Precomposition on lattice characters is exactly postcomposition of the
induced quotient character with the canonical torus endomorphism. -/
theorem characterOf_dualCharacterAct
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) :
    characterOf (dualCharacterAct D i χ) = (characterOf χ).comp (D.torusEndAct i) := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  change characterOf (dualCharacterAct D i χ) ((QuotientAddGroup.mk' L) x) =
    characterOf χ (D.torusEndAct i ((QuotientAddGroup.mk' L) x))
  rw [D.torusEndAct_mk']
  simp only [characterOf_mk', dualCharacterAct_apply]

/-- The full iterate form of torus/character equivariance. -/
@[simp] theorem characterOf_dualCharacterAct_iterate_apply
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (n : ℕ)
    (z : Pt ⧸ L) :
    characterOf ((dualCharacterAct D i)^[n] χ) z =
      characterOf χ ((D.torusEndAct i)^[n] z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h := congrArg (fun f : (Pt ⧸ L) →+ AddCircle (1 : ℝ) => f z)
        (characterOf_dualCharacterAct D i ((dualCharacterAct D i)^[n] χ))
      calc
        characterOf (dualCharacterAct D i ((dualCharacterAct D i)^[n] χ)) z =
            characterOf ((dualCharacterAct D i)^[n] χ) (D.torusEndAct i z) := h
        _ = characterOf χ ((D.torusEndAct i)^[n] (D.torusEndAct i z)) := ih (D.torusEndAct i z)
        _ = characterOf χ (D.torusEndAct i ((D.torusEndAct i)^[n] z)) := by
          congr 1
          exact (Function.iterate_succ_apply (D.torusEndAct i) n z).symm.trans
            (Function.iterate_succ_apply' (D.torusEndAct i) n z)

/-- The annihilation relation used in Berend's Proposition 4.3.  Only the
action on the points of `H` occurs; `H` itself need not be invariant. -/
theorem dualCharacterAct_iterate_annihilates_iff
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (n : ℕ)
    (H : Set (Pt ⧸ L)) :
    (∀ h ∈ H, characterOf ((dualCharacterAct D i)^[n] χ) h = 0) ↔
      (∀ h ∈ H, characterOf χ ((D.torusEndAct i)^[n] h) = 0) := by
  simp only [characterOf_dualCharacterAct_iterate_apply]

end UnitPrimeCharacters

section LatticeDualEquivalence

variable {L : AddSubgroup Pt}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- The standard integral basis of the full lattice. -/
noncomputable def latticeDualBasis : Basis (Fin 3) ℤ (AddSubgroup.toIntSubmodule L) :=
  IsZLattice.basis (AddSubgroup.toIntSubmodule L)

/-- The same basis, regarded as a real basis of the ambient space. -/
noncomputable def latticeRealBasis : Basis (Fin 3) ℝ Pt :=
  (latticeDualBasis (L := L)).ofZLatticeBasis ℝ (AddSubgroup.toIntSubmodule L)

@[simp] theorem latticeRealBasis_apply (i : Fin 3) :
    latticeRealBasis (L := L) i = ((latticeDualBasis (L := L) i : AddSubgroup.toIntSubmodule L) : Pt) := by
  simp [latticeRealBasis, latticeDualBasis]

/-- The integral value of a lattice character on a lattice point. -/
noncomputable def latticeValue (χ : latticeCharacters L)
    (x : AddSubgroup.toIntSubmodule L) : ℤ :=
  (χ.property x x.property).choose

@[simp] theorem latticeValue_spec (χ : latticeCharacters L)
    (x : AddSubgroup.toIntSubmodule L) :
    χ.1 x = (latticeValue χ x : ℝ) :=
  (χ.property x x.property).choose_spec

/-- Restriction to the lattice, as an additive integer-valued functional. -/
noncomputable def restrictLatticeDualAdd (χ : latticeCharacters L) :
    (AddSubgroup.toIntSubmodule L) →+ ℤ where
  toFun := latticeValue χ
  map_zero' := by
    have h : ((latticeValue χ (0 : AddSubgroup.toIntSubmodule L) : ℤ) : ℝ) = 0 := by
      rw [← latticeValue_spec]
      simp
    exact_mod_cast h
  map_add' := by
    intro x y
    have h : ((latticeValue χ (x + y) : ℤ) : ℝ) =
        ((latticeValue χ x + latticeValue χ y : ℤ) : ℝ) := by
      rw [Int.cast_add, ← latticeValue_spec, ← latticeValue_spec, ← latticeValue_spec]
      simp
    exact_mod_cast h

/-- Restriction to the integral dual of the lattice. -/
noncomputable def restrictLatticeDual (χ : latticeCharacters L) :
    Module.Dual ℤ (AddSubgroup.toIntSubmodule L) :=
  (restrictLatticeDualAdd χ).toIntLinearMap

@[simp] theorem restrictLatticeDual_spec (χ : latticeCharacters L)
    (x : AddSubgroup.toIntSubmodule L) :
    χ.1 x = (restrictLatticeDual χ x : ℝ) :=
  latticeValue_spec χ x

/-- Extension of an integral dual vector to a real-linear functional, using the
lattice basis as a real basis. -/
noncomputable def extendLatticeDual (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) :
    Pt →ₗ[ℝ] ℝ :=
  (latticeRealBasis (L := L)).constr ℝ (fun i => (φ (latticeDualBasis (L := L) i) : ℝ))

@[simp] theorem extendLatticeDual_apply_lattice
    (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L))
    (x : AddSubgroup.toIntSubmodule L) :
    extendLatticeDual φ x = (φ x : ℝ) := by
  let eZ : (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] ℝ :=
    ((extendLatticeDual φ).restrictScalars ℤ).comp (AddSubgroup.toIntSubmodule L).subtype
  let φR : (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] ℝ :=
    { toFun := fun x => (φ x : ℝ)
      map_add' := by intro x y; simp
      map_smul' := by intro z x; simp [Int.cast_smul_eq_zsmul] }
  have heq : eZ = φR := by
    apply (latticeDualBasis (L := L)).ext
    intro i
    dsimp [eZ, φR]
    rw [← latticeRealBasis_apply (L := L) i]
    exact Module.Basis.constr_basis (latticeRealBasis (L := L)) ℝ
      (fun j => (φ (latticeDualBasis (L := L) j) : ℝ)) i
  exact LinearMap.congr_fun heq x

/-- The extension is integral on the whole lattice. -/
theorem extendLatticeDual_mem (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) :
    ∀ x ∈ L, ∃ z : ℤ, extendLatticeDual φ x = z := by
  intro x hx
  let xM : AddSubgroup.toIntSubmodule L := ⟨x, hx⟩
  exact ⟨φ xM, extendLatticeDual_apply_lattice φ xM⟩

/-- Extension as a lattice character. -/
noncomputable def extendLatticeCharacter
    (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) : latticeCharacters L :=
  ⟨extendLatticeDual φ, extendLatticeDual_mem φ⟩

/-- Restriction followed by extension is the identity. -/
theorem extendLatticeDual_restrict (χ : latticeCharacters L) :
    extendLatticeDual (restrictLatticeDual χ) = χ.1 := by
  apply (latticeRealBasis (L := L)).ext
  intro i
  calc
    extendLatticeDual (restrictLatticeDual χ) (latticeRealBasis (L := L) i) =
        (restrictLatticeDual χ (latticeDualBasis (L := L) i) : ℝ) := by
      simpa only [extendLatticeDual] using
        (Module.Basis.constr_basis (latticeRealBasis (L := L)) ℝ
          (fun j => (restrictLatticeDual χ (latticeDualBasis (L := L) j) : ℝ)) i)
    _ = χ.1 ((latticeDualBasis (L := L) i : AddSubgroup.toIntSubmodule L) : Pt) :=
      (restrictLatticeDual_spec χ (latticeDualBasis (L := L) i)).symm
    _ = χ.1 (latticeRealBasis (L := L) i) := by rw [latticeRealBasis_apply]

/-- Extension followed by restriction is the identity. -/
theorem restrictLatticeDual_extend (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) :
    restrictLatticeDual (extendLatticeCharacter φ) = φ := by
  apply LinearMap.ext
  intro x
  have h := restrictLatticeDual_spec (extendLatticeCharacter φ) x
  change extendLatticeDual φ x = _ at h
  rw [extendLatticeDual_apply_lattice] at h
  exact_mod_cast h.symm

/-- Additive equivalence between lattice characters and the integral dual. -/
noncomputable def latticeCharacterDualAddEquiv :
    (latticeCharacters L) ≃+ Module.Dual ℤ (AddSubgroup.toIntSubmodule L) where
  toFun := restrictLatticeDual
  invFun := extendLatticeCharacter
  left_inv := by
    intro χ
    apply Subtype.ext
    exact extendLatticeDual_restrict χ
  right_inv := restrictLatticeDual_extend
  map_add' := by
    intro χ ψ
    apply LinearMap.ext
    intro x
    change restrictLatticeDual (χ + ψ) x = restrictLatticeDual χ x + restrictLatticeDual ψ x
    have h : ((restrictLatticeDual (χ + ψ) x : ℤ) : ℝ) =
        ((restrictLatticeDual χ x + restrictLatticeDual ψ x : ℤ) : ℝ) := by
      rw [Int.cast_add, ← restrictLatticeDual_spec, ← restrictLatticeDual_spec,
        ← restrictLatticeDual_spec]
      rfl
    exact_mod_cast h

/-- The restriction/extension equivalence, linear over the integers. -/
noncomputable def latticeCharacterDualEquiv :
    (latticeCharacters L) ≃ₗ[ℤ] Module.Dual ℤ (AddSubgroup.toIntSubmodule L) :=
  latticeCharacterDualAddEquiv.toIntLinearEquiv

@[simp] theorem latticeCharacterDualEquiv_apply (χ : latticeCharacters L) :
    latticeCharacterDualEquiv χ = restrictLatticeDual χ := rfl

@[simp] theorem latticeCharacterDualEquiv_symm_apply
    (φ : Module.Dual ℤ (AddSubgroup.toIntSubmodule L)) :
    (latticeCharacterDualEquiv (L := L)).symm φ = extendLatticeCharacter φ := rfl

end LatticeDualEquivalence

section CanonicalDualCompatibility

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

local instance : Module.Free ℤ (latticeCharacters L) :=
  Module.Free.of_equiv (latticeCharacterDualEquiv (L := L)).symm

local instance : Module.Finite ℤ (latticeCharacters L) :=
  Module.Finite.equiv (latticeCharacterDualEquiv (L := L)).symm

/-- Under the integral-dual equivalence, canonical precomposition is precisely
the dual of the lattice endomorphism whose characteristic polynomial occurs in
B1. -/
theorem restrictLatticeDual_dualCharacterAct
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) :
    restrictLatticeDual (dualCharacterAct D i χ) =
      (D.intLact i).dualMap (restrictLatticeDual χ) := by
  apply LinearMap.ext
  intro x
  have h : ((restrictLatticeDual (dualCharacterAct D i χ) x : ℤ) : ℝ) =
      ((restrictLatticeDual χ ((D.intLact i) x) : ℤ) : ℝ) := by
    rw [← restrictLatticeDual_spec, ← restrictLatticeDual_spec]
    rfl
  exact_mod_cast h

/-- The iterate form of canonical equivalence/precomposition compatibility. -/
theorem restrictLatticeDual_dualCharacterAct_iterate
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (n : ℕ) :
    restrictLatticeDual ((dualCharacterAct D i)^[n] χ) =
      ((D.intLact i).dualMap ^ n) (restrictLatticeDual χ) := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply,
        restrictLatticeDual_dualCharacterAct, ih]

/-- The same compatibility using the packaged integer-linear equivalence. -/
theorem latticeCharacterDualEquiv_dualCharacterAct_iterate
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (n : ℕ) :
    latticeCharacterDualEquiv ((dualCharacterAct D i)^[n] χ) =
      ((D.intLact i).dualMap ^ n) (latticeCharacterDualEquiv χ) :=
  restrictLatticeDual_dualCharacterAct_iterate D i χ n

/-- The canonical precomposition action as an integer-linear endomorphism of
lattice characters. -/
noncomputable def dualCharacterLinearAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (latticeCharacters L) →ₗ[ℤ] (latticeCharacters L) :=
  (dualCharacterAct D i).toIntLinearMap

/-- The integral-dual equivalence conjugates the character action to the dual
of the canonical lattice endomorphism. -/
theorem conj_dualCharacterLinearAct
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (latticeCharacterDualEquiv (L := L)).conj (dualCharacterLinearAct D i) =
      (D.intLact i).dualMap := by
  apply LinearMap.ext
  intro φ
  change restrictLatticeDual
    (dualCharacterAct D i ((latticeCharacterDualEquiv (L := L)).symm φ)) = _
  rw [restrictLatticeDual_dualCharacterAct]
  exact congrArg (D.intLact i).dualMap
    ((latticeCharacterDualEquiv (L := L)).apply_symm_apply φ)

/-- B1 for the integer-linear endomorphism of the actual lattice-character
group, transported from the canonical lattice endomorphism. -/
theorem exists_irreducible_charpoly_dualCharacterLinearAct
    (D : UnitPrimeModel L 𝒪)
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i).dualMap ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((dualCharacterLinearAct D i) ^ n)) := by
  obtain ⟨i, hi⟩ := B1
  refine ⟨i, fun n hn => ?_⟩
  have hcp : LinearMap.charpoly ((dualCharacterLinearAct D i) ^ n) =
      LinearMap.charpoly ((D.intLact i).dualMap ^ n) := by
    calc
      LinearMap.charpoly ((dualCharacterLinearAct D i) ^ n) =
          LinearMap.charpoly ((latticeCharacterDualEquiv (L := L)).conj
            ((dualCharacterLinearAct D i) ^ n)) :=
        (LinearEquiv.charpoly_conj _ _).symm
      _ = LinearMap.charpoly
          (((latticeCharacterDualEquiv (L := L)).conj
            (dualCharacterLinearAct D i)) ^ n) := by rw [conj_pow]
      _ = LinearMap.charpoly ((D.intLact i).dualMap ^ n) := by
        rw [conj_dualCharacterLinearAct]
  rw [hcp]
  exact hi n hn

/-- The original primal unit-prime B1, directly in the form needed by the
characterwise proof of Proposition 4.3. -/
theorem exists_irreducible_charpoly_dualCharacterLinearAct_of_unitPrimeB1
    (D : UnitPrimeModel L 𝒪)
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((dualCharacterLinearAct D i) ^ n)) :=
  exists_irreducible_charpoly_dualCharacterLinearAct D
    (UnitPrimeModel.exists_irreducible_charpoly_dual_intLact D B1)

end CanonicalDualCompatibility

end BerendProp43Canonical
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Canonical.charpoly_dualMap
#print axioms CubicTwoStage.BerendProp43Canonical.charpoly_ratAct_pow
#print axioms CubicTwoStage.BerendProp43Canonical.UnitPrimeModel.exists_irreducible_charpoly_dual_intLact
#print axioms CubicTwoStage.BerendProp43Canonical.characterOf
#print axioms CubicTwoStage.BerendProp43Canonical.continuous_characterOf
#print axioms CubicTwoStage.BerendProp43Canonical.characterOf_ne_zero
#print axioms CubicTwoStage.BerendProp43Canonical.characterOf_dualCharacterAct_iterate_apply
#print axioms CubicTwoStage.BerendProp43Canonical.dualCharacterAct_iterate_annihilates_iff
#print axioms CubicTwoStage.BerendProp43Canonical.latticeCharacterDualEquiv
#print axioms CubicTwoStage.BerendProp43Canonical.restrictLatticeDual_dualCharacterAct_iterate
#print axioms CubicTwoStage.BerendProp43Canonical.conj_dualCharacterLinearAct
#print axioms CubicTwoStage.BerendProp43Canonical.exists_irreducible_charpoly_dualCharacterLinearAct_of_unitPrimeB1
