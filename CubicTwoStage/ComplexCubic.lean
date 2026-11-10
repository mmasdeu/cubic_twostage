/-
# A canonical `FieldModel` for a complex cubic field

A complex cubic field has one real and one complex infinite place.  The real and
imaginary parts of the complex embedding give exactly the coordinates used in
`Model.lean`, and the formula for `normR` is the usual product formula
`|Nm_{K/ℚ}|`.
-/
import CubicTwoStage.Main
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

namespace CubicTwoStage
namespace NumberFieldCubic

open Function Fintype Module NumberField
open scoped Classical TensorProduct

variable (K : Type*) [Field K] [NumberField K]

/-- A complex cubic field has one real infinite place. -/
theorem one_real_place (h : IsComplexCubic K) : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  have hcard := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h.2] at hcard
  rw [h.1] at hrank
  omega

/-- A complex cubic field has one complex infinite place. -/
theorem one_complex_place (h : IsComplexCubic K) : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have hcard := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h.2] at hcard
  rw [h.1] at hrank
  omega

/-- The two choices of real and complex infinite place at a cubic field. -/
theorem exists_real_complex_places (h : IsComplexCubic K) :
    ∃ wr wc : InfinitePlace K, NumberField.InfinitePlace.IsReal wr ∧ NumberField.InfinitePlace.IsComplex wc ∧ wr ≠ wc := by
  classical
  have htwo : 1 < Fintype.card (NumberField.InfinitePlace K) := by rw [h.2]; norm_num
  obtain ⟨w1, w2, hw12⟩ := Fintype.one_lt_card_iff.mp htwo
  by_cases hw1 : NumberField.InfinitePlace.IsReal w1
  · by_cases hw2 : NumberField.InfinitePlace.IsReal w2
    · obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp (one_real_place K h)
      exact False.elim (hw12 (congrArg Subtype.val
        ((hu ⟨w1, hw1⟩).trans (hu ⟨w2, hw2⟩).symm)))
    · exact ⟨w1, w2, hw1, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw2, hw12⟩
  · by_cases hw2 : NumberField.InfinitePlace.IsComplex w2
    · obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp (one_complex_place K h)
      exact False.elim (hw12 (congrArg Subtype.val
        ((hu ⟨w1, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw1⟩).trans
          (hu ⟨w2, hw2⟩).symm)))
    · exact ⟨w2, w1, NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw2,
        NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw1, hw12.symm⟩

/-- A selected real infinite place. -/
noncomputable def realPlace (h : IsComplexCubic K) : InfinitePlace K :=
  (exists_real_complex_places K h).choose

/-- A selected complex infinite place. -/
noncomputable def complexPlace (h : IsComplexCubic K) : InfinitePlace K :=
  Classical.choose (Classical.choose_spec (exists_real_complex_places K h))

theorem realPlace_isReal (h : IsComplexCubic K) : InfinitePlace.IsReal (realPlace K h) :=
  (Classical.choose_spec (Classical.choose_spec (exists_real_complex_places K h))).1

theorem complexPlace_isComplex (h : IsComplexCubic K) : InfinitePlace.IsComplex (complexPlace K h) :=
  (Classical.choose_spec (Classical.choose_spec (exists_real_complex_places K h))).2.1

/-- The two places are distinct. -/
theorem real_ne_complex (h : IsComplexCubic K) : realPlace K h ≠ complexPlace K h :=
  (Classical.choose_spec (Classical.choose_spec (exists_real_complex_places K h))).2.2


/-- The real embedding selected by the unique real place. -/
noncomputable def realEmbedding (h : IsComplexCubic K) : K →+* ℝ :=
  NumberField.InfinitePlace.embedding_of_isReal (realPlace_isReal K h)

/-- A complex embedding selected by the unique complex place. -/
noncomputable def complexEmbedding (h : IsComplexCubic K) : K →+* ℂ :=
  NumberField.InfinitePlace.embedding (complexPlace K h)

/-- The canonical embedding into the coordinates of `Pt = ℝ × ℂ`. -/
noncomputable def σ (h : IsComplexCubic K) (x : K) : Pt :=
  ![realEmbedding K h x, (complexEmbedding K h x).re, (complexEmbedding K h x).im]

@[simp] lemma σ_apply_zero (h : IsComplexCubic K) (x : K) :
    σ K h x 0 = realEmbedding K h x := by simp [σ]

@[simp] lemma σ_apply_one (h : IsComplexCubic K) (x : K) :
    σ K h x 1 = (complexEmbedding K h x).re := by simp [σ]

@[simp] lemma σ_apply_two (h : IsComplexCubic K) (x : K) :
    σ K h x 2 = (complexEmbedding K h x).im := by simp [σ]

/-- The selected places exhaust the infinite places. -/
theorem places_eq_univ (h : IsComplexCubic K) :
    ({realPlace K h, complexPlace K h} : Finset (InfinitePlace K)) = Finset.univ := by
  classical
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [Finset.card_pair (real_ne_complex K h), h.2]

/-- The absolute value of the model norm is the absolute algebraic norm. -/
theorem abs_normR_σ (h : IsComplexCubic K) (x : K) :
    (((numberFieldAbsNorm K x : ℚ≥0) : ℝ)) = |normR (σ K h x)| := by
  classical
  have hp := NumberField.InfinitePlace.prod_eq_abs_norm (K := K) x
  rw [← places_eq_univ K h, Finset.prod_pair (real_ne_complex K h),
    (realPlace_isReal K h).mult_eq_one, (complexPlace_isComplex K h).mult_eq_two,
    pow_one] at hp
  have hr : realPlace K h x = ‖realEmbedding K h x‖ :=
    (NumberField.InfinitePlace.norm_embedding_of_isReal (realPlace_isReal K h) x).symm
  have hc : complexPlace K h x = ‖complexEmbedding K h x‖ :=
    (NumberField.InfinitePlace.norm_embedding_eq (complexPlace K h) x).symm
  rw [hr, hc] at hp
  change (↑|Algebra.norm ℚ x| : ℝ) = |normR (σ K h x)|
  rw [← hp]
  simp only [normR, σ_apply_zero, σ_apply_one, σ_apply_two, Real.norm_eq_abs, abs_mul]
  have hsum : 0 ≤ (complexEmbedding K h x).re ^ 2 + (complexEmbedding K h x).im ^ 2 := by
    nlinarith [sq_nonneg (complexEmbedding K h x).re, sq_nonneg (complexEmbedding K h x).im]
  rw [abs_of_nonneg hsum, Complex.sq_norm, Complex.normSq_apply]
  ring

@[simp] theorem σ_zero (h : IsComplexCubic K) : σ K h 0 = 0 := by
  funext i
  fin_cases i <;> simp [σ]

@[simp] theorem σ_add (h : IsComplexCubic K) (a b : K) :
    σ K h (a + b) = σ K h a + σ K h b := by
  funext i
  fin_cases i <;> simp [σ]

@[simp] theorem σ_mul (h : IsComplexCubic K) (a b : K) :
    σ K h (a * b) = σ K h a ⋆ σ K h b := by
  funext i
  fin_cases i <;> simp [σ, mulC]

@[simp] theorem σ_one (h : IsComplexCubic K) : σ K h 1 = oneC := by
  funext i
  fin_cases i <;> simp [σ, oneC]

/-- The canonical coordinate embedding is injective. -/
theorem σ_injective (h : IsComplexCubic K) : Function.Injective (σ K h) := by
  intro a b hab
  apply (realEmbedding K h).injective
  simpa using congrFun hab 0

/-- The canonical field model on the ring of integers of a complex cubic field. -/
noncomputable def canonicalFieldModel (h : IsComplexCubic K) :
    FieldModel K (numberFieldO K) (numberFieldAbsNorm K) where
  σ := σ K h
  σ_zero := σ_zero K h
  σ_add := σ_add K h
  σ_mul := σ_mul K h
  σ_one := σ_one K h
  σ_inv a ha := by
    rw [← σ_mul, mul_inv_cancel₀ ha, σ_one]
  normR_abs a := (abs_normR_σ K h a).symm
  norm_nat a ha := by
    let x : 𝓞 K := ⟨a, ha⟩
    refine ⟨(Algebra.norm ℤ x).natAbs, ?_⟩
    apply NNRat.coe_inj.mp
    change |Algebra.norm ℚ a| = (((Algebra.norm ℤ x).natAbs : ℕ) : ℚ)
    change |Algebra.norm ℚ (x : K)| = (((Algebra.norm ℤ x).natAbs : ℕ) : ℚ)
    rw [← Algebra.coe_norm_int x]
    simp

/-! ## The integer lattice in the canonical coordinates -/

/-- The linear equivalence between Mathlib's mixed space and the selected
coordinates in `Pt`.  Both subtype index types are singletons in signature
`(1,1)`. -/
noncomputable def mixedCoordEquiv (h : IsComplexCubic K) :
    NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ] Pt := by
  letI : Unique {w : InfinitePlace K // w.IsReal} :=
    Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp (one_real_place K h))
  letI : Unique {w : InfinitePlace K // w.IsComplex} :=
    Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp (one_complex_place K h))
  exact {
    toFun := fun x => ![x.1 ⟨realPlace K h, realPlace_isReal K h⟩,
      (x.2 ⟨complexPlace K h, complexPlace_isComplex K h⟩).re,
      (x.2 ⟨complexPlace K h, complexPlace_isComplex K h⟩).im]
    invFun := fun p => (fun _ => p 0, fun _ => ⟨p 1, p 2⟩)
    map_add' := by
      intro x y
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro r x
      funext i
      fin_cases i <;> simp [Complex.real_smul]
    left_inv := by
      intro x
      apply Prod.ext
      · funext w
        have hw : w = ⟨realPlace K h, realPlace_isReal K h⟩ := Subsingleton.elim _ _
        subst w
        rfl
      · funext w
        have hw : w = ⟨complexPlace K h, complexPlace_isComplex K h⟩ := Subsingleton.elim _ _
        subst w
        apply Complex.ext <;> simp
    right_inv := by
      intro p
      funext i
      fin_cases i <;> simp }

/-- The coordinate equivalence identifies the two canonical embeddings. -/
theorem mixedCoordEquiv_mixedEmbedding (h : IsComplexCubic K) (x : K) :
    mixedCoordEquiv K h (NumberField.mixedEmbedding K x) = σ K h x := by
  funext i
  fin_cases i <;> simp [mixedCoordEquiv, σ, realEmbedding, complexEmbedding]

/-- Mathlib's integer lattice transported to the canonical coordinates. -/
noncomputable def canonicalIntegerLattice (h : IsComplexCubic K) : Submodule ℤ Pt :=
  ZLattice.comap ℝ (NumberField.mixedEmbedding.integerLattice K)
    (mixedCoordEquiv K h).symm.toContinuousLinearEquiv.toLinearMap

instance discreteTopology_canonicalIntegerLattice (h : IsComplexCubic K) :
    DiscreteTopology (canonicalIntegerLattice K h) := by
  unfold canonicalIntegerLattice
  infer_instance

instance isZLattice_canonicalIntegerLattice (h : IsComplexCubic K) :
    IsZLattice ℝ (canonicalIntegerLattice K h) := by
  unfold canonicalIntegerLattice
  infer_instance

/-- The transported integer lattice is exactly `σ(𝒪_K)`. -/
theorem canonicalIntegerLattice_eq (h : IsComplexCubic K) : canonicalIntegerLattice K h =
    AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice := by
  ext p
  constructor
  · intro hp
    change (mixedCoordEquiv K h).symm p ∈ NumberField.mixedEmbedding.integerLattice K at hp
    obtain ⟨a, ha⟩ := hp
    have ha' : NumberField.mixedEmbedding K (a : K) = (mixedCoordEquiv K h).symm p := ha
    change p ∈ (canonicalFieldModel K h).lattice
    apply (canonicalFieldModel K h).mem_lattice.mpr
    refine ⟨⟨(a : K), a.2⟩, ?_⟩
    calc
      (canonicalFieldModel K h).σ (a : K) =
          mixedCoordEquiv K h (NumberField.mixedEmbedding K (a : K)) :=
        (mixedCoordEquiv_mixedEmbedding K h (a : K)).symm
      _ = mixedCoordEquiv K h ((mixedCoordEquiv K h).symm p) :=
        congrArg (mixedCoordEquiv K h) ha'
      _ = p := (mixedCoordEquiv K h).apply_symm_apply p
  · intro hp
    change p ∈ (canonicalFieldModel K h).lattice at hp
    obtain ⟨g, hg⟩ := (canonicalFieldModel K h).mem_lattice.mp hp
    change (mixedCoordEquiv K h).symm p ∈ NumberField.mixedEmbedding.integerLattice K
    refine ⟨⟨(g : K), g.2⟩, ?_⟩
    apply (mixedCoordEquiv K h).injective
    simp only [LinearEquiv.apply_symm_apply]
    change mixedCoordEquiv K h (NumberField.mixedEmbedding K (g : K)) = p
    rw [mixedCoordEquiv_mixedEmbedding]
    exact hg

instance discreteTopology_canonicalFieldModel_lattice (h : IsComplexCubic K) :
    DiscreteTopology (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) := by
  rw [← canonicalIntegerLattice_eq]
  infer_instance

instance isZLattice_canonicalFieldModel_lattice (h : IsComplexCubic K) :
    IsZLattice ℝ (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) := by
  constructor
  have hs : Submodule.span ℝ (canonicalIntegerLattice K h : Set Pt) = ⊤ :=
    IsZLattice.span_top
  rwa [canonicalIntegerLattice_eq] at hs

/-- The torus `(ℝ × ℂ) / σ(𝒪_K)` is compact for the canonical embedding. -/
instance compactSpace_canonicalFieldModel_torus (h : IsComplexCubic K) :
    CompactSpace (Torus (canonicalFieldModel K h).lattice) :=
  compact_quotient_of_isZLattice (canonicalFieldModel K h).lattice

/- The public canonical theorem is completed in `BerendCompleteCanonical`. -/

end NumberFieldCubic
end CubicTwoStage
