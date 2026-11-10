/-
Section 1: the theorems of the introduction, and Section 9: the questions.
-/
import CubicTwoStage.Basic
import CubicTwoStage.Setting
import CubicTwoStage.Equiv
import CubicTwoStage.Verify
import CubicTwoStage.General
import CubicTwoStage.FieldModel
import CubicTwoStage.RationalIndependence
import CubicTwoStage.Lattice

open scoped TensorProduct

set_option linter.unusedVariables false

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-- The canonical absolute norm `x ↦ |Nm_{K/ℚ}(x)|` of a number field. -/
noncomputable def numberFieldAbsNorm (K : Type*) [Field K] [NumberField K] : AbsNorm K where
  toFun x := ⟨|((Algebra.norm ℚ) x : ℚ)|, abs_nonneg _⟩
  map_zero' := by
    apply NNRat.coe_inj.mp
    show |((Algebra.norm ℚ) (0 : K) : ℚ)| = (0 : ℚ)
    rw [Algebra.norm_zero]
    simp
  map_one' := by
    apply NNRat.coe_inj.mp
    show |((Algebra.norm ℚ) (1 : K) : ℚ)| = (1 : ℚ)
    rw [map_one]
    norm_num
  map_mul' := by
    intro a b
    apply NNRat.coe_inj.mp
    simp only [map_mul, NNRat.coe_mk]
    exact abs_mul _ _

/-- The ring of integers of a number field, as a subring of the field. -/
noncomputable def numberFieldO (K : Type*) [Field K] [NumberField K] : Subring K :=
  (integralClosure ℤ K).toSubring

/-- A complex cubic field: degree three with exactly one real and one complex
infinite place. -/
def IsComplexCubic (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 3 ∧ Fintype.card (NumberField.InfinitePlace K) = 2

/-- An explicit finite covering of the fundamental domain by regions
`V(q)`.  This is the mathematical content of a certificate; the interval
arithmetic verification is computational data and is not encoded here. -/
def HasFiniteRegionCover (K : Type*) [Field K] [NumberField K] (σ : K → Pt) : Prop :=
  ∃ F : Finset (K × K),
    (∀ p ∈ F, p.1 ∈ numberFieldO K ∧ p.2 ∈ numberFieldO K ∧ p.2 ≠ 0) ∧
    unitCube ⊆ ⋃ p ∈ F,
      V (σ (p.1 + p.2⁻¹)) (((numberFieldAbsNorm K p.2 : ℚ≥0) : ℝ))⁻¹

/-- **External computational input for Theorem 1.1.**

This is the assertion produced in the paper by the SageMath/PARI search and the
interval-arithmetic verification of the certificates for the complex cubic
fields of class number one and `|d_K| < 5000`.  The certificates comprise 3.4 GB
of external data and are not formalized here; this is therefore the single
custom axiom behind `thm_main`. -/
axiom thm_main_computational_input (K : Type*) [Field K] [NumberField K]
    (hcubic : IsComplexCubic K)
    (hclass : NumberField.classNumber K = 1)
    (hdisc : Int.natAbs (NumberField.discr K) < 5000) :
    IsTwoStageEuclidean (numberFieldO K) (numberFieldAbsNorm K) ∧
      ∃ σ : K → Pt,
        Function.Injective σ ∧
        (∀ a b : K, σ (a + b) = σ a + σ b) ∧
        (∀ x : K, (((numberFieldAbsNorm K x : ℚ≥0) : ℝ) = |normR (σ x)|)) ∧
        HasFiniteRegionCover K σ

/-- **Theorem 1.1**.  Every complex cubic field of class number one with
`|d_K| < 5000` is 2-stage Euclidean, and admits an explicit finite covering of
a fundamental domain by regions `V(q)`.

Compared with the earlier schema, the statement now quantifies over actual
number fields, uses Mathlib's class number and discriminant, fixes the complex
cubic signature, and concludes both 2-stage Euclideanity and a finite region
covering.  The existence of the 550 specific fields and the certificates is the
external input `thm_main_computational_input`. -/
theorem thm_main (K : Type*) [Field K] [NumberField K]
    (hcubic : IsComplexCubic K)
    (hclass : NumberField.classNumber K = 1)
    (hdisc : Int.natAbs (NumberField.discr K) < 5000) :
    IsTwoStageEuclidean (numberFieldO K) (numberFieldAbsNorm K) ∧
      ∃ σ : K → Pt,
        Function.Injective σ ∧
        (∀ a b : K, σ (a + b) = σ a + σ b) ∧
        (∀ x : K, (((numberFieldAbsNorm K x : ℚ≥0) : ℝ) = |normR (σ x)|)) ∧
        HasFiniteRegionCover K σ :=
  thm_main_computational_input K hcubic hclass hdisc

/-- **Theorem 1.2** (equivalence, introduction form).

Let `K` be a number field with infinite unit group, `𝒪` a subring with integral
absolute norm and `σ : K → ℝ × ℂ` the embedding of §3.  The points of `ℝ × ℂ`
that lie in no region `V(q)` form finitely many classes modulo `σ(𝒪)`, and each
of those classes has a representative in `σ(K)`.  In particular `K` is 2-stage
Euclidean if and only if a fundamental domain of `𝒪` is covered by finitely many
regions `V(q)`.

This is Theorems 3.3 and 3.6 assembled.  The geometric and embedding hypotheses
that the earlier version assumed (`L = σ(𝒪)`, `W` open and a union of classes,
unit invariance of the uncovered set, `σ` additive and odd, the action of units
on `σ(K)`, no nonzero fixed vectors) are now *proved* in `FieldModel.lean` from
the field data `FM`.  What remains assumed is the paper's number theory: the
`p`-adic property of `π` (Lemma 3.7), Berend's conditions (B1)–(B2),
and the `IsZLattice` property `DiscreteTopology` together with
  `Submodule.span ℝ L = ⊤`.  Berend's (B3) is deduced from `Nm π = p`
in `CubicTwoStage/RationalIndependence.lean`. -/
theorem thm_intro_equiv {K : Type*} [Field K] (𝒪 : Subring K) (N : AbsNorm K)
    (FM : FieldModel K 𝒪 N) (ε : 𝒪ˣ) (π : K) (m : ℕ)
    (hfrac : ∀ x : K, ∃ α ∈ 𝒪, ∃ β ∈ 𝒪, β ≠ 0 ∧ x = α / β)
    (C : Set Pt) (V : Pt → Set Pt)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : 𝒪), ∃ k : ℕ, ∃ h ∈ 𝒪,
      (1 + π ^ m * ((g : 𝒪) : K)) - ((ε : 𝒪) : K) ^ k = π ^ (m + j) * h)
    (hVopen : ∀ c, IsOpen (V c))
    (hVtrans : ∀ c g, g ∈ FM.lattice → ∀ x, x ∈ V (c + g) ↔ x - g ∈ V c)
    (hCtrans : ∀ c ∈ C, ∀ g ∈ FM.lattice, c + g ∈ C)
    (hfund : ∀ x : Pt, ∃ g ∈ FM.lattice, x - g ∈ unitCube)
    (hBerend : (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧
        N (x - (q1 + q2⁻¹)) < (N q2)⁻¹) →
      (∀ x : Pt, ∃ c ∈ C, x ∈ V c))
    (hsub : (∀ x : Pt, ∃ c ∈ C, x ∈ V c) →
      (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧
        N (x - (q1 + q2⁻¹)) < (N q2)⁻¹))
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    (hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly (((FM.toModel ε π hπO hπ0).lact i) ^ n)))
    (p : ℕ) (hp : 1 < p) (hπN : N π = (p : ℚ≥0))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ,
        LinearMap.baseChange ℂ (((FM.toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt)) x =
          μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) (FM.toModel ε π hπO hπ0).linFam FM.lattice
      (FM.toModel ε π hπO hπ0).linFam_preserves hZL B1 B2
      (rational_independence_corrected FM ε π hπO hπ0 hεpow p hp (hπN)) 
      (FM.toModel ε π hπO hπ0).linFam_comm) :
    (∃ F : Finset Pt, ∀ x ∈ uncovered 𝒪 N FM.σ, ∃ c ∈ F,
      (∃ y : K, c = FM.σ y) ∧ x - c ∈ FM.lattice) ∧
      (IsTwoStageEuclidean 𝒪 N ↔
        ∃ F : Finset Pt, (∀ c ∈ F, c ∈ C) ∧ unitCube ⊆ ⋃ c ∈ F, V c) :=
  ⟨thm_uncovered_field FM ε π m hπO hπ0 hεpow hpadic hZL B1 p hp hπN B2 H,
    (thm_equiv 𝒪 N hfrac FM.lattice C V hVopen hVtrans hCtrans hfund hBerend hsub).2⟩




/-- **External computational input for Theorem 1.3.**

Over the 550 complex cubic fields of class number one and `|d_K| < 5000`, every
exact smooth level exists and lies between `1` and `59`.  The finer distribution
of exact values in the paper is external data and is not encoded here. -/
axiom thm_smooth_computational_input (ι : Type*) [Fintype ι]
    (K' : ι → Type*) [∀ i, Field (K' i)] [∀ i, NumberField (K' i)]
    (h550 : Fintype.card ι = 550)
    (hcubic : ∀ i, IsComplexCubic (K' i))
    (hclass : ∀ i, NumberField.classNumber (K' i) = 1)
    (hdisc : ∀ i, Int.natAbs (NumberField.discr (K' i)) < 5000) :
    ∀ i, ∃ (σ : K' i → Pt) (N : ℕ),
      Function.Injective σ ∧
      (∀ a b : K' i, σ (a + b) = σ a + σ b) ∧
      (∀ x : K' i,
        (((numberFieldAbsNorm (K' i) x : ℚ≥0) : ℝ) = |normR (σ x)|)) ∧
      HasSmoothLevel (numberFieldO (K' i)) (numberFieldAbsNorm (K' i)) σ N ∧
      1 ≤ N ∧ N ≤ 59

/-- **Theorem 1.3**.  For the 550 complex cubic fields of class number one and
`|d_K| < 5000`, certificates determine an exact smooth level between `1` and
`59`.

The finer cardinality statement—166 fields by the authors' computations, 52
further `N_min=2` fields re-checked from Bagger–Booker–Trudgian, and 3 more taken
from that paper—is external numerical data and is not represented in this
statement. -/
theorem thm_smooth (ι : Type*) [Fintype ι]
    (K' : ι → Type*) [∀ i, Field (K' i)] [∀ i, NumberField (K' i)]
    (h550 : Fintype.card ι = 550)
    (hcubic : ∀ i, IsComplexCubic (K' i))
    (hclass : ∀ i, NumberField.classNumber (K' i) = 1)
    (hdisc : ∀ i, Int.natAbs (NumberField.discr (K' i)) < 5000) :
    ∀ i, ∃ (σ : K' i → Pt) (N : ℕ),
      Function.Injective σ ∧
      (∀ a b : K' i, σ (a + b) = σ a + σ b) ∧
      (∀ x : K' i,
        (((numberFieldAbsNorm (K' i) x : ℚ≥0) : ℝ) = |normR (σ x)|)) ∧
      HasSmoothLevel (numberFieldO (K' i)) (numberFieldAbsNorm (K' i)) σ N ∧
      1 ≤ N ∧ N ≤ 59 :=
  thm_smooth_computational_input ι K' h550 hcubic hclass hdisc

/-! ### Section 9: the questions

The three questions of §9 are open problems; they are recorded as `Prop`s.-/

/-- **Question 9.1**.  Is every complex cubic field of class number one 2-stage
Euclidean, unconditionally?  By Theorem 3.3 this is the same as asking whether
`D̄` is always covered by finitely many regions. -/
def QuestionConverse : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra ℚ K'] (𝒪 : Subring K') (Nm : AbsNorm K'),
    Module.finrank ℚ K' = 3 → IsTwoStageEuclidean 𝒪 Nm

/-- **Question 9.2** (bounded denominators).  Suppose that every point of `σ(K)`
lies in a region whose denominator has norm at most `N`.  Is `K` then `N`-smooth
Euclidean, i.e. are the points of `ℝ × ℂ` also covered by such regions? -/
def QuestionBounded (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (N : ℕ) : Prop :=
  (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ Nm q2 ≤ (N : ℚ≥0) ∧
      |normR (σ x - σ (q1 + q2⁻¹))| < (((Nm q2 : ℚ≥0)) : ℝ)⁻¹) →
    IsNSmoothEuclidean 𝒪 Nm σ N

/-- **Question 9.3**.  Which arithmetic invariants determine `N_min(K)`? -/
def QuestionInvariants (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (N : ℕ) : Prop :=
  HasSmoothLevel 𝒪 Nm σ N

end CubicTwoStage
