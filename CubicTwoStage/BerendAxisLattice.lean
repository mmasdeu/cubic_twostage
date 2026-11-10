/-
# The axis density hypothesis `haxis` from the rank-three integer lattice

Swarm `smw97otfd`, member `m2`, direction `d2`.

`CubicTwoStage/BerendStageIBlockAxis.lean` reduces Stage I for the block model
`Pt = ℝ × ℂ` to two arithmetic densities, `hscal` and

  `haxis : Dense ((coord {0} : Set Pt) + (L : Set Pt))`.

This file **proves `haxis` for the canonical complex cubic** and leaves no
hypothesis behind.  The mathematical content is the classical fact behind
Berend's "density of the complex projection of the lattice":

* `coord {0}` is the kernel of the complex projection `cplxOf : Pt → ℂ`, so
  `Dense (coord {0} + L) ↔ Dense (cplxOf '' L)` (Section 2, elementary: a point
  of the coset is reached by adjusting its real coordinate, which costs nothing).
* `cplxOf '' L` is the image `A` of the ring of integers `𝓞 K` under the
  non-real complex embedding, i.e. a *subring* of `ℂ` containing `1` whose
  additive group is free of rank three.
* A closed additive subgroup `H ≤ ℂ` with `1 ∈ H`, closed under multiplication,
  not contained in `ℝ`, and containing a set of `ℤ`-rank `3`, is all of `ℂ`
  (`eq_top_of_isClosed_mul_mem`).  Suppose `H ≠ ⊤`.  If `H` contained a line
  `ℝ • u` with `u ≠ 0`, then for `h ∈ H` the product `u * h` again lies on a line
  inside `H`; if `u * h` left `ℝ • u` then `H` would be everything, so
  `u * h = c * u` and hence `h = c ∈ ℝ`, contradicting that `H` is not real.
  Therefore `H` has an isolated zero, i.e. is discrete.  Then the `ℤ`-span of the
  rank-`3` set is discrete as well, so `Real.finrank_eq_int_finrank_of_discrete`
  gives `Set.finrank ℝ s = 3`, while `s ⊆ ℂ` forces `Set.finrank ℝ s ≤ 2`.
  Contradiction.

Consequently `haxis` holds for `canonicalFieldModel K h` for every complex cubic
field `K` (`haxis_canonicalFieldModel`), and Stage I for that model follows from
`BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar` with only the two
named residuals `hscal` and the planar case left.

Everything is axiom free; the audit at the end shows only `propext`,
`Classical.choice`, `Quot.sound`.  The old axiom
`CubicTwoStage.berend_multi_invariance` is imported transitively
(`FieldModel → Uncovered → Berend`) but never used.
-/
import CubicTwoStage.BerendStageIBlockAxis
import CubicTwoStage.ComplexCubic
import CubicTwoStage.BerendCoordDense

open Set Filter Topology
open scoped Pointwise NumberField

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendAxisLattice

/-! ## 1. The complex projection and the axis -/

lemma cplxOf_sub (a b : Pt) : cplxOf (a - b) = cplxOf a - cplxOf b := by
  apply Complex.ext <;> simp [cplxOf, Matrix.vecHead, Matrix.vecTail]

lemma cplxOf_surjective : Function.Surjective cplxOf := fun z =>
  ⟨![0, z.re, z.im], by apply Complex.ext <;> simp [cplxOf]⟩

lemma cplxOf_eq_zero_iff (x : Pt) : cplxOf x = 0 ↔ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · intro h
    have h1 : (cplxOf x).re = 0 := by rw [h]; rfl
    have h2 : (cplxOf x).im = 0 := by rw [h]; rfl
    simpa using ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [cplxOf, h1, h2]

/-- The axis `coord {0}` is exactly the kernel of the complex projection. -/
lemma mem_coord_zero_iff (x : Pt) :
    x ∈ (BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) ↔ cplxOf x = 0 := by
  simp only [SetLike.mem_coe, BerendSec4.mem_coord]
  constructor
  · intro h
    exact (cplxOf_eq_zero_iff x).mpr ⟨h 1 (by decide), h 2 (by decide)⟩
  · intro h i hi
    rcases (cplxOf_eq_zero_iff x).mp h with ⟨h1, h2⟩
    fin_cases i
    · exact absurd rfl hi
    · exact h1
    · exact h2

lemma continuous_cplxOf : Continuous cplxOf := by
  have h1 : Continuous fun x : Pt => ((x 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_apply 1)
  have h2 : Continuous fun x : Pt => ((x 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_apply 2)
  have hh : cplxOf = fun x : Pt => ((x 1 : ℝ) : ℂ) + ((x 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [cplxOf, Matrix.vecHead, Matrix.vecTail]
  rw [hh]
  exact h1.add (h2.mul continuous_const)

/-- A point of the model space whose real coordinate vanishes has norm bounded by
the modulus of its complex projection. -/
lemma norm_le_norm_cplxOf {z : Pt} (h0 : z 0 = 0) : ‖z‖ ≤ ‖cplxOf z‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr ?_
  have hnorm : ‖cplxOf z‖ = Real.sqrt (z 1 ^ 2 + z 2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    norm_num [cplxOf, sq]
  intro i
  rw [hnorm, Real.norm_eq_abs]
  fin_cases i
  · show |z 0| ≤ Real.sqrt (z 1 ^ 2 + z 2 ^ 2)
    rw [h0]; simp
  · show |z 1| ≤ Real.sqrt (z 1 ^ 2 + z 2 ^ 2)
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (z 2), sq_abs (z 1)]
  · show |z 2| ≤ Real.sqrt (z 1 ^ 2 + z 2 ^ 2)
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (z 1), sq_abs (z 2)]

/-! ## 2. Density transfers from the axis to the complex projection -/

/-- `x` lies in the coset `coord {0} + L` exactly when some lattice point has the
same complex projection as `x`. -/
lemma mem_coord_add_iff (L : AddSubgroup Pt) {x : Pt} :
    x ∈ (BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt) ↔
      ∃ l ∈ L, cplxOf l = cplxOf x := by
  constructor
  · rintro ⟨c, hc, l, hl, rfl⟩
    exact ⟨l, hl, by rw [cplxOf_add, (mem_coord_zero_iff c).mp hc, zero_add]⟩
  · rintro ⟨l, hl, hcl⟩
    refine ⟨x - l, ?_, l, hl, sub_add_cancel x l⟩
    rw [mem_coord_zero_iff, cplxOf_sub, hcl, sub_self]

/-- **The axis density is the density of the complex projection of the lattice.** -/
theorem dense_coord_add_iff_dense_cplx (L : AddSubgroup Pt) :
    Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt)) ↔
      Dense (cplxOf '' (L : Set Pt)) := by
  constructor
  · intro h
    have himg : cplxOf '' ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt))
        = cplxOf '' (L : Set Pt) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hcl⟩ := (mem_coord_add_iff L).mp hy
        exact ⟨l, hl, hcl⟩
      · rintro ⟨l, hl, rfl⟩
        refine ⟨l, ⟨0, (BerendSec4.coord ({0} : Set (Fin 3))).zero_mem, l, hl, zero_add l⟩, rfl⟩
    have hsub := image_closure_subset_closure_image continuous_cplxOf
      (s := ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt)))
    rw [h.closure_eq, himg, Set.image_univ, cplxOf_surjective.range_eq] at hsub
    rw [dense_iff_closure_eq]
    exact top_unique hsub
  · intro h x
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hz : ∀ z : ℂ, ∃ l ∈ L, ‖cplxOf l - z‖ < ε := by
      intro z
      have hmem : z ∈ closure (cplxOf '' (L : Set Pt)) := by rw [h.closure_eq]; trivial
      rw [Metric.mem_closure_iff] at hmem
      obtain ⟨w, hw, hdist⟩ := hmem ε hε
      obtain ⟨l, hl, rfl⟩ := hw
      refine ⟨l, hl, ?_⟩
      have h1 : ‖cplxOf l - z‖ = dist z (cplxOf l) := by rw [dist_eq_norm, norm_sub_rev]
      rw [h1]
      exact hdist
    obtain ⟨l, hl, hd⟩ := hz (cplxOf x)
    have hcc : cplxOf (![x 0 - l 0, 0, 0] : Pt) = 0 := by
      apply Complex.ext <;> simp [cplxOf, Matrix.vecHead, Matrix.vecTail]
    have hc' : (![x 0 - l 0, 0, 0] : Pt) ∈
        (BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) :=
      (mem_coord_zero_iff _).mpr hcc
    refine ⟨![x 0 - l 0, 0, 0] + l, ⟨![x 0 - l 0, 0, 0], hc', l, hl, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hzero : (x - (![x 0 - l 0, 0, 0] + l)) 0 = 0 := by
      show x 0 - (x 0 - l 0 + l 0) = 0
      ring
    refine lt_of_le_of_lt (norm_le_norm_cplxOf hzero) ?_
    have hce : cplxOf (x - (![x 0 - l 0, 0, 0] + l)) = cplxOf (x - l) := by
      apply Complex.ext <;> simp [cplxOf, Matrix.vecHead, Matrix.vecTail]
    rw [hce, cplxOf_sub, norm_sub_rev]
    exact hd

/-! ## 3. A closed subring of `ℂ` of `ℤ`-rank three is everything -/

section Main

/-- A subgroup with an isolated zero has discrete subspace topology. -/
theorem discreteTopology_of_isolatedZero {E : Type*} [NormedAddCommGroup E]
    {D : AddSubgroup E} (h : BerendCoordDense.IsolatedZero D) : DiscreteTopology D := by
  obtain ⟨ε, hε, hiso⟩ := h
  have h0 : IsOpen ({0} : Set D) := by
    have heq : ({0} : Set D) = Subtype.val ⁻¹' (Metric.ball (0 : E) ε) := by
      ext x
      constructor
      · rintro rfl
        simpa [Metric.mem_ball] using hε
      · intro hx
        rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hx
        exact Subtype.ext (hiso (x : E) x.2 hx)
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  exact discreteTopology_iff_isOpen_singleton_zero.mpr h0

/-- **The key dichotomy.**  If `0 ≠ u` lies on a line inside `H` and `H` is closed
under multiplication, then either `H` is everything or `H` is contained in `ℝ`. -/
theorem eq_top_or_subset_real {H : AddSubgroup ℂ}
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ t : ℝ, t • u ∈ H) : H = ⊤ ∨ ∀ h ∈ H, h.im = 0 := by
  classical
  rcases eq_or_ne H ⊤ with htop | hproper
  · exact Or.inl htop
  refine Or.inr fun h hh => ?_
  have hul : u ∈ BerendCoordDense.lineal H := by
    rw [BerendCoordDense.mem_lineal]; exact hu
  have huh : u * h ∈ BerendCoordDense.lineal H := by
    rw [BerendCoordDense.mem_lineal]
    intro t
    have hteq : t • (u * h) = (t • u) * h := by
      rw [Complex.real_smul, Complex.real_smul, mul_assoc]
    rw [hteq]
    exact hmul _ (hu t) _ hh
  have hlineal_ne_top : BerendCoordDense.lineal H ≠ ⊤ := by
    intro htop'
    exact hproper (eq_top_iff.mpr fun x _ =>
      BerendCoordDense.lineal_le (H := H) (by rw [htop']; trivial))
  have hlt : BerendCoordDense.lineal H < ⊤ := lt_top_iff_ne_top.mpr hlineal_ne_top
  have hfin_lt : Module.finrank ℝ ↥(BerendCoordDense.lineal H) < 2 := by
    have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [finrank_top, Complex.finrank_real_complex] at hlt'
  have hle_span : Submodule.span ℝ ({u} : Set ℂ) ≤ BerendCoordDense.lineal H :=
    Submodule.span_le.mpr (by simpa using hul)
  have hfin_pos : 0 < Module.finrank ℝ ↥(BerendCoordDense.lineal H) := by
    have h1 := Submodule.finrank_mono hle_span
    rw [finrank_span_singleton (K := ℝ) hu0] at h1
    omega
  have hspan : Submodule.span ℝ ({u} : Set ℂ) = BerendCoordDense.lineal H := by
    refine Submodule.eq_of_le_of_finrank_eq hle_span ?_
    rw [finrank_span_singleton (K := ℝ) hu0]
    omega
  rw [← hspan] at huh
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huh
  have hreal : h = (c : ℂ) := by
    refine mul_left_cancel₀ hu0 ?_
    rw [← hc, Complex.real_smul, mul_comm]
  rw [hreal]
  simp

/-- **A closed, multiplicatively closed additive subgroup of `ℂ` containing a set
of `ℤ`-rank three is either real or everything.** -/
theorem eq_top_of_isClosed_mul_mem (H : AddSubgroup ℂ) (hH : IsClosed (H : Set ℂ))
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hne : ∃ z ∈ H, z.im ≠ 0)
    {s : Set ℂ} (hs : s ⊆ (H : Set ℂ)) (hs3 : Set.finrank ℤ s = 3) :
    H = ⊤ := by
  classical
  by_contra hproper
  have hiso : BerendCoordDense.IsolatedZero H := by
    by_cases hniso : BerendCoordDense.IsolatedZero H
    · exact hniso
    · obtain ⟨u, hu0, hu⟩ := BerendCoordDense.exists_line_of_not_isolatedZero hH hniso
      rcases eq_top_or_subset_real hmul hu0 hu with htop | hreal
      · exact (hproper htop).elim
      · obtain ⟨z, hz, hz'⟩ := hne
        exact (hz' (hreal z hz)).elim
  have hsub : (Submodule.span ℤ s : Set ℂ) ⊆ (H : Set ℂ) := by
    intro d hd
    refine Submodule.span_induction (R := ℤ) (s := s) (p := fun d _ => d ∈ H) ?_
      H.zero_mem ?_ ?_ ?_
    · intro x hx
      exact hs hx
    · intro x y _ _ hx hy
      exact H.add_mem hx hy
    · intro z x _ hx
      exact H.zsmul_mem hx z
    · exact hd
  have hisoZ : BerendCoordDense.IsolatedZero (Submodule.span ℤ s).toAddSubgroup := by
    obtain ⟨ε, hε, hε'⟩ := hiso
    exact ⟨ε, hε, fun d hd hlt => hε' d (hsub hd) hlt⟩
  have hdisc : DiscreteTopology ↥(Submodule.span ℤ s) :=
    discreteTopology_of_isolatedZero hisoZ
  have hrank := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [hs3] at hrank
  have hle : Set.finrank ℝ s ≤ 2 := by
    have h' := Submodule.finrank_le (R := ℝ) (M := ℂ) (Submodule.span ℝ s)
    rwa [Complex.finrank_real_complex] at h'
  omega

/-- The topological closure of a multiplicatively closed subgroup is again
multiplicatively closed. -/
theorem mul_mem_topologicalClosure {A : AddSubgroup ℂ}
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) :
    ∀ x ∈ A.topologicalClosure, ∀ y ∈ A.topologicalClosure,
      x * y ∈ A.topologicalClosure := by
  have hclosed : ∀ x : ℂ, IsClosed {y : ℂ | x * y ∈ A.topologicalClosure} := fun x =>
    (AddSubgroup.isClosed_topologicalClosure A).preimage (continuous_const.mul continuous_id)
  have step1 : ∀ x ∈ A, ∀ y ∈ A.topologicalClosure, x * y ∈ A.topologicalClosure := by
    intro x hx y hy
    have hsub : (A : Set ℂ) ⊆ {y : ℂ | x * y ∈ A.topologicalClosure} :=
      fun y hy => AddSubgroup.le_topologicalClosure A (hmul x hx y hy)
    have h := (hclosed x).closure_subset_iff.mpr hsub
    exact h hy
  intro x hx y hy
  have hclosed' : IsClosed {x : ℂ | x * y ∈ A.topologicalClosure} :=
    (AddSubgroup.isClosed_topologicalClosure A).preimage (continuous_id.mul continuous_const)
  have hsub : (A : Set ℂ) ⊆ {x : ℂ | x * y ∈ A.topologicalClosure} :=
    fun x hx => step1 x hx y hy
  have h := hclosed'.closure_subset_iff.mpr hsub
  exact h hx

end Main

/-! ## 4. The canonical complex cubic -/

section Canonical

variable {K : Type*} [Field K] [NumberField K] (h : IsComplexCubic K)

/-- The non-real complex embedding of the ring of integers. -/
noncomputable def cplxEmb : 𝓞 K →+* ℂ :=
  (NumberFieldCubic.complexEmbedding K h).comp (algebraMap (𝓞 K) K)

lemma cplxEmb_apply (a : 𝓞 K) :
    cplxEmb h a = NumberFieldCubic.complexEmbedding K h ((a : K)) := rfl

lemma cplxEmb_injective : Function.Injective (cplxEmb h) :=
  (NumberFieldCubic.complexEmbedding K h).injective.comp
    NumberField.RingOfIntegers.coe_injective

/-- The complex projection of the canonical embedding is the complex embedding. -/
lemma cplxOf_σ (x : K) :
    cplxOf (NumberFieldCubic.σ K h x) =
      NumberFieldCubic.complexEmbedding K h x := by
  apply Complex.ext <;> simp [cplxOf, Matrix.vecHead, Matrix.vecTail]

/-- **There is an algebraic integer with non-real complex embedding.** -/
theorem exists_int_im_ne_zero :
    ∃ a : 𝓞 K, (NumberFieldCubic.complexEmbedding K h ((a : K))).im ≠ 0 := by
  classical
  set φ := NumberFieldCubic.complexEmbedding K h
  by_contra hcon
  push_neg at hcon
  let F : K →ₗ[ℚ] ℝ :=
    { toFun := fun x => (φ x).im
      map_add' := fun x y => by simp [map_add]
      map_smul' := fun (q : ℚ) (x : K) => by
        show (φ (q • x)).im = q • (φ x).im
        rw [Rat.smul_def, map_mul, map_ratCast]
        simp [Complex.mul_im]
        norm_cast }
  have hF : F = 0 := by
    refine LinearMap.ext_on (s := Set.range (NumberField.integralBasis K))
      (NumberField.integralBasis K).span_eq ?_
    rintro _ ⟨i, rfl⟩
    show (φ (NumberField.integralBasis K i)).im = 0
    rw [NumberField.integralBasis_apply]
    exact hcon (NumberField.RingOfIntegers.basis K i)
  have hreal : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : (φ x).im = 0 := by
      have h' := LinearMap.congr_fun hF x
      simpa [F] using h'
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr hx
  have hnreal := NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (NumberFieldCubic.complexPlace_isComplex K h)
  apply hnreal
  exact (NumberField.InfinitePlace.isReal_iff.mpr hreal)

/-- The complex conjugates of an integral basis, a set of `ℤ`-rank three. -/
noncomputable def basisSet : Set ℂ :=
  Set.range fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 K) =>
    cplxEmb h (NumberField.RingOfIntegers.basis K i)

theorem finrank_basisSet : Set.finrank ℤ (basisSet h) = 3 := by
  have hlin : LinearIndependent ℤ (fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 K) =>
      cplxEmb h (NumberField.RingOfIntegers.basis K i)) := by
    set f : 𝓞 K →ₗ[ℤ] ℂ := AddMonoidHom.toIntLinearMap (cplxEmb h).toAddMonoidHom with hf
    have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr (cplxEmb_injective h)
    have hbas := LinearIndependent.map' (Module.Basis.linearIndependent
      (NumberField.RingOfIntegers.basis K)) f hker
    exact hbas
  rw [basisSet, Set.finrank, finrank_span_eq_card hlin,
    ← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, h.1]

/-- **The complex projection of the canonical lattice is dense in `ℂ`.** -/
theorem dense_cplxOf_lattice :
    Dense (cplxOf '' ((NumberFieldCubic.canonicalFieldModel K h).lattice : Set Pt)) := by
  classical
  have himg : cplxOf '' ((NumberFieldCubic.canonicalFieldModel K h).lattice : Set Pt)
      = Set.range (cplxEmb h) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨g, hg⟩ := (NumberFieldCubic.canonicalFieldModel K h).mem_lattice.mp hp
      let g' : 𝓞 K := ⟨g.1, g.2⟩
      refine ⟨g', ?_⟩
      rw [cplxEmb_apply, ← cplxOf_σ]
      exact congrArg cplxOf hg
    · rintro ⟨a, rfl⟩
      exact ⟨NumberFieldCubic.σ K h ((a : K)),
        (NumberFieldCubic.canonicalFieldModel K h).mem_lattice.mpr ⟨a, rfl⟩,
        by rw [cplxOf_σ, cplxEmb_apply]⟩
  rw [himg]
  set A : AddSubgroup ℂ := (cplxEmb h).toAddMonoidHom.range with hA
  have hAcoe : (A : Set ℂ) = Set.range (cplxEmb h) := rfl
  have hmulA : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact ⟨a * b, map_mul (cplxEmb h) a b⟩
  have h1A : (1 : ℂ) ∈ A := ⟨1, map_one (cplxEmb h)⟩
  have hneA : ∃ z ∈ A, z.im ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_int_im_ne_zero h
    exact ⟨cplxEmb h a, ⟨a, rfl⟩, by rwa [cplxEmb_apply]⟩
  have hsA : basisSet h ⊆ (A : Set ℂ) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  have hneH : ∃ z ∈ A.topologicalClosure, z.im ≠ 0 := by
    obtain ⟨z, hzA, hz⟩ := hneA
    exact ⟨z, AddSubgroup.le_topologicalClosure A hzA, hz⟩
  have hsH : basisSet h ⊆ (A.topologicalClosure : Set ℂ) := fun z hz =>
    AddSubgroup.le_topologicalClosure A (hsA hz)
  have htop := eq_top_of_isClosed_mul_mem A.topologicalClosure
    (AddSubgroup.isClosed_topologicalClosure _)
    (mul_mem_topologicalClosure hmulA) hneH hsH (finrank_basisSet h)
  have hdenseA : Dense (A : Set ℂ) := by
    rw [dense_iff_closure_eq, ← AddSubgroup.topologicalClosure_coe, htop, AddSubgroup.coe_top]
  rw [← hAcoe]
  exact hdenseA

/-- **`haxis` for the canonical complex cubic**, in the exact form consumed by
`BerendStageIBlock.zeroNonisolatedFull_fieldModel_of_planar`. -/
theorem haxis_canonicalFieldModel :
    Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) +
      ((NumberFieldCubic.canonicalFieldModel K h).lattice : Set Pt)) :=
  (dense_coord_add_iff_dense_cplx _).mpr (dense_cplxOf_lattice h)

end Canonical

/-! ## 5. Generic bridge from the field model -/

/-- For any field model, density of the complex projection of the lattice gives
`haxis`. -/
theorem dense_coord_add_of_dense_cplx {K : Type*} [Field K] {𝒪 : Subring K}
    {Nm : AbsNorm K} (FM : FieldModel K 𝒪 Nm)
    (hd : Dense (cplxOf '' (FM.lattice : Set Pt))) :
    Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)) :=
  (dense_coord_add_iff_dense_cplx _).mpr hd

end BerendAxisLattice
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendAxisLattice.dense_coord_add_iff_dense_cplx
#print axioms CubicTwoStage.BerendAxisLattice.eq_top_of_isClosed_mul_mem
#print axioms CubicTwoStage.BerendAxisLattice.exists_int_im_ne_zero
#print axioms CubicTwoStage.BerendAxisLattice.finrank_basisSet
#print axioms CubicTwoStage.BerendAxisLattice.haxis_canonicalFieldModel
