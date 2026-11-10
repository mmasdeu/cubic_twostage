/-
# Characterwise approximation on finite-dimensional tori

The analytic part of Berend's Lemma 4.7, formulated for probability measures on
`UnitAddTorus d`.  If every nontrivial Fourier character has integral tending
to zero, then integrals of all continuous functions tend to their Haar
integrals.  The proof uses only the dense Fourier span and uniform norm
estimates.
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Regular

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal Pointwise

namespace BerendTorusCharacters

/-- Use the normalized Haar measure for which `UnitAddTorus.mFourier` is
orthonormal.  These are the same local instances as in `AddCircleMulti`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

local notation "𝕋" => UnitAddTorus d

lemma integrable_continuousMap (μ : Measure (𝕋)) [IsFiniteMeasure μ]
    (f : C(𝕋, ℂ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma dist_integral_le_dist (μ : Measure (𝕋)) [IsProbabilityMeasure μ]
    (f g : C(𝕋, ℂ)) :
    dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub (integrable_continuousMap μ f)
    (integrable_continuousMap μ g)]
  calc
    ‖∫ x, (f x - g x) ∂μ‖ ≤ ‖f - g‖ * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
        simpa only [ContinuousMap.sub_apply] using (f - g).norm_coe_le_norm x)
    _ = ‖f - g‖ := by simp
    _ = dist f g := (dist_eq_norm f g).symm

section GenericCharacters

variable {T ι : Type*} [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace T] [BorelSpace T]

lemma integrable_continuousMap_generic (μ : Measure T) [IsFiniteMeasure μ]
    (f : C(T, ℂ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma dist_integral_le_dist_generic (μ : Measure T) [IsProbabilityMeasure μ]
    (f g : C(T, ℂ)) :
    dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub (integrable_continuousMap_generic μ f)
    (integrable_continuousMap_generic μ g)]
  calc
    ‖∫ x, (f x - g x) ∂μ‖ ≤ ‖f - g‖ * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
        simpa only [ContinuousMap.sub_apply] using (f - g).norm_coe_le_norm x)
    _ = ‖f - g‖ := by simp
    _ = dist f g := (dist_eq_norm f g).symm

/-- Generic form of characterwise approximation: the characters need only
have dense complex linear span in the continuous functions. -/
lemma tendsto_integral_of_mem_span_generic (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (μ n)] (χ : ι → C(T, ℂ))
    (hchar : ∀ i, ∀ᶠ n in atTop, ∫ x, χ i x ∂μ n = ∫ x, χ i x ∂ν)
    (f : C(T, ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range χ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact tendsto_const_nhds.congr' (hchar i |>.mono fun n hn => hn.symm)
  | zero => simp only [ContinuousMap.coe_zero, Pi.zero_apply, integral_zero,
      tendsto_const_nhds]
  | add x y hx hy ihx ihy =>
      simpa only [ContinuousMap.add_apply,
        integral_add (integrable_continuousMap_generic _ _)
          (integrable_continuousMap_generic _ _), add_zero] using ihx.add ihy
  | smul a x hx ih =>
      change Tendsto (fun n => ∫ y, a • x y ∂μ n) atTop (𝓝 (∫ y, a • x y ∂ν))
      simp_rw [integral_smul]
      exact ih.const_smul a

/-- Weak convergence against every continuous function, from convergence on a
uniformly dense family of characters. -/
theorem tendsto_integral_continuous_generic (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (μ n)] (χ : ι → C(T, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hchar : ∀ i, ∀ᶠ n in atTop, ∫ x, χ i x ∂μ n = ∫ x, χ i x ∂ν)
    (f : C(T, ℂ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcl : f ∈ (Submodule.span ℂ (Set.range χ)).topologicalClosure := by
    rw [hdense]
    exact Submodule.mem_top
  have hcl' : f ∈ closure ((Submodule.span ℂ (Set.range χ)) : Set C(T, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hcl' (ε / 4) (by positivity)
  have ht := tendsto_integral_of_mem_span_generic ν μ χ hchar g hg
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := dist_integral_le_dist_generic (μ n) f g
  have h2 := dist_integral_le_dist_generic ν g f
  have h3 := hN n hn
  rw [dist_eq_norm] at h1 h2 ⊢
  have h1' : ‖(∫ x, f x ∂μ n) - ∫ x, g x ∂μ n‖ < ε / 4 :=
    lt_of_le_of_lt h1 hfg
  have h2' : ‖(∫ x, g x ∂ν) - ∫ x, f x ∂ν‖ < ε / 4 := by
    apply lt_of_le_of_lt h2
    rwa [dist_comm]
  have h3' : ‖(∫ x, g x ∂μ n) - ∫ x, g x ∂ν‖ < ε / 4 := by
    simpa only [dist_eq_norm] using h3
  calc
    ‖(∫ x, f x ∂μ n) - ∫ x, f x ∂ν‖
        = ‖((∫ x, f x ∂μ n) - ∫ x, g x ∂μ n) +
          ((∫ x, g x ∂μ n) - ∫ x, g x ∂ν) +
          ((∫ x, g x ∂ν) - ∫ x, f x ∂ν)‖ := by congr 1; abel
    _ ≤ ‖(∫ x, f x ∂μ n) - ∫ x, g x ∂μ n‖ +
          ‖(∫ x, g x ∂μ n) - ∫ x, g x ∂ν‖ +
          ‖(∫ x, g x ∂ν) - ∫ x, f x ∂ν‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε / 4 + ε / 4 + ε / 4 := add_lt_add (add_lt_add h1' h3') h2'
    _ < ε := by linarith

end GenericCharacters

lemma integral_mFourier_volume {γ : d → ℤ} (hγ : γ ≠ 0) :
    ∫ x, UnitAddTorus.mFourier γ x = 0 := by
  have h := (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier) (-γ) 0
  have hneg : -γ ≠ 0 := neg_ne_zero.mpr hγ
  simp only [ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add, hneg, if_false] at h
  simpa using h

/-- Character integrals determine integrals of all finite Fourier polynomials. -/
lemma tendsto_integral_of_mem_span_mFourier (μ : ℕ → Measure (𝕋))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hchar : ∀ γ : d → ℤ, γ ≠ 0 →
      ∀ᶠ n in atTop, ∫ x, UnitAddTorus.mFourier γ x ∂μ n = 0)
    (f : C(𝕋, ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range UnitAddTorus.mFourier)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      by_cases hγ : γ = 0
      · subst γ
        simp [UnitAddTorus.mFourier_zero]
      · have hv := integral_mFourier_volume (d := d) hγ
        rw [hv]
        exact tendsto_const_nhds.congr' (hchar γ hγ |>.mono fun n hn => hn.symm)
  | zero => simp only [ContinuousMap.coe_zero, Pi.zero_apply, integral_zero,
      tendsto_const_nhds]
  | add x y hx hy ihx ihy =>
      simpa only [ContinuousMap.add_apply,
        integral_add (integrable_continuousMap _ _) (integrable_continuousMap _ _),
        add_zero] using ihx.add ihy
  | smul a x hx ih =>
      change Tendsto (fun n => ∫ y, a • x y ∂μ n) atTop (𝓝 (∫ y, a • x y))
      simp_rw [integral_smul]
      exact ih.const_smul a

/-- **Weak approximation from character integrals.**
For probability measures on the standard finite-dimensional torus, eventual
vanishing of every nontrivial character integral implies convergence of all
continuous integrals to normalized Haar integration. -/
theorem tendsto_integral_continuous (μ : ℕ → Measure (𝕋))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hchar : ∀ γ : d → ℤ, γ ≠ 0 →
      ∀ᶠ n in atTop, ∫ x, UnitAddTorus.mFourier γ x ∂μ n = 0)
    (f : C(𝕋, ℂ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcl : f ∈ (Submodule.span ℂ
      (Set.range (UnitAddTorus.mFourier (d := d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  have hcl' : f ∈ closure ((Submodule.span ℂ
      (Set.range (UnitAddTorus.mFourier (d := d)))) : Set C(𝕋, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hcl' (ε / 4) (by positivity)
  have ht := tendsto_integral_of_mem_span_mFourier μ hchar g hg
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := dist_integral_le_dist (μ n) f g
  have h2 := dist_integral_le_dist (volume : Measure (𝕋)) g f
  have h3 := hN n hn
  rw [dist_eq_norm] at h1 h2 ⊢
  have h1' : ‖(∫ x, f x ∂μ n) - ∫ x, g x ∂μ n‖ < ε / 4 :=
    lt_of_le_of_lt h1 hfg
  have h2' : ‖(∫ x, g x) - ∫ x, f x‖ < ε / 4 := by
    apply lt_of_le_of_lt h2
    rwa [dist_comm]
  have h3' : ‖(∫ x, g x ∂μ n) - ∫ x, g x‖ < ε / 4 := by
    simpa only [dist_eq_norm] using h3
  calc
    ‖(∫ x, f x ∂μ n) - ∫ x, f x‖
        = ‖((∫ x, f x ∂μ n) - ∫ x, g x ∂μ n) +
          ((∫ x, g x ∂μ n) - ∫ x, g x) +
          ((∫ x, g x) - ∫ x, f x)‖ := by congr 1; abel
    _ ≤ ‖(∫ x, f x ∂μ n) - ∫ x, g x ∂μ n‖ +
          ‖(∫ x, g x ∂μ n) - ∫ x, g x‖ +
          ‖(∫ x, g x) - ∫ x, f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε / 4 + ε / 4 + ε / 4 := add_lt_add (add_lt_add h1' h3') h2'
    _ < ε := by linarith

/-- **Density from characterwise approximation.**  If probability measures
`μ n` are concentrated on subgroups `G n` and every nonzero character integral
is eventually zero, then the union of the subgroups is dense. -/
theorem dense_iUnion_of_character_eventually_zero (G : ℕ → AddSubgroup (𝕋))
    (μ : ℕ → Measure (𝕋)) [∀ n, IsProbabilityMeasure (μ n)]
    (hsupp : ∀ n, μ n ((G n : Set (𝕋))ᶜ) = 0)
    (hchar : ∀ γ : d → ℤ, γ ≠ 0 →
      ∀ᶠ n in atTop, ∫ x, UnitAddTorus.mFourier γ x ∂μ n = 0) :
    Dense (⋃ n, (G n : Set (𝕋))) := by
  by_contra hd
  have hC : closure (⋃ n, (G n : Set (𝕋))) ≠ Set.univ := by
    intro htop
    exact hd ((dense_iff_closure_eq).2 htop)
  obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hC
  have hxC : x ∉ closure (⋃ n, (G n : Set (𝕋))) := hx
  obtain ⟨f, hfC, hfx, hf01⟩ := exists_continuous_zero_one_of_isClosed
    isClosed_closure (isClosed_singleton : IsClosed ({x} : Set (𝕋)))
    (Set.disjoint_singleton_right.mpr hxC)
  have hx1 : f x = 1 := hfx (Set.mem_singleton x)
  have hnonneg : 0 ≤ f := fun y => (hf01 y).1
  have hpos : 0 < ∫ y, f y :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace f) hnonneg (by rw [hx1]; norm_num)
  let fC : C(𝕋, ℂ) := ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hzero : ∀ n, ∫ y, fC y ∂μ n = 0 := by
    intro n
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null ?_ (hsupp n)
    intro y hy
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at hy
    intro hyG
    apply hy
    have hyC : y ∈ closure (⋃ n, (G n : Set (𝕋))) :=
      subset_closure (Set.mem_iUnion.mpr ⟨n, hyG⟩)
    have hy0 : f y = 0 := hfC hyC
    simp [fC, hy0]
  have hlim := tendsto_integral_continuous μ hchar fC
  have hlim0 : Tendsto (fun n => ∫ y, fC y ∂μ n) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hv : ∫ y, fC y = 0 := tendsto_nhds_unique hlim hlim0
  change (∫ y, (f y : ℂ)) = 0 at hv
  have hv' : ((∫ y, f y : ℝ) : ℂ) = 0 :=
    (integral_complex_ofReal (μ := (volume : Measure (𝕋))) (f := fun y => f y)).symm.trans hv
  have : ∫ y, f y = 0 := Complex.ofReal_inj.mp hv'
  linarith

/-- Haar orthogonality for a not-identically-one additive character. -/
lemma integral_eq_zero_of_add_character_ne_one {H : Type*}
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsAddLeftInvariant] (χ : H → ℂ)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) {g : H} (hg : χ g ≠ 1) :
    ∫ x, χ x ∂μ = 0 := by
  let I : ℂ := ∫ x, χ x ∂μ
  have heq : I = χ g * I := by
    calc
      I = ∫ x, χ (g + x) ∂μ := (integral_add_left_eq_self χ g).symm
      _ = ∫ x, χ g * χ x ∂μ := by simp_rw [hχ]
      _ = χ g * I := by exact integral_const_mul _ _
  have hz : (1 - χ g) * I = 0 := by
    dsimp only [I] at heq ⊢
    linear_combination heq
  rcases mul_eq_zero.mp hz with hc | hI
  · exact (hg (sub_eq_zero.mp hc).symm).elim
  · exact hI

lemma mFourier_add_apply (γ : d → ℤ) (x y : 𝕋) :
    UnitAddTorus.mFourier γ (x + y) =
      UnitAddTorus.mFourier γ x * UnitAddTorus.mFourier γ y := by
  simp [UnitAddTorus.mFourier, fourier_apply, smul_add, AddCircle.toCircle_add,
    Finset.prod_mul_distrib]

/-- Normalized Haar measure on a compact additive group. -/
noncomputable def compactHaar (H : Type*) [AddGroup H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H]
    [CompactSpace H] [Nonempty H] : Measure H :=
  Measure.addHaarMeasure ⊤

noncomputable instance compactHaar_isAddHaarMeasure (H : Type*) [AddGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H]
    [CompactSpace H] [Nonempty H] : (compactHaar H).IsAddHaarMeasure := by
  rw [compactHaar]
  infer_instance

noncomputable instance compactHaar_isProbability (H : Type*) [AddGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H]
    [CompactSpace H] [Nonempty H] : IsProbabilityMeasure (compactHaar H) := by
  apply IsProbabilityMeasure.mk
  rw [compactHaar, ← TopologicalSpace.PositiveCompacts.coe_top]
  exact Measure.addHaarMeasure_self

/-- The pushforward of normalized Haar measure on a compact subgroup. -/
noncomputable def subgroupMeasure (H : AddSubgroup (𝕋)) [CompactSpace H] : Measure (𝕋) :=
  Measure.map ((↑) : H → 𝕋) (compactHaar H)

noncomputable instance subgroupMeasure_isProbability (H : AddSubgroup (𝕋))
    [CompactSpace H] : IsProbabilityMeasure (subgroupMeasure H) :=
  Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable

lemma subgroupMeasure_compl (H : AddSubgroup (𝕋)) [CompactSpace H]
    (hH : IsClosed (H : Set (𝕋))) :
    subgroupMeasure H ((H : Set (𝕋))ᶜ) = 0 := by
  rw [subgroupMeasure, Measure.map_apply continuous_subtype_val.measurable
    hH.measurableSet.compl]
  have hempty : ((↑) : H → 𝕋) ⁻¹' (H : Set (𝕋))ᶜ = ∅ := by
    ext h
    simp
  rw [hempty, measure_empty]

lemma integral_mFourier_subgroupMeasure {H : AddSubgroup (𝕋)} [CompactSpace H]
    (γ : d → ℤ) (hγ : ∃ h ∈ H, UnitAddTorus.mFourier γ h ≠ 1) :
    ∫ x, UnitAddTorus.mFourier γ x ∂subgroupMeasure H = 0 := by
  obtain ⟨h, hh, hne⟩ := hγ
  rw [subgroupMeasure, integral_map continuous_subtype_val.measurable.aemeasurable
    (UnitAddTorus.mFourier γ).continuous.aestronglyMeasurable]
  apply integral_eq_zero_of_add_character_ne_one (g := (⟨h, hh⟩ : H)) (compactHaar H)
    (fun h : H => UnitAddTorus.mFourier γ (h : 𝕋))
  · intro x y
    exact mFourier_add_apply γ (x : 𝕋) (y : 𝕋)
  · exact hne

/-- **Berend's Lemma 4.7, density form.**  For closed subgroups `G n` of a
standard finite-dimensional torus, if every fixed nontrivial character is
nontrivial on `G n` for all sufficiently large `n`, then the union of the
subgroups is dense. -/
theorem dense_iUnion_of_character_nontrivial_eventually
    (G : ℕ → AddSubgroup (𝕋)) [∀ n, CompactSpace (G n)]
    (hG : ∀ n, IsClosed (G n : Set (𝕋)))
    (hchar : ∀ γ : d → ℤ, γ ≠ 0 → ∀ᶠ n in atTop,
      ∃ h ∈ G n, UnitAddTorus.mFourier γ h ≠ 1) :
    Dense (⋃ n, (G n : Set (𝕋))) := by
  apply dense_iUnion_of_character_eventually_zero G (fun n => subgroupMeasure (G n))
  · intro n
    exact subgroupMeasure_compl (G n) (hG n)
  · intro γ hγ
    filter_upwards [hchar γ hγ] with n hn
    exact integral_mFourier_subgroupMeasure γ hn

section GenericNet

variable {T ι : Type*} [MetricSpace T] [AddCommGroup T] [CompactSpace T]
  [MeasurableSpace T] [BorelSpace T]

/-- Characterwise approximation gives eventual intersection with a fixed
ball, for any character family with dense continuous-function span. -/
theorem eventually_exists_mem_ball_generic (ν : Measure T)
    [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    (μ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (μ n)] (χ : ι → C(T, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hchar : ∀ i, ∀ᶠ n in atTop, ∫ x, χ i x ∂μ n = ∫ x, χ i x ∂ν)
    (G : ℕ → AddSubgroup T) (hsupp : ∀ n, μ n ((G n : Set T)ᶜ) = 0)
    (q : T) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∃ y ∈ G n, dist q y < r := by
  obtain ⟨f, hfC, hfq, hf01⟩ := exists_continuous_zero_one_of_isClosed
    (Metric.isOpen_ball.isClosed_compl : IsClosed (Metric.ball q r)ᶜ)
    (isClosed_singleton : IsClosed ({q} : Set T))
    (Set.disjoint_singleton_right.mpr (by simp [Metric.mem_ball, hr]))
  have hq1 : f q = 1 := hfq (Set.mem_singleton q)
  have hnonneg : 0 ≤ f := fun y => (hf01 y).1
  have hpos : 0 < ∫ y, f y ∂ν :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace f) hnonneg (by rw [hq1]; norm_num)
  let fC : C(T, ℂ) :=
    ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hvol : (∫ y, fC y ∂ν) ≠ 0 := by
    intro hz
    change (∫ y, (f y : ℂ) ∂ν) = 0 at hz
    rw [integral_complex_ofReal] at hz
    have hz' : ∫ y, f y ∂ν = 0 := Complex.ofReal_inj.mp hz
    linarith
  have hlim := tendsto_integral_continuous_generic ν μ χ hdense hchar fC
  filter_upwards [hlim.eventually_ne hvol] with n hn
  by_contra hmiss
  push Not at hmiss
  apply hn
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  apply measure_mono_null ?_ (hsupp n)
  intro y hy
  simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hy
  intro hyG
  apply hy
  have hdist : r ≤ dist y q := by
    rw [dist_comm]
    exact hmiss y hyG
  have hyball : y ∉ Metric.ball q r := by
    simpa [Metric.mem_ball, not_lt] using hdist
  have hy0 : f y = 0 := hfC hyball
  simp [fC, hy0]

/-- Eventual epsilon-nets from convergence of integrals on a dense character
family. -/
theorem eventually_net_generic (ν : Measure T)
    [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    (μ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (μ n)] (χ : ι → C(T, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hchar : ∀ i, ∀ᶠ n in atTop, ∫ x, χ i x ∂μ n = ∫ x, χ i x ∂ν)
    (G : ℕ → AddSubgroup T) (hsupp : ∀ n, μ n ((G n : Set T)ᶜ) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : T, ∃ y ∈ G n, dist x y < ε := by
  obtain ⟨t, _htsub, htfin, htcover⟩ := finite_cover_balls_of_compact
    (s := (Set.univ : Set T)) isCompact_univ (half_pos hε)
  have hballs : ∀ᶠ n in atTop, ∀ q ∈ t, ∃ y ∈ G n, dist q y < ε / 2 :=
    htfin.eventually_all.mpr fun q _hq =>
      eventually_exists_mem_ball_generic ν μ χ hdense hchar G hsupp q (half_pos hε)
  filter_upwards [hballs] with n hn x
  have hx : x ∈ ⋃ q ∈ t, Metric.ball q (ε / 2) := htcover (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨q, hqt, hxq⟩ := hx
  obtain ⟨y, hyG, hqy⟩ := hn q hqt
  refine ⟨y, hyG, ?_⟩
  calc
    dist x y ≤ dist x q + dist q y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxq hqy
    _ = ε := add_halves ε

/-- A single sufficiently large index gives an arbitrarily fine net. -/
theorem exists_net_generic (ν : Measure T)
    [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    (μ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (μ n)] (χ : ι → C(T, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hchar : ∀ i, ∀ᶠ n in atTop, ∫ x, χ i x ∂μ n = ∫ x, χ i x ∂ν)
    (G : ℕ → AddSubgroup T) (hsupp : ∀ n, μ n ((G n : Set T)ᶜ) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : T, ∃ y ∈ G n, dist x y < ε :=
  (eventually_net_generic ν μ χ hdense hchar G hsupp hε).exists

end GenericNet

end BerendTorusCharacters
