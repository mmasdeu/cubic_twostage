/-
# Berend §4, Stage I: the radial flow forces `E = univ`
-/
import CubicTwoStage.BerendModulus

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendRadialFull

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The preimage in the linear model -/

section Preimage

/-- The preimage of a torus set `E ⊆ (ι → ℝ) ⧸ L` in the linear model. -/
def prec (L : AddSubgroup (ι → ℝ)) (E : Set ((ι → ℝ) ⧸ L)) : Set (ι → ℝ) :=
  QuotientAddGroup.mk' L ⁻¹' E

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)}

theorem mem_prec {x : ι → ℝ} : x ∈ prec L E ↔ QuotientAddGroup.mk' L x ∈ E := Iff.rfl

theorem continuous_mk' (L : AddSubgroup (ι → ℝ)) :
    Continuous (QuotientAddGroup.mk' L) := by
  simpa [QuotientAddGroup.mk'_apply] using
    (QuotientAddGroup.continuous_mk (N := L) : Continuous
      (QuotientAddGroup.mk : (ι → ℝ) → (ι → ℝ) ⧸ L))

theorem isClosed_prec (hE : IsClosed E) : IsClosed (prec L E) :=
  hE.preimage (continuous_mk' L)

theorem prec_nonempty (hE : E.Nonempty) : (prec L E).Nonempty := by
  obtain ⟨y, hy⟩ := hE
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  exact ⟨x, hy⟩

/-- **Lattice saturation.** -/
theorem prec_add_mem {x ℓ : ι → ℝ} (hx : x ∈ prec L E) (hℓ : ℓ ∈ L) :
    x + ℓ ∈ prec L E := by
  have h : QuotientAddGroup.mk' L (x + ℓ) = QuotientAddGroup.mk' L x := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem]
    simpa using hℓ
  show QuotientAddGroup.mk' L (x + ℓ) ∈ E
  rw [h]
  exact hx

/-- The preimage is everything exactly when the set is. -/
theorem prec_eq_univ_iff : prec L E = univ ↔ E = univ := by
  constructor
  · intro h
    have hsurj : Function.Surjective (QuotientAddGroup.mk' L) :=
      QuotientAddGroup.mk'_surjective L
    have himg : E = QuotientAddGroup.mk' L '' (prec L E) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hsurj y
        exact ⟨x, hy, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [himg, h]
    simp
  · intro h
    rw [h]
    exact preimage_univ

end Preimage

/-! ## 2. Collapsing the flow at `s → 0` -/

section Collapse

variable {X : Set (ι → ℝ)} {S : Set ι} {w : ι → ℕ}

/-- The point obtained from `x` by collapsing the coordinates of `S` to `0`. -/
noncomputable def collapse (S : Set ι) (x : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ S then 0 else x i

theorem collapse_apply_of_mem {x : ι → ℝ} {i : ι} (hi : i ∈ S) : collapse S x i = 0 := by
  classical
  simp [collapse, hi]

theorem collapse_apply_of_not_mem {x : ι → ℝ} {i : ι} (hi : i ∉ S) :
    collapse S x i = x i := by
  classical
  simp [collapse, hi]

/-- **The radial flow collapses to `0` on its support.** -/
theorem flow_limit_mem (hX : IsClosed X)
    (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    (hflow : ∀ x ∈ X, ∀ s : ℝ, 0 < s → (fun i => s ^ (w i) * x i) ∈ X)
    {x : ι → ℝ} (hx : x ∈ X) : collapse S x ∈ X := by
  classical
  refine hX.mem_of_tendsto (f := fun s : ℝ => fun i => s ^ (w i) * x i)
    (b := 𝓝[>] (0 : ℝ)) ?_ ?_
  · rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i ∈ S
    · have hpos : 0 < w i := hwS i hi
      have hne : w i ≠ 0 := hpos.ne'
      have h1 : Tendsto (fun s : ℝ => s ^ (w i)) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ (w i))) :=
        ((continuousAt_id.pow (w i)).tendsto).mono_left nhdsWithin_le_nhds
      rw [zero_pow hne] at h1
      have h2 : Tendsto (fun s : ℝ => s ^ (w i) * x i) (𝓝[>] (0 : ℝ)) (𝓝 (0 * x i)) :=
        h1.mul_const (x i)
      have h3 : (0 : ℝ) * x i = collapse S x i := by
        rw [collapse_apply_of_mem hi, zero_mul]
      rw [h3] at h2
      exact h2
    · have hz : w i = 0 := hw0 i hi
      have hconst : ∀ s : ℝ, s ^ (w i) * x i = x i := by
        intro s
        rw [hz, pow_zero, one_mul]
      have : Tendsto (fun s : ℝ => s ^ (w i) * x i) (𝓝[>] (0 : ℝ)) (𝓝 (x i)) := by
        simpa only [hconst] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => x i) (𝓝[>] (0 : ℝ)) (𝓝 (x i)))
      rwa [collapse_apply_of_not_mem hi]
  · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ))] with s hs
    exact hflow x hx s hs

end Collapse

/-! ## 3. The slab over the complement of the support -/

section Slab

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)}

/-- **The slab.** -/
theorem slab_mem (hE : IsClosed E) {S : Set ι} {w : ι → ℕ}
    (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    (hflow : ∀ x ∈ prec L E, ∀ s : ℝ, 0 < s →
      (fun i => s ^ (w i) * x i) ∈ prec L E)
    (hden : ∀ (v : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε)
    (hne : (prec L E).Nonempty) {y : ι → ℝ} (hy : ∀ i ∈ S, y i = 0) :
    y ∈ prec L E := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hcollapse' : ∀ ℓ ∈ L, collapse S (x + ℓ) ∈ prec L E := by
    intro ℓ hℓ
    exact flow_limit_mem (isClosed_prec hE) hwS hw0 hflow (prec_add_mem hx hℓ)
  rw [← (isClosed_prec hE).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ℓ, hℓ, hclose⟩ := hden (fun i => y i - collapse S x i) ε hε
  refine ⟨collapse S (x + ℓ), hcollapse' ℓ hℓ, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq]
  by_cases hi : i ∈ S
  · rw [hy i hi, collapse_apply_of_mem hi, sub_zero, abs_zero]
    exact hε
  · rw [collapse_apply_of_not_mem hi, Pi.add_apply]
    have h := hclose i hi
    rw [collapse_apply_of_not_mem hi] at h
    have heq : y i - (x i + ℓ i) = y i - x i - ℓ i := by ring
    rw [heq]
    exact h

end Slab

/-! ## 4. Stage I under the radial flow -/

section Main

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)}

/-- **Stage I, radial-flow form.** -/
theorem eq_univ_of_flow (hE : IsClosed E) (hne : E.Nonempty)
    {S : Set ι} {w : ι → ℕ} (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    (hflow : ∀ x ∈ prec L E, ∀ s : ℝ, 0 < s →
      (fun i => s ^ (w i) * x i) ∈ prec L E)
    (hdenS : ∀ (v : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |v i - ℓ i| < ε)
    (hdenSc : ∀ (v : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε) :
    E = univ := by
  classical
  have hne' : (prec L E).Nonempty := prec_nonempty hne
  have hprec : prec L E = univ := by
    refine eq_univ_of_forall fun y => ?_
    rw [← (isClosed_prec hE).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨ℓ, hℓ, hclose⟩ := hdenS y ε hε
    have hslab : (fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) ∈ prec L E := by
      refine slab_mem hE hwS hw0 hflow hdenSc hne' (fun i hi => ?_)
      simp [hi]
    have hadd : (fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ ∈ prec L E :=
      prec_add_mem hslab hℓ
    refine ⟨(fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ, hadd, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    by_cases hi : i ∈ S
    · have h1 : ((fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ) i = ℓ i := by
        simp [hi]
      rw [h1]
      exact hclose i hi
    · have h1 : ((fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ) i = y i := by
        simp [hi]
      rw [h1, sub_self, abs_zero]
      exact hε
  exact prec_eq_univ_iff.mp hprec

end Main

/-! ## 5. The assembled form -/

section Radial

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)}

/-- **Stage I from two multiplicatively independent weighted dilations.** -/
theorem eq_univ_of_radial (hE : IsClosed E) (hne : E.Nonempty)
    {S : Set ι} {w : ι → ℕ} (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : BerendModulus.MulIndep c d)
    (hinv1 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => c ^ w i) x ∈ prec L E)
    (hinv2 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => d ^ w i) x ∈ prec L E)
    (hdenS : ∀ (v : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |v i - ℓ i| < ε)
    (hdenSc : ∀ (v : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε) :
    E = univ := by
  refine eq_univ_of_flow hE hne hwS hw0 ?_ hdenS hdenSc
  intro x hx s hs
  exact BerendModulus.radial_flow_mem_of_indep (isClosed_prec hE) hc hd0 hd1 hind
    hinv1 hinv2 hx hs

end Radial

/-! ## 6. Axiom audit -/

#print axioms CubicTwoStage.BerendRadialFull.flow_limit_mem
#print axioms CubicTwoStage.BerendRadialFull.slab_mem
#print axioms CubicTwoStage.BerendRadialFull.eq_univ_of_flow
#print axioms CubicTwoStage.BerendRadialFull.eq_univ_of_radial

end BerendRadialFull
end CubicTwoStage
