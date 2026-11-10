/-
# Density in finite-dimensional real spaces and integral functionals
-/
import CubicTwoStage.BerendCoordDense

namespace BerendDensity

open Set Filter Topology
open scoped Pointwise

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Separation for an arbitrary closed proper subgroup of a finite-dimensional
real normed space, in `AddSubgroup` form. -/
theorem exists_nonzero_integral_functional_of_not_dense
    {W : Submodule ℝ E} {L : AddSubgroup E}
    (hnd : ¬ Dense ((W : Set E) + (L : Set E))) :
    ∃ k : E →ₗ[ℝ] ℝ, k ≠ 0 ∧
      (∀ w ∈ W, k w = 0) ∧ (∀ l ∈ L, ∃ m : ℤ, k l = m) := by
  let H : AddSubgroup E := (W.toAddSubgroup ⊔ L).topologicalClosure
  have hsub : ∀ x ∈ (W : Set E) + (L : Set E), x ∈ H := by
    intro x hx
    obtain ⟨w, hw, l, hl, rfl⟩ := hx
    exact AddSubgroup.le_topologicalClosure _ (AddSubgroup.add_mem_sup hw hl)
  have hHne : H ≠ ⊤ := by
    intro htop
    apply hnd
    rw [dense_iff_closure_eq]
    have hsupset : (↑(W.toAddSubgroup ⊔ L) : Set E) = (W : Set E) + (L : Set E) := by
      ext x
      exact AddSubgroup.mem_sup
    have hcarrier : (H : Set E) = closure ((W : Set E) + (L : Set E)) := by
      rw [← hsupset]
      exact AddSubgroup.topologicalClosure_coe (s := W.toAddSubgroup ⊔ L)
    rw [← hcarrier]
    exact congrArg (fun A : AddSubgroup E => (A : Set E)) htop
  obtain ⟨k, hkne, hkint⟩ :=
    BerendCoordDense.exists_integral_functional_of_isClosed E
      (AddSubgroup.isClosed_topologicalClosure _) hHne
  refine ⟨k, hkne, ?_, ?_⟩
  · intro w hw
    obtain ⟨m, hm⟩ := hkint w (hsub _ (by simpa using Set.add_mem_add hw L.zero_mem))
    by_cases hm0 : m = 0
    · rw [hm0] at hm
      exact_mod_cast hm
    · have hval : k (((2 * (m : ℤ) : ℝ)⁻¹) • (w : E)) = (1 / 2 : ℝ) := by
        rw [map_smul, smul_eq_mul, hm]
        field_simp
      have hnonint : k (((2 * (m : ℤ) : ℝ)⁻¹) • (w : E)) ∉ Set.range ((↑) : ℤ → ℝ) := by
        rw [hval]
        rintro ⟨n, hn⟩
        have hn' : (2 : ℝ) * (n : ℝ) = 1 := by linarith
        have hnz : (2 * n : ℤ) = 1 := by exact_mod_cast hn'
        omega
      have hwmem : ((2 * (m : ℤ) : ℝ)⁻¹) • (w : E) ∈ H :=
        hsub _ (by simpa using Set.add_mem_add (W.smul_mem (((2 * (m : ℤ) : ℝ)⁻¹)) hw) L.zero_mem)
      obtain ⟨n, hn⟩ := hkint _ hwmem
      exact (hnonint ⟨n, hn.symm⟩).elim
  · intro l hl
    exact hkint l (hsub _ (by simpa using Set.add_mem_add (Submodule.zero_mem W) hl))

/-- If a closed real subspace and a subgroup add up densely, a real-linear map
that kills the subspace and is integer-valued on the subgroup must be zero. -/
theorem eq_zero_of_dense {W : Submodule ℝ E} {L : AddSubgroup E}
    (hd : Dense ((W : Set E) + (L : Set E))) (k : E →ₗ[ℝ] ℝ)
    (hkW : ∀ w ∈ W, k w = 0) (hkL : ∀ l ∈ L, ∃ m : ℤ, k l = m) : k = 0 := by
  have hpre : (W : Set E) + (L : Set E) ⊆ k ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
    rintro x ⟨w, hw, l, hl, rfl⟩
    obtain ⟨m, hm⟩ := hkL l hl
    refine ⟨m, ?_⟩
    rw [map_add, hkW w hw, zero_add, hm]
  have hclosed : IsClosed (k ⁻¹' Set.range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isClosed_range.preimage
      (LinearMap.continuous_of_finiteDimensional k)
  have hall : ∀ x : E, k x ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro x
    have hx : x ∈ closure ((W : Set E) + (L : Set E)) := by
      rw [hd.closure_eq]
      exact Set.mem_univ x
    exact closure_minimal hpre hclosed hx
  by_contra hkne
  obtain ⟨x, hx⟩ := not_forall.mp (fun hzero => hkne (LinearMap.ext hzero))
  have hz : k ((2 * k x)⁻¹ • x) = (1 / 2 : ℝ) := by
    rw [map_smul, smul_eq_mul]
    calc
      (2 * k x)⁻¹ * k x = (2 : ℝ)⁻¹ * ((k x)⁻¹ * k x) := by ring
      _ = 1 / 2 := by rw [inv_mul_cancel₀ hx]; norm_num
  obtain ⟨m, hm⟩ := hall ((2 * k x)⁻¹ • x)
  rw [hz] at hm
  have hn : (2 * m : ℤ) = 1 := by
    have hm2 : (2 : ℝ) * (m : ℝ) = 1 := by linarith
    exact_mod_cast hm2
  omega

/-- Density of the sum of a real subspace and an additive subgroup is exactly
nonexistence of a nonzero real-linear functional vanishing on the subspace and
integer-valued on the subgroup. -/
theorem dense_iff_no_nonzero_integral_functional
    {W : Submodule ℝ E} {L : AddSubgroup E} :
    Dense ((W : Set E) + (L : Set E)) ↔
      ∀ k : E →ₗ[ℝ] ℝ,
        (∀ w ∈ W, k w = 0) → (∀ l ∈ L, ∃ m : ℤ, k l = m) → k = 0 := by
  constructor
  · intro hd k hkW hkL
    exact eq_zero_of_dense hd k hkW hkL
  · intro h
    by_contra hd
    obtain ⟨k, hkne, hkW, hkL⟩ := exists_nonzero_integral_functional_of_not_dense hd
    exact hkne (h k hkW hkL)

end BerendDensity
