/-
# Sharpness for *every* single dilation: `k •` alone never forces `univ`

`CubicTwoStage/BerendSharpness.lean` proves that Stage I
(`eq_univ_of_zero_nonisolated`) fails for the single doubling map.  This module
removes the special role of `2`: for **every** `k ≥ 2` the closed set

  `Y k = {0} ∪ {k⁻⁽ⁿ⁺¹⁾ : n : ℕ} ⊆ ℝ/ℤ`

is infinite, proper, closed, invariant under `k •`, and `0` is a non-isolated point
of it; every minimal closed `k •`-invariant subset of it is `{0}`, hence finite.

Consequences:

* `stage_one_single_map_false` — for every `k ≥ 2` there is a closed nonempty
  `E ⊊ univ` with `0` non-isolated and `k • E ⊆ E`.  So no single dilation, of any
  size, suffices for Stage I: the multiplicatively independent *family* in the
  hypotheses is essential, not an artefact of `k = 2`.
* `minimal_finite_but_infinite` — the amended plan §D.5 phenomenon for every
  `k ≥ 2`.

Axiom free: no `sorry`, no new axiom, `#print axioms` at the end.
-/
import CubicTwoStage.BerendSharpness

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendSharpGen

/-! ## 1. The `k`-dyadic sequence -/

/-- `e k n = k⁻⁽ⁿ⁺¹⁾` in the circle. -/
noncomputable def e (k : ℕ) : ℕ → (AddCircle (1 : ℝ)) := fun n => (↑(((k : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ)))

/-- `Y k = {0} ∪ {k⁻⁽ⁿ⁺¹⁾ : n : ℕ}`. -/
noncomputable def Y (k : ℕ) : Set (AddCircle (1 : ℝ)) := insert 0 (range (e k))

theorem mem_Y_iff {k : ℕ} {y : (AddCircle (1 : ℝ))} :
    y ∈ Y k ↔ y = 0 ∨ ∃ n : ℕ, (↑(((k : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ))) = y := Iff.rfl

/-- The `k`-dyadic sequence tends to `0` for `k > 1`. -/
theorem tendsto_e {k : ℕ} (hk : 1 < k) : Tendsto (e k) atTop (𝓝 (0 : (AddCircle (1 : ℝ)))) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hpow : Tendsto (fun n : ℕ => (k : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hkR).comp (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun n : ℕ => (((k : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hcont : Continuous (fun x : ℝ => ((x : (AddCircle (1 : ℝ))))) := QuotientAddGroup.continuous_mk
  have hco : Tendsto (fun x : ℝ => ((x : (AddCircle (1 : ℝ))))) (𝓝 0) (𝓝 (0 : (AddCircle (1 : ℝ)))) := by
    have h0 := hcont.tendsto (0 : ℝ)
    rwa [AddCircle.coe_zero] at h0
  exact hco.comp hu

/-- **`Y k` is closed** for `k > 1`. -/
theorem Y_closed {k : ℕ} (hk : 1 < k) : IsClosed (Y k) :=
  BerendSharpness.isClosed_insert_range (tendsto_e hk)

/-- **`0` is a non-isolated point of `Y k`** for `k > 1`. -/
theorem zero_nonisolated {k : ℕ} (hk : 1 < k) : (0 : (AddCircle (1 : ℝ))) ∈ closure (Y k \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, (e k n) ∈ Metric.ball (0 : (AddCircle (1 : ℝ))) ε :=
    (tendsto_e hk).eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hne : e k n ≠ 0 := by
    intro hzero
    have hmem : (↑(((k : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ))) = 0 := hzero
    rw [AddCircle.coe_eq_zero_iff] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hz' : ((z : ℤ) : ℝ) = ((k : ℝ) ^ (n + 1))⁻¹ := by simpa using hz
    have hpos : (0 : ℝ) < (k : ℝ) ^ (n + 1) := by positivity
    have hone : (1 : ℝ) < (k : ℝ) ^ (n + 1) := by
      have h2 : (k : ℝ) ≤ (k : ℝ) ^ (n + 1) := by
        simpa using pow_le_pow_right₀ (le_of_lt hkR) (Nat.succ_le_succ (Nat.zero_le n))
      linarith
    have hlt : ((k : ℝ) ^ (n + 1))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact hone
    have hzpos : (0 : ℝ) < ((z : ℤ) : ℝ) := by rw [hz']; positivity
    have hz1z : (1 : ℤ) ≤ z := by
      have h0 : (0 : ℤ) < z := by exact_mod_cast hzpos
      omega
    have hz1 : (1 : ℝ) ≤ ((z : ℤ) : ℝ) := by exact_mod_cast hz1z
    rw [hz'] at hz1
    linarith
  refine ⟨e k n, ⟨?_, hne⟩, ?_⟩
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩)
  · simpa [Metric.mem_ball, dist_comm] using hn

/-- **`Y k` is infinite** (closed, with `0` non-isolated). -/
theorem Y_infinite {k : ℕ} (hk : 1 < k) : (Y k).Infinite := by
  intro hfin
  have hclosed : IsClosed (Y k \ {0}) := hfin.sdiff.isClosed
  have hc : closure (Y k \ {0}) = Y k \ {0} := hclosed.closure_eq
  have hmem : (0 : (AddCircle (1 : ℝ))) ∈ Y k \ {0} := hc ▸ zero_nonisolated hk
  simpa using hmem

/-- **`Y k` is proper.**  It is countable while the circle is not. -/
theorem Y_proper (k : ℕ) : Y k ≠ univ := by
  intro h
  have hc : (univ : Set (AddCircle (1 : ℝ))).Countable := by
    rw [← h]
    exact (Set.countable_range (e k)).insert 0
  exact BerendSharpness.not_countable_circle (Set.countable_univ_iff.mp hc)

/-! ## 2. Invariance under `k •` -/

theorem nsmul_coe_gen (m : ℕ) (x : ℝ) :
    m • ((x : (AddCircle (1 : ℝ)))) = (((m : ℝ) * x : ℝ) : (AddCircle (1 : ℝ))) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]

/-- `k • k⁻⁽ⁿ⁺¹⁾ = k⁻ⁿ`. -/
theorem k_nsmul_dyadic {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (k : ℝ) * (((k : ℝ) ^ (n + 1))⁻¹) = ((k : ℝ) ^ n)⁻¹ := by
  have h2 : (k : ℝ) ^ (n + 1) = k * (k : ℝ) ^ n := by
    rw [pow_succ]; ring
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul]

/-- **`Y k` is invariant under `k •`** for `k ≥ 2`. -/
theorem Y_invariant {k : ℕ} (hk : 2 ≤ k) : ∀ y ∈ Y k, k • y ∈ Y k := by
  have hk0 : 0 < k := by omega
  intro y hy
  rw [mem_Y_iff] at hy
  rcases hy with rfl | ⟨n, rfl⟩
  · rw [smul_zero]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · rw [nsmul_coe_gen, k_nsmul_dyadic hk0]
    rcases n with _ | j
    · have h1 : (((k : ℝ) ^ 0)⁻¹) = 1 := by norm_num
      rw [h1]
      have hzero : ((1 : ℝ) : (AddCircle (1 : ℝ))) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨1, by norm_num⟩
      rw [hzero]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨j, rfl⟩)

/-! ## 3. Minimal subsets are `{0}`, hence finite -/

/-- `k`-doubling a `k`-dyadic `n + 1` times gives `1 ≡ 0`. -/
theorem pow_nsmul_e {k : ℕ} (hk : 0 < k) (n : ℕ) : k ^ (n + 1) • e k n = 0 := by
  rw [show ((e k n) : (AddCircle (1 : ℝ))) = (↑(((k : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ))) from rfl, nsmul_coe_gen]
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨1, ?_⟩
  rw [one_smul]
  push_cast
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Every nonempty closed `k •`-invariant subset of `Y k` contains `0` (`k ≥ 2`). -/
theorem zero_mem_of_subset {k : ℕ} (hk : 2 ≤ k) (Z : Set (AddCircle (1 : ℝ))) (hZ : Z ⊆ Y k)
    (hne : Z.Nonempty) (hinv : ∀ z ∈ Z, k • z ∈ Z) : (0 : (AddCircle (1 : ℝ))) ∈ Z := by
  have hk0 : 0 < k := by omega
  obtain ⟨z, hz⟩ := hne
  rcases mem_Y_iff.mp (hZ hz) with h | ⟨n, rfl⟩
  · rwa [h] at hz
  · have hiter : ∀ m : ℕ, k ^ m • e k n ∈ Z := by
      intro m
      induction m with
      | zero => simpa [e] using hz
      | succ m ih =>
          rw [pow_succ, mul_nsmul]
          exact hinv _ ih
    have hfull : k ^ (n + 1) • e k n = 0 := pow_nsmul_e hk0 n
    rw [← hfull]
    exact hiter (n + 1)

/-- Every minimal nonempty closed `k •`-invariant subset of `Y k` is `{0}`. -/
theorem minimal_eq_singleton {k : ℕ} (hk : 2 ≤ k) (Z : Set (AddCircle (1 : ℝ))) (hZ : Z ⊆ Y k)
    (hne : Z.Nonempty) (hinv : ∀ z ∈ Z, k • z ∈ Z)
    (hmin : ∀ W : Set (AddCircle (1 : ℝ)), W ⊆ Z → IsClosed W → W.Nonempty →
      (∀ z ∈ W, k • z ∈ W) → W = Z) :
    Z = {0} := by
  have h0 : (0 : (AddCircle (1 : ℝ))) ∈ Z := zero_mem_of_subset hk Z hZ hne hinv
  have hsub : ({0} : Set (AddCircle (1 : ℝ))) ⊆ Z := singleton_subset_iff.mpr h0
  have hinv0 : ∀ z ∈ ({0} : Set (AddCircle (1 : ℝ))), k • z ∈ ({0} : Set (AddCircle (1 : ℝ))) := by
    intro z hz
    rw [mem_singleton_iff] at hz ⊢
    rw [hz, smul_zero]
  exact (hmin {0} hsub isClosed_singleton (singleton_nonempty 0) hinv0).symm

/-! ## 4. The refutations for an arbitrary single dilation -/

/-- **Stage I fails for every single dilation `k ≥ 2`.** -/
theorem stage_one_single_map_false {k : ℕ} (hk : 2 ≤ k) :
    ¬ (∀ E : Set (AddCircle (1 : ℝ)), IsClosed E → E.Nonempty →
        (0 : (AddCircle (1 : ℝ))) ∈ closure (E \ {0}) → (∀ z ∈ E, k • z ∈ E) → E = univ) := by
  intro h
  have hY : Y k = univ :=
    h (Y k) (Y_closed (by omega)) ⟨0, Set.mem_insert_iff.mpr (Or.inl rfl)⟩
      (zero_nonisolated (by omega)) (Y_invariant hk)
  exact Y_proper k hY

/-- **The amended §D.5 phenomenon for every single dilation `k ≥ 2`.** -/
theorem minimal_finite_but_infinite {k : ℕ} (hk : 2 ≤ k) :
    IsClosed (Y k) ∧ (Y k).Infinite ∧ Y k ≠ univ ∧ (∀ z ∈ Y k, k • z ∈ Y k) ∧
      (0 : (AddCircle (1 : ℝ))) ∈ closure (Y k \ {0}) ∧
      (∀ Z : Set (AddCircle (1 : ℝ)), Z ⊆ Y k → Z.Nonempty → (∀ z ∈ Z, k • z ∈ Z) →
        (∀ W : Set (AddCircle (1 : ℝ)), W ⊆ Z → IsClosed W → W.Nonempty →
          (∀ z ∈ W, k • z ∈ W) → W = Z) → Z.Finite) :=
  ⟨Y_closed (by omega), Y_infinite (by omega), Y_proper k, Y_invariant hk,
    zero_nonisolated (by omega),
    fun Z hZ hn hi hm => by
      rw [minimal_eq_singleton hk Z hZ hn hi hm]
      exact finite_singleton 0⟩

/-! ## 5. `Y k - Y k ≠ univ` and the bundled summary for every `k ≥ 2` -/

/-- `Y k` is countable. -/
theorem Y_countable (k : ℕ) : (Y k).Countable :=
  (Set.countable_range (e k)).insert 0

/-- **`Y k - Y k` is not the whole circle**: `Y k` is countable, hence so is its
difference set, while the circle is not.  So the witness does not violate the
residual statement of amended §D.5. -/
theorem Y_diffSet_ne_univ (k : ℕ) : Y k - Y k ≠ univ := by
  intro h
  have hpair : (Y k ×ˢ Y k).Countable := (Y_countable k).prod (Y_countable k)
  have himg : Y k - Y k =
      (fun p : (AddCircle (1 : ℝ)) × (AddCircle (1 : ℝ)) => p.1 - p.2) ''
        (Y k ×ˢ Y k) := by
    rw [sub_image_prod]
  have hcount : (Y k - Y k).Countable := by
    rw [himg]
    exact Set.Countable.image hpair _
  have huniv : (univ : Set (AddCircle (1 : ℝ))).Countable := by
    rw [← h]
    exact hcount
  exact BerendSharpness.not_countable_circle (Set.countable_univ_iff.mp huniv)

/-- **The amended §D.5 sentence for an arbitrary single dilation `k ≥ 2`**, with
every clause machine-checked: `Y k` is closed, infinite, proper, `k •`-invariant,
`0` is a non-isolated point of it, every minimal closed `k •`-invariant subset of it
is finite, and its difference set is not the whole circle. -/
theorem counterexample_summary {k : ℕ} (hk : 2 ≤ k) :
    IsClosed (Y k) ∧ (Y k).Infinite ∧ Y k ≠ univ ∧ (∀ z ∈ Y k, k • z ∈ Y k) ∧
      (0 : AddCircle (1 : ℝ)) ∈ closure (Y k \ {0}) ∧ Y k - Y k ≠ univ ∧
      (∀ Z : Set (AddCircle (1 : ℝ)), Z ⊆ Y k → Z.Nonempty → (∀ z ∈ Z, k • z ∈ Z) →
        (∀ W : Set (AddCircle (1 : ℝ)), W ⊆ Z → IsClosed W → W.Nonempty →
          (∀ z ∈ W, k • z ∈ W) → W = Z) → Z.Finite) :=
  ⟨Y_closed (by omega), Y_infinite (by omega), Y_proper k, Y_invariant hk,
    zero_nonisolated (by omega), Y_diffSet_ne_univ k,
    fun Z hZ hn hi hm => by
      rw [minimal_eq_singleton hk Z hZ hn hi hm]
      exact finite_singleton 0⟩

end BerendSharpGen

end CubicTwoStage

/-! ## 5. Axiom audit -/

#print axioms CubicTwoStage.BerendSharpGen.Y_closed
#print axioms CubicTwoStage.BerendSharpGen.zero_nonisolated
#print axioms CubicTwoStage.BerendSharpGen.Y_infinite
#print axioms CubicTwoStage.BerendSharpGen.Y_proper
#print axioms CubicTwoStage.BerendSharpGen.Y_invariant
#print axioms CubicTwoStage.BerendSharpGen.minimal_eq_singleton
#print axioms CubicTwoStage.BerendSharpGen.stage_one_single_map_false
#print axioms CubicTwoStage.BerendSharpGen.minimal_finite_but_infinite


#print axioms CubicTwoStage.BerendSharpGen.Y_diffSet_ne_univ
#print axioms CubicTwoStage.BerendSharpGen.counterexample_summary
