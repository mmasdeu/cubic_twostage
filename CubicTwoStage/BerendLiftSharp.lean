/-
# The lift of the dyadic witness: C4's cone step needs the whole family

`CubicTwoStage/BerendSharpness.lean` shows that Stage I fails on the circle for a
single dilation.  In Berend §4 the set under consideration does *not* live on the
circle however: it is a lift, so it is periodic with the lattice and closed in `ℝ^d`.
This module shows that the periodic lift of the dyadic witness has exactly the
properties plan §C.4 asks for — closed, lattice-periodic, doubling-invariant, `0`
non-isolated, and (with `k = 2`) accumulating at `0` inside the only coordinate
subspace — while having **empty interior**.  Hence

  closed + lattice-periodic + invariant under one expanding map + `0` non-isolated

does *not* give a point of `E` in a nonempty open subset of the invariant subspace:
C4's conclusion needs the whole multiplicatively independent family, not just the
single uniformly expanding member produced by
`BerendSec4.exists_minimal_and_expanding`.

Main results:

* `Ef : Set ℝ` — the `ℤ`-periodic lift `⋃_{m : ℤ} (m + {0} ∪ {2⁻⁽ⁿ⁺¹⁾})`;
* `Ef_closed`, `Ef_periodic`, `Ef_invariant`, `Ef_zero_nonisolated`,
  `Ef_interior_empty`;
* `E1 : Set (Fin 1 → ℝ)` — the same set in the diagonalized model of
  `BerendSec4` (`ι = Fin 1`), with `E1_closed`, `E1_acc` (Berend's `Acc`),
  `E1_invariant` (`diag (fun _ => 2)`), `E1_interior_empty`, and the refutation
  `cone_step_single_map_false`.

Axiom free: imports `CubicTwoStage.BerendSec4` and
`CubicTwoStage.BerendSharpness`; no `sorry`, no new axiom.
-/
import CubicTwoStage.BerendSec4
import CubicTwoStage.BerendSharpness

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendLiftSharp

/-! ## 1. An irrationality helper -/

/-- Adding a rational to an irrational number keeps it irrational. -/
theorem irrational_add_rat {x : ℝ} (hx : Irrational x) (q : ℚ) : Irrational (x + q) := by
  rintro ⟨r, hr⟩
  refine hx ⟨r - q, ?_⟩
  have h1 : ((r : ℚ) : ℝ) = x + (q : ℝ) := hr
  have h2 : (((r - q : ℚ)) : ℝ) = (r : ℝ) - (q : ℝ) := by push_cast; ring
  rw [h2]
  linarith

/-! ## 2. The periodic lift in `ℝ` -/

/-- The `ℤ`-periodic lift of `BerendSharpness.Y`: all integer translates of the
dyadic points `2⁻⁽ⁿ⁺¹⁾`, plus all integers. -/
def Ef : Set ℝ :=
  {x : ℝ | ∃ m : ℤ, ∃ n : ℕ, x = (m : ℝ) + ((2 : ℝ) ^ (n + 1))⁻¹} ∪
    (Set.range (fun z : ℤ => (z : ℝ)))

theorem mem_Ef_iff {x : ℝ} :
    x ∈ Ef ↔ (∃ m : ℤ, ∃ n : ℕ, x = (m : ℝ) + ((2 : ℝ) ^ (n + 1))⁻¹) ∨
      ∃ z : ℤ, (z : ℝ) = x := Iff.rfl

/-- The lift is the preimage of the circle witness `Y`. -/
theorem Ef_eq_preimage :
    Ef = (fun x : ℝ => ((x : (AddCircle (1 : ℝ))))) ⁻¹' BerendSharpness.Y := by
  ext x
  constructor
  · rintro (⟨m, n, rfl⟩ | ⟨z, rfl⟩)
    · -- an integer shift disappears in the circle
      simp only [Set.mem_preimage]
      have hint : (((m : ℝ)) : (AddCircle (1 : ℝ))) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨m, by norm_num⟩
      have hcoe : ((↑((m : ℝ) + ((2 : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ))))
          = (↑(((2 : ℝ) ^ (n + 1))⁻¹) : (AddCircle (1 : ℝ))) := by
        rw [AddCircle.coe_add, hint, zero_add]
      rw [hcoe]
      exact Set.mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩)
    · simp only [Set.mem_preimage]
      have hint : (((z : ℝ)) : (AddCircle (1 : ℝ))) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨z, by norm_num⟩
      rw [hint]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · intro hx
    simp only [Set.mem_preimage] at hx
    rw [BerendSharpness.mem_Y_iff] at hx
    rcases hx with h | ⟨n, hn⟩
    · -- the class is `0`: `x` is an integer
      have h0 : ((x : ℝ) : (AddCircle (1 : ℝ))) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h0
      obtain ⟨z, hz⟩ := h0
      refine Or.inr ⟨z, ?_⟩
      simpa using hz
    · -- the class is that of a dyadic: `x` is an integer translate of it
      have hsub : x - ((2 : ℝ) ^ (n + 1))⁻¹ ∈ AddSubgroup.zmultiples (1 : ℝ) := by
        have heq : ((x : ℝ) : (AddCircle (1 : ℝ))) =
            ((((2 : ℝ) ^ (n + 1))⁻¹ : ℝ) : (AddCircle (1 : ℝ))) := hn.symm
        exact QuotientAddGroup.eq_iff_sub_mem.mp heq
      rw [AddSubgroup.mem_zmultiples_iff] at hsub
      obtain ⟨m, hm⟩ := hsub
      refine Or.inl ⟨m, n, ?_⟩
      have hm' : (m : ℝ) = x - ((2 : ℝ) ^ (n + 1))⁻¹ := by simpa using hm
      linarith [hm']

/-- **The lift is closed.** -/
theorem Ef_closed : IsClosed Ef := by
  rw [Ef_eq_preimage]
  exact BerendSharpness.Y_closed.preimage QuotientAddGroup.continuous_mk

/-- **The lift is `ℤ`-periodic.** -/
theorem Ef_periodic (x : ℝ) : x ∈ Ef ↔ x + 1 ∈ Ef := by
  rw [Ef_eq_preimage] at *
  constructor
  · intro h
    simp only [Set.mem_preimage] at h ⊢
    have hcoe : ((↑(x + 1) : (AddCircle (1 : ℝ)))) = ((x : (AddCircle (1 : ℝ)))) := by
      rw [AddCircle.coe_add]
      have : ((1 : ℝ) : (AddCircle (1 : ℝ))) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]; exact ⟨1, by norm_num⟩
      rw [this, add_zero]
    rw [hcoe]
    exact h
  · intro h
    simp only [Set.mem_preimage] at h ⊢
    have hcoe : ((↑x : (AddCircle (1 : ℝ)))) = ((↑(x + 1) : (AddCircle (1 : ℝ)))) := by
      rw [AddCircle.coe_add]
      have : ((1 : ℝ) : (AddCircle (1 : ℝ))) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]; exact ⟨1, by norm_num⟩
      rw [this, add_zero]
    rw [hcoe]
    exact h

/-- **The lift is invariant under doubling.** -/
theorem Ef_invariant {x : ℝ} (hx : x ∈ Ef) : 2 * x ∈ Ef := by
  rw [Ef_eq_preimage] at hx ⊢
  simp only [Set.mem_preimage] at hx ⊢
  have hcoe : ((↑(2 * x) : (AddCircle (1 : ℝ)))) = (2 : ℕ) • ((x : (AddCircle (1 : ℝ)))) := by
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    norm_num
  rw [hcoe]
  exact BerendSharpness.Y_invariant _ hx

/-- **`0` is a non-isolated point of the lift.** -/
theorem Ef_zero_nonisolated : (0 : ℝ) ∈ closure (Ef \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ < ε := by
    have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hu : Tendsto (fun n : ℕ => (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hpow
    have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ (n + 1))⁻¹ < ε :=
      hu.eventually (eventually_lt_nhds hε)
    exact Filter.Eventually.exists hev
  refine ⟨((2 : ℝ) ^ (n + 1))⁻¹, ⟨?_, ?_⟩, ?_⟩
  · exact mem_Ef_iff.mpr (Or.inl ⟨0, n, by norm_num⟩)
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
    exact inv_ne_zero (ne_of_gt hpos)
  · have hv : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
    rw [dist_zero_left, Real.norm_eq_abs, abs_of_pos hv]
    exact hn

/-- Every point of the lift is rational. -/
theorem Ef_subset_rat {x : ℝ} (hx : x ∈ Ef) : ∃ q : ℚ, x = (q : ℝ) := by
  rcases mem_Ef_iff.mp hx with ⟨m, n, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨m + ((2 : ℚ) ^ (n + 1))⁻¹, ?_⟩
    push_cast
    ring
  · exact ⟨z, by push_cast; ring⟩

/-- **The lift has empty interior**: it consists of rationals only. -/
theorem Ef_interior_empty : interior Ef = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxE : x ∈ Ef := interior_subset hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨q, rfl⟩ := Ef_subset_rat hxE
  -- an irrational point as close to `x` as we like
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧ Real.sqrt 2 / N < ε := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    obtain ⟨M, hM⟩ := exists_nat_gt (Real.sqrt 2 / ε)
    refine ⟨M + 1, Nat.succ_pos M, ?_⟩
    have hNpos' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hNpos']
    have hlt : Real.sqrt 2 / ε < (M : ℝ) + 1 := by
      have : (M : ℝ) < (M : ℝ) + 1 := by linarith
      linarith
    have h2 : Real.sqrt 2 = (Real.sqrt 2 / ε) * ε := by field_simp
    have h3 : (Real.sqrt 2 / ε) * ε < ((M : ℝ) + 1) * ε :=
      mul_lt_mul_of_pos_right hlt hε
    push_cast
    linarith [h2, h3]
  have hδirr : Irrational (Real.sqrt 2 / N) :=
    Irrational.div_natCast irrational_sqrt_two (by omega)
  have hyirr : Irrational ((q : ℝ) + Real.sqrt 2 / N) :=
    (by simpa [add_comm] using irrational_add_rat hδirr q)
  have hyE : ((q : ℝ) + Real.sqrt 2 / N) ∉ Ef := by
    intro hmem
    obtain ⟨q', hq'⟩ := Ef_subset_rat hmem
    exact hyirr ⟨q', by push_cast; linarith [hq']⟩
  refine hyE (hball ?_)
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
  have hval : (q : ℝ) + Real.sqrt 2 / N - (q : ℝ) = Real.sqrt 2 / N := by ring
  rw [hval, abs_of_pos (by positivity)]
  exact hN

/-! ## 3. The same witness in the diagonalized model of `BerendSec4` -/

open CubicTwoStage.BerendSec4

/-- The witness in the diagonalized model `Fin 1 → ℝ` (a single coordinate). -/
def E1 : Set (Fin 1 → ℝ) := {x | x 0 ∈ Ef}

/-- **`E1` is closed.** -/
theorem E1_closed : IsClosed E1 :=
  Ef_closed.preimage (continuous_apply 0)

/-- The `ε`-form of Berend's `Acc` for a nonnegative `ε`: the definitional unfolding
used below. -/
theorem acc_univ_iff {E : Set (Fin 1 → ℝ)} :
    Acc E Finset.univ ↔ ∀ ε > 0, ∃ u : Fin 1 → ℝ, u ∈ E ∧ u ≠ 0 ∧ ‖u‖ < ε := by
  rw [acc_iff]
  constructor
  · intro h ε hε
    obtain ⟨u, huE, -, hune, hult⟩ := h ε hε
    exact ⟨u, huE, hune, hult⟩
  · intro h ε hε
    obtain ⟨u, huE, hune, hult⟩ := h ε hε
    exact ⟨u, huE, fun i hi => absurd (Finset.mem_univ i) hi, hune, hult⟩

/-- **`0` is an accumulation point of `E1` in Berend's sense** (`Acc E1 univ`). -/
theorem E1_acc : Acc E1 Finset.univ := by
  rw [acc_univ_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ < ε := by
    have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hu : Tendsto (fun n : ℕ => (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hpow
    have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ (n + 1))⁻¹ < ε :=
      hu.eventually (eventually_lt_nhds hε)
    exact Filter.Eventually.exists hev
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  refine ⟨fun _ => ((2 : ℝ) ^ (n + 1))⁻¹, ?_, ?_, ?_⟩
  · show ((fun _ : Fin 1 => ((2 : ℝ) ^ (n + 1))⁻¹) 0) ∈ Ef
    exact mem_Ef_iff.mpr (Or.inl ⟨0, n, by norm_num⟩)
  · intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply] at h0
    exact absurd h0 (ne_of_gt hpos)
  · have hnorm : ‖(fun _ : Fin 1 => ((2 : ℝ) ^ (n + 1))⁻¹)‖ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
      refine le_antisymm ?_ ?_
      · rw [pi_norm_le_iff_of_nonneg (le_of_lt hpos)]
        intro i
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using le_rfl
      · have h := norm_le_pi_norm (fun _ : Fin 1 => ((2 : ℝ) ^ (n + 1))⁻¹) 0
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using h
    rw [hnorm]
    exact hn

/-- **`E1` is invariant under `diag (fun _ => 2)`.** -/
theorem E1_invariant {x : Fin 1 → ℝ} (hx : x ∈ E1) :
    diag (fun _ : Fin 1 => (2 : ℝ)) x ∈ E1 := by
  show (diag (fun _ : Fin 1 => (2 : ℝ)) x) 0 ∈ Ef
  rw [diag_apply]
  exact Ef_invariant hx

/-- **`E1` has empty interior.** -/
theorem E1_interior_empty : interior E1 = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxE : x ∈ E1 := interior_subset hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨q, hq⟩ := Ef_subset_rat hxE
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧ Real.sqrt 2 / N < ε := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    obtain ⟨M, hM⟩ := exists_nat_gt (Real.sqrt 2 / ε)
    refine ⟨M + 1, Nat.succ_pos M, ?_⟩
    have hNpos' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hNpos']
    have hM1 : Real.sqrt 2 / ε < (M : ℝ) + 1 := by
      have : (M : ℝ) < (M : ℝ) + 1 := by linarith
      linarith
    have h2 : Real.sqrt 2 = (Real.sqrt 2 / ε) * ε := by field_simp
    have h3 : (Real.sqrt 2 / ε) * ε < ((M : ℝ) + 1) * ε :=
      mul_lt_mul_of_pos_right hM1 hε
    push_cast
    linarith [h2, h3]
  have hδirr : Irrational (Real.sqrt 2 / N) :=
    Irrational.div_natCast irrational_sqrt_two (by omega)
  have hyirr : Irrational ((q : ℝ) + Real.sqrt 2 / N) :=
    (by simpa [add_comm] using irrational_add_rat hδirr q)
  set y : Fin 1 → ℝ := fun _ => (q : ℝ) + Real.sqrt 2 / N with hydef
  have hyE : y ∉ E1 := by
    intro hmem
    obtain ⟨q', hq'⟩ := Ef_subset_rat (x := y 0) hmem
    exact hyirr ⟨q', by simpa [hydef] using hq'.symm⟩
  refine hyE (hball ?_)
  rw [Metric.mem_ball]
  have hle : dist y x ≤ Real.sqrt 2 / N := by
    rw [dist_pi_le_iff (le_of_lt (by positivity : (0:ℝ) < Real.sqrt 2 / N))]
    intro i
    rw [Real.dist_eq]
    have hzero : y i - x i = Real.sqrt 2 / N := by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simp only [hydef]
      rw [← hq]
      ring
    rw [hzero, abs_of_pos (by positivity)]
  linarith [hle, hN]

/-- **C4's cone conclusion fails for a single expanding map.**  There is a closed
set `E ⊆ ℝ¹` (the lift of the dyadic witness, hence lattice-periodic), of which `0`
is an accumulation point in Berend's `Acc` sense, invariant under the expanding
`diag (fun _ => 2)`, that contains **no** nonempty open set.

So the conclusion of plan §C.4 ("a point of `E` in a nonempty open subset of the
selected invariant subspace") cannot be derived from the hypotheses delivered by
`BerendSec4.exists_minimal_and_expanding`: the whole multiplicatively independent
family is needed, not just one expanding member. -/
theorem cone_step_single_map_false :
    ¬ (∀ E : Set (Fin 1 → ℝ), IsClosed E → Acc E Finset.univ →
        (∀ x ∈ E, diag (fun _ : Fin 1 => (2 : ℝ)) x ∈ E) →
        ∃ U : Set (Fin 1 → ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ E) := by
  intro h
  obtain ⟨U, hUopen, ⟨y, hyU⟩, hUE⟩ :=
    h E1 E1_closed E1_acc (fun x hx => E1_invariant hx)
  have hsub : U ⊆ interior E1 := interior_maximal hUE hUopen
  have hmem : y ∈ interior E1 := hsub hyU
  rw [E1_interior_empty] at hmem
  exact absurd hmem (by simp)

/-! ## 4. The refutation in every nonempty dimension (in particular the project's
`Fin 3 → ℝ`) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The witness in `ι → ℝ`: the lift of the dyadic set in the coordinate `i₀`. -/
def Emodel (i₀ : ι) : Set (ι → ℝ) := {x | x i₀ ∈ Ef}

theorem Emodel_closed (i₀ : ι) : IsClosed (Emodel i₀) :=
  Ef_closed.preimage (continuous_apply i₀)

/-- `0` is an accumulation point of `Emodel i₀` in Berend's `Acc` sense: the
constant sequence `n ↦ 2⁻⁽ⁿ⁺¹⁾` lies in it and tends to `0`. -/
theorem Emodel_acc (i₀ : ι) : Acc (Emodel i₀) Finset.univ := by
  rw [acc_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ < ε := by
    have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hu : Tendsto (fun n : ℕ => (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hpow
    have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ (n + 1))⁻¹ < ε :=
      hu.eventually (eventually_lt_nhds hε)
    exact Filter.Eventually.exists hev
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  refine ⟨fun _ => ((2 : ℝ) ^ (n + 1))⁻¹, ?_, ?_, ?_, ?_⟩
  · exact mem_Ef_iff.mpr (Or.inl ⟨0, n, by norm_num⟩)
  · intro i hi
    exact absurd (Finset.mem_univ i) hi
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h0 := congrFun h i
    exact absurd h0 (ne_of_gt hpos)
  · have hnorm : ‖(fun _ : ι => ((2 : ℝ) ^ (n + 1))⁻¹)‖ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
      refine le_antisymm ?_ ?_
      · rw [pi_norm_le_iff_of_nonneg (le_of_lt hpos)]
        intro i
        simp [Real.norm_eq_abs, abs_of_pos hpos]
      · obtain ⟨i⟩ := ‹Nonempty ι›
        have h := norm_le_pi_norm (fun _ : ι => ((2 : ℝ) ^ (n + 1))⁻¹) i
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using h
    rw [hnorm]
    exact hn

theorem Emodel_invariant (i₀ : ι) {x : ι → ℝ} (hx : x ∈ Emodel i₀) :
    diag (fun _ : ι => (2 : ℝ)) x ∈ Emodel i₀ := by
  show (diag (fun _ : ι => (2 : ℝ)) x) i₀ ∈ Ef
  rw [diag_apply]
  exact Ef_invariant hx

/-- **The witness has empty interior in every dimension.** -/
theorem Emodel_interior_empty (i₀ : ι) : interior (Emodel i₀) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxE : x ∈ Emodel i₀ := interior_subset hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨q, hq⟩ := Ef_subset_rat hxE
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧ Real.sqrt 2 / N < ε := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    obtain ⟨M, hM⟩ := exists_nat_gt (Real.sqrt 2 / ε)
    refine ⟨M + 1, Nat.succ_pos M, ?_⟩
    have hNpos' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hNpos']
    have hM1 : Real.sqrt 2 / ε < (M : ℝ) + 1 := by
      have : (M : ℝ) < (M : ℝ) + 1 := by linarith
      linarith
    have h2 : Real.sqrt 2 = (Real.sqrt 2 / ε) * ε := by field_simp
    have h3 : (Real.sqrt 2 / ε) * ε < ((M : ℝ) + 1) * ε :=
      mul_lt_mul_of_pos_right hM1 hε
    push_cast
    linarith [h2, h3]
  have hδirr : Irrational (Real.sqrt 2 / N) :=
    Irrational.div_natCast irrational_sqrt_two (by omega)
  have hyirr : Irrational ((q : ℝ) + Real.sqrt 2 / N) :=
    (by simpa [add_comm] using irrational_add_rat hδirr q)
  set y : ι → ℝ := fun i => x i + Real.sqrt 2 / N with hydef
  have hyE : y ∉ Emodel i₀ := by
    intro hmem
    obtain ⟨q', hq'⟩ := Ef_subset_rat (x := y i₀) hmem
    exact hyirr ⟨q', by simpa [hydef, hq] using hq'.symm⟩
  refine hyE (hball ?_)
  rw [Metric.mem_ball]
  have hle : dist y x ≤ Real.sqrt 2 / N := by
    rw [dist_pi_le_iff (le_of_lt (by positivity : (0:ℝ) < Real.sqrt 2 / N))]
    intro i
    rw [Real.dist_eq]
    have hzero : y i - x i = Real.sqrt 2 / N := by
      simp only [hydef]
      ring
    rw [hzero, abs_of_pos (by positivity)]
  linarith [hle, hN]

/-- **C4's cone conclusion fails for a single expanding map in every nonempty
dimension** — in particular in the project's own `Fin 3 → ℝ`, which is the
dimension of `Pt`. -/
theorem cone_step_single_map_false_gen (i₀ : ι) :
    ¬ (∀ E : Set (ι → ℝ), IsClosed E → Acc E Finset.univ →
        (∀ x ∈ E, diag (fun _ : ι => (2 : ℝ)) x ∈ E) →
        ∃ U : Set (ι → ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ E) := by
  intro h
  obtain ⟨U, hUopen, ⟨y, hyU⟩, hUE⟩ :=
    h (Emodel i₀) (Emodel_closed i₀) (Emodel_acc i₀) (fun x hx => Emodel_invariant i₀ hx)
  have hsub : U ⊆ interior (Emodel i₀) := interior_maximal hUE hUopen
  have hmem : y ∈ interior (Emodel i₀) := hsub hyU
  rw [Emodel_interior_empty i₀] at hmem
  exact absurd hmem (by simp)

end BerendLiftSharp

end CubicTwoStage

#print axioms CubicTwoStage.BerendLiftSharp.Ef_closed
#print axioms CubicTwoStage.BerendLiftSharp.Ef_periodic
#print axioms CubicTwoStage.BerendLiftSharp.Ef_invariant
#print axioms CubicTwoStage.BerendLiftSharp.Ef_zero_nonisolated
#print axioms CubicTwoStage.BerendLiftSharp.Ef_interior_empty

#print axioms CubicTwoStage.BerendLiftSharp.E1_closed
#print axioms CubicTwoStage.BerendLiftSharp.E1_acc
#print axioms CubicTwoStage.BerendLiftSharp.E1_invariant
#print axioms CubicTwoStage.BerendLiftSharp.E1_interior_empty
#print axioms CubicTwoStage.BerendLiftSharp.cone_step_single_map_false

#print axioms CubicTwoStage.BerendLiftSharp.Emodel_closed
#print axioms CubicTwoStage.BerendLiftSharp.Emodel_acc
#print axioms CubicTwoStage.BerendLiftSharp.Emodel_invariant
#print axioms CubicTwoStage.BerendLiftSharp.Emodel_interior_empty
#print axioms CubicTwoStage.BerendLiftSharp.cone_step_single_map_false_gen
