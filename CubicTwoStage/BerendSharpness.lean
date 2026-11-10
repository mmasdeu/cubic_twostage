/-
# Sharpness witnesses for the deep Berend stages

`BEREND_PROOF_PLAN.md` §D.5 (amended) says, of the closed proper invariant set
`𝒀 = {0} ∪ {2⁻ⁿ : n ≥ 1} ⊆ ℝ/ℤ`:

> The doubling-map counterexample `Y = {0} ∪ {2⁻ⁿ : n ≥ 1} ⊆ ℝ/ℤ` is closed,
> infinite, proper and invariant, but its only minimal closed invariant subset is
> `{0}`.  The residual statement is exactly that no closed invariant proper `Y`
> has `diffSet Y = univ`.

This module **machine-checks every clause of that sentence**, so that no member of
the swarm can spend effort on a strengthening that is false:

* `Y_closed`, `Y_infinite`, `Y_proper`, `Y_invariant` — closed, infinite, proper
  and invariant under the doubling map `y ↦ 2 • y`;
* `zero_nonisolated` — `0` is a non-isolated point of `Y`, i.e. the hypothesis of
  Stage I (`eq_univ_of_zero_nonisolated`) that is *not* about the family holds;
* `minimal_subset_finite` / `minimal_eq_singleton` — every minimal nonempty
  closed doubling-invariant subset of `Y` is `{0}`, hence finite.

Consequences (the point of the file):

* `stage_one_single_map_false` — **Stage I is false for a single dilation**:
  `Y` satisfies closed, nonempty, `0` non-isolated and `2 • Y ⊆ Y`, yet
  `Y ≠ univ`.  So `eq_univ_of_zero_nonisolated` can only be true with the whole
  multiplicatively independent family in its hypotheses (B2/B3 in the project's
  numbering); a proof of the cone step from `exists_minimal_and_expanding` that
  keeps only one expanding family element cannot exist.
* `minimal_finite_but_infinite` / `counterexample_summary` — **finiteness of all
  minimal closed invariant subsets does not propagate**: `Y` is infinite and proper
  while each of its minimal closed invariant subsets is `{0}`, hence finite, and
  `Y - Y ≠ univ`.  This machine-checks the plan's amended §D.5 and refutes the
  removed placeholder reduction `infinite_has_infinite_minimal_of_multi_parameter`
  *in the single-map form*; the multi-parameter form stays the open obligation.
* The hypothesis that fails here is the second, multiplicatively independent map
  (`3 • Y ⊄ Y`, e.g. `3 • (1/4) = 3/4 ∉ Y`); this is elementary but is **not**
  formalised in this file, only the `×2` invariance is.

Axiom free: imports only Mathlib, no `sorry`, `#print axioms` at the end reports
only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendSharpness

/-! ## 1. A general closedness lemma: a sequence tending to `a`, plus `a` -/

/-- **`{a} ∪ range e` is closed when `e` tends to `a`.**  Every point `x` outside
it has positive distance `c` to `a`; all but finitely many terms of `e` are then
at distance `> c / 2` from `x`, and the finitely many exceptional terms are at
positive distance because `x` is not among them. -/
theorem isClosed_insert_range {X : Type*} [MetricSpace X] {e : ℕ → X} {a : X}
    (h : Tendsto e atTop (𝓝 a)) : IsClosed (insert a (range e)) := by
  classical
  rw [isClosed_iff_nhds]
  intro x hx
  by_contra hxm
  have hxa : x ≠ a := fun h' => hxm (Or.inl h')
  have hxr : ∀ n, e n ≠ x := fun n h' => hxm (Or.inr ⟨n, h'⟩)
  have hd : 0 < dist x a := dist_pos.mpr hxa
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (dist x a / 2) (by linarith)
  -- a uniform lower bound for `dist x (e n)` away from the initial segment
  have htail : ∀ n, N ≤ n → dist x a / 2 ≤ dist x (e n) := by
    intro n hn
    have h1 : dist (e n) a < dist x a / 2 := hN n hn
    have h2 : dist x a ≤ dist x (e n) + dist (e n) a := dist_triangle x (e n) a
    linarith
  -- a positive lower bound on the finite initial segment
  obtain ⟨d, hdpos, hdle⟩ : ∃ d : ℝ, 0 < d ∧ ∀ n, n < N → d ≤ dist x (e n) := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · exact ⟨1, one_pos, fun n hn => absurd hn (by omega)⟩
    · refine ⟨(Finset.range N).inf' (Finset.nonempty_range_iff.mpr (by omega))
        (fun n => dist x (e n)), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro n _
        exact dist_pos.mpr (Ne.symm (hxr n))
      · intro n hn
        exact Finset.inf'_le _ (Finset.mem_range.mpr hn)
  obtain ⟨y, hyb, hy | ⟨n, rfl⟩⟩ :=
    hx (Metric.ball x (min (dist x a / 2) d)) (Metric.ball_mem_nhds x (by positivity))
  · rw [hy, Metric.mem_ball, dist_comm a x] at hyb
    have h1 : min (dist x a / 2) d ≤ dist x a / 2 := min_le_left _ _
    linarith
  · rw [Metric.mem_ball, dist_comm (e n) x] at hyb
    rcases lt_or_ge n N with hn | hn
    · have h1 : min (dist x a / 2) d ≤ d := min_le_right _ _
      have h2 := hdle n hn
      linarith
    · have h1 : min (dist x a / 2) d ≤ dist x a / 2 := min_le_left _ _
      have h2 := htail n hn
      linarith

/-! ## 2. The doubling map on the circle and the dyadic sequence -/

/-- The circle `ℝ/ℤ`. -/
abbrev Circle : Type := AddCircle (1 : ℝ)

/-- The dyadic sequence `e n = 2⁻⁽ⁿ⁺¹⁾` in the circle. -/
noncomputable def e : ℕ → Circle := fun n => ((↑(((2 : ℝ) ^ (n + 1))⁻¹) : Circle))

/-- **The doubling-map counterexample set** `𝒀 = {0} ∪ {2⁻⁽ⁿ⁺¹⁾ : n ∈ ℕ}`. -/
noncomputable def Y : Set Circle := insert 0 (range e)

theorem mem_Y_iff {y : Circle} :
    y ∈ Y ↔ y = 0 ∨ ∃ n : ℕ, ((↑(((2 : ℝ) ^ (n + 1))⁻¹) : Circle)) = y := Iff.rfl

/-- The dyadic sequence tends to `0` in the circle. -/
theorem tendsto_e : Tendsto e atTop (𝓝 (0 : Circle)) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun n : ℕ => (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hcont : Continuous (fun x : ℝ => ((x : Circle))) := QuotientAddGroup.continuous_mk
  have hco : Tendsto (fun x : ℝ => ((x : Circle))) (𝓝 0) (𝓝 (0 : Circle)) := by
    have h0 := hcont.tendsto (0 : ℝ)
    rwa [AddCircle.coe_zero] at h0
  exact hco.comp hu

/-- **`Y` is closed.** -/
theorem Y_closed : IsClosed Y := isClosed_insert_range tendsto_e

/-- **`0` is a non-isolated point of `Y`**: the dyadic sequence consists of nonzero
points of `Y` converging to `0`. -/
theorem zero_nonisolated : (0 : Circle) ∈ closure (Y \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, (e n) ∈ Metric.ball (0 : Circle) ε :=
    tendsto_e.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
  have hne : e n ≠ 0 := by
    intro hzero
    have hmem : (↑(((2 : ℝ) ^ (n + 1))⁻¹) : Circle) = 0 := hzero
    rw [AddCircle.coe_eq_zero_iff] at hmem
    obtain ⟨z, hz⟩ := hmem
    -- `z • 1 = 2⁻⁽ⁿ⁺¹⁾`, impossible since the right side is in `(0,1)`
    have hz' : ((z : ℤ) : ℝ) = ((2 : ℝ) ^ (n + 1))⁻¹ := by simpa using hz
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
    have hone : (1 : ℝ) < (2 : ℝ) ^ (n + 1) := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (Nat.succ_le_succ (Nat.zero_le n))
      linarith
    have hlt : ((2 : ℝ) ^ (n + 1))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact hone
    have hzpos : (0 : ℝ) < ((z : ℤ) : ℝ) := by rw [hz']; positivity
    have hz1z : (1 : ℤ) ≤ z := by
      have h0 : (0 : ℤ) < z := by exact_mod_cast hzpos
      omega
    have hz1 : (1 : ℝ) ≤ ((z : ℤ) : ℝ) := by exact_mod_cast hz1z
    rw [hz'] at hz1
    linarith
  refine ⟨e n, ⟨?_, hne⟩, ?_⟩
  · rw [mem_Y_iff]; exact Or.inr ⟨n, rfl⟩
  · simpa [Metric.mem_ball, dist_comm] using hn

/-! ## 3. `Y` is infinite, proper and doubling-invariant -/

/-- **`Y` is infinite.**  `Y` is closed and `0` is a non-isolated point of it, so
it cannot be finite (a finite set is closed, and removing `0` leaves `0` out of
the closure). -/
theorem Y_infinite : Y.Infinite := by
  intro hfin
  have hclosed : IsClosed (Y \ {0}) := hfin.sdiff.isClosed
  have hc : closure (Y \ {0}) = Y \ {0} := hclosed.closure_eq
  have hmem : (0 : Circle) ∈ Y \ {0} := hc ▸ zero_nonisolated
  simpa using hmem

/-- Doubling the dyadic `2⁻⁽ⁿ⁺¹⁾` gives `2⁻ⁿ`. -/
theorem two_nsmul_dyadic (n : ℕ) :
    (2 : ℝ) * (((2 : ℝ) ^ (n + 1))⁻¹) = ((2 : ℝ) ^ n)⁻¹ := by
  have h2 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ]; ring
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]

/-- Coercion bookkeeping: the natural scalar `2` acting on a circle element is the
real multiplication by `2` upstairs. -/
theorem two_nsmul_coe (x : ℝ) :
    (2 : ℕ) • ((x : Circle)) = ((2 * x : ℝ) : Circle) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  push_cast
  ring

/-- Coercion bookkeeping for an arbitrary natural scalar. -/
theorem nsmul_coe (m : ℕ) (x : ℝ) :
    m • ((x : Circle)) = (((m : ℝ) * x : ℝ) : Circle) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]

/-- **`Y` is invariant under the doubling map `y ↦ 2 • y`.** -/
theorem Y_invariant : ∀ y ∈ Y, (2 : ℕ) • y ∈ Y := by
  intro y hy
  rw [mem_Y_iff] at hy
  rcases hy with rfl | ⟨n, rfl⟩
  · rw [smul_zero]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · rw [two_nsmul_coe, two_nsmul_dyadic]
    rcases n with _ | k
    · have h1 : (((2 : ℝ) ^ 0)⁻¹) = 1 := by norm_num
      rw [h1]
      have hzero : ((1 : ℝ) : Circle) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨1, by norm_num⟩
      rw [hzero]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨k, rfl⟩)

/-! ## 4. `Y` is proper: `1/3 ∉ Y` -/

theorem third_ne_zero : ((1 / 3 : ℝ) : Circle) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  have hz' : ((z : ℤ) : ℝ) = 1 / 3 := by simpa using hz
  have h3 : (3 : ℤ) * z = 1 := by
    have h3R : (3 : ℝ) * ((z : ℤ) : ℝ) = 1 := by rw [hz']; norm_num
    exact_mod_cast h3R
  omega

/-- **`1/3` is not one of the dyadics `e n`.**  Otherwise `1/3 - 2⁻⁽ⁿ⁺¹⁾` would be
an integer `z`; multiplying by `3 · 2ⁿ⁺¹` gives `2ⁿ⁺¹ = 3 · (z · 2ⁿ⁺¹ + 1)`, i.e.
`3 ∣ 2ⁿ⁺¹`. -/
theorem third_ne_e (n : ℕ) : ((1 / 3 : ℝ) : Circle) ≠ e n := by
  intro h
  have hmem : (1 / 3 : ℝ) - (((2 : ℝ) ^ (n + 1))⁻¹) ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    (QuotientAddGroup.eq_iff_sub_mem).mp h
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz' : ((z : ℤ) : ℝ) = 1 / 3 - (((2 : ℝ) ^ (n + 1))⁻¹) := by simpa using hz
  have h3 : (3 : ℝ) * ((z : ℤ) : ℝ) * ((2 : ℝ) ^ (n + 1)) =
      ((2 : ℝ) ^ (n + 1)) - 3 := by
    rw [hz']
    field_simp
  have hZ : (3 : ℤ) * z * (2 : ℤ) ^ (n + 1) = (2 : ℤ) ^ (n + 1) - 3 := by
    have hcast : (((3 : ℤ) * z * (2 : ℤ) ^ (n + 1) : ℤ) : ℝ) =
        ((((2 : ℤ) ^ (n + 1) - 3 : ℤ)) : ℝ) := by
      push_cast
      linarith [h3]
    exact_mod_cast hcast
  have hZ2 : (2 : ℤ) ^ (n + 1) = 3 * (z * (2 : ℤ) ^ (n + 1) + 1) := by
    linarith [hZ]
  have hdvd : (3 : ℤ) ∣ (2 : ℤ) ^ (n + 1) := ⟨z * (2 : ℤ) ^ (n + 1) + 1, hZ2⟩
  have hdvdN : (3 : ℕ) ∣ 2 ^ (n + 1) := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using h
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvdN
  norm_num at h32

/-- **`Y` is proper**: `1/3` is a point of the circle that is not in `Y`. -/
theorem Y_proper : Y ≠ univ := by
  intro h
  have hmem : ((1 / 3 : ℝ) : Circle) ∈ Y := by rw [h]; exact Set.mem_univ _
  rw [mem_Y_iff] at hmem
  rcases hmem with h' | ⟨n, hn⟩
  · exact third_ne_zero h'
  · exact third_ne_e n hn.symm

/-! ## 5. Every minimal closed doubling-invariant subset of `Y` is `{0}` -/

/-- Doubling a dyadic `2⁻⁽ⁿ⁺¹⁾` exactly `n + 1` times gives `1 ≡ 0`. -/
theorem pow_two_nsmul_e (n : ℕ) : (2 : ℕ) ^ (n + 1) • e n = 0 := by
  rw [show ((e n) : Circle) = (↑(((2 : ℝ) ^ (n + 1))⁻¹) : Circle) from rfl, nsmul_coe]
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨1, ?_⟩
  rw [one_smul]
  push_cast
  field_simp

/-- A nonempty closed doubling-invariant subset of `Y` contains `0`. -/
theorem zero_mem_of_subset (Z : Set Circle) (hZ : Z ⊆ Y) (hne : Z.Nonempty)
    (hinv : ∀ z ∈ Z, (2 : ℕ) • z ∈ Z) : (0 : Circle) ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  rcases mem_Y_iff.mp (hZ hz) with h | ⟨n, rfl⟩
  · rwa [h] at hz
  · have hiter : ∀ k : ℕ, (2 : ℕ) ^ k • e n ∈ Z := by
      intro k
      induction k with
      | zero => simpa [e] using hz
      | succ k ih =>
          rw [pow_succ, mul_nsmul]
          exact hinv _ ih
    have hfull : (2 : ℕ) ^ (n + 1) • e n = 0 := pow_two_nsmul_e n
    rw [← hfull]
    exact hiter (n + 1)

/-- **A minimal closed doubling-invariant subset of `Y` is `{0}`.** -/
theorem minimal_eq_singleton (Z : Set Circle) (hZ : Z ⊆ Y) (_hclosed : IsClosed Z)
    (hne : Z.Nonempty) (hinv : ∀ z ∈ Z, (2 : ℕ) • z ∈ Z)
    (hmin : ∀ W : Set Circle, W ⊆ Z → IsClosed W → W.Nonempty →
      (∀ z ∈ W, (2 : ℕ) • z ∈ W) → W = Z) :
    Z = {0} := by
  have h0 : (0 : Circle) ∈ Z := zero_mem_of_subset Z hZ hne hinv
  have hsub : ({0} : Set Circle) ⊆ Z := singleton_subset_iff.mpr h0
  have hinv0 : ∀ z ∈ ({0} : Set Circle), (2 : ℕ) • z ∈ ({0} : Set Circle) := by
    intro z hz
    rw [mem_singleton_iff] at hz ⊢
    rw [hz, smul_zero]
  have h := hmin {0} hsub isClosed_singleton (singleton_nonempty 0) hinv0
  exact h.symm

/-- Consequently every minimal closed doubling-invariant subset of `Y` is finite
(it is `{0}`). -/
theorem minimal_finite (Z : Set Circle) (hZ : Z ⊆ Y) (hclosed : IsClosed Z)
    (hne : Z.Nonempty) (hinv : ∀ z ∈ Z, (2 : ℕ) • z ∈ Z)
    (hmin : ∀ W : Set Circle, W ⊆ Z → IsClosed W → W.Nonempty →
      (∀ z ∈ W, (2 : ℕ) • z ∈ W) → W = Z) :
    Z.Finite := by
  rw [minimal_eq_singleton Z hZ hclosed hne hinv hmin]
  exact finite_singleton 0

/-! ## 6. The refutations -/

/-- **Stage I is false for a single dilation.**  There is a closed nonempty
`E ⊆ ℝ/ℤ` of which `0` is a non-isolated point, with `2 • E ⊆ E`, and yet
`E ≠ univ`.  So `eq_univ_of_zero_nonisolated` (plan §C) can only be true with the
whole multiplicatively independent family in its hypotheses; in particular no
lemma whose only invariance hypothesis is the single uniformly expanding member
supplied by `BerendSec4.exists_minimal_and_expanding` can conclude `E = univ` or
that `E` has interior. -/
theorem stage_one_single_map_false :
    ¬ (∀ E : Set Circle, IsClosed E → E.Nonempty →
        (0 : Circle) ∈ closure (E \ {0}) → (∀ z ∈ E, (2 : ℕ) • z ∈ E) → E = univ) := by
  intro h
  have hY : Y = univ :=
    h Y Y_closed ⟨0, Set.mem_insert_iff.mpr (Or.inl rfl)⟩ zero_nonisolated Y_invariant
  exact Y_proper hY

/-- **Finiteness of the minimal closed invariant subsets does not propagate.**
`Y` is closed, infinite, proper and doubling-invariant, yet each of its minimal
closed doubling-invariant subsets is `{0}`, hence finite.  This machine-checks the
amended plan §D.5 counterexample: no argument may derive finiteness of `Y` from
finiteness of its minimal closed invariant subsets alone. -/
theorem minimal_finite_but_infinite :
    IsClosed Y ∧ Y.Infinite ∧ Y ≠ univ ∧ (∀ z ∈ Y, (2 : ℕ) • z ∈ Y) ∧
      (∀ Z : Set Circle, Z ⊆ Y → IsClosed Z → Z.Nonempty →
        (∀ z ∈ Z, (2 : ℕ) • z ∈ Z) →
        (∀ W : Set Circle, W ⊆ Z → IsClosed W → W.Nonempty →
          (∀ z ∈ W, (2 : ℕ) • z ∈ W) → W = Z) → Z.Finite) :=
  ⟨Y_closed, Y_infinite, Y_proper, Y_invariant,
    fun Z hZ hc hn hi hm => minimal_finite Z hZ hc hn hi hm⟩

/-! ## 8. `Y - Y ≠ univ`: the example does *not* violate the residual statement

The residual obligation of amended §D.5 says that no closed invariant proper `Y` has
full difference set.  The example above is consistent with it: `Y` is countable, so
`Y - Y` is countable, while the circle is not.  This closes the last clause of the
plan's §D.5 sentence for the example.
-/

/-- Every fibre of the quotient map `ℝ → ℝ/ℤ` is countable (it is a translate of
the integers). -/
theorem countable_fibre (q : Circle) : {x : ℝ | ((x : Circle)) = q}.Countable := by
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) q
  have hsub : {x : ℝ | ((x : Circle)) = q} ⊆ (fun z : ℤ => a₀ + z • (1 : ℝ)) '' (univ : Set ℤ) := by
    intro x hx
    have heq : ((x : ℝ) : Circle) = ((a₀ : ℝ) : Circle) := by
      rw [hx]
      exact ha₀.symm
    have hxm : x - a₀ ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      QuotientAddGroup.eq_iff_sub_mem.mp heq
    rw [AddSubgroup.mem_zmultiples_iff] at hxm
    obtain ⟨z, hz⟩ := hxm
    exact ⟨z, trivial, by show a₀ + z • (1 : ℝ) = x; rw [hz]; abel⟩
  exact Set.Countable.mono hsub (Set.countable_univ.image _)

/-- **The circle is uncountable.**  Otherwise `ℝ` would be a countable union of the
countable fibres of the quotient map. -/
theorem not_countable_circle : ¬ Countable Circle := by
  intro hq
  haveI : Countable Circle := hq
  have hfib : ∀ q : Circle, ({x : ℝ | ((x : Circle)) = q}).Countable := countable_fibre
  have hcover : (univ : Set ℝ) ⊆ ⋃ q : Circle, {x : ℝ | ((x : Circle)) = q} := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨((x : Circle)), rfl⟩
  have hR : Countable ℝ :=
    Set.countable_univ_iff.mp (Set.Countable.mono hcover (Set.countable_iUnion hfib))
  exact (inferInstance : Uncountable ℝ).not_countable hR

/-- `Y` is countable (it is `{0}` plus the range of a sequence). -/
theorem Y_countable : Y.Countable :=
  (Set.countable_range e).insert 0

/-- **`Y - Y` is not the whole circle.** -/
theorem Y_diffSet_ne_univ : Y - Y ≠ univ := by
  intro h
  have hpair : (Y ×ˢ Y).Countable := Y_countable.prod Y_countable
  have himg : Y - Y = (fun p : Circle × Circle => p.1 - p.2) '' (Y ×ˢ Y) := by
    rw [sub_image_prod]
  have hcount : (Y - Y).Countable := by
    rw [himg]
    exact Set.Countable.image hpair _
  have huniv : (univ : Set Circle).Countable := by
    rw [← h]
    exact hcount
  exact not_countable_circle (Set.countable_univ_iff.mp huniv)

/-- **The full amended §D.5 sentence, machine-checked**: `Y` is closed, infinite,
proper, doubling-invariant, `0` is a non-isolated point of it, every minimal closed
doubling-invariant subset of `Y` is finite, and `Y - Y` is not the whole circle —
so the example is a sharpness witness and not a counterexample to the residual
statement. -/
theorem counterexample_summary :
    IsClosed Y ∧ Y.Infinite ∧ Y ≠ univ ∧ (∀ z ∈ Y, (2 : ℕ) • z ∈ Y) ∧
      (0 : Circle) ∈ closure (Y \ {0}) ∧ Y - Y ≠ univ ∧
      (∀ Z : Set Circle, Z ⊆ Y → IsClosed Z → Z.Nonempty →
        (∀ z ∈ Z, (2 : ℕ) • z ∈ Z) →
        (∀ W : Set Circle, W ⊆ Z → IsClosed W → W.Nonempty →
          (∀ z ∈ W, (2 : ℕ) • z ∈ W) → W = Z) → Z.Finite) :=
  ⟨Y_closed, Y_infinite, Y_proper, Y_invariant, zero_nonisolated, Y_diffSet_ne_univ,
    fun Z hZ hc hn hi hm => minimal_finite Z hZ hc hn hi hm⟩

end BerendSharpness

end CubicTwoStage

/-! ## 7. Axiom audit -/

#print axioms CubicTwoStage.BerendSharpness.Y_closed
#print axioms CubicTwoStage.BerendSharpness.zero_nonisolated
#print axioms CubicTwoStage.BerendSharpness.Y_infinite
#print axioms CubicTwoStage.BerendSharpness.Y_proper
#print axioms CubicTwoStage.BerendSharpness.Y_invariant
#print axioms CubicTwoStage.BerendSharpness.minimal_finite
#print axioms CubicTwoStage.BerendSharpness.stage_one_single_map_false
#print axioms CubicTwoStage.BerendSharpness.minimal_finite_but_infinite


#print axioms CubicTwoStage.BerendSharpness.not_countable_circle
#print axioms CubicTwoStage.BerendSharpness.Y_diffSet_ne_univ
#print axioms CubicTwoStage.BerendSharpness.counterexample_summary
