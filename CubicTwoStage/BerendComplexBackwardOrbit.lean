import CubicTwoStage.BerendNormalizedCompactArc

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1200000

namespace CubicTwoStage
namespace BerendNormalizedCompactArc

open BerendPlanarArc BerendPhaseArc

/-- Iterates of complex left multiplication. -/
theorem iterate_mul_left_apply (c : ℂ) (n : ℕ) (z : ℂ) :
    ((fun w => c * w)^[n]) z = c ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      ring

theorem iterate_mul_left_mem {F : Set ℂ} (hinv : ∀ z ∈ F, c * z ∈ F) :
    ∀ (n : ℕ) {z : ℂ}, z ∈ F → ((fun w => c * w)^[n]) z ∈ F := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply]
      exact ih (hinv z hz)

theorem iterate_mul_left_norm_le (c : ℂ) (n : ℕ) (z : ℂ) :
    ‖((fun w => c * w)^[n]) z‖ ≤ ‖c‖ ^ n * ‖z‖ := by
  rw [iterate_mul_left_apply, norm_mul, norm_pow]

theorem exists_iterate_mul_left_norm_ge {c : ℂ} (hc : 1 < ‖c‖) {z : ℂ}
    (hz : z ≠ 0) (a : ℝ) : ∃ n : ℕ, a ≤ ‖((fun w => c * w)^[n]) z‖ := by
  have ht : Tendsto (fun n : ℕ => ‖c‖ ^ n * ‖z‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const (norm_pos_iff.mpr hz)
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.1 ht) a
  refine ⟨n, (hn n le_rfl).trans ?_⟩
  rw [iterate_mul_left_apply, norm_mul, norm_pow]

/-- The finite backward chart attached to a hitting time. -/
noncomputable def chartEntryC (c : ℂ) (v : ℕ → ℂ) (jh : ℕ → ℕ) (m j : ℕ) : ℂ :=
  if j ≤ jh m then ((fun w => c * w)^[jh m - j]) (v m) else 0

/-- Berend Lemma 4.3, compact-chart form for one complex coordinate. -/
theorem exists_backward_orbit_complex
    {F : Set ℂ} (hF : IsClosed F) {c : ℂ} (hinv : ∀ z ∈ F, c * z ∈ F)
    {v : ℕ → ℂ} (hvF : ∀ m, v m ∈ F)
    {jh : ℕ → ℕ} (hjh : Tendsto jh atTop atTop)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hann : ∀ m, a ≤ ‖((fun w => c * w)^[jh m]) (v m)‖)
    (hwin : ∀ m j, j ≤ jh m → ‖((fun w => c * w)^[jh m - j]) (v m)‖ ≤ R) :
    ∃ w : ℕ → ℂ, (∀ j, w j ∈ F) ∧ (∀ j, c * w (j + 1) = w j) ∧
      a ≤ ‖w 0‖ ∧ ∀ j, ‖w j‖ ≤ R := by
  classical
  set chart : ℕ → (ℕ → ℂ) := fun m j => chartEntryC c v jh m j
  have hcball : ∀ m j, chart m j ∈ Metric.closedBall (0 : ℂ) R := by
    intro m j
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hj : j ≤ jh m
    · simpa only [chart, chartEntryC, if_pos hj] using hwin m j hj
    · simp only [chart, chartEntryC, if_neg hj, norm_zero]
      exact le_trans ha.le haR
  set K : Set (ℕ → ℂ) := {x | ∀ j, x j ∈ Metric.closedBall (0 : ℂ) R}
  have hKeq : K = Set.univ.pi (fun _ : ℕ => Metric.closedBall (0 : ℂ) R) := by
    ext x
    simp only [K, Set.mem_setOf_eq, Set.mem_univ_pi]
  have hKcompact : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi (s := fun _ : ℕ => Metric.closedBall (0 : ℂ) R)
      (fun _ => Metric.isCompact_iff_isClosed_bounded.2
        ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall⟩)
  have hcK : ∀ m, chart m ∈ K := fun m => hcball m
  obtain ⟨x, -, hxcl⟩ := hKcompact.exists_mapClusterPt (u := chart)
    (Filter.le_principal_iff.2
      (Filter.Eventually.of_forall (f := atTop) (p := fun m => chart m ∈ K) hcK))
  have hcoord : ∀ j, MapClusterPt (x j) atTop (fun m => chart m j) := by
    intro j
    have h := hxcl.continuousAt_comp (continuous_apply j).continuousAt
    simpa [Function.comp_def] using h
  have hxF : ∀ j, x j ∈ F := by
    intro j
    refine hF.mem_of_mapClusterPt (hcoord j) ?_
    refine Eventually.mono (hjh.eventually (eventually_ge_atTop j)) ?_
    intro m hm
    simp only [chart, chartEntryC, if_pos hm]
    exact iterate_mul_left_mem hinv _ (hvF m)
  have hback : ∀ j, c * x (j + 1) = x j := by
    intro j
    have hclosed : IsClosed {y : ℕ → ℂ | c * y (j + 1) = y j} := by
      have hcont : Continuous fun y : ℕ → ℂ => c * y (j + 1) :=
        continuous_const.mul (continuous_apply (j + 1))
      exact isClosed_eq hcont (continuous_apply j)
    refine hclosed.mem_of_mapClusterPt hxcl ?_
    refine Eventually.mono (hjh.eventually (eventually_ge_atTop (j + 1))) ?_
    intro m hm
    have hj : j ≤ jh m := le_trans (Nat.le_succ j) hm
    simp only [Set.mem_setOf_eq, chart, chartEntryC, if_pos hm, if_pos hj]
    have hstep : jh m - j = (jh m - (j + 1)) + 1 := by omega
    rw [hstep, Function.iterate_succ_apply']
  have hnorm : a ≤ ‖x 0‖ := by
    have hclosed : IsClosed {y : ℕ → ℂ | a ≤ ‖y 0‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_apply 0))
    refine hclosed.mem_of_mapClusterPt hxcl ?_
    exact Eventually.of_forall fun m => by
      simpa only [Set.mem_setOf_eq, chart, chartEntryC, if_pos (Nat.zero_le _),
        Nat.sub_zero] using hann m
  have hbdd : ∀ j, ‖x j‖ ≤ R := by
    intro j
    have hmem := Metric.isClosed_closedBall.mem_of_mapClusterPt (hcoord j)
      (Filter.Eventually.of_forall fun m => hcball m j)
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  exact ⟨x, hxF, hback, hnorm, hbdd⟩

/-- An accumulating nonzero sequence and an expanding complex multiplier produce a full
backward orbit. -/
theorem exists_backward_orbit_complex_of_acc {F : Set ℂ} (hF : IsClosed F)
    {c : ℂ} (hc : 1 < ‖c‖) (hinv : ∀ z ∈ F, c * z ∈ F)
    (hacc : (0 : ℂ) ∈ closure (F \ {0})) {a : ℝ} (ha : 0 < a) :
    ∃ w : ℕ → ℂ, (∀ j, w j ∈ F) ∧ (∀ j, c * w (j + 1) = w j) ∧ a ≤ ‖w 0‖ := by
  classical
  have hseq : ∀ m : ℕ, ∃ u : ℂ, u ∈ F ∧ u ≠ 0 ∧ ‖u‖ < min a (a / ((m : ℝ) + 1)) := by
    intro m
    obtain ⟨u, hu, hdist⟩ := (Metric.mem_closure_iff.mp hacc)
      (min a (a / ((m : ℝ) + 1))) (lt_min ha (by positivity))
    refine ⟨u, hu.1, by simpa using hu.2, ?_⟩
    simpa [dist_zero_right] using hdist
  choose v hvF hvne hvlt using hseq
  have hex : ∀ m, ∃ k : ℕ, a ≤ ‖((fun w => c * w)^[k]) (v m)‖ := fun m =>
    exists_iterate_mul_left_norm_ge hc (hvne m) a
  let jh : ℕ → ℕ := fun m => Nat.find (hex m)
  have hann : ∀ m, a ≤ ‖((fun w => c * w)^[jh m]) (v m)‖ := fun m => Nat.find_spec (hex m)
  have hsv : ∀ m, ‖v m‖ < a := fun m =>
    (hvlt m).trans_le (min_le_left a (a / ((m : ℝ) + 1)))
  have hjhpos : ∀ m, 1 ≤ jh m := by
    intro m
    rcases Nat.eq_zero_or_pos (jh m) with h | h
    · have hspec := hann m
      rw [h] at hspec
      simp only [Function.iterate_zero, id_eq] at hspec
      exact absurd hspec (not_le_of_gt (hsv m))
    · exact h
  have hwin : ∀ m j, j ≤ jh m →
      ‖((fun w => c * w)^[jh m - j]) (v m)‖ ≤ ‖c‖ * a := by
    intro m j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst j
      have hprev : ‖((fun w => c * w)^[jh m - 1]) (v m)‖ < a :=
        not_le.1 (Nat.find_min (hex m) (Nat.sub_one_lt_of_lt (hjhpos m)))
      have heq : jh m - 0 = (jh m - 1) + 1 := by
        rw [Nat.sub_zero, Nat.sub_add_cancel (hjhpos m)]
      rw [heq, Function.iterate_succ_apply', norm_mul]
      exact mul_le_mul_of_nonneg_left hprev.le (norm_nonneg c)
    · have hsub : jh m - j < jh m := Nat.sub_lt (hjhpos m) hjpos
      have hsmall : ‖((fun w => c * w)^[jh m - j]) (v m)‖ < a :=
        not_le.1 (Nat.find_min (hex m) hsub)
      exact hsmall.le.trans (by nlinarith [norm_nonneg c, hc.le])
  have hjh : Tendsto jh atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro K
    have hlim : Tendsto (fun m : ℕ => ‖c‖ ^ K * (a / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => a * ((1 : ℝ) / ((m : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a
      have h2 : (fun m : ℕ => a * ((1 : ℝ) / ((m : ℝ) + 1))) =
          fun m : ℕ => a / ((m : ℝ) + 1) := by funext m; rw [mul_one_div]
      rw [h2] at h1
      simpa using h1.const_mul (‖c‖ ^ K)
    have hev : ∀ᶠ m : ℕ in atTop, ‖c‖ ^ K * (a / ((m : ℝ) + 1)) < a := by
      have hb := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) ha)
      filter_upwards [hb] with m hm
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hm
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    refine ⟨M, fun m hm => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hspec := hann m
    have hstep : ‖((fun w => c * w)^[jh m]) (v m)‖ ≤ ‖c‖ ^ jh m * ‖v m‖ :=
      iterate_mul_left_norm_le c (jh m) (v m)
    have hle1 : ‖c‖ ^ jh m ≤ ‖c‖ ^ K := pow_le_pow_right₀ hc.le (le_of_lt hlt)
    have hle2 : ‖v m‖ ≤ a / ((m : ℝ) + 1) :=
      (hvlt m).le.trans (min_le_right a (a / ((m : ℝ) + 1)))
    have hle3 : ‖c‖ ^ jh m * ‖v m‖ ≤ ‖c‖ ^ K * (a / ((m : ℝ) + 1)) :=
      mul_le_mul hle1 hle2 (norm_nonneg _) (pow_nonneg (norm_nonneg _) K)
    linarith [hM m hm]
  obtain ⟨w, hwF, hback, hnorm, -⟩ := exists_backward_orbit_complex hF hinv hvF hjh
    (R := ‖c‖ * a) ha (by nlinarith [norm_nonneg c, hc.le]) hann hwin
  exact ⟨w, hwF, hback, hnorm⟩

/-- The backward orbit shrinks geometrically to zero. -/
theorem backward_orbit_complex_tendsto_zero {c : ℂ} (hc : 1 < ‖c‖) {w : ℕ → ℂ}
    (hback : ∀ j, c * w (j + 1) = w j) (hw0 : w 0 ≠ 0) :
    Tendsto (fun j => ‖w j‖) atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    norm_num at hc
  have hformula : ∀ j, c ^ j * w j = w 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          c ^ (j + 1) * w (j + 1) = c ^ j * (c * w (j + 1)) := by rw [pow_succ]; ring
          _ = c ^ j * w j := by rw [hback j]
          _ = w 0 := ih
  have hnorm : ∀ j, ‖w j‖ = ‖w 0‖ / ‖c‖ ^ j := by
    intro j
    have h := congrArg norm (hformula j)
    rw [norm_mul, norm_pow] at h
    have hcp : 0 < ‖c‖ ^ j := pow_pos (lt_trans zero_lt_one hc) j
    apply (eq_div_iff (ne_of_gt hcp)).2
    rw [mul_comm]
    exact h
  have hgeo : Tendsto (fun j : ℕ => (‖c‖⁻¹) ^ j) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · positivity
    · exact inv_lt_one_of_one_lt₀ hc
  have hlim := hgeo.const_mul ‖w 0‖
  have heq : (fun j : ℕ => ‖w 0‖ / ‖c‖ ^ j) = fun j => ‖w 0‖ * (‖c‖⁻¹) ^ j := by
    funext j
    rw [div_eq_mul_inv, inv_pow]
  have heqfun : (fun j : ℕ => ‖w j‖) = fun j : ℕ => ‖w 0‖ / ‖c‖ ^ j := by
    funext j
    exact hnorm j
  rw [heqfun, heq]
  simpa using hlim

/-- Explicit closed form of the backward orbit. -/
theorem backward_orbit_complex_apply {c : ℂ} (hc : c ≠ 0) {w : ℕ → ℂ}
    (hback : ∀ j, c * w (j + 1) = w j) (j : ℕ) :
    w j = c ^ (-(j : ℤ)) * w 0 := by
  have hformula : ∀ n : ℕ, c ^ (n : ℤ) * w n = w 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          c ^ ((n + 1 : ℕ) : ℤ) * w (n + 1) = c * (c ^ (n : ℤ) * w (n + 1)) := by
            push_cast
            rw [zpow_add₀ hc, zpow_one]
            ring
          _ = c ^ (n : ℤ) * w n := by rw [mul_left_comm, hback n]
          _ = w 0 := ih
  calc
    w j = c ^ (-(j : ℤ)) * (c ^ (j : ℤ) * w j) := by
      rw [← mul_assoc, ← zpow_add₀ hc]
      simp
    _ = c ^ (-(j : ℤ)) * w 0 := by rw [hformula j]

/-- Forward invariance under complex multiplication gives invariance under all natural powers. -/
theorem pow_mul_left_mem {F : Set ℂ} {d : ℂ} (hinv : ∀ z ∈ F, d * z ∈ F) :
    ∀ (n : ℕ) {z : ℂ}, z ∈ F → d ^ n * z ∈ F := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
      intro z hz
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hinv _ (ih hz)

/-- The normalized samples attached to the backward orbit stay in the forward-invariant set. -/
theorem normalizedSample_mul_basepoint_mem {F : Set ℂ} {c d : ℂ} (hc : c ≠ 0)
    {α : ℝ} (hα0 : 0 ≤ α) (hinv : ∀ z ∈ F, d * z ∈ F)
    {w : ℕ → ℂ} (hwF : ∀ j, w j ∈ F) (hback : ∀ j, c * w (j + 1) = w j) :
    ∀ j, normalizedSample c d α j * w 0 ∈ F := by
  intro j
  let n : ℕ := (⌊((j : ℝ) * α)⌋).toNat
  have hfn : 0 ≤ ⌊((j : ℝ) * α)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg j) hα0)
  have hn : (n : ℤ) = ⌊((j : ℝ) * α)⌋ := Int.toNat_of_nonneg hfn
  have hwc : c ^ (-⌊((j : ℝ) * α)⌋) * w 0 = w n := by
    rw [← hn]
    exact (backward_orbit_complex_apply hc hback n).symm
  have hdj : d ^ (j : ℤ) * w n ∈ F := by
    rw [zpow_natCast]
    exact pow_mul_left_mem hinv j (hwF n)
  convert hdj using 1
  rw [normalizedSample]
  calc
    c ^ (-⌊((j : ℝ) * α)⌋) * d ^ (j : ℤ) * w 0 =
        d ^ (j : ℤ) * (c ^ (-⌊((j : ℝ) * α)⌋) * w 0) := by ring
    _ = d ^ (j : ℤ) * w n := by rw [hwc]

/-- Abstract complex-planar Stage I arc from actual accumulation.  The closed set `F` is only
forward invariant; no density, full-circle, annulus, or invariance of a subgroup is assumed. -/
theorem exists_normalizedArc_complex_of_acc {F : Set ℂ} (hF : IsClosed F)
    {c d : ℂ} (hc : 1 < ‖c‖) (hd : d ≠ 0) (hB3 : MultIndepPair c d)
    {α β γ : ℝ} (hα : α = Real.log ‖d‖ / Real.log ‖c‖)
    (hβ : β = phaseOf c) (hγ : γ = phaseOf d) (hα0 : 0 ≤ α)
    (hcinv : ∀ z ∈ F, c * z ∈ F) (hdinv : ∀ z ∈ F, d * z ∈ F)
    (hacc : (0 : ℂ) ∈ closure (F \ {0})) :
    ∃ w₀ : ℂ, w₀ ≠ 0 ∧ ∃ (l : ℤ × ℤ) (t' : ℝ), l ≠ 0 ∧ 0 ≤ l.1 ∧ 0 < t' ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t', normalizedArc c β l w₀ t ∈ F := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    norm_num at hc
  have hlogc : Real.log ‖c‖ ≠ 0 := ne_of_gt (Real.log_pos hc)
  obtain ⟨w, hwF, hback, hnorm⟩ :=
    exists_backward_orbit_complex_of_acc hF hc hcinv hacc zero_lt_one
  have hw0 : w 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hsample : ∀ j, normalizedSample c d α j * w 0 ∈ F :=
    normalizedSample_mul_basepoint_mem hc0 hα0 hdinv hwF hback
  by_cases hirr : Irrational α
  · obtain ⟨l, t', hl0ne, hl0, ht', harc⟩ :=
      exists_normalizedArc_of_irrational hc0 hd hB3 hlogc hα hβ hγ hirr hF (w 0) hsample
    exact ⟨w 0, hw0, l, t', hl0ne, hl0.le, ht', harc⟩
  · have hr : ∃ r : ℚ, (r : ℝ) = α := by
      by_contra h
      apply hirr
      exact h
    obtain ⟨r, hr⟩ := hr
    have hA : (r.den : ℝ) * α = (r.num : ℝ) := by
      rw [← hr, Rat.cast_def]
      field_simp [r.den_nz]
    refine ⟨w 0, hw0, (0, (r.den : ℤ)), 1, by simp [r.den_nz], by simp, zero_lt_one, ?_⟩
    intro t _ht
    exact normalizedArc_mem_of_rational hc0 hd hB3 hlogc hα hβ hγ r.den_pos hA hF
      (w 0) hsample t

end BerendNormalizedCompactArc
end CubicTwoStage
