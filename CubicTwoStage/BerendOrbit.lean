/-
# Berend §4, Lemma 4.3: the backward orbit of a minimizing sequence

`CubicTwoStage/BerendFullCone.lean` stops at the *forward* half of plan §C.4:
from a minimal accumulating coordinate set `S` and an expanding family member it
produces points of `E` in the full cone over `S` at every scale.  Berend's §4
next needs the **backward** half: a single point `w 0` of `E` high up in the
cone together with an infinite chain

`⋯ ↦ w (j+1) ↦ w j ↦ ⋯ ↦ w 0`  (i.e. `diag lam (w (j+1)) = w j`)

of points of `E`.  That chain is what makes the *growth-rate comparison* of
Berend's Lemma 4.4 possible: `diag lam` is diagonal, so one has the closed form
`(lam i) ^ j * (w j) i = (w 0) i`; the chain therefore shrinks geometrically in
each coordinate at the rate `|lam i|`, and its directions concentrate on the
coordinates of minimal modulus.

## What is proved here

* `exists_backward_orbit` — **Berend Lemma 4.3**, compactness form: bounded
  backward charts of every length, ending in the annulus `‖·‖ ≥ a`, force an
  infinite backward orbit in the closed invariant set.  The proof is a genuine
  compactness argument, but instead of a diagonal subsequence extraction it uses
  Tychonoff's theorem on the product `ℕ → (ι → ℝ)` together with the
  cluster-point form of closedness (`IsClosed.mem_of_mapClusterPt`): every entry
  of the orbit must lie in a closed set in which the corresponding entry of the
  charts is eventually known to lie.
* `exists_backward_orbit_of_acc` — the lemma in the form plan §C.5 consumes: from
  `Acc E S` plus an expanding member.  The minimal hitting times of the annulus
  supply the charts (proper entries have norm `< a`, the annulus entry is at most
  `N a`), and they are unbounded because the starting cone points tend to `0`.
* `backward_orbit_coord` — the closed form `(lam i) ^ j * (w j) i = (w 0) i`.
* `backward_orbit_coord_tendsto_zero`, `backward_orbit_norm_tendsto_zero` — the
  chain shrinks to `0` geometrically, with an explicit rate.
* `backward_orbit_support_eq` — **minimality of `S` forces the support of `w 0`
  to be all of `S`**: `w j` has the same support as `w 0` for every `j`, so a
  strictly smaller support would accumulate at `0` inside a proper coordinate
  subspace, contradicting minimality.  Hence `w 0` lies in the **full cone** over
  `S`, which is exactly the extra information the growth-rate comparison needs.
* `exists_min_modulus_coord_vanishing` — Berend's "compare logarithmic absolute
  growth-rate ratios": the normalized direction `‖w j‖⁻¹ • w j` vanishes at every
  coordinate whose multiplier modulus is strictly larger than the minimal one.
* `diag_mul`, `diag_iterate_mul`, `invariant_diag_mul` — the bookkeeping for the
  paper's device of replacing `σ` by `σ ^ m * τ`: a product of diagonal maps is
  diagonal with the product multipliers, so the Lemma 4.3/4.4 analysis applies to
  every element of the semigroup and to all its products.

## Provenance

The public AMS full text of §4 could not be re-read while this file was written
(`ams.org` / `pubs.ams.org` answer automated requests with a browser check, and
the paper is not in `attachments/`).  `exists_backward_orbit` is therefore the
reconstruction of Lemma 4.3 from its role in the proof — "retain a nonzero limit
point and prove that backward iterates of the minimizing sequence converge to
iterates of that limit" — and is the standard backward-orbit compactness lemma.
Everything downstream is derived from it, not assumed.

No `axiom`, no `sorry`, no assumed `Prop`.  Imports only the project module
`BerendFullCone`, which is itself axiom free.
-/
import CubicTwoStage.BerendFullCone

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendSec4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Bookkeeping: iterates, Lipschitz bounds, closed coordinate subspaces -/

/-- Iterates of `diag lam` stay in a forward invariant set. -/
theorem iterate_mem {E : Set (ι → ℝ)} {lam : ι → ℝ} (hinv : ∀ x ∈ E, diag lam x ∈ E) :
    ∀ (k : ℕ) {x : ι → ℝ}, x ∈ E → ((diag lam)^[k]) x ∈ E := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; rw [Function.iterate_succ_apply]; exact ih (hinv x hx)

/-- A Lipschitz bound for the iterates of the diagonal map. -/
theorem iterate_norm_le {lam : ι → ℝ} {N : ℝ}
    (hN : ∀ x : ι → ℝ, ‖diag lam x‖ ≤ N * ‖x‖) (hN0 : 0 ≤ N) (k : ℕ) (x : ι → ℝ) :
    ‖((diag lam)^[k]) x‖ ≤ N ^ k * ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc ‖diag lam (((diag lam)^[k]) x)‖ ≤ N * ‖((diag lam)^[k]) x‖ := hN _
        _ ≤ N * (N ^ k * ‖x‖) := mul_le_mul_of_nonneg_left ih hN0
        _ = N ^ (k + 1) * ‖x‖ := by ring

/-- A coordinate subspace is closed. -/
theorem isClosed_coord (S : Set ι) : IsClosed (coord S : Set (ι → ℝ)) := by
  have h : (coord S : Set (ι → ℝ)) = {x : ι → ℝ | (fun i : {i // i ∉ S} => x i.1) = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, funext_iff, Pi.zero_apply]
    exact ⟨fun hx i => hx i.1 i.2, fun hx i hi => hx ⟨i, hi⟩⟩
  rw [h]
  exact isClosed_eq (continuous_pi fun i => continuous_apply i.1) continuous_const

/-- **Expansion pushes a nonzero point of a coordinate subspace past any bound.**
The annulus-half of Berend's Lemma 4.2, isolated for reuse. -/
theorem exists_iterate_norm_ge {lam : ι → ℝ} {S : Finset ι}
    (hexp : ∀ i ∈ S, 1 < |lam i|) {x : ι → ℝ} (hx : x ∈ coord (S : Set ι))
    (hxne : x ≠ 0) (a : ℝ) :
    ∃ n : ℕ, a ≤ ‖((diag lam)^[n]) x‖ := by
  classical
  have hne : ∃ i ∈ S, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxne (funext fun i => by
      by_cases hi : i ∈ S
      · exact h i hi
      · exact mem_coord.1 hx i hi)
  obtain ⟨i₀, hi₀S, hi₀ne⟩ := hne
  have hgt : 1 < |lam i₀| := hexp i₀ hi₀S
  have htend : Tendsto (fun n : ℕ => |lam i₀| ^ n * |x i₀|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const (abs_pos.2 hi₀ne)
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.1 htend) a
  refine ⟨n, le_trans (hn n le_rfl) ?_⟩
  have hcoord : (((diag lam)^[n]) x) i₀ = (lam i₀) ^ n * x i₀ := diag_iterate_apply lam n x i₀
  calc |lam i₀| ^ n * |x i₀| = ‖(((diag lam)^[n]) x) i₀‖ := by
        rw [hcoord, Real.norm_eq_abs, abs_mul, abs_pow]
    _ ≤ ‖((diag lam)^[n]) x‖ := norm_le_pi_norm _ _

/-! ## 2. Berend Lemma 4.3: bounded charts of every length give an infinite
backward orbit -/

/-- The `j`-th entry of the chart cut out by the `m`-th hitting time: the point of
`E` that reaches the annulus at time `jh m` and needs `j` further steps.  Past the
end of the chart the value is padded by `0`, which keeps every entry in a fixed
ball. -/
noncomputable def chartEntry (lam : ι → ℝ) (v : ℕ → ι → ℝ) (jh : ℕ → ℕ) (m j : ℕ) :
    ι → ℝ :=
  if j ≤ jh m then ((diag lam)^[jh m - j]) (v m) else 0

theorem chartEntry_of_le {lam : ι → ℝ} {v : ℕ → ι → ℝ} {jh : ℕ → ℕ} {m j : ℕ}
    (h : j ≤ jh m) : chartEntry lam v jh m j = ((diag lam)^[jh m - j]) (v m) := by
  rw [chartEntry, if_pos h]

theorem chartEntry_of_not_le {lam : ι → ℝ} {v : ℕ → ι → ℝ} {jh : ℕ → ℕ} {m j : ℕ}
    (h : ¬ j ≤ jh m) : chartEntry lam v jh m j = 0 := by
  rw [chartEntry, if_neg h]

/-- **Berend Lemma 4.3** (Trans. AMS 280 (1983), §4), compactness form.

Let `E` be closed and forward invariant under the diagonal map `diag lam`.  Let
`v m ∈ E` and suppose that for every `m` the time `jh m` at which the orbit of
`v m` enters the annulus `‖·‖ ≥ a` is finite, with

* the annulus entry `diag lam ^[jh m] (v m)` of norm at least `a`,
* every entry of the chart of length `jh m` of norm at most `R`,
* and `jh m → ∞`, so that charts of every prescribed length occur.

Then `E` contains an infinite backward orbit whose `0`-th term lies in the
annulus: there is `w : ℕ → ι → ℝ` with `w j ∈ E`, `diag lam (w (j+1)) = w j`,
`a ≤ ‖w 0‖` and `‖w j‖ ≤ R` for every `j`. -/
theorem exists_backward_orbit
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {v : ℕ → ι → ℝ} (hvE : ∀ m, v m ∈ E)
    {jh : ℕ → ℕ} (hjh : Tendsto jh atTop atTop)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hann : ∀ m, a ≤ ‖((diag lam)^[jh m]) (v m)‖)
    (hwin : ∀ m j, j ≤ jh m → ‖((diag lam)^[jh m - j]) (v m)‖ ≤ R) :
    ∃ w : ℕ → ι → ℝ, (∀ j, w j ∈ E) ∧ (∀ j, diag lam (w (j+1)) = w j) ∧
      a ≤ ‖w 0‖ ∧ ∀ j, ‖w j‖ ≤ R := by
  classical
  set c : ℕ → (ℕ → ι → ℝ) := fun m j => chartEntry lam v jh m j with hc
  have hcball : ∀ m j, c m j ∈ Metric.closedBall (0 : ι → ℝ) R := by
    intro m j
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hj : j ≤ jh m
    · rw [hc]
      simp only
      rw [chartEntry_of_le hj]
      exact hwin m j hj
    · rw [hc]
      simp only
      rw [chartEntry_of_not_le hj]
      simpa using le_trans ha.le haR
  -- the compact product of closed balls
  set K : Set (ℕ → ι → ℝ) := {x | ∀ j, x j ∈ Metric.closedBall (0 : ι → ℝ) R} with hK
  have hKeq : K = Set.univ.pi (fun _ : ℕ => Metric.closedBall (0 : ι → ℝ) R) := by
    ext x
    rw [hK]
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
  have hKcompact : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi (s := fun _ : ℕ => Metric.closedBall (0 : ι → ℝ) R)
      (fun _ => Metric.isCompact_iff_isClosed_bounded.2
        ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall⟩)
  have hcK : ∀ m, c m ∈ K := by
    intro m
    rw [hK]
    exact hcball m
  obtain ⟨x, -, hxcl⟩ := hKcompact.exists_mapClusterPt (u := c)
    (Filter.le_principal_iff.2
      (Filter.Eventually.of_forall (f := atTop) (p := fun m => c m ∈ K) hcK))
  -- evaluation at a fixed time preserves cluster points
  have hcoord : ∀ j, MapClusterPt (x j) atTop (fun m => c m j) := by
    intro j
    have hcont : Continuous fun y : ℕ → ι → ℝ => y j := continuous_apply j
    have h := hxcl.continuousAt_comp hcont.continuousAt
    simpa [Function.comp_def] using h
  have hEmem : ∀ j, x j ∈ E := by
    intro j
    refine hE.mem_of_mapClusterPt (hcoord j) ?_
    refine Eventually.mono (hjh.eventually (eventually_ge_atTop j)) ?_
    intro m hm
    rw [hc]
    simp only
    rw [chartEntry_of_le hm]
    exact iterate_mem hinv _ (hvE m)
  have hback : ∀ j, diag lam (x (j+1)) = x j := by
    intro j
    have hclosed : IsClosed {y : ℕ → ι → ℝ | diag lam (y (j+1)) = y j} := by
      have h1 : Continuous fun y : ℕ → ι → ℝ => diag lam (y (j+1)) :=
        (continuous_diag lam).comp (continuous_apply (j + 1))
      exact isClosed_eq h1 (continuous_apply j)
    refine hclosed.mem_of_mapClusterPt hxcl ?_
    refine Eventually.mono (hjh.eventually (eventually_ge_atTop (j + 1))) ?_
    intro m hm
    simp only [Set.mem_setOf_eq]
    have hj : j ≤ jh m := le_trans (Nat.le_succ j) hm
    rw [hc]
    simp only
    rw [chartEntry_of_le hm, chartEntry_of_le hj]
    have hstep : jh m - j = (jh m - (j + 1)) + 1 := by omega
    rw [hstep, Function.iterate_succ_apply']
  have hnorm : a ≤ ‖x 0‖ := by
    have hclosed : IsClosed {y : ℕ → ι → ℝ | a ≤ ‖y 0‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_apply 0))
    refine hclosed.mem_of_mapClusterPt hxcl ?_
    refine Eventually.of_forall ?_
    intro m
    simp only [Set.mem_setOf_eq]
    rw [hc]
    simp only
    rw [chartEntry_of_le (Nat.zero_le _)]
    exact hann m
  have hbdd : ∀ j, ‖x j‖ ≤ R := by
    intro j
    have hmem : x j ∈ Metric.closedBall (0 : ι → ℝ) R :=
      Metric.isClosed_closedBall.mem_of_mapClusterPt (hcoord j)
        (Filter.Eventually.of_forall fun m => hcball m j)
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  exact ⟨x, hEmem, hback, hnorm, hbdd⟩

/-! ## 3. Lemma 4.3 from the accumulation hypothesis of plan §C.4 -/

/-- **Berend Lemma 4.3**, starting from the accumulation hypothesis.

`E` is closed and invariant under `diag lam`, `S` is minimal among the coordinate
sets in which `E` accumulates at `0`, and `diag lam` expands on `S`.  Then for
every prescribed `a > 0` there is an infinite backward orbit of `diag lam` inside
`E ∩ coord S` whose `0`-th term has norm at least `a`.

The charts come from the minimal hitting times of the annulus `‖·‖ ≥ a`: every
proper entry has norm `< a`, the annulus entry is at most `N a`, and the hitting
times are unbounded because the starting cone points tend to `0`. -/
theorem exists_backward_orbit_of_acc
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {S : Finset ι} (hexp : ∀ i ∈ S, 1 < |lam i|)
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {a : ℝ} (ha : 0 < a) :
    ∃ w : ℕ → ι → ℝ, (∀ j, w j ∈ E) ∧ (∀ j, w j ∈ coord (S : Set ι)) ∧
      (∀ j, diag lam (w (j+1)) = w j) ∧ a ≤ ‖w 0‖ := by
  classical
  obtain ⟨N, hN1, hN⟩ := exists_norm_bound (ι := ι) lam
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hN0 : 0 ≤ N := le_of_lt hNpos
  -- the sequence of small cone points
  have hcone := acc_cone hacc hmin
  have hseq : ∀ m : ℕ, ∃ u : ι → ℝ, u ∈ E ∧ u ∈ coord (S : Set ι) ∧ u ≠ 0 ∧
      ‖u‖ < min a (a / ((m : ℝ) + 1)) := by
    intro m
    obtain ⟨u, huE, huc, hune, hult⟩ :=
      hcone (min a (a / ((m : ℝ) + 1))) (lt_min ha (by positivity))
    exact ⟨u, huE, cone_subset_coord S huc, hune, hult⟩
  choose v hvE hvS hvne hvlt using hseq
  -- the minimal hitting time of the annulus
  have hex : ∀ m, ∃ k : ℕ, a ≤ ‖((diag lam)^[k]) (v m)‖ := fun m =>
    exists_iterate_norm_ge hexp (hvS m) (hvne m) a
  set jh : ℕ → ℕ := fun m => Nat.find (hex m) with hjhdef
  have hann : ∀ m, a ≤ ‖((diag lam)^[jh m]) (v m)‖ := fun m => Nat.find_spec (hex m)
  have hsv : ∀ m, ‖v m‖ < a := fun m =>
    (hvlt m).trans_le (min_le_left a (a / ((m : ℝ) + 1)))
  have hjhpos : ∀ m, 1 ≤ jh m := by
    intro m
    rcases Nat.eq_zero_or_pos (jh m) with h | h
    · exfalso
      have hspec := hann m
      rw [h] at hspec
      simp only [Function.iterate_zero, id] at hspec
      linarith [hsv m]
    · exact h
  -- the chart bound
  have hwin : ∀ m j, j ≤ jh m → ‖((diag lam)^[jh m - j]) (v m)‖ ≤ N * a := by
    intro m j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- the annulus entry itself
      subst hj0
      have hprev : ‖((diag lam)^[jh m - 1]) (v m)‖ < a := by
        have hlt : jh m - 1 < jh m := Nat.sub_one_lt_of_lt (hjhpos m)
        exact not_le.1 (Nat.find_min (hex m) hlt)
      have hEq : jh m - 0 = (jh m - 1) + 1 := by
        rw [Nat.sub_zero, Nat.sub_add_cancel (hjhpos m)]
      have hstep : ((diag lam)^[jh m - 0]) (v m)
          = diag lam (((diag lam)^[jh m - 1]) (v m)) := by
        rw [hEq, Function.iterate_succ_apply']
      rw [hstep]
      calc ‖diag lam (((diag lam)^[jh m - 1]) (v m))‖
            ≤ N * ‖((diag lam)^[jh m - 1]) (v m)‖ := hN _
        _ ≤ N * a := mul_le_mul_of_nonneg_left hprev.le hN0
    · -- a proper entry
      have hsub : jh m - j < jh m := Nat.sub_lt (hjhpos m) hjpos
      have hsmall : ‖((diag lam)^[jh m - j]) (v m)‖ < a :=
        not_le.1 (Nat.find_min (hex m) hsub)
      exact le_trans hsmall.le (le_mul_of_one_le_left ha.le hN1)
  -- the hitting times are unbounded
  have hjh : Tendsto jh atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro K
    have hlim : Tendsto (fun m : ℕ => N ^ K * (a / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => a * ((1 : ℝ) / ((m : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a
      have h2 : (fun m : ℕ => a * ((1 : ℝ) / ((m : ℝ) + 1)))
          = fun m : ℕ => a / ((m : ℝ) + 1) := by
        funext m; rw [mul_one_div]
      rw [h2] at h1
      simpa using h1.const_mul (N ^ K)
    have hev : ∀ᶠ m : ℕ in atTop, N ^ K * (a / ((m : ℝ) + 1)) < a := by
      have hb := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) ha)
      filter_upwards [hb] with m hm
      rwa [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)] at hm
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    refine ⟨M, fun m hm => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hspec := hann m
    have hstep1 : ‖((diag lam)^[jh m]) (v m)‖ ≤ N ^ (jh m) * ‖v m‖ :=
      iterate_norm_le hN hN0 (jh m) (v m)
    have hle1 : N ^ (jh m) ≤ N ^ K := pow_le_pow_right₀ hN1 (le_of_lt hlt)
    have hle2 : ‖v m‖ ≤ a / ((m : ℝ) + 1) :=
      (hvlt m).le.trans (min_le_right a (a / ((m : ℝ) + 1)))
    have hle3 : N ^ (jh m) * ‖v m‖ ≤ N ^ K * (a / ((m : ℝ) + 1)) :=
      mul_le_mul hle1 hle2 (norm_nonneg _) (pow_nonneg hN0 K)
    linarith [hM m hm]
  -- apply the compactness lemma inside `E ∩ coord S`
  set E' : Set (ι → ℝ) := E ∩ coord ((S : Finset ι) : Set ι) with hE'
  have hE'closed : IsClosed E' := hE.inter (isClosed_coord _)
  have hinv' : ∀ x ∈ E', diag lam x ∈ E' := fun x hx =>
    ⟨hinv x hx.1, diag_mem_coord lam hx.2⟩
  have hvE' : ∀ m, v m ∈ E' := fun m => ⟨hvE m, hvS m⟩
  obtain ⟨w, hwE', hback, hann0, -⟩ :=
    exists_backward_orbit hE'closed hinv' hvE' hjh (a := a) (R := N * a) ha
      (le_mul_of_one_le_left ha.le hN1) hann hwin
  exact ⟨w, fun j => (hwE' j).1, fun j => (hwE' j).2, hback, hann0⟩

/-! ## 4. The closed form of a backward orbit -/

/-- **The coordinate formula for a backward orbit.**  Because `diag lam` is
diagonal, the chain is determined by its `0`-th term:
`(lam i) ^ j * (w j) i = (w 0) i` for every `j` and every coordinate `i`. -/
theorem backward_orbit_coord {lam : ι → ℝ} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) (i : ι) :
    ∀ j : ℕ, (lam i) ^ j * w j i = w 0 i := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : lam i * w (j + 1) i = w j i := by
        have h := congrFun (hback j) i
        simpa [diag_apply] using h
      calc (lam i) ^ (j + 1) * w (j + 1) i
          = (lam i) ^ j * (lam i * w (j + 1) i) := by ring
        _ = (lam i) ^ j * w j i := by rw [h1]
        _ = w 0 i := ih

/-- The quotient form of `backward_orbit_coord`. -/
theorem backward_orbit_apply {lam : ι → ℝ} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) {i : ι} (hne : lam i ≠ 0) (j : ℕ) :
    w j i = w 0 i / (lam i) ^ j := by
  rw [eq_div_iff (pow_ne_zero j hne), mul_comm]
  exact backward_orbit_coord hback i j

/-- The absolute-value form of `backward_orbit_apply`. -/
theorem backward_orbit_abs_apply {lam : ι → ℝ} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) {i : ι} (hne : lam i ≠ 0) (j : ℕ) :
    |w j i| = |w 0 i| / |lam i| ^ j := by
  rw [backward_orbit_apply hback hne j, abs_div, abs_pow]

/-- A backward orbit is nonzero at every time as soon as its `0`-th term is, as
long as the multipliers in sight are nonzero. -/
theorem backward_orbit_ne_zero {lam : ι → ℝ} {S : Finset ι} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) (_hlam : ∀ i ∈ S, lam i ≠ 0)
    (hwS : ∀ j, w j ∈ coord (S : Set ι)) (h0 : w 0 ≠ 0) (j : ℕ) : w j ≠ 0 := by
  intro hzero
  refine h0 (funext fun i => ?_)
  by_cases hi : i ∈ S
  · have h1 := backward_orbit_coord hback i j
    rw [hzero] at h1
    simp only [Pi.zero_apply, mul_zero] at h1
    exact h1.symm
  · exact mem_coord.1 (hwS 0) i hi

/-- **A backward orbit shrinks to `0` at every coordinate of `S`.** -/
theorem backward_orbit_coord_tendsto_zero {lam : ι → ℝ} {S : Finset ι} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hexp : ∀ i ∈ S, 1 < |lam i|)
    {i : ι} (hi : i ∈ S) :
    Tendsto (fun j : ℕ => w j i) atTop (𝓝 0) := by
  have hgt : 1 < |lam i| := hexp i hi
  have hne : lam i ≠ 0 := by
    intro h
    rw [h, abs_zero] at hgt
    linarith
  have hlim : Tendsto (fun j : ℕ => |w 0 i| / |lam i| ^ j) atTop (𝓝 0) := by
    have h2 : Tendsto (fun j : ℕ => (|lam i| ^ j)⁻¹) atTop (𝓝 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hgt).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using h2.const_mul |w 0 i|
  have habs : Tendsto (fun j : ℕ => |w j i|) atTop (𝓝 0) :=
    hlim.congr' (Filter.Eventually.of_forall fun j =>
      (backward_orbit_abs_apply hback hne j).symm)
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)

/-- A division identity used in the growth-rate comparison. -/
theorem div_div_div_eq' {a b c d : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a / b / (c / d) = a / c * (d / b) := by
  field_simp

/-- **A backward orbit shrinks to `0` in norm**, at a geometric rate. -/
theorem backward_orbit_norm_tendsto_zero {lam : ι → ℝ} {S : Finset ι} {w : ℕ → ι → ℝ}
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hSne : S.Nonempty)
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hwS : ∀ j, w j ∈ coord (S : Set ι)) :
    Tendsto (fun j : ℕ => ‖w j‖) atTop (𝓝 0) := by
  classical
  obtain ⟨k, hkS, hkmin⟩ := Finset.exists_min_image S (fun i => |lam i|) hSne
  set c : ℝ := |lam k| with hcdef
  have hc1 : 1 < c := hexp k hkS
  have hc0 : 0 < c := lt_trans zero_lt_one hc1
  have hge : ∀ i ∈ S, c ≤ |lam i| := fun i hi => hkmin i hi
  set C : ℝ := ∑ i : ι, |w 0 i| with hC
  have hne : ∀ i ∈ S, lam i ≠ 0 := by
    intro i hi h
    have := hexp i hi
    rw [h, abs_zero] at this
    linarith
  have hbound : ∀ j : ℕ, ‖w j‖ ≤ C / c ^ j := by
    intro j
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    by_cases hi : i ∈ S
    · rw [backward_orbit_abs_apply hback (hne i hi) j, div_eq_mul_inv, div_eq_mul_inv]
      have h1 : (|lam i| ^ j)⁻¹ ≤ (c ^ j)⁻¹ :=
        inv_anti₀ (pow_pos hc0 j) (pow_le_pow_left₀ hc0.le (hge i hi) j)
      refine le_trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact Finset.single_le_sum (f := fun i => |w 0 i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)
    · have hzero : w j i = 0 := mem_coord.1 (hwS j) i hi
      rw [hzero, abs_zero]
      positivity
  refine squeeze_zero (fun j => norm_nonneg _) hbound ?_
  have hlim : Tendsto (fun j : ℕ => (c ^ j)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).inv_tendsto_atTop
  simpa [div_eq_mul_inv] using hlim.const_mul C

/-! ## 5. Minimality forces the support of the limit point to be all of `S` -/

/-- **Minimality identifies the support.**  Suppose `S` is minimal among the
coordinate sets in which `E` accumulates at `0` and `w` is a backward orbit in
`E ∩ coord S` with `w 0 ≠ 0`.  Then every coordinate of `S` is nonzero at
`w 0`: a vanishing coordinate would give a strictly smaller support, and since
`w j` has the same support as `w 0` for all `j`, the orbit would accumulate at
`0` inside the proper coordinate subspace `S.filter (w 0 · ≠ 0)`.

In particular the limit point `w 0` lies in the **full cone** over `S` — the form
in which the growth-rate comparison of Berend's Lemma 4.4 uses it. -/
theorem backward_orbit_support_eq {E : Set (ι → ℝ)} {lam : ι → ℝ} {S : Finset ι}
    {w : ℕ → ι → ℝ} (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hSne : S.Nonempty)
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hwE : ∀ j, w j ∈ E)
    (hwS : ∀ j, w j ∈ coord (S : Set ι)) (h0 : w 0 ≠ 0) :
    ∀ i ∈ S, w 0 i ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀S, hi₀0⟩ := hcon
  have hlam : ∀ i ∈ S, lam i ≠ 0 := by
    intro i hi h
    exact absurd (hexp i hi) (by rw [h, abs_zero]; norm_num)
  set T : Finset ι := S.filter (fun i => w 0 i ≠ 0) with hT
  have hTS : T ⊆ S := by rw [hT]; exact Finset.filter_subset _ _
  have hTsub : T ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hTS, ?_⟩
    intro hEq
    have hmem : i₀ ∈ T := hEq ▸ hi₀S
    rw [hT, Finset.mem_filter] at hmem
    exact hmem.2 hi₀0
  have hAccT : Acc E T := by
    rw [acc_iff]
    intro ε hε
    have hlim := backward_orbit_norm_tendsto_zero hback hSne hexp hwS
    have hev : ∀ᶠ j : ℕ in atTop, ‖w j‖ < ε := by
      have hb := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
      filter_upwards [hb] with j hj
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hj
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    have hne : w N₀ ≠ 0 := backward_orbit_ne_zero hback hlam hwS h0 N₀
    refine ⟨w N₀, hwE N₀, ?_, hne, hN₀ N₀ le_rfl⟩
    intro i hi
    by_cases hiS : i ∈ S
    · have hzero : w 0 i = 0 := by
        by_contra hc
        exact hi (by rw [hT]; exact Finset.mem_filter.2 ⟨hiS, hc⟩)
      rw [backward_orbit_apply hback (hlam i hiS) N₀, hzero]
      simp
    · exact mem_coord.1 (hwS N₀) i hiS
  exact hmin T hTsub hAccT

/-- **The limit point of the backward orbit lies in the full cone.** -/
theorem backward_orbit_mem_cone {E : Set (ι → ℝ)} {lam : ι → ℝ} {S : Finset ι}
    {w : ℕ → ι → ℝ} (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hSne : S.Nonempty)
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hwE : ∀ j, w j ∈ E)
    (hwS : ∀ j, w j ∈ coord (S : Set ι)) (h0 : w 0 ≠ 0) :
    w 0 ∈ cone S :=
  ⟨hwS 0, backward_orbit_support_eq hmin hback hSne hexp hwE hwS h0⟩

/-- **Minimality forbids backward orbits inside proper coordinate subspaces.**  A
backward orbit of `E` supported in a proper coordinate subset `T ⊂ S` would
accumulate at `0` inside `T` — its norm tends to `0` by
`backward_orbit_norm_tendsto_zero`, and expansion on `S` restricts to `T` — which
minimality of `S` rules out.

This is the exact form in which minimality constrains the growth-rate analysis:
it forbids *supports* in proper subspaces, but by `backward_orbit_mem_cone` it
does **not** forbid the projective directions from concentrating in one (see
`exists_min_modulus_coord_vanishing`).  The gap between those two statements is
the content of Berend's Lemma 4.4. -/
theorem not_exists_backward_orbit_of_ssubset {E : Set (ι → ℝ)} {lam : ι → ℝ}
    {S T : Finset ι} {w : ℕ → ι → ℝ} (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hTS : T ⊂ S)
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hwE : ∀ j, w j ∈ E)
    (hwT : ∀ j, w j ∈ coord (T : Set ι)) (h0 : w 0 ≠ 0) : False := by
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · exfalso
      have hne := hwT 0
      rw [h] at hne
      refine h0 (funext fun i => ?_)
      exact mem_coord.1 hne i (by simp)
    · exact h
  have hexpT : ∀ i ∈ T, 1 < |lam i| := fun i hi => hexp i (hTS.subset hi)
  have hAccT : Acc E T := by
    rw [acc_iff]
    intro ε hε
    have hlim := backward_orbit_norm_tendsto_zero hback hTne hexpT hwT
    have hev : ∀ᶠ j : ℕ in atTop, ‖w j‖ < ε := by
      have hb := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
      filter_upwards [hb] with j hj
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hj
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    refine ⟨w N₀, hwE N₀, hwT N₀, ?_, hN₀ N₀ le_rfl⟩
    intro hzero
    refine h0 (funext fun i => ?_)
    by_cases hi : i ∈ T
    · have h1 := backward_orbit_coord hback i N₀
      rw [hzero] at h1
      simpa using h1.symm
    · exact mem_coord.1 (hwT 0) i hi
  exact hmin T hTS hAccT

/-! ## 6. The growth-rate comparison: fast coordinates die in the limit -/

/-- **Berend's growth-rate comparison.**  Along a backward orbit, the normalized
direction `‖w j‖⁻¹ • w j` vanishes at every coordinate `i ∈ S` whose multiplier
modulus is strictly larger than that of another coordinate `k ∈ S` at which
`w 0` does not vanish: `|w j i| / ‖w j‖ → 0`.

Thus, if the moduli on `S` are not all equal, the accumulation directions of `E`
at `0` concentrate in the proper coordinate subspace spanned by the coordinates
of minimal modulus — the phenomenon Berend's Lemma 4.4 turns into accumulation of
`E` inside a proper coordinate subspace. -/
theorem backward_orbit_coord_ratio_tendsto_zero {lam : ι → ℝ} {S : Finset ι}
    {w : ℕ → ι → ℝ} (hback : ∀ j, diag lam (w (j+1)) = w j)
    (hexp : ∀ i ∈ S, 1 < |lam i|) {i k : ι} (hi : i ∈ S) (hk : k ∈ S)
    (hcone : w 0 k ≠ 0) (hlt : |lam k| < |lam i|) :
    Tendsto (fun j : ℕ => |w j i| / ‖w j‖) atTop (𝓝 0) := by
  have hkne : lam k ≠ 0 := by
    intro h
    have := hexp k hk
    rw [h, abs_zero] at this
    linarith
  have hine : lam i ≠ 0 := by
    intro h
    have := hexp i hi
    rw [h, abs_zero] at this
    linarith
  have hwk0 : (0 : ℝ) < |w 0 k| := abs_pos.2 hcone
  have hwjne : ∀ j, w j k ≠ 0 := by
    intro j hj
    have h := backward_orbit_coord hback k j
    rw [hj, mul_zero] at h
    exact hcone h.symm
  have hbound : ∀ j : ℕ, |w j i| / ‖w j‖
      ≤ (|w 0 i| / |w 0 k|) * (|lam k| / |lam i|) ^ j := by
    intro j
    have hnum : |w j i| = |w 0 i| / |lam i| ^ j := backward_orbit_abs_apply hback hine j
    have hden : |w j k| = |w 0 k| / |lam k| ^ j := backward_orbit_abs_apply hback hkne j
    have hnorm : |w j k| ≤ ‖w j‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm _ k
    have hpos : 0 < |w 0 k| / |lam k| ^ j := by positivity
    have hnormpos : 0 < ‖w j‖ := by
      rw [← hden] at hpos
      exact lt_of_lt_of_le hpos hnorm
    rw [hnum]
    have hstep : |w 0 i| / |lam i| ^ j / ‖w j‖
        ≤ |w 0 i| / |lam i| ^ j / (|w 0 k| / |lam k| ^ j) := by
      rw [div_le_div_iff₀ hnormpos hpos, ← hden]
      exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [div_div_div_eq' (a := |w 0 i|) (b := |lam i| ^ j) (c := |w 0 k|)
      (d := |lam k| ^ j) (pow_ne_zero j (abs_ne_zero.2 hine)) (ne_of_gt hwk0)
      (pow_ne_zero j (abs_ne_zero.2 hkne)), ← div_pow]
  have hratio_lt : |lam k| / |lam i| < 1 := by
    rw [div_lt_one (abs_pos.2 hine)]
    exact hlt
  have hratio0 : 0 ≤ |lam k| / |lam i| :=
    div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hgeo : Tendsto (fun j : ℕ => (|lam k| / |lam i|) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio_lt
  have hgeo2 : Tendsto (fun j : ℕ => (|w 0 i| / |w 0 k|) * (|lam k| / |lam i|) ^ j)
      atTop (𝓝 0) := by
    simpa using hgeo.const_mul (|w 0 i| / |w 0 k|)
  exact squeeze_zero (fun j => by positivity) hbound hgeo2

/-- **The growth-rate comparison at the minimal coordinate of `S`.**  Under the
hypotheses of `backward_orbit_support_eq` (minimality of `S` and `w 0 ≠ 0`) there
is a coordinate `k ∈ S` of minimal modulus such that every coordinate of `S` with
strictly larger modulus dies in the projective limit. -/
theorem exists_min_modulus_coord_vanishing {E : Set (ι → ℝ)} {lam : ι → ℝ}
    {S : Finset ι} {w : ℕ → ι → ℝ} (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    (hback : ∀ j, diag lam (w (j+1)) = w j) (hSne : S.Nonempty)
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hwE : ∀ j, w j ∈ E)
    (hwS : ∀ j, w j ∈ coord (S : Set ι)) (h0 : w 0 ≠ 0) :
    ∃ k ∈ S, ∀ i ∈ S, |lam k| < |lam i| →
      Tendsto (fun j : ℕ => |w j i| / ‖w j‖) atTop (𝓝 0) := by
  obtain ⟨k, hkS, hkmin⟩ := Finset.exists_min_image S (fun i => |lam i|) hSne
  have hsupport := backward_orbit_support_eq hmin hback hSne hexp hwE hwS h0
  exact ⟨k, hkS, fun i hi hlt =>
    backward_orbit_coord_ratio_tendsto_zero hback hexp (i := i) (k := k) hi hkS
      (hsupport k hkS) hlt⟩

/-- **Lemma 4.3 assembled with all its consequences** — the exact input of Berend's
Lemma 4.4.  From a minimal accumulating coordinate set `S` and an expanding family
member one gets, for every prescribed scale `a > 0`, a single backward orbit
`w` with all of:

* `w j ∈ E ∩ coord S` and `diag lam (w (j+1)) = w j`,
* `a ≤ ‖w 0‖` (the limit point lies in the annulus) and `‖w j‖ → 0`,
* `w 0` in the **full cone** over `S` (minimality forces the support),
* the growth-rate conclusion: the projective directions of `w` concentrate on the
  coordinates of `S` of minimal multiplier modulus. -/
theorem exists_backward_orbit_cone
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {S : Finset ι} (hexp : ∀ i ∈ S, 1 < |lam i|)
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {a : ℝ} (ha : 0 < a) :
    ∃ w : ℕ → ι → ℝ, (∀ j, w j ∈ E) ∧ (∀ j, w j ∈ coord (S : Set ι)) ∧
      (∀ j, diag lam (w (j+1)) = w j) ∧ a ≤ ‖w 0‖ ∧ w 0 ∈ cone S ∧
      Tendsto (fun j : ℕ => ‖w j‖) atTop (𝓝 0) ∧
      ∃ k ∈ S, ∀ i ∈ S, |lam k| < |lam i| →
        Tendsto (fun j : ℕ => |w j i| / ‖w j‖) atTop (𝓝 0) := by
  obtain ⟨w, hwE, hwS, hback, hann⟩ :=
    exists_backward_orbit_of_acc hE hinv hexp hacc hmin ha
  have hSne : S.Nonempty := acc_nonempty hacc
  have h0 : w 0 ≠ 0 := by
    intro h
    rw [h] at hann
    simp at hann
    linarith
  exact ⟨w, hwE, hwS, hback, hann,
    backward_orbit_mem_cone hmin hback hSne hexp hwE hwS h0,
    backward_orbit_norm_tendsto_zero hback hSne hexp hwS,
    exists_min_modulus_coord_vanishing hmin hback hSne hexp hwE hwS h0⟩

/-! ## 7. The multiplicative device: replacing `σ` by `σ ^ m * τ` -/

/-- A product of diagonal maps is diagonal, with the product multipliers. -/
theorem diag_comp (lam mu : ι → ℝ) (x : ι → ℝ) :
    diag lam (diag mu x) = diag (fun i => lam i * mu i) x := by
  funext i
  simp only [diag_apply]
  ring

/-- Iterates of `diag lam` composed with `diag mu`. -/
theorem diag_iterate_mul (lam mu : ι → ℝ) (m : ℕ) (x : ι → ℝ) :
    ((diag lam)^[m]) (diag mu x) = diag (fun i => (lam i) ^ m * mu i) x := by
  funext i
  simp only [diag_iterate_apply, diag_apply]
  ring

/-- **Invariance under `σ ^ m * τ`.**  A set invariant under two diagonal maps is
invariant under every product of a power of the first with the second — the device
by which Berend replaces `σ` by `σ ^ m * τ` in the growth-rate argument. -/
theorem invariant_diag_mul {E : Set (ι → ℝ)} {lam mu : ι → ℝ}
    (h1 : ∀ x ∈ E, diag lam x ∈ E) (h2 : ∀ x ∈ E, diag mu x ∈ E) (m : ℕ) :
    ∀ x ∈ E, diag (fun i => (lam i) ^ m * mu i) x ∈ E := by
  intro x hx
  rw [← diag_iterate_mul]
  exact iterate_mem h1 m (h2 x hx)

end BerendSec4

end CubicTwoStage
