/-
# Expansion/covering toolkit for Stage C of Berend's multi-invariance theorem

Project-owned copy of the covering / difference-set / tangent-cone toolkit
(namespace `BerendExpansion`), together with its instantiation at the project's
model space `Pt = Fin 3 → ℝ` and its quotient `Pt ⧸ L` in §8.  It isolates the
*covering* half of Berend §4 (stage C of `BEREND_PROOF_PLAN.md`, steps
C.2/C.4/C.6): the step which, from

* a set `B` invariant under an endomorphism `s` of an abelian group, and
* a neighbourhood `U` of `0` contained in `B`,

concludes `B = univ` because the iterates `s^k '' U` expand to cover the whole
group.

Everything here is unconditional, uses no project axiom, and imports only
Mathlib.  The abstract form comes first
(`eq_univ_of_mapsTo_of_iterate_cover` and its closed/dense variant); then the
concrete one-parameter instance on the circle `AddCircle 1` for multiplication
by `n ≥ 2`, where the covering hypothesis is *proved*
(`AddCircle.eq_univ_of_nsmul_of_ball`); then the difference-set corollary
(`AddCircle.sub_eq_univ_of_ball_subset`), which is the shape in which stage D
consumes stage C: if the difference set `Y - Y` of an `n`-invariant set `Y`
contains a neighbourhood of `0`, then `Y - Y` is the whole circle.

What is *not* here: the converse direction ("if `0` is a non-isolated point of
the closed invariant set `B`, then `B - B` contains a neighbourhood of `0`") is
Berend's Lemma 4.2/4.4 and is exactly where the multiplicative independence
(B3) is consumed.  It is not formalised in this module.
-/
import CubicTwoStage.Basic

open Set Function Metric Filter
open scoped Pointwise Topology

namespace BerendExpansion

/-! ## 1. Abstract covering lemmas -/

section Abstract

variable {T : Type*}

/-- **Iterate covering.**  A set `B` containing `U` and invariant under `s`
contains `s^[k] '' U` for every `k`, hence is everything as soon as the
iterates of `U` cover the ambient type.

In stage C of the plan this is the "*expansion and translation*" step: `U` is
the open subset of the invariant coordinate subspace produced by B2 and the
annulus compactness argument, and `s` runs over the members of `Σ`, which expand
on that subspace. -/
theorem eq_univ_of_mapsTo_of_iterate_cover {s : T → T} {B U : Set T}
    (hB : MapsTo s B B) (hU : U ⊆ B)
    (hcover : ∀ x : T, ∃ k : ℕ, x ∈ s^[k] '' U) : B = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨k, y, hy, rfl⟩ := hcover x
  exact hB.iterate k (hU hy)

/-- **Iterate covering, closure form.**  The covering hypothesis weakened to
density of the union of the iterates (the form produced by compactness
arguments that only know the iterates fill a dense set), paid for by closedness
of `B`. -/
theorem eq_univ_of_isClosed_of_dense_iUnion_iterate {T : Type*} [TopologicalSpace T]
    {s : T → T} {B U : Set T} (hclosed : IsClosed B) (hB : MapsTo s B B)
    (hU : U ⊆ B) (hdense : Dense (⋃ k : ℕ, s^[k] '' U)) : B = univ := by
  have hsub : (⋃ k : ℕ, s^[k] '' U) ⊆ B := by
    intro x hx
    simp only [mem_iUnion, mem_image] at hx
    obtain ⟨k, y, hy, rfl⟩ := hx
    exact hB.iterate k (hU hy)
  have huniv : (univ : Set T) ⊆ B := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  exact eq_univ_of_forall fun x => huniv (mem_univ x)

/-- **A neighbourhood of the identity gives everything.**  Same statement with
`U` open, which is the form in which the plan states C.4. -/
theorem eq_univ_of_isClosed_of_isOpen_cover {T : Type*} [TopologicalSpace T]
    {s : T → T} {B U : Set T} (_hclosed : IsClosed B) (hB : MapsTo s B B)
    (hU : U ⊆ B) (_hUopen : IsOpen U)
    (hcover : ∀ x : T, ∃ k : ℕ, x ∈ s^[k] '' U) : B = univ :=
  eq_univ_of_mapsTo_of_iterate_cover hB hU hcover

end Abstract

/-! ## 2. The one-parameter instance on the circle

For `s : y ↦ n • y` on `AddCircle 1` with `n ≥ 2`, the covering hypothesis of
§1 holds for *every* neighbourhood of `0`: every point of the circle is the
image of a point within distance `δ` of `0` under `n ^ k • ·`, for `k` large.
This is where the Archimedean property of `ℝ` is used. -/

namespace AddCircle

variable {n : ℕ}

/-- The `k`-th iterate of `y ↦ n • y` on the circle is `y ↦ n ^ k • y`. -/
theorem iterate_nsmul_apply (n k : ℕ) (y : AddCircle (1 : ℝ)) :
    (fun z : AddCircle (1 : ℝ) => n • z)^[k] y = n ^ k • y := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ, mul_nsmul]

/-- **The expansion/covering fact.**  For `n ≥ 2`, every point of the circle is
the `n ^ k`-th multiple of a point within distance `δ` of `0`. -/
theorem exists_pow_nsmul_mem_ball (n : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (z : AddCircle (1 : ℝ)) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : AddCircle (1 : ℝ)) δ, n ^ k • y = z := by
  -- a lift of `z` in `[0,1)`
  set w : Set.Ico (0 : ℝ) (0 + 1) := AddCircle.equivIco (1 : ℝ) 0 z with hw
  have hw1 : (w : ℝ) < 1 := by simpa using w.2.2
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := w.2.1
  have hwz : (↑(w : ℝ) : AddCircle (1 : ℝ)) = z := by
    have h := AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := z)
    rw [← hw] at h
    exact h
  -- choose `k ≥ 1` with `n ^ k` large
  have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (1 / δ) hn'
  set k : ℕ := max k₀ 1 with hk
  have hk1 : 1 ≤ k := le_max_right _ _
  have hkmono : (n : ℝ) ^ k₀ ≤ (n : ℝ) ^ k :=
    pow_le_pow_right₀ hn'.le (le_max_left _ _)
  have hbig : 1 / δ < (n : ℝ) ^ k := lt_of_lt_of_le hk₀ hkmono
  have hnkpos : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  have hnk2 : (2 : ℝ) ≤ (n : ℝ) ^ k := by
    calc (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      _ = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ k := pow_le_pow_right₀ hn'.le hk1
  -- the small preimage
  set r : ℝ := (w : ℝ) / (n : ℝ) ^ k with hr
  have hr0 : 0 ≤ r := div_nonneg hw0 hnkpos.le
  have hr_half : r < 1 / 2 := by
    rw [hr, div_lt_iff₀ hnkpos]; nlinarith
  have hrδ : r < δ := by
    rw [hr, div_lt_iff₀ hnkpos]
    rw [div_lt_iff₀ hδ] at hbig
    nlinarith
  refine ⟨k, (r : AddCircle (1 : ℝ)), ?_, ?_⟩
  · -- it lies within `δ` of `0`
    rw [Metric.mem_ball, dist_zero_right, AddCircle.norm_eq]
    have hround : round ((1 : ℝ)⁻¹ * r) = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith
    rw [hround, Int.cast_zero, zero_mul, sub_zero, abs_of_nonneg hr0]
    exact hrδ
  · -- and `n ^ k` times it is `z`
    have hmul : (n : ℝ) ^ k * r = (w : ℝ) := by
      rw [hr]; field_simp
    calc n ^ k • (r : AddCircle (1 : ℝ))
        = (↑((n : ℝ) ^ k * r) : AddCircle (1 : ℝ)) := by
          rw [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_pow]
      _ = (↑(w : ℝ) : AddCircle (1 : ℝ)) := by rw [hmul]
      _ = z := hwz

/-- **A set containing a neighbourhood of `0` and invariant under `y ↦ n • y`
is the whole circle** (`n ≥ 2`).  This is the conclusion of stage C for a single
expanding multiplier. -/
theorem eq_univ_of_nsmul_of_ball (n : ℕ) (hn : 2 ≤ n) {B : Set (AddCircle (1 : ℝ))}
    (hinv : ∀ y ∈ B, n • y ∈ B) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : AddCircle (1 : ℝ)) δ ⊆ B) : B = univ := by
  refine eq_univ_of_mapsTo_of_iterate_cover (s := fun z => n • z) ?_ hball ?_
  · intro y hy
    exact hinv y hy
  · intro x
    obtain ⟨k, y, hy, hxy⟩ := exists_pow_nsmul_mem_ball n hn hδ x
    exact ⟨k, y, hy, by rw [iterate_nsmul_apply]; exact hxy⟩

/-- **Difference-set corollary** (the shape stage D consumes).  If `Y` is
invariant under `y ↦ n • y` and `Y - Y` contains a neighbourhood of `0`, then
`Y - Y` is the whole circle.

No closedness of `Y` is needed: `n ≥ 2` and forward invariance of `Y` suffice,
because `Y - Y` is then automatically forward invariant. -/
theorem sub_eq_univ_of_ball_subset (n : ℕ) (hn : 2 ≤ n) {Y : Set (AddCircle (1 : ℝ))}
    (hinv : ∀ y ∈ Y, n • y ∈ Y) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : AddCircle (1 : ℝ)) δ ⊆ Y - Y) : Y - Y = univ := by
  have hinv' : ∀ y ∈ Y - Y, n • y ∈ Y - Y := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨n • a, hinv a ha, n • b, hinv b hb, by rw [nsmul_sub]⟩
  exact eq_univ_of_nsmul_of_ball n hn hinv' hδ hball

end AddCircle

/-! ## 3. The quotient form: expanding scalar maps on `V ⧸ L`

This is the form in which stage C reaches the torus `Pt ⧸ L`.  A map `s` of the
quotient that is induced by a scalar multiplication `x ↦ c • x` with `c > 1`
covers every ball around `0` by its iterates of the preimage:

every `z` is `s ^ k` of a point within `δ` of `0`, for `k` large.

The proof is the Archimedean argument of §2 in the normed setting: reduce a
representative `t` of `z`, and use that the quotient norm is dominated by the
norm of any representative (`QuotientAddGroup.norm_mk_le_norm`). -/

section Quotient

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The iterates of a map induced by scalar multiplication are induced by the
powers of the scalar. -/
theorem iterate_of_scalar_apply (L : AddSubgroup V) (s : V ⧸ L → V ⧸ L) (c : ℝ)
    (hs : ∀ t : V, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (c • t))
    (k : ℕ) (t : V) :
    s^[k] (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (c ^ k • t) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hs, smul_smul, pow_succ']

/-- **The covering fact for expanding scalar maps on a quotient.**  If `c > 1`
and `s` is induced by `x ↦ c • x` on `V ⧸ L`, then every point of `V ⧸ L` is
`s ^ k` of a point within distance `δ` of `0`. -/
theorem exists_iterate_mem_ball_of_scalar (L : AddSubgroup V) (s : V ⧸ L → V ⧸ L)
    {c : ℝ} (hc : 1 < c)
    (hs : ∀ t : V, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (c • t))
    {δ : ℝ} (hδ : 0 < δ) (z : V ⧸ L) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : V ⧸ L) δ, s^[k] y = z := by
  have hc0 : (0 : ℝ) < c := lt_trans zero_lt_one hc
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  have hcpow : Tendsto (fun k : ℕ => c ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hc
  have hzero : Tendsto (fun k : ℕ => ‖t‖ / c ^ k) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hcpow
  have hev : ∀ᶠ k : ℕ in atTop, ‖t‖ / c ^ k < δ :=
    (tendsto_order.1 hzero).2 δ hδ
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖t‖ / c ^ k < δ := ⟨a, ha a le_rfl⟩
  refine ⟨k, QuotientAddGroup.mk' L ((c ^ k)⁻¹ • t), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖QuotientAddGroup.mk' L ((c ^ k)⁻¹ • t)‖ ≤ ‖(c ^ k)⁻¹ • t‖ :=
      QuotientAddGroup.norm_mk_le_norm
    have h2 : ‖(c ^ k)⁻¹ • t‖ = ‖t‖ / c ^ k := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hc0]
      field_simp
    linarith
  · rw [iterate_of_scalar_apply L s c hs k ((c ^ k)⁻¹ • t)]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k hc0.ne'), one_smul]

/-- **A set of the quotient containing a ball around `0` and invariant under an
expanding scalar map is everything.** -/
theorem eq_univ_of_invariant_of_scalar (L : AddSubgroup V) (s : V ⧸ L → V ⧸ L)
    {c : ℝ} (hc : 1 < c)
    (hs : ∀ t : V, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (c • t))
    {B : Set (V ⧸ L)} (hinv : ∀ y ∈ B, s y ∈ B) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : V ⧸ L) δ ⊆ B) : B = univ :=
  eq_univ_of_mapsTo_of_iterate_cover (s := s) (fun _ hy => hinv _ hy) hball
    fun z => exists_iterate_mem_ball_of_scalar L s hc hs hδ z

/-- **Difference-set form** for an additive expanding quotient map: if `Y - Y`
contains a ball around `0` then `Y - Y` is everything.  This is the boundary
between stage C and stage D of the plan. -/
theorem sub_eq_univ_of_ball_subset_of_scalar (L : AddSubgroup V) (s : V ⧸ L →+ V ⧸ L)
    (c : ℝ) (hc : 1 < c)
    (hs : ∀ t : V, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (c • t))
    {Y : Set (V ⧸ L)} (hinv : ∀ y ∈ Y, s y ∈ Y) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : V ⧸ L) δ ⊆ Y - Y) : Y - Y = univ := by
  have hinv' : ∀ y ∈ Y - Y, s y ∈ Y - Y := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨s a, hinv a ha, s b, hinv b hb, (map_sub s a b).symm⟩
  exact eq_univ_of_invariant_of_scalar L (s : V ⧸ L → V ⧸ L) hc hs hinv' hδ hball

end Quotient

/-! ## 4. The coordinatewise (simultaneously diagonal) case

Stage C works in the common eigenbasis supplied by stage A, where every member of
`Σ` scales each coordinate separately (Berend Lemma 3.4).  The covering
argument is then purely coordinatewise: one `k` works simultaneously in all
coordinates, because the coordinates with small multiplier need a larger `k`
only.  This is the abstract form of "each map is uniformly expanding on the
selected invariant coordinate subspace" (C.3) followed by "expansion and
translation" (C.4). -/

section Product

variable {ι : Type*}

/-- Iterating coordinatewise scaling multiplies each coordinate by the
corresponding power. -/
theorem iterate_pi_mul (c : ι → ℝ) (k : ℕ) (y : ι → ℝ) :
    (fun z : ι → ℝ => fun i => c i * z i)^[k] y = fun i => (c i) ^ k * y i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i
      show c i * (c i ^ k * y i) = c i ^ (k + 1) * y i
      rw [pow_succ]
      ring

variable [Fintype ι]

/-- **Covering for a diagonal expanding map.**  If every coordinate multiplier
exceeds `1`, then every point of `ι → ℝ` is the image under `k` iterations of a
point of any prescribed ball around `0`. -/
theorem exists_iterate_mem_ball_pi (c : ι → ℝ) (hc : ∀ i, 1 < c i) {δ : ℝ}
    (hδ : 0 < δ) (z : ι → ℝ) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : ι → ℝ) δ,
      (fun w : ι → ℝ => fun i => c i * w i)^[k] y = z := by
  have hc0 : ∀ i, (0 : ℝ) < c i := fun i => lt_trans zero_lt_one (hc i)
  -- one `k` works for all coordinates
  have hsingle : ∀ i, ∀ᶠ k : ℕ in atTop, ‖z i‖ / c i ^ k < δ := by
    intro i
    have hcpow : Tendsto (fun k : ℕ => c i ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (hc i)
    have hzero : Tendsto (fun k : ℕ => ‖z i‖ / c i ^ k) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hcpow
    exact (tendsto_order.1 hzero).2 δ hδ
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i, ‖z i‖ / c i ^ k < δ :=
    Filter.eventually_all.2 hsingle
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hall
  refine ⟨a, fun i => ((c i) ^ a)⁻¹ * z i, ?_, ?_⟩
  · -- every coordinate is small, hence the point is in the ball
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hδ]
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, abs_of_pos (hc0 i)]
    have hlt : |z i| / c i ^ a < δ := by
      simpa [Real.norm_eq_abs] using (ha a le_rfl i)
    rwa [inv_mul_eq_div]
  · rw [iterate_pi_mul]
    funext i
    show (c i) ^ a * (((c i) ^ a)⁻¹ * z i) = z i
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero a (hc0 i).ne'), one_mul]

/-- **A coordinatewise expanding invariant set containing a ball is
everything.** -/
theorem eq_univ_of_invariant_of_pi_mul (c : ι → ℝ) (hc : ∀ i, 1 < c i)
    {B : Set (ι → ℝ)}
    (hinv : ∀ y ∈ B, (fun w : ι → ℝ => fun i => c i * w i) y ∈ B) {δ : ℝ}
    (hδ : 0 < δ) (hball : Metric.ball (0 : ι → ℝ) δ ⊆ B) : B = univ :=
  eq_univ_of_mapsTo_of_iterate_cover (s := fun w : ι → ℝ => fun i => c i * w i)
    (fun _ hy => hinv _ hy) hball fun z =>
    exists_iterate_mem_ball_pi c hc hδ z

end Product

/-! ## 5. Transport: conjugation and passage to the quotient

Stage C obtains the covering property in the *eigenbasis* (stage A) and needs it
on the original space and on the torus.  Two elementary transports are recorded
here: conjugation by a linear isometry (change of basis, no metric distortion),
and passage to the quotient `V ⧸ L` for a map that is induced by a map of `V`
(the quotient norm is non-increasing, so a covered ball remains covered). -/

section Transport

/-- **Conjugation.**  A covering property for `t` transfers to any conjugate `s`
of `t` under a homeomorphism `e` (in stage C, the change of basis to the common
eigenbasis): the covering set is replaced by its preimage, which is again a
neighbourhood of `0`. -/
theorem exists_iterate_mem_preimage_of_conj {V W : Type*} [TopologicalSpace V]
    [TopologicalSpace W] (e : V ≃ₜ W) (s : V → V) (t : W → W)
    (hconj : ∀ x, e (s x) = t (e x)) {U : Set W}
    (hcover : ∀ w : W, ∃ k : ℕ, w ∈ t^[k] '' U) :
    ∀ z : V, ∃ k : ℕ, z ∈ s^[k] '' (e ⁻¹' U) := by
  intro z
  obtain ⟨k, u, hu, htu⟩ := hcover (e z)
  refine ⟨k, e.symm u, ?_, ?_⟩
  · simpa using hu
  have hiter : ∀ n : ℕ, e (s^[n] (e.symm u)) = t^[n] u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hconj]
  · apply e.injective
    rw [hiter, htu]

/-- **Passage to the quotient.**  If a map `F` of `V` covers balls with its
iterates and `s` on `V ⧸ L` is induced by `F`, then `s` covers balls too. -/
theorem exists_iterate_mem_ball_of_quotient {V : Type*} [NormedAddCommGroup V]
    (L : AddSubgroup V) (s : V ⧸ L → V ⧸ L) (F : V → V)
    (hs : ∀ t : V, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (F t))
    {δ : ℝ} (hcover : ∀ z : V, ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : V) δ, F^[k] y = z)
    (z : V ⧸ L) : ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : V ⧸ L) δ, s^[k] y = z := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  obtain ⟨k, y, hy, hFy⟩ := hcover t
  refine ⟨k, QuotientAddGroup.mk' L y, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hy ⊢
    exact lt_of_le_of_lt QuotientAddGroup.norm_mk_le_norm hy
  · have hiter : ∀ n : ℕ, s^[n] (QuotientAddGroup.mk' L y) =
        QuotientAddGroup.mk' L (F^[n] y) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hs]
    rw [hiter, hFy]

end Transport

/-! ## 6. The normalised accumulation ("tangent direction") lemma

Stage C.2 of the plan selects a *minimal nonzero invariant coordinate subspace*
containing directions in which the closed invariant set `E` accumulates at `0`.
The set-theoretic content of "accumulates at `0` with a limiting direction" is
extracted here, in the model space `ι → ℝ` (the project's `Pt = Fin 3 → ℝ` is
this with `ι = Fin 3`):

if `E` meets every ball around `0` away from `0`, then there is a sequence
`x n ∈ E ∖ {0}` with `‖x n‖ → 0` whose normalised directions
`‖x n‖⁻¹ • x n` converge to a point `d` of the unit sphere.

All the mathematics is the compactness of the unit sphere; the hypothesis is
exactly "`0` is a non-isolated point of `E`", and no invariance is used. -/

section Direction

variable {ι : Type*} [Fintype ι]

/-- **Normalised accumulation.**  From points of `E` arbitrarily close to `0`
one extracts a sequence whose normalised directions converge on the unit
sphere. -/
theorem exists_normalized_tendsto {E : Set (ι → ℝ)}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < ‖x‖ ∧ ‖x‖ < ε) :
    ∃ (x : ℕ → ι → ℝ) (d : ι → ℝ), (∀ n, x n ∈ E) ∧ (∀ n, x n ≠ 0) ∧
      Tendsto (fun n => ‖x n‖) atTop (𝓝 0) ∧ ‖d‖ = 1 ∧
      Tendsto (fun n => ‖x n‖⁻¹ • x n) atTop (𝓝 d) := by
  -- a sequence in `E ∖ {0}` tending to `0`
  have hchoice : ∀ n : ℕ, ∃ x ∈ E, 0 < ‖x‖ ∧ ‖x‖ < 1 / (n + 1 : ℝ) := by
    intro n
    refine hacc _ ?_
    positivity
  choose x hxE hxpos hxsmall using hchoice
  -- its normalised directions lie on the unit sphere
  have hnorm : ∀ n, ‖x n‖⁻¹ • x n ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hxpos n), inv_mul_cancel₀ (hxpos n).ne']
  -- compactness of the sphere gives a convergent subsequence
  obtain ⟨d, hd, φ, hφ, htend⟩ :=
    isCompact_sphere (0 : ι → ℝ) 1 |>.tendsto_subseq hnorm
  refine ⟨x ∘ φ, d, fun n => hxE _, fun n => norm_ne_zero_iff.mp (hxpos (φ n)).ne',
    ?_, ?_, ?_⟩
  · -- `‖x (φ n)‖ → 0`
    refine squeeze_zero (fun n => (hxpos (φ n)).le) (fun n => (hxsmall (φ n)).le) ?_
    have h : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact h.comp hφ.tendsto_atTop
  · rw [Metric.mem_sphere, dist_zero_right] at hd
    exact hd
  · exact htend

end Direction

/-! ## 7. The tangent cone at `0` and its invariance

Stage C.2 needs to *move* accumulating directions around by the maps of `Σ`.
The right object is the tangent cone at `0`: the set of nonzero limits of
`s n • x n` for `x n ∈ E` and `s n → ∞`.  Its virtue is that it is invariant
under every linear map preserving `E`, with no projective normalisation in the
statement:

if `d` lies in the tangent cone of `E` at `0` and `T` is a linear map with
`T '' E ⊆ E` and `T d ≠ 0`, then `T d` lies in the tangent cone of `E` at `0`.

Together with §6 (`0` non-isolated ⟹ some `d` with `‖d‖ = 1` in the tangent
cone) this is the "minimal invariant coordinate subspace" input of C.2: the
supports of the elements of the tangent cone form a `Σ`-invariant family of
coordinate sets, so a minimal one can be chosen. -/

section Tangent

variable {ι : Type*} [Fintype ι]

/-- The **tangent cone at `0`** of a set `E`: the nonzero limits of `s n • x n`
with `x n ∈ E` and `s n → ∞`. -/
def InTangentConeAtZero (E : Set (ι → ℝ)) (d : ι → ℝ) : Prop :=
  ∃ (x : ℕ → ι → ℝ) (s : ℕ → ℝ), (∀ n, x n ∈ E) ∧ Tendsto s atTop atTop ∧
    Tendsto (fun n => s n • x n) atTop (𝓝 d) ∧ d ≠ 0

/-- **Invariance of the tangent cone** under a linear map preserving `E`. -/
theorem InTangentConeAtZero.map {E : Set (ι → ℝ)} {T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hTE : ∀ x ∈ E, T x ∈ E) {d : ι → ℝ} (hd : InTangentConeAtZero E d)
    (hTd : T d ≠ 0) : InTangentConeAtZero E (T d) := by
  obtain ⟨x, s, hx, hs, htend, -⟩ := hd
  refine ⟨fun n => T (x n), s, fun n => hTE _ (hx n), hs, ?_, hTd⟩
  have hcT : ContinuousAt T d := (LinearMap.continuous_of_finiteDimensional T).continuousAt
  have h1 : Tendsto (fun n => T (s n • x n)) atTop (𝓝 (T d)) := hcT.tendsto.comp htend
  refine Filter.Tendsto.congr' (Eventually.of_forall fun n => ?_) h1
  simp

/-- **The tangent cone is nonempty at a non-isolated point.**  If `E` meets
every ball around `0` away from `0`, some unit vector lies in the tangent cone
of `E` at `0`. -/
theorem exists_mem_tangentConeAtZero {E : Set (ι → ℝ)}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < ‖x‖ ∧ ‖x‖ < ε) :
    ∃ d : ι → ℝ, InTangentConeAtZero E d ∧ ‖d‖ = 1 := by
  obtain ⟨x, d, hxE, hxne, hxnorm, hd1, hdtend⟩ := exists_normalized_tendsto hacc
  have hxpos : ∀ n, 0 < ‖x n‖ := fun n => norm_pos_iff.mpr (hxne n)
  have hgt : Tendsto (fun n => ‖x n‖) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxnorm, Eventually.of_forall hxpos⟩
  have hsinf : Tendsto (fun n => ‖x n‖⁻¹) atTop atTop :=
    hgt.inv_tendsto_nhdsGT_zero
  refine ⟨d, ⟨x, fun n => ‖x n‖⁻¹, hxE, hsinf, ?_, ?_⟩, hd1⟩
  · simpa [smul_eq_mul] using hdtend
  · have h0 : (0 : ℝ) < ‖d‖ := by rw [hd1]; norm_num
    exact norm_ne_zero_iff.mp h0.ne'

end Tangent

end BerendExpansion

namespace CubicTwoStage

/-- **Coordinatewise covering on `Pt`.** -/
theorem pt_exists_iterate_mem_ball (c : Pt) (hc : ∀ i, 1 < c i) {δ : ℝ} (hδ : 0 < δ)
    (z : Pt) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : Pt) δ,
      (fun w : Pt => fun i => c i * w i)^[k] y = z :=
  BerendExpansion.exists_iterate_mem_ball_pi c hc hδ z

/-- **Normalised accumulation on `Pt`** (`0` non-isolated in `E` gives a
sequence in `E ∖ {0}` with convergent normalised directions on the unit
sphere). -/
theorem pt_exists_normalized_tendsto {E : Set Pt}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < ‖x‖ ∧ ‖x‖ < ε) :
    ∃ (x : ℕ → Pt) (d : Pt), (∀ n, x n ∈ E) ∧ (∀ n, x n ≠ 0) ∧
      Tendsto (fun n => ‖x n‖) atTop (𝓝 0) ∧ ‖d‖ = 1 ∧
      Tendsto (fun n => ‖x n‖⁻¹ • x n) atTop (𝓝 d) :=
  BerendExpansion.exists_normalized_tendsto hacc

/-- **Tangent cone on `Pt`.**  A direction in which the closed invariant set
accumulates at `0` (as a unit vector of the tangent cone) is produced by §6. -/
theorem pt_exists_mem_tangentConeAtZero {E : Set Pt}
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < ‖x‖ ∧ ‖x‖ < ε) :
    ∃ d : Pt, BerendExpansion.InTangentConeAtZero E d ∧ ‖d‖ = 1 :=
  BerendExpansion.exists_mem_tangentConeAtZero hacc

/-- **The covering fact on the torus.**  If `F` is the diagonal expanding map
`w ↦ fun i => c i * w i` and `s` on `Pt ⧸ L` is induced by `F`, then the
iterates of `s` of any ball around `0` cover the torus. -/
theorem torus_exists_iterate_mem_ball (L : AddSubgroup Pt) (F : Pt → Pt)
    (s : Pt ⧸ L → Pt ⧸ L)
    (hs : ∀ t : Pt, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (F t))
    (c : Pt) (hc : ∀ i, 1 < c i) (hF : ∀ w : Pt, F w = fun i => c i * w i)
    {δ : ℝ} (hδ : 0 < δ) (z : Pt ⧸ L) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : Pt ⧸ L) δ, s^[k] y = z := by
  refine BerendExpansion.exists_iterate_mem_ball_of_quotient L s F hs ?_ z
  intro t
  have hFeq : F = fun w : Pt => fun i => c i * w i := funext hF
  rw [hFeq]
  exact pt_exists_iterate_mem_ball c hc hδ t

/-- **Stage C, covering form, on `Pt ⧸ L`.**  A set containing a ball around
`0` and invariant under an expanding diagonal torus endomorphism is the whole
torus.  (Closedness of `Y` is not needed: the invariant set already contains a
ball.) -/
theorem torus_eq_univ_of_diagonal (L : AddSubgroup Pt) (F : Pt → Pt)
    (s : Pt ⧸ L → Pt ⧸ L)
    (hs : ∀ t : Pt, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (F t))
    (c : Pt) (hc : ∀ i, 1 < c i) (hF : ∀ w : Pt, F w = fun i => c i * w i)
    {Y : Set (Pt ⧸ L)} (hinv : ∀ y ∈ Y, s y ∈ Y) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : Pt ⧸ L) δ ⊆ Y) : Y = univ :=
  BerendExpansion.eq_univ_of_mapsTo_of_iterate_cover (s := s)
    (fun _ hy => hinv _ hy) hball
    fun z => torus_exists_iterate_mem_ball L F s hs c hc hF hδ z

/-- **The difference-set form on `Pt ⧸ L`**: if `Y - Y` contains a ball around
`0` then `Y - Y` is the whole torus.  This is the interface at which stage D
consumes stage C. -/
theorem torus_sub_eq_univ_of_diagonal (L : AddSubgroup Pt) (F : Pt → Pt)
    (s : Pt ⧸ L →+ Pt ⧸ L)
    (hs : ∀ t : Pt, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (F t))
    (c : Pt) (hc : ∀ i, 1 < c i) (hF : ∀ w : Pt, F w = fun i => c i * w i)
    {Y : Set (Pt ⧸ L)} (hinv : ∀ y ∈ Y, s y ∈ Y) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : Pt ⧸ L) δ ⊆ Y - Y) : Y - Y = univ := by
  have hinv' : ∀ y ∈ Y - Y, s y ∈ Y - Y := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨s a, hinv a ha, s b, hinv b hb, (map_sub s a b).symm⟩
  exact torus_eq_univ_of_diagonal L F (s : Pt ⧸ L → Pt ⧸ L) hs c hc hF hinv' hδ hball

end CubicTwoStage
