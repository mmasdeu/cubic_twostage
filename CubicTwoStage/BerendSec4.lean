/-
# Berend §4 in Lean: Lemmas 4.1 and 4.2, and the reduction of plan §C

Target file in the project: `CubicTwoStage/BerendSec4.lean` (copy verbatim from
this directory).  **Axiom free**, does not import `CubicTwoStage.Berend`.

## What this file is

`BEREND_PROOF_PLAN.md` §C ("Stage I: zero non-isolated implies full") is
Berend's §4 (D. Berend, *Multi-invariant sets on tori*, Trans. AMS **280**
(1983)).  This file implements the two lemmas the plan names, §C.1–§C.3, and the
assembly that §C.4 consumes.  It is faithful to the primary source:

* **the diagonalized model** (§C.1): `ι → ℝ` with `diag lam x = fun i => lam i * x i`,
  coordinate subspaces `coord S`, and the accumulation predicate
  `Acc E S : 0 ∈ closure ((E ∩ coord S) \ {0})`, plus its `ε`-form `acc_iff`,
  its monotonicity `acc_of_subset` and its negation `not_acc_iff`;
* **`coordinate_invariant`** = **Berend Lemma 4.1**: if the multipliers are
  pairwise distinct then *every* `diag lam`-invariant subspace is a coordinate
  subspace.  (Proof as in the paper's hint, but with Lagrange interpolation
  implemented through `Polynomial.aeval`: `q_i(lam k) = 0` for `k ≠ i`, so
  `aeval (diag lam) q_i` projects onto the `i`-th coordinate, hence carries `W`
  into `W`.)
* **`exists_minimal_acc`**: among the coordinate subspaces in which `E`
  accumulates at `0` there is a minimal one (§C.2);
* **`acc_of_expanding`** = the paper's proof of **Lemma 4.2**, verbatim: take
  nonzero points of `E ∩ coord S` tending to `0`, multiply each by the *least*
  iterate of `diag lam` that lands it in the annulus `a ≤ ‖·‖ ≤ N a`, use
  compactness of the annulus to extract a nonzero limit point of `E` whose
  coordinates off `T` have died, and repeat with `a → 0`;
* **`dichotomy`** = **Berend Lemma 4.2**: on a minimal accumulating coordinate
  set, `diag lam` is uniformly expanding or uniformly nonexpanding;
* **`exists_expanding`**: Berend's (B2) upgrades the dichotomy — if every
  coordinate direction of the minimal set carries a family element with
  `|λ| > 1`, then **one** family element is uniformly expanding on all of it;
* **`exists_minimal_and_expanding`**: §C.2 + §C.3 + (B2) assembled, which is the
  exact configuration plan §C.4 starts from.

## What this file is *not*

Plan **§C.4** (the cone/compactness argument that upgrades the accumulating
sequence to a point of `E` inside a nonempty open set of the selected coordinate
subspace) and **§C.5** (the rank-two step) are **not** implemented, and nothing
here is conditional on them: no proposition is assumed, no axiom declared, no
`sorry`.

They are not bookkeeping gaps.  `Acc` alone does not force interior: on `ℝ/ℤ`
with `x ↦ 2x` the base-2 Cantor set is closed, infinite, proper, invariant and
has `0` as a non-isolated point, so §C.5 cannot be dispensed with, and in
dimension one §C.5 *is* Furstenberg's `×2 ×3` theorem.  What is proved here is
therefore the honest frontier of §4: the paper's Lemma 4.1 and Lemma 4.2 with
their full proofs, and the reduction of §C to a single uniformly expanding
generator on a minimal coordinate subspace with the accumulation hypothesis
intact.
-/
import CubicTwoStage.Lattice

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendSec4

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The diagonalized model -/

/-- The diagonal endomorphism with multiplier vector `lam`. -/
def diag (lam : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x := fun i => lam i * x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, mul_add]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem diag_apply (lam : ι → ℝ) (x : ι → ℝ) (i : ι) :
    diag lam x i = lam i * x i := rfl

/-- `diag lam` is continuous. -/
theorem continuous_diag (lam : ι → ℝ) : Continuous (diag lam) :=
  (diag lam).continuous_of_finiteDimensional

/-- Iterates of the diagonal map act coordinatewise. -/
theorem diag_iterate_apply (lam : ι → ℝ) (n : ℕ) (x : ι → ℝ) (i : ι) :
    ((diag lam)^[n] x) i = (lam i) ^ n * x i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', diag_apply, ih, pow_succ]
      ring

/-- The coordinate subspace of a set `S` of coordinates. -/
def coord (S : Set ι) : Submodule ℝ (ι → ℝ) where
  carrier := {x | ∀ i, i ∉ S → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro c x hx i hi
    simp only [Pi.smul_apply, smul_eq_mul, hx i hi, mul_zero]

theorem mem_coord {S : Set ι} {x : ι → ℝ} : x ∈ coord S ↔ ∀ i, i ∉ S → x i = 0 :=
  Iff.rfl

theorem diag_mem_coord (lam : ι → ℝ) {S : Set ι} {x : ι → ℝ} (hx : x ∈ coord S) :
    diag lam x ∈ coord S := by
  intro i hi
  simp only [diag_apply, hx i hi, mul_zero]

/-- Below the diagonal map, an element of a coordinate subspace that has no
coordinate in `T` lies in the smaller coordinate subspace. -/
theorem mem_coord_sdiff {S T : Finset ι} {x : ι → ℝ} (hS : x ∈ coord (S : Set ι))
    (hT : ∀ i ∈ T, x i = 0) : x ∈ coord ((S \ T : Finset ι) : Set ι) := by
  intro i hi
  rw [Finset.mem_coe, Finset.mem_sdiff, not_and] at hi
  by_cases hSi : i ∈ S
  · exact hT i (by simpa using hi hSi)
  · exact hS i hSi

/-! ## 2. Accumulation at `0` in a coordinate subspace -/

/-- `E` accumulates at `0` inside the coordinate subspace of `S`.  This is
Berend's "`É` contains a sequence of nonzero points converging to `0`" restricted
to `V_S`.  Plan §C.2. -/
def Acc (E : Set (ι → ℝ)) (S : Finset ι) : Prop :=
  (0 : ι → ℝ) ∈ closure ((E ∩ (coord (S : Set ι) : Set (ι → ℝ))) \ {0})

/-- The `ε`-form of `Acc`. -/
theorem acc_iff {E : Set (ι → ℝ)} {S : Finset ι} :
    Acc E S ↔ ∀ ε > 0, ∃ u : ι → ℝ, u ∈ E ∧ u ∈ coord (S : Set ι) ∧ u ≠ 0 ∧
      ‖u‖ < ε := by
  rw [Acc, mem_closure_iff_nhds]
  constructor
  · intro h ε hε
    obtain ⟨u, hu_t, hu_s⟩ := h (Metric.ball (0 : ι → ℝ) ε) (Metric.ball_mem_nhds 0 hε)
    obtain ⟨⟨huE, huS⟩, hune⟩ := hu_s
    exact ⟨u, huE, huS, hune, by simpa [Metric.mem_ball, dist_zero_right] using hu_t⟩
  · intro h t ht
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
    obtain ⟨u, huE, huS, hune, hult⟩ := h ε hε
    exact ⟨u, hball (by simpa [Metric.mem_ball, dist_zero_right] using hult),
      ⟨⟨huE, huS⟩, hune⟩⟩

/-- `Acc` is antitone in the coordinate set. -/
theorem acc_of_subset {E : Set (ι → ℝ)} {S T : Finset ι} (h : Acc E T) (hTS : T ⊆ S) :
    Acc E S := by
  rw [acc_iff] at h ⊢
  intro ε hε
  obtain ⟨u, huE, huT, hune, hult⟩ := h ε hε
  refine ⟨u, huE, ?_, hune, hult⟩
  intro i hi
  exact huT i (fun hT => hi (hTS hT))

/-- **The negation of `Acc`, in the form the annulus argument uses**: the nonzero
points of `E` inside `coord S` are bounded away from `0`. -/
theorem not_acc_iff {E : Set (ι → ℝ)} {S : Finset ι} :
    ¬ Acc E S ↔ ∃ d, 0 < d ∧ ∀ v, v ∈ E → v ∈ coord (S : Set ι) → v ≠ 0 → d ≤ ‖v‖ := by
  rw [acc_iff]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h hc
  · rintro ⟨d, hd, hd'⟩ h
    obtain ⟨v, hvE, hvS, hvne, hvlt⟩ := h d hd
    exact absurd (hd' v hvE hvS hvne) (not_le.2 hvlt)

/-! ## 3. Norm bounds for the diagonal map -/

/-- A common Lipschitz bound `N ≥ 1` for `diag lam`. -/
theorem exists_norm_bound (lam : ι → ℝ) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ v : ι → ℝ, ‖diag lam v‖ ≤ N * ‖v‖ := by
  refine ⟨max 1 (∑ i, |lam i|), le_max_left _ _, fun v => ?_⟩
  have hNabs : ∀ i, |lam i| ≤ max 1 (∑ i, |lam i|) := fun i =>
    le_trans (Finset.single_le_sum (f := fun i => |lam i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)) (le_max_right _ _)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [diag_apply, Real.norm_eq_abs, abs_mul]
  have h2 : |v i| ≤ ‖v‖ := by
    have h := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at h
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have h4 : 0 ≤ |v i| := abs_nonneg _
  have hN0 : 0 ≤ max 1 (∑ i, |lam i|) := le_trans zero_le_one (le_max_left _ _)
  nlinarith [hNabs i, h2, hv, h4, hN0]


/-! ## 4. Berend Lemma 4.2: the annulus argument -/

/-- **Berend Lemma 4.2** (Trans. AMS 280 (1983), §4), in the form of the paper's
contradiction engine.

`E ⊆ ι → ℝ` is closed and invariant under the diagonal map `diag lam`; `T ⊆ S` is
a set of coordinates on which `1 < |lam i|`, while `|lam i| ≤ 1` on `S \ T`; `T`
is nonempty; and `E` does **not** accumulate at `0` inside the smaller coordinate
subspace `coord (S \ T)`.  Then `E` accumulates at `0` inside `coord T`.

This is the paper's argument: take a sequence of nonzero points of `E ∩ coord S`
tending to `0`, multiply each by the least iterate of `diag lam` that puts it in
the annulus `a ≤ ‖·‖ ≤ N a`; by compactness of the annulus a subsequence converges
to a nonzero point of `E`, whose coordinates off `T` have died, and repeating with
`a → 0` exhibits accumulation inside `coord T`. -/
theorem acc_of_expanding
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {S T : Finset ι} (_hTS : T ⊆ S)
    (hexp : ∀ i ∈ T, 1 < |lam i|)
    (hcon : ∀ i ∈ S, i ∉ T → |lam i| ≤ 1)
    (_hTne : T.Nonempty)
    (haccS : Acc E S) (hnoAcc : ¬ Acc E (S \ T)) :
    Acc E T := by
  classical
  obtain ⟨d, hd, hd'⟩ := not_acc_iff.1 hnoAcc
  obtain ⟨N, hN1, hN⟩ := exists_norm_bound (ι := ι) lam
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hiter : ∀ (k : ℕ) {x : ι → ℝ}, x ∈ E → ((diag lam)^[k]) x ∈ E := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [Function.iterate_succ_apply]; exact ih (hinv x hx)
  rw [acc_iff]
  intro ε hε
  set a : ℝ := min d (ε / (2 * N)) with ha
  have ha_pos : 0 < a := lt_min hd (by positivity)
  have ha_d : a ≤ d := min_le_left _ _
  have ha_eps : N * a ≤ ε / 2 := by
    have h1 : N * a ≤ N * (ε / (2 * N)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hNpos)
    have h2 : N * (ε / (2 * N)) = ε / 2 := by field_simp
    rw [h2] at h1; exact h1
  -- the sequence of small points of `E` inside `coord S`
  have hseq : ∀ m : ℕ, ∃ u : ι → ℝ, u ∈ E ∧ u ∈ coord (S : Set ι) ∧ u ≠ 0 ∧
      ‖u‖ < min a (a / (m + 1)) := fun m =>
    acc_iff.1 haccS _ (lt_min ha_pos (by positivity))
  choose u huE huS hune hult using hseq
  have hult_a : ∀ m, ‖u m‖ < a := fun m => lt_of_lt_of_le (hult m) (min_le_left _ _)
  have hult_d : ∀ m, ‖u m‖ < d := fun m => lt_of_lt_of_le (hult_a m) ha_d
  have hTcoord : ∀ m, ∃ i ∈ T, u m i ≠ 0 := by
    intro m
    by_contra hc
    push_neg at hc
    exact absurd (hd' (u m) (huE m) (mem_coord_sdiff (huS m) hc) (hune m))
      (not_le.2 (hult_d m))
  -- the hitting time of the annulus
  have hex : ∀ m, ∃ y : ℕ, a ≤ ‖((diag lam)^[y]) (u m)‖ := by
    intro m
    obtain ⟨i₀, hi₀T, hi₀ne⟩ := hTcoord m
    have hgt : 1 < |lam i₀| := hexp i₀ hi₀T
    have htend : Tendsto (fun y : ℕ => |lam i₀| ^ y * |u m i₀|) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const (abs_pos.2 hi₀ne)
    obtain ⟨y, hy⟩ := (tendsto_atTop_atTop.1 htend) a
    have hy' : a ≤ |lam i₀| ^ y * |u m i₀| := hy y le_rfl
    have hcoord : |lam i₀| ^ y * |u m i₀| = ‖(((diag lam)^[y]) (u m)) i₀‖ := by
      rw [diag_iterate_apply, Real.norm_eq_abs, abs_mul, abs_pow]
    rw [hcoord] at hy'
    exact ⟨y, le_trans hy' (norm_le_pi_norm _ _)⟩
  set Y : ℕ → ℕ := fun m => Nat.find (hex m) with hY
  have hYspec : ∀ m, a ≤ ‖((diag lam)^[Y m]) (u m)‖ := fun m => Nat.find_spec (hex m)
  have hYpos : ∀ m, 1 ≤ Y m := by
    intro m
    rcases Nat.eq_zero_or_pos (Y m) with h | h
    · exfalso
      have hspec := hYspec m
      rw [h] at hspec
      simp only [Function.iterate_zero, id] at hspec
      exact absurd hspec (not_le.2 (hult_a m))
    · exact h
  have hYmin : ∀ m, ‖((diag lam)^[Y m - 1]) (u m)‖ < a := by
    intro m
    have hm1 : 1 ≤ Y m := hYpos m
    have hlt : Y m - 1 < Y m := Nat.sub_one_lt_of_lt hm1
    exact not_le.1 (Nat.find_min (hex m) hlt)
  set w : ℕ → (ι → ℝ) := fun m => ((diag lam)^[Y m]) (u m) with hw
  have hwdef : ∀ m, w m = ((diag lam)^[Y m]) (u m) := fun m => rfl
  have hwE : ∀ m, w m ∈ E := fun m => hiter (Y m) (huE m)
  have hw_ge : ∀ m, a ≤ ‖w m‖ := fun m => hYspec m
  have hw_le : ∀ m, ‖w m‖ ≤ N * a := by
    intro m
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 (hYpos m))
    have hwk : w m = diag lam (((diag lam)^[k]) (u m)) := by
      rw [hwdef, hk, Function.iterate_succ']
      rfl
    have hkmin : ‖((diag lam)^[k]) (u m)‖ < a := by
      have hkey : Y m - 1 = k := by omega
      have := hYmin m
      rwa [hkey] at this
    rw [hwk]
    exact (hN _).trans (le_of_lt (mul_lt_mul_of_pos_left hkmin hNpos))
  -- compactness of the annulus
  have hann : IsCompact {v : ι → ℝ | a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a} := by
    have hclosed : IsClosed {v : ι → ℝ | a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a} := by
      have h1 : IsClosed {v : ι → ℝ | a ≤ ‖v‖} := isClosed_le continuous_const continuous_norm
      have h2 : IsClosed {v : ι → ℝ | ‖v‖ ≤ N * a} := isClosed_le continuous_norm continuous_const
      simpa only [Set.ofPred_and] using h1.inter h2
    have hbdd : Bornology.IsBounded {v : ι → ℝ | a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a} :=
      Metric.isBounded_closedBall.subset (fun v hv => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hv.2)
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbdd⟩
  obtain ⟨z, hz_ann, φ, hφmono, hφtend⟩ :=
    hann.tendsto_subseq (x := w) (fun m => ⟨hw_ge m, hw_le m⟩)
  have hzE : z ∈ E :=
    hE.mem_of_tendsto hφtend (Filter.Eventually.of_forall fun m => hwE (φ m))
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le ha_pos hz_ann.1
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hz_pos; simp at hz_pos
  have hz_small : ‖z‖ < ε := lt_of_le_of_lt (le_trans hz_ann.2 ha_eps) (by linarith)
  have hzT : z ∈ coord (T : Set ι) := by
    intro i hiT
    have hzero : Tendsto (fun m => w m i) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun m : ℕ => a / ((m : ℝ) + 1)) (fun m => ?_) ?_
      · rw [hwdef, diag_iterate_apply, Real.norm_eq_abs, abs_mul, abs_pow]
        by_cases hiS : i ∈ S
        · have hle : |lam i| ≤ 1 := hcon i hiS hiT
          have h1 : |lam i| ^ Y m * |u m i| ≤ 1 * |u m i| := by
            have h0 : (0 : ℝ) ≤ |lam i| ^ Y m := by positivity
            have h1' : |lam i| ^ Y m ≤ 1 := pow_le_one₀ (abs_nonneg _) hle
            exact mul_le_mul_of_nonneg_right h1' (abs_nonneg _)
          have h2 : |u m i| ≤ ‖u m‖ := by
            have := norm_le_pi_norm (u m) i
            rwa [Real.norm_eq_abs] at this
          have h3 : ‖u m‖ < a / (m + 1) := lt_of_lt_of_le (hult m) (min_le_right _ _)
          linarith
        · have h0 : u m i = 0 := huS m i hiS
          simp only [h0, mul_zero, abs_zero]
          positivity
      · have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Tendsto (fun m : ℕ => a * (1 / ((m : ℝ) + 1))) atTop (𝓝 (a * 0)) :=
          h1.const_mul a
        rw [mul_zero] at h2
        refine h2.congr fun m => ?_
        rw [mul_one_div]
    have hsub : Tendsto (fun m => w (φ m) i) atTop (𝓝 (z i)) :=
      (tendsto_pi_nhds.1 hφtend) i
    have hsub0 : Tendsto (fun m => w (φ m) i) atTop (𝓝 0) :=
      hzero.comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique hsub hsub0
  exact ⟨z, hzE, hzT, hzne, hz_small⟩


/-! ## 5. Berend Lemmas 4.1/4.2, assembled: minimal coordinate set and dichotomy -/

/-- **Berend Lemma 4.1, minimality part** (plan §C.2): among the coordinate
subspaces in which `E` accumulates at `0` there is one that is minimal for
inclusion.  (In the paper, Lemma 4.1 additionally identifies *all* Σ-invariant
subspaces as coordinate subspaces; see `coordinate_invariant` below.) -/
theorem exists_minimal_acc {E : Set (ι → ℝ)} (h : Acc E (Finset.univ)) :
    ∃ S : Finset ι, Acc E S ∧ ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S' := by
  classical
  set P : Finset (Finset ι) := Finset.univ.filter (fun S => Acc E S) with hP
  have hPne : P.Nonempty := ⟨Finset.univ, by rw [hP]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  obtain ⟨S, hSP, hSmin⟩ := Finset.exists_min_image P (fun S => S.card) hPne
  have hSacc : Acc E S := (Finset.mem_filter.1 (hP ▸ hSP)).2
  refine ⟨S, hSacc, fun S' hS' => ?_⟩
  intro hacc'
  have hS'P : S' ∈ P := by
    rw [hP]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hacc'⟩
  have hcard : S'.card < S.card := Finset.card_lt_card hS'
  have := hSmin S' hS'P
  omega

/-- **Berend Lemma 4.2** (plan §C.3): on a minimal accumulating coordinate set,
`diag lam` is uniformly expanding or uniformly nonexpanding. -/
theorem dichotomy
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {S : Finset ι} (hacc : Acc E S)
    (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') :
    (∀ i ∈ S, 1 < |lam i|) ∨ (∀ i ∈ S, |lam i| ≤ 1) := by
  classical
  set T : Finset ι := S.filter (fun i => 1 < |lam i|) with hT
  have hTS : T ⊆ S := by rw [hT]; exact Finset.filter_subset _ _
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine Or.inr fun i hi => ?_
    by_contra hle
    have hmem : i ∈ T := by
      rw [hT]; exact Finset.mem_filter.2 ⟨hi, not_le.1 hle⟩
    rw [hTe] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  · rcases eq_or_lt_of_le hTS with hEq | hlt
    · refine Or.inl fun i hi => ?_
      have hi' : i ∈ T := hEq.symm ▸ hi
      rw [hT] at hi'
      exact (Finset.mem_filter.1 hi').2
    · exfalso
      have hexp : ∀ i ∈ T, 1 < |lam i| := by
        intro i hi
        rw [hT] at hi
        exact (Finset.mem_filter.1 hi).2
      have hcon : ∀ i ∈ S, i ∉ T → |lam i| ≤ 1 := by
        intro i hiS hiT
        by_contra hle
        exact hiT (by rw [hT]; exact Finset.mem_filter.2 ⟨hiS, not_le.1 hle⟩)
      have hnoAcc : ¬ Acc E (S \ T) := by
        refine hmin (S \ T) ?_
        refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩
        intro hcontra
        obtain ⟨i, hiT⟩ := hTne
        have hiS : i ∈ S := hTS hiT
        have hmem : i ∈ S \ T := by rw [hcontra]; exact hiS
        exact (Finset.mem_sdiff.1 hmem).2 hiT
      exact hmin T hlt (acc_of_expanding hE hinv hTS hexp hcon hTne hacc hnoAcc)

/-- **Berend's (B2) ⇒ a uniformly expanding element** (plan §C.4–§C.5 input): if
every coordinate direction of the minimal accumulating set `S` carries an element
of the semigroup with eigenvalue of modulus `> 1` there, then one single element
is uniformly expanding on all of `S`. -/
theorem exists_expanding
    {E : Set (ι → ℝ)} {lam : ι → ℝ} (hE : IsClosed E)
    (hinv : ∀ x ∈ E, diag lam x ∈ E)
    {S : Finset ι} (hacc : Acc E S)
    (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    (hB2 : ∀ i ∈ S, ∃ mu : ι → ℝ, (∀ x ∈ E, diag mu x ∈ E) ∧ 1 < |mu i|) :
    ∃ mu : ι → ℝ, (∀ x ∈ E, diag mu x ∈ E) ∧ ∀ i ∈ S, 1 < |mu i| := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨lam, hinv, fun i hi => ?_⟩
    rw [hS] at hi
    exact absurd hi (Finset.notMem_empty i)
  · obtain ⟨i₀, hi₀⟩ := hS
    obtain ⟨mu, hmuinv, hmu⟩ := hB2 i₀ hi₀
    rcases dichotomy hE hmuinv hacc hmin with h | h
    · exact ⟨mu, hmuinv, h⟩
    · exact absurd (h i₀ hi₀) (not_le.2 hmu)


/-! ## 6. Berend Lemma 4.1: invariant subspaces are coordinate subspaces -/

/-- Powers of the diagonal map act coordinatewise. -/
theorem diag_pow_apply (lam : ι → ℝ) (n : ℕ) (x : ι → ℝ) (k : ι) :
    ((diag lam) ^ n) x k = (lam k) ^ n * x k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, diag_apply, ih, pow_succ']
      ring

/-- The Lagrange interpolation polynomial of the `i`-th coordinate: for pairwise
distinct multipliers, `q_i(lam k)` is `0` for `k ≠ i` and nonzero at `i`. -/
noncomputable def lagrangePoly (lam : ι → ℝ) (i : ι) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (X - C (lam j))

theorem eval_lagrangePoly (lam : ι → ℝ) (i k : ι) :
    (lagrangePoly lam i).eval (lam k) = ∏ j ∈ Finset.univ.erase i, (lam k - lam j) := by
  rw [lagrangePoly, Polynomial.eval_prod]
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `aeval (diag lam) p` acts coordinatewise by `p.eval (lam k)`. -/
theorem aeval_diag_apply (lam : ι → ℝ) (p : Polynomial ℝ) (x : ι → ℝ) (k : ι) :
    (aeval (diag lam) p) x k = p.eval (lam k) * x k := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply, Pi.smul_apply, smul_eq_mul, Polynomial.eval_C]
  | add p q hp hq =>
      rw [map_add, LinearMap.add_apply, Pi.add_apply, Polynomial.eval_add, hp, hq, add_mul]
  | monomial n a =>
      have h1 : aeval (diag lam) (Polynomial.C a * Polynomial.X ^ (n + 1))
          = a • ((diag lam) ^ (n + 1)) := by
        rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [h1, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, diag_pow_apply,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      ring

/-- **Berend Lemma 4.1**: if the multipliers of the diagonal map are pairwise
distinct, every `diag lam`-invariant subspace is a coordinate subspace.  This is
the paper's "a subspace `V` of `ℂ^r` is Σ-invariant iff it is spanned by some
subset of the standard basis", for the diagonalized semigroup; it is what lets
plan §C.1–§C.2 restrict the accumulation hypothesis to coordinate subspaces. -/
theorem coordinate_invariant {lam : ι → ℝ} (hlam : ∀ i j, lam i = lam j → i = j)
    (W : Submodule ℝ (ι → ℝ)) (hW : ∀ x ∈ W, diag lam x ∈ W) :
    ∃ S : Set ι, W = coord S := by
  classical
  refine ⟨{i | (fun k => if k = i then (1 : ℝ) else 0) ∈ W}, ?_⟩
  have hpowmem : ∀ (m : ℕ) {x : ι → ℝ}, x ∈ W → ((diag lam) ^ m) x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih => intro x hx; rw [pow_succ']; exact hW _ (ih hx)
  have hmono : ∀ (n : ℕ) (a : ℝ), ∀ x ∈ W,
      (aeval (diag lam) (Polynomial.C a * Polynomial.X ^ (n + 1))) x ∈ W := by
    intro n a x hx
    have h1 : aeval (diag lam) (Polynomial.C a * Polynomial.X ^ (n + 1))
        = a • ((diag lam) ^ (n + 1)) := by
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h1, LinearMap.smul_apply]
    exact W.smul_mem a (hpowmem (n + 1) hx)
  have hpoly : ∀ p : Polynomial ℝ, ∀ x ∈ W, (aeval (diag lam) p) x ∈ W := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        intro x hx
        rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
          Module.End.one_apply]
        exact W.smul_mem a hx
    | add p q hp hq =>
        intro x hx
        rw [map_add, LinearMap.add_apply]
        exact W.add_mem (hp x hx) (hq x hx)
    | monomial n a => exact hmono n a
  ext x
  constructor
  · intro hx
    rw [mem_coord]
    intro i hi
    set c : ℝ := ∏ j ∈ Finset.univ.erase i, (lam i - lam j) with hcdef
    have hc : c ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      exact sub_ne_zero.2 fun h => hji (hlam i j h).symm
    have hmemW : (aeval (diag lam) (lagrangePoly lam i)) x ∈ W := hpoly _ x hx
    have hval : (aeval (diag lam) (lagrangePoly lam i)) x
        = fun k => if k = i then c * x i else 0 := by
      funext k
      rw [aeval_diag_apply, eval_lagrangePoly]
      by_cases hk : k = i
      · subst hk; simp [hcdef]
      · have hmem : k ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩
        rw [Finset.prod_eq_zero hmem (by ring), if_neg hk, zero_mul]
    rw [hval] at hmemW
    by_contra hne
    have hcxi : c * x i ≠ 0 := mul_ne_zero hc hne
    have heq : (fun k => if k = i then c * x i else 0)
        = (c * x i) • (fun k => if k = i then (1 : ℝ) else 0) := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [heq] at hmemW
    have hsm := W.smul_mem (c * x i)⁻¹ hmemW
    rw [smul_smul, inv_mul_cancel₀ hcxi, one_smul] at hsm
    exact hi hsm
  · intro hx
    rw [mem_coord] at hx
    have hsum : x = ∑ i : ι, x i • (fun k => if k = i then (1 : ℝ) else 0) := by
      funext k
      simp
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (fun k => if k = i then (1 : ℝ) else 0) ∈ W
    · exact W.smul_mem (x i) hi
    · have hxi : x i = 0 := hx i hi
      rw [hxi, zero_smul]
      exact W.zero_mem


/-- **Plan §C.2–§C.3 assembled, with the (B2) input.**  If `E` is closed and
invariant under a family of diagonal endomorphisms and accumulates at `0`, then
there is a nonempty *minimal* coordinate set `S` in which `E` accumulates, and a
**single** element of the family that is uniformly expanding on all of `S`
(Berend's (B2) turns the `∨` of `dichotomy` into its expanding branch).

This is exactly the configuration that plan §C.4–§C.5 start from. -/
theorem exists_minimal_and_expanding
    {E : Set (ι → ℝ)} (hE : IsClosed E) (hacc : Acc E Finset.univ)
    {κ : Type*} {fam : κ → ι → ℝ} (hinv : ∀ k, ∀ x ∈ E, diag (fam k) x ∈ E)
    (hB2 : ∀ i : ι, ∃ k : κ, 1 < |fam k i|) :
    ∃ S : Finset ι, S.Nonempty ∧ Acc E S ∧
      (∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') ∧
      ∃ k : κ, ∀ i ∈ S, 1 < |fam k i| := by
  classical
  obtain ⟨S, hSacc, hSmin⟩ := exists_minimal_acc hacc
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨v, -, hv, hvne, -⟩ := acc_iff.1 (h ▸ hSacc) 1 one_pos
      refine hvne (funext fun i => ?_)
      exact hv i (by simp)
    · exact h
  refine ⟨S, hne, hSacc, hSmin, ?_⟩
  -- take the (B2) witness for one coordinate of `S`; by `dichotomy` it is
  -- uniformly expanding on all of `S`
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨k, hk⟩ := hB2 i₀
  rcases dichotomy hE (hinv k) hSacc hSmin with hexp | hcon
  · exact ⟨k, hexp⟩
  · exact absurd (hcon i₀ hi₀) (not_le.2 hk)

end BerendSec4

end CubicTwoStage
