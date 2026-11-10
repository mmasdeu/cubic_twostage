/-
# The cone layer of Berend §4 (plan §C.4), in the diagonalized model

This module implements the part of `BEREND_PROOF_PLAN.md` §C.4 that comes
*before* the rank-two step §C.5, in the diagonalized model of
`CubicTwoStage/BerendSec4.lean`.  Axiom free: it imports only
`CubicTwoStage.BerendSec4` and does not mention `berend_multi_invariance`.

## What is here

* **`exists_iterate_norm_ge`** — the expansion fact: if `1 < |lam i|` on the
  coordinate set `S` and `0 ≠ x ∈ coord S`, the iterates of `diag lam` push `x`
  out of every annulus.
* **`exists_annulus_point`** (plan §C.4, "compactness of coefficient annuli") —
  the reusable form of the annulus step buried inside `acc_of_expanding`: a
  closed `diag lam`-invariant `E` that accumulates at `0` inside `coord S` meets
  the annulus `a ≤ ‖·‖ ≤ N a` at a nonzero point of `coord S`, for any Lipschitz
  bound `N ≥ 1` of `diag lam`.
* **`exists_cone_accumulation`** — the "full cone" strengthening of `Acc`: `E`
  accumulates at `0` inside one *fixed* closed cone
  `dominantCone S i = {|x j| ≤ |x i| for j ∈ S}` of the minimal coordinate set.
* **`dirSet`**, `dirSet_nonempty`, `dirSet_mapsTo` — the projective
  ("tangent direction") object: the accumulation directions of `E` at `0` inside
  `coord S`, a subset of the unit sphere of `coord S`, carried into itself by the
  projectivized dilation `ξ ↦ ‖diag mu ξ‖⁻¹ • diag mu ξ`; `acc_iff_dirSet_nonempty`
  shows `Acc` is *exactly* nonemptiness of `dirSet`, so the direction set keeps
  all the information `Acc` has.
* **§5, quotient form of the covering step** (plan §C.6): for `s` on
  `(ι → ℝ) ⧸ L` induced by a coordinatewise dilation `x ↦ (c i * x i)` with
  `1 < c i`, the iterates of any ball around `0` cover the quotient
  (`exists_iterate_mem_ball_pi_quotient`), so an invariant set containing a ball
  around `0` is everything (`eq_univ_of_invariant_of_pi_mul_quotient`).  This is
  the diagonal-quotient case missing from `BerendCovering` (which has the scalar
  quotient case and the diagonal linear case).
* **§7, "expansion and translation"** (plan §C.4's last sentence): for `s` on
  `(ι → ℝ) ⧸ L` induced by a coordinatewise dilation with multipliers `≥ m > 1`,
  any `s`-invariant set containing *any* open ball — equivalently with nonempty
  interior (`eq_univ_of_interior_nonempty`) — is the whole torus.  This weakens
  the C.4 target from "a ball around `0`" to "some nonempty open subset".
* **§6, the two bridges to the torus** (plan §C.6): the entry point
  `acc_preimage_of_zero_nonisolated` (a non-isolated `0` in `Y ⊆ (ι → ℝ) ⧸ L`
  gives `BerendSec4.Acc (mk' L ⁻¹' Y) univ`, the hypothesis of stage C), and the
  last mile `eq_univ_of_ball_subset_preimage` (a linear-model ball inside the
  preimage of an invariant `Y` forces `Y = univ`).

## What is *not* here

Nothing here produces an *open* subset of `E`, and the cone/annulus data alone
cannot: for the base-`2` Cantor set `C ⊆ ℝ/ℤ` the closed `×2`-invariant set
`E = C` has `dirSet E univ = {±1}`, i.e. the largest possible direction set,
and empty interior.  So "cone data ⟹ interior" is exactly the rank-two rigidity
of plan §C.5 (Furstenberg's `×2 ×3` theorem in dimension one).
-/
import CubicTwoStage.BerendSec4
import CubicTwoStage.BerendCovering

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendCone

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Expansion of the norm under `diag lam` -/

/-- **The norm of an iterate is unbounded.**  If `1 < |lam i|` on the coordinate
set `S` and `0 ≠ x ∈ coord S`, then for every `a` some iterate of `x` under
`diag lam` has norm at least `a`.  (The coordinate attaining `‖x‖` lies in `S`,
and its multiplier exceeds `1`.) -/
theorem exists_iterate_norm_ge {lam : ι → ℝ} {S : Finset ι}
    (hexp : ∀ i ∈ S, 1 < |lam i|) {x : ι → ℝ} (hx : x ∈ BerendSec4.coord (S : Set ι))
    (hxne : x ≠ 0) (a : ℝ) :
    ∃ n : ℕ, a ≤ ‖((BerendSec4.diag lam)^[n]) x‖ := by
  classical
  have hne : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hxne (funext h)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i => |x i|) ⟨hne.choose, Finset.mem_univ _⟩
  have hnx : ‖x‖ = |x i₀| := by
    refine le_antisymm ?_ ?_
    · refine pi_norm_le_iff_of_nonneg (abs_nonneg _) |>.2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact hi₀ i (Finset.mem_univ i)
    · have h := norm_le_pi_norm x i₀
      rwa [Real.norm_eq_abs] at h
  have hi₀ne : x i₀ ≠ 0 := by
    intro h
    have h0 : ‖x‖ = 0 := by simp [hnx, h]
    exact hxne (norm_eq_zero.1 h0)
  have hi₀S : i₀ ∈ S := by
    by_contra h
    exact hi₀ne (BerendSec4.mem_coord.1 hx i₀ h)
  have hgt : 1 < |lam i₀| := hexp i₀ hi₀S
  have htend : Tendsto (fun n : ℕ => |lam i₀| ^ n * |x i₀|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const (abs_pos.2 hi₀ne)
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.1 htend) a
  have hn' : a ≤ |lam i₀| ^ n * |x i₀| := hn n le_rfl
  have hcoord : |lam i₀| ^ n * |x i₀| = ‖(((BerendSec4.diag lam)^[n]) x) i₀‖ := by
    rw [BerendSec4.diag_iterate_apply, Real.norm_eq_abs, abs_mul, abs_pow]
  rw [hcoord] at hn'
  exact ⟨n, le_trans hn' (norm_le_pi_norm _ _)⟩


/-! ## 2. The annulus step of plan §C.4 -/

section Annulus

variable {E : Set (ι → ℝ)} {lam : ι → ℝ}

/-- Iterates of `diag lam` stay in an invariant set. -/
theorem iterate_mem (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) (k : ℕ) {x : ι → ℝ}
    (hx : x ∈ E) : ((BerendSec4.diag lam)^[k]) x ∈ E := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih

/-- Iterates of `diag lam` stay in the coordinate subspace. -/
theorem iterate_mem_coord {S : Finset ι} (k : ℕ) {x : ι → ℝ}
    (hx : x ∈ BerendSec4.coord (S : Set ι)) :
    ((BerendSec4.diag lam)^[k]) x ∈ BerendSec4.coord (S : Set ι) := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact BerendSec4.diag_mem_coord lam ih

/-- **Plan §C.4, "compactness of coefficient annuli", first form.**  Let `E` be
closed and invariant under `diag lam`, let `1 < |lam i|` on the coordinate set
`S`, and suppose `0` is a non-isolated point of `E ∩ coord S`.  Then for every
`a > 0` the set `E` contains a nonzero point of `coord S` in the annulus
`a ≤ ‖·‖ ≤ N a`, where `N ≥ 1` is any Lipschitz bound for `diag lam`.
(Closedness of `E` is *not* needed: the point is an iterate of a point of `E`.)

Proof: take `u ∈ E ∩ coord S` with `0 < ‖u‖ < a` (`acc_iff`), let `Y` be the
*first* iterate of `u` whose norm reaches `a`, and use that the previous iterate
had norm `< a`, so the iterate at time `Y` has norm `≤ N a`. -/
theorem exists_annulus_point
    (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) {S : Finset ι}
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hacc : BerendSec4.Acc E S) {a : ℝ} (ha : 0 < a)
    {N : ℝ} (hN1 : 1 ≤ N) (hN : ∀ v : ι → ℝ, ‖BerendSec4.diag lam v‖ ≤ N * ‖v‖) :
    ∃ y ∈ E, y ∈ BerendSec4.coord (S : Set ι) ∧ y ≠ 0 ∧ a ≤ ‖y‖ ∧ ‖y‖ ≤ N * a := by
  classical
  obtain ⟨u, huE, huS, hune, hult⟩ := BerendSec4.acc_iff.1 hacc a ha
  have hex : ∃ n : ℕ, a ≤ ‖((BerendSec4.diag lam)^[n]) u‖ :=
    exists_iterate_norm_ge hexp huS hune a
  have hYspec : a ≤ ‖((BerendSec4.diag lam)^[Nat.find hex]) u‖ := Nat.find_spec hex
  have hYpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      rw [h] at hYspec
      simp only [Function.iterate_zero, id] at hYspec
      exact absurd hYspec (not_le.2 hult)
    · exact h
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 hYpos)
  have hkmin : ‖((BerendSec4.diag lam)^[k]) u‖ < a := by
    have hlt : k < Nat.find hex := by omega
    exact not_le.1 (Nat.find_min hex hlt)
  refine ⟨((BerendSec4.diag lam)^[Nat.find hex]) u, iterate_mem hinv _ huE,
    iterate_mem_coord _ huS, ?_, hYspec, ?_⟩
  · intro h0
    have hzero : ‖((BerendSec4.diag lam)^[Nat.find hex]) u‖ = 0 := by rw [h0]; simp
    linarith
  · have hstep : ((BerendSec4.diag lam)^[Nat.find hex]) u
        = BerendSec4.diag lam (((BerendSec4.diag lam)^[k]) u) := by
      rw [hk, Function.iterate_succ_apply']
    rw [hstep]
    exact (hN _).trans (mul_le_mul_of_nonneg_left (le_of_lt hkmin) (le_trans zero_le_one hN1))

end Annulus

/-! ## 3. Cones: the dominant coordinate, and accumulation inside one cone -/

/-- The closed cone of points of `coord S` whose `i`-th coordinate dominates all
coordinates of `S`.  The finitely many cones `dominantCone S i` (`i ∈ S`) cover
`coord S \ {0}`; this is the "cone" of plan §C.4. -/
def dominantCone (S : Finset ι) (i : ι) : Set (ι → ℝ) :=
  {x | x ∈ BerendSec4.coord (S : Set ι) ∧ ∀ j ∈ S, |x j| ≤ |x i|}

theorem mem_dominantCone {S : Finset ι} {i : ι} {x : ι → ℝ} :
    x ∈ dominantCone S i ↔ x ∈ BerendSec4.coord (S : Set ι) ∧ ∀ j ∈ S, |x j| ≤ |x i| :=
  Iff.rfl

/-- **The cones cover.**  Every nonzero point of `coord S` lies in one of the
cones `dominantCone S i`, `i ∈ S`. -/
theorem exists_dominantCone {S : Finset ι} {x : ι → ℝ}
    (hx : x ∈ BerendSec4.coord (S : Set ι)) (hne : x ≠ 0) :
    ∃ i ∈ S, x ∈ dominantCone S i := by
  classical
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exfalso
      refine hne (funext fun i => ?_)
      exact BerendSec4.mem_coord.1 hx i (by simp [h])
    · exact h
  obtain ⟨i₀, hi₀S, hi₀⟩ := Finset.exists_max_image S (fun i => |x i|) hSne
  exact ⟨i₀, hi₀S, hx, fun j hj => hi₀ j hj⟩

/-- **Plan §C.4, the cone form of `Acc`.**  If `E` is invariant under `diag lam`,
`1 < |lam i|` on `S`, and `0` is a non-isolated point of `E ∩ coord S`, then `E`
accumulates at `0` inside one *fixed* closed cone `dominantCone S i`.

Proof: the annulus lemma produces a nonzero point of `E ∩ coord S` of norm at
most `N/(k+1)` for every `k`; each of these lies in some cone, and by pigeonhole
over the finite set `S` one cone occurs at arbitrarily large `k`. -/
theorem exists_cone_accumulation {E : Set (ι → ℝ)} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) {S : Finset ι}
    (hexp : ∀ i ∈ S, 1 < |lam i|) (hacc : BerendSec4.Acc E S) :
    ∃ i ∈ S, ∀ a : ℝ, 0 < a → ∃ y ∈ E ∩ dominantCone S i, y ≠ 0 ∧ ‖y‖ ≤ a := by
  classical
  obtain ⟨N, hN1, hN⟩ := BerendSec4.exists_norm_bound (ι := ι) lam
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hseq : ∀ k : ℕ, ∃ y : ι → ℝ,
      y ∈ E ∧ y ∈ BerendSec4.coord (S : Set ι) ∧ y ≠ 0 ∧ ‖y‖ ≤ N * (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨y, hyE, hyS, hyne, -, hle⟩ :=
      exists_annulus_point (a := 1 / ((k : ℝ) + 1)) hinv hexp hacc (by positivity) hN1 hN
    exact ⟨y, hyE, hyS, hyne, hle⟩
  choose y hyE hyS hyne hynorm using hseq
  have hdom : ∀ k : ℕ, ∃ i : ι, i ∈ S ∧ y k ∈ dominantCone S i :=
    fun k => exists_dominantCone (hyS k) (hyne k)
  choose ii hiiS hiiCone using hdom
  -- pigeonhole over the finite set `S`
  have hpigeon : ∃ i₀ ∈ S, ∀ m : ℕ, ∃ k : ℕ, m ≤ k ∧ ii k = i₀ := by
    by_contra hcon
    push Not at hcon
    have hexm : ∀ i : ι, ∃ m : ℕ, i ∈ S → ∀ k : ℕ, m ≤ k → ii k ≠ i := by
      intro i
      by_cases hi : i ∈ S
      · obtain ⟨m, hm⟩ := hcon i hi
        exact ⟨m, fun _ => hm⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose m hm using hexm
    have hbound : m (ii (S.sup m)) ≤ S.sup m :=
      Finset.le_sup (s := S) (f := m) (hiiS (S.sup m))
    exact hm (ii (S.sup m)) (hiiS (S.sup m)) (S.sup m) hbound rfl
  obtain ⟨i₀, hi₀S, hrec⟩ := hpigeon
  refine ⟨i₀, hi₀S, fun a ha => ?_⟩
  -- choose `k₀` with `N / (k₀ + 1) < a`, then a later `k` with `ii k = i₀`
  have hexk : ∃ k₀ : ℕ, N * (1 / ((k₀ : ℝ) + 1)) < a := by
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (N / a)
    have hk₀pos : (0 : ℝ) < (k₀ : ℝ) := lt_trans (div_pos hNpos ha) hk₀
    refine ⟨k₀, ?_⟩
    rw [mul_one_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (k₀ : ℝ) + 1)]
    have h1 : N < (k₀ : ℝ) * a := by
      rw [div_lt_iff₀ ha] at hk₀
      linarith
    nlinarith [h1, hk₀pos, hNpos.le, ha]
  obtain ⟨k₀, hk₀⟩ := hexk
  obtain ⟨k, hk, hik⟩ := hrec k₀
  refine ⟨y k, ⟨hyE k, ?_⟩, hyne k, ?_⟩
  · rw [← hik]; exact hiiCone k
  · refine le_trans (hynorm k) ?_
    have hmono : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
      have hkk : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith
    nlinarith [hNpos.le, hmono]


/-! ## 4. The accumulation directions at `0`: the projective object of §C.4 -/

/-- **The set of accumulation directions of `E` at `0` inside `coord S`.**  A unit
vector `ξ ∈ coord S` is an accumulation direction when some sequence
`0 ≠ f n ∈ E` with `f n ∈ coord S` tends to `0` with normalized directions
`‖f n‖⁻¹ • f n → ξ`.

This is the "cone" datum the paper's §4 keeps about `E` at `0`: the directions
from which `E` approaches the origin.  It is a subset of the unit sphere. -/
def dirSet (E : Set (ι → ℝ)) (S : Finset ι) : Set (ι → ℝ) :=
  {ξ | ξ ∈ BerendSec4.coord (S : Set ι) ∧ ‖ξ‖ = 1 ∧
    ∃ f : ℕ → ι → ℝ, (∀ n, f n ∈ E) ∧ (∀ n, f n ∈ BerendSec4.coord (S : Set ι)) ∧
      (∀ n, f n ≠ 0) ∧ Tendsto f atTop (𝓝 0) ∧
      Tendsto (fun n => ‖f n‖⁻¹ • f n) atTop (𝓝 ξ)}

/-- **Accumulation directions exist.**  If `0` is a non-isolated point of
`E ∩ coord S`, the compactness of the unit sphere of `coord S` yields an
accumulation direction. -/
theorem dirSet_nonempty {E : Set (ι → ℝ)} {S : Finset ι} (hacc : BerendSec4.Acc E S) :
    (dirSet E S).Nonempty := by
  classical
  have hseq : ∀ n : ℕ, ∃ u : ι → ℝ, u ∈ E ∧ u ∈ BerendSec4.coord (S : Set ι) ∧ u ≠ 0 ∧
      ‖u‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact BerendSec4.acc_iff.1 hacc _ (by positivity)
  choose x hxE hxS hxne hxs using hseq
  set d : ℕ → ι → ℝ := fun n => ‖x n‖⁻¹ • x n with hd
  have hdsphere : ∀ n, d n ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_smul_inv_norm (hxne n)
  have hdcoord : ∀ n, d n ∈ BerendSec4.coord (S : Set ι) := fun n =>
    (BerendSec4.coord (S : Set ι)).smul_mem _ (hxS n)
  have hK : IsCompact ((Metric.sphere (0 : ι → ℝ) 1) ∩
      (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))) :=
    (isCompact_sphere (0 : ι → ℝ) 1).inter_right (Submodule.closed_of_finiteDimensional _)
  obtain ⟨ξ, hξK, φ, hφ, hφtend⟩ := hK.tendsto_subseq (x := d) fun n => ⟨hdsphere n, hdcoord n⟩
  have hξnorm : ‖ξ‖ = 1 := by
    have h := hξK.1
    rwa [Metric.mem_sphere, dist_zero_right] at h
  refine ⟨ξ, hξK.2, hξnorm, x ∘ φ, fun n => hxE (φ n), fun n => hxS (φ n),
    fun n => hxne (φ n), ?_, ?_⟩
  · refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_) ?_
    · show ‖x (φ n)‖ ≤ 1 / ((n : ℝ) + 1)
      have h1 : ‖x (φ n)‖ < 1 / ((φ n : ℝ) + 1) := hxs (φ n)
      have hφn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
      have h2 : (1 : ℝ) / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        linarith
      linarith
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact hφtend

/-- The projectivized dilation `ξ ↦ [diag lam ξ]` on directions. -/
noncomputable def projDil (lam : ι → ℝ) (ξ : ι → ℝ) : ι → ℝ :=
  ‖BerendSec4.diag lam ξ‖⁻¹ • BerendSec4.diag lam ξ

/-- `projDil` is homogeneous: only the direction of its argument matters. -/
theorem projDil_smul (lam : ι → ℝ) {c : ℝ} (hc : 0 < c) (w : ι → ℝ) :
    projDil lam (c • w) = projDil lam w := by
  have hsmul : BerendSec4.diag lam (c • w) = c • BerendSec4.diag lam w := by
    rw [map_smul]
  rw [projDil, projDil, hsmul, norm_smul, Real.norm_of_nonneg hc.le, smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- `projDil` lands in the unit sphere as soon as `diag lam ξ ≠ 0`. -/
theorem norm_projDil (lam : ι → ℝ) {ξ : ι → ℝ} (h : BerendSec4.diag lam ξ ≠ 0) :
    ‖projDil lam ξ‖ = 1 :=
  norm_smul_inv_norm h

/-- **The accumulation direction set is invariant under the projectivized
dilation.**  This is the structural fact §C.4 keeps about the origin: expanding
`E` and renormalizing permutes (indeed carries into itself) the directions from
which `E` approaches `0`. -/
theorem dirSet_mapsTo {E : Set (ι → ℝ)} {S : Finset ι} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) (hlam : ∀ i ∈ S, lam i ≠ 0) :
    MapsTo (projDil lam) (dirSet E S) (dirSet E S) := by
  rintro ξ ⟨hξcoord, hξnorm, f, hfE, hfS, hfne, hf0, hfdir⟩
  -- `ξ` has a nonzero coordinate in `S`, hence so does `diag lam ξ`
  have hξne : ξ ≠ 0 := by
    intro h
    rw [h] at hξnorm
    simp at hξnorm
  obtain ⟨i₀, hi₀ne⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hξne (funext h)
  have hi₀S : i₀ ∈ S := by
    by_contra h
    exact hi₀ne (BerendSec4.mem_coord.1 hξcoord i₀ h)
  have hdξ : BerendSec4.diag lam ξ ≠ 0 := by
    intro h
    have hcoord := congrFun h i₀
    simp only [BerendSec4.diag_apply, Pi.zero_apply] at hcoord
    exact mul_ne_zero (hlam i₀ hi₀S) hi₀ne hcoord
  -- the witness sequence: images of `f n`
  have hgne : ∀ n, BerendSec4.diag lam (f n) ≠ 0 := by
    intro n h
    have hfnn : f n ≠ 0 := hfne n
    obtain ⟨i, hine⟩ : ∃ i, f n i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hfnn (funext h')
    have hiS : i ∈ S := by
      by_contra h'
      exact hine (BerendSec4.mem_coord.1 (hfS n) i h')
    have := congrFun h i
    simp only [BerendSec4.diag_apply, Pi.zero_apply] at this
    exact mul_ne_zero (hlam i hiS) hine this
  refine ⟨?_, norm_projDil lam hdξ, fun n => BerendSec4.diag lam (f n),
    fun n => hinv _ (hfE n), fun n => BerendSec4.diag_mem_coord lam (hfS n), hgne, ?_, ?_⟩
  · exact (BerendSec4.coord (S : Set ι)).smul_mem _ (BerendSec4.diag_mem_coord lam hξcoord)
  · have hcont : Tendsto (BerendSec4.diag lam) (𝓝 0) (𝓝 (BerendSec4.diag lam 0)) :=
      (BerendSec4.continuous_diag lam).tendsto 0
    have := hcont.comp hf0
    simpa [Function.comp_def] using this
  · -- the normalized images are `projDil` of the normalized preimages
    have hcont : ContinuousAt (projDil lam) ξ := by
      have h1 : ContinuousAt (fun w : ι → ℝ => ‖w‖⁻¹) (BerendSec4.diag lam ξ) :=
        (continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hdξ)
      have h2 : ContinuousAt (fun w : ι → ℝ => w) (BerendSec4.diag lam ξ) :=
        continuousAt_id
      exact (h1.smul h2).comp (BerendSec4.continuous_diag lam).continuousAt
    have hcomp : Tendsto (fun n => projDil lam (‖f n‖⁻¹ • f n)) atTop (𝓝 (projDil lam ξ)) :=
      hcont.tendsto.comp hfdir
    have hpoint : ∀ n : ℕ, ‖BerendSec4.diag lam (f n)‖⁻¹ • BerendSec4.diag lam (f n)
        = projDil lam (‖f n‖⁻¹ • f n) := by
      intro n
      rw [projDil_smul lam (c := (‖f n‖)⁻¹) (inv_pos.2 (norm_pos_iff.2 (hfne n)))]
      rfl
    rw [show (fun n : ℕ => ‖BerendSec4.diag lam (f n)‖⁻¹ • BerendSec4.diag lam (f n))
        = fun n => projDil lam (‖f n‖⁻¹ • f n) from funext hpoint]
    exact hcomp

/-- **Directions are exactly the accumulation datum.**  `E` accumulates at `0`
inside `coord S` iff it has at least one accumulation direction there, so
`dirSet` loses no information about `Acc`. -/
theorem acc_iff_dirSet_nonempty {E : Set (ι → ℝ)} {S : Finset ι} :
    BerendSec4.Acc E S ↔ (dirSet E S).Nonempty := by
  constructor
  · exact dirSet_nonempty
  · rintro ⟨ξ, -, -, f, hfE, hfS, hfne, hf0, -⟩
    rw [BerendSec4.acc_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 hf0) ε hε
    exact ⟨f n, hfE n, hfS n, hfne n, by simpa [dist_eq_norm] using hn n le_rfl⟩

/-! ## 5. The quotient (torus) form of the diagonal covering step, plan §C.6

Plan §C.6 has to carry a *linear-model* conclusion back to the torus
`Pt ⧸ L`.  The covering package `BerendCovering` provides this for a single
scalar multiplier on the quotient (`eq_univ_of_invariant_of_scalar`) and for the
diagonal map on the linear space (`eq_univ_of_invariant_of_pi_mul`), but not for
a **diagonal** map on the quotient.  This section closes that gap: if `s` on
`(ι → ℝ) ⧸ L` is induced by a coordinatewise dilation `x ↦ (c i * x i)` with
`1 < c i`, then the iterates of any ball around `0` cover the quotient, so a
closed invariant set containing a ball around `0` is everything.

(Note that *some* hypothesis forcing every coordinate to expand is needed: with
`c` having a coordinate `< 1` the cover fails.  This is exactly the hypothesis
`1 < |lam i|` on the selected coordinate set in `exists_minimal_and_expanding`.)
-/

section QuotientDiagonal

variable {L : AddSubgroup (ι → ℝ)} {s : (ι → ℝ) ⧸ L → (ι → ℝ) ⧸ L} {c : ι → ℝ}

/-- Iterating a quotient map induced by a coordinatewise dilation multiplies the
representation coordinatewise by the powers of `c`. -/
theorem iterate_diag_quotient
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    (k : ℕ) (t : ι → ℝ) :
    s^[k] (QuotientAddGroup.mk' L t)
      = QuotientAddGroup.mk' L ((fun z : ι → ℝ => fun i => c i * z i)^[k] t) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hs, Function.iterate_succ_apply']

/-- **The covering fact for coordinatewise dilations on a quotient.**  If every
coordinate multiplier exceeds `1`, then every point of `(ι → ℝ) ⧸ L` is the
`k`-th iterate of a point within distance `δ` of `0`. -/
theorem exists_iterate_mem_ball_pi_quotient (hc : ∀ i, 1 < c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {δ : ℝ} (hδ : 0 < δ) (z : (ι → ℝ) ⧸ L) :
    ∃ k : ℕ, ∃ y ∈ Metric.ball (0 : (ι → ℝ) ⧸ L) δ, s^[k] y = z := by
  classical
  have hc0 : ∀ i, (0 : ℝ) < c i := fun i => lt_trans zero_lt_one (hc i)
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  have hsingle : ∀ i, ∀ᶠ k : ℕ in atTop, |t i| / (c i) ^ k < δ := by
    intro i
    have hcpow : Tendsto (fun k : ℕ => (c i) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (hc i)
    have hzero : Tendsto (fun k : ℕ => |t i| / (c i) ^ k) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hcpow
    exact (tendsto_order.1 hzero).2 δ hδ
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i, |t i| / (c i) ^ k < δ :=
    Filter.eventually_all.2 hsingle
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hall
  refine ⟨a, QuotientAddGroup.mk' L (fun i => ((c i) ^ a)⁻¹ * t i), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm (S := L) (m := fun i => ((c i) ^ a)⁻¹ * t i)) ?_
    rw [pi_norm_lt_iff hδ]
    intro i
    have hlt : |t i| / (c i) ^ a < δ := ha a le_rfl i
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, abs_of_pos (hc0 i), inv_mul_eq_div]
    exact hlt
  · rw [iterate_diag_quotient hs]
    congr 1
    funext i
    rw [BerendExpansion.iterate_pi_mul]
    show (c i) ^ a * (((c i) ^ a)⁻¹ * t i) = t i
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero a (hc0 i).ne'), one_mul]

/-- **Plan §C.6, quotient form.**  A set of the torus `(ι → ℝ) ⧸ L` invariant
under a coordinatewise expanding dilation and containing a ball around `0` is
everything.  This is the torus-level partner of
`BerendExpansion.eq_univ_of_invariant_of_pi_mul`. -/
theorem eq_univ_of_invariant_of_pi_mul_quotient (hc : ∀ i, 1 < c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {B : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ B, s y ∈ B) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : (ι → ℝ) ⧸ L) δ ⊆ B) : B = univ :=
  BerendExpansion.eq_univ_of_mapsTo_of_iterate_cover (s := s) (fun _ hy => hinv _ hy) hball
    fun z => exists_iterate_mem_ball_pi_quotient hc hs hδ z

end QuotientDiagonal

/-! ## 6. Bridges between the torus and the diagonal model, and the §C.6 last mile

`BerendSec4` works on the linear model `ι → ℝ`; the theorem is about the torus
`Pt ⧸ L`.  The two lemmas here are the transport in the two directions.

* **In** (`acc_preimage_of_zero_nonisolated`): if `0` is a non-isolated point of
  `Y ⊆ (ι → ℝ) ⧸ L`, then the full preimage of `Y` accumulates at `0` in the
  linear model, i.e. `BerendSec4.Acc (mk' L ⁻¹' Y) univ` holds.  This is the
  entry point of stage C (plan §D.2) after the eigenbasis change.
* **Out** (`eq_univ_of_ball_subset_preimage`): the last mile of plan §C.6.  If
  the preimage in the linear model contains a ball around `0`, then the torus
  set contains a ball around `0` (the quotient map is open), and §5 then makes
  it everything.
-/

section Bridges

variable {L : AddSubgroup (ι → ℝ)}

/-- A small nonzero point of the linear model over a near-origin point of `Y`. -/
theorem exists_small_rep {Y : Set ((ι → ℝ) ⧸ L)}
    (h : (0 : (ι → ℝ) ⧸ L) ∈ closure (Y \ {0})) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ x ∈ QuotientAddGroup.mk' L ⁻¹' Y ∧ ‖x‖ < δ := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hopen : IsOpen (Metric.ball (0 : (ι → ℝ) ⧸ L) (δ / 2)) := Metric.isOpen_ball
  obtain ⟨y, hyball, hyY, hyne⟩ := (mem_closure_iff.1 h) _ hopen (Metric.mem_ball_self hδ2)
  have hysmall : ‖y‖ < δ / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hyball
  obtain ⟨v, hv, hvnorm⟩ := QuotientAddGroup.exists_norm_mk_lt y hδ2
  have hv' : QuotientAddGroup.mk' L v = y := hv
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv0
    rw [hv0] at hv'
    exact hyne (by simpa using hv'.symm)
  · rw [mem_preimage, hv']
    exact hyY
  · have : ‖v‖ < ‖y‖ + δ / 2 := hvnorm
    linarith

/-- **Entry point of stage C from the torus.**  If `0` is a non-isolated point of
`Y ⊆ (ι → ℝ) ⧸ L`, the full preimage of `Y` accumulates at `0` in the linear
model. -/
theorem acc_preimage_of_zero_nonisolated {Y : Set ((ι → ℝ) ⧸ L)}
    (h : (0 : (ι → ℝ) ⧸ L) ∈ closure (Y \ {0})) :
    BerendSec4.Acc (QuotientAddGroup.mk' L ⁻¹' Y) Finset.univ := by
  rw [BerendSec4.acc_iff]
  intro ε hε
  obtain ⟨x, hxne, hxY, hxnorm⟩ := exists_small_rep h hε
  refine ⟨x, hxY, ?_, hxne, hxnorm⟩
  intro i hi
  simp at hi

/-- The quotient map is open, so a set whose preimage contains a ball around `0`
contains a ball around `0`. -/
theorem exists_ball_subset_of_preimage_ball {Y : Set ((ι → ℝ) ⧸ L)} {δ : ℝ} (hδ : 0 < δ)
    (h : Metric.ball (0 : ι → ℝ) δ ⊆ QuotientAddGroup.mk' L ⁻¹' Y) :
    ∃ δ' : ℝ, 0 < δ' ∧ Metric.ball (0 : (ι → ℝ) ⧸ L) δ' ⊆ Y := by
  have hopen : IsOpen (QuotientAddGroup.mk' L '' Metric.ball (0 : ι → ℝ) δ) :=
    QuotientAddGroup.isOpenMap_coe _ Metric.isOpen_ball
  have h0 : (0 : (ι → ℝ) ⧸ L) ∈ QuotientAddGroup.mk' L '' Metric.ball (0 : ι → ℝ) δ :=
    ⟨0, Metric.mem_ball_self hδ, map_zero _⟩
  obtain ⟨δ', hδ', hball⟩ := Metric.isOpen_iff.1 hopen _ h0
  refine ⟨δ', hδ', fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hball hy
  exact h hx

/-- **Plan §C.6, last mile.**  Let `s` on the torus `(ι → ℝ) ⧸ L` be induced by a
coordinatewise dilation with all multipliers `> 1`.  If the preimage in the
linear model of an `s`-invariant set `Y` contains a ball around `0`, then `Y` is
everything. -/
theorem eq_univ_of_ball_subset_preimage {s : (ι → ℝ) ⧸ L → (ι → ℝ) ⧸ L} {c : ι → ℝ}
    (hc : ∀ i, 1 < c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {Y : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ Y, s y ∈ Y) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (0 : ι → ℝ) δ ⊆ QuotientAddGroup.mk' L ⁻¹' Y) : Y = univ := by
  obtain ⟨δ', hδ', hsub⟩ := exists_ball_subset_of_preimage_ball hδ hball
  exact eq_univ_of_invariant_of_pi_mul_quotient hc hs hinv hδ' hsub

end Bridges

/-! ## 7. "Expansion and translation": a nonempty open subset of the torus forces
everything (plan §C.4, last sentence)

Plan §C.4 ends with "produce a point of the invariant set in a full open cone and
then in a nonempty open subset of the selected invariant subspace.  **Continue by
expansion and translation** to get a whole coordinate subspace."  At the level of
the torus the corresponding statement is clean and strong: an invariant set
containing *any* open ball (not necessarily around `0`) is the whole torus.  The
proof is the covering mechanism of §5 together with additivity of the dilation:
the iterates of a ball of radius `δ` contain balls of radius `m ^ k * δ`
(`m > 1` a lower bound for the multipliers), and the quotient norm is bounded, so
some iterate of the ball is all of the torus.
-/

section ExpansionTranslation

variable {L : AddSubgroup (ι → ℝ)} {s : (ι → ℝ) ⧸ L → (ι → ℝ) ⧸ L} {c : ι → ℝ}

/-- **Ball scaling.**  The `k`-th iterate of the ball of radius `δ` around `0`
contains the ball of radius `m ^ k * δ`, for any `1 < m ≤ c i`. -/
theorem ball_subset_iterate_ball_image {m : ℝ} (hm1 : 1 < m)
    (hmc : ∀ i, m ≤ c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    Metric.ball (0 : (ι → ℝ) ⧸ L) (m ^ k * δ) ⊆ s^[k] '' Metric.ball (0 : (ι → ℝ) ⧸ L) δ := by
  classical
  have hm0 : (0 : ℝ) < m := lt_trans zero_lt_one hm1
  have hcpow_pos : (0 : ℝ) < m ^ k := pow_pos hm0 k
  intro w hw
  have hwnorm : ‖w‖ < m ^ k * δ := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hε : 0 < (m ^ k * δ - ‖w‖) / 2 := by linarith
  obtain ⟨t, ht, htne⟩ := QuotientAddGroup.exists_norm_mk_lt w hε
  -- the preimage point
  refine ⟨QuotientAddGroup.mk' L (fun i => ((c i) ^ k)⁻¹ * t i), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt
      (QuotientAddGroup.norm_mk_le_norm (S := L) (m := fun i => ((c i) ^ k)⁻¹ * t i)) ?_
    rw [pi_norm_lt_iff hδ]
    intro i
    have hci : m ≤ c i := hmc i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le hm0 hci
    have hck : m ^ k ≤ (c i) ^ k := pow_le_pow_left₀ hm0.le hci k
    have hti : |t i| < m ^ k * δ := by
      have h1 : |t i| ≤ ‖t‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm t i
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, abs_of_pos hci0, inv_mul_eq_div,
      div_lt_iff₀ (pow_pos hci0 k)]
    calc |t i| < m ^ k * δ := hti
      _ ≤ (c i) ^ k * δ := by nlinarith [hδ.le]
      _ = δ * (c i) ^ k := by ring
  · rw [← ht, iterate_diag_quotient hs]
    have hfix : (fun z : ι → ℝ => fun i => c i * z i)^[k] (fun i => ((c i) ^ k)⁻¹ * t i) = t := by
      funext i
      rw [BerendExpansion.iterate_pi_mul]
      show (c i) ^ k * (((c i) ^ k)⁻¹ * t i) = t i
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (ne_of_gt (lt_of_lt_of_le hm0 (hmc i)))),
        one_mul]
    rw [hfix]
    rfl

/-- The dilation `s` on the torus is additive (it is induced by a linear map). -/
theorem add_of_diag_quotient
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    (a b : (ι → ℝ) ⧸ L) : s (a + b) = s a + s b := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective L a
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective L b
  rw [← map_add, hs, hs, hs, ← map_add]
  congr 1
  funext i
  simp only [Pi.add_apply, mul_add]

/-- Additivity of the iterates of `s`. -/
theorem iterate_add_of_diag_quotient
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    (k : ℕ) (a b : (ι → ℝ) ⧸ L) : s^[k] (a + b) = s^[k] a + s^[k] b := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, add_of_diag_quotient hs,
        Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterates of `s` preserve invariance. -/
theorem iterate_mem_quotient {E : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ E, s y ∈ E)
    (k : ℕ) {y : (ι → ℝ) ⧸ L} (hy : y ∈ E) : s^[k] y ∈ E := by
  induction k with
  | zero => simpa using hy
  | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih

/-- **Plan §C.4, "continue by expansion and translation".**  Let `s` be induced on
the torus by a coordinatewise dilation whose multipliers are all at least
`m > 1`, let `R` bound the norm of the torus (compactness), and let `E` be
`s`-invariant.  If `E` contains *any* open ball `ball y δ` (not necessarily
around `0`), then `E` is the whole torus.

Proof: the `k`-th iterate of `ball 0 δ` contains `ball 0 (m^k δ)`, and `m^k δ`
eventually exceeds `R`, so by additivity `z = s^[k] y + s^[k] b = s^[k] (y + b)`
with `b ∈ ball 0 δ`; invariance then gives `z ∈ E`. -/
theorem eq_univ_of_ball_subset {m R : ℝ} (hm1 : 1 < m) (hmc : ∀ i, m ≤ c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {E : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ E, s y ∈ E) {y : (ι → ℝ) ⧸ L}
    {δ : ℝ} (hδ : 0 < δ) (hball : Metric.ball y δ ⊆ E) (hR : ∀ z : (ι → ℝ) ⧸ L, ‖z‖ ≤ R) :
    E = univ := by
  classical
  refine eq_univ_of_forall fun z => ?_
  -- a `k` with the scaled radius exceeding the diameter bound
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / δ) hm1
  have hk' : R < m ^ k * δ := by
    rw [div_lt_iff₀ hδ] at hk
    linarith
  have hsub : z - s^[k] y ∈ Metric.ball (0 : (ι → ℝ) ⧸ L) (m ^ k * δ) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hR _) hk'
  obtain ⟨b, hb, hbk⟩ := ball_subset_iterate_ball_image hm1 hmc hs hδ k hsub
  have hyb : y + b ∈ E := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : y + b - y = b := by abel
    rw [hdiff]
    simpa [Metric.mem_ball, dist_zero_right] using hb
  have hz : s^[k] (y + b) = z := by
    rw [iterate_add_of_diag_quotient hs, hbk]
    abel
  rw [← hz]
  exact iterate_mem_quotient hinv k hyb

/-- **Nonempty interior forces the whole torus.**  This is the form in which plan
§C.4's last sentence ("continue by expansion and translation") is consumed: the
cone step only has to exhibit *some* nonempty open subset of the invariant set,
not a neighbourhood of `0`. -/
theorem eq_univ_of_interior_nonempty {m R : ℝ} (hm1 : 1 < m) (hmc : ∀ i, m ≤ c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {E : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ E, s y ∈ E) (hint : (interior E).Nonempty)
    (hR : ∀ z : (ι → ℝ) ⧸ L, ‖z‖ ≤ R) : E = univ := by
  obtain ⟨y, hy⟩ := hint
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  exact eq_univ_of_ball_subset hm1 hmc hs hinv hδ (fun x hx => interior_subset (hball hx)) hR

/-- In a compact normed space the norm is bounded; this supplies the constant `R`
of `eq_univ_of_ball_subset` for a compact torus. -/
theorem exists_norm_bound_of_compactSpace (T : Type*) [SeminormedAddCommGroup T] [CompactSpace T] :
    ∃ R : ℝ, ∀ z : T, ‖z‖ ≤ R := by
  have hb : Bornology.IsBounded (Set.univ : Set T) := isCompact_univ.isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hb
  exact ⟨C, fun z => by
    simpa [dist_zero_right] using hC (Set.mem_univ (0 : T)) (Set.mem_univ z)⟩

/-- **Compact-torus form of §C.4's last sentence**: no explicit diameter bound is
needed when the torus is compact (e.g. `L` a lattice). -/
theorem eq_univ_of_interior_nonempty_of_compactSpace [CompactSpace ((ι → ℝ) ⧸ L)]
    {m : ℝ} (hm1 : 1 < m) (hmc : ∀ i, m ≤ c i)
    (hs : ∀ t : ι → ℝ, s (QuotientAddGroup.mk' L t) = QuotientAddGroup.mk' L (fun i => c i * t i))
    {E : Set ((ι → ℝ) ⧸ L)} (hinv : ∀ y ∈ E, s y ∈ E) (hint : (interior E).Nonempty) :
    E = univ := by
  obtain ⟨R, hR⟩ := exists_norm_bound_of_compactSpace ((ι → ℝ) ⧸ L)
  exact eq_univ_of_interior_nonempty hm1 hmc hs hinv hint hR

end ExpansionTranslation

end BerendCone

end CubicTwoStage
