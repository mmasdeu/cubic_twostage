/-
# Stage I of Berend's multi-invariance theorem: the one-dimensional (`k = 1`) branch

`BEREND_PROOF_PLAN.md` §C reduces Stage I (`eq_univ_of_zero_nonisolated`) to a minimal
accumulating coordinate set `S`, on which Berend's Lemmas 4.1-4.3 produce a backward orbit
in the full cone and Lemma 4.4 produces either *common rates* on `S` or a reduction to
`|S| = 1`.  This module discharges the `|S| = 1` alternative:

* `eLine_mem_of_mul_nonneg` (with `norm_eLine`, `diag_iterate_eLine`, `iterate_mem`) —
  if a closed set is invariant under two diagonal maps multiplying by `a > 1` and
  `b ∈ (0,1)` at coordinate `i`, with `log a / log b` irrational (corrected (B3) read on
  the multipliers), and contains the nonzero point `t • e i`, then it contains the
  half-line `{s • e i : 0 ≤ s t}`.  The proof is the density of `{a ^ m * b ^ n}` in
  `(0, ∞)`, i.e. `BerendRankTwo.exists_pow_mul_pow_near`, plus closedness.

* `neg_mem_of_closed_add_subsemigroup`, `addMonoidHom_mem_of_mem_Ici` /
  `addMonoidHom_mem_of_mem_Iic` — **a one-sided ray in a compact torus is two-sided**:
  a closed additive subsemigroup of a compact additive group is a subgroup (via
  `exists_idempotent_in_compact_add_subsemigroup`), so a closed set containing
  `{φ s : s ≥ 0}` for a continuous homomorphism `φ : ℝ →+ T` contains `φ '' univ`.

* **`eq_univ_of_acc_coord`** — **Stage I, `k = 1` branch.**  If the lift of a closed
  `Y ⊆ (ι → ℝ) ⧸ L` accumulates at `0` on the single coordinate line `coord {i}`
  (Berend Lemmas 4.1-4.3), the lift is invariant under the expanding/contracting pair with
  independent multipliers at `i`, and `coord {i} + L` is dense, then **`Y = univ`**.

  This is *not* a difference-set statement.  The `BerendRankTwoDiag` /
  `BerendModulus` / `BerendTorusLastMile` route produces `Y - Y = univ` from the same
  hypotheses; that conclusion cannot give `Y = univ` (the base-`2` Cantor set `D` has
  `D - D = 𝕋` and is closed, `×2`-invariant with `0` non-isolated, and proper).  Here the
  accumulation point itself generates a ray in `Y`, and the ray closure is the whole torus.

* `eq_univ_of_acc_coord_of_weights` — the same with the multipliers read off a common
  weight vector (`lam i = c ^ w`, `mu i = d ^ w`, `c > 1 > d > 0` multiplicatively
  independent), the form in which `BerendRate.exists_common_rate` delivers Lemma 4.4.

## The remaining input, precisely

The only hypothesis not produced by the existing project modules is

`Dense ((coord {i} : Set (ι → ℝ)) + (L : Set (ι → ℝ)))`,

equivalently: no nonzero character of `(ι → ℝ) ⧸ L` annihilates the `i`-th basis vector
(no nonzero `k` with `⟨k, L⟩ ⊆ ℤ` and `k i = 0`).  When it fails, the closure of the
coordinate circle is a *proper* non-zero closed connected subgroup `H ⊆ Y`; its tangent
space `W` contains `ℝ • e i`, is invariant (every family member is diagonal, so it maps
`W` to itself) and rational (closed connected subgroups of a torus are images of rational
subspaces), so `W` is a proper non-zero invariant rational subspace: exactly what (B1)
forbids.  Hence **under (B1) the density hypothesis is automatic, and this module closes
the `k = 1` branch of Stage I** once the (B1) consequence "no proper invariant rational
subspace" is available; this module isolates that single missing step rather than assuming
the conclusion.

## Trust

No `axiom`, no `sorry`, no assumed `Prop`, no import of `CubicTwoStage.Berend`.  Every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound` (printed at the
end of the file).
-/
/-
Stage I of Berend's multi-invariance theorem: the one-dimensional (`k = 1`) branch.
-/
import CubicTwoStage.BerendModulus
import CubicTwoStage.BerendRankTwoDiag
import CubicTwoStage.BerendCone

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace CubicTwoStage
namespace BerendStageILine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The coordinate ray `s ↦ s • e i` -/

/-- The point with coordinate `s` at `i` and `0` elsewhere. -/
noncomputable def eLine (i : ι) (s : ℝ) : ι → ℝ := fun j => if j = i then s else 0

@[simp] theorem eLine_self (i : ι) (s : ℝ) : eLine i s i = s := by simp [eLine]

theorem eLine_of_ne {i j : ι} (h : j ≠ i) (s : ℝ) : eLine i s j = 0 := by simp [eLine, h]

theorem eLine_zero (i : ι) : eLine i 0 = (0 : ι → ℝ) := by funext j; simp [eLine]

theorem eLine_add (i : ι) (s s' : ℝ) : eLine i (s + s') = eLine i s + eLine i s' := by
  funext j
  by_cases h : j = i <;> simp [eLine, h]

theorem eLine_sub (i : ι) (s s' : ℝ) : eLine i s - eLine i s' = eLine i (s - s') := by
  funext j
  by_cases h : j = i <;> simp [eLine, h]

theorem eLine_mem_coord (i : ι) (s : ℝ) :
    eLine i s ∈ BerendSec4.coord ({i} : Set ι) := by
  intro j hj
  exact eLine_of_ne (by simpa using hj) s

theorem eq_eLine_of_mem_coord {i : ι} {x : ι → ℝ}
    (hx : x ∈ BerendSec4.coord ({i} : Set ι)) : x = eLine i (x i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [eLine_of_ne hj]
    exact (BerendSec4.mem_coord.1 hx) j (by simpa using hj)

theorem continuous_eLine (i : ι) : Continuous (eLine i) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hfun : (fun s : ℝ => eLine j s j) = id := by funext s; simp
    rw [hfun]; exact continuous_id
  · have hfun : (fun s : ℝ => eLine i s j) = fun _ => (0 : ℝ) := by
      funext s; exact eLine_of_ne hj s
    rw [hfun]; exact continuous_const

theorem norm_eLine (i : ι) (s : ℝ) : ‖eLine i s‖ = |s| := by
  have hle : ‖eLine i s‖ ≤ |s| := by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg s)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases h : j = i
    · simp [eLine, h]
    · simp [eLine, h]
  have hge : |s| ≤ ‖eLine i s‖ := by
    calc |s| = ‖eLine i s i‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖eLine i s‖ := norm_le_pi_norm _ i
  linarith

theorem diag_eLine (lam : ι → ℝ) (i : ι) (s : ℝ) :
    BerendSec4.diag lam (eLine i s) = eLine i (lam i * s) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [BerendSec4.diag_apply, eLine]
  · simp [BerendSec4.diag_apply, eLine, hj]

theorem iterate_mem {E : Set (ι → ℝ)} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) :
    ∀ (k : ℕ) {x : ι → ℝ}, x ∈ E → ((BerendSec4.diag lam)^[k]) x ∈ E
  | 0, x, hx => by simpa using hx
  | (k + 1), x, hx => by
      rw [Function.iterate_succ_apply]
      exact iterate_mem hinv k (hinv x hx)

theorem diag_iterate_eLine (lam : ι → ℝ) (i : ι) (s : ℝ) (m : ℕ) :
    ((BerendSec4.diag lam)^[m]) (eLine i s) = eLine i ((lam i) ^ m * s) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, diag_eLine, pow_succ]
      congr 1
      ring_nf

/-! ## 2. The ray through a point of the invariant set -/

/-- **The ray lemma.**  If a closed set is invariant under two diagonal maps which at the
coordinate `i` multiply by `a > 1` and by `b ∈ (0,1)` with `log a / log b` irrational, and it
contains the nonzero point `t • e i`, then it contains the half-line in the direction of `t`. -/
theorem eLine_mem_of_mul_nonneg {E : Set (ι → ℝ)} (hE : IsClosed E)
    {lam mu : ι → ℝ} (hinv1 : ∀ x ∈ E, BerendSec4.diag lam x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag mu x ∈ E)
    {i : ι} {a b : ℝ} (ha : 1 < a) (hb0 : 0 < b) (hb1 : b < 1)
    (hirr : Irrational (Real.log a / Real.log b))
    (hlam : lam i = a) (hmu : mu i = b)
    {t : ℝ} (ht : t ≠ 0) (hx : eLine i t ∈ E) :
    ∀ s : ℝ, 0 ≤ s * t → eLine i s ∈ E := by
  have hiter : ∀ m n : ℕ, eLine i (a ^ m * b ^ n * t) ∈ E := by
    intro m n
    have h1 : ((BerendSec4.diag lam)^[m]) (eLine i t) ∈ E :=
      iterate_mem hinv1 m hx
    have h2 : ((BerendSec4.diag mu)^[n]) (((BerendSec4.diag lam)^[m]) (eLine i t)) ∈ E :=
      iterate_mem hinv2 n h1
    rw [diag_iterate_eLine, diag_iterate_eLine, hlam, hmu] at h2
    have hfun : a ^ m * b ^ n * t = b ^ n * (a ^ m * t) := by ring
    rwa [hfun]
  intro s hs
  rcases eq_or_lt_of_le hs with hzero | hpos
  · -- `s = 0`, a limit of the geometric sequence
    have hs0 : s = 0 := by
      rcases mul_eq_zero.1 hzero.symm with h | h
      · exact h
      · exact absurd h ht
    subst hs0
    have hb : Tendsto (fun n : ℕ => b ^ n * t) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).mul_const t
      simpa using h
    have hlim : Tendsto (fun n : ℕ => eLine i (b ^ n * t)) atTop (𝓝 (eLine i 0)) :=
      ((continuous_eLine i).tendsto 0).comp hb
    refine hE.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    simpa using hiter 0 n
  · -- `s ≠ 0`: the semigroup `{a ^ m * b ^ n}` is dense
    have hr : 0 < s / t := by
      rcases mul_pos_iff.1 hpos with h | h
      · exact div_pos h.1 h.2
      · exact div_pos_of_neg_of_neg h.1 h.2
    have htabs : 0 < |t| := abs_pos.2 ht
    -- the approximating sequence
    have hseq : ∀ n : ℕ, ∃ m k : ℕ, |s - a ^ m * b ^ k * t| < |t| * (1 / ((n : ℝ) + 1)) := by
      intro n
      obtain ⟨m, k, hmk⟩ := BerendRankTwo.exists_pow_mul_pow_near ha hb0 hb1 hirr hr
        (ε := 1 / ((n : ℝ) + 1)) (by positivity)
      refine ⟨m, k, ?_⟩
      have heq : s - a ^ m * b ^ k * t = t * (s / t - a ^ m * b ^ k) := by
        rw [mul_sub, mul_div_cancel₀ s ht]
        ring_nf
      rw [heq, abs_mul]
      exact mul_lt_mul_of_pos_left hmk htabs
    choose m k hmk using hseq
    have hbound : Tendsto (fun n : ℕ => |t| * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |t|)
    have hprod : Tendsto (fun n : ℕ => a ^ (m n) * b ^ (k n) * t) atTop (𝓝 s) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbound ε hε
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      have h2 : |t| * (1 / ((n : ℝ) + 1)) < ε := by
        have h3 : |t| * |(n : ℝ) + 1|⁻¹ < ε := by simpa [one_div] using hN n hn
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)] at h3
        simpa [one_div] using h3
      linarith [hmk n]
    have hlim : Tendsto (fun n : ℕ => eLine i (a ^ (m n) * b ^ (k n) * t)) atTop (𝓝 (eLine i s)) :=
      ((continuous_eLine i).tendsto s).comp hprod
    exact hE.mem_of_tendsto hlim (Eventually.of_forall fun n => hiter (m n) (k n))


/-! ## 3. A one-sided coordinate ray in a compact group is two-sided

The content is the standard fact that a closed additive subsemigroup of a compact
additive group is an additive subgroup.  This is what lets the ray lemma of §2 —
which only gives the half-line in the direction of the point found by accumulation —
produce the *whole* coordinate circle in the torus. -/

section SignFlip

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
  [CompactSpace T] [T2Space T]

theorem nsmul_mem_of_closed_add_subsemigroup {K : Set T} (h0 : (0 : T) ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) {x : T} (hx : x ∈ K) :
    ∀ n : ℕ, n • x ∈ K := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul]; exact hadd _ ih _ hx

/-- **A closed additive subsemigroup of a compact additive group is closed under
negation.** -/
theorem neg_mem_of_closed_add_subsemigroup {K : Set T} (hK : IsClosed K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) {x : T} (hx : x ∈ K) : -x ∈ K := by
  -- `0` lies in `K`: the only idempotent of a group is `0`
  obtain ⟨e, heK, hee⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => continuous_id.add continuous_const) K ⟨x, hx⟩ hK.isCompact hadd
  have he0 : e = 0 := by
    have h : e + e = e + 0 := by rw [hee, add_zero]
    exact add_left_cancel h
  have h0 : (0 : T) ∈ K := he0 ▸ heK
  -- the closed subsemigroup generated by `x`
  set F : ℕ+ → T := fun n => (n : ℕ) • x with hF
  have hFS : ∀ n, F n ∈ K := fun n => nsmul_mem_of_closed_add_subsemigroup h0 hadd hx _
  have hSadd : ∀ y ∈ closure (Set.range F), ∀ z ∈ closure (Set.range F),
      y + z ∈ closure (Set.range F) := by
    intro y hy z hz
    have key : ∀ a ∈ Set.range F, ∀ b ∈ closure (Set.range F), a + b ∈ closure (Set.range F) := by
      rintro a ⟨n, rfl⟩ b hb
      have hclosed : IsClosed {b : T | F n + b ∈ closure (Set.range F)} :=
        isClosed_closure.preimage (continuous_const.add continuous_id)
      refine hclosed.closure_subset_iff.2 ?_ hb
      rintro _ ⟨m, rfl⟩
      refine subset_closure ⟨n + m, ?_⟩
      simp only [hF]
      push_cast
      rw [add_nsmul]
    have hclosed : IsClosed {y : T | y + z ∈ closure (Set.range F)} :=
      isClosed_closure.preimage (continuous_id.add continuous_const)
    exact hclosed.closure_subset_iff.2 (fun a ha => key a ha z hz) hy
  -- an idempotent of that closed subsemigroup is `0`
  obtain ⟨e', he'S, he'e'⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => continuous_id.add continuous_const) (closure (Set.range F))
    ⟨F 1, subset_closure ⟨1, rfl⟩⟩ isClosed_closure.isCompact hSadd
  have he'0 : e' = 0 := by
    have h : e' + e' = e' + 0 := by rw [he'e', add_zero]
    exact add_left_cancel h
  have h0S : (0 : T) ∈ closure (Set.range F) := he'0 ▸ he'S
  -- translate by `-x`: the points `n • x` go to `(n - 1) • x`
  have himage : (fun y : T => y - x) '' Set.range F ⊆ K := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℕ) = m + 1 :=
      ⟨(n : ℕ) - 1, (Nat.sub_one_add_one n.ne_zero).symm⟩
    have hsub : F n - x = m • x := by
      simp only [hF, hm, succ_nsmul]
      abel
    show F n - x ∈ K
    rw [hsub]
    exact nsmul_mem_of_closed_add_subsemigroup h0 hadd hx m
  have hcont : Continuous (fun y : T => y - x) := continuous_id.sub continuous_const
  have hmem : (0 : T) - x ∈ closure ((fun y : T => y - x) '' Set.range F) :=
    image_closure_subset_closure_image hcont ⟨0, h0S, rfl⟩
  simpa using hK.closure_subset_iff.2 himage hmem

/-- **A closed set containing a half of a one-parameter subgroup contains all of it.** -/
theorem addMonoidHom_mem_of_mem_Ici {φ : ℝ →+ T} {Y : Set T} (hY : IsClosed Y)
    (h : ∀ s : ℝ, 0 ≤ s → φ s ∈ Y) : ∀ r : ℝ, φ r ∈ Y := by
  set K : Set T := closure (φ '' Set.Ici 0) with hK
  have hKY : K ⊆ Y :=
    closure_minimal (fun y hy => by obtain ⟨s, hs, rfl⟩ := hy; exact h s hs) hY
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := by
    intro a ha b hb
    have key : ∀ a' ∈ φ '' Set.Ici 0, ∀ b' ∈ K, a' + b' ∈ K := by
      rintro a' ⟨s, hs, rfl⟩ b' hb'
      have hclosed : IsClosed {b' : T | φ s + b' ∈ K} :=
        isClosed_closure.preimage (continuous_const.add continuous_id)
      refine hclosed.closure_subset_iff.2 ?_ hb'
      rintro _ ⟨s', hs', rfl⟩
      have hss : 0 ≤ s + s' := by
        have hs0 : (0 : ℝ) ≤ s := Set.mem_Ici.1 hs
        have hs1 : (0 : ℝ) ≤ s' := Set.mem_Ici.1 hs'
        linarith
      show φ s + φ s' ∈ K
      rw [← φ.map_add s s']
      exact subset_closure ⟨s + s', hss, rfl⟩
    have hclosed : IsClosed {a' : T | a' + b ∈ K} :=
      isClosed_closure.preimage (continuous_id.add continuous_const)
    exact hclosed.closure_subset_iff.2 (fun a' ha' => key a' ha' b hb) ha
  intro r
  rcases le_or_gt 0 r with hr | hr
  · exact hKY (subset_closure ⟨r, hr, rfl⟩)
  · have h1 : φ (-r) ∈ K := subset_closure ⟨-r, by simpa using hr.le, rfl⟩
    have h2 : -φ (-r) ∈ K := neg_mem_of_closed_add_subsemigroup isClosed_closure hKadd h1
    have h3 : φ r = -φ (-r) := by
      have := φ.map_neg (-r)
      simpa using this.symm
    rw [h3]
    exact hKY h2

/-- The `s ≤ 0` form of `addMonoidHom_mem_of_mem_Ici`. -/
theorem addMonoidHom_mem_of_mem_Iic {φ : ℝ →+ T} {Y : Set T} (hY : IsClosed Y)
    (h : ∀ s : ℝ, s ≤ 0 → φ s ∈ Y) : ∀ r : ℝ, φ r ∈ Y := by
  let ψ : ℝ →+ T :=
    { toFun := fun s => φ (-s)
      map_zero' := by simp
      map_add' := fun s s' => by
        have hneg : -(s + s') = -s + -s' := by ring
        rw [hneg, φ.map_add] }
  have hψ : ∀ s : ℝ, 0 ≤ s → ψ s ∈ Y := by
    intro s hs
    exact h (-s) (by linarith)
  have hall := addMonoidHom_mem_of_mem_Ici (φ := ψ) hY hψ
  intro r
  have h1 : ψ (-r) ∈ Y := hall (-r)
  simpa [ψ] using h1

end SignFlip

/-! ## 4. Stage I, the `k = 1` branch -/

section Torus

variable {L : AddSubgroup (ι → ℝ)}

/-- The one-parameter subgroup of the torus generated by the `i`-th coordinate line. -/
noncomputable def rayHom (L : AddSubgroup (ι → ℝ)) (i : ι) : ℝ →+ ((ι → ℝ) ⧸ L) where
  toFun s := QuotientAddGroup.mk' L (eLine i s)
  map_zero' := by
    show QuotientAddGroup.mk' L (eLine i 0) = 0
    rw [eLine_zero]
    exact map_zero _
  map_add' s s' := by rw [eLine_add, map_add]

@[simp] theorem rayHom_apply (L : AddSubgroup (ι → ℝ)) (i : ι) (s : ℝ) :
    rayHom L i s = QuotientAddGroup.mk' L (eLine i s) := rfl

/-- **Stage I of Berend's Theorem 2.1, one-dimensional (`k = 1`) branch.**

Let `Y` be a closed subset of the torus `(ι → ℝ) ⧸ L` whose lift is invariant under two
diagonal endomorphisms which at the coordinate `i` multiply by `a > 1` and by
`b ∈ (0, 1)` with `log a / log b` irrational (corrected (B3) read on the multipliers),
and suppose `0` is a non-isolated point of the lift inside the coordinate line
`coord {i}` (this is the output of Berend's Lemmas 4.1-4.3 for a minimal accumulating
coordinate set of cardinality one).  If moreover the coordinate line is dense modulo
`L`, then `Y` is the whole torus.

The conclusion is *not* a difference-set statement: it uses the ray generated by the
accumulating point, which lies in `Y`, and the density of the coordinate line. -/
theorem eq_univ_of_acc_coord [CompactSpace ((ι → ℝ) ⧸ L)] [T2Space ((ι → ℝ) ⧸ L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y)
    {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag lam x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag mu x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {i : ι} (hlam : 1 < lam i) (hmu0 : 0 < mu i) (hmu1 : mu i < 1)
    (hirr : Irrational (Real.log (lam i) / Real.log (mu i)))
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hdense : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Y = univ := by
  classical
  have hEclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage QuotientAddGroup.continuous_mk
  obtain ⟨x, hxE, hxS, hxi⟩ := BerendRankTwo.exists_ne_zero_of_acc hacc
  have hxeq : x = eLine i (x i) := eq_eLine_of_mem_coord hxS
  have hx' : eLine i (x i) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rw [← hxeq]; exact hxE
  -- the half-line in the direction of `x i` is contained in the lift
  have hray : ∀ s : ℝ, 0 ≤ s * (x i) → QuotientAddGroup.mk' L (eLine i s) ∈ Y := fun s hs =>
    eLine_mem_of_mul_nonneg hEclosed hinv1 hinv2 hlam hmu0 hmu1 hirr rfl rfl hxi hx' s hs
  -- both one-sided rays give the full coordinate circle in `Y`
  have hboth : ∀ r : ℝ, QuotientAddGroup.mk' L (eLine i r) ∈ Y := by
    rcases lt_or_gt_of_ne hxi with hneg | hpos
    · have hI : ∀ s : ℝ, s ≤ 0 → rayHom L i s ∈ Y := by
        intro s hs
        rw [rayHom_apply]
        exact hray s (by nlinarith)
      exact fun r => addMonoidHom_mem_of_mem_Iic (φ := rayHom L i) hY hI r
    · have hI : ∀ s : ℝ, 0 ≤ s → rayHom L i s ∈ Y := by
        intro s hs
        rw [rayHom_apply]
        exact hray s (by nlinarith)
      exact fun r => addMonoidHom_mem_of_mem_Ici (φ := rayHom L i) hY hI r
  -- the coordinate line is dense in the torus
  have himage : (QuotientAddGroup.mk' L) '' (BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) ⊆ Y := by
    rintro _ ⟨y, hy, rfl⟩
    rw [eq_eLine_of_mem_coord hy]
    exact hboth (y i)
  have hdense' : Dense ((QuotientAddGroup.mk' L) ''
      (BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) :=
    QuotientAddGroup.dense_image_mk.2 hdense
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense'.closure_eq]
  exact closure_minimal himage hY

/-- **Stage I, `k = 1` branch, with the multipliers read off a common weight vector.**

This is the form in which `BerendRate.exists_common_rate` delivers the output of Berend's
Lemma 4.4: at the coordinate `i` the two family members multiply by `c ^ w i` and
`d ^ w i`, with `c > 1 > d > 0` multiplicatively independent (corrected (B3)). -/
theorem eq_univ_of_acc_coord_of_weights [CompactSpace ((ι → ℝ) ⧸ L)]
    [T2Space ((ι → ℝ) ⧸ L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y)
    {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag lam x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag mu x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {i : ι} {c d : ℝ} {w : ℕ} (hw : 0 < w) (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1)
    (hind : ∀ m n : ℤ, c ^ m = d ^ n → m = 0 ∧ n = 0)
    (hlam : lam i = c ^ w) (hmu : mu i = d ^ w)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hdense : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Y = univ := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcp : 1 < c ^ w := one_lt_pow₀ hc hw.ne'
  have hdp0 : 0 < d ^ w := pow_pos hd0 w
  have hdp1 : d ^ w < 1 := pow_lt_one₀ hd0.le hd1 hw.ne'
  have hind' : ∀ m n : ℤ, (c ^ w) ^ m = (d ^ w) ^ n → m = 0 ∧ n = 0 := by
    intro m n hmn
    refine BerendModulus.mulIndep_pow hind hw.ne' m n ?_
    simpa [zpow_natCast] using hmn
  refine eq_univ_of_acc_coord (L := L) (Y := Y) (lam := lam) (mu := mu) (i := i)
    hY hinv1 hinv2 ?_ ?_ ?_ ?_ hacc hdense
  · rw [hlam]; exact hcp
  · rw [hmu]; exact hdp0
  · rw [hmu]; exact hdp1
  · rw [hlam, hmu]
    exact BerendRankTwo.irrational_log_div_log_of_indep (pow_pos hc0 w) hdp0 hind'

/-- **Stage I, `k = 1` branch, assembled from the torus.**

This is the interface of the branch: the only input beyond the density and
expanding/contracting-pair hypotheses is `hsingle`, which says that *every* minimal
coordinate set at which the lift accumulates at `0` is a singleton — i.e. that the
multi-coordinate alternative of Berend's Lemma 4.4 does not occur.  Under that input the
branch gives `Y = univ`, with no difference-set detour.

`hsingle` is exactly the hypothesis that the conformal/common-rate branch has to
contradict, and `BerendSec4.dichotomy` plus `BerendRate.exists_common_rate` are the tools
available for that on the other side. -/
theorem eq_univ_of_zero_nonisolated_of_singleton {κ : Type*} {f : κ → ι → ℝ}
    [CompactSpace ((ι → ℝ) ⧸ L)] [T2Space ((ι → ℝ) ⧸ L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y)
    (hacc0 : (0 : (ι → ℝ) ⧸ L) ∈ closure (Y \ {0}))
    (hinv : ∀ (j : κ) (x : ι → ℝ), x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y →
      BerendSec4.diag (f j) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hpair : ∀ i : ι, ∃ j j' : κ, 1 < f j i ∧ 0 < f j' i ∧ f j' i < 1 ∧
      Irrational (Real.log (f j i) / Real.log (f j' i)))
    (hdense : ∀ i : ι, Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) +
      (L : Set (ι → ℝ))))
    (hsingle : ∀ S : Finset ι, BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) S →
      (∀ S' : Finset ι, S' ⊂ S → ¬ BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) S') →
      S.card = 1) :
    Y = univ := by
  have haccuniv : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) Finset.univ :=
    BerendCone.acc_preimage_of_zero_nonisolated hacc0
  obtain ⟨S, hSacc, hSmin⟩ := BerendSec4.exists_minimal_acc haccuniv
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (hsingle S hSacc hSmin)
  obtain ⟨j, j', hij, h0, h1, hirr⟩ := hpair i
  exact eq_univ_of_acc_coord hY (hinv j) (hinv j') hij h0 h1 hirr hSacc (hdense i)

end Torus

end BerendStageILine
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendStageILine.eLine_mem_of_mul_nonneg
#print axioms CubicTwoStage.BerendStageILine.neg_mem_of_closed_add_subsemigroup
#print axioms CubicTwoStage.BerendStageILine.addMonoidHom_mem_of_mem_Ici
#print axioms CubicTwoStage.BerendStageILine.addMonoidHom_mem_of_mem_Iic
#print axioms CubicTwoStage.BerendStageILine.eq_univ_of_acc_coord
#print axioms CubicTwoStage.BerendStageILine.eq_univ_of_acc_coord_of_weights
#print axioms CubicTwoStage.BerendStageILine.eq_univ_of_zero_nonisolated_of_singleton
