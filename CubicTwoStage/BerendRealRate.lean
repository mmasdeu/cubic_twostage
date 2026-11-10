/-
# Stage I with real exponents: the radial flow at the logarithmic rate

`CubicTwoStage/BerendRate.lean` (Berend's Lemma 4.4) produces *real*
proportionality of the logarithmic growth-rate vectors on a minimal accumulating
coordinate set: `Real.log |nu j| = t * Real.log |mu j|` for a single `t < 0`.
`CubicTwoStage/BerendRadialFull.lean` turns invariance under two weighted
dilations into invariance under the whole radial flow and then into `E = univ`,
but its weight vector is `w : ι → ℕ`.

This module removes the integrality.  It redoes the flow limit, the slab
argument and the assembled Stage I theorem with a **real** exponent vector
`v : ι → ℝ`, and shows that a pair of dilations `diag (c ^ v)`, `diag (d ^ v)`
with `c > 1 > d > 0` multiplicatively independent generates the flow
`s ↦ diag (s ^ v)` (`s > 0`).  The integer-weight theorems of
`BerendModulus`/`BerendRadialFull` are the special case `v = w`, `c ^ (w i)`.

The point of the generalisation is that the exponents produced by Lemma 4.4 are
logarithms of eigenvalues, so they are real; nothing in the argument below uses
more than `s ↦ s ^ (v i)` being continuous on `(0, ∞)` with the right limits at
`0`.

The file also records the hypothesis shape that is *not* yet discharged (and is
not a bookkeeping matter): the flow fixes the complement of its support, so the
theorem applies to dilations that are the identity off `S`.  For the project's
family no member has that shape, and the two density hypotheses are what an
application on the full torus has to supply.  What is *unconditionally* proved
here is everything after that: the flow, its collapse at `s → 0`, the slab over
the complement, `E = univ`, the consumer form with signed real multipliers, and
the instance of `BerendDichotomy.ZeroNonisolatedFull` for the pair.

Direction d6 of swarm `smw8dyr2n` (member m4).  Axiom free: the `#print axioms`
audit at the end reports only `propext`, `Classical.choice` and `Quot.sound`.
-/
import CubicTwoStage.BerendRadialFull
import CubicTwoStage.BerendDichotomy

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendRealRate

open BerendRadialFull BerendModulus BerendSec4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The limit `s ^ v → 0` as `s → 0⁺` for `v > 0` -/

/-- `s ↦ s ^ v` tends to `0` as `s → 0⁺` when `v > 0` (`Real.rpow`). -/
theorem tendsto_rpow_zero_right {q : ℝ} (hq : 0 < q) :
    Tendsto (fun s : ℝ => s ^ q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => s ^ q) (𝓝 (0 : ℝ)) (𝓝 (0 ^ q)) :=
    Real.continuousAt_rpow_const 0 q (Or.inr hq.le)
  rw [Real.zero_rpow hq.ne'] at h1
  exact h1.mono_left nhdsWithin_le_nhds

/-! ## 2. The radial flow collapses to `0` on its support -/

section Collapse

variable {X : Set (ι → ℝ)} {S : Set ι} {v : ι → ℝ}

/-- **The radial flow with real exponents collapses to `0` on its support.** -/
theorem flow_limit_mem_rpow (hX : IsClosed X)
    (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    (hflow : ∀ x ∈ X, ∀ s : ℝ, 0 < s → (fun i => s ^ (v i) * x i) ∈ X)
    {x : ι → ℝ} (hx : x ∈ X) : collapse S x ∈ X := by
  classical
  refine hX.mem_of_tendsto (f := fun s : ℝ => fun i => s ^ (v i) * x i)
    (b := 𝓝[>] (0 : ℝ)) ?_ ?_
  · rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i ∈ S
    · have hpos : 0 < v i := hvS i hi
      have h2 : Tendsto (fun s : ℝ => s ^ (v i) * x i) (𝓝[>] (0 : ℝ)) (𝓝 (0 * x i)) :=
        (tendsto_rpow_zero_right hpos).mul_const (x i)
      have h3 : (0 : ℝ) * x i = collapse S x i := by
        rw [collapse_apply_of_mem hi, zero_mul]
      rw [h3] at h2
      exact h2
    · have hz : v i = 0 := hv0 i hi
      have hconst : ∀ s : ℝ, s ^ (v i) * x i = x i := by
        intro s
        rw [hz, Real.rpow_zero, one_mul]
      have : Tendsto (fun s : ℝ => s ^ (v i) * x i) (𝓝[>] (0 : ℝ)) (𝓝 (x i)) := by
        simpa only [hconst] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => x i) (𝓝[>] (0 : ℝ)) (𝓝 (x i)))
      rwa [collapse_apply_of_not_mem hi]
  · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ))] with s hs
    exact hflow x hx s hs

end Collapse

/-! ## 3. The slab over the complement of the support -/

section Slab

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)} {S : Set ι} {v : ι → ℝ}

/-- **The slab, real exponents.**  Every point vanishing on the support `S` of the
flow lies in the closed flow-invariant set: the flow pushes the `S`-coordinates
to `0` while the complementary coordinates can be matched by lattice vectors
(density of the projection of `L` to `Sᶜ`). -/
theorem slab_mem_rpow (hE : IsClosed E)
    (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    (hflow : ∀ x ∈ prec L E, ∀ s : ℝ, 0 < s →
      (fun i => s ^ (v i) * x i) ∈ prec L E)
    (hden : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |z i - ℓ i| < ε)
    (hne : (prec L E).Nonempty) {y : ι → ℝ} (hy : ∀ i ∈ S, y i = 0) :
    y ∈ prec L E := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hcollapse' : ∀ ℓ ∈ L, collapse S (x + ℓ) ∈ prec L E := by
    intro ℓ hℓ
    exact flow_limit_mem_rpow (isClosed_prec hE) hvS hv0 hflow (prec_add_mem hx hℓ)
  rw [← (isClosed_prec hE).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ℓ, hℓ, hclose⟩ := hden (fun i => y i - collapse S x i) ε hε
  refine ⟨collapse S (x + ℓ), hcollapse' ℓ hℓ, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq]
  by_cases hi : i ∈ S
  · rw [hy i hi, collapse_apply_of_mem hi, sub_zero, abs_zero]
    exact hε
  · rw [collapse_apply_of_not_mem hi, Pi.add_apply]
    have h := hclose i hi
    rw [collapse_apply_of_not_mem hi] at h
    have heq : y i - (x i + ℓ i) = y i - x i - ℓ i := by ring
    rw [heq]
    exact h

end Slab

/-! ## 4. Stage I under a real-weight radial flow -/

section Main

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)} {S : Set ι} {v : ι → ℝ}

/-- **Stage I, real-weight radial-flow form.**  A closed nonempty set of the torus
whose lift carries the whole flow `s ↦ diag (s ^ v)` (`s > 0`) is everything,
provided the projections of `L` to the support of `v` and to its complement are
both dense. -/
theorem eq_univ_of_flow_rpow (hE : IsClosed E) (hne : E.Nonempty)
    (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    (hflow : ∀ x ∈ prec L E, ∀ s : ℝ, 0 < s →
      (fun i => s ^ (v i) * x i) ∈ prec L E)
    (hdenS : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |z i - ℓ i| < ε)
    (hdenSc : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |z i - ℓ i| < ε) :
    E = univ := by
  classical
  have hne' : (prec L E).Nonempty := prec_nonempty hne
  have hprec : prec L E = univ := by
    refine eq_univ_of_forall fun y => ?_
    rw [← (isClosed_prec hE).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨ℓ, hℓ, hclose⟩ := hdenS y ε hε
    have hslab : (fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) ∈ prec L E := by
      refine slab_mem_rpow hE hvS hv0 hflow hdenSc hne' (fun i hi => ?_)
      simp [hi]
    have hadd : (fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ ∈ prec L E :=
      prec_add_mem hslab hℓ
    refine ⟨(fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ, hadd, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    by_cases hi : i ∈ S
    · have h1 : ((fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ) i = ℓ i := by
        simp [hi]
      rw [h1]
      exact hclose i hi
    · have h1 : ((fun i => if i ∈ S then (0 : ℝ) else y i - ℓ i) + ℓ) i = y i := by
        simp [hi]
      rw [h1, sub_self, abs_zero]
      exact hε
  exact prec_eq_univ_iff.mp hprec

end Main

/-! ## 5. The flow generated by a multiplicatively independent pair of
real-weight dilations -/

section Pair

variable {E : Set (ι → ℝ)} {v : ι → ℝ}

/-- Iterates of a real-weight dilation: the `k`-th iterate multiplies the `i`-th
coordinate by `u ^ (k * v i)`. -/
theorem iterate_diag_rpow (u : ℝ) (hu : 0 < u) (v : ι → ℝ) (k : ℕ) (x : ι → ℝ) :
    (BerendSec4.diag (fun i => u ^ (v i)))^[k] x = fun i => u ^ ((k : ℝ) * v i) * x i := by
  induction k with
  | zero =>
      funext i
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i
      rw [BerendSec4.diag_apply, ← mul_assoc, ← Real.rpow_add hu,
        show v i + (k : ℝ) * v i = ((k + 1 : ℕ) : ℝ) * v i from by push_cast; ring]

/-- Membership of the iterates. -/
theorem iterate_mem_of_invariant_rpow {u : ℝ} (hu : 0 < u) {v : ι → ℝ}
    (hinv : ∀ x ∈ E, BerendSec4.diag (fun i => u ^ (v i)) x ∈ E)
    (k : ℕ) {x : ι → ℝ} (hx : x ∈ E) :
    (fun i => u ^ ((k : ℝ) * v i) * x i) ∈ E := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      have hmem := hinv _ ih
      have hfun : BerendSec4.diag (fun i => u ^ (v i))
            (fun i => u ^ ((k : ℝ) * v i) * x i)
          = fun i => u ^ (((k + 1 : ℕ) : ℝ) * v i) * x i := by
        funext i
        rw [BerendSec4.diag_apply, ← mul_assoc, ← Real.rpow_add hu,
          show v i + (k : ℝ) * v i = ((k + 1 : ℕ) : ℝ) * v i from by push_cast; ring]
      rwa [hfun] at hmem

end Pair
/-! ## 6. Two multiplicatively independent real-weight dilations generate the flow -/

section Radial

variable {E : Set (ι → ℝ)} {v : ι → ℝ}

/-- **The radial flow from a multiplicatively independent pair of real-weight
dilations.**  If `E` is closed and invariant under `diag (c ^ v)` and
`diag (d ^ v)` with `c > 1 > d > 0` and `log c / log d` irrational, then `E`
carries the whole positive flow `s ↦ diag (s ^ v)`.

This is `BerendModulus.radial_flow_mem` with the integrality of the weight
vector removed, so that it applies to the real logarithmic rates produced by
`BerendRate.exists_common_rate`. -/
theorem radial_flow_mem_rpow (hE : IsClosed E) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hirr : Irrational (Real.log c / Real.log d))
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (v i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (v i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) {s : ℝ} (hs : 0 < s) :
    (fun i => s ^ (v i) * x i) ∈ E := by
  classical
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  -- the semigroup orbit: every `(c ^ m * d ^ n) ^ v * x` is in `E`
  have hmem : ∀ m n : ℕ, (fun i => (c ^ m * d ^ n) ^ (v i) * x i) ∈ E := by
    intro m n
    have h1 : (fun i => c ^ ((m : ℝ) * v i) * x i) ∈ E :=
      iterate_mem_of_invariant_rpow hc0 hinv1 m hx
    have h2 : (fun i => d ^ ((n : ℝ) * v i) * (c ^ ((m : ℝ) * v i) * x i)) ∈ E :=
      iterate_mem_of_invariant_rpow hd0 hinv2 n h1
    have hfun : (fun i => d ^ ((n : ℝ) * v i) * (c ^ ((m : ℝ) * v i) * x i))
        = fun i => (c ^ m * d ^ n) ^ (v i) * x i := by
      funext i
      rw [Real.mul_rpow (pow_nonneg hc0.le m) (pow_nonneg hd0.le n),
        ← Real.rpow_natCast_mul hc0.le m (v i), ← Real.rpow_natCast_mul hd0.le n (v i)]
      ring
    rwa [hfun] at h2
  -- a sequence of radial factors converging to `s`
  have hseq : ∀ k : ℕ, ∃ m n : ℕ, |s - c ^ m * d ^ n| < 1 / ((k : ℝ) + 1) :=
    fun k => BerendRankTwo.exists_pow_mul_pow_near hc hd0 hd1 hirr hs (by positivity)
  choose m n hmn using hseq
  have htend : Tendsto (fun k : ℕ => c ^ (m k) * d ^ (n k)) atTop (𝓝 s) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    have hKε : 1 < (K : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hK
      linarith
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have h1 : |s - c ^ (m k) * d ^ (n k)| < 1 / ((k : ℝ) + 1) := hmn k
    have hk' : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith
    have h3 : 1 / ((K : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- continuity of the radial action at `s > 0`
  have hcont : Tendsto (fun t : ℝ => fun i => t ^ (v i) * x i) (𝓝 s)
      (𝓝 (fun i => s ^ (v i) * x i)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact ((Real.continuousAt_rpow_const s (v i) (Or.inl hs.ne')).mul_const (x i))
  exact hE.mem_of_tendsto (hcont.comp htend)
    (Filter.Eventually.of_forall fun k => hmem (m k) (n k))

/-- **The radial flow from corrected (B3), real-weight form**: the arithmetic
hypothesis is exponent independence of the two multipliers. -/
theorem radial_flow_mem_of_indep_rpow (hE : IsClosed E) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (v i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (v i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) {s : ℝ} (hs : 0 < s) :
    (fun i => s ^ (v i) * x i) ∈ E :=
  radial_flow_mem_rpow hE hc hd0 hd1
    (BerendRankTwo.irrational_log_div_log_of_indep (lt_trans zero_lt_one hc) hd0 hind)
    hinv1 hinv2 hx hs

/-- The whole positive ray through a point of `E` lies in `E`. -/
theorem radial_ray_subset_rpow (hE : IsClosed E) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (v i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (v i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) :
    (fun s : ℝ => fun i => s ^ (v i) * x i) '' (Set.Ioi 0) ⊆ E := by
  rintro _ ⟨s, hs, rfl⟩
  exact radial_flow_mem_of_indep_rpow hE hc hd0 hd1 hind hinv1 hinv2 hx hs

end Radial

/-! ## 7. Stage I from the two dilations, real weights -/

section Assembled

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)} {S : Set ι} {v : ι → ℝ}

/-- **Stage I from a pair of real-weight dilations.**  `BerendRadialStageI`'s
unconditional Stage I with the integer weight vector replaced by a real exponent
vector: the hypotheses are those left over after Berend's Lemma 4.4 has been
applied (a common real rate vector on the minimal accumulating coordinate set,
one expanding and one contracting multiplier). -/
theorem eq_univ_of_radial_rpow (hE : IsClosed E) (hne : E.Nonempty)
    (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => c ^ (v i)) x ∈ prec L E)
    (hinv2 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => d ^ (v i)) x ∈ prec L E)
    (hdenS : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |z i - ℓ i| < ε)
    (hdenSc : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |z i - ℓ i| < ε) :
    E = univ := by
  refine eq_univ_of_flow_rpow hE hne hvS hv0 ?_ hdenS hdenSc
  intro x hx s hs
  exact radial_flow_mem_of_indep_rpow (isClosed_prec hE) hc hd0 hd1 hind hinv1 hinv2 hx hs

end Assembled

/-! ## 8. Consumer form: arbitrary real multipliers with proportional squared moduli -/

section Squared

variable {L : AddSubgroup (ι → ℝ)} {E : Set ((ι → ℝ) ⧸ L)} {S : Set ι} {v : ι → ℝ}

/-- Squaring a diagonal map: `diag mu ∘ diag mu = diag (fun i => mu i ^ 2)`. -/
theorem diag_comp_diag (mu : ι → ℝ) (x : ι → ℝ) :
    BerendSec4.diag mu (BerendSec4.diag mu x) = BerendSec4.diag (fun i => mu i ^ 2) x := by
  funext i
  simp only [BerendSec4.diag_apply, pow_two]
  ring

/-- **Stage I from two dilations given by arbitrary real multipliers whose squares
are proportional weight dilations.**

Nothing is assumed about the signs of `mu` and `nu`: only their squares have to
be the two real-weight dilations `c ^ v` and `d ^ v` with `c > 1 > d > 0`
multiplicatively independent.  This is the shape in which Berend's Lemma 4.4
supplies the data (`nu j ^ 2 = (mu j ^ 2) ^ t` with `t < 0`, i.e.
`Real.log (nu j ^ 2) = t * Real.log (mu j ^ 2)`), once the common weight is
written out. -/
theorem eq_univ_of_sq_rpow (hE : IsClosed E) (hne : E.Nonempty)
    (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    {mu nu : ι → ℝ} (hmu : ∀ i, mu i ^ 2 = c ^ (v i)) (hnu : ∀ i, nu i ^ 2 = d ^ (v i))
    (hinv1 : ∀ x ∈ prec L E, BerendSec4.diag mu x ∈ prec L E)
    (hinv2 : ∀ x ∈ prec L E, BerendSec4.diag nu x ∈ prec L E)
    (hdenS : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |z i - ℓ i| < ε)
    (hdenSc : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |z i - ℓ i| < ε) :
    E = univ := by
  have hc1 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => c ^ (v i)) x ∈ prec L E := by
    intro x hx
    have h := hinv1 _ (hinv1 x hx)
    have hfun : BerendSec4.diag mu (BerendSec4.diag mu x)
        = BerendSec4.diag (fun i => c ^ (v i)) x := by
      rw [diag_comp_diag]
      funext i
      simp only [BerendSec4.diag_apply]
      rw [hmu i]
    rwa [hfun] at h
  have hc2 : ∀ x ∈ prec L E, BerendSec4.diag (fun i => d ^ (v i)) x ∈ prec L E := by
    intro x hx
    have h := hinv2 _ (hinv2 x hx)
    have hfun : BerendSec4.diag nu (BerendSec4.diag nu x)
        = BerendSec4.diag (fun i => d ^ (v i)) x := by
      rw [diag_comp_diag]
      funext i
      simp only [BerendSec4.diag_apply]
      rw [hnu i]
    rwa [hfun] at h
  exact eq_univ_of_radial_rpow hE hne hvS hv0 hc hd0 hd1 hind hc1 hc2 hdenS hdenSc

end Squared

/-! ## 9. The Stage I proposition for the pair of real-weight dilations -/

section StageI

variable {L : AddSubgroup (ι → ℝ)}

/-- The torus endomorphism induced by the real-weight dilation `diag (c ^ v)`. -/
noncomputable def dilEndR (c : ℝ) (v : ι → ℝ)
    (h : ∀ g ∈ L, BerendSec4.diag (fun i => c ^ (v i)) g ∈ L) :
    (ι → ℝ) ⧸ L →+ (ι → ℝ) ⧸ L :=
  QuotientAddGroup.map L L ((BerendSec4.diag (fun i => c ^ (v i))).toAddMonoidHom)
    fun _ hg => h _ hg

/-- `dilEndR` on classes. -/
theorem dilEndR_mk (c : ℝ) (v : ι → ℝ)
    (h : ∀ g ∈ L, BerendSec4.diag (fun i => c ^ (v i)) g ∈ L) (x : ι → ℝ) :
    dilEndR (L := L) c v h (QuotientAddGroup.mk' L x)
      = QuotientAddGroup.mk' L (BerendSec4.diag (fun i => c ^ (v i)) x) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply]
  exact QuotientAddGroup.map_mk L L _ _ x

/-- Invariance of a torus set under `dilEndR` is invariance of its lift. -/
theorem preimage_invariant_of_image_subset_dilEndR (c : ℝ) (v : ι → ℝ)
    (h : ∀ g ∈ L, BerendSec4.diag (fun i => c ^ (v i)) g ∈ L)
    {E : Set ((ι → ℝ) ⧸ L)} (hinv : dilEndR (L := L) c v h '' E ⊆ E)
    {x : ι → ℝ} (hx : x ∈ prec L E) :
    BerendSec4.diag (fun i => c ^ (v i)) x ∈ prec L E := by
  have hmem : dilEndR (L := L) c v h (QuotientAddGroup.mk' L x) ∈ E := hinv ⟨_, hx, rfl⟩
  rwa [dilEndR_mk] at hmem

/-- **Stage I (`BerendDichotomy.ZeroNonisolatedFull`) for a pair of real-weight
torus dilations `{diag (c ^ v), diag (d ^ v)}`** with `c > 1 > d > 0`
multiplicatively independent and both projections of the lattice dense.

The conclusion is *stronger* than Stage I asks for: only nonemptiness and
closedness of the invariant set are used. -/
theorem zeroNonisolatedFull_dil_pair_rpow
    {S : Set ι} {v : ι → ℝ} (hvS : ∀ i ∈ S, 0 < v i) (hv0 : ∀ i ∉ S, v i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hpresc : ∀ g ∈ L, BerendSec4.diag (fun i => c ^ (v i)) g ∈ L)
    (hpresd : ∀ g ∈ L, BerendSec4.diag (fun i => d ^ (v i)) g ∈ L)
    (hdenS : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∈ S → |z i - ℓ i| < ε)
    (hdenSc : ∀ (z : ι → ℝ) (ε : ℝ), 0 < ε → ∃ ℓ ∈ L, ∀ i, i ∉ S → |z i - ℓ i| < ε) :
    BerendDichotomy.ZeroNonisolatedFull (fun b : Bool =>
      if b then dilEndR (L := L) c v hpresc else dilEndR (L := L) d v hpresd) := by
  intro E hE hne _hacc hinv
  exact eq_univ_of_radial_rpow hE hne hvS hv0 hc hd0 hd1 hind
    (fun x hx => preimage_invariant_of_image_subset_dilEndR c v hpresc
      (by simpa using hinv true) hx)
    (fun x hx => preimage_invariant_of_image_subset_dilEndR d v hpresd
      (by simpa using hinv false) hx)
    hdenS hdenSc

end StageI

/-! ## 10. Difference-set form at real rates -/

section DiffSet

variable {E : Set (ι → ℝ)} {i : ι} {c d v : ℝ}

/-- **Powers of multiplicatively independent reals are multiplicatively
independent**: `MulIndep c d → MulIndep (c ^ v) (d ^ v)` for `v ≠ 0`. -/
theorem mulIndep_rpow {c d v : ℝ} (hc : 0 < c) (hd : 0 < d) (hv : v ≠ 0)
    (hind : MulIndep c d) : MulIndep (c ^ v) (d ^ v) := by
  intro m n hmn
  have h1 : c ^ (v * (m : ℝ)) = d ^ (v * (n : ℝ)) := by
    rw [Real.rpow_mul hc.le v (m : ℝ), Real.rpow_mul hd.le v (n : ℝ),
      Real.rpow_intCast (c ^ v) m, Real.rpow_intCast (d ^ v) n]
    exact hmn
  have h2 : (m : ℝ) * Real.log c = (n : ℝ) * Real.log d := by
    have h := congrArg Real.log h1
    rw [Real.log_rpow hc, Real.log_rpow hd] at h
    have h' : v * ((m : ℝ) * Real.log c) = v * ((n : ℝ) * Real.log d) := by linarith
    exact mul_left_cancel₀ hv h'
  have h3 : c ^ m = d ^ n := by
    rw [← Real.rpow_intCast c m, ← Real.rpow_intCast d n,
      Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hd, mul_comm (Real.log c),
      mul_comm (Real.log d), h2]
  exact hind m n h3

/-- **Stage C, `k = 1`, real-rate form.**  `BerendModulus.coord_subset_sub_of_weights`
with the integer exponent `w` replaced by a real exponent `v > 0`: if `E` is closed
and invariant under two diagonal maps whose multipliers at the coordinate `i` are
`c ^ v`, `d ^ v` with `c > 1 > d > 0` multiplicatively independent, and `E`
accumulates at `0` on the coordinate line `{i}`, then the whole line lies in
`E - E`. -/
theorem coord_subset_sub_of_weights_rpow {E : Set (ι → ℝ)} (hE : IsClosed E)
    {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ E, BerendSec4.diag lam x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag mu x ∈ E)
    {i : ι} {c d v : ℝ} (hv : 0 < v)
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hlam : lam i = c ^ v) (hmu : mu i = d ^ v)
    (hacc : BerendSec4.Acc E {i}) :
    ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) ⊆ E - E := by
  refine BerendRankTwo.acc_coord_subset_sub hE hinv1 hinv2 ?_ ?_ ?_ ?_ hacc
  · rw [hlam]
    exact Real.one_lt_rpow hc hv
  · rw [hmu]
    exact Real.rpow_pos_of_pos hd0 v
  · rw [hmu]
    exact Real.rpow_lt_one hd0.le hd1 hv
  · rw [hlam, hmu]
    exact mulIndep_rpow (lt_trans zero_lt_one hc) hd0 hv.ne' hind

end DiffSet

/-- **Stage C, `k = 1`, real-rate difference-set form on the torus.**  The
real-exponent version of `BerendModulus.torus_sub_eq_univ_of_acc_coord`: `Y` is
closed, its lift is invariant under the two diagonal maps and accumulates at `0`
on the coordinate line `{i}`, and that line projects densely into the torus;
then `Y - Y` is the whole torus. -/
theorem torus_sub_eq_univ_of_acc_coord_rpow {L : AddSubgroup (ι → ℝ)}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) {lam mu : ι → ℝ} {i : ι}
    {c d v : ℝ} (hv : 0 < v)
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag lam x ∈
      (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag mu x ∈
      (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hlam : lam i = c ^ v) (hmu : mu i = d ^ v)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hdense : DenseRange (fun t : ℝ =>
      QuotientAddGroup.mk' L (fun j => if j = i then t else 0))) :
    Y - Y = univ := by
  classical
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set (ι → ℝ)) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set (ι → ℝ)) := hLclosed
  haveI : T2Space ((ι → ℝ) ⧸ L) := inferInstance
  have _hcomp : CompactSpace ((ι → ℝ) ⧸ L) := compact_quotient_of_isZLattice L
  have hline : ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) ⊆
      ((QuotientAddGroup.mk' L) ⁻¹' Y) - ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    coord_subset_sub_of_weights_rpow (hY.preimage QuotientAddGroup.continuous_mk)
      hinv1 hinv2 hv hc hd0 hd1 hind hlam hmu hacc
  have hsat := coord_add_lattice_subset_sub (lSaturated_preimage L Y) hline
  have hrange : Set.range (fun t : ℝ =>
      QuotientAddGroup.mk' L (fun j => if j = i then t else 0)) ⊆ Y - Y := by
    rintro _ ⟨t, rfl⟩
    have hmem : (t • e i : ι → ℝ) ∈ ((QuotientAddGroup.mk' L) ⁻¹' Y) -
        ((QuotientAddGroup.mk' L) ⁻¹' Y) := by
      have h := hsat (t • e i) (Submodule.smul_mem _ t (e_mem_coord i)) 0 L.zero_mem
      simpa using h
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hmem
    rw [Set.mem_preimage] at ha hb
    have hdiff : (QuotientAddGroup.mk' L) a - (QuotientAddGroup.mk' L) b =
        (QuotientAddGroup.mk' L) (fun j => if j = i then t else 0) := by
      rw [← map_sub, hab, smul_e]
    change (QuotientAddGroup.mk' L) (fun j => if j = i then t else 0) ∈ Y - Y
    rw [← hdiff]
    exact Set.sub_mem_sub ha hb
  have hclosed : IsClosed (Y - Y) := BerendMinimal.isClosed_sub hY
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense.closure_range]
  exact closure_minimal hrange hclosed

/-! ## 11. Axiom audit -/

#print axioms CubicTwoStage.BerendRealRate.tendsto_rpow_zero_right
#print axioms CubicTwoStage.BerendRealRate.flow_limit_mem_rpow
#print axioms CubicTwoStage.BerendRealRate.slab_mem_rpow
#print axioms CubicTwoStage.BerendRealRate.eq_univ_of_flow_rpow
#print axioms CubicTwoStage.BerendRealRate.radial_flow_mem_rpow
#print axioms CubicTwoStage.BerendRealRate.eq_univ_of_radial_rpow
#print axioms CubicTwoStage.BerendRealRate.eq_univ_of_sq_rpow
#print axioms CubicTwoStage.BerendRealRate.zeroNonisolatedFull_dil_pair_rpow
#print axioms CubicTwoStage.BerendRealRate.mulIndep_rpow
#print axioms CubicTwoStage.BerendRealRate.coord_subset_sub_of_weights_rpow
#print axioms CubicTwoStage.BerendRealRate.torus_sub_eq_univ_of_acc_coord_rpow

end BerendRealRate
end CubicTwoStage
