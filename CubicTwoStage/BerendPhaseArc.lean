/-
# Stage I, planar branch: the compact arc with *nonnegative* powers only

Integration note: swarm direction `smw9bimdc/d3` was rejected as a solution of
the normalized arc-placement problem.  This file is integrated for its verified
semigroup, modulus-one circle, density helpers, and counterexamples.  The
ordinary exponential flow in §12 is not an arc placed in an invariant lift;
`PhaseDenseSemi` remains an independent conditional input.  See the final
sections and `BEREND_PROOF_PLAN.md` for the unresolved boundary.

Swarm `smw9bimdc`, member `m1`, direction `d3` (Berend Lemma 4.5, compact
phase-vector arc).

## Why this file exists

`CubicTwoStage.BerendPlanarArc` (swarm `smw97otfd`) contains the analytic skeleton
of Berend's Lemma 4.5 and the `B3 → lattice-phase non-degeneracy` step
`pair_latticePhase_nondeg`.  Its compact-arc lemmas, however, are stated for a set
`S ⊆ ℂ*` closed under multiplication **and inversion**
(`unitCircle_subset_closure_of_mem`, and through it
`unitCircle_subset_closure_zpow`, `cplxPlane_subset_of_multiplier_data`,
`cplxPlane_subset_of_pair`).  The family of the canonical unit–prime model is
indexed by `𝒪ˣ × ℕ`: the unit part is a group, but the prime part is only a
**semigroup** (`π^k`, `k : ℕ`).  Inverting the prime is not an operation of the
torus action, and the plan forbids it ("no inverse prime indices", "no
invertibility of prime on `L`").  So those arc lemmas cannot be applied to the
actual family as they stand.

This module removes that obstruction for the `|λ| = 1` branch of Berend's
Lemma 4.5:

* **§1** the closure of the *nonnegative* powers of a unit complex number is
  already the whole unit circle (`unitCircle_subset_closure_range_pow`): a compact
  subsemigroup of the circle is a subgroup, so `ℕ`-powers suffice;
* **§2** consequently a multiplicative *semigroup* `S` containing `1` and a
  unit-modulus element of infinite order has `S¹ ⊆ closure S`
  (`unitCircle_subset_closure_semigroup`);
* **§3** with corrected `(B3)` this turns a nontrivial lattice combination of
  modulus one into the circle for the *nonnegative* multiplier semigroup
  `{c ^ l * d ^ k | l : ℤ, k : ℕ}`
  (`unitCircle_subset_closure_multSemigroup_of_modulus_one`), and hence into the
  full circle `{ofCplx (μ * z₀) | ‖μ‖ = 1}` inside a closed invariant `E ⊆ Pt`
  (`circle_ofCplx_of_modulus_one`);
* **§4** the exact modulus dichotomy that makes the case split of Berend's
  Lemma 4.5 usable: a nontrivial modulus-one combination exists **iff** the ratio
  of the log-moduli is rational (`exists_modulus_one_of_rat_log`,
  `irrational_log_of_no_modulus_one`);
* **§5** the explicit one-parameter arc `t ↦ e^{2πi t ξ}` in Berend's real
  parameter, inside the closure of the nonnegative powers and injective for
  irrational `ξ` (`range_phaseArc_subset_closure_range_pow`, `phaseArc_injective`).

No `sorry`, no `axiom`, no new hypothesis posing as the conclusion.  The
`#print axioms` block at the end audits every declaration.

## What is *not* proved here (and must not be confused with the above)

The other branch of Lemma 4.5 — dense log-moduli, where no modulus-one
combination exists — still requires non-torsion of the *lattice phase vector* in
Berend's normalised compact group, and that is **not** implied by corrected
`(B3)`: `pair_latticePhase_nondeg` says that every nontrivial integer combination
either has nonzero log-modulus or non-integral phase, which is vacuous in the
dense-modulus case, where the first alternative always holds.  Producing the arc
there needs Berend's `§4.1–4.4` (growth-rate proportionality) plus the closure of
the normalised phase lattice; §5 below proves the arc only for the phase
coordinate of a single unit-modulus multiplier.
-/
import CubicTwoStage.BerendPlanarArc
import CubicTwoStage.BerendStageIBlockAxis
import CubicTwoStage.BerendPlaneNet

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1200000

namespace CubicTwoStage
namespace BerendPhaseArc

open BerendPlanarArc
open BerendBlockLastMile

/-! ## 1. Nonnegative powers already generate the whole compact closure -/

/-- Powers of a point of the unit circle are again on the unit circle. -/
theorem pow_mem_unitCircle {c : ℂ} (hc : c ∈ unitCircle) (n : ℕ) : c ^ n ∈ unitCircle := by
  rw [mem_unitCircle] at hc ⊢
  rw [norm_pow, hc, one_pow]

/-- The set of nonnegative powers of `c` is closed under multiplication. -/
theorem range_pow_mul (c : ℂ) :
    ∀ x ∈ Set.range (fun n : ℕ => c ^ n), ∀ y ∈ Set.range (fun n : ℕ => c ^ n),
      x * y ∈ Set.range (fun n : ℕ => c ^ n) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  refine ⟨m + n, ?_⟩
  simp only [pow_add]

/-- **The closure of the nonnegative powers of a unit complex number is a
subgroup.** -/
theorem inv_mem_closure_range_pow {c : ℂ} (hc : ‖c‖ = 1) {x : ℂ}
    (hx : x ∈ closure (Set.range fun n : ℕ => c ^ n)) :
    x⁻¹ ∈ closure (Set.range fun n : ℕ => c ^ n) := by
  set K : Set ℂ := closure (Set.range fun n : ℕ => c ^ n) with hKdef
  have hKclosed : IsClosed K := isClosed_closure
  have hmul : ∀ y ∈ K, ∀ z ∈ K, y * z ∈ K := mul_mem_closure (range_pow_mul c)
  have hKunit : K ⊆ unitCircle := by
    refine closure_minimal ?_ isClosed_unitCircle
    rintro _ ⟨n, rfl⟩
    rw [mem_unitCircle]
    rw [norm_pow, hc, one_pow]
  have hxb : ‖x‖ = 1 := hKunit hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hxb
    exact zero_ne_one hxb
  have hone : (1 : ℂ) ∈ K :=
    subset_closure ⟨0, by simp⟩
  have hpow : ∀ n : ℕ, x ^ n ∈ K := by
    intro n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_sphere (x := (0 : ℂ)) (r := 1)).subset ?_
    intro y hy
    rw [mem_sphere_zero_iff_norm]
    exact hKunit hy
  have hKcpt : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hbdd⟩
  obtain ⟨a, haK, φ, hφ, htend⟩ :=
    hKcpt.isSeqCompact (x := fun n : ℕ => x ^ n) (fun n => hpow n)
  have hab : ‖a‖ = 1 := hKunit haK
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hab
    exact zero_ne_one hab
  have hshift : Tendsto (fun j : ℕ => x ^ (φ (j + 1))) atTop (𝓝 a) := by
    simpa [Function.comp_def] using htend.comp (tendsto_add_atTop_nat 1)
  have hinvseq : Tendsto (fun j : ℕ => (x ^ (φ j))⁻¹) atTop (𝓝 a⁻¹) := htend.inv₀ ha0
  have hstep : ∀ j : ℕ, x ^ (φ (j + 1)) = x ^ (φ (j + 1) - φ j) * x ^ (φ j) := by
    intro j
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt (hφ (Nat.lt_succ_self j)))]
  have hret : Tendsto (fun j : ℕ => x ^ (φ (j + 1) - φ j)) atTop (𝓝 1) := by
    have hprod : Tendsto (fun j : ℕ => x ^ (φ (j + 1)) * (x ^ (φ j))⁻¹) atTop (𝓝 (a * a⁻¹)) :=
      hshift.mul hinvseq
    rw [mul_inv_cancel₀ ha0] at hprod
    refine hprod.congr' (Eventually.of_forall fun j => ?_)
    rw [hstep j, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), mul_one]
  have hd1 : ∀ j : ℕ, 1 ≤ φ (j + 1) - φ j := by
    intro j
    have h : φ j < φ (j + 1) := hφ (Nat.lt_succ_self j)
    omega
  have hsplit : ∀ j : ℕ, x ^ (φ (j + 1) - φ j - 1) * x = x ^ (φ (j + 1) - φ j) := by
    intro j
    rw [← pow_succ, Nat.sub_add_cancel (hd1 j)]
  have hlast : Tendsto (fun j : ℕ => x ^ (φ (j + 1) - φ j - 1)) atTop (𝓝 x⁻¹) := by
    have hret' : Tendsto (fun j : ℕ => x ^ (φ (j + 1) - φ j - 1) * x) atTop (𝓝 1) :=
      hret.congr' (Eventually.of_forall fun j => (hsplit j).symm)
    have hmulc : Tendsto (fun j : ℕ => x ^ (φ (j + 1) - φ j - 1) * x * x⁻¹) atTop
        (𝓝 (1 * x⁻¹)) := hret'.mul_const x⁻¹
    rw [one_mul] at hmulc
    refine hmulc.congr' (Eventually.of_forall fun j => ?_)
    rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
  exact hKclosed.mem_of_tendsto hlast
    (Eventually.of_forall fun j => hpow (φ (j + 1) - φ j - 1))

/-- **`ℕ`-powers reach the whole circle.**  A unit complex number of infinite
multiplicative order has nonnegative powers dense in the unit circle: this is
`unitCircle_subset_closure_zpow` without inverses. -/
theorem unitCircle_subset_closure_range_pow {c : ℂ} (hc : ‖c‖ = 1)
    (hinf : ∀ m : ℤ, m ≠ 0 → c ^ m ≠ 1) :
    unitCircle ⊆ closure (Set.range fun n : ℕ => c ^ n) := by
  have hZ : unitCircle ⊆ closure (Set.range fun m : ℤ => c ^ m) :=
    unitCircle_subset_closure_zpow hc hinf
  have hsub : closure (Set.range fun m : ℤ => c ^ m) ⊆ closure (Set.range fun n : ℕ => c ^ n) := by
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨m, rfl⟩
    show c ^ m ∈ closure (Set.range fun n : ℕ => c ^ n)
    by_cases hm : (0 : ℤ) ≤ m
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      refine subset_closure ⟨n, ?_⟩
      simp
    · have hpos : (0 : ℤ) < -m := by omega
      have hz : c ^ m = (c ^ (-m))⁻¹ := by rw [zpow_neg]; simp
      rw [hz]
      refine inv_mem_closure_range_pow hc ?_
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hpos)
      refine subset_closure ⟨n, ?_⟩
      rw [hn]
      simp
  intro z hz
  exact hsub (hZ hz)

/-- **Semigroup form of the compact arc.**  A multiplicative semigroup `S ⊆ ℂ`
containing `1` and a unit-modulus element of infinite order has the whole unit
circle in its closure.  No inverses in `S` are needed. -/
theorem unitCircle_subset_closure_semigroup {S : Set ℂ}
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (h1 : (1 : ℂ) ∈ S) {g : ℂ} (hgS : g ∈ S)
    (hgunit : ‖g‖ = 1) (hginf : ∀ m : ℤ, m ≠ 0 → g ^ m ≠ 1) :
    unitCircle ⊆ closure S := by
  have hgpow : ∀ n : ℕ, g ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hgS
  refine subset_trans (unitCircle_subset_closure_range_pow hgunit hginf) ?_
  exact closure_mono (by rintro _ ⟨n, rfl⟩; exact hgpow n)

/-! ## 2. The `|λ| = 1` branch of Lemma 4.5 for the nonnegative multiplier semigroup -/

/-- The multiplier semigroup of two complex multipliers, with the exponent of the
prime multiplier restricted to `ℕ`. -/
noncomputable def multSemi (c d : ℂ) : Set ℂ :=
  Set.range fun p : ℤ × ℕ => c ^ p.1 * d ^ (p.2 : ℤ)

theorem multSemi_mul {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ x ∈ multSemi c d, ∀ y ∈ multSemi c d, x * y ∈ multSemi c d := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  refine ⟨(p.1 + q.1, p.2 + q.2), ?_⟩
  show c ^ (p.1 + q.1) * d ^ ((p.2 + q.2 : ℕ) : ℤ)
      = (c ^ p.1 * d ^ (p.2 : ℤ)) * (c ^ q.1 * d ^ (q.2 : ℤ))
  rw [Nat.cast_add, zpow_add₀ hd, zpow_add₀ hc]
  ring

theorem one_mem_multSemi (c d : ℂ) : (1 : ℂ) ∈ multSemi c d :=
  ⟨(0, 0), by simp⟩

/-- **Berend Lemma 4.5, `|λ| = 1` branch, semigroup-correct.**  Let `c d ≠ 0` be
multiplicatively independent in the sense of the corrected `(B3)`.  If some
nontrivial lattice combination has modulus one, then the unit circle lies in the
closure of the *nonnegative* multiplier semigroup
`{c ^ l * d ^ k | l : ℤ, k : ℕ}`.

This is exactly the hypothesis the unit–prime family supplies: unit exponents are
inverted (the units form a group), prime exponents are not. -/
theorem unitCircle_subset_closure_multSemigroup_of_modulus_one {c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hB3 : MultIndepPair c d) {l k : ℤ}
    (hlk : l ≠ 0 ∨ k ≠ 0) (hmod : ‖c‖ ^ l * ‖d‖ ^ k = 1) :
    unitCircle ⊆ closure (multSemi c d) := by
  have hnorm : ‖c ^ l * d ^ k‖ = 1 := by
    rw [norm_mul, norm_zpow, norm_zpow]
    exact hmod
  have hginf : ∀ m : ℤ, m ≠ 0 → (c ^ l * d ^ k) ^ m ≠ 1 :=
    pair_infinite_order hB3 hlk
  have hmul := multSemi_mul hc hd
  have h1 := one_mem_multSemi c d
  by_cases hk : (0 : ℤ) ≤ k
  · refine unitCircle_subset_closure_semigroup hmul h1 ?_ hnorm hginf
    exact ⟨(l, k.toNat), by simp [Int.toNat_of_nonneg hk]⟩
  · have hk' : (0 : ℤ) ≤ -k := by omega
    have hnorm' : ‖(c ^ l * d ^ k)⁻¹‖ = 1 := by
      rw [norm_inv, hnorm, inv_one]
    have hginf' : ∀ m : ℤ, m ≠ 0 → ((c ^ l * d ^ k)⁻¹) ^ m ≠ 1 := by
      intro m hm hcontra
      rw [inv_zpow] at hcontra
      exact hginf m hm (inv_eq_one.mp hcontra)
    refine unitCircle_subset_closure_semigroup hmul h1 ?_ hnorm' hginf'
    have hge : (c ^ l * d ^ k)⁻¹ = c ^ (-l) * d ^ (-k) := by
      rw [mul_inv, zpow_neg, zpow_neg]
    rw [hge]
    exact ⟨(-l, (-k).toNat), by simp [Int.toNat_of_nonneg hk']⟩

/-- **The compact arc inside a closed invariant `E ⊆ Pt`**, `|λ| = 1` branch: a
closed set meeting the complex plane away from `0` and invariant under the
nonnegative multiplier semigroup contains the whole circle through that point.
This is `BerendPlanarArc.circle_ofCplx_in_lift` with the semigroup hypothesis in
place of a group. -/
theorem circle_ofCplx_of_modulus_one {E : Set Pt} (hE : IsClosed E) {c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hB3 : MultIndepPair c d)
    (hinvE : ∀ p : ℤ × ℕ, ∀ z : ℂ,
      ofCplx z ∈ E → ofCplx (c ^ p.1 * d ^ (p.2 : ℤ) * z) ∈ E)
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0) (hmod : ‖c‖ ^ l * ‖d‖ ^ k = 1)
    {z₀ : ℂ} (_hz₀ : z₀ ≠ 0) (hz₀E : ofCplx z₀ ∈ E) :
    ∀ μ ∈ unitCircle, ofCplx (μ * z₀) ∈ E := by
  refine circle_ofCplx_in_lift hE ?_
    (unitCircle_subset_closure_multSemigroup_of_modulus_one hc hd hB3 hlk hmod) hz₀E
  rintro s ⟨p, rfl⟩ z hz
  exact hinvE p z hz

/-! ## 3. The modulus dichotomy of Lemma 4.5

Berend's Lemma 4.5 splits on whether a nontrivial lattice combination has modulus
one.  That split is exactly the rationality of the ratio of the log-moduli, so it
needs no transcendence input — which is why the `|λ| = 1` branch above is
unconditional from `(B3)`, while the dense-modulus branch is not. -/

/-- **A rational log-ratio produces a modulus-one lattice combination.** -/
theorem modulus_eq_one_of_ratio {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (hdn : ‖d‖ ≠ 1)
    {m n : ℤ} (hn : n ≠ 0)
    (h : Real.log ‖c‖ / Real.log ‖d‖ = (m : ℝ) / (n : ℝ)) :
    ‖c‖ ^ n * ‖d‖ ^ (-m) = 1 := by
  have hLd : Real.log ‖d‖ ≠ 0 := by
    intro hz
    rcases Real.log_eq_zero.mp hz with h0 | h1 | h1
    · exact norm_ne_zero_iff.mpr hd h0
    · exact hdn h1
    · nlinarith [norm_nonneg d]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hmn : (n : ℝ) * Real.log ‖c‖ = (m : ℝ) * Real.log ‖d‖ := by
    rw [div_eq_iff hLd] at h
    rw [h]
    field_simp
  have hlog : latticeLog c d n (-m) = 0 := by
    simp only [latticeLog]
    push_cast
    linarith
  rw [modulus_zpow_mul hc hd n (-m), hlog, Real.exp_zero]

/-- **The modulus dichotomy of Berend's Lemma 4.5.**  Either a nontrivial lattice
combination has modulus one — the `|λ| = 1` branch treated in §2 — or the ratio of
the two log-moduli is irrational, which is the dense-modulus branch.  No
transcendence input is used: the split is the rationality of a real number. -/
theorem modulus_one_or_irrational_log {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hdn : ‖d‖ ≠ 1) :
    (∃ l k : ℤ, (l ≠ 0 ∨ k ≠ 0) ∧ ‖c‖ ^ l * ‖d‖ ^ k = 1) ∨
      Irrational (Real.log ‖c‖ / Real.log ‖d‖) := by
  by_cases hex : ∃ l k : ℤ, (l ≠ 0 ∨ k ≠ 0) ∧ ‖c‖ ^ l * ‖d‖ ^ k = 1
  · exact Or.inl hex
  · refine Or.inr ?_
    rw [irrational_iff_ne_rational]
    intro m n hn hmn
    exact hex ⟨n, -m, Or.inl hn, modulus_eq_one_of_ratio hc hd hdn hn hmn⟩

/-! ## 4. The explicit one-parameter arc -/

/-- The one-parameter subgroup of the unit circle of frequency `ξ`, in Berend's
form `e((l₀ t))` with `l₀ = ξ`. -/
noncomputable def phaseArc (ξ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((t * ξ : ℝ) * (2 * (Real.pi : ℂ) * Complex.I))

@[simp] theorem phaseArc_zero (ξ : ℝ) : phaseArc ξ 0 = 1 := by
  simp [phaseArc]

theorem phaseArc_add (ξ : ℝ) (s t : ℝ) :
    phaseArc ξ (s + t) = phaseArc ξ s * phaseArc ξ t := by
  rw [phaseArc, phaseArc, phaseArc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem norm_phaseArc (ξ : ℝ) (t : ℝ) : ‖phaseArc ξ t‖ = 1 := by
  rw [phaseArc, Complex.norm_exp]
  simp

theorem continuous_phaseArc (ξ : ℝ) : Continuous (phaseArc ξ) := by
  unfold phaseArc
  fun_prop

/-- Integer points of the arc are the powers of its value at `1`. -/
theorem phaseArc_int (ξ : ℝ) (n : ℤ) : phaseArc ξ (n : ℝ) = phaseArc ξ 1 ^ n := by
  rw [phaseArc, phaseArc, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- `ℕ`-indexed form of `phaseArc_int`. -/
theorem phaseArc_nat (ξ : ℝ) (n : ℕ) : phaseArc ξ (n : ℝ) = phaseArc ξ 1 ^ n := by
  rw [phaseArc, phaseArc, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The arc of frequency `phaseOf z` passes through `z` (for `‖z‖ = 1`) at `t = 1`. -/
theorem phaseArc_one_eq_turns (z : ℂ) : phaseArc (phaseOf z) 1 = turns z := by
  rw [phaseArc, turns]
  norm_num

/-- A real number whose `2πi`-multiple is an integer `2πi`-multiple is that integer. -/
theorem real_eq_int_of_mul_two_pi_I {y : ℝ} {n : ℤ}
    (h : (y : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    y = (n : ℝ) := by
  have him : y * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im h
    simpa [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.mul_I_re, Complex.mul_I_im] using this
  have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact mul_right_cancel₀ h2 him

/-- **The arc lies in the closure of the nonnegative powers.**  This is the
"compact closure contains a one-parameter group" clause of Berend's Lemma 4.5 in
the phase coordinate, with the nonnegative powers of the multiplier. -/
theorem range_phaseArc_subset_closure_range_pow {ξ : ℝ} (hξ : Irrational ξ) :
    Set.range (phaseArc ξ) ⊆ closure (Set.range fun n : ℕ => phaseArc ξ n) := by
  have hunit : ‖phaseArc ξ 1‖ = 1 := norm_phaseArc ξ 1
  have hinf : ∀ m : ℤ, m ≠ 0 → phaseArc ξ 1 ^ m ≠ 1 := by
    intro m hm hm1
    have h2 : phaseArc ξ (m : ℝ) = 1 := by
      rw [phaseArc_int]; exact hm1
    rw [phaseArc, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    have h3 : (m : ℝ) * ξ = (n : ℝ) := real_eq_int_of_mul_two_pi_I hn
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hrat : ξ = (n : ℝ) / (m : ℝ) := by field_simp; linarith
    exact hξ ⟨(n : ℚ) / (m : ℚ), by push_cast; rw [hrat]⟩
  have hcl := unitCircle_subset_closure_range_pow hunit hinf
  rintro _ ⟨t, rfl⟩
  have hmem : phaseArc ξ t ∈ closure (Set.range fun n : ℕ => phaseArc ξ 1 ^ n) :=
    hcl (by rw [mem_unitCircle]; exact norm_phaseArc ξ t)
  simpa only [phaseArc_nat] using hmem

/-- **The arc is injective on a period** for irrational frequency, so it is a
genuine arc and not a circle traversed repeatedly.  The period of `t ↦ e^{2πi t ξ}`
is `1 / ξ`, so the correct statement is injectivity on a half-period. -/
theorem phaseArc_injOn {ξ : ℝ} (hξ : Irrational ξ) :
    Set.InjOn (phaseArc ξ) (Set.Icc 0 (1 / (2 * |ξ|))) := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    exact hξ ⟨0, by simp⟩
  have habs : 0 < |ξ| := abs_pos.mpr hξ0
  intro s hs t ht hst
  by_contra hne
  have hd : s - t ≠ 0 := sub_ne_zero.mpr hne
  have hunit : ‖phaseArc ξ 1‖ = 1 := norm_phaseArc ξ 1
  have hneg : phaseArc ξ (-t) = (phaseArc ξ t)⁻¹ := by
    rw [phaseArc, phaseArc, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have h1 : phaseArc ξ (s - t) = 1 := by
    rw [sub_eq_add_neg, phaseArc_add, hneg, hst, mul_inv_cancel₀]
    rw [← norm_ne_zero_iff, norm_phaseArc]
    exact one_ne_zero
  rw [phaseArc, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : (s - t) * ξ = (n : ℝ) := real_eq_int_of_mul_two_pi_I hn
  -- the interval is a half-period, so `(s - t) * ξ` cannot be a nonzero integer
  have hst' : |s - t| ≤ 1 / (2 * |ξ|) := by
    rw [abs_le]
    constructor
    · linarith [hs.1, ht.2]
    · linarith [ht.1, hs.2]
  have hsmall : |(s - t) * ξ| < 1 := by
    rw [abs_mul]
    calc |s - t| * |ξ| ≤ (1 / (2 * |ξ|)) * |ξ| :=
          mul_le_mul_of_nonneg_right hst' (le_of_lt habs)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have habsn : |((n : ℝ))| < 1 := by rw [← h2]; exact hsmall
  have hn0 : n = 0 := by
    have h1' : (-1 : ℝ) < (n : ℝ) := (abs_lt.mp habsn).1
    have h2' : (n : ℝ) < 1 := (abs_lt.mp habsn).2
    have h1'' : (-1 : ℤ) < n := by exact_mod_cast h1'
    have h2'' : n < (1 : ℤ) := by exact_mod_cast h2'
    omega
  rw [hn0] at h2
  simp only [Int.cast_zero] at h2
  exact hd ((mul_eq_zero.mp h2).resolve_right hξ0)

/-! ## 5. The plane-filling machine with semigroup invariance only

`BerendPlanarArc.eq_univ_of_closed_invariant` and
`cplxPlane_subset_of_multiplier_data` carry an unused-in-the-proof hypothesis
`∀ x ∈ S, x⁻¹ ∈ S`.  These are the same statements with that hypothesis removed,
so they apply to the multiplier *semigroup* of the unit–prime family.  The proofs
are the repo's, with the inverse-free dependency only. -/

/-- **Dense moduli plus the unit circle fill the punctured plane**, for a
multiplicative semigroup `S`. -/
theorem closure_eq_of_unitCircle_and_dense_radius {S : Set ℂ}
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hunit : unitCircle ⊆ closure S)
    (hrad : ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε → ∃ s ∈ S, |‖s‖ - r| < ε) :
    ∀ z : ℂ, z ≠ 0 → z ∈ closure S := by
  have hmul' := mul_mem_closure hmul
  have hcirc : ∀ s ∈ S, ∀ z' : ℂ, ‖z'‖ = ‖s‖ → z' ∈ closure S := by
    intro s hs z' hz'
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [norm_zero] at hz'
      have hz'0 : z' = 0 := norm_eq_zero.mp hz'
      rw [hz'0]
      exact subset_closure hs
    · have hμ : z' / s ∈ unitCircle := by
        rw [mem_unitCircle, norm_div, hz', div_self (norm_ne_zero_iff.mpr hs0)]
      have heq : z' = (z' / s) * s := by field_simp
      rw [heq]
      exact hmul' _ (hunit hμ) _ (subset_closure hs)
  intro z hz
  have hzcl : z ∈ closure (closure S) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨s, hsS, hsdist⟩ := hrad ‖z‖ hzn (ε / 2) (by linarith)
    set u : ℂ := (((‖s‖ / ‖z‖ : ℝ)) : ℂ) * z with hudef
    have hzu : ‖u‖ = ‖s‖ := by
      rw [hudef, norm_mul]
      have hz1 : ‖(((‖s‖ / ‖z‖ : ℝ)) : ℂ)‖ = ‖s‖ / ‖z‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (norm_nonneg s) hzn.le)]
      rw [hz1, div_mul_cancel₀ _ hzn.ne']
    refine ⟨u, hcirc s hsS u hzu, ?_⟩
    rw [dist_eq_norm]
    have hsplit : z - u = (((1 - ‖s‖ / ‖z‖ : ℝ)) : ℂ) * z := by
      rw [hudef]
      push_cast
      ring
    rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |1 - ‖s‖ / ‖z‖| * ‖z‖ = |‖z‖ - ‖s‖| := by
      have hz0 : ‖z‖ ≠ 0 := hzn.ne'
      rw [show 1 - ‖s‖ / ‖z‖ = (‖z‖ - ‖s‖) / ‖z‖ by
        rw [eq_div_iff hz0, sub_mul, one_mul, div_mul_cancel₀ _ hz0]]
      rw [abs_div, abs_of_pos hzn, div_mul_cancel₀ _ hz0]
    rw [h1, abs_sub_comm]
    linarith
  rwa [closure_closure] at hzcl

/-- **A closed semigroup-invariant set of `ℂ` containing one nonzero point is
everything.**  No inverse invariance is used. -/
theorem eq_univ_of_closed_semigroup_invariant {W : Set ℂ} (hW : IsClosed W) {S : Set ℂ}
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hunit : unitCircle ⊆ closure S)
    (hrad : ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε → ∃ s ∈ S, |‖s‖ - r| < ε)
    (hactW : ∀ s ∈ S, ∀ w ∈ W, s * w ∈ W)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0) : W = Set.univ := by
  have hcl := closure_eq_of_unitCircle_and_dense_radius hmul hunit hrad
  have hact : ∀ k ∈ closure S, ∀ w ∈ W, k * w ∈ W := by
    intro k hk w hw
    obtain ⟨u, huS, hutend⟩ := mem_closure_iff_seq_limit.mp hk
    exact hW.mem_of_tendsto (hutend.mul_const w)
      (Eventually.of_forall fun n => hactW _ (huS n) _ hw)
  have hsub : ∀ z : ℂ, z ≠ 0 → z ∈ W := by
    intro z hz
    have hzw : z / w₀ ∈ closure S := hcl _ (div_ne_zero hz hw₀0)
    have heq : z = (z / w₀) * w₀ := by field_simp
    rw [heq]
    exact hact _ hzw _ hw₀
  have hclosed : closure ({z : ℂ | z ≠ 0}) ⊆ W := closure_minimal hsub hW
  have hd : closure ({z : ℂ | z ≠ 0}) = Set.univ := (dense_compl_singleton (0 : ℂ)).closure_eq
  rw [Set.eq_univ_iff_forall]
  intro z
  exact hclosed (hd ▸ Set.mem_univ z)

/-- **Planar Stage I with semigroup invariance only.**  A closed `E ⊆ Pt` invariant
under the nonnegative multiplier semigroup, whose multiplier moduli are dense and
whose closure meets the unit circle, contains the whole complex plane as soon as it
meets it away from the origin. -/
theorem cplxPlane_subset_of_semigroup {E : Set Pt} (hE : IsClosed E) {c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : unitCircle ⊆ closure (multSemi c d))
    (hrad : ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε → ∃ s ∈ multSemi c d, |‖s‖ - r| < ε)
    (hinvE : ∀ p : ℤ × ℕ, ∀ z : ℂ,
      ofCplx z ∈ E → ofCplx (c ^ p.1 * d ^ (p.2 : ℤ) * z) ∈ E)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀E : ofCplx z₀ ∈ E) :
    cplxPlane ⊆ E := by
  set S : Set ℂ := multSemi c d with hS
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := multSemi_mul hc hd
  -- the hypothesis-free version of the semigroup closure inside `E`
  have hWeq : {z : ℂ | ofCplx z ∈ E} = Set.univ :=
    eq_univ_of_closed_semigroup_invariant (isClosed_ofCplx_preimage hE) hmul hunit hrad
      (fun s hs z hz => by
        obtain ⟨p, rfl⟩ := hs
        exact hinvE p z hz) hz₀E hz₀
  intro x hx
  have hx' : ofCplx (cplxOf x) ∈ E := by
    have hmem : cplxOf x ∈ {z : ℂ | ofCplx z ∈ E} := by
      rw [hWeq]
      trivial
    exact hmem
  rwa [eq_ofCplx_cplxOf hx] at hx'

/-! ## 6. The dense-modulus residual, named in semigroup form

`BerendPlanarArc.PhaseDense c d` quantifies over `m n : ℤ`.  In branch 2 of §3
(irrational log-ratio, no modulus-one combination) `B3` says nothing about the
phases, so the phase input has to be stated separately — and, for the actual
family, over a *nonnegative* prime exponent.  The following is that statement,
together with the fact that it supplies exactly the `hunit` hypothesis of §5.

`PhaseDenseSemi` is *not* a restatement of the conclusion and is *not* derivable
from `B3`; it is the honest residual of the dense branch (Berend's non-torsion of
the lattice phase vector, after §4.1–4.4 normalisation, which the project has not
formalised).  It is also *false* for real-positive multiplier pairs, so it cannot
be dropped. -/

/-- Phases of approximate modulus-one combinations, with the prime exponent
restricted to `ℕ`, fill the circle. -/
def PhaseDenseSemi (c d : ℂ) : Prop :=
  ∀ φ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ m : ℤ, ∃ n : ℕ,
    |(m : ℝ) * Real.log ‖c‖ + (n : ℝ) * Real.log ‖d‖| < ε ∧
      ‖c ^ m * d ^ (n : ℤ) - Complex.exp ((φ : ℂ) * Complex.I)‖ < ε

theorem unitCircle_subset_closure_of_phaseDenseSemi {c d : ℂ} (h : PhaseDenseSemi c d) :
    unitCircle ⊆ closure (multSemi c d) := by
  intro z hz
  have hz1 : ‖z‖ = 1 := hz
  have hzexp : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    have h' := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1] at h'
    simpa using h'
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, n, _hmn, hph⟩ := h z.arg ε hε
  exact ⟨c ^ m * d ^ (n : ℤ), ⟨(m, n), rfl⟩,
    by rw [dist_eq_norm, norm_sub_rev, ← hzexp]; exact hph⟩

/-! ## 7. Model-level glue: the circle inside a `UnitPrimeModel` lift -/

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- A factor of an invertible model element has nonzero complex coordinate. -/
theorem cplxOf_ne_zero_of_mulC_eq_one {a b : Pt} (h : a ⋆ b = oneC) : cplxOf a ≠ 0 := by
  intro hz
  have h2 : cplxOf a * cplxOf b = 1 := by
    have := congrArg cplxOf h
    rwa [cplxOf_mulC, BerendStageIBlock.cplxOf_oneC] at this
  rw [hz, zero_mul] at h2
  exact one_ne_zero h2.symm

/-- The complex coordinate of the inverse of a unit's image is the inverse. -/
theorem cplxOf_unit_image_inv {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ) :
    cplxOf (D.unit_image u⁻¹) = (cplxOf (D.unit_image u))⁻¹ := by
  have h := D.unit_mul u u⁻¹
  rw [mul_inv_cancel, D.unit_one] at h
  have h2 : cplxOf (D.unit_image u) * cplxOf (D.unit_image u⁻¹) = 1 := by
    have h3 := congrArg cplxOf h
    rw [cplxOf_mulC, BerendStageIBlock.cplxOf_oneC] at h3
    exact h3.symm
  exact eq_inv_of_mul_eq_one_right h2

/-- Every integral power of a unit's complex image is the complex image of a unit
of the family (negative powers use the unit inverse). -/
theorem exists_unit_cplxOf_zpow {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ) (l : ℤ) :
    ∃ v : 𝒪ˣ, cplxOf (D.unit_image v) = (cplxOf (D.unit_image u)) ^ l := by
  by_cases hl : 0 ≤ l
  · refine ⟨u ^ l.toNat, ?_⟩
    rw [BerendStageIBlock.unit_image_pow, BerendStageIBlock.cplxOf_powC,
      ← zpow_natCast, Int.toNat_of_nonneg hl]
  · have hl' : l < 0 := not_le.mp hl
    have hpos : (0 : ℤ) ≤ -l := by omega
    refine ⟨(u⁻¹) ^ (-l).toNat, ?_⟩
    rw [BerendStageIBlock.unit_image_pow, BerendStageIBlock.cplxOf_powC, cplxOf_unit_image_inv]
    conv_rhs =>
      rw [show l = -(((-l).toNat : ℕ) : ℤ) by omega, zpow_neg]
    exact inv_pow (cplxOf (D.unit_image u)) ((-l).toNat)

/-- **Every semigroup element is a family multiplier.**  For the unit generator `u`
and the prime generator `π`, the complex multiplier `c ^ l * d ^ k` with
`l : ℤ`, `k : ℕ` is `cplxOf (D.mult v j)` for an honest family index `(v, j)`. -/
theorem exists_family_of_multSemi {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ) (p : ℤ × ℕ) :
    ∃ i : 𝒪ˣ × ℕ,
      cplxOf (D.mult i.1 i.2) =
        (cplxOf (D.unit_image u)) ^ p.1 * (cplxOf (D.prime_image D.prime)) ^ (p.2 : ℤ) := by
  obtain ⟨v, hv⟩ := exists_unit_cplxOf_zpow (D := D) u p.1
  refine ⟨(v, p.2), ?_⟩
  show cplxOf (D.unit_image v ⋆ powC (D.prime_image D.prime) p.2) = _
  rw [cplxOf_mulC, hv, BerendStageIBlock.cplxOf_powC, zpow_natCast]

/-- **Semigroup-invariance glue.**  The invariance of the lift under the
nonnegative multiplier semigroup follows from forward invariance of `Y` under the
whole family: each semigroup element is a family multiplier (previous lemma). -/
theorem semigroup_invariant_of_family (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ)
    {Y : Set (Torus L)} (hinv : ∀ i, D.torusAct i '' Y ⊆ Y) :
    ∀ p : ℤ × ℕ, ∀ z : ℂ,
      ofCplx z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y →
      ofCplx ((cplxOf (D.unit_image u)) ^ p.1 *
        (cplxOf (D.prime_image D.prime)) ^ (p.2 : ℤ) * z) ∈
        (QuotientAddGroup.mk' L) ⁻¹' Y := by
  rintro p z hzE
  obtain ⟨i, hi⟩ := exists_family_of_multSemi (D := D) u p
  have hzy : (QuotientAddGroup.mk' L) (ofCplx z) ∈ Y := hzE
  have hact : D.torusAct i ((QuotientAddGroup.mk' L) (ofCplx z))
      = (QuotientAddGroup.mk' L) (D.family.act i (ofCplx z)) := D.torusAct_mk' i (ofCplx z)
  have hmem : D.torusAct i ((QuotientAddGroup.mk' L) (ofCplx z)) ∈ Y :=
    hinv i ⟨_, hzy, rfl⟩
  rw [hact] at hmem
  have hfam : D.family.act i (ofCplx z) = ptMul (D.mult i.1 i.2) (ofCplx z) := rfl
  rw [hfam, ptMul_ofCplx, hi] at hmem
  exact hmem

/-- **Planar Stage I for a `UnitPrimeModel`, dense branch.**  A closed invariant
`Y` whose lift meets the complex plane away from `0` contains the whole plane as
soon as (i) the phases of approximate modulus-one combinations of the two
generators are dense (`PhaseDenseSemi` — the honest residual, not derivable from
`(B3)`) and (ii) the semigroup moduli are dense in `ℝ_{>0}` (which *is* implied by
irrationality of the log-ratio, see `modulus_one_or_irrational_log`). -/
theorem cplxPlane_subset_preimage_of_phaseDense {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hc0 : cplxOf (D.unit_image u) ≠ 0)
    (hd0 : cplxOf (D.prime_image D.prime) ≠ 0)
    (hphase : PhaseDenseSemi (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    (hrad : ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε →
      ∃ s ∈ multSemi (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)),
        |‖s‖ - r| < ε)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    cplxPlane ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  have hE : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) := hY.preimage continuous_quotient_mk'
  have hx' : x = ofCplx (cplxOf x) := (eq_ofCplx_cplxOf hx).symm
  have hz : cplxOf x ≠ 0 := by
    intro h
    apply hx0
    rw [hx', h]
    funext i
    fin_cases i <;> simp [ofCplx]
  have hzY : ofCplx (cplxOf x) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rw [← hx']
    exact hxY
  exact cplxPlane_subset_of_semigroup hE hc0 hd0
    (unitCircle_subset_closure_of_phaseDenseSemi hphase) hrad
    (semigroup_invariant_of_family D u hinv) hz hzY

/-- **The compact arc inside the lift of a `UnitPrimeModel`**, `|λ| = 1` branch:
from corrected `(B3)` for the two generators and a nontrivial modulus-one lattice
combination, a closed invariant `Y` whose lift meets the complex plane away from
`0` contains the whole circle through that point.  This is the input that the
circle ⇒ annulus ⇒ plane direction consumes. -/
theorem circle_in_lift_of_modulus_one (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hB3 : MultIndepPair (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (D.unit_image u)‖ ^ l *
      ‖cplxOf (D.prime_image D.prime)‖ ^ k = 1)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    ∀ μ ∈ unitCircle, ofCplx (μ * cplxOf x) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  have hE : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) := hY.preimage continuous_quotient_mk'
  have hx' : x = ofCplx (cplxOf x) := (eq_ofCplx_cplxOf hx).symm
  have hz : cplxOf x ≠ 0 := by
    intro h
    apply hx0
    rw [hx', h]
    funext i
    fin_cases i <;> simp [ofCplx]
  have hinvE : ∀ p : ℤ × ℕ, ∀ z : ℂ,
      ofCplx z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y →
      ofCplx ((cplxOf (D.unit_image u)) ^ p.1 *
        (cplxOf (D.prime_image D.prime)) ^ (p.2 : ℤ) * z) ∈
        (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rintro p z hzE
    obtain ⟨i, hi⟩ := exists_family_of_multSemi (D := D) u p
    have hzy : (QuotientAddGroup.mk' L) (ofCplx z) ∈ Y := hzE
    have hact : D.torusAct i ((QuotientAddGroup.mk' L) (ofCplx z))
        = (QuotientAddGroup.mk' L) (D.family.act i (ofCplx z)) := D.torusAct_mk' i (ofCplx z)
    have hmem : D.torusAct i ((QuotientAddGroup.mk' L) (ofCplx z)) ∈ Y :=
      hinv i ⟨_, hzy, rfl⟩
    rw [hact] at hmem
    have hfam : D.family.act i (ofCplx z) = ptMul (D.mult i.1 i.2) (ofCplx z) := rfl
    rw [hfam, ptMul_ofCplx, hi] at hmem
    exact hmem
  have hzY : ofCplx (cplxOf x) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rw [← hx']
    exact hxY
  exact circle_ofCplx_of_modulus_one hE
    (cplxOf_ne_zero_of_mulC_eq_one (D.unit_inv_mul u))
    (cplxOf_ne_zero_of_mulC_eq_one D.prime_inv_mul)
    hB3 hinvE hlk hmod hz hzY


/-! ## 8. Nonnegative multiples mod 1 are dense (from the compact arc) -/

/-- `‖e^{2πit} - 1‖² = 4 sin²(πt)`, the squared form of the metric bridge between
the circle and its angle. -/
theorem norm_phaseArc_sub_one_sq (t : ℝ) :
    ‖phaseArc t 1 - 1‖ ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
  set θ : ℝ := 2 * Real.pi * t with hθ
  have hz : phaseArc t 1 = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [phaseArc]
    have harg : ((1 * t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = ((θ : ℝ) : ℂ) * Complex.I := by
      rw [hθ]; push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I]
  have hsq : ‖phaseArc t 1 - 1‖ ^ 2 = (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 := by
    rw [hz, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hcos : Real.cos θ = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have h1 : θ = 2 * (Real.pi * t) := by rw [hθ]; ring
    rw [h1, Real.cos_two_mul]
    have h2 : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    linarith
  have hsin : Real.sin θ ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 * (1 - Real.sin (Real.pi * t) ^ 2) := by
    have h1 : θ = 2 * (Real.pi * t) := by rw [hθ]; ring
    rw [h1, Real.sin_two_mul]
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * t)
    nlinarith [h2]
  rw [hsq, hcos, hsin]
  ring

/-- For `|θ| ≤ 1/2`, the distance on the circle controls the angle from below:
`4 |θ| ≤ ‖e^{2πiθ} - 1‖`. -/
theorem abs_le_of_norm_phaseArc_sub_one {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    4 * |θ| ≤ ‖phaseArc θ 1 - 1‖ := by
  have hsq := norm_phaseArc_sub_one_sq θ
  have hsin : Real.sin (Real.pi * |θ|) = |Real.sin (Real.pi * θ)| := by
    by_cases h : 0 ≤ θ
    · have hθ1 : |θ| = θ := abs_of_nonneg h
      rw [hθ1, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, hθ])
    · have h' : θ < 0 := not_le.mp h
      have habs : -(1 / 2 : ℝ) ≤ θ := (abs_le.mp hθ).1
      rw [abs_of_neg h',
        abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos, habs])),
        show Real.pi * -θ = -(Real.pi * θ) by ring, Real.sin_neg]
  have hbound : 2 * |θ| ≤ Real.sin (Real.pi * |θ|) := by
    have h2 : 2 / Real.pi * (Real.pi * |θ|) ≤ Real.sin (Real.pi * |θ|) := by
      refine Real.mul_le_sin ?_ ?_
      · positivity
      · nlinarith [Real.pi_pos, abs_nonneg θ, hθ]
    have h3 : 2 / Real.pi * (Real.pi * |θ|) = 2 * |θ| := by field_simp
    linarith
  have hsinabs : |Real.sin (Real.pi * θ)| = Real.sin (Real.pi * |θ|) := hsin.symm
  have hnn : 0 ≤ Real.sin (Real.pi * |θ|) := le_trans (by linarith [abs_nonneg θ]) hbound
  have hkey : ‖phaseArc θ 1 - 1‖ = 2 * Real.sin (Real.pi * |θ|) := by
    have hn2 : 0 ≤ ‖phaseArc θ 1 - 1‖ := norm_nonneg _
    nlinarith [sq_abs (Real.sin (Real.pi * θ))]
  rw [hkey]
  linarith

/-- **Angle recovery.**  If `e^{2πiy}` is close to `1`, then `y` is close to an
integer. -/
theorem exists_int_close_of_norm {y : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ‖phaseArc y 1 - 1‖ < 4 * δ) : ∃ m : ℤ, |y - m| < δ := by
  refine ⟨⌊y + 1 / 2⌋, ?_⟩
  have hm : |y - (⌊y + 1 / 2⌋ : ℝ)| ≤ 1 / 2 := by
    have h1 : (⌊y + 1 / 2⌋ : ℝ) ≤ y + 1 / 2 := Int.floor_le _
    have h2 : y + 1 / 2 < (⌊y + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hper : phaseArc y 1 = phaseArc (y - (⌊y + 1 / 2⌋ : ℝ)) 1 := by
    have h1 : phaseArc (y - (⌊y + 1 / 2⌋ : ℝ)) 1 * phaseArc ((⌊y + 1 / 2⌋ : ℝ)) 1 = phaseArc y 1 := by
      rw [phaseArc, phaseArc, phaseArc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : phaseArc ((⌊y + 1 / 2⌋ : ℝ)) 1 = 1 := by
      have h3 : phaseArc ((⌊y + 1 / 2⌋ : ℝ)) 1
          = Complex.exp (((⌊y + 1 / 2⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
        rw [phaseArc]
        push_cast
        ring_nf
      rw [h3, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    rw [h2, mul_one] at h1
    exact h1.symm
  rw [hper] at h
  have := abs_le_of_norm_phaseArc_sub_one (θ := y - (⌊y + 1 / 2⌋ : ℝ)) hm
  linarith

/-- **`ℕ`-multiples of an irrational number are dense mod `1`.**  This is the
semigroup-correct form of the density of `{k α mod 1}`: no negative multiples. -/
theorem exists_nat_mul_close {α : ℝ} (hα : Irrational α) (φ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∃ m : ℤ, |(k : ℝ) * α - φ - m| < δ := by
  have hunit : ‖phaseArc α 1‖ = 1 := norm_phaseArc α 1
  have hinf : ∀ m : ℤ, m ≠ 0 → phaseArc α 1 ^ m ≠ 1 := by
    intro m hm hcontra
    rw [← phaseArc_int] at hcontra
    rw [phaseArc, Complex.exp_eq_one_iff] at hcontra
    obtain ⟨n, hn⟩ := hcontra
    have hαm : (m : ℝ) * α = (n : ℝ) := real_eq_int_of_mul_two_pi_I hn
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have : α = (n : ℝ) / (m : ℝ) := by field_simp; linarith
    exact hα ⟨(n : ℚ) / (m : ℚ), by push_cast; rw [this]⟩
  have hcl := unitCircle_subset_closure_range_pow hunit hinf
  have htarget : phaseArc φ 1 ∈ unitCircle := by
    rw [mem_unitCircle]; exact norm_phaseArc φ 1
  have hmem : phaseArc φ 1 ∈ closure (Set.range fun n : ℕ => phaseArc α 1 ^ n) := hcl htarget
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.mp hmem (4 * δ) (by linarith)
  rw [dist_eq_norm, norm_sub_rev] at hk
  change ‖phaseArc α 1 ^ k - phaseArc φ 1‖ < 4 * δ at hk
  have hsplit : phaseArc α 1 ^ k = phaseArc ((k : ℝ) * α) 1 := by
    rw [← phaseArc_nat, phaseArc, phaseArc]
    congr 1
    push_cast
    ring
  have hkey : phaseArc ((k : ℝ) * α) 1 - phaseArc φ 1
      = phaseArc φ 1 * (phaseArc ((k : ℝ) * α - φ) 1 - 1) := by
    have hadd : phaseArc φ 1 * phaseArc ((k : ℝ) * α - φ) 1 = phaseArc ((k : ℝ) * α) 1 := by
      rw [phaseArc, phaseArc, phaseArc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hadd]
    ring
  rw [hsplit, hkey, norm_mul, norm_phaseArc, one_mul] at hk
  obtain ⟨m, hm⟩ := exists_int_close_of_norm hδ hk
  exact ⟨k, m, by rw [show (k : ℝ) * α - φ - m = ((k : ℝ) * α - φ) - m by ring]; exact hm⟩

/-! ## 9. Dense moduli for the nonnegative multiplier semigroup -/

/-- **Moduli of the nonnegative multiplier semigroup are dense** when the ratio of
the log-moduli is irrational.  This is the semigroup-correct form of
`BerendPlanarArc.dense_zpow_mul`: the exponent of `d` is a natural number, so it can
be used with the actual unit–prime family (no inverted prime). -/
theorem dense_radius_of_multSemi {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (hdn : ‖d‖ ≠ 1)
    (hirr : Irrational (Real.log ‖c‖ / Real.log ‖d‖)) :
    ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε →
      ∃ s ∈ multSemi c d, |‖s‖ - r| < ε := by
  intro r hr ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp (Real.continuous_exp.continuousAt) ε hε
  have hY0 : Real.log ‖d‖ ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | h1
    · exact (norm_ne_zero_iff.mpr hd) h0
    · exact hdn h1
    · nlinarith [norm_nonneg d]
  have hX0 : Real.log ‖c‖ ≠ 0 := by
    intro h
    apply hirr
    rw [h, zero_div]
    exact ⟨0, by norm_num⟩
  have hα : Irrational (Real.log ‖d‖ / Real.log ‖c‖) := by
    intro ⟨q, hq⟩
    have hYX : Real.log ‖d‖ = (q : ℝ) * Real.log ‖c‖ := by
      have h2 : Real.log ‖d‖ = (Real.log ‖d‖ / Real.log ‖c‖) * Real.log ‖c‖ := by
        field_simp
      rw [h2, hq]
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hYX
      exact hY0 hYX
    apply hirr
    refine ⟨q⁻¹, ?_⟩
    rw [hYX]
    push_cast
    field_simp
  have hδX : 0 < δ / |Real.log ‖c‖| := by
    have : (0:ℝ) < |Real.log ‖c‖| := abs_pos.mpr hX0
    positivity
  obtain ⟨k, m, hm⟩ := exists_nat_mul_close hα (Real.log r / Real.log ‖c‖) hδX
  refine ⟨c ^ (-m) * d ^ (k : ℤ), ⟨(-m, k), rfl⟩, ?_⟩
  rw [norm_mul, norm_zpow, norm_zpow, modulus_zpow_mul hc hd]
  have hlog : latticeLog c d (-m) (k : ℤ)
      = -((m : ℝ) * Real.log ‖c‖) + (k : ℝ) * Real.log ‖d‖ := by
    rw [latticeLog]
    push_cast
    ring
  have hexp : -((m : ℝ) * Real.log ‖c‖) + (k : ℝ) * Real.log ‖d‖ - Real.log r
      = Real.log ‖c‖ * ((k : ℝ) * (Real.log ‖d‖ / Real.log ‖c‖) - Real.log r / Real.log ‖c‖
          - (m : ℝ)) := by
    field_simp
    try ring
  have hmain : dist (latticeLog c d (-m) (k : ℤ)) (Real.log r) < δ := by
    rw [Real.dist_eq, hlog, hexp, abs_mul]
    calc |Real.log ‖c‖| * |(k : ℝ) * (Real.log ‖d‖ / Real.log ‖c‖) - Real.log r / Real.log ‖c‖ - (m : ℝ)|
        < |Real.log ‖c‖| * (δ / |Real.log ‖c‖|) :=
          mul_lt_mul_of_pos_left hm (abs_pos.mpr hX0)
      _ = δ := by field_simp
  have hres := hδ hmain
  rw [Real.dist_eq] at hres
  rw [← Real.exp_log hr]
  exact hres

/-! ## 10. Planar Stage I for a `UnitPrimeModel`, both branches -/

/-- **The planar accumulation case of Stage I for a `UnitPrimeModel`, modulo one
arithmetic input.**  Let `Y` be closed and invariant under the unit–prime family and
suppose `0` is a non-isolated point of the lift's planar part.  If

* the ratio of the log-moduli of the two complex generators is irrational (by
  `modulus_one_or_irrational_log` this is the only other case, the `|λ| = 1` case
  being handled by `circle_in_lift_of_modulus_one`), and
* the phases of approximate modulus-one combinations of the two generators are
  dense (`PhaseDenseSemi`, Berend's lattice-phase non-torsion — the honest residual,
  not derivable from `(B3)`),

then `Y` is the whole torus.  Nothing here inverts a prime. -/
theorem eq_univ_of_planar_acc_of_phaseDense {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ)
    (hc : CofinalPlane L) {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hc0 : cplxOf (D.unit_image u) ≠ 0)
    (hd0 : cplxOf (D.prime_image D.prime) ≠ 0)
    (hdn : ‖cplxOf (D.prime_image D.prime)‖ ≠ 1)
    (hirr : Irrational (Real.log ‖cplxOf (D.unit_image u)‖ /
      Real.log ‖cplxOf (D.prime_image D.prime)‖))
    (hphase : PhaseDenseSemi (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    (hacc : (0 : Pt) ∈ closure (((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) \ {0})) :
    Y = univ := by
  have hE : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) := hY.preimage continuous_quotient_mk'
  have hclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) := hE.inter cplxPlane_closed
  have hne : (((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) \ {0}).Nonempty := by
    rcases Set.eq_empty_or_nonempty (((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) \ {0}) with h | h
    · rw [h, closure_empty] at hacc
      exact absurd hacc (by simp)
    · exact h
  obtain ⟨x, hx, hx0⟩ := hne
  have hxplane : x ∈ cplxPlane := hx.2
  have hxeq : ofCplx (cplxOf x) = x := eq_ofCplx_cplxOf hxplane
  have hz₀ : cplxOf x ≠ 0 := by
    rintro h
    apply hx0
    rw [Set.mem_singleton_iff, ← hxeq, h, ofCplx]
    funext i
    fin_cases i <;> simp
  have hplane : cplxPlane ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y :=
    cplxPlane_subset_preimage_of_phaseDense (D := D) u hY hinv hc0 hd0 hphase
      (dense_radius_of_multSemi hc0 hd0 hdn hirr) hxplane hx0 hx.1
  refine BerendBlockLastMile.torus_eq_univ_of_unboundedPlane (L := L) hc hY (R := 0) ?_
  intro w hw _
  exact hplane hw

/-- **The planar residual binder, discharged from `PhaseDenseSemi`.**  This is the
form in which `BerendStageIPlanarOnly.zeroNonisolatedFull_canonical_planarOnly`
(and `zeroNonisolatedFull_fieldModel_of_planar`) consume the planar case: the
accumulation is taken over `(mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane`.  That set is
contained in the one used above, so no extra hypothesis on `L ∩ cplxPlane` is
needed. -/
theorem eq_univ_of_planar_residual_of_phaseDense {D : UnitPrimeModel L 𝒪} (u : 𝒪ˣ)
    (hc : CofinalPlane L) {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hc0 : cplxOf (D.unit_image u) ≠ 0)
    (hd0 : cplxOf (D.prime_image D.prime) ≠ 0)
    (hdn : ‖cplxOf (D.prime_image D.prime)‖ ≠ 1)
    (hirr : Irrational (Real.log ‖cplxOf (D.unit_image u)‖ /
      Real.log ‖cplxOf (D.prime_image D.prime)‖))
    (hphase : PhaseDenseSemi (cplxOf (D.unit_image u)) (cplxOf (D.prime_image D.prime)))
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    Y = univ := by
  have hsub : ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)
      ⊆ (((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) \ {0}) := by
    rintro z ⟨hz, hzp⟩
    refine ⟨⟨hz.1, hzp⟩, ?_⟩
    intro hz0
    subst hz0
    exact hz.2 (by simp)
  exact eq_univ_of_planar_acc_of_phaseDense (D := D) u hc hY hinv hc0 hd0 hdn hirr hphase
    (closure_mono hsub hacc)

/-! ## 11. A counterexample: a circle plus an expanding multiplier does not fill the plane

Direction (C) of this swarm tried to deduce the annulus
`{w : |z₀| ≤ ‖w‖ ≤ r|z₀|}` from a closed set containing the circle of radius `|z₀|`
and invariant under a multiplier of modulus `r ≥ 2`.  That implication is **false**,
even when the invariance is under the whole (two-sided) multiplier group `2 ^ ℤ`:
the union of the circles of radii `2 ^ k`, closed up at `0`, is a closed invariant set
that contains the unit circle, accumulates at `0`, and is very far from the plane.
Closedness does not fill the radial direction; the missing input is exactly the
density of the moduli (`dense_radius_of_multSemi`) or of the phases
(`PhaseDenseSemi`), not a consequence of expansion alone. -/

/-- The chain of circles of radii `2 ^ k` around the origin, closed up. -/
noncomputable def circleChain : Set ℂ :=
  closure (⋃ k : ℤ, {z : ℂ | ‖z‖ = (2 : ℝ) ^ k})

theorem circleChain_closed : IsClosed circleChain := isClosed_closure

theorem circleChain_mem {z : ℂ} {k : ℤ} (hz : ‖z‖ = (2 : ℝ) ^ k) : z ∈ circleChain :=
  subset_closure (Set.mem_iUnion.mpr ⟨k, hz⟩)

/-- The unit circle sits inside the chain (the `k = 0` circle). -/
theorem unitCircle_subset_circleChain : unitCircle ⊆ circleChain := by
  intro z hz
  refine circleChain_mem (k := 0) ?_
  rw [mem_unitCircle] at hz
  simpa using hz

/-- The chain is invariant under multiplication by `2`. -/
theorem circleChain_mul_two {z : ℂ} (hz : z ∈ circleChain) : (2 : ℂ) * z ∈ circleChain := by
  have hsub : (⋃ k : ℤ, {z : ℂ | ‖z‖ = (2 : ℝ) ^ k})
      ⊆ {w : ℂ | (2 : ℂ) * w ∈ circleChain} := by
    intro w hw
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    refine circleChain_mem (k := k + 1) ?_
    rw [norm_mul, hk, h2n]
    push_cast
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
    ring
  have hclosed : IsClosed {w : ℂ | (2 : ℂ) * w ∈ circleChain} :=
    circleChain_closed.preimage (continuous_const.mul continuous_id)
  exact closure_minimal hsub hclosed hz

/-- The chain accumulates at `0` through nonzero points. -/
theorem circleChain_acc_zero : (0 : ℂ) ∈ closure (circleChain \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
  have hrad : (1 / 2 : ℝ) ^ m = (2 : ℝ) ^ (-(m : ℤ)) := by
    have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h2, inv_pow, ← zpow_natCast, ← zpow_neg]
  refine ⟨(((1 / 2 : ℝ) ^ m : ℝ) : ℂ), ?_, ?_⟩
  · refine ⟨circleChain_mem (k := -(m : ℤ)) ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hrad]
    · simp [Complex.ofReal_eq_zero, hpos.ne']
  · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact hm

/-- Nothing at radius `3/2` is in the chain: every circle in it has radius `≤ 1` or
`≥ 2`, so the whole chain stays at distance `≥ 1/2` from `3/2`. -/
theorem not_mem_circleChain_three_halves : ((3 / 2 : ℝ) : ℂ) ∉ circleChain := by
  have hpos : (0:ℝ) < 3 / 2 := by norm_num
  have hsub : (⋃ k : ℤ, {z : ℂ | ‖z‖ = (2 : ℝ) ^ k})
      ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖} := by
    intro z hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    have h32 : ‖((3 / 2 : ℝ) : ℂ)‖ = 3 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    by_cases hk0 : k ≤ 0
    · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hle : (2 : ℝ) ^ k ≤ 1 := by
        have h1 : (2:ℝ) ^ k = Real.exp (Real.log 2 * (k:ℝ)) := by
          rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        rw [h1]
        have hkle : Real.log 2 * (k:ℝ) ≤ 0 := by
          have : (k:ℝ) ≤ 0 := by exact_mod_cast hk0
          nlinarith
        calc Real.exp (Real.log 2 * (k:ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hkle
          _ = 1 := Real.exp_zero
      have hzle : ‖z‖ ≤ 1 := by rw [hk]; exact hle
      have h3 : ‖z - ((3 / 2 : ℝ) : ℂ)‖ ≥ 3 / 2 - ‖z‖ := by
        have h4 := norm_sub_norm_le ((3 / 2 : ℝ) : ℂ) z
        rw [h32, norm_sub_rev] at h4
        linarith
      rw [Set.mem_ofPred_eq]
      linarith
    · have hk1 : 1 ≤ k := by omega
      have hge : (2 : ℝ) ^ k ≥ 2 := by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h1 : (2:ℝ) ^ k = Real.exp (Real.log 2 * (k:ℝ)) := by
          rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        rw [h1]
        have hkge : Real.log 2 ≤ Real.log 2 * (k:ℝ) := by
          have hk1' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
          nlinarith
        calc Real.exp (Real.log 2 * (k:ℝ)) ≥ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hkge
          _ = 2 := Real.exp_log (by norm_num)
      have hzge : ‖z‖ ≥ 2 := by rw [hk]; exact hge
      have h3 : ‖z - ((3 / 2 : ℝ) : ℂ)‖ ≥ ‖z‖ - 3 / 2 := by
        have h4 := norm_sub_norm_le z ((3 / 2 : ℝ) : ℂ)
        rw [h32] at h4
        linarith
      rw [Set.mem_ofPred_eq]
      linarith
  intro hmem
  have hclosed : IsClosed {z : ℂ | (1 / 2 : ℝ) ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hmem' : ((3 / 2 : ℝ) : ℂ) ∈ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖} :=
    closure_minimal hsub hclosed hmem
  rw [Set.mem_ofPred_eq, sub_self, norm_zero] at hmem'
  linarith

theorem circleChain_ne_univ : circleChain ≠ Set.univ := by
  intro h
  have : ((3 / 2 : ℝ) : ℂ) ∈ circleChain := by rw [h]; trivial
  exact not_mem_circleChain_three_halves this

/-! ## 12. The lattice phase vector and its one-parameter subgroup

Berend's Lemma 4.5 consumes an **integer phase vector** `({α}, {γᵢ - αβᵢ})` whose
integer span generates a compact group containing a one-parameter subgroup
`t ↦ ({l₀t}, {l₁t}, …)` with integers `l₀, l₁, …`.  This section builds the data
in the model: the *integer combinations* `(l,k)` of the two multipliers give the
lattice phase vector `(latticeLog, latticePhase)`; corrected `(B3)` makes every
nontrivial such vector avoid `{0} × ℤ` (`phaseVec_nondeg`, the vector form of
`pair_latticePhase_nondeg`); a nontrivial combination with **positive** rate exists
(`exists_pos_rate`); and its flow in `ℂ*` is an **injective** one-parameter subgroup
whose integer points are exactly the powers of `c^l * d^k`
(`scaleFlow_injective_of_norm_ne_one`, `scaleFlow_int`).  So `l₀ = 1 > 0` with
integer coefficients — exactly the `({l₀t}, …)` shape — and the flow's modulus and
turn are `‖c^l d^k‖^t` and `e(t · phaseOf (c^l d^k))`. -/

/-- The lattice phase vector of the integer combination `(l,k)`: logarithmic rate
and phase. -/
noncomputable def phaseVec (c d : ℂ) (l k : ℤ) : ℝ × ℝ :=
  (latticeLog c d l k, latticePhase c d l k)

/-- **Corrected `(B3)` in vector form.**  No nontrivial integer combination has
both zero logarithmic rate and integral phase. -/
theorem phaseVec_nondeg {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (hB3 : MultIndepPair c d)
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0) :
    (phaseVec c d l k).1 ≠ 0 ∨ ∀ n : ℤ, (phaseVec c d l k).2 ≠ n :=
  pair_latticePhase_nondeg hc hd hB3 hlk

theorem latticeLog_neg (c d : ℂ) (l k : ℤ) :
    latticeLog c d (-l) (-k) = -latticeLog c d l k := by
  rw [latticeLog, latticeLog]
  push_cast
  ring

/-- **A nontrivial combination with positive rate exists** as soon as some
nontrivial combination has nonzero rate. -/
theorem exists_pos_rate {c d : ℂ}
    (h : ∃ l k : ℤ, (l ≠ 0 ∨ k ≠ 0) ∧ latticeLog c d l k ≠ 0) :
    ∃ l k : ℤ, (l ≠ 0 ∨ k ≠ 0) ∧ 0 < latticeLog c d l k := by
  obtain ⟨l, k, hlk, hlog⟩ := h
  rcases lt_or_gt_of_ne hlog with hneg | hpos
  · exact ⟨-l, -k, by omega, by rw [latticeLog_neg]; linarith⟩
  · exact ⟨l, k, hlk, hpos⟩

/-- **The flow of a non-unit-modulus multiplier is an injective one-parameter
subgroup**: a genuine arc of `ℂ*`, not a circle traversed repeatedly. -/
theorem scaleFlow_injective_of_norm_ne_one {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    Function.Injective (scaleFlow z) := by
  intro s t hst
  by_contra hne
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hne
  rw [scaleFlow, scaleFlow] at hst
  have hsplit : ((s : ℂ) * Complex.log z)
      = ((t : ℂ) * Complex.log z) + (((s - t : ℝ)) : ℂ) * Complex.log z := by
    push_cast
    ring
  have hdiv : Complex.exp (((s - t : ℝ) : ℂ) * Complex.log z) = 1 := by
    have hA : Complex.exp ((t : ℂ) * Complex.log z) ≠ 0 := Complex.exp_ne_zero _
    rw [hsplit, Complex.exp_add] at hst
    exact mul_left_cancel₀ hA (by rw [mul_one]; exact hst)
  rw [Complex.exp_eq_one_iff] at hdiv
  obtain ⟨n, hn'⟩ := hdiv
  have hre : (s - t) * Real.log ‖z‖ = 0 := by
    have him := congrArg Complex.re hn'
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_I_re, Complex.mul_I_im, mul_zero, sub_zero, add_zero,
      Complex.log_re] at him
    simpa using him
  have hlogz : Real.log ‖z‖ ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | h1
    · exact hz (norm_eq_zero.mp h0)
    · exact hn h1
    · nlinarith [norm_nonneg z]
  rcases mul_eq_zero.mp hre with h | h
  · exact hst0 h
  · exact absurd h hlogz

/-- **The modulus/turn shape of the flow** (Berend's `|λ|^{l₀t} e((l₀β)t)` with
`l₀ = 1`, `λ = ‖z‖`): the modulus is the real power `‖z‖^t` and the argument is
`t · phaseOf z`. -/
theorem scaleFlow_eq_lambda_pow_turn {z : ℂ} (hz : z ≠ 0) (t : ℝ) :
    scaleFlow z t = ((‖z‖ ^ t : ℝ) : ℂ) *
      Complex.exp (((t * phaseOf z : ℝ)) * (2 * (Real.pi : ℂ) * Complex.I)) := by
  have harg : ((t * z.arg : ℝ) : ℂ) * Complex.I
      = ((t * phaseOf z : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [phaseOf]
    push_cast
    field_simp
  rw [scaleFlow, scaleFlow_exponent, harg, Complex.exp_add, ← Complex.ofReal_exp,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm t (Real.log ‖z‖)]

/-! ## 13. The Berend §4.4 normalisation in the block model

Berend's Lemma 4.4 normalises the logarithmic growth rates of the family members
on a minimal accumulating coordinate subspace `V_k`.  In the block model the
accumulating subspace is the complex plane `cplxPlane`, where every family member
acts *conformally* (multiplication by the single complex number `cplxOf (D.mult i)`):
there is only one rate, so the proportionality of Lemma 4.4 is automatic and the
normalised data are `λ = ‖cplxOf (D.mult i)‖` and the phase `phaseOf (cplxOf (D.mult i))`. -/

/-- On the complex plane every multiplier acts conformally, with logarithmic rate
`log ‖cplxOf (D.mult i)‖` — the normalised rate of Berend's Lemma 4.4. -/
theorem plane_log_rate (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) {x : Pt}
    (hx : x ∈ cplxPlane) (hx0 : cplxOf x ≠ 0)
    (hi0 : cplxOf (D.mult i.1 i.2) ≠ 0) :
    Real.log ‖cplxOf (ptMul (D.mult i.1 i.2) x)‖
      = Real.log ‖cplxOf (D.mult i.1 i.2)‖ + Real.log ‖cplxOf x‖ := by
  rw [cplxOf_ptMul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hi0) (norm_ne_zero_iff.mpr hx0)]

/-! ## 14. Corrected `(B3)` does not supply the phase non-torsion

The one-parameter subgroup of §12 exists for every nontrivial combination, but
corrected `(B3)` does not by itself give phase density or a full unit circle in
the multiplier closure: the pair `(e, e^{√2})` consists of positive reals and
satisfies `(B3)`, while its semigroup closure contains no non-real point.
Phase density is a sufficient input for the *unit-circle* shortcut, not a
necessary condition for every arc.  `BerendInterfaceAudit` proves that this
exact example still has an injective positive-real `scaleFlow` arc in its
closure from radius density alone.  Consequently phase non-torsion must not be
treated as an equivalent formulation of the remaining general arc-placement
problem. -/

/-- **`(B3)` holds for `(e, e^{√2})`.**  The two are real, and `l + k√2 = 0` has only
the trivial integer solution. -/
theorem exp_one_multIndep : MultIndepPair (Real.exp 1) (Real.exp (Real.sqrt 2)) := by
  intro l k h
  have hreal : (Real.exp 1) ^ l * (Real.exp (Real.sqrt 2)) ^ k = 1 := by
    have h2 : (((Real.exp 1) ^ l * (Real.exp (Real.sqrt 2)) ^ k : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_zpow]
      exact h
    exact Complex.ofReal_inj.mp h2
  have hpos1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpos2 : (0:ℝ) < Real.exp (Real.sqrt 2) := Real.exp_pos _
  have hlog : (l : ℝ) + (k : ℝ) * Real.sqrt 2 = 0 := by
    have := congrArg Real.log hreal
    rw [Real.log_mul (ne_of_gt (zpow_pos hpos1 l)) (ne_of_gt (zpow_pos hpos2 k)),
      Real.log_zpow, Real.log_zpow, Real.log_exp, Real.log_exp, Real.log_one] at this
    linarith
  have hk : k = 0 := by
    by_contra hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hsqrt : Real.sqrt 2 = -(l : ℝ) / (k : ℝ) := by
      field_simp
      linarith
    exact irrational_sqrt_two ⟨-(l : ℚ) / (k : ℚ), by push_cast; rw [hsqrt]⟩
  subst hk
  refine ⟨?_, rfl⟩
  have : (l : ℝ) = 0 := by simpa using hlog
  exact_mod_cast this

/-- **`(B3)` does not give the phase non-torsion.**  For `(e, e^{√2})` every element
of the multiplier semigroup is a positive real, so the closure contains no non-real
point and the unit circle is *not* in it: the circle conclusion of the `|λ| = 1`
branch, and hence the phase non-torsion that places the Lemma 4.5 arc inside the
lift, is not a consequence of `(B3)`. -/
theorem not_unitCircle_subset_closure_multSemi :
    ¬ (unitCircle ⊆ closure (multSemi (Real.exp 1) (Real.exp (Real.sqrt 2)))) := by
  intro h
  have him : Complex.I ∈ closure (multSemi (Real.exp 1) (Real.exp (Real.sqrt 2))) :=
    h (by rw [mem_unitCircle]; simp)
  have hclosed : IsClosed {z : ℂ | z.im = 0} :=
    isClosed_eq Complex.continuous_im continuous_const
  have hsub : multSemi (Real.exp 1) (Real.exp (Real.sqrt 2)) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨p, rfl⟩
    have hc : ((Real.exp 1 : ℂ)) ^ p.1 * ((Real.exp (Real.sqrt 2) : ℂ)) ^ (p.2 : ℤ)
        = (((Real.exp 1) ^ p.1 * (Real.exp (Real.sqrt 2)) ^ (p.2 : ℤ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_zpow]
    show ((fun p : ℤ × ℕ => ((Real.exp 1 : ℂ)) ^ p.1
      * ((Real.exp (Real.sqrt 2) : ℂ)) ^ (p.2 : ℤ)) p).im = 0
    rw [show ((fun p : ℤ × ℕ => ((Real.exp 1 : ℂ)) ^ p.1
        * ((Real.exp (Real.sqrt 2) : ℂ)) ^ (p.2 : ℤ)) p)
        = ((Real.exp 1 : ℂ)) ^ p.1 * ((Real.exp (Real.sqrt 2) : ℂ)) ^ (p.2 : ℤ) from rfl, hc,
      Complex.ofReal_im]
  have := closure_minimal hsub hclosed him
  simpa using this

end BerendPhaseArc
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendPhaseArc.pow_mem_unitCircle
#print axioms CubicTwoStage.BerendPhaseArc.inv_mem_closure_range_pow
#print axioms CubicTwoStage.BerendPhaseArc.unitCircle_subset_closure_range_pow
#print axioms CubicTwoStage.BerendPhaseArc.unitCircle_subset_closure_semigroup
#print axioms CubicTwoStage.BerendPhaseArc.multSemi_mul
#print axioms CubicTwoStage.BerendPhaseArc.unitCircle_subset_closure_multSemigroup_of_modulus_one
#print axioms CubicTwoStage.BerendPhaseArc.circle_ofCplx_of_modulus_one
#print axioms CubicTwoStage.BerendPhaseArc.phaseArc_nat
#print axioms CubicTwoStage.BerendPhaseArc.modulus_eq_one_of_ratio
#print axioms CubicTwoStage.BerendPhaseArc.modulus_one_or_irrational_log
#print axioms CubicTwoStage.BerendPhaseArc.phaseArc_add
#print axioms CubicTwoStage.BerendPhaseArc.phaseArc_int
#print axioms CubicTwoStage.BerendPhaseArc.real_eq_int_of_mul_two_pi_I
#print axioms CubicTwoStage.BerendPhaseArc.range_phaseArc_subset_closure_range_pow
#print axioms CubicTwoStage.BerendPhaseArc.phaseArc_injOn
#print axioms CubicTwoStage.BerendPhaseArc.closure_eq_of_unitCircle_and_dense_radius
#print axioms CubicTwoStage.BerendPhaseArc.eq_univ_of_closed_semigroup_invariant
#print axioms CubicTwoStage.BerendPhaseArc.cplxPlane_subset_of_semigroup
#print axioms CubicTwoStage.BerendPhaseArc.unitCircle_subset_closure_of_phaseDenseSemi
#print axioms CubicTwoStage.BerendPhaseArc.cplxOf_ne_zero_of_mulC_eq_one
#print axioms CubicTwoStage.BerendPhaseArc.cplxOf_unit_image_inv
#print axioms CubicTwoStage.BerendPhaseArc.exists_unit_cplxOf_zpow
#print axioms CubicTwoStage.BerendPhaseArc.exists_family_of_multSemi
#print axioms CubicTwoStage.BerendPhaseArc.semigroup_invariant_of_family
#print axioms CubicTwoStage.BerendPhaseArc.cplxPlane_subset_preimage_of_phaseDense
#print axioms CubicTwoStage.BerendPhaseArc.norm_phaseArc_sub_one_sq
#print axioms CubicTwoStage.BerendPhaseArc.abs_le_of_norm_phaseArc_sub_one
#print axioms CubicTwoStage.BerendPhaseArc.exists_int_close_of_norm
#print axioms CubicTwoStage.BerendPhaseArc.exists_nat_mul_close
#print axioms CubicTwoStage.BerendPhaseArc.dense_radius_of_multSemi
#print axioms CubicTwoStage.BerendPhaseArc.eq_univ_of_planar_acc_of_phaseDense
#print axioms CubicTwoStage.BerendPhaseArc.eq_univ_of_planar_residual_of_phaseDense
#print axioms CubicTwoStage.BerendPhaseArc.circle_in_lift_of_modulus_one

#print axioms CubicTwoStage.BerendPhaseArc.circleChain_closed
#print axioms CubicTwoStage.BerendPhaseArc.unitCircle_subset_circleChain
#print axioms CubicTwoStage.BerendPhaseArc.circleChain_mul_two
#print axioms CubicTwoStage.BerendPhaseArc.circleChain_acc_zero
#print axioms CubicTwoStage.BerendPhaseArc.not_mem_circleChain_three_halves
#print axioms CubicTwoStage.BerendPhaseArc.circleChain_ne_univ

#print axioms CubicTwoStage.BerendPhaseArc.phaseVec_nondeg
#print axioms CubicTwoStage.BerendPhaseArc.exists_pos_rate
#print axioms CubicTwoStage.BerendPhaseArc.scaleFlow_injective_of_norm_ne_one
#print axioms CubicTwoStage.BerendPhaseArc.scaleFlow_eq_lambda_pow_turn
#print axioms CubicTwoStage.BerendPhaseArc.plane_log_rate
#print axioms CubicTwoStage.BerendPhaseArc.exp_one_multIndep
#print axioms CubicTwoStage.BerendPhaseArc.not_unitCircle_subset_closure_multSemi

/-! ## Statement printout of the two headline results -/

#check @CubicTwoStage.BerendPhaseArc.circle_in_lift_of_modulus_one
#check @CubicTwoStage.BerendPhaseArc.eq_univ_of_planar_residual_of_phaseDense
