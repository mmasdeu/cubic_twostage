/-
# Stage I, Lemma 4.6: expanding images of a partial arc are ε-nets of long segments

Swarm `smw9bimdc`, member `m4`, direction `d2`.

Berend (*Multi-invariant sets on tori*, TAMS **280** (1983), Lemma 4.6, p. 525)
states: *for every `ε > 0`, `Ẽ` forms an `ε`-net for arbitrarily long line
segments in `V_k`*.  His proof takes the arc of Lemma 4.5,

  `w(t) = Σ_j |λ_{j,0}|^{l₀ t} · e((l_j + l₀ β_j) t) · u^{(j)}`,  `0 ≤ t ≤ t'`,

its images `w_m(t) = ã^m(w(t))` under high powers of an expanding endomorphism,
expands the arc around `t = 0` into the *linear* curve

  `v_m(t) = Σ_j λ_{j,0}^m (1 + l₀ t ln|λ_{j,0}| + 2πi (l_j + l₀ β_j) t) u^{(j)}`,

and compares them termwise.  The analytic input is the boxed inequality
`|exp z − 1 − z| ≤ |z|² exp(|z|)/2` (`z ∈ ℂ`), which gives a **uniform quadratic
error** `‖w_m(t) − v_m(t)‖ ≤ c t² |λ_{1,0}|^m` for `0 ≤ t ≤ t'`; restricting to
the partial arcs `0 ≤ t ≤ t_m` with

  `t_m² |λ_{1,0}|^m → 0`  and  `t_m |λ_{1,0}|^m → ∞`

makes the images of the partial arcs `ε`-nets for the segments `V_m`, while the
length of `V_m` tends to infinity.

This file formalises that mechanism for the block model `Pt = ℝ × ℂ` of the
project, in the single-rate form in which the Lemma 4.5 arc is a logarithmic
spiral `w₀ · exp(t L)`.  That is exactly `BerendPlanarArc.scaleFlow`, whose polar
form `|λ|^{l₀ t} e((l_j + l₀ β_j) t)` is `scaleFlow_eq_polar`, with the rate `L`
the common real log-rate together with the lattice-phase rate of the planar
accumulation data (`BerendRate`, `BerendOrbit`, `BerendPlanarArc.latticePhase`).

## What is proved, and what is a named input

* §1 the second-order exponential inequality (Berend's boxed display);
* §2 the uniform quadratic Taylor bound for the flow `scaleFlow c`, and its
  derivative at `t = 0`;
* §3 the source-faithful net statement: *the partial scaled arcs `{m • γ(t/m)}`
  form `ε`-nets of arbitrarily long tangent segments* for an abstract arc `γ`
  with a quadratic Taylor bound — this is the exact shape `{m γ(t/m) mod L}` of
  the lemma, with no reference to the model;
* §4 the Lemma 4.5 arc `arcThrough w₀ c` inside the lift `Pt` and its tangent
  `arcTangent w₀ c`, with the quadratic bound transported through `ofCplx`
  (`‖ofCplx z‖ ≤ ‖z‖`) and the norm identities of the block model;
* §5 **Lemma 4.6 for the actual one-expanding-member context**: if `E ⊆ Pt` is
  closed under `ptMul a` for one member `a` with `1 < ‖cplxOf a‖`, and contains
  the arc `arcThrough w₀ c` on `[0,t']`, then for every `ε > 0` and `R > 0`
  there are `m` and `t_m > 0` such that `E` contains an `ε`-net for the tangent
  segment `{ofCplx ((cplxOf a)^m w₀ (1 + s L)) | s ∈ [0, t_m]}`, whose length
  `t_m ‖cplxOf a‖^m ‖w₀‖ ‖L‖` is at least `R`, while the approximation error
  `‖w₀‖ ‖cplxOf a‖^m t_m² ‖L‖²` is less than `ε`;
* §6 the torus form (the `ε`-net taken in `Torus L`, where the invariant sets of
  Stage I live), the litotes form of the conclusion — *the `ε`-neighbourhood of
  `E` contains a segment of every length `R`* — and conjugation compatibility:
  the conjugate place has the same modulus and negated phase (`scaleFlow_conj`,
  `Complex.log_conj`), so the bound is unchanged under `φ ↦ −φ`;
* §7 the passage to the limit of Berend's Proposition 4.2, in its two halves:
  `segment_subset_of_eps_nets` (a closed set meeting `1/(k+1)`-neighbourhoods of
  segments whose base classes and unit directions converge contains the limiting
  segment) and `exists_segment_subset` (the compact torus and the compact unit
  sphere supply the convergent subsequence, so a closed invariant `Y` meeting the
  lift of the Lemma 4.5 arc **contains a nontrivial segment**), with the
  unit-prime instantiation `exists_segment_subset_torusAct`;
* §8 the sweep `circle × segment = annulus`: a set closed under unit-circle
  rotations and containing a segment that avoids `0` contains the annulus
  between the endpoint moduli (`annulus_subset_of_segment`); hung on the lift it
  gives `plane_unbounded_of_segment` (the unbounded complex plane, via
  `BerendBlockLastMile.plane_unbounded_of_annulus`), and the capstone
  `eq_univ_of_plane_segment` / `torus_eq_univ_of_segment_data`: **Stage I,
  `E = univ`, from one nontrivial plane segment in the lift, unit-circle
  invariance, one expanding member, `L`-saturation and `CofinalPlane`.**

**The arc placement is an explicit named input `harc`, not a repackaged target.**
Nothing here produces the Lemma 4.5 arc from the arithmetic: that is
`BerendPlanarArc.pair_latticePhase_nondeg` plus the lattice-phase one-parameter
subgroup construction, and its absence is exactly why this file is not a Stage I
proof.  Conversely `harc` is far weaker than Stage I: it is a statement about one
compact arc through one plane point, whereas Stage I concludes `Y = univ`.  In
particular `CplxMultiplierDense` is never assumed, no `PhaseDense` hypothesis is
introduced.  The only statement of the form `Y = univ` is the capstone of §8,
which is explicitly conditional on a plane segment in the lift.  Two named inputs remain, and they are the honest boundary of this file:
(i) the **arc placement** `harc` of §5 (the output of Lemma 4.5, i.e.
`BerendPlanarArc.pair_latticePhase_nondeg` together with the lattice-phase
one-parameter subgroup construction), and (ii) a **genuine plane segment in the
lift**, which §7 produces in the *torus*; upgrading it needs path lifting of the
torus segment along `Pt → Pt ⧸ L` for a discrete lattice (available for
`canonicalFieldModel`) and is not done here.

What §7 does **not** contain is Berend's closed-subgroup step (Propositions 4.2–4.3): from the nontrivial segment
in `Y` one must still obtain a translate of a closed connected subgroup, use
irreducibility of every positive power (B1) to rule out a proper rational
invariant subgroup, and conclude `Y = univ` together with the accumulation
hypothesis.  That argument needs the structure theory of closed subgroups of
`Torus L` and the finite-torsion/finite-kernel data of `BerendLatticeIndex` and
`BerendFibre`; it is not formalised here, and nothing below pretends otherwise.

No `sorry`, no `axiom`; the audit at the end prints the axiom basis.
-/
import CubicTwoStage.BerendPlanarArc

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace CubicTwoStage
namespace BerendTangentNet

open BerendPlanarArc BerendBlockLastMile

/-! ## 0. The block model: `ofCplx` arithmetic and the norm bound -/

theorem ofCplx_add (a b : ℂ) : ofCplx (a + b) = ofCplx a + ofCplx b := by
  funext i
  fin_cases i <;> simp [ofCplx]

theorem ofCplx_neg (a : ℂ) : ofCplx (-a) = -ofCplx a := by
  funext i
  fin_cases i <;> simp [ofCplx]

theorem ofCplx_sub (a b : ℂ) : ofCplx (a - b) = ofCplx a - ofCplx b := by
  funext i
  fin_cases i <;> simp [ofCplx]

/-- Real scalars act on the plane through `ofCplx`. -/
theorem ofCplx_real_smul (r : ℝ) (z : ℂ) : ofCplx ((r : ℂ) * z) = r • ofCplx z := by
  funext i
  fin_cases i <;> simp [ofCplx, Complex.mul_re, Complex.mul_im]

/-- The supremum norm of the block model is dominated by the complex modulus on
the complex plane. -/
theorem norm_ofCplx_le (z : ℂ) : ‖ofCplx z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (x := ofCplx z) (r := ‖z‖) (norm_nonneg z)).mpr ?_
  intro i
  fin_cases i
  · simp [ofCplx]
  · simpa [ofCplx] using Complex.abs_re_le_norm z
  · simpa [ofCplx] using Complex.abs_im_le_norm z

/-! ## 1. The second-order exponential inequality

Berend's proof of Lemma 4.6 uses `|exp z − 1 − z| ≤ |z|² exp(|z|)/2` for all
`z ∈ ℂ`.  For `‖z‖ ≤ 1` the exponential factor can be dropped, and that sharp
form is in Mathlib.  Since the partial arcs satisfy `t_m → 0`, this is the form
the net argument needs. -/

/-- **Berend's second-order exponential inequality** (small-argument form). -/
theorem norm_exp_sub_one_sub_self_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
  Complex.norm_exp_sub_one_sub_id_le hz

theorem norm_real_mul (t : ℝ) (z : ℂ) : ‖(t : ℂ) * z‖ = |t| * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-! ## 2. The uniform quadratic Taylor bound for the flow -/

/-- **Uniform quadratic Taylor bound for the flow.**  On the range
`t ‖log c‖ ≤ 1` the error of the linear approximation `1 + t log c` is at most
`t² ‖log c‖²`. -/
theorem scaleFlow_taylor {c : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hsmall : t * ‖Complex.log c‖ ≤ 1) :
    ‖scaleFlow c t - 1 - (t : ℂ) * Complex.log c‖
      ≤ t ^ 2 * ‖Complex.log c‖ ^ 2 := by
  have hnorm : ‖(t : ℂ) * Complex.log c‖ ≤ 1 := by
    rw [norm_real_mul, abs_of_nonneg ht]
    exact hsmall
  have h := norm_exp_sub_one_sub_self_le hnorm
  refine h.trans_eq ?_
  rw [norm_real_mul, abs_of_nonneg ht]
  ring

/-- The tangent of the flow at `t = 0` is the log-rate. -/
theorem hasDerivAt_scaleFlow (c : ℂ) (t : ℝ) :
    HasDerivAt (scaleFlow c) (Complex.log c * scaleFlow c t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id (x := t)).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.log c) (Complex.log c) t := by
    simpa using h1.mul_const (Complex.log c)
  have h3 := h2.cexp
  have heq : (scaleFlow c) = fun s : ℝ => Complex.exp ((s : ℂ) * Complex.log c) := rfl
  rw [heq]
  convert h3 using 1
  ring

/-! ## 3. The net statement in its source form: partial scaled arcs

This is the exact shape of Lemma 4.6 quoted by the task: the partial scaled arcs
`{m γ(t/m)}` (resp. their images `mod L`) are `ε`-nets of the tangent segments
`{s v | 0 ≤ s ≤ R}`, and the segments are *arbitrarily long* because `R` is
arbitrary.  The proof is the uniform quadratic bound: `m γ(s/m) = s v + O(s²/m)`. -/

/-- **Partial scaled arcs are ε-nets of arbitrarily long tangent segments.**
Let `γ` be an arc with uniform quadratic Taylor error `‖γ(t) − t v‖ ≤ K t²` on
`[0,t']`.  Then for every `ε > 0` and `R > 0` there is `m` such that every point
of the segment `{s v | s ∈ [0,R]}` is within `ε` of a point of the scaled partial
arc `{m • γ(s/m) | s ∈ [0,R]}`. -/
theorem exists_partial_scaled_arc_net {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {γ : ℝ → V} {v : V} {K t' : ℝ}
    (hK : 0 < K) (ht' : 0 < t')
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) t', ‖γ t - t • v‖ ≤ K * t ^ 2)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ m : ℕ, 0 < m ∧ ∀ s ∈ Set.Icc (0 : ℝ) R,
      ∃ t ∈ Set.Icc (0 : ℝ) t', ‖(m : ℝ) • γ t - s • v‖ < ε := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (max (K * R ^ 2 / ε) (R / t'))
  have hmaxpos : (0 : ℝ) < max (K * R ^ 2 / ε) (R / t') :=
    lt_of_lt_of_le (div_pos (mul_pos hK (pow_pos hR 2)) hε) (le_max_left _ _)
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_trans hmaxpos hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmne : m ≠ 0 := by
    rintro rfl
    exact absurd hmpos (by norm_num)
  have hmK : K * R ^ 2 / ε < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmR : R / t' < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmR' : R < t' * (m : ℝ) := by
    rw [div_lt_iff₀ ht'] at hmR
    linarith
  refine ⟨m, Nat.pos_of_ne_zero hmne, fun s hs =>
    ⟨s / (m : ℝ), ⟨div_nonneg hs.1 hmpos.le, ?_⟩, ?_⟩⟩
  · -- the shrunken parameter stays in `[0,t']`
    rw [div_le_iff₀ hmpos]
    linarith [hs.2, hmR']
  · -- the quadratic error, scaled back
    have hmem : s / (m : ℝ) ∈ Set.Icc (0 : ℝ) t' :=
      ⟨div_nonneg hs.1 hmpos.le, by rw [div_le_iff₀ hmpos]; linarith [hs.2, hmR']⟩
    have hsm : (m : ℝ) • γ (s / (m : ℝ)) - s • v
        = (m : ℝ) • (γ (s / (m : ℝ)) - (s / (m : ℝ)) • v) := by
      rw [smul_sub, smul_smul, mul_div_cancel₀ s hm0]
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hmpos]
    have hbound := hγ (s / (m : ℝ)) hmem
    have hsq : (m : ℝ) * (K * (s / (m : ℝ)) ^ 2) = K * s ^ 2 / (m : ℝ) := by
      field_simp
    have hs2 : K * s ^ 2 ≤ K * R ^ 2 := by
      have h2 : s ^ 2 ≤ R ^ 2 := by nlinarith [hs.1, hs.2]
      exact mul_le_mul_of_nonneg_left h2 hK.le
    have hmono : K * s ^ 2 / (m : ℝ) ≤ K * R ^ 2 / (m : ℝ) :=
      div_le_div_of_nonneg_right hs2 hmpos.le
    have hfinal : K * R ^ 2 / (m : ℝ) < ε := by
      rw [div_lt_iff₀ hmpos]
      rw [div_lt_iff₀ hε] at hmK
      linarith
    calc (m : ℝ) * ‖γ (s / (m : ℝ)) - (s / (m : ℝ)) • v‖
        ≤ (m : ℝ) * (K * (s / (m : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hmpos)
      _ = K * s ^ 2 / (m : ℝ) := hsq
      _ ≤ K * R ^ 2 / (m : ℝ) := hmono
      _ < ε := hfinal

/-! ## 4. The Lemma 4.5 arc in the lift `Pt` and its tangent

`w₀ · exp(t log c)` is the spiral of Lemma 4.5 read in the complex block: the
modulus is `|w₀| |c|^t` (`norm_scaleFlow`) and the phase rate is `arg c`
(`scaleFlow_eq_polar`); the general Lemma 4.5 arc has one such factor per
eigen-coordinate, and the planar branch of the block model keeps the single
complex one (the real coordinate is cut out by the invariant plane). -/

/-- The Lemma 4.5 arc through the plane point `w₀ ∈ ℂ`, with log-rate `log c`. -/
noncomputable def arcThrough (w₀ c : ℂ) (t : ℝ) : Pt := ofCplx (w₀ * scaleFlow c t)

/-- The tangent vector of `arcThrough w₀ c` at `t = 0`: `w₀ log c`. -/
noncomputable def arcTangent (w₀ c : ℂ) : Pt := ofCplx (w₀ * Complex.log c)

@[simp] theorem arcThrough_zero (w₀ c : ℂ) : arcThrough w₀ c 0 = ofCplx w₀ := by
  simp [arcThrough]

theorem continuous_arcThrough (w₀ c : ℂ) : Continuous (arcThrough w₀ c) :=
  ofCplx_continuous.comp (continuous_const.mul (continuous_scaleFlow c))

/-- The integer points of the arc are the plane orbit points of the multiplier. -/
theorem arcThrough_nat (w₀ c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    arcThrough w₀ c n = ofCplx (w₀ * c ^ n) := by
  rw [arcThrough, scaleFlow_nat c hc n]

/-- **Quadratic Taylor bound for the Lemma 4.5 arc in the lift.** -/
theorem arcThrough_taylor {w₀ c : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hsmall : t * ‖Complex.log c‖ ≤ 1) :
    ‖arcThrough w₀ c t - arcThrough w₀ c 0 - t • arcTangent w₀ c‖
      ≤ ‖w₀‖ * (t ^ 2 * ‖Complex.log c‖ ^ 2) := by
  have hid : arcThrough w₀ c t - arcThrough w₀ c 0 - t • arcTangent w₀ c
      = ofCplx (w₀ * (scaleFlow c t - 1 - (t : ℂ) * Complex.log c)) := by
    unfold arcThrough arcTangent
    rw [scaleFlow_zero, mul_one, ← ofCplx_real_smul, ← ofCplx_sub, ← ofCplx_sub]
    congr 1
    ring
  rw [hid]
  calc ‖ofCplx (w₀ * (scaleFlow c t - 1 - (t : ℂ) * Complex.log c))‖
      ≤ ‖w₀ * (scaleFlow c t - 1 - (t : ℂ) * Complex.log c)‖ := norm_ofCplx_le _
    _ = ‖w₀‖ * ‖scaleFlow c t - 1 - (t : ℂ) * Complex.log c‖ := norm_mul _ _
    _ ≤ ‖w₀‖ * (t ^ 2 * ‖Complex.log c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (scaleFlow_taylor ht hsmall) (norm_nonneg w₀)

/-! ## 5. Lemma 4.6: expanding images of a partial arc are ε-nets of long segments -/

/-- Iterating a `ptMul`-invariant set. -/
theorem iterate_mem {E : Set Pt} {a : Pt} (hE : ∀ x ∈ E, ptMul a x ∈ E) (m : ℕ) :
    ∀ {x : Pt}, x ∈ E → ((ptMul a) ^ m) x ∈ E := by
  induction m with
  | zero => intro x hx; simpa using hx
  | succ m ih => intro x hx; rw [pow_succ]; exact ih (hE x hx)

/-- The `m`-th iterate of the family action on a plane point. -/
theorem iterate_ptMul_ofCplx (a : Pt) (z : ℂ) (m : ℕ) :
    ((ptMul a) ^ m) (ofCplx z) = ofCplx ((cplxOf a) ^ m * z) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, ptMul_ofCplx, pow_succ']
      congr 1
      ring

/-- `Complex.log` vanishes only at `1`, for non-zero arguments. -/
theorem log_ne_zero {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : Complex.log c ≠ 0 := by
  intro h
  apply hc1
  have h1 : Complex.exp (Complex.log c) = Complex.exp 0 := by rw [h]
  rwa [Complex.exp_log hc0, Complex.exp_zero] at h1

/-- **Berend, Lemma 4.6, in the block model with one expanding member.**

Let `E ⊆ Pt` be closed under multiplication by a family member `a` whose complex
multiplier expands, `1 < ‖cplxOf a‖`, and suppose `E` contains the Lemma 4.5 arc
`arcThrough w₀ c` on `[0,t']` (the named input `harc`).  Then for every `ε > 0`
and every `R > 0` there are `m ≥ 1` and `t_m > 0` such that

* the tangent segment `s ↦ ofCplx ((cplxOf a)^m w₀ (1 + s log c))`, `s ∈ [0,t_m]`,
  has length `t_m ‖cplxOf a‖^m ‖w₀‖ ‖log c‖ ≥ R` (arbitrarily long), and
* every point of it is within `ε` of a point of `E` (sharper: of the image of
  the partial arc `arcThrough w₀ c ([0,t_m])` under the `m`-th power of `a`).

Both error and length are governed by the same scale `‖cplxOf a‖^m`: the error
is `‖w₀‖ ‖cplxOf a‖^m t_m² ‖log c‖² < ε`.  This is Berend's `(4.11)–(4.13)`,
with `t_m² |λ|^m → 0` and `t_m |λ|^m → ∞`. -/
theorem exists_eps_net_long_segment {E : Set Pt} {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hE : ∀ x ∈ E, ptMul a x ∈ E)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', arcThrough w₀ c t ∈ E)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ m : ℕ, 0 < m ∧ ∃ t_m : ℝ, 0 < t_m ∧
      R ≤ t_m * ‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖ ∧
      ‖w₀‖ * ‖cplxOf a‖ ^ m * t_m ^ 2 * ‖Complex.log c‖ ^ 2 < ε ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t_m, ∃ y ∈ E,
        ‖y - ofCplx ((cplxOf a) ^ m * w₀ * (1 + (s : ℂ) * Complex.log c))‖ < ε) := by
  classical
  set ρ := ‖cplxOf a‖ with hρdef
  set L := Complex.log c with hLdef
  have hρpos : 0 < ρ := by linarith
  have hLpos : 0 < ‖L‖ := by
    rw [hLdef, norm_pos_iff]
    exact log_ne_zero hc0 hc1
  have hw₀pos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  -- the two scale quantities of the error and length bounds
  set K : ℝ := ‖w₀‖ * ‖L‖ ^ 2 with hKdef
  set D : ℝ := ‖w₀‖ * ‖L‖ with hDdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hDpos : 0 < D := by rw [hDdef]; positivity
  -- an Archimedean threshold for `ρ^n`
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y := ρ)
    (max (max 1 (K / ε)) (max (max (R / D) ‖L‖) (1 / t'))) hρ
  set P : ℝ := ρ ^ n with hPdef
  have hA1 : (1 : ℝ) ≤ max 1 (K / ε) := le_max_left _ _
  have hA2 : K / ε ≤ max 1 (K / ε) := le_max_right _ _
  have hB1 : R / D ≤ max (R / D) ‖L‖ := le_max_left _ _
  have hB2 : ‖L‖ ≤ max (R / D) ‖L‖ := le_max_right _ _
  have hB3 : max (R / D) ‖L‖ ≤ max (max (R / D) ‖L‖) (1 / t') := le_max_left _ _
  have hB4 : (1 : ℝ) / t' ≤ max (max (R / D) ‖L‖) (1 / t') := le_max_right _ _
  have hC1 : max 1 (K / ε) ≤ max (max 1 (K / ε)) (max (max (R / D) ‖L‖) (1 / t')) :=
    le_max_left _ _
  have hC2 : max (max (R / D) ‖L‖) (1 / t')
      ≤ max (max 1 (K / ε)) (max (max (R / D) ‖L‖) (1 / t')) := le_max_right _ _
  have hP1 : 1 < P := lt_of_le_of_lt (le_trans hA1 hC1) hn
  have hPK : K / ε < P := lt_of_le_of_lt (le_trans hA2 hC1) hn
  have hPR : R / D < P := lt_of_le_of_lt (le_trans (le_trans hB1 hB3) hC2) hn
  have hPL : ‖L‖ < P := lt_of_le_of_lt (le_trans (le_trans hB2 hB3) hC2) hn
  have hPt : (1 : ℝ) / t' < P := lt_of_le_of_lt (le_trans hB4 hC2) hn
  have hPpos : 0 < P := by linarith
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero] at hPdef
      rw [← hPdef] at hP1
      exact absurd hP1 (by norm_num)
    · exact h
  have hmpos : 0 < 4 * n := by omega
  have hP3pos : (0 : ℝ) < P ^ 3 := pow_pos hPpos 3
  -- the scale: `m = 4n`, `t_m = 1 / P ^ 3`
  refine ⟨4 * n, hmpos, 1 / P ^ 3, div_pos one_pos hP3pos, ?_, ?_, ?_⟩
  · -- the tangent segment is at least as long as `R`
    have hpow : ρ ^ (4 * n) = P ^ 4 := by
      rw [hPdef, ← pow_mul]
      congr 1
      omega
    have hlen : 1 / P ^ 3 * ρ ^ (4 * n) * ‖w₀‖ * ‖L‖ = P * D := by
      rw [hpow, hDdef]
      field_simp
    rw [hlen]
    rw [div_lt_iff₀ hDpos] at hPR
    linarith
  · -- the approximation error is less than `ε`
    have hpow : ρ ^ (4 * n) = P ^ 4 := by
      rw [hPdef, ← pow_mul]
      congr 1
      omega
    have herr : ‖w₀‖ * ρ ^ (4 * n) * (1 / P ^ 3) ^ 2 * ‖L‖ ^ 2 = K / P ^ 2 := by
      rw [hpow, hKdef]
      field_simp
    rw [herr]
    have h1 : K / P ^ 2 ≤ K / P :=
      div_le_div_of_nonneg_left hKpos.le hPpos (by nlinarith)
    have h2 : K / P < ε := by
      rw [div_lt_iff₀ hPpos]
      rw [div_lt_iff₀ hε] at hPK
      linarith
    linarith
  · -- the ε-net property on the partial arc
    intro s hs
    have hst' : s ≤ t' := by
      have h2 : (1 : ℝ) / P ^ 3 ≤ t' := by
        rw [div_le_iff₀ hP3pos]
        rw [div_lt_iff₀ ht'] at hPt
        have h3 : (1 : ℝ) ≤ P ^ 3 := one_le_pow₀ hP1.le
        have h5 : (1 : ℝ) ≤ P ^ 2 := one_le_pow₀ hP1.le
        have h6 : t' * P ^ 3 = (P * t') * P ^ 2 := by ring
        rw [h6]
        exact le_of_lt (lt_of_lt_of_le hPt
          (le_mul_of_one_le_right (le_of_lt (mul_pos hPpos ht')) h5))
      linarith [hs.2]
    have hsI : s ∈ Set.Icc (0 : ℝ) t' := ⟨hs.1, hst'⟩
    refine ⟨((ptMul a) ^ (4 * n)) (arcThrough w₀ c s),
      iterate_mem hE (4 * n) (harc s hsI), ?_⟩
    have hiter : ((ptMul a) ^ (4 * n)) (arcThrough w₀ c s)
        = ofCplx (cplxOf a ^ (4 * n) * (w₀ * scaleFlow c s)) := by
      rw [arcThrough, iterate_ptMul_ofCplx]
    rw [hiter, ← ofCplx_sub]
    have hkey : cplxOf a ^ (4 * n) * (w₀ * scaleFlow c s)
          - cplxOf a ^ (4 * n) * w₀ * (1 + (s : ℂ) * L)
        = cplxOf a ^ (4 * n) * w₀ * (scaleFlow c s - 1 - (s : ℂ) * L) := by
      rw [hLdef]
      ring
    rw [hkey, hLdef]
    -- the quadratic Taylor bound, uniformly in the scale
    have hs_small : s * ‖Complex.log c‖ ≤ 1 := by
      have h1 : s ≤ 1 / P ^ 3 := hs.2
      have h0 : (0 : ℝ) ≤ 1 / P ^ 3 := le_of_lt (div_pos one_pos hP3pos)
      have h3 : s * ‖L‖ ≤ (1 / P ^ 3) * P :=
        mul_le_mul h1 hPL.le (norm_nonneg L) h0
      have h4 : (1 / P ^ 3) * P = 1 / P ^ 2 := by
        field_simp
      have h5 : 1 / P ^ 2 ≤ 1 := by
        rw [div_le_one (pow_pos hPpos 2)]
        nlinarith
      linarith
    have hbound := scaleFlow_taylor (c := c) (t := s) hs.1 hs_small
    refine (norm_ofCplx_le _).trans_lt ?_
    rw [norm_mul, norm_mul, norm_pow]
    have hscaled : ‖cplxOf a‖ ^ (4 * n) * ‖w₀‖
        * ‖scaleFlow c s - 1 - (s : ℂ) * Complex.log c‖
        ≤ ‖cplxOf a‖ ^ (4 * n) * ‖w₀‖ * (s ^ 2 * ‖Complex.log c‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    refine hscaled.trans_lt ?_
    have hpow : ‖cplxOf a‖ ^ (4 * n) = P ^ 4 := by
      rw [← hρdef, hPdef, ← pow_mul]
      congr 1
      omega
    have hs2 : s ^ 2 ≤ 1 / P ^ 6 := by
      have h1 : s ≤ 1 / P ^ 3 := hs.2
      have h0 : (0 : ℝ) ≤ 1 / P ^ 3 := le_of_lt (div_pos one_pos hP3pos)
      have h6 : (1 / P ^ 3) ^ 2 = 1 / P ^ 6 := by
        field_simp
      nlinarith [hs.1, h1, h0, h6]
    have hfin : P ^ 4 * ‖w₀‖ * (s ^ 2 * ‖Complex.log c‖ ^ 2) ≤ K / P ^ 2 := by
      have hstep : P ^ 4 * ‖w₀‖ * (s ^ 2 * ‖Complex.log c‖ ^ 2)
          ≤ P ^ 4 * ‖w₀‖ * ((1 / P ^ 6) * ‖Complex.log c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hs2 (by positivity)
      refine hstep.trans (le_of_eq ?_)
      rw [hKdef]
      field_simp
      ring
    have herr : K / P ^ 2 < ε := by
      have h1 : K / P ^ 2 ≤ K / P :=
        div_le_div_of_nonneg_left hKpos.le hPpos (by nlinarith)
      have h2 : K / P < ε := by
        rw [div_lt_iff₀ hPpos]
        rw [div_lt_iff₀ hε] at hPK
        linarith
      linarith
    rw [hpow]
    linarith

/-! ## 6. Conjugate places, the torus form, and the conclusion in Berend's words

Three additions close the file.  First, a comparison of the two norms on the
complex block: the model norm and the complex modulus differ by at most `√2`.
Second, the conjugate place: complex conjugation negates the phase rate and
preserves the modulus, so the net statement for the conjugate multiplier carries
exactly the same constants.  Third, the torus form: the actual sets of Stage I
live in `Pt ⧸ L`, and the quotient map does not increase distances, so the
`ε`-nets of §5 are `ε`-nets there too.  The section closes with the sentence of
Berend's Lemma 4.6 in its literal form: *for every `ε > 0` there are segments of
every length in the `ε`-neighbourhood of `E`*. -/

/-- The model norm of a plane point and the complex modulus differ by at most
`√2`: the complex plane carries the Euclidean metric, the lift the supremum
metric. -/
theorem norm_le_sqrt_two_mul_norm_ofCplx (z : ℂ) :
    ‖z‖ ≤ Real.sqrt 2 * ‖ofCplx z‖ := by
  have hre : |z.re| ≤ ‖ofCplx z‖ := by
    have h := norm_le_pi_norm (ofCplx z) 1
    simpa [ofCplx] using h
  have him : |z.im| ≤ ‖ofCplx z‖ := by
    have h := norm_le_pi_norm (ofCplx z) 2
    simpa [ofCplx] using h
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ 2 * ‖ofCplx z‖ ^ 2 := by
    nlinarith [abs_nonneg z.re, abs_nonneg z.im, sq_abs z.re, sq_abs z.im, hre, him]
  have h3 : ‖z‖ ≤ Real.sqrt (2 * ‖ofCplx z‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg z)]
    exact Real.sqrt_le_sqrt (by rw [hsq]; exact h2)
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The converse comparison: the complex modulus is at most `√2` times the model
norm, i.e. a plane point of modulus `r` has model norm at least `r / √2`. -/
theorem norm_ofCplx_ge (z : ℂ) : ‖z‖ / Real.sqrt 2 ≤ ‖ofCplx z‖ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_iff₀ h2]
  linarith [norm_le_sqrt_two_mul_norm_ofCplx z]

/-- Conjugation of the block model: the real coordinate is fixed and the complex
coordinate is conjugated.  It is the other complex place. -/
noncomputable def conjPt (x : Pt) : Pt := ![x 0, x 1, -x 2]

theorem conjPt_ofCplx (z : ℂ) : conjPt (ofCplx z) = ofCplx (starRingEnd ℂ z) := by
  funext i
  fin_cases i <;> simp [conjPt, ofCplx]

/-- **The conjugate place negates the phase.**  The conjugate multiplier's
log-rate is the conjugate log-rate: the real (modulus) part is unchanged and the
imaginary (phase) part changes sign. -/
theorem log_conj {c : ℂ} (harg : c.arg ≠ Real.pi) :
    Complex.log (starRingEnd ℂ c) = starRingEnd ℂ (Complex.log c) :=
  Complex.log_conj c harg

theorem log_conj_re {c : ℂ} (harg : c.arg ≠ Real.pi) :
    (Complex.log (starRingEnd ℂ c)).re = (Complex.log c).re := by
  rw [log_conj harg, Complex.conj_re]

theorem log_conj_im {c : ℂ} (harg : c.arg ≠ Real.pi) :
    (Complex.log (starRingEnd ℂ c)).im = -(Complex.log c).im := by
  rw [log_conj harg, Complex.conj_im]

/-- **The arc of the conjugate place is the conjugate arc**: the modulus is the
same at every parameter and the phase runs backwards. -/
theorem arcThrough_conj {w₀ c : ℂ} (harg : c.arg ≠ Real.pi) (t : ℝ) :
    conjPt (arcThrough w₀ c t)
      = arcThrough (starRingEnd ℂ w₀) (starRingEnd ℂ c) t := by
  rw [arcThrough, arcThrough, conjPt_ofCplx, map_mul, ← scaleFlow_conj c harg]

/-- **The net statement for the conjugate place, with the constants of the
original one.**  The arc is placed for the conjugate multiplier
`conj c` (the conjugate spiral), and the length/error constants are those of
`(w₀, c)`, because conjugation preserves both moduli. -/
theorem exists_eps_net_long_segment_conj {E : Set Pt} {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (harg : c.arg ≠ Real.pi)
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hE : ∀ x ∈ E, ptMul a x ∈ E)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      arcThrough (starRingEnd ℂ w₀) (starRingEnd ℂ c) t ∈ E)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ m : ℕ, 0 < m ∧ ∃ t_m : ℝ, 0 < t_m ∧
      R ≤ t_m * ‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖ ∧
      ‖w₀‖ * ‖cplxOf a‖ ^ m * t_m ^ 2 * ‖Complex.log c‖ ^ 2 < ε ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t_m, ∃ y ∈ E,
        ‖y - ofCplx ((cplxOf a) ^ m * starRingEnd ℂ w₀
          * (1 + (s : ℂ) * Complex.log (starRingEnd ℂ c)))‖ < ε) := by
  have hc0' : starRingEnd ℂ c ≠ 0 := by
    simpa using hc0
  have hc1' : starRingEnd ℂ c ≠ 1 := by
    intro h
    exact hc1 (by simpa using congrArg (starRingEnd ℂ) h)
  have hw₀' : starRingEnd ℂ w₀ ≠ 0 := by
    simpa using hw₀
  have hlen : ‖Complex.log (starRingEnd ℂ c)‖ = ‖Complex.log c‖ := by
    rw [log_conj harg]
    exact Complex.norm_conj _
  have hwn : ‖starRingEnd ℂ w₀‖ = ‖w₀‖ := Complex.norm_conj w₀
  obtain ⟨m, hm, t_m, htm, h1, h2, h3⟩ :=
    exists_eps_net_long_segment (E := E) (a := a) (w₀ := starRingEnd ℂ w₀)
      (c := starRingEnd ℂ c) hρ hw₀' hc0' hc1' ht' hE harc hε hR
  have h1' : R ≤ t_m * ‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖ := by
    rw [← hwn, ← hlen]
    exact h1
  have h2' : ‖w₀‖ * ‖cplxOf a‖ ^ m * t_m ^ 2 * ‖Complex.log c‖ ^ 2 < ε := by
    rw [← hwn, ← hlen]
    exact h2
  exact ⟨m, hm, t_m, htm, h1', h2', h3⟩

/-! ### The torus form -/

/-- The quotient map of the torus does not increase distances. -/
theorem dist_mk_le (L : AddSubgroup Pt) (x y : Pt) :
    dist ((QuotientAddGroup.mk' L) x) ((QuotientAddGroup.mk' L) y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- **Lemma 4.6 in the torus.**  If a set `Y` of `Torus L` is invariant under the
member `a` and meets the arc `arcThrough w₀ c` (both read in the lift), then `Y`
contains `ε`-nets for tangent segments of every length, the length being
`t_m ‖cplxOf a‖^m ‖w₀‖ ‖log c‖ ≥ R`. -/
theorem exists_eps_net_long_segment_torus {L : AddSubgroup Pt} {Y : Set (Torus L)}
    {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ m : ℕ, 0 < m ∧ ∃ t_m : ℝ, 0 < t_m ∧
      R ≤ t_m * ‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t_m, ∃ y ∈ Y,
        dist y ((QuotientAddGroup.mk' L)
          (ofCplx ((cplxOf a) ^ m * w₀ * (1 + (s : ℂ) * Complex.log c)))) < ε) := by
  obtain ⟨m, hm, t_m, htm, hlen, _herr, hnet⟩ :=
    exists_eps_net_long_segment (E := (QuotientAddGroup.mk' L) ⁻¹' Y) (a := a)
      hρ hw₀ hc0 hc1 ht' (fun x hx => hinv x hx) harc hε hR
  refine ⟨m, hm, t_m, htm, hlen, fun s hs => ?_⟩
  obtain ⟨y, hy, hdist⟩ := hnet s hs
  exact ⟨(QuotientAddGroup.mk' L) y, hy,
    lt_of_le_of_lt (dist_mk_le L y _) hdist⟩

/-! ### Berend's conclusion in its literal form: arbitrarily long segments -/

/-- **Lemma 4.6, litotes form.**  For every `ε > 0` and every `R > 0`, the
`ε`-neighbourhood of `E` contains a line segment of length at least `R`:
there are `base dir ∈ Pt` with `R ≤ ‖dir‖` and every point `base + u • dir`,
`u ∈ [0,1]`, within `ε` of `E`.  Since `R` is arbitrary, `E` is an `ε`-net for
arbitrarily long line segments in `Pt`. -/
theorem exists_arbitrarily_long_segment {E : Set Pt} {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hE : ∀ x ∈ E, ptMul a x ∈ E)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', arcThrough w₀ c t ∈ E)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ base dir : Pt, R ≤ ‖dir‖ ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ E, ‖y - (base + u • dir)‖ < ε := by
  have hRpos : (0 : ℝ) < Real.sqrt 2 * |R| + 1 := by
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 := abs_nonneg R
    nlinarith
  obtain ⟨m, hm, t_m, htm, hlen, _herr, hnet⟩ :=
    exists_eps_net_long_segment (E := E) (a := a) hρ hw₀ hc0 hc1 ht' hE harc hε
      hRpos
  refine ⟨ofCplx ((cplxOf a) ^ m * w₀),
    t_m • ofCplx ((cplxOf a) ^ m * w₀ * Complex.log c), ?_, ?_⟩
  · -- the length of the segment in the model norm
    have hdir : t_m • ofCplx ((cplxOf a) ^ m * w₀ * Complex.log c)
        = ofCplx ((t_m : ℂ) * ((cplxOf a) ^ m * w₀ * Complex.log c)) := by
      rw [ofCplx_real_smul]
    rw [hdir]
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hone : ‖((t_m : ℂ) * ((cplxOf a) ^ m * w₀ * Complex.log c))‖
        = t_m * (‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htm,
        norm_mul, norm_mul, norm_pow]
    have hge := norm_ofCplx_ge ((t_m : ℂ) * ((cplxOf a) ^ m * w₀ * Complex.log c))
    rw [hone] at hge
    refine le_trans ?_ hge
    rw [le_div_iff₀ hpos]
    nlinarith [hlen, le_abs_self R, hpos]
  · -- the net property, reparametrised from `[0,t_m]` to `[0,1]`
    intro u hu
    have hs : u * t_m ∈ Set.Icc (0 : ℝ) t_m :=
      ⟨mul_nonneg hu.1 htm.le, by nlinarith [hu.2, htm]⟩
    obtain ⟨y, hy, hdist⟩ := hnet (u * t_m) hs
    refine ⟨y, hy, ?_⟩
    have hpt : ofCplx ((cplxOf a) ^ m * w₀) + u • (t_m • ofCplx ((cplxOf a) ^ m * w₀
          * Complex.log c))
        = ofCplx ((cplxOf a) ^ m * w₀ * (1 + ((u * t_m : ℝ) : ℂ) * Complex.log c)) := by
      rw [smul_smul, ← ofCplx_real_smul, ← ofCplx_add]
      congr 1
      push_cast
      ring
    rw [hpt]
    exact hdist

/-- **Lemma 4.6 in the torus, litotes form.**  The `ε`-neighbourhood of `Y`
(in the quotient metric) contains the image of a segment of length at least `R`.
This is the input of Berend's Proposition 4.2: long segments of a closed
invariant set in a compact torus force a translate of a one-parameter subgroup. -/
theorem exists_arbitrarily_long_segment_torus {L : AddSubgroup Pt} {Y : Set (Torus L)}
    {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ base dir : Pt, R ≤ ‖dir‖ ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Y,
        dist y ((QuotientAddGroup.mk' L) (base + u • dir)) < ε := by
  obtain ⟨base, dir, hlen, hseg⟩ :=
    exists_arbitrarily_long_segment (E := (QuotientAddGroup.mk' L) ⁻¹' Y) (a := a)
      hρ hw₀ hc0 hc1 ht' (fun x hx => hinv x hx) harc hε R
  refine ⟨base, dir, hlen, fun u hu => ?_⟩
  obtain ⟨y, hy, hdist⟩ := hseg u hu
  exact ⟨(QuotientAddGroup.mk' L) y, hy,
    lt_of_le_of_lt (dist_mk_le L y (base + u • dir)) hdist⟩

/-! ### Bridges: the repo's own arc and the actual expanding member

`BerendPlanarArc.arcPt` is the Lemma 4.5 arc through the plane point `1`; the arc
of this file is the same object translated to an arbitrary plane point `w₀`.
The final theorem is Lemma 4.6 stated for the invariant sets of the unit-prime
family `D.torusAct`, with the expanding member supplied by
`BerendExpandingMember.exists_mult_margin` (through
`BerendBlockLastMile.two_le_norm_cplxOf_of_normC`). -/

/-- The arc of `BerendPlanarArc` is the arc of this file through `w₀ = 1`. -/
theorem arcPt_eq_arcThrough (c : ℂ) (t : ℝ) : arcPt c t = arcThrough 1 c t := by
  rw [arcPt, arcThrough, one_mul]

/-- **Lemma 4.6 for the one-expanding-member context of the unit-prime model.**
If `Y ⊆ Torus L` is invariant under the whole family `D.torusAct`, the member
`D.mult u j` expands the complex plane (`16 ≤ normC`), and `Y` meets the lift of
the arc `arcThrough w₀ c`, then `Y` meets the `ε`-neighbourhood of the image of a
segment of every length `R`. -/
theorem exists_arbitrarily_long_segment_torusAct {K : Type*} [Field K]
    {L : AddSubgroup Pt} {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪)
    (u : 𝒪ˣ) (j : ℕ) (hC : 16 ≤ normC (D.mult u j))
    {Y : Set (Torus L)} (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {w₀ c : ℂ} {t' : ℝ} (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ base dir : Pt, R ≤ ‖dir‖ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Y,
        dist y ((QuotientAddGroup.mk' L) (base + s • dir)) < ε := by
  have hρ : 1 < ‖cplxOf (D.mult u j)‖ :=
    lt_of_lt_of_le (by norm_num) (BerendBlockLastMile.two_le_norm_cplxOf_of_normC hC)
  have hinv' : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul (D.mult u j) x) ∈ Y := by
    intro x hx
    have h := hinv (u, j) (Set.mem_image_of_mem (D.torusAct (u, j)) hx)
    rwa [D.torusAct_mk', D.family_act_eq_ptMul] at h
  exact exists_arbitrarily_long_segment_torus hρ hw₀ hc0 hc1 ht' hinv' harc hε R

/-! ## 7. From ε-nets of long segments to genuine long segments

Berend's Lemma 4.6 gives `ε`-nets for arbitrarily long segments; Proposition 4.2
then passes to the limit and finds a translate of an infinite closed subgroup.
The passage to the limit has two halves, both proved here for the block model:

* `segment_subset_of_eps_nets` — the analytic half: if a closed `Y` meets the
  `1/(k+1)`-neighbourhood of segments whose base classes converge in the torus
  and whose unit directions converge (lengths growing at least linearly), then
  `Y` contains the limiting segment;
* `exists_segment_subset` — the compactness half: the compact torus and the
  compact unit sphere of `Pt` supply the convergent subsequence, so *a closed
  invariant `Y` meeting the lift of the Lemma 4.5 arc contains a nontrivial
  segment*.  This is the input of Proposition 4.2 and the first genuinely
  geometric conclusion drawn from Lemma 4.6.

Neither statement concludes `Y = univ`: the closed-subgroup/irreducibility
argument of Berend's Propositions 4.2–4.3 is not in this file. -/

/-- **The limiting step of Berend's Proposition 4.2.**  Let `Y ⊆ Torus L` be
closed, let the base classes `mk' (base k)` converge to `b`, let the unit
directions `‖dir k‖⁻¹ • dir k` converge to `e`, let the lengths grow at least
linearly, `k ≤ ‖dir k‖`, and let `Y` meet the `1/(k+1)`-neighbourhood of the
segment `{base k + u • dir k | u ∈ [0,1]}`.  Then `Y` contains the limiting
segment `{b + s • e | s ≥ 0}`. -/
theorem segment_subset_of_eps_nets {L : AddSubgroup Pt} {Y : Set (Torus L)}
    (hY : IsClosed Y) {base : ℕ → Pt} {b : Torus L}
    (hb : Tendsto (fun k => (QuotientAddGroup.mk' L) (base k)) atTop (𝓝 b))
    {dir : ℕ → Pt} {e : Pt}
    (he : Tendsto (fun k => (‖dir k‖)⁻¹ • dir k) atTop (𝓝 e))
    (hlen : ∀ k : ℕ, (k : ℝ) ≤ ‖dir k‖)
    (hnet : ∀ k : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Y,
      dist y ((QuotientAddGroup.mk' L) (base k + u • dir k)) < 1 / (k + 1)) :
    ∀ s : ℝ, 0 ≤ s → b + (QuotientAddGroup.mk' L) (s • e) ∈ Y := by
  intro s hs
  have hcl : b + (QuotientAddGroup.mk' L) (s • e) ∈ closure Y := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- the approximations converge to the limiting point
    have htend : Tendsto
        (fun k : ℕ => (QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k))
        atTop (𝓝 (b + (QuotientAddGroup.mk' L) (s • e))) := by
      have hsplit : ∀ k : ℕ, (QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k)
          = (QuotientAddGroup.mk' L) (base k)
            + (QuotientAddGroup.mk' L) ((s / ‖dir k‖) • dir k) := fun k => map_add _ _ _
      have h2 : Tendsto (fun k : ℕ => (QuotientAddGroup.mk' L) ((s / ‖dir k‖) • dir k))
          atTop (𝓝 ((QuotientAddGroup.mk' L) (s • e))) := by
        refine (continuous_quotient_mk'.tendsto _).comp ?_
        have h4 : Tendsto (fun k : ℕ => s • ((‖dir k‖)⁻¹ • dir k)) atTop (𝓝 (s • e)) :=
          he.const_smul s
        refine h4.congr' ?_
        filter_upwards with k
        rw [smul_smul, div_eq_mul_inv]
      have := hb.add h2
      refine this.congr' ?_
      filter_upwards with k
      exact (hsplit k).symm
    -- three eventual conditions
    have e1 : ∀ᶠ k : ℕ in atTop,
        dist ((QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k))
          (b + (QuotientAddGroup.mk' L) (s • e)) < ε / 2 :=
      htend.eventually (Metric.ball_mem_nhds _ (by linarith))
    have e2 : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / (k + 1) < ε / 2 := by
      filter_upwards [eventually_ge_atTop (Nat.ceil (2 / ε))] with k hk
      have hk' : 2 / ε ≤ (k : ℝ) :=
        le_trans (Nat.le_ceil (2 / ε)) (by exact_mod_cast hk)
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hk0]
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      have hmul : ε / 2 * (2 / ε) = 1 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hk' hε2.le]
    have e3 : ∀ᶠ k : ℕ in atTop, s / ‖dir k‖ ≤ 1 := by
      filter_upwards [eventually_ge_atTop (max 1 (Nat.ceil s))] with k hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (le_trans (le_max_left 1 (Nat.ceil s)) hk)
      have hks : s ≤ (k : ℝ) := by
        have h1 : Nat.ceil s ≤ k := le_trans (le_max_right 1 (Nat.ceil s)) hk
        exact le_trans (Nat.le_ceil s) (by exact_mod_cast h1)
      have hk0 : (0 : ℝ) < ‖dir k‖ := lt_of_lt_of_le (by linarith) (hlen k)
      rw [div_le_one hk0]
      exact le_trans hks (hlen k)
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
      (e1.and (e2.and (e3.and (eventually_ge_atTop 1)))).exists
    have hkpos : (0 : ℝ) < ‖dir k‖ := by
      have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
      linarith [hlen k]
    have hu : s / ‖dir k‖ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs hkpos.le, hk3⟩
    obtain ⟨y, hyY, hydist⟩ := hnet k _ hu
    refine ⟨y, hyY, ?_⟩
    have hsym : dist (b + (QuotientAddGroup.mk' L) (s • e))
        ((QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k))
        = dist ((QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k))
          (b + (QuotientAddGroup.mk' L) (s • e)) := dist_comm _ _
    calc dist (b + (QuotientAddGroup.mk' L) (s • e)) y
        ≤ dist (b + (QuotientAddGroup.mk' L) (s • e))
            ((QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k))
          + dist ((QuotientAddGroup.mk' L) (base k + (s / ‖dir k‖) • dir k)) y :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [hsym]
          exact add_lt_add hk1 (lt_trans (by rw [dist_comm]; exact hydist) hk2)
      _ = ε := by ring
  rwa [hY.closure_eq] at hcl

/-- **A closed invariant set meeting the lift of the Lemma 4.5 arc contains a
nontrivial ray** (the first half of Berend's Proposition 4.2).

The hypotheses are exactly those of `exists_eps_net_long_segment_torus` plus
compactness of the torus.  The conclusion is the ray statement
`{b + s • e | 0 ≤ s} ⊆ Y` with `e ≠ 0` in the complex plane, obtained by
extracting from the `ε`-net segments of Lemma 4.6 a subsequence whose base
classes and unit directions converge.  Planarity of `e` is preserved in the
limit because every approximating tangent direction is planar. -/
theorem exists_ray_subset {L : AddSubgroup Pt} [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (b : Torus L) (e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s : ℝ, 0 ≤ s → b + (QuotientAddGroup.mk' L) (s • e) ∈ Y := by
  classical
  -- for each `k`, Lemma 4.6 gives a long segment whose `(1/(k+1))`-net is in `Y`
  have hex : ∀ k : ℕ, ∃ (m : ℕ) (t_m : ℝ), 0 < m ∧ 0 < t_m ∧
      Real.sqrt 2 * k + 1 ≤ t_m * ‖cplxOf a‖ ^ m * ‖w₀‖ * ‖Complex.log c‖ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t_m, ∃ y ∈ Y,
        dist y ((QuotientAddGroup.mk' L)
          (ofCplx ((cplxOf a) ^ m * w₀ * (1 + (s : ℂ) * Complex.log c)))) < 1 / (k + 1)) := by
    intro k
    have hR : (0 : ℝ) < Real.sqrt 2 * k + 1 := by positivity
    obtain ⟨m, hm, t_m, htm, h1, h2⟩ :=
      exists_eps_net_long_segment_torus (L := L) (Y := Y) hρ hw₀ hc0 hc1 ht' hinv harc
        (ε := 1 / (k + 1)) (R := Real.sqrt 2 * k + 1) (by positivity) hR
    exact ⟨m, t_m, hm, htm, h1, h2⟩
  choose m t_m hm htm hlen hnet using hex
  -- the base points and the segment directions at scale `k`
  set base : ℕ → Pt := fun k => ofCplx ((cplxOf a) ^ (m k) * w₀) with hbase
  set dir : ℕ → Pt := fun k => t_m k • ofCplx ((cplxOf a) ^ (m k) * w₀ * Complex.log c)
    with hdir
  -- the reparametrisation identity
  have hpt : ∀ k : ℕ, ∀ u : ℝ, base k + u • dir k
      = ofCplx ((cplxOf a) ^ (m k) * w₀ * (1 + ((u * t_m k : ℝ) : ℂ) * Complex.log c)) := by
    intro k u
    rw [hbase, hdir, smul_smul, ← ofCplx_real_smul, ← ofCplx_add]
    congr 1
    push_cast
    ring
  -- lengths: the model norm dominates the complex modulus up to `√2`
  have hMpos : ∀ k : ℕ, (0 : ℝ) < ‖cplxOf a‖ ^ (m k) * ‖w₀‖ * ‖Complex.log c‖ := by
    intro k
    have hL : 0 < ‖Complex.log c‖ := by
      rw [norm_pos_iff]
      exact log_ne_zero hc0 hc1
    have hw : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
    have hρ' : 0 < ‖cplxOf a‖ ^ (m k) := pow_pos (by linarith) _
    exact mul_pos (mul_pos hρ' hw) hL
  have hdir_ge : ∀ k : ℕ,
      t_m k * (‖cplxOf a‖ ^ (m k) * ‖w₀‖ * ‖Complex.log c‖) / Real.sqrt 2
        ≤ ‖dir k‖ := by
    intro k
    have hge := norm_ofCplx_ge ((t_m k : ℂ) * ((cplxOf a) ^ (m k) * w₀ * Complex.log c))
    have hnorm : ‖((t_m k : ℂ) * ((cplxOf a) ^ (m k) * w₀ * Complex.log c))‖
        = t_m k * (‖cplxOf a‖ ^ (m k) * ‖w₀‖ * ‖Complex.log c‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htm k),
        norm_mul, norm_mul, norm_pow]
    have hdir' : dir k
        = ofCplx ((t_m k : ℂ) * ((cplxOf a) ^ (m k) * w₀ * Complex.log c)) := by
      rw [hdir, ofCplx_real_smul]
    have hg' : t_m k * (‖cplxOf a‖ ^ (m k) * ‖w₀‖ * ‖Complex.log c‖) / Real.sqrt 2
        ≤ ‖ofCplx ((t_m k : ℂ) * ((cplxOf a) ^ (m k) * w₀ * Complex.log c))‖ := by
      rw [← hnorm]
      exact hge
    rw [hdir']
    exact hg'
  have hdir_pos : ∀ k : ℕ, (0 : ℝ) < ‖dir k‖ := by
    intro k
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact lt_of_lt_of_le (div_pos (mul_pos (htm k) (hMpos k)) hpos) (hdir_ge k)
  have hlen' : ∀ k : ℕ, (k : ℝ) ≤ ‖dir k‖ := by
    intro k
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    refine le_trans ?_ (hdir_ge k)
    rw [le_div_iff₀ hpos]
    nlinarith [hlen k]
  -- the nets, in the parametrisation of the limiting step
  have hnet' : ∀ k : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Y,
      dist y ((QuotientAddGroup.mk' L) (base k + u • dir k)) < 1 / (k + 1) := by
    intro k u hu
    have hs : u * t_m k ∈ Set.Icc (0 : ℝ) (t_m k) :=
      ⟨mul_nonneg hu.1 (le_of_lt (htm k)), by nlinarith [hu.2, htm k]⟩
    obtain ⟨y, hy, hd⟩ := hnet k (u * t_m k) hs
    exact ⟨y, hy, by rw [hpt k u]; exact hd⟩
  -- compactness: a subsequence along which the base class and unit direction converge
  have hunit : ∀ k : ℕ, (‖dir k‖)⁻¹ • dir k ∈ Metric.sphere (0 : Pt) 1 := by
    intro k
    have hk : (0 : ℝ) < ‖dir k‖ := hdir_pos k
    show dist ((‖dir k‖)⁻¹ • dir k) (0 : Pt) = 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk,
      inv_mul_cancel₀ (ne_of_gt hk)]
  obtain ⟨a₀, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq
    (fun k : ℕ => ((QuotientAddGroup.mk' L) (base k),
      (⟨(‖dir k‖)⁻¹ • dir k, hunit k⟩ : ↥(Metric.sphere (0 : Pt) 1))))
  have hb : Tendsto (fun k => (QuotientAddGroup.mk' L) (base (φ k))) atTop (𝓝 a₀.1) := by
    have h := (continuous_fst.tendsto a₀).comp hconv
    simpa [Function.comp_def] using h
  have he : Tendsto (fun k => (‖dir (φ k)‖)⁻¹ • dir (φ k)) atTop (𝓝 (a₀.2 : Pt)) := by
    have h := (continuous_subtype_val.tendsto a₀.2).comp
      ((continuous_snd.tendsto a₀).comp hconv)
    simpa [Function.comp_def] using h
  have hlen_sub : ∀ k : ℕ, (k : ℝ) ≤ ‖dir (φ k)‖ := by
    intro k
    refine le_trans ?_ (hlen' (φ k))
    exact_mod_cast hφ.id_le k
  have hnet_sub : ∀ k : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Y,
      dist y ((QuotientAddGroup.mk' L) (base (φ k) + u • dir (φ k))) < 1 / (k + 1) := by
    intro k u hu
    obtain ⟨y, hy, hd⟩ := hnet' (φ k) u hu
    refine ⟨y, hy, lt_of_lt_of_le hd (one_div_le_one_div_of_le (by positivity) ?_)⟩
    exact_mod_cast Nat.succ_le_succ (hφ.id_le k)
  have hseg := segment_subset_of_eps_nets (L := L) (Y := Y) hY (base := fun k => base (φ k))
    (b := a₀.1) (dir := fun k => dir (φ k)) (e := (a₀.2 : Pt)) hb he hlen_sub hnet_sub
  have hdir_plane : ∀ k : ℕ, (‖dir k‖)⁻¹ • dir k ∈ cplxPlane := by
    intro k
    show ((‖dir k‖)⁻¹ • dir k) 0 = 0
    simp [hdir, ofCplx]
  have heplane : (a₀.2 : Pt) ∈ cplxPlane :=
    cplxPlane_closed.mem_of_tendsto he (Eventually.of_forall fun k => hdir_plane (φ k))
  refine ⟨a₀.1, (a₀.2 : Pt), heplane, ?_, hseg⟩
  intro hzero
  have hone : ‖(a₀.2 : Pt)‖ = 1 := by
    have h := a₀.2.property
    rwa [Metric.mem_sphere, dist_zero_right] at h
  rw [hzero, norm_zero] at hone
  exact zero_ne_one hone

/-- The unit-interval segment form of `exists_ray_subset`. -/
theorem exists_segment_subset {L : AddSubgroup Pt} [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (b : Torus L) (e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, b + (QuotientAddGroup.mk' L) (s • e) ∈ Y := by
  obtain ⟨b, e, heplane, he, hray⟩ :=
    exists_ray_subset hY hρ hw₀ hc0 hc1 ht' hinv harc
  exact ⟨b, e, heplane, he, fun s hs => hray s hs.1⟩

/-- **A nontrivial planar-direction ray in an invariant set of the unit-prime
family.**  This is `exists_ray_subset` for the actual family `D.torusAct` and
one expanding member. -/
theorem exists_ray_subset_torusAct {K : Type*} [Field K]
    {L : AddSubgroup Pt} {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪)
    (u : 𝒪ˣ) (j : ℕ) (hC : 16 ≤ normC (D.mult u j)) [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {w₀ c : ℂ} {t' : ℝ} (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (b : Torus L) (e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s : ℝ, 0 ≤ s → b + (QuotientAddGroup.mk' L) (s • e) ∈ Y := by
  have hρ : 1 < ‖cplxOf (D.mult u j)‖ :=
    lt_of_lt_of_le (by norm_num) (BerendBlockLastMile.two_le_norm_cplxOf_of_normC hC)
  have hinv' : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul (D.mult u j) x) ∈ Y := by
    intro x hx
    have h := hinv (u, j) (Set.mem_image_of_mem (D.torusAct (u, j)) hx)
    rwa [D.torusAct_mk', D.family_act_eq_ptMul] at h
  exact exists_ray_subset hY hρ hw₀ hc0 hc1 ht' hinv' harc

/-- The unit-interval segment form of `exists_ray_subset_torusAct`. -/
theorem exists_segment_subset_torusAct {K : Type*} [Field K]
    {L : AddSubgroup Pt} {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪)
    (u : 𝒪ˣ) (j : ℕ) (hC : 16 ≤ normC (D.mult u j)) [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {w₀ c : ℂ} {t' : ℝ} (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t', (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (b : Torus L) (e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, b + (QuotientAddGroup.mk' L) (s • e) ∈ Y := by
  obtain ⟨b, e, heplane, he, hray⟩ :=
    exists_ray_subset_torusAct D u j hC hY hinv hw₀ hc0 hc1 ht' harc
  exact ⟨b, e, heplane, he, fun s hs => hray s hs.1⟩

/-! ## 8. Circle × segment = annulus: the sweep lemma

A `|λ| = 1` multiplier of infinite order spreads a plane point over its whole
circle (`BerendPlanarArc.circle_ofCplx_in_lift`).  A single circle, however, does
**not** thicken under an expanding multiplier: the union of the circles of radii
`ρ^n s` is closed invariant and has empty interior, so it is a counterexample to
"a circle plus one expanding member gives an annulus".  What does thicken is a
*segment*: sweeping a segment which avoids `0` by the unit circle produces the
annulus between the moduli of its endpoints.  This section proves that sweep and
composes it with `BerendBlockLastMile.plane_unbounded_of_annulus`, so that the
following named input — *the lift contains one nontrivial plane segment* —
suffices for the unbounded plane, and hence (with `L`-saturation and
`CofinalPlane`) for Stage I itself.  §7 supplies such a segment in the torus;
is not done here.  `BerendSegmentLift` subsequently lifts the full affine ray,
but its compactness-selected basepoint need not belong to `cplxPlane`. -/

/-- **Sweeping a segment by the unit circle.**  If `W ⊆ ℂ` is closed under
multiplication by unit complex numbers and contains the segment
`{b + s e | s ∈ [0,1]}`, which avoids `0`, then every `z` whose modulus is the
modulus of a point of the segment lies in `W`. -/
theorem smul_unitCircle_mem_of_norm_eq_segment {W : Set ℂ}
    (hunit : ∀ μ ∈ unitCircle, ∀ z ∈ W, μ * z ∈ W)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ∈ W)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0) :
    ∀ z : ℂ, (∃ s ∈ Set.Icc (0 : ℝ) 1, ‖z‖ = ‖b + s • e‖) → z ∈ W := by
  rintro z ⟨s, hs, hzs⟩
  have hsegne : b + s • e ≠ 0 := hne s hs
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hzs
    exact hsegne (norm_eq_zero.mp hzs.symm)
  have hμ : z / (b + s • e) ∈ unitCircle := by
    rw [mem_unitCircle, norm_div, hzs, div_self (norm_ne_zero_iff.mpr hsegne)]
  have hz : z = (z / (b + s • e)) * (b + s • e) := by
    field_simp
  rw [hz]
  exact hunit _ hμ _ (hseg s hs)

/-- **The annulus between the endpoint moduli of a segment.**  Under the same
hypotheses, every `z` with `min ‖b‖ ‖b+e‖ ≤ ‖z‖ ≤ max ‖b‖ ‖b+e‖` lies in `W`:
the modulus function `s ↦ ‖b + s e‖` is continuous, so it attains every
intermediate value, and the circle of that radius is swept out. -/
theorem annulus_subset_of_segment {W : Set ℂ}
    (hunit : ∀ μ ∈ unitCircle, ∀ z ∈ W, μ * z ∈ W)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ∈ W)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0) :
    ∀ z : ℂ, min ‖b‖ ‖b + e‖ ≤ ‖z‖ → ‖z‖ ≤ max ‖b‖ ‖b + e‖ → z ∈ W := by
  intro z h1 h2
  have hcont : ContinuousOn (fun s : ℝ => ‖b + s • e‖) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hmem : ‖z‖ ∈ (fun s : ℝ => ‖b + s • e‖) '' Set.Icc (0 : ℝ) 1 := by
    rcases le_total ‖b‖ ‖b + e‖ with hle | hle
    · have hmin : min ‖b‖ ‖b + e‖ = ‖b‖ := min_eq_left hle
      have hmax : max ‖b‖ ‖b + e‖ = ‖b + e‖ := max_eq_right hle
      have hsub := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one hcont
      refine hsub ⟨?_, ?_⟩
      · rw [hmin] at h1
        simpa using h1
      · rw [hmax] at h2
        simpa using h2
    · have hmin : min ‖b‖ ‖b + e‖ = ‖b + e‖ := min_eq_right hle
      have hmax : max ‖b‖ ‖b + e‖ = ‖b‖ := max_eq_left hle
      have hsub := intermediate_value_Icc' (a := (0 : ℝ)) (b := 1) zero_le_one hcont
      refine hsub ⟨?_, ?_⟩
      · rw [hmin] at h1
        simpa using h1
      · rw [hmax] at h2
        simpa using h2
  obtain ⟨s, hs, hsr⟩ := hmem
  exact smul_unitCircle_mem_of_norm_eq_segment hunit hseg hne z ⟨s, hs, hsr.symm⟩

/-- **The annulus in the lift, from a plane segment in the lift.**  If a set
`E ⊆ Pt` contains the plane segment through `b` with direction `e`, avoids the
origin along it, and is closed under multiplication of its plane points by unit
complex numbers, then the plane annulus between the endpoint moduli is in `E`.
This is the exact `hann` shape of `BerendBlockLastMile.plane_unbounded_of_annulus`. -/
theorem cplxPlane_annulus_subset_of_segment {E : Set Pt}
    (hunit : ∀ μ ∈ unitCircle, ∀ z : ℂ, ofCplx z ∈ E → ofCplx (μ * z) ∈ E)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ofCplx (b + s • e) ∈ E)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0) :
    ∀ w : Pt, w ∈ cplxPlane → min ‖b‖ ‖b + e‖ ≤ ‖cplxOf w‖ →
      ‖cplxOf w‖ ≤ max ‖b‖ ‖b + e‖ → w ∈ E := by
  intro w hw h1 h2
  have h := annulus_subset_of_segment (W := {z : ℂ | ofCplx z ∈ E})
    (fun μ hμ z hz => hunit μ hμ z hz) hseg hne (cplxOf w) h1 h2
  have h' : ofCplx (cplxOf w) ∈ E := h
  rwa [eq_ofCplx_cplxOf hw] at h'

/-- **The unbounded plane from one plane segment and one expanding member.**
Composing the annulus sweep with `BerendBlockLastMile.plane_unbounded_of_annulus`:
a closed-`ptMul a` set containing a plane segment that avoids `0`, closed under
unit-circle rotations of its plane points, and with the annulus at least as wide
as the expansion ratio `‖cplxOf a‖`, contains every plane point of modulus at
least `min ‖b‖ ‖b + e‖`. -/
theorem plane_unbounded_of_segment {E : Set Pt} {a : Pt}
    (hm : 2 ≤ ‖cplxOf a‖) (hE : ∀ x ∈ E, ptMul a x ∈ E)
    (hunit : ∀ μ ∈ unitCircle, ∀ z : ℂ, ofCplx z ∈ E → ofCplx (μ * z) ∈ E)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ofCplx (b + s • e) ∈ E)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0)
    (h1pos : 0 < min ‖b‖ ‖b + e‖)
    (hgap : ‖cplxOf a‖ * min ‖b‖ ‖b + e‖ ≤ max ‖b‖ ‖b + e‖) :
    ∀ w : Pt, w ∈ cplxPlane → min ‖b‖ ‖b + e‖ ≤ ‖cplxOf w‖ → w ∈ E := by
  refine BerendBlockLastMile.plane_unbounded_of_annulus hm hE h1pos ?_ hgap ?_
  · exact le_trans (min_le_left _ _) (le_max_left _ _)
  · intro w hw h2 h3
    exact cplxPlane_annulus_subset_of_segment hunit hseg hne w hw h2 h3

/-! ### The capstone: Stage I from a plane segment

Composing the sweep lemma with the already-proved last mile
(`BerendBlockLastMile.eq_univ_of_annulus_subset`, `torus_eq_univ_of_annulus`).
The named inputs are exactly: **one nontrivial plane segment in the lift** (which
§7 produces in the torus; path lifting for a discrete lattice upgrades it), the
unit-circle closure input (`|λ| = 1` branch of Lemma 4.5), one expanding member,
`L`-saturation and `CofinalPlane`.  None of these is `CplxMultiplierDense`, none
is equivalent to `Y = univ`, and no Stage I claim is made without them. -/

/-- **Stage I for a closed `L`-saturated set containing one plane segment.** -/
theorem eq_univ_of_plane_segment {L : AddSubgroup Pt} (hc : CofinalPlane L)
    {E : Set Pt} (hE : IsClosed E) (hsat : ∀ l ∈ L, ∀ x ∈ E, x + l ∈ E)
    {a : Pt} (hm : 2 ≤ ‖cplxOf a‖) (hinv : ∀ x ∈ E, ptMul a x ∈ E)
    (hunit : ∀ μ ∈ unitCircle, ∀ z : ℂ, ofCplx z ∈ E → ofCplx (μ * z) ∈ E)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ofCplx (b + s • e) ∈ E)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0)
    (h1pos : 0 < min ‖b‖ ‖b + e‖)
    (hgap : ‖cplxOf a‖ * min ‖b‖ ‖b + e‖ ≤ max ‖b‖ ‖b + e‖) :
    E = univ :=
  BerendBlockLastMile.eq_univ_of_annulus_subset hc hE hsat hm hinv h1pos
    (le_trans (min_le_left _ _) (le_max_left _ _)) hgap
    (fun w hw h2 h3 => cplxPlane_annulus_subset_of_segment hunit hseg hne w hw h2 h3)

/-- **Stage I in torus form from one plane segment.** -/
theorem torus_eq_univ_of_segment_data {L : AddSubgroup Pt} (hc : CofinalPlane L)
    {Y : Set (Torus L)} (hY : IsClosed Y) {a : Pt} (hm : 2 ≤ ‖cplxOf a‖)
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (hunit : ∀ μ ∈ unitCircle, ∀ z : ℂ, (QuotientAddGroup.mk' L) (ofCplx z) ∈ Y →
      (QuotientAddGroup.mk' L) (ofCplx (μ * z)) ∈ Y)
    {b e : ℂ} (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (QuotientAddGroup.mk' L) (ofCplx (b + s • e)) ∈ Y)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, b + s • e ≠ 0)
    (h1pos : 0 < min ‖b‖ ‖b + e‖)
    (hgap : ‖cplxOf a‖ * min ‖b‖ ‖b + e‖ ≤ max ‖b‖ ‖b + e‖) :
    Y = univ := by
  have hpre : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsat : ∀ l ∈ L, ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, x + l ∈
      (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro l hl x hx
    show (QuotientAddGroup.mk' L) (x + l) ∈ Y
    rw [map_add]
    have h0 : (QuotientAddGroup.mk' L) l = 0 := by
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa using hl
    rw [h0, add_zero]
    exact hx
  have hE : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    eq_univ_of_plane_segment (L := L) hc hpre hsat hm (fun x hx => hinv x hx)
      (fun μ hμ z hz => hunit μ hμ z hz) hseg hne h1pos hgap
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by rw [hE]; exact mem_univ x
  exact this

end BerendTangentNet
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendTangentNet.ofCplx_real_smul
#print axioms CubicTwoStage.BerendTangentNet.norm_ofCplx_le
#print axioms CubicTwoStage.BerendTangentNet.norm_exp_sub_one_sub_self_le
#print axioms CubicTwoStage.BerendTangentNet.scaleFlow_taylor
#print axioms CubicTwoStage.BerendTangentNet.hasDerivAt_scaleFlow
#print axioms CubicTwoStage.BerendTangentNet.exists_partial_scaled_arc_net
#print axioms CubicTwoStage.BerendTangentNet.arcThrough_taylor
#print axioms CubicTwoStage.BerendTangentNet.iterate_ptMul_ofCplx
#print axioms CubicTwoStage.BerendTangentNet.exists_eps_net_long_segment
#print axioms CubicTwoStage.BerendTangentNet.norm_le_sqrt_two_mul_norm_ofCplx
#print axioms CubicTwoStage.BerendTangentNet.norm_ofCplx_ge
#print axioms CubicTwoStage.BerendTangentNet.log_conj_re
#print axioms CubicTwoStage.BerendTangentNet.log_conj_im
#print axioms CubicTwoStage.BerendTangentNet.arcThrough_conj
#print axioms CubicTwoStage.BerendTangentNet.exists_eps_net_long_segment_conj
#print axioms CubicTwoStage.BerendTangentNet.dist_mk_le
#print axioms CubicTwoStage.BerendTangentNet.exists_eps_net_long_segment_torus
#print axioms CubicTwoStage.BerendTangentNet.exists_arbitrarily_long_segment
#print axioms CubicTwoStage.BerendTangentNet.exists_arbitrarily_long_segment_torus
#print axioms CubicTwoStage.BerendTangentNet.arcPt_eq_arcThrough
#print axioms CubicTwoStage.BerendTangentNet.exists_arbitrarily_long_segment_torusAct
#print axioms CubicTwoStage.BerendTangentNet.segment_subset_of_eps_nets
#print axioms CubicTwoStage.BerendTangentNet.exists_ray_subset
#print axioms CubicTwoStage.BerendTangentNet.exists_segment_subset
#print axioms CubicTwoStage.BerendTangentNet.exists_ray_subset_torusAct
#print axioms CubicTwoStage.BerendTangentNet.exists_segment_subset_torusAct
#print axioms CubicTwoStage.BerendTangentNet.smul_unitCircle_mem_of_norm_eq_segment
#print axioms CubicTwoStage.BerendTangentNet.annulus_subset_of_segment
#print axioms CubicTwoStage.BerendTangentNet.cplxPlane_annulus_subset_of_segment
#print axioms CubicTwoStage.BerendTangentNet.plane_unbounded_of_segment
#print axioms CubicTwoStage.BerendTangentNet.eq_univ_of_plane_segment
#print axioms CubicTwoStage.BerendTangentNet.torus_eq_univ_of_segment_data
