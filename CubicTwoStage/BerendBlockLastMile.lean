/-
# Block-model Stage I: the last mile, and the exact residual

Swarm `smw949qod`, member `m1`, direction `d2` (Stage I / axiom deletion).

`BEREND_SEC5_NOTES.md` §3.1 records that in the project's model
`Pt = ℝ × ℂ` the family acts by `(r, v) ↦ (σ₁(a) r, σ₂(a) v)`, so the complex
plane `{r = 0}` is *invariant* and there is no real eigenbasis to diagonalise
in.  This file supplies the **last mile of Stage I for that block model**, and
then states the residual of Stage I exactly.

## 1. The last mile (unconditional)

`cplxPlane = {x : Pt | x 0 = 0}` is the complex plane.  Say that `L` *is
cofinal in the plane* when

  `CofinalPlane L :  ∀ x ε R, 0 < ε → ∃ w ∈ cplxPlane, R ≤ ‖w‖ ∧ ∃ l ∈ L, ‖w + l - x‖ < ε`.

Then:

* `dense_unboundedPlane_add`: for every `R` the saturation
  `{w ∈ cplxPlane | R ≤ ‖w‖} + L` is **dense** in `Pt`;
* `eq_univ_of_unboundedPlane_subset`: a closed `L`-saturated set containing the
  unbounded part `{w ∈ cplxPlane | R ≤ ‖w‖}` of the plane is **everything**;
* `torus_eq_univ_of_unboundedPlane`: the same for a closed `Y ⊆ Pt ⧸ L`
  containing the image of that unbounded part.

`cofinalPlane_of_farAtHeight` derives `CofinalPlane L` from the two arithmetic
facts that the model supplies:

* `denseRangeProj L` — density of the real-coordinate projection of `L`, which
  `BerendTorusLastMile.dense_range_coord_of_irrational` produces as soon as two
  lattice elements have an irrational real-coordinate ratio;
* `SmallRealLargeNorm L` — lattice elements with arbitrarily small real
  coordinate and arbitrarily large norm (in the cubic model the images of
  `ε ^ (-m)`, `m → ∞`, for a unit with `|σ₁ ε| > 1`).

## 2. The exact residual of Stage I in the block model

`zeroNonisolatedFull_iff_unboundedPlane` states, for any toral family `F`:

  `ZeroNonisolatedFull F`  ↔  every closed invariant `Y` with `0` as a
   non-isolated point contains `π '' {w ∈ cplxPlane | R ≤ ‖w‖}` for **some** `R`.

The forward direction is the definition; the converse is §1 and uses **no**
diagonalisation, no ergodicity and no measure theory.  This mirrors
`BerendStageIClosure.zeroNonisolatedFull_iff_localFull`, which does the same for
the real-diagonal model with a coordinate box in place of the unbounded complex
plane.  It is the sharp form of the residual here: a *bounded* piece of the
plane does **not** suffice, because `π` is injective on the plane (the model
lattice meets it trivially) so the image of a bounded piece is compact, hence
never dense.

No `sorry`, no `axiom`, no assumed `Prop`: the audit at the end of the file
prints the axioms of every declaration.
-/
import CubicTwoStage.BerendTorusLastMile
import CubicTwoStage.BerendDichotomy
import CubicTwoStage.BerendEigenBridge

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendBlockLastMile

/-! ## 1. The complex plane in `Pt = Fin 3 → ℝ` -/

/-- The complex plane `{x : Pt | x 0 = 0}`: the real coordinate vanishes.  This
is an invariant plane of every multiplier of the unit–prime model. -/
def cplxPlane : Set Pt := {x | x 0 = 0}

/-- `cplxPlane` is the coordinate subspace with the real coordinate erased. -/
theorem cplxPlane_eq_coord :
    cplxPlane =
      (BerendSec4.coord (((Finset.univ.erase (0 : Fin 3)) : Finset (Fin 3)) : Set (Fin 3)) :
        Set Pt) := by
  ext x
  simp only [cplxPlane, Set.mem_ofPred_eq, SetLike.mem_coe, BerendSec4.mem_coord]
  constructor
  · intro h i hi
    have h0 : i = 0 := by simpa using hi
    rw [h0]; exact h
  · intro h
    exact h 0 (by simp)

/-- The unit vector in the real coordinate. -/
noncomputable def eReal : Pt := Pi.single (0 : Fin 3) (1 : ℝ)

theorem eReal_apply_zero : eReal 0 = 1 := Pi.single_eq_same _ _

theorem norm_eReal : ‖eReal‖ = 1 := by
  rw [eReal, Pi.norm_single]
  norm_num

/-- The component of `x` in the complex plane: `x` with its real coordinate
removed. -/
noncomputable def planePart (x : Pt) : Pt := x - (x 0) • eReal

theorem planePart_mem (x : Pt) : planePart x ∈ cplxPlane := by
  show (x - (x 0) • eReal) 0 = 0
  simp [eReal_apply_zero]

theorem sub_planePart (x : Pt) : x - planePart x = (x 0) • eReal := by
  rw [planePart]; abel

theorem norm_sub_planePart (x : Pt) : ‖x - planePart x‖ = |x 0| := by
  rw [sub_planePart, norm_smul, norm_eReal, mul_one, Real.norm_eq_abs]

/-- The plane component is at least `‖x‖ - |x 0|`. -/
theorem norm_planePart_ge (x : Pt) : ‖x‖ - |x 0| ≤ ‖planePart x‖ := by
  have h : x = planePart x + (x 0) • eReal := by rw [planePart]; abel
  have h2 : ‖x‖ ≤ ‖planePart x‖ + ‖(x 0) • eReal‖ := by
    have h3 := norm_add_le (planePart x) ((x 0) • eReal)
    rw [← h] at h3
    exact h3
  rw [norm_smul, norm_eReal, mul_one, Real.norm_eq_abs] at h2
  linarith

theorem cplxPlane_closed : IsClosed cplxPlane := by
  have h : cplxPlane = (LinearMap.proj (0 : Fin 3) : Pt →ₗ[ℝ] ℝ) ⁻¹' {0} := by
    ext x; simp [cplxPlane]
  rw [h]
  exact isClosed_singleton.preimage (LinearMap.continuous_of_finiteDimensional _)

/-! ## 2. Density criteria for the plane -/

variable {L : AddSubgroup Pt}

/-- The real coordinate projection of the lattice is dense. -/
def denseRangeProj (L : AddSubgroup Pt) : Prop :=
  Dense (Set.range (fun l : L => (l : Pt) 0))

/-- **The saturation of the complex plane is dense** as soon as the real
coordinate projection of the lattice is (the codimension-one criterion of
`BerendTorusLastMile`). -/
theorem dense_cplxPlane_add (hd : denseRangeProj L) :
    Dense (cplxPlane + (L : Set Pt)) := by
  rw [cplxPlane_eq_coord]
  exact BerendTorusLastMile.dense_coord_erase_add_of_dense_proj (ι := Fin 3) (j := 0) hd

/-- **The irrational ratio criterion** for the density of the plane's
saturation. -/
theorem dense_cplxPlane_add_of_irrational {l l' : L}
    (hirr : Irrational ((l : Pt) 0 / (l' : Pt) 0)) :
    Dense (cplxPlane + (L : Set Pt)) :=
  dense_cplxPlane_add (BerendTorusLastMile.dense_range_coord_of_irrational (j := 0) hirr)

/-! ## 3. Cofinality of the lattice in the plane, and the last mile -/

/-- **`L` is cofinal in the complex plane**: every point of `Pt` is approximated
by `w + l` with `w` in the plane of *arbitrarily large* norm. -/
def CofinalPlane (L : AddSubgroup Pt) : Prop :=
  ∀ (x : Pt) (ε R : ℝ), 0 < ε →
    ∃ w : Pt, w ∈ cplxPlane ∧ R ≤ ‖w‖ ∧ ∃ l ∈ L, ‖w + l - x‖ < ε

/-- Lattice elements with arbitrarily small real coordinate and arbitrarily large
norm.  In the cubic model this holds for the images of `ε ^ (-m)`, `m → ∞`, for
a unit with `|σ₁ ε| > 1` (then `|σ₂ ε| = |σ₁ ε| ^ (-1/2) > 1`, so the norm grows
while the real coordinate tends to `0`). -/
def SmallRealLargeNorm (L : AddSubgroup Pt) : Prop :=
  ∀ (ε R : ℝ), 0 < ε → ∃ l ∈ L, |(l : Pt) 0| < ε ∧ R ≤ ‖(l : Pt)‖

/-- Lattice elements whose real coordinate is close to `x 0` and which are far
from `x`: the intermediate form of the cofinality input. -/
def FarAtHeight (L : AddSubgroup Pt) : Prop :=
  ∀ (x : Pt) (ε R : ℝ), 0 < ε →
    ∃ l ∈ L, |(l : Pt) 0 - x 0| < ε ∧ R ≤ ‖x - (l : Pt)‖

/-- **Density plus small-real/large-norm gives `FarAtHeight`.** -/
theorem farAtHeight_of_dense_proj (hd : denseRangeProj L) (hunb : SmallRealLargeNorm L) :
    FarAtHeight L := by
  intro x ε R hε
  have hd' : Dense (Set.range (fun l : L => (l : Pt) 0)) := hd
  obtain ⟨l₁, h1⟩ : ∃ l₁ : L, |(l₁ : Pt) 0 - x 0| < ε / 2 := by
    obtain ⟨t, hball, htmem⟩ := Metric.dense_iff.mp hd' (x 0) (ε / 2) (by linarith)
    obtain ⟨m, hm⟩ := htmem
    refine ⟨m, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hball
    simpa [hm, abs_sub_comm] using hball
  obtain ⟨l₂, hl₂, h20, h2n⟩ := hunb (ε / 2) (R + 1 + ‖x - (l₁ : Pt)‖) (by linarith)
  refine ⟨(l₁ : Pt) + l₂, L.add_mem l₁.2 hl₂, ?_, ?_⟩
  · have hsum : ((l₁ : Pt) + l₂) 0 - x 0 = ((l₁ : Pt) 0 - x 0) + l₂ 0 := by
      simp only [Pi.add_apply]; ring
    rw [hsum]
    calc |((l₁ : Pt) 0 - x 0) + l₂ 0| ≤ |(l₁ : Pt) 0 - x 0| + |l₂ 0| := abs_add_le _ _
      _ < ε := by linarith
  · have hsplit : x - ((l₁ : Pt) + l₂) = (x - (l₁ : Pt)) - l₂ := by abel
    have htri : ‖l₂‖ ≤ ‖l₂ - (x - (l₁ : Pt))‖ + ‖x - (l₁ : Pt)‖ := by
      have h := norm_add_le (l₂ - (x - (l₁ : Pt))) (x - (l₁ : Pt))
      rwa [sub_add_cancel] at h
    have hsym : ‖(x - (l₁ : Pt)) - l₂‖ = ‖l₂ - (x - (l₁ : Pt))‖ := by
      rw [← norm_neg]; congr 1; abel
    rw [hsplit, hsym]
    linarith

/-- **Cofinality of the lattice in the plane.** -/
theorem cofinalPlane_of_farAtHeight (hf : FarAtHeight L) : CofinalPlane L := by
  intro x ε R hε
  obtain ⟨l, hl, h1, h2⟩ := hf x (min ε 1) (R + 1) (by positivity)
  have h1 : |x 0 - (l : Pt) 0| < min ε 1 := by rw [abs_sub_comm]; exact h1
  refine ⟨planePart (x - (l : Pt)), planePart_mem _, ?_, l, hl, ?_⟩
  · have h3 : ‖x - (l : Pt)‖ - |(x - (l : Pt)) 0| ≤ ‖planePart (x - (l : Pt))‖ :=
      norm_planePart_ge _
    have h4 : ((x - (l : Pt)) 0) = x 0 - (l : Pt) 0 := rfl
    have h5 : |x 0 - (l : Pt) 0| < ε := lt_of_lt_of_le h1 (min_le_left _ _)
    have h6 : |x 0 - (l : Pt) 0| < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
    rw [h4] at h3
    nlinarith [abs_nonneg (x 0 - (l : Pt) 0)]
  · have hsub : planePart (x - (l : Pt)) + (l : Pt) - x =
        -(((x - (l : Pt)) 0) • eReal) := by
      rw [planePart]; abel
    rw [hsub, norm_neg, norm_smul, norm_eReal, mul_one, Real.norm_eq_abs]
    have h4 : ((x - (l : Pt)) 0) = x 0 - (l : Pt) 0 := rfl
    rw [h4]
    exact lt_of_lt_of_le h1 (min_le_left _ _)

/-- **The last mile.**  The saturation by `L` of the unbounded part
`{w ∈ cplxPlane | R ≤ ‖w‖}` of the plane is dense. -/
theorem dense_unboundedPlane_add (hc : CofinalPlane L) (R : ℝ) :
    Dense ({w : Pt | w ∈ cplxPlane ∧ R ≤ ‖w‖} + (L : Set Pt)) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨w, hw, hn, l, hl, hdist⟩ := hc x ε R hε
  refine ⟨w + l, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    exact hdist
  · rw [Set.mem_add]
    exact ⟨w, ⟨hw, hn⟩, l, hl, rfl⟩

/-- **A closed `L`-saturated set containing the unbounded part of the complex
plane is everything.**  This is the block-model replacement for the box-growth
argument of `BerendStageIClosure.eq_univ_of_closedBox_subset`: the complex plane
is invariant under every multiplier of the model, so expansion stays inside it,
and it is the *unbounded* part of the plane that saturates densely. -/
theorem eq_univ_of_unboundedPlane_subset (hc : CofinalPlane L) {E : Set Pt}
    (hE : IsClosed E) (hsat : ∀ l ∈ L, ∀ x ∈ E, x + l ∈ E) {R : ℝ}
    (hsub : ∀ w : Pt, w ∈ cplxPlane → R ≤ ‖w‖ → w ∈ E) : E = univ := by
  refine Set.eq_univ_of_univ_subset ?_
  have hdense := dense_unboundedPlane_add (L := L) hc R
  rw [← hdense.closure_eq]
  refine closure_minimal ?_ hE
  rintro z ⟨w, hw, l, hl, rfl⟩
  exact hsat l hl w (hsub w hw.1 hw.2)

/-- **Torus form of the last mile.** -/
theorem torus_eq_univ_of_unboundedPlane (hc : CofinalPlane L) {Y : Set (Torus L)}
    (hY : IsClosed Y) {R : ℝ}
    (hsub : ∀ w : Pt, w ∈ cplxPlane → R ≤ ‖w‖ → (QuotientAddGroup.mk' L) w ∈ Y) :
    Y = univ := by
  have hpre : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsat : ∀ l ∈ L, ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      x + l ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro l hl x hx
    show (QuotientAddGroup.mk' L) (x + l) ∈ Y
    rw [map_add]
    have h0 : (QuotientAddGroup.mk' L) l = 0 := by
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa using hl
    rw [h0, add_zero]
    exact hx
  have hE : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    eq_univ_of_unboundedPlane_subset (L := L) hc hpre hsat
      (R := R) (fun w hw hn => hsub w hw hn)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by rw [hE]; exact mem_univ x
  exact hx

/-! ## 4. The exact residual of Stage I in the block model -/

/-- **Stage I for a toral family is equivalent to "the accumulation forces the
unbounded complex plane into the lift".**  This is the block-model analogue of
`BerendStageIClosure.zeroNonisolatedFull_iff_localFull`; it needs no
diagonalisation, no ergodicity and no measure theory. -/
theorem zeroNonisolatedFull_iff_unboundedPlane (hc : CofinalPlane L) {ι : Type*}
    (F : ι → Torus L →+ Torus L) :
    BerendDichotomy.ZeroNonisolatedFull F ↔
      ∀ Y : Set (Torus L), IsClosed Y → Y.Nonempty → (0 : Torus L) ∈ closure (Y \ {0}) →
        BerendDichotomy.FamilyInvariant F Y →
        ∃ R : ℝ, ∀ w : Pt, w ∈ cplxPlane → R ≤ ‖w‖ → (QuotientAddGroup.mk' L) w ∈ Y := by
  constructor
  · intro hStage Y hY hne hacc hinv
    rw [hStage Y hY hne hacc hinv]
    exact ⟨0, fun w _ _ => mem_univ _⟩
  · intro h Y hY hne hacc hinv
    obtain ⟨R, hR⟩ := h Y hY hne hacc hinv
    exact torus_eq_univ_of_unboundedPlane (L := L) hc hY hR

/-! ## 5. The producer side: one annulus in the plane plus an expanding multiplier

Berend's §4.3–4.5 produce, from the accumulation at `0`, a *bounded* piece of the
plane in the lift (a point of `E` in a cone, scaled into a fixed annulus).  The
content of this section is that such a bounded piece is enough **once it is an
annulus and the family contains a multiplier that expands the plane**: the
annulus is invariant-plane-internal, so iterating the expanding multiplier tiles
the whole unbounded part of the plane. -/

/-- The point of `Pt` with real coordinate `0` and complex coordinate `z`. -/
noncomputable def ofCplx (z : ℂ) : Pt := ![0, z.re, z.im]

theorem ofCplx_mem (z : ℂ) : ofCplx z ∈ cplxPlane := rfl

theorem cplxOf_ofCplx (z : ℂ) : cplxOf (ofCplx z) = z := by
  apply Complex.ext <;> simp [cplxOf, ofCplx]

/-- Two points of `Pt` with the same real coordinate and the same complex
coordinate are equal. -/
theorem ext_pt {x y : Pt} (h0 : x 0 = y 0) (hc : cplxOf x = cplxOf y) : x = y := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact h0
  · fin_cases j
    · exact congrArg Complex.re hc
    · exact congrArg Complex.im hc

theorem eq_ofCplx_cplxOf {w : Pt} (hw : w ∈ cplxPlane) : ofCplx (cplxOf w) = w := by
  refine ext_pt ?_ ?_
  · show (0 : ℝ) = w 0
    rw [hw]
  · rw [cplxOf_ofCplx]

theorem cplxOf_oneC : cplxOf (oneC : Pt) = 1 := by
  apply Complex.ext <;> simp [cplxOf, oneC]

theorem cplxOf_powC (a : Pt) (k : ℕ) : cplxOf (powC a k) = (cplxOf a) ^ k := by
  induction k with
  | zero => rw [powC_zero, pow_zero]; exact cplxOf_oneC
  | succ k ih => rw [powC_succ, cplxOf_mulC, ih, pow_succ, mul_comm]

theorem ptMul_ofCplx (a : Pt) (z : ℂ) : ptMul a (ofCplx z) = ofCplx (cplxOf a * z) := by
  have h := cplxOf_ptMul a (ofCplx z)
  rw [cplxOf_ofCplx] at h
  refine ext_pt ?_ h
  show a 0 * (ofCplx z) 0 = (0 : ℝ)
  simp [ofCplx]

/-- On the complex plane the supremum norm is dominated by the complex modulus. -/
theorem norm_le_norm_cplxOf {w : Pt} (hw : w ∈ cplxPlane) : ‖w‖ ≤ ‖cplxOf w‖ := by
  have h0 : w 0 = 0 := hw
  have hb : ∀ i : Fin 3, |w i| ≤ ‖cplxOf w‖ := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · rw [h0]; simp
    · have h1 : (cplxOf w).re = w 1 := rfl
      rw [← h1]; exact Complex.abs_re_le_norm _
    · have h2 : (cplxOf w).im = w 2 := rfl
      rw [← h2]; exact Complex.abs_im_le_norm _
  exact (pi_norm_le_iff_of_nonneg (x := w) (r := ‖cplxOf w‖) (hr := norm_nonneg _)).mpr hb

/-- **The annulus tiles the unbounded plane.**  If a closed-under-`ptMul a` set
`E` contains the plane annulus `{ρ₁ ≤ |z| ≤ ρ₂}` and `a` expands the plane by at
least `2` and by at least the ratio `ρ₂ / ρ₁`, then `E` contains every point of
the plane with `|z| ≥ ρ₁`. -/
theorem plane_unbounded_of_annulus {E : Set Pt} {a : Pt} (hm : 2 ≤ ‖cplxOf a‖)
    (hinv : ∀ x ∈ E, ptMul a x ∈ E)
    {ρ1 ρ2 : ℝ} (h1 : 0 < ρ1) (h12 : ρ1 ≤ ρ2) (hgap : ‖cplxOf a‖ * ρ1 ≤ ρ2)
    (hann : ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 → w ∈ E) :
    ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → w ∈ E := by
  intro w hw hw1
  set m := ‖cplxOf a‖ with hmdef
  have hm1 : 1 < m := by linarith
  set s := ‖cplxOf w‖ with hsdef
  rcases le_or_gt s ρ2 with hle | hlt
  · exact hann w hw hw1 hle
  have hmpos : 0 < m := by linarith
  have hex : ∃ k : ℕ, s < ρ2 * m ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s / ρ2) hm1
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ (by linarith)] at hk
    linarith
  set k := Nat.find hex with hkdef
  have hkspec : s < ρ2 * m ^ k := Nat.find_spec hex
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, mul_one] at hkspec; linarith
    · exact h
  have hprev : ¬ (s < ρ2 * m ^ (k - 1)) := Nat.find_min hex (by omega)
  have hprev' : ρ2 * m ^ (k - 1) ≤ s := not_lt.mp hprev
  have hcne : cplxOf a ≠ 0 := by
    intro h
    have h2 : ‖cplxOf a‖ = 0 := by rw [h]; simp
    rw [← hmdef] at h2
    linarith
  set u : ℂ := cplxOf w / (cplxOf a) ^ k with hudef
  have hpowpos : (0 : ℝ) < m ^ k := by positivity
  have hu1 : ρ1 ≤ ‖u‖ := by
    rw [hudef, norm_div, norm_pow, ← hmdef, le_div_iff₀ hpowpos]
    have hstep : ρ1 * m ≤ ρ2 := by rw [mul_comm]; exact hgap
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    have hpow : m ^ k = m ^ (k - 1) * m := by
      conv_lhs => rw [← hk1]
      exact pow_succ m (k - 1)
    calc ρ1 * m ^ k = ρ1 * m * m ^ (k - 1) := by rw [hpow]; ring
      _ ≤ ρ2 * m ^ (k - 1) := by
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
      _ ≤ s := hprev'
  have hu2 : ‖u‖ ≤ ρ2 := by
    rw [hudef, norm_div, norm_pow, ← hmdef, div_le_iff₀ hpowpos]
    linarith
  have hw'E : ofCplx u ∈ E :=
    hann _ (ofCplx_mem u) (by rwa [cplxOf_ofCplx]) (by rwa [cplxOf_ofCplx])
  have hiter : ∀ n : ℕ, (((ptMul a) ^ n) (ofCplx u)) ∈ E := by
    intro n
    induction n with
    | zero => simpa using hw'E
    | succ n ih =>
        rw [pow_succ']
        exact hinv _ ih
  have hfin : (((ptMul a) ^ k) (ofCplx u)) = w := by
    rw [ptMul_pow, ptMul_ofCplx, cplxOf_powC, hudef, mul_div_cancel₀ _ (pow_ne_zero k hcne)]
    exact eq_ofCplx_cplxOf hw
  rw [← hfin]
  exact hiter k

/-- **Stage I from one plane annulus.**  A closed `L`-saturated set containing a
plane annulus and invariant under one multiplier that expands the plane by at
least `2` is everything. -/
theorem eq_univ_of_annulus_subset (hc : CofinalPlane L) {E : Set Pt}
    (hE : IsClosed E) (hsat : ∀ l ∈ L, ∀ x ∈ E, x + l ∈ E)
    {a : Pt} (hm : 2 ≤ ‖cplxOf a‖) (hinv : ∀ x ∈ E, ptMul a x ∈ E)
    {ρ1 ρ2 : ℝ} (h1 : 0 < ρ1) (h12 : ρ1 ≤ ρ2) (hgap : ‖cplxOf a‖ * ρ1 ≤ ρ2)
    (hann : ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 → w ∈ E) :
    E = univ := by
  refine eq_univ_of_unboundedPlane_subset (L := L) hc hE hsat (R := ρ1) ?_
  intro w hw hwR
  exact plane_unbounded_of_annulus hm hinv h1 h12 hgap hann w hw
    (le_trans hwR (norm_le_norm_cplxOf hw))

/-- **Torus form: one plane annulus forces `Y = univ`.**  `Y` is closed and the
lift contains the annulus, so the hypothesis is exactly "the image in the torus of
the plane annulus is contained in `Y`". -/
theorem torus_eq_univ_of_annulus (hc : CofinalPlane L) {Y : Set (Torus L)}
    (hY : IsClosed Y) {a : Pt} (hm : 2 ≤ ‖cplxOf a‖)
    (hinv : ∀ x : Pt, x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y → ptMul a x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {ρ1 ρ2 : ℝ} (h1 : 0 < ρ1) (h12 : ρ1 ≤ ρ2) (hgap : ‖cplxOf a‖ * ρ1 ≤ ρ2)
    (hann : ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 →
      (QuotientAddGroup.mk' L) w ∈ Y) :
    Y = univ := by
  have hpre : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsat : ∀ l ∈ L, ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      x + l ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro l hl x hx
    show (QuotientAddGroup.mk' L) (x + l) ∈ Y
    rw [map_add]
    have h0 : (QuotientAddGroup.mk' L) l = 0 := by
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa using hl
    rw [h0, add_zero]
    exact hx
  have hE : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    eq_univ_of_annulus_subset (L := L) hc hpre hsat hm hinv h1 h12 hgap
      (fun w hw h2 h3 => hann w hw h2 h3)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by rw [hE]; exact mem_univ x
  exact hx

/-- **Stage I from one annulus, in consumer form.**  If the family `F` on the
torus contains the map induced by a multiplier `a` that expands the complex plane
by at least `2`, and if every closed invariant `Y` with `0` as a non-isolated
point contains the image of *some* plane annulus of ratio at most `‖cplxOf a‖`,
then Stage I holds for `F`.  With `BerendSec5.dichotomy_of_stageI_of_minimal_torsion`
this is the last input of the axiom replacement: everything else in that assembly
(finite kernels, finite torsion, minimal torsion points, one transitive member)
is bookkeeping. -/
theorem zeroNonisolatedFull_of_annulusInput (hc : CofinalPlane L) {ι : Type*}
    {F : ι → Torus L →+ Torus L} {a : Pt} {i₀ : ι} (hm : 2 ≤ ‖cplxOf a‖)
    (hF : ∀ x : Pt, F i₀ (QuotientAddGroup.mk' L x) = QuotientAddGroup.mk' L (ptMul a x))
    (hann : ∀ Y : Set (Torus L), IsClosed Y → Y.Nonempty →
      (0 : Torus L) ∈ closure (Y \ {0}) → BerendDichotomy.FamilyInvariant F Y →
      ∃ ρ1 ρ2 : ℝ, 0 < ρ1 ∧ ρ1 ≤ ρ2 ∧ ‖cplxOf a‖ * ρ1 ≤ ρ2 ∧
        ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 →
          (QuotientAddGroup.mk' L) w ∈ Y) :
    BerendDichotomy.ZeroNonisolatedFull F := by
  intro Y hY hne hacc hinv
  obtain ⟨ρ1, ρ2, h1, h12, hgap, hann'⟩ := hann Y hY hne hacc hinv
  have hinv' : ∀ x : Pt, x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y →
      ptMul a x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro x hx
    show (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y
    rw [← hF x]
    exact hinv i₀ ⟨(QuotientAddGroup.mk' L) x, hx, rfl⟩
  exact torus_eq_univ_of_annulus (L := L) hc hY hm hinv' h1 h12 hgap hann'

/-! ## 6. Instantiation at the unit–prime model

The annulus input is stated for the actual family `D.torusAct` of the project: the
expanding member supplied by `BerendExpandingMember.exists_mult_margin`
(`4 ≤ |a 0|`, `16 ≤ normC a`) satisfies `4 ≤ ‖cplxOf a‖`, hence the `2` of §5. -/

theorem two_le_norm_cplxOf_of_normC {a : Pt} (hC : 16 ≤ normC a) : 2 ≤ ‖cplxOf a‖ := by
  have hsq : ‖cplxOf a‖ ^ 2 = normC a := by
    rw [normC_eq_normSq, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (cplxOf a)]

/-- **Stage I for the unit–prime family from one plane annulus.**  If every closed
invariant `Y` with `0` as a non-isolated point contains the image of a plane
annulus whose ratio is at most `‖cplxOf (D.mult u j)‖`, and some member of the
family expands the plane by at least `2`, then Stage I holds for `D.torusAct`. -/
theorem zeroNonisolatedFull_torusAct_of_annulusInput {K : Type*} [Field K]
    {L : AddSubgroup Pt} {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (hc : CofinalPlane L)
    (u : 𝒪ˣ) (j : ℕ) (hC : 16 ≤ normC (D.mult u j))
    (hann : ∀ Y : Set (Torus L), IsClosed Y → Y.Nonempty →
      (0 : Torus L) ∈ closure (Y \ {0}) →
      BerendDichotomy.FamilyInvariant D.torusAct Y →
      ∃ ρ1 ρ2 : ℝ, 0 < ρ1 ∧ ρ1 ≤ ρ2 ∧ ‖cplxOf (D.mult u j)‖ * ρ1 ≤ ρ2 ∧
        ∀ w : Pt, w ∈ cplxPlane → ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 →
          (QuotientAddGroup.mk' L) w ∈ Y) :
    BerendDichotomy.ZeroNonisolatedFull D.torusAct := by
  refine zeroNonisolatedFull_of_annulusInput (L := L) hc
    (a := D.mult u j) (i₀ := (u, j)) (two_le_norm_cplxOf_of_normC hC) ?_ hann
  intro x
  rw [D.torusAct_mk', D.family_act_eq_ptMul]
  rfl

end BerendBlockLastMile
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendBlockLastMile.cplxPlane_eq_coord
#print axioms CubicTwoStage.BerendBlockLastMile.dense_cplxPlane_add
#print axioms CubicTwoStage.BerendBlockLastMile.dense_cplxPlane_add_of_irrational
#print axioms CubicTwoStage.BerendBlockLastMile.norm_planePart_ge
#print axioms CubicTwoStage.BerendBlockLastMile.farAtHeight_of_dense_proj
#print axioms CubicTwoStage.BerendBlockLastMile.cofinalPlane_of_farAtHeight
#print axioms CubicTwoStage.BerendBlockLastMile.dense_unboundedPlane_add
#print axioms CubicTwoStage.BerendBlockLastMile.eq_univ_of_unboundedPlane_subset
#print axioms CubicTwoStage.BerendBlockLastMile.torus_eq_univ_of_unboundedPlane
#print axioms CubicTwoStage.BerendBlockLastMile.zeroNonisolatedFull_iff_unboundedPlane
#print axioms CubicTwoStage.BerendBlockLastMile.cplxOf_powC
#print axioms CubicTwoStage.BerendBlockLastMile.ptMul_ofCplx
#print axioms CubicTwoStage.BerendBlockLastMile.norm_le_norm_cplxOf
#print axioms CubicTwoStage.BerendBlockLastMile.plane_unbounded_of_annulus
#print axioms CubicTwoStage.BerendBlockLastMile.eq_univ_of_annulus_subset
#print axioms CubicTwoStage.BerendBlockLastMile.torus_eq_univ_of_annulus
#print axioms CubicTwoStage.BerendBlockLastMile.zeroNonisolatedFull_of_annulusInput
#print axioms CubicTwoStage.BerendBlockLastMile.two_le_norm_cplxOf_of_normC
#print axioms CubicTwoStage.BerendBlockLastMile.zeroNonisolatedFull_torusAct_of_annulusInput
