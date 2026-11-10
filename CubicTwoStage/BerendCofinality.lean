/-
# Cofinality of `σ(𝒪)` in the complex plane: the concrete input of Stage I

Swarm `smw952unn`, member `m6`, direction `d2`.

`BerendBlockLastMile` reduces Stage I of the block model to two arithmetic facts
about the lattice `L = σ(𝒪) ⊆ Pt = ℝ × ℂ`:

* `denseRangeProj L` — the real-coordinate projection of `L` is dense in `ℝ`;
* `SmallRealLargeNorm L` — `L` contains elements of arbitrarily small real
  coordinate and arbitrarily large norm.

`cofinalPlane_of_farAtHeight` turns them into `CofinalPlane L`, which is the
hypothesis `hc` of `zeroNonisolatedFull_torusAct_of_annulusInput` (and of
`zeroNonisolatedFull_iff_unboundedPlane`).

This file *proves* both facts for the actual lattice `σ(𝒪)` of a `FieldModel`,
from two field-theoretic inputs, and assembles `CofinalPlane (σ(𝒪))`.

## The two inputs

1. `𝒪` contains an element that is not a rational number.  For the cubic field
   of the paper this is automatic (`𝒪` is a rank-three ℤ-lattice).  It gives the
   irrational real coordinate: the real coordinate of `σ` is a *ring
   homomorphism* `K → ℝ`, hence injective, so a rational real coordinate forces
   the field element to be rational.

2. A unit `ε` whose real embedding is not of modulus `1`.  Then the norm identity
   `|Nm ε| = |σ₁ ε| · |σ₂ ε|² = 1` forces exactly one of `ε`, `ε⁻¹` to expand at
   the real place and contract at the complex one, and the images of its
   *negative* powers therefore have real coordinate `→ 0` and norm `→ ∞`.

Both inputs are available in the project: (1) holds for any cubic field, and (2)
is satisfied by a unit of infinite order (`BerendExpandingMember`'s
`exists_mult_margin_fieldModel` already consumes the same hypothesis).

No `sorry`, no new axiom, no use of `berend_multi_invariance`.
-/
import CubicTwoStage.BerendBlockLastMile
import CubicTwoStage.BerendExpandingMember

open Set

set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendCofinality

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-! ## 1. The real coordinate of `σ` is a ring homomorphism -/

/-- The real coordinate of the embedding `σ : K → ℝ × ℂ`, as a ring
homomorphism.  It is injective, because `K` is a field and `ℝ` is nontrivial. -/
noncomputable def sigmaReal (FM : FieldModel K 𝒪 Nm) : K →+* ℝ where
  toFun a := (FM.σ a) 0
  map_one' := by rw [FM.σ_one]; rfl
  map_mul' a b := by rw [FM.σ_mul]; rfl
  map_zero' := by rw [FM.σ_zero]; rfl
  map_add' a b := by rw [FM.σ_add]; rfl

@[simp] lemma sigmaReal_apply (FM : FieldModel K 𝒪 Nm) (a : K) :
    sigmaReal FM a = (FM.σ a) 0 := rfl

lemma sigmaReal_injective (FM : FieldModel K 𝒪 Nm) : Function.Injective (sigmaReal FM) :=
  RingHom.injective (sigmaReal FM)

/-- **A non-rational ring element has irrational real coordinate.**  The real
coordinate map is a ring homomorphism out of a field, hence injective, so a
rational real coordinate forces the element itself to be the corresponding
rational number. -/
theorem irrational_sigma_zero_of_ne_rat (FM : FieldModel K 𝒪 Nm) {b : 𝒪}
    (hb : ∀ q : ℚ, ((b : 𝒪) : K) ≠ (q : K)) :
    Irrational ((FM.σ ((b : 𝒪) : K)) 0) := by
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hq' : sigmaReal FM ((b : 𝒪) : K) = sigmaReal FM ((q : K)) := by
    have hqrat : sigmaReal FM ((q : K)) = (q : ℝ) := map_ratCast (sigmaReal FM) q
    rw [hqrat, sigmaReal_apply]
    exact hq.symm
  exact hb q (sigmaReal_injective FM hq')

/-! ## 2. The real-coordinate projection of the lattice is dense -/

/-- The lattice element `σ(1)`, whose real coordinate is `1`. -/
noncomputable def latticeOne (FM : FieldModel K 𝒪 Nm) : FM.lattice :=
  ⟨oneC, FM.mem_lattice.mpr ⟨1, by rw [Subring.coe_one, FM.σ_one]⟩⟩

@[simp] lemma latticeOne_coe (FM : FieldModel K 𝒪 Nm) :
    ((latticeOne FM : FM.lattice) : Pt) = oneC := rfl

lemma latticeOne_apply_zero (FM : FieldModel K 𝒪 Nm) : (latticeOne FM : Pt) 0 = 1 := rfl

/-- The lattice element `σ(b)`. -/
noncomputable def latticeOf (FM : FieldModel K 𝒪 Nm) (b : 𝒪) : FM.lattice :=
  ⟨FM.σ ((b : 𝒪) : K), FM.mem_lattice.mpr ⟨b, rfl⟩⟩

@[simp] lemma latticeOf_coe (FM : FieldModel K 𝒪 Nm) (b : 𝒪) :
    ((latticeOf FM b : FM.lattice) : Pt) = FM.σ ((b : 𝒪) : K) := rfl

lemma latticeOf_apply_zero (FM : FieldModel K 𝒪 Nm) (b : 𝒪) :
    ((latticeOf FM b : FM.lattice) : Pt) 0 = (FM.σ ((b : 𝒪) : K)) 0 := rfl

/-- **Density of the real-coordinate projection of `σ(𝒪)`** from an irrational
real coordinate of one ring element: the two lattice elements `σ(b)` and `σ(1)`
have irrational real-coordinate ratio `σ₁(b)/1`, which is the hypothesis of
`BerendTorusLastMile.dense_range_coord_of_irrational`. -/
theorem denseRangeProj_lattice_of_irrational (FM : FieldModel K 𝒪 Nm) {b : 𝒪}
    (hb : Irrational ((FM.σ ((b : 𝒪) : K)) 0)) :
    BerendBlockLastMile.denseRangeProj FM.lattice := by
  refine BerendTorusLastMile.dense_range_coord_of_irrational (ι := Fin 3) (j := 0)
    (l := latticeOf FM b) (l' := latticeOne FM) ?_
  show Irrational ((FM.σ ((b : 𝒪) : K)) 0 / (oneC : Pt) 0)
  simpa using hb

/-- **Density of the real-coordinate projection of `σ(𝒪)`** from a
non-rational ring element. -/
theorem denseRangeProj_lattice (FM : FieldModel K 𝒪 Nm) {b : 𝒪}
    (hb : ∀ q : ℚ, ((b : 𝒪) : K) ≠ (q : K)) :
    BerendBlockLastMile.denseRangeProj FM.lattice :=
  denseRangeProj_lattice_of_irrational FM (irrational_sigma_zero_of_ne_rat FM hb)

/-! ## 3. The eigen-moduli of a unit and its negative powers -/

/-- `lamAbs` at the complex place is the modulus of the complex coordinate. -/
theorem lamAbs_one_eq_norm_cplxOf (a : Pt) : lamAbs a 1 = ‖cplxOf a‖ := rfl

/-- The supremum norm dominates half the complex modulus. -/
theorem half_norm_cplxOf_le_norm (w : Pt) : ‖cplxOf w‖ / 2 ≤ ‖w‖ := by
  have h := Complex.norm_le_abs_re_add_abs_im (cplxOf w)
  have h1 : |(cplxOf w).re| ≤ ‖w‖ := abs_apply_le_norm w 1
  have h2 : |(cplxOf w).im| ≤ ‖w‖ := abs_apply_le_norm w 2
  linarith

/-- **The product relation for a unit**, in the form used below:
`lamAbs (σ u) 0 * (lamAbs (σ u) 1)^2 = 1`. -/
theorem lamAbs_sigma_unit_product (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) :
    lamAbs (FM.σ (((u : 𝒪) : K))) 0 * (lamAbs (FM.σ (((u : 𝒪) : K))) 1) ^ 2 = 1 := by
  have h := prod_lamAbs_unit FM u
  have h12 := lamAbs_one_eq_two (FM.σ (((u : 𝒪) : K)))
  rw [Fin.prod_univ_three, ← h12] at h
  calc lamAbs (FM.σ (((u : 𝒪) : K))) 0 * (lamAbs (FM.σ (((u : 𝒪) : K))) 1) ^ 2
      = lamAbs (FM.σ (((u : 𝒪) : K))) 0 * lamAbs (FM.σ (((u : 𝒪) : K))) 1
        * lamAbs (FM.σ (((u : 𝒪) : K))) 1 := by ring
    _ = 1 := h

/-- **A unit and its inverse have reciprocal moduli.** -/
theorem lamAbs_sigma_unit_inv (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) (i : Fin 3) :
    lamAbs (FM.σ (((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) i
      = (lamAbs (FM.σ (((u : 𝒪) : K))) i)⁻¹ := by
  have h : FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) ⋆ FM.σ (((u : 𝒪) : K)) = oneC := by
    rw [← FM.σ_mul, mul_comm]
    have h1 : ((u : 𝒪) : K) * (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
    rw [h1, FM.σ_one]
  have h2 : lamAbs (FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K))) i
      * lamAbs (FM.σ (((u : 𝒪) : K))) i = 1 := by
    have h3 := congrFun (lamAbs_mulC (FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)))
      (FM.σ (((u : 𝒪) : K)))) i
    rw [h, lamAbs_oneC] at h3
    exact h3.symm
  exact eq_inv_of_mul_eq_one_left h2

/-- **The moduli of the powers of a unit are the powers of the moduli.** -/
theorem lamAbs_sigma_pow (FM : FieldModel K 𝒪 Nm) (v : 𝒪ˣ) (m : ℕ) (i : Fin 3) :
    lamAbs (FM.σ ((((v ^ m : 𝒪ˣ) : 𝒪) : K))) i
      = (lamAbs (FM.σ (((v : 𝒪) : K))) i) ^ m := by
  induction m with
  | zero =>
      have h1 : ((((v ^ 0 : 𝒪ˣ) : 𝒪) : K)) = (1 : K) := by
        rw [pow_zero, Units.val_one, Subring.coe_one]
      rw [h1, FM.σ_one, lamAbs_oneC, pow_zero]
  | succ m ih =>
      have h1 : ((((v ^ (m + 1) : 𝒪ˣ) : 𝒪) : K))
          = ((((v ^ m : 𝒪ˣ) : 𝒪) : K)) * ((((v : 𝒪ˣ) : 𝒪) : K)) := by
        rw [pow_succ, Units.val_mul, Subring.coe_mul]
      rw [h1, FM.σ_mul]
      have h3 := congrFun (lamAbs_mulC (FM.σ ((((v ^ m : 𝒪ˣ) : 𝒪) : K)))
        (FM.σ (((v : 𝒪ˣ) : 𝒪) : K))) i
      rw [h3, ih, pow_succ]

/-- **The moduli of the negative powers of a unit are the reciprocal powers.** -/
theorem lamAbs_sigma_unit_pow_inv (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) (m : ℕ) (i : Fin 3) :
    lamAbs (FM.σ (((((u ^ m)⁻¹ : 𝒪ˣ) : 𝒪) : K))) i
      = ((lamAbs (FM.σ (((u : 𝒪) : K))) i) ^ m)⁻¹ := by
  have h1 : ((u ^ m)⁻¹ : 𝒪ˣ) = (u⁻¹) ^ m := (inv_pow u m).symm
  rw [h1, lamAbs_sigma_pow (v := u⁻¹), lamAbs_sigma_unit_inv, inv_pow]

/-! ## 4. Small real coordinate and large norm -/

/-- **`SmallRealLargeNorm` for `σ(𝒪)` from a unit expanding at the real place.**
The element `σ(ε⁻ᵐ)` has real coordinate `|σ₁ ε|⁻ᵐ → 0`, while its complex
coordinate has modulus `|σ₂ ε|⁻ᵐ → ∞` because `|σ₂ ε| < 1`. -/
theorem smallRealLargeNorm_lattice_of_one_lt (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ)
    (hU : 1 < lamAbs (FM.σ (((u : 𝒪) : K))) 0) :
    BerendBlockLastMile.SmallRealLargeNorm FM.lattice := by
  intro ε R hε
  set U := lamAbs (FM.σ (((u : 𝒪) : K))) 0 with hUdef
  set V := lamAbs (FM.σ (((u : 𝒪) : K))) 1 with hVdef
  have hUpos : 0 < U := by linarith
  have hVnn : 0 ≤ V := lamAbs_nonneg _ 1
  -- the product relation and `V < 1`
  have hprod : U * V ^ 2 = 1 := lamAbs_sigma_unit_product FM u
  have hVsq : V ^ 2 = U⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  have hV1 : V < 1 := by
    have hUinv : U⁻¹ < 1 := inv_lt_one_iff₀.mpr (Or.inr hU)
    nlinarith [hVsq, hVnn]
  have hVpos : 0 < V := by
    have : 0 < V ^ 2 := by rw [hVsq]; positivity
    nlinarith
  have hUinv1 : U⁻¹ < 1 := inv_lt_one_iff₀.mpr (Or.inr hU)
  have hVinv1 : 1 < V⁻¹ := one_lt_inv_iff₀.mpr ⟨hVpos, hV1⟩
  -- choose the exponent
  obtain ⟨m₁, hm₁⟩ := exists_pow_lt_of_lt_one hε hUinv1
  obtain ⟨m₂, hm₂⟩ := pow_unbounded_of_one_lt (2 * R) hVinv1
  refine ⟨FM.σ (((((u ^ (max m₁ m₂))⁻¹ : 𝒪ˣ) : 𝒪) : K)),
    FM.mem_lattice.mpr ⟨((u ^ (max m₁ m₂))⁻¹ : 𝒪ˣ), rfl⟩, ?_, ?_⟩
  · -- small real coordinate
    rw [← lamAbs_zero_eq_abs, lamAbs_sigma_unit_pow_inv, ← inv_pow]
    have hmono : (U⁻¹) ^ (max m₁ m₂) ≤ (U⁻¹) ^ m₁ :=
      pow_le_pow_of_le_one (by positivity) hUinv1.le (le_max_left _ _)
    linarith
  · -- large norm
    have hcplx : ‖cplxOf (FM.σ (((((u ^ (max m₁ m₂))⁻¹ : 𝒪ˣ) : 𝒪) : K)))‖
        = ((V ^ (max m₁ m₂))⁻¹) := by
      rw [← lamAbs_one_eq_norm_cplxOf, lamAbs_sigma_unit_pow_inv]
    have hhalf := half_norm_cplxOf_le_norm
      (FM.σ (((((u ^ (max m₁ m₂))⁻¹ : 𝒪ˣ) : 𝒪) : K)))
    rw [hcplx, ← inv_pow] at hhalf
    have hmono : (V⁻¹) ^ m₂ ≤ (V⁻¹) ^ (max m₁ m₂) :=
      pow_le_pow_right₀ hVinv1.le (le_max_right _ _)
    linarith

/-- **`SmallRealLargeNorm` for `σ(𝒪)` from a unit whose real embedding is not of
modulus one.**  If the unit contracts at the real place, the same argument is
run with its inverse, which then expands there. -/
theorem smallRealLargeNorm_lattice_of_ne_one (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ)
    (hU : lamAbs (FM.σ (((u : 𝒪) : K))) 0 ≠ 1) :
    BerendBlockLastMile.SmallRealLargeNorm FM.lattice := by
  set U := lamAbs (FM.σ (((u : 𝒪) : K))) 0 with hUdef
  have hprod : U * (lamAbs (FM.σ (((u : 𝒪) : K))) 1) ^ 2 = 1 :=
    lamAbs_sigma_unit_product FM u
  have hUpos : 0 < U := by
    have hnn : 0 ≤ U := lamAbs_nonneg (FM.σ (((u : 𝒪) : K))) 0
    have hne : U ≠ 0 := by
      intro h0
      rw [h0] at hprod
      simp at hprod
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  rcases lt_or_gt_of_ne hU with hlt | hgt
  · -- the unit contracts at the real place: use `ε⁻¹`
    have hUinv : 1 < lamAbs (FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K))) 0 := by
      rw [lamAbs_sigma_unit_inv]
      exact one_lt_inv_iff₀.mpr ⟨hUpos, hlt⟩
    exact smallRealLargeNorm_lattice_of_one_lt FM u⁻¹ hUinv
  · exact smallRealLargeNorm_lattice_of_one_lt FM u hgt

/-! ## 5. Cofinality of `σ(𝒪)` in the complex plane -/

/-- **The concrete cofinality input.**  For the lattice `σ(𝒪)` of a field model
with a non-rational ring element and a unit of real modulus `≠ 1`, the lattice is
cofinal in the complex plane: `CofinalPlane (σ(𝒪))`, the hypothesis `hc` of
`BerendBlockLastMile.zeroNonisolatedFull_torusAct_of_annulusInput`. -/
theorem cofinalPlane_lattice (FM : FieldModel K 𝒪 Nm) {b : 𝒪}
    (hb : ∀ q : ℚ, ((b : 𝒪) : K) ≠ (q : K)) (u : 𝒪ˣ)
    (hU : lamAbs (FM.σ (((u : 𝒪) : K))) 0 ≠ 1) :
    BerendBlockLastMile.CofinalPlane FM.lattice :=
  BerendBlockLastMile.cofinalPlane_of_farAtHeight
    (BerendBlockLastMile.farAtHeight_of_dense_proj
      (denseRangeProj_lattice FM hb)
      (smallRealLargeNorm_lattice_of_ne_one FM u hU))


/-! ## 6. `SmallRealLargeNorm` with no unit at all

`BerendBlockLastMile.SmallRealLargeNorm` asks for lattice elements of arbitrarily
small real coordinate and arbitrarily large norm.  The powers `ε^{-m}` of a unit
supply them (§4), but they are not needed: density of the real-coordinate
projection already gives *integral* elements `0 ≠ x` with `|σ₁ x| < δ`, and for
those the product formula `Nm x = σ₁ x · |σ₂ x|²` with `Nm x ≥ 1` forces
`|σ₂ x| ≥ δ^{-1/2}`, hence `‖σ x‖ → ∞`.  So cofinality of `σ(𝒪)` in the plane
needs **density only**.
-/

/-- The (`cplxOf`) complex modulus squared is `normC`. -/
theorem normC_eq_sq_norm_cplxOf (w : Pt) : normC w = ‖cplxOf w‖ ^ 2 := by
  rw [normC_eq_normSq, Complex.normSq_eq_norm_sq]

theorem normC_nonneg' (w : Pt) : 0 ≤ normC w := by
  rw [normC_eq_sq_norm_cplxOf]; positivity

/-- **Some ring element `x` has `σ₁ x` close to a prescribed real number.** -/
theorem exists_ring_near (FM : FieldModel K 𝒪 Nm)
    (hd : BerendBlockLastMile.denseRangeProj FM.lattice) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ g : 𝒪, |(FM.σ (((g : 𝒪) : K))) 0 - y| < r := by
  obtain ⟨t, htball, htmem⟩ := Metric.dense_iff.mp hd y r hr
  obtain ⟨l, hl⟩ := htmem
  rw [Metric.mem_ball, Real.dist_eq] at htball
  obtain ⟨g, hg⟩ := FM.mem_lattice.mp l.2
  refine ⟨g, ?_⟩
  have hlt : ((l : FM.lattice) : Pt) 0 = (FM.σ (((g : 𝒪) : K))) 0 := by rw [hg]
  rw [← hlt]
  rw [show ((l : FM.lattice) : Pt) 0 = t from hl]
  exact abs_sub_comm y t ▸ htball

/-- **`SmallRealLargeNorm` from density of the real-coordinate projection.** -/
theorem smallRealLargeNorm_lattice_of_dense (FM : FieldModel K 𝒪 Nm)
    (hd : BerendBlockLastMile.denseRangeProj FM.lattice) :
    BerendBlockLastMile.SmallRealLargeNorm FM.lattice := by
  intro εs R hεs
  set δ := min εs (1 / (4 * (R ^ 2 + 1))) with hδdef
  have hδpos : 0 < δ := lt_min hεs (by positivity)
  have hδle : δ ≤ εs := min_le_left _ _
  have hδR : δ ≤ 1 / (4 * (R ^ 2 + 1)) := min_le_right _ _
  have hR2 : 0 < R ^ 2 + 1 := by positivity
  obtain ⟨g₁, hg₁⟩ := exists_ring_near FM hd 0 (r := δ / 4) (by linarith)
  obtain ⟨g₂, hg₂⟩ := exists_ring_near FM hd (δ / 2) (r := δ / 4) (by linarith)
  have h0₁ : |(FM.σ (((g₁ : 𝒪) : K))) 0| < δ / 4 := by simpa using hg₁
  have h0₂lo : δ / 4 < (FM.σ (((g₂ : 𝒪) : K))) 0 := by
    have := (abs_lt.mp hg₂).1
    linarith
  have h0₂hi : (FM.σ (((g₂ : 𝒪) : K))) 0 < 3 * δ / 4 := by
    have := (abs_lt.mp hg₂).2
    linarith
  -- the difference, a nonzero ring element
  set a : 𝒪 := g₁ - g₂ with hadef
  have hσa : FM.σ (((a : 𝒪) : K))
      = FM.σ (((g₁ : 𝒪) : K)) - FM.σ (((g₂ : 𝒪) : K)) := by
    have hcoee : (((a : 𝒪) : K)) = ((g₁ : 𝒪) : K) - ((g₂ : 𝒪) : K) := by
      rw [hadef]; simp
    rw [hcoee, FM.σ_sub]
  have habs0 : |(FM.σ (((a : 𝒪) : K))) 0| < δ := by
    rw [hσa]
    simp only [Pi.sub_apply]
    have h2abs : |(FM.σ (((g₂ : 𝒪) : K))) 0| < 3 * δ / 4 := by
      rw [abs_of_pos (by linarith)]
      exact h0₂hi
    calc |(FM.σ (((g₁ : 𝒪) : K))) 0 - (FM.σ (((g₂ : 𝒪) : K))) 0|
        ≤ |(FM.σ (((g₁ : 𝒪) : K))) 0| + |(FM.σ (((g₂ : 𝒪) : K))) 0| := abs_sub _ _
      _ < δ / 4 + 3 * δ / 4 := by linarith
      _ = δ := by ring
  have hpos0 : 0 < |(FM.σ (((a : 𝒪) : K))) 0| := by
    rw [abs_pos, hσa]
    simp only [Pi.sub_apply, sub_eq_zero]
    intro hzero
    have hb : (FM.σ (((g₁ : 𝒪) : K))) 0 < δ / 4 := (abs_lt.mp h0₁).2
    linarith
  have hane : a ≠ 0 := by
    intro h
    rw [h] at hpos0
    simpa [FM.σ_zero] using hpos0
  -- integrality: the norm of a nonzero integral element is at least one
  have hNm1 : (1 : ℝ) ≤ ((Nm a : ℚ≥0) : ℝ) := by
    obtain ⟨n, hn⟩ := FM.norm_nat a a.2
    have hn0 : n ≠ 0 := by
      intro h
      apply hane
      apply Subtype.ext
      apply (AbsNorm.eq_zero_iff Nm).mp
      rw [hn, h]
      simp
    have h1n : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    rw [hn]
    exact_mod_cast h1n
  -- the product formula
  have hkey : |(FM.σ (((a : 𝒪) : K))) 0| * normC (FM.σ (((a : 𝒪) : K)))
      = ((Nm a : ℚ≥0) : ℝ) := by
    have hCnn : 0 ≤ normC (FM.σ (((a : 𝒪) : K))) := normC_nonneg' _
    calc |(FM.σ (((a : 𝒪) : K))) 0| * normC (FM.σ (((a : 𝒪) : K)))
        = |(FM.σ (((a : 𝒪) : K))) 0 * normC (FM.σ (((a : 𝒪) : K)))| := by
          rw [abs_mul, abs_of_nonneg hCnn]
      _ = |normR (FM.σ (((a : 𝒪) : K)))| := by rw [normR_eq_mul_normC]
      _ = ((Nm a : ℚ≥0) : ℝ) := FM.normR_abs a
  -- the complex modulus of `σ a` is at least `δ^{-1/2}`
  have hCbound : 1 / δ < normC (FM.σ (((a : 𝒪) : K))) := by
    have h1 : 1 ≤ normC (FM.σ (((a : 𝒪) : K))) * |(FM.σ (((a : 𝒪) : K))) 0| := by
      rw [mul_comm]
      linarith
    have h2 : 1 / |(FM.σ (((a : 𝒪) : K))) 0| ≤ normC (FM.σ (((a : 𝒪) : K))) := by
      rw [div_le_iff₀ hpos0]
      linarith
    have h3 : 1 / δ < 1 / |(FM.σ (((a : 𝒪) : K))) 0| :=
      one_div_lt_one_div_of_lt hpos0 habs0
    linarith
  have hδinv : 4 * (R ^ 2 + 1) ≤ 1 / δ := by
    have h := one_div_le_one_div_of_le hδpos hδR
    rwa [one_div_one_div] at h
  have hnorm2 : R ^ 2 + 1 < ‖FM.σ (((a : 𝒪) : K))‖ ^ 2 := by
    have hhalf := half_norm_cplxOf_le_norm (FM.σ (((a : 𝒪) : K)))
    have hsq : normC (FM.σ (((a : 𝒪) : K)))
        = ‖cplxOf (FM.σ (((a : 𝒪) : K)))‖ ^ 2 := normC_eq_sq_norm_cplxOf _
    have hnn : 0 ≤ ‖cplxOf (FM.σ (((a : 𝒪) : K)))‖ := norm_nonneg _
    have h3 : ‖FM.σ (((a : 𝒪) : K))‖ ^ 2
        ≥ normC (FM.σ (((a : 𝒪) : K))) / 4 := by
      nlinarith
    nlinarith
  refine ⟨FM.σ (((a : 𝒪) : K)), FM.mem_lattice.mpr ⟨a, rfl⟩, ?_, ?_⟩
  · linarith
  · have habs : |R| < ‖FM.σ (((a : 𝒪) : K))‖ :=
      abs_lt_of_sq_lt_sq (by nlinarith) (norm_nonneg _)
    linarith [le_abs_self R]

/-- **Cofinality of `σ(𝒪)` in the complex plane from density alone.**  This is
`CofinalPlane (σ(𝒪))` — the hypothesis `hc` of
`BerendBlockLastMile.zeroNonisolatedFull_torusAct_of_annulusInput` — with the
unit hypothesis of §4 eliminated. -/
theorem cofinalPlane_lattice_of_dense (FM : FieldModel K 𝒪 Nm)
    (hd : BerendBlockLastMile.denseRangeProj FM.lattice) :
    BerendBlockLastMile.CofinalPlane FM.lattice :=
  BerendBlockLastMile.cofinalPlane_of_farAtHeight
    (BerendBlockLastMile.farAtHeight_of_dense_proj hd
      (smallRealLargeNorm_lattice_of_dense FM hd))

end BerendCofinality
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendCofinality.sigmaReal_injective
#print axioms CubicTwoStage.BerendCofinality.irrational_sigma_zero_of_ne_rat
#print axioms CubicTwoStage.BerendCofinality.denseRangeProj_lattice
#print axioms CubicTwoStage.BerendCofinality.half_norm_cplxOf_le_norm
#print axioms CubicTwoStage.BerendCofinality.lamAbs_sigma_unit_inv
#print axioms CubicTwoStage.BerendCofinality.lamAbs_sigma_unit_pow_inv
#print axioms CubicTwoStage.BerendCofinality.smallRealLargeNorm_lattice_of_one_lt
#print axioms CubicTwoStage.BerendCofinality.smallRealLargeNorm_lattice_of_ne_one
#print axioms CubicTwoStage.BerendCofinality.cofinalPlane_lattice

#print axioms CubicTwoStage.BerendCofinality.exists_ring_near
#print axioms CubicTwoStage.BerendCofinality.smallRealLargeNorm_lattice_of_dense
#print axioms CubicTwoStage.BerendCofinality.cofinalPlane_lattice_of_dense
