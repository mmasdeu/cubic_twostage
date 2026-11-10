/-
# Cofinality of the concrete lattice of a complex cubic field

Swarm `smw952unn`, member `m6`, direction `d2`.

`BerendCofinality` proves `CofinalPlane (σ(𝒪))` for any `FieldModel` from two
inputs: a non-rational element of `𝒪` and a unit of real modulus `≠ 1`.  This
file instantiates that result at the *canonical* model of a complex cubic field
(`ComplexCubic.canonicalFieldModel`), and removes the first input entirely:

* `exists_not_rat_numberFieldO` — the ring of integers of a complex cubic field
  contains an element that is not a rational number.  (`Module.finrank ℚ K = 3`
  makes `K ≠ ℚ`, and the fraction-field property of `𝓞 K` turns a non-rational
  field element into a non-rational *integral* one.)  Hence
  `denseRangeProj (σ(𝓞 K))` holds **unconditionally** for a complex cubic field.

* `cofinalPlane_canonicalFieldModel` — `CofinalPlane (σ(𝓞 K))` from a unit `ε`
  with `|σ₁ ε| ≠ 1`.  This is the exact hypothesis `hε` of
  `BerendExpandingMember.exists_mult_margin_fieldModel_of_ne_one`: an infinite
  order unit (the project's `hεpow`) is never critical at the real place, since
  a unit of modulus one at every place is a root of unity.

* `zeroNonisolatedFull_canonical_torusAct_of_annulusInput` — the accepted block
  last mile of `BerendBlockLastMile` with its `hc : CofinalPlane` hypothesis now
  discharged for the canonical model.

No `sorry`, no new axiom, no use of `berend_multi_invariance`.
-/
import CubicTwoStage.BerendCofinality
import CubicTwoStage.ComplexCubic

open Set

set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendCofinality

open NumberField
open NumberFieldCubic

variable (K : Type*) [Field K] [NumberField K]

/-! ## 1. `𝓞 K` contains a non-rational element -/

/-- **A complex cubic field is not `ℚ`.**  There is a field element that is not
the image of a rational number; otherwise `K` would be one-dimensional over `ℚ`,
contradicting `finrank ℚ K = 3`. -/
theorem exists_not_rat_of_isComplexCubic (h : IsComplexCubic K) :
    ∃ x : K, ∀ q : ℚ, x ≠ (q : K) := by
  by_contra hcon
  push Not at hcon
  have hspan : Submodule.span ℚ ({(1 : K)} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨q, rfl⟩ := hcon x
    have hq : (q : K) = q • (1 : K) := (Rat.smul_one_eq_cast K q).symm
    rw [hq]
    exact Submodule.smul_mem _ q (Submodule.subset_span (Set.mem_singleton 1))
  have h1 : Module.finrank ℚ (Submodule.span ℚ ({(1 : K)} : Set K)) = 1 :=
    finrank_span_singleton (one_ne_zero)
  rw [hspan, finrank_top] at h1
  have h3 : Module.finrank ℚ K = 3 := h.1
  omega

/-- **The ring of integers of a complex cubic field contains a non-rational
element.**  `𝓞 K` has fraction field `K`, so a non-rational `x ∈ K` is a
quotient `a / b` of integral elements; if both `a` and `b` were rational, so
would be `x`. -/
theorem exists_not_rat_numberFieldO (h : IsComplexCubic K) :
    ∃ b : numberFieldO K, ∀ q : ℚ, ((b : numberFieldO K) : K) ≠ (q : K) := by
  obtain ⟨x, hx⟩ := exists_not_rat_of_isComplexCubic K h
  have hfr : IsFractionRing (numberFieldO K) K := inferInstanceAs (IsFractionRing (𝓞 K) K)
  obtain ⟨a, b, hbne, hab⟩ := IsFractionRing.div_surjective (numberFieldO K) x
  by_cases ha : ∃ q : ℚ, ((a : numberFieldO K) : K) = (q : K)
  · refine ⟨b, ?_⟩
    intro q hbq
    obtain ⟨qa, hqa⟩ := ha
    refine hx (qa / q) ?_
    have hqa' : (algebraMap (numberFieldO K) K) a = (qa : K) := hqa
    have hbq' : (algebraMap (numberFieldO K) K) b = (q : K) := hbq
    rw [← hab, hqa', hbq', Rat.cast_div]
  · exact ⟨a, fun q hq => ha ⟨q, hq⟩⟩

/-- **Density of the real-coordinate projection of `σ(𝓞 K)`**, unconditionally
for a complex cubic field. -/
theorem denseRangeProj_canonicalFieldModel (h : IsComplexCubic K) :
    BerendBlockLastMile.denseRangeProj (canonicalFieldModel K h).lattice := by
  obtain ⟨b, hb⟩ := exists_not_rat_numberFieldO K h
  exact denseRangeProj_lattice (canonicalFieldModel K h) hb

/-! ## 2. The unit of real modulus `≠ 1` -/

/-- **`SmallRealLargeNorm` for the canonical lattice**, from a unit whose real
embedding is not of modulus one. -/
theorem smallRealLargeNorm_canonicalFieldModel (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ)
    (hε : |realEmbedding K h (((ε : numberFieldO K) : K))| ≠ 1) :
    BerendBlockLastMile.SmallRealLargeNorm (canonicalFieldModel K h).lattice := by
  refine smallRealLargeNorm_lattice_of_ne_one (canonicalFieldModel K h) ε ?_
  rw [lamAbs_zero_eq_abs]
  simpa [NumberFieldCubic.canonicalFieldModel] using hε

/-- **The concrete cofinality input for a complex cubic field**: `CofinalPlane`
for the lattice `σ(𝓞 K)` of the canonical model, from a unit that is not of
modulus one at the real place. -/
theorem cofinalPlane_canonicalFieldModel (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ)
    (hε : |realEmbedding K h (((ε : numberFieldO K) : K))| ≠ 1) :
    BerendBlockLastMile.CofinalPlane (canonicalFieldModel K h).lattice :=
  BerendBlockLastMile.cofinalPlane_of_farAtHeight
    (BerendBlockLastMile.farAtHeight_of_dense_proj
      (denseRangeProj_canonicalFieldModel K h)
      (smallRealLargeNorm_canonicalFieldModel K h ε hε))

/-- **Cofinality of the canonical complex-cubic lattice, with no unit
hypothesis.**  The real projection is dense because the ring of integers
contains a non-rational element; density alone then supplies the required
small-real/large-complex-norm lattice elements. -/
theorem cofinalPlane_canonicalFieldModel_of_isComplexCubic (h : IsComplexCubic K) :
    BerendBlockLastMile.CofinalPlane (canonicalFieldModel K h).lattice :=
  cofinalPlane_lattice_of_dense (canonicalFieldModel K h)
    (denseRangeProj_canonicalFieldModel K h)

/-! ## 3. Plugging into the accepted block last mile -/

/-- **Stage I for the canonical model of a complex cubic field, from one plane
annulus.**  This is
`BerendBlockLastMile.zeroNonisolatedFull_torusAct_of_annulusInput` with the
cofinality hypothesis `hc` *proved* rather than assumed.  What remains is exactly
the annulus input (direction d3) and the expanding member's margin (available
from `BerendExpandingMember.exists_mult_margin_fieldModel_of_ne_one`). -/
theorem zeroNonisolatedFull_canonical_torusAct_of_annulusInput (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hε : |realEmbedding K h (((ε : numberFieldO K) : K))| ≠ 1)
    (u : (numberFieldO K)ˣ) (j : ℕ)
    (hC : 16 ≤ normC (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult u j))
    (hann : ∀ Y : Set (Torus (canonicalFieldModel K h).lattice), IsClosed Y → Y.Nonempty →
      (0 : Torus (canonicalFieldModel K h).lattice) ∈ closure (Y \ {0}) →
      BerendDichotomy.FamilyInvariant
        ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct Y →
      ∃ ρ1 ρ2 : ℝ, 0 < ρ1 ∧ ρ1 ≤ ρ2 ∧
        ‖cplxOf (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult u j)‖ * ρ1 ≤ ρ2 ∧
        ∀ w : Pt, w ∈ BerendBlockLastMile.cplxPlane →
          ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 →
          (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) w ∈ Y) :
    BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  BerendBlockLastMile.zeroNonisolatedFull_torusAct_of_annulusInput
    ((canonicalFieldModel K h).toModel ε π hπO hπ0)
    (cofinalPlane_canonicalFieldModel K h ε hε) u j hC hann

end BerendCofinality
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendCofinality.exists_not_rat_of_isComplexCubic
#print axioms CubicTwoStage.BerendCofinality.exists_not_rat_numberFieldO
#print axioms CubicTwoStage.BerendCofinality.denseRangeProj_canonicalFieldModel
#print axioms CubicTwoStage.BerendCofinality.smallRealLargeNorm_canonicalFieldModel
#print axioms CubicTwoStage.BerendCofinality.cofinalPlane_canonicalFieldModel
#print axioms CubicTwoStage.BerendCofinality.cofinalPlane_canonicalFieldModel_of_isComplexCubic
#print axioms CubicTwoStage.BerendCofinality.zeroNonisolatedFull_canonical_torusAct_of_annulusInput
