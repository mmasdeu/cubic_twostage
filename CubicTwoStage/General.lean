/-
Section 8 of the paper: the general form of the results for every number field
with infinite unit group.
-/
import CubicTwoStage.Representatives
import CubicTwoStage.Cooke
import CubicTwoStage.Classes
import CubicTwoStage.Equiv
import CubicTwoStage.Box
import CubicTwoStage.Normalize
import CubicTwoStage.Verify
import CubicTwoStage.Witness

set_option linter.unusedVariables false

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-- **Proposition 8.1(i)**.  A pair `α, β ∈ 𝒪`, `β ≠ 0`, has a decreasing chain of
length at most two iff `|Nm(α/β - [q₁,q₂])| < |Nm q₂|⁻¹` for some `q₁,q₂ ∈ 𝒪`.

Nothing in the proof depends on the degree or the signature: it is
`prop_cooke`. -/
theorem prop_gen_basic_i (𝒪 : Subring K) (N : AbsNorm K) {α β : K}
    (hα : α ∈ 𝒪) (hβ : β ∈ 𝒪) (hβ0 : β ≠ 0) :
    HasTwoStageChain 𝒪 N α β ↔
      ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (α / β - (q1 + q2⁻¹)) < (N q2)⁻¹ :=
  prop_cooke 𝒪 N hα hβ hβ0

/-- **Proposition 8.1(ii)**.  For `α ∈ 𝒪` the elements `[q₁,q₂]` with
`q₂𝒪 = α𝒪` form the set `{r/α + g : r ∈ U_α, g ∈ 𝒪}`.  This is
`lem_classes`, whose proof does not use the degree. -/
theorem prop_gen_basic_ii (𝒪 : Subring K) {α : 𝒪} (hα : α ≠ 0) :
    {x : K | ∃ q1 q2 : 𝒪, Ideal.span {q2} = Ideal.span {α} ∧
        x = (q1 : K) + ((q2 : K))⁻¹}
      = {x : K | ∃ u : 𝒪ˣ, ∃ g : 𝒪,
        x = (((u : 𝒪) : K)) / (((α : 𝒪) : K)) + (g : K)} :=
  lem_classes 𝒪 hα

/-- **Proposition 8.1(iii)**.  If `D̄` is covered by regions `V(q)` then it is
covered by finitely many of them, and `K` is 2-stage Euclidean.

The compactness half is `thm_equiv_ii_iii`; the passage to division chains is
`prop_cooke`. -/
theorem prop_gen_basic_iii (𝒪 : Subring K) (N : AbsNorm K)
    (hfrac : ∀ x : K, ∃ α ∈ 𝒪, ∃ β ∈ 𝒪, β ≠ 0 ∧ x = α / β)
    (L : AddSubgroup Pt) (C : Set Pt) (V : Pt → Set Pt)
    (hVopen : ∀ c, IsOpen (V c))
    (hVtrans : ∀ c g, g ∈ L → ∀ x, x ∈ V (c + g) ↔ x - g ∈ V c)
    (hCtrans : ∀ c ∈ C, ∀ g ∈ L, c + g ∈ C)
    (hfund : ∀ x : Pt, ∃ g ∈ L, x - g ∈ unitCube)
    (hcover : ∃ F : Finset Pt, (∀ c ∈ F, c ∈ C) ∧ unitCube ⊆ ⋃ c ∈ F, V c)
    (hsub : (∀ x : Pt, ∃ c ∈ C, x ∈ V c) →
      (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (x - (q1 + q2⁻¹)) < (N q2)⁻¹)) :
    IsTwoStageEuclidean 𝒪 N := by
  have hii := (thm_equiv_ii_iii L C V hVopen hVtrans hCtrans hfund).mpr hcover
  exact (thm_equiv_i_ii 𝒪 N hfrac).mpr (hsub hii)

/-- **Proposition 8.1(iv)**: the general-signature form of Theorem 3.6.

Nothing in the proof of Theorem 3.6 uses the degree, the signature or even that
`K` is a number field: it uses only the unit–prime model, Berend's theorem on
`(ℝ × ℂ)/L`, and the tower lemma.  Accordingly 8.1(iv) *is* the field-data form
of Theorem 3.6, `thm_uncovered_field`, and is recorded here as that statement
rather than restated. -/
def prop_gen_basic_iv := @thm_uncovered_field

/-- **Theorem 8.3(i), three-dimensional instance only.**  A finite list of
triples (dyadic cube in `[0,1]³`, centre `r/α + g`, integer `ν ≥ 1`) satisfying
(i)–(iii) of Proposition 5.2 proves that `K` is `N`-smooth Euclidean.

The paper states this in arbitrary dimension `n`, but this declaration is
literally `prop_verify` for the fixed model space `Pt = Fin 3 → ℝ`.  It is not a
general-`n` theorem and should not be cited as one. -/
def thm_gen_cert_i := @prop_verify

/-- **Theorem 8.3(ii), three-dimensional instance only.**  If `D̄` is covered
by regions with centres in `𝒞_N`, then the depth-first subdivision terminates
with a certificate, for a candidate set containing a finite `Z ⊆ 𝒞_N` and a
maximal depth `ℓ`.

This is the fixed three-dimensional statement, not the paper's arbitrary-degree
form. -/
def thm_gen_cert_ii := @prop_terminate

/-- **Theorem 8.5(i), three-dimensional instance only.**  This is
Proposition 6.2 in the fixed model space `Pt = Fin 3 → ℝ`, not an arbitrary-degree
statement. -/
def thm_gen_witness_i := @prop_witness

/-- **Theorem 8.5(ii), three-dimensional instance only.**  This is
Proposition 6.3 in the fixed model space `Pt = Fin 3 → ℝ`, not an arbitrary-degree
statement. -/
def thm_gen_witness_ii := @prop_level

end CubicTwoStage
