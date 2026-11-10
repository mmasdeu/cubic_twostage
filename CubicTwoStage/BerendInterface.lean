/-
# Interface check: the project's deep `Prop` is the dichotomy of `BerendDichotomy`

`CubicTwoStage/BerendCorrected.lean` states Berend's Theorem 2.1 (sufficiency) as
the `Prop` `BerendMultiInvarianceCorrected`, and every downstream statement
(`berend_multi_invariance_corrected`, `UnitPrimeModel.berend_corrected`,
`finite_torus_image_of_orbit_avoid_corrected`) consumes it.  The plan's stages C/D
aim at proving it.

This module removes any doubt about *statement matching*: the project's `Prop` is
literally the dichotomy of `CubicTwoStage/BerendDichotomy.lean` for the concrete
family `fun i => torusEnd L (f i) (hpres i)`, so a proof of either is a proof of
the other with no rewriting, and `BerendDichotomy.dichotomy_iff_noProperFullDiffSet`
(the amended §D.5 equivalence) applies to it verbatim.

Also here: a nontrivial full torus is never a *minimal* invariant set — the side
condition that `BEREND_PROOF_PLAN.md` §D attaches to Proposition IV.1.

Axiom free: imports only `CubicTwoStage.BerendDichotomy` and
`CubicTwoStage.BerendCorrected`; no new axiom, no `sorry`.
-/
import CubicTwoStage.BerendDichotomy
import CubicTwoStage.BerendCorrected

open scoped TensorProduct Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendInterface

open BerendDichotomy

variable {L : AddSubgroup Pt} [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- The project's torus is nontrivial (it is uncountable). -/
theorem nontrivial_torus : Nontrivial (Pt ⧸ L) := by
  haveI : Infinite (Pt ⧸ L) := BerendDichotomy.infinite_torus
  infer_instance

/-- **The project's deep `Prop` *is* the dichotomy** for the concrete family of
toral endomorphisms: `BerendMultiInvarianceCorrected ... ↔ Dichotomy (fun i =>
torusEnd L (f i) (hpres i))`. -/
theorem berendCorrected_iff_dichotomy {κ : Type*} (f : κ → Pt ≃ₗ[ℝ] Pt)
    (M : AddSubgroup Pt) (hpres : ∀ (i : κ) (g : Pt), g ∈ M → f i g ∈ M)
    [DiscreteTopology (AddSubgroup.toIntSubmodule M)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule M))
    (B1 : ∃ i : κ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeActZ M ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : κ → ℂ), x ≠ 0 →
      (∀ i : κ, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : κ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x)) :
    BerendMultiInvarianceCorrected κ f M hpres hZ B1 B2 B3 hcomm ↔
      Dichotomy (fun i => torusEnd M ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i)) :=
  Iff.rfl

/-- Consequently the amended §D.5 equivalence applies to the project's own `Prop`:
given Stage I for the concrete family, `BerendMultiInvarianceCorrected` is
equivalent to its residual form "no proper closed invariant set has full difference
set". -/
theorem berendCorrected_iff_diffSet {κ : Type*} (f : κ → Pt ≃ₗ[ℝ] Pt)
    (M : AddSubgroup Pt) (hpres : ∀ (i : κ) (g : Pt), g ∈ M → f i g ∈ M)
    [DiscreteTopology (AddSubgroup.toIntSubmodule M)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule M))
    (B1 : ∃ i : κ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeActZ M ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : κ → ℂ), x ≠ 0 →
      (∀ i : κ, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : κ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    (hStage : ZeroNonisolatedFull
      (fun i => torusEnd M ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i))) :
    BerendMultiInvarianceCorrected κ f M hpres hZ B1 B2 B3 hcomm ↔
      NoProperFullDiffSet
        (fun i => torusEnd M ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i)) := by
  haveI : CompactSpace (Pt ⧸ M) := compact_quotient_of_isZLattice M
  haveI : Infinite (Pt ⧸ M) := BerendDichotomy.infinite_torus
  rw [berendCorrected_iff_dichotomy f M hpres hZ B1 B2 B3 hcomm]
  exact dichotomy_iff_noProperFullDiffSet hStage

/-- In particular the side condition of Proposition IV.1 holds at the project's
torus: the whole torus is not a minimal invariant set, because `{0}` is a proper
closed nonempty invariant subset. -/
theorem not_isMinimalInvariant_univ_torus {κ : Type*} [Nonempty κ]
    (G : κ → (Pt ⧸ L) →+ (Pt ⧸ L)) :
    ¬ BerendMinimal.IsMinimalInvariant (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L)))
      (Set.univ : Set (Pt ⧸ L)) := by
  haveI : Nontrivial (Pt ⧸ L) := nontrivial_torus
  exact BerendDichotomy.not_isMinimalInvariant_univ (F := G)

end BerendInterface

end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendInterface.nontrivial_torus
#print axioms CubicTwoStage.BerendInterface.berendCorrected_iff_dichotomy
#print axioms CubicTwoStage.BerendInterface.berendCorrected_iff_diffSet
#print axioms CubicTwoStage.BerendInterface.not_isMinimalInvariant_univ_torus
