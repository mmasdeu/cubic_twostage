/-
# Bridge: `BerendCorrected`'s private copies of the torus API agree definitionally
with the ones in `CubicTwoStage/Berend.lean`

`CubicTwoStage/BerendCorrected.lean` names none of the definitions of
`CubicTwoStage/Berend.lean`, so that it can be read and audited without the
axiom `berend_multi_invariance` in view; it repeats four of them verbatim under
its own names: `torusEnd`, `latticeActZ`, `lactZ`, `torusEndAct`.

Caveat, stated plainly: `CubicTwoStage.Berend` *is* imported transitively
(`CubicTwoStage.RationalIndependence` -> `CubicTwoStage.FieldModel` ->
`CubicTwoStage.Uncovered` -> `CubicTwoStage.Berend`), so "the axiom is out of
scope" is not what is being claimed.  What is claimed, and checked by
`CubicTwoStage/BerendCheck.lean`, is that **no theorem of the new modules
depends on it**.

This file checks that the four copies are *definitionally equal* to
`torusMap`, `latticeAct`, `lact` and `torusAct`.  Consequently a proof of
`BerendMultiInvarianceCorrected` discharges `UnitPrimeModel.berend` of
`CubicTwoStage/Berend.lean` with no rewriting.
-/
import CubicTwoStage.Berend
import CubicTwoStage.BerendCorrected

open scoped TensorProduct

set_option linter.unusedVariables false

namespace CubicTwoStage

theorem torusEnd_eq_torusMap (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L) :
    torusEnd L f hf = torusMap L f hf := rfl

theorem latticeActZ_eq_latticeAct (L : AddSubgroup Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L) :
    @latticeActZ L f hf = @latticeAct L f hf := rfl

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

theorem lactZ_eq_lact (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    D.lactZ i = D.lact i := rfl

theorem torusEndAct_eq_torusAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    D.torusEndAct i = D.torusAct i := rfl

/-- Hence a proof of the corrected statement discharges the *conclusion* of the
old `UnitPrimeModel.berend` for the corrected (B3) — with the axiom unused. -/
theorem UnitPrimeModel.berend_of_corrected (D : UnitPrimeModel L 𝒪)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lact i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair D.linFam)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZ B1 B2 B3
      D.linFam_comm)
    (Y : Set (Torus L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : 𝒪ˣ × ℕ, D.torusAct i '' Y ⊆ Y) :
    Y ≠ Set.univ → Y.Finite :=
  H Y hclosed hne hinv

/-- **The corrected statement gives the exact conclusion of the old axiom**, with
the corrected (B3), for an arbitrary commuting family.  This is the form in
which `CubicTwoStage/Berend.lean`'s `berend_multi_invariance` is consumed: the
conclusion has the same shape, the hypothesis is an explicitly proved `Prop`
instead of an axiom. -/
theorem berend_multi_invariance_of_corrected (ι : Type*) (f : ι → Pt ≃ₗ[ℝ] Pt)
    (L : AddSubgroup Pt) (hpres : ∀ (i : ι) (g : Pt), g ∈ L → f i g ∈ L)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : ι, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeAct L ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : ι → ℂ), x ≠ 0 →
      (∀ i : ι, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : ι, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    (H : BerendMultiInvarianceCorrected ι f L hpres hZ B1 B2 B3 hcomm)
    (Y : Set (Torus L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : ι, (fun y => torusMap L ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom
      (hpres i) y) '' Y ⊆ Y) :
    Y ≠ Set.univ → Y.Finite :=
  fun hproper => H Y hclosed hne hinv hproper

#print axioms berend_multi_invariance_of_corrected

/-- The old `CubicTwoStage.berend_multi_invariance` follows from a proof of the
corrected statement (with the corrected (B3), which the model satisfies
unconditionally by `rational_independence_corrected`). -/
theorem berend_multi_invariance_from_corrected (ι : Type*) (f : ι → Pt ≃ₗ[ℝ] Pt)
    (L : AddSubgroup Pt) (hpres : ∀ (i : ι) (g : Pt), g ∈ L → f i g ∈ L)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : ι, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeAct L ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : ι → ℂ), x ≠ 0 →
      (∀ i : ι, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : ι, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    (H : BerendMultiInvarianceCorrected ι f L hpres hZ B1 B2 B3 hcomm)
    (B3old : RationallyIndependentPairOld f)
    (Y : Set (Torus L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : ι, (fun y => torusMap L ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom
      (hpres i) y) '' Y ⊆ Y) :
    Y ≠ Set.univ → Y.Finite :=
  berend_multi_invariance_of_corrected ι f L hpres hZ B1 B2 B3 hcomm H Y hclosed hne hinv

#print axioms torusEnd_eq_torusMap
#print axioms UnitPrimeModel.berend_of_corrected

end CubicTwoStage
