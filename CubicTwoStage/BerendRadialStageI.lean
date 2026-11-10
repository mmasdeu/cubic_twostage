/-
# Stage I (`ZeroNonisolatedFull`) for a pair of weighted dilations with dense
# coordinate projections

`CubicTwoStage/BerendRadialFull.lean` proves that a closed subset of the torus
`(ι → ℝ) ⧸ L` whose preimage carries the whole weighted radial flow and whose
lattice has dense coordinate projections inside and outside the support of the
weight vector is the whole torus.  This module turns that into an **instance of
the project's Stage I proposition** `BerendDichotomy.ZeroNonisolatedFull` for the
two-element family `{diag (c ^ w), diag (d ^ w)}` of torus endomorphisms, and
records the arithmetic shape of the two density hypotheses.

## The density hypotheses are the "no subgroup configuration" input

For `L = σ(𝒪)` the dual lattice is the image of the inverse different `𝔡⁻¹`
under `σ` (`Tr_{K/ℚ}(μ β) ∈ ℤ`).  A nonzero functional of the dual lattice whose
support is contained in a coordinate set `T` is exactly a nonzero `μ ∈ 𝔡⁻¹`
whose embeddings vanish off `T`; since the embeddings are injective, no such `μ`
exists as soon as `T ≠ univ`.  Hence both projections in
`BerendRadialFull.eq_univ_of_radial` are dense whenever `∅ ≠ S ≠ univ`, which is
the model situation (`|ι| = 3`, `|S| ∈ {1, 2}`).  That is the precise form in
which "no proper rational invariant subspace" (B1) enters here: the failure of
one of the two densities *is* a nonzero dual-lattice functional supported on one
side of the splitting, i.e. the subgroup configuration.
-/
import CubicTwoStage.BerendRadialFull
import CubicTwoStage.BerendDichotomy

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CubicTwoStage
namespace BerendRadialStageI

open BerendRadialFull BerendDichotomy BerendModulus BerendSec4

/-- The diagonal torus endomorphism induced by `diag (fun i => c ^ w i)`. -/
noncomputable def dilEnd {ι : Type*} [Fintype ι] [DecidableEq ι] {L : AddSubgroup (ι → ℝ)}
    (c : ℝ) (w : ι → ℕ) (h : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L) :
    (ι → ℝ) ⧸ L →+ (ι → ℝ) ⧸ L :=
  QuotientAddGroup.map L L ((diag (fun i => c ^ w i)).toAddMonoidHom) fun _ hg => h _ hg

theorem dilEnd_mk {ι : Type*} [Fintype ι] [DecidableEq ι] {L : AddSubgroup (ι → ℝ)}
    (c : ℝ) (w : ι → ℕ) (h : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L) (x : ι → ℝ) :
    dilEnd c w h (QuotientAddGroup.mk' L x) = QuotientAddGroup.mk' L (diag (fun i => c ^ w i) x) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply]
  exact QuotientAddGroup.map_mk L L _ _ x

/-- Invariance of a torus set under `dilEnd` is invariance of its preimage under
the diagonal map. -/
theorem preimage_invariant_of_image_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : AddSubgroup (ι → ℝ)} {c : ℝ} {w : ι → ℕ}
    (h : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L)
    {E : Set ((ι → ℝ) ⧸ L)} (hinv : dilEnd c w h '' E ⊆ E)
    {x : ι → ℝ} (hx : x ∈ prec L E) : diag (fun i => c ^ w i) x ∈ prec L E := by
  have hmem : dilEnd c w h (QuotientAddGroup.mk' L x) ∈ E := hinv ⟨_, hx, rfl⟩
  rwa [dilEnd_mk] at hmem

/-! ## The Stage I instance -/

section Main

variable {L : AddSubgroup (Fin 3 → ℝ)}

/-- **Every nonempty closed invariant set of the pair is the whole torus.**
This is the unconditional form of the invariance argument, from which both
Stage I and the dichotomy below follow. -/
theorem eq_univ_of_invariant
    {S : Set (Fin 3)} {w : Fin 3 → ℕ} (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hpresc : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L)
    (hpresd : ∀ g ∈ L, diag (fun i => d ^ w i) g ∈ L)
    (hdenS : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∈ S → |v i - ℓ i| < ε)
    (hdenSc : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε)
    {E : Set ((Fin 3 → ℝ) ⧸ L)} (hE : IsClosed E) (hne : E.Nonempty)
    (hinvc : dilEnd (L := L) c w hpresc '' E ⊆ E)
    (hinvd : dilEnd (L := L) d w hpresd '' E ⊆ E) :
    E = univ := by
  refine eq_univ_of_radial hE hne hwS hw0 hc hd0 hd1 hind ?_ ?_ hdenS hdenSc
  · intro x hx
    exact preimage_invariant_of_image_subset hpresc hinvc hx
  · intro x hx
    exact preimage_invariant_of_image_subset hpresd hinvd hx

/-- **Stage I for the pair `{diag (c ^ w), diag (d ^ w)}`.**  This is the
project's `BerendDichotomy.ZeroNonisolatedFull` for the two-element family of
torus endomorphisms induced by the weighted dilations, under Berend's Lemma 4.4
hypotheses (`c > 1 > d > 0`, multiplicatively independent multipliers, common
weight vector) and the two dense-projection hypotheses.

Note the hypothesis is *weaker* than Stage I asks for: only nonemptiness of `E`
is used, "zero non-isolated" is not needed. -/
theorem zeroNonisolatedFull_dil_pair
    {S : Set (Fin 3)} {w : Fin 3 → ℕ} (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hpresc : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L)
    (hpresd : ∀ g ∈ L, diag (fun i => d ^ w i) g ∈ L)
    (hdenS : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∈ S → |v i - ℓ i| < ε)
    (hdenSc : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε) :
    ZeroNonisolatedFull (fun b : Bool =>
      if b then dilEnd (L := L) c w hpresc else dilEnd (L := L) d w hpresd) := by
  intro E hE hne _hacc hinv
  exact eq_univ_of_invariant hwS hw0 hc hd0 hd1 hind hpresc hpresd hdenS hdenSc
    hE hne (by simpa using hinv true) (by simpa using hinv false)

/-- **The dichotomy (Berend Theorem 2.1, sufficiency) for the pair.**  For the
two-element family of weighted dilations, `BerendDichotomy.Dichotomy` holds
outright: every closed nonempty invariant set is the whole torus, so no proper
one exists and the "proper ⟹ finite" statement is vacuous.  This is the
conclusion of `BerendMultiInvarianceCorrected` for this family. -/
theorem dichotomy_dil_pair
    {S : Set (Fin 3)} {w : Fin 3 → ℕ} (hwS : ∀ i ∈ S, 0 < w i) (hw0 : ∀ i ∉ S, w i = 0)
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hpresc : ∀ g ∈ L, diag (fun i => c ^ w i) g ∈ L)
    (hpresd : ∀ g ∈ L, diag (fun i => d ^ w i) g ∈ L)
    (hdenS : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∈ S → |v i - ℓ i| < ε)
    (hdenSc : ∀ (v : Fin 3 → ℝ) (ε : ℝ), 0 < ε →
      ∃ ℓ ∈ L, ∀ i, i ∉ S → |v i - ℓ i| < ε) :
    Dichotomy (fun b : Bool =>
      if b then dilEnd (L := L) c w hpresc else dilEnd (L := L) d w hpresd) := by
  intro Y hY hne hinv hproper
  exact absurd
    (eq_univ_of_invariant hwS hw0 hc hd0 hd1 hind hpresc hpresd hdenS hdenSc hY hne
      (by simpa using hinv true) (by simpa using hinv false)) hproper

end Main

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendRadialStageI.dilEnd_mk
#print axioms CubicTwoStage.BerendRadialStageI.preimage_invariant_of_image_subset
#print axioms CubicTwoStage.BerendRadialStageI.eq_univ_of_invariant
#print axioms CubicTwoStage.BerendRadialStageI.zeroNonisolatedFull_dil_pair
#print axioms CubicTwoStage.BerendRadialStageI.dichotomy_dil_pair

end BerendRadialStageI
end CubicTwoStage
