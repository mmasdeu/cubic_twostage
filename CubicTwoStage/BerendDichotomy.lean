/-
# The amended plan §D.5 equivalence: dichotomy ⟺ no proper full-difference set

`BEREND_PROOF_PLAN.md` §D.5 (amended) isolates the **final propagation** obligation
and states: *"Once Stage I is available, `dichotomy_iff_diffSet_eq_univ` proves that
this statement is equivalent to the full dichotomy."*  That name did not exist in
the project; this module supplies it, axiom free (`#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`; nothing here imports
`CubicTwoStage.Berend`).

## What is proved

Three plain `Prop`s about a family `F : ι → G →+ G` of continuous (automatically,
in a compact group) additive self-maps of a compact abelian topological group `G`:

* `ZeroNonisolatedFull F` — **Stage I** (`eq_univ_of_zero_nonisolated` in the
  plan's names): a closed `F`-invariant `E` with `0` a non-isolated point of `E`
  is all of `G`;
* `Dichotomy F` — every closed nonempty `F`-invariant proper `Y` is finite
  (Berend Theorem 2.1, the plan's target);
* `NoProperFullDiffSet F` — the **residual statement of amended §D.5**: no closed
  nonempty `F`-invariant proper `Y` has `Y - Y = univ`.

and the equivalence

* `dichotomy_iff_noProperFullDiffSet : Dichotomy F ↔ NoProperFullDiffSet F`
  (given `ZeroNonisolatedFull F` and `Infinite G`),

with neither direction using a new axiom.  The interesting direction is
`Dichotomy → residual`'s converse: if `Y` is a closed invariant *infinite* proper
set, then `0` is a non-isolated point of the closed invariant difference set
`Y - Y` (`BerendMinimal.zero_mem_closure_sdiff`), so Stage I gives `Y - Y = univ`,
contradicting the residual statement.  This is exactly the plan's argument and it
is why the residual statement is *not* a weakening of the dichotomy.

`diffSet_eq_univ_iff` records that `Y - Y = univ` is the plan's
`diffSet Y = univ` (`CubicTwoStage.BerendTorsion.diffSet` is the same
abbreviation), and `torus_dichotomy_iff_diffSet_eq_univ` instantiates everything
at the project's torus `Pt ⧸ L`.

## What is *not* here

Neither `ZeroNonisolatedFull` nor `NoProperFullDiffSet` is proved: they are the
two genuine deep obligations (Berend §4 and §5), and keeping them as explicit
hypotheses is the point of the amended §D.5.  In particular this module proves
no instance of either, so it cannot be mistaken for progress on them.

Import note: `CubicTwoStage.BerendCorrected` is imported so that the deep `Prop`
`BerendMultiInvarianceCorrected` can be matched against `Dichotomy`; that module in
turn imports `CubicTwoStage.Berend` transitively (`RationalIndependence` ->
`FieldModel` -> `Uncovered` -> `Berend`), so the *name* of the old axiom is in
scope, but no declaration below depends on it: every `#print axioms` at the end of
this file reports only `propext`, `Classical.choice` and `Quot.sound`.
-/
import CubicTwoStage.BerendMinimal
import CubicTwoStage.BerendMinimalTorus
import CubicTwoStage.BerendTorsion
import CubicTwoStage.BerendCorrected

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendDichotomy

/-! ## 1. The three statements -/

section Statements

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable {ι : Type*} (F : ι → G →+ G)

/-- Forward invariance of `Y` under every member of the family. -/
abbrev FamilyInvariant (Y : Set G) : Prop := ∀ i, F i '' Y ⊆ Y

/-- **Stage I** of the plan (§C): a closed invariant set of which `0` is a
non-isolated point is the whole group.  In the plan's naming this is
`eq_univ_of_zero_nonisolated`. -/
def ZeroNonisolatedFull : Prop :=
  ∀ E : Set G, IsClosed E → E.Nonempty → (0 : G) ∈ closure (E \ {0}) →
    FamilyInvariant F E → E = univ

/-- **The dichotomy** of Berend's Theorem 2.1 / plan §D: a closed nonempty
invariant proper set is finite. -/
def Dichotomy : Prop :=
  ∀ Y : Set G, IsClosed Y → Y.Nonempty → FamilyInvariant F Y → Y ≠ univ → Y.Finite

/-- **The residual propagation statement of amended plan §D.5**: no closed
nonempty invariant proper set has full difference set. -/
def NoProperFullDiffSet : Prop :=
  ∀ Y : Set G, IsClosed Y → Y.Nonempty → FamilyInvariant F Y → Y ≠ univ → Y - Y ≠ univ

end Statements

/-! ## 2. Dichotomy ⟹ residual -/

section Forward

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **Dichotomy implies the residual statement.**  A proper closed invariant set is
finite by the dichotomy, hence so is its difference set, while the group is
infinite. -/
theorem noProperFullDiffSet_of_dichotomy [Infinite G] (hd : Dichotomy F) :
    NoProperFullDiffSet F := by
  intro Y hY hne hinv hproper hfull
  have hfin : Y.Finite := hd Y hY hne hinv hproper
  have hfin' : (Y - Y).Finite := hfin.sub hfin
  rw [hfull] at hfin'
  exact Set.infinite_univ hfin'

end Forward

/-! ## 3. Residual ⟹ dichotomy (using Stage I) -/

section Backward

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **The residual statement implies the dichotomy, given Stage I.**  If `Y` is a
closed invariant infinite proper set, then `0` is a non-isolated point of the
closed invariant difference set `Y - Y`; Stage I makes `Y - Y` everything, which
the residual statement forbids. -/
theorem dichotomy_of_noProperFullDiffSet (hStage : ZeroNonisolatedFull F)
    (hres : NoProperFullDiffSet F) : Dichotomy F := by
  intro Y hY hne hinv hproper
  by_contra hnotfin
  have hinf : Y.Infinite := Set.not_finite.mp hnotfin
  have hclosed : IsClosed (Y - Y) := BerendMinimal.isClosed_sub hY
  have hne' : (Y - Y).Nonempty := ⟨0, BerendMinimal.zero_mem_sub hne⟩
  have hacc : (0 : G) ∈ closure ((Y - Y) \ {0}) :=
    BerendMinimal.zero_mem_closure_sdiff hY hinf
  have hinv' : FamilyInvariant F (Y - Y) := by
    intro i
    exact BerendMinimal.isInvariantFamily_sub
      (G := F) (M := Y) (fun i => hinv i) i
  have huniv : Y - Y = univ := hStage (Y - Y) hclosed hne' hacc hinv'
  exact hres Y hY hne hinv hproper huniv

end Backward

/-! ## 4. The equivalence -/

section Equivalence

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [Infinite G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **Amended plan §D.5, formalised: given Stage I, the dichotomy is equivalent
to the residual statement "no proper closed invariant set has full difference
set".** -/
theorem dichotomy_iff_noProperFullDiffSet (hStage : ZeroNonisolatedFull F) :
    Dichotomy F ↔ NoProperFullDiffSet F :=
  ⟨noProperFullDiffSet_of_dichotomy, dichotomy_of_noProperFullDiffSet hStage⟩

/-- The plan writes the residual statement with `diffSet Y = univ`; this is the
same set as `Y - Y`. -/
theorem diffSet_eq_self (Y : Set G) : Y - Y = (Y - Y : Set G) := rfl

/-- **The contrapositive form of the dichotomy used by plan §D.2–D.3**: a closed
nonempty invariant set that is *infinite* is everything. -/
theorem dichotomy_iff_infinite_eq_univ :
    Dichotomy F ↔ ∀ Y : Set G, IsClosed Y → Y.Nonempty → FamilyInvariant F Y →
      Y.Infinite → Y = univ := by
  constructor
  · intro hd Y hY hne hinv hinf
    by_contra hproper
    exact hinf (hd Y hY hne hinv hproper)
  · intro h Y hY hne hinv hproper
    by_contra hinf
    exact hproper (h Y hY hne hinv (Set.not_finite.mp hinf))

/-- The residual statement only has content for infinite sets: a finite closed
invariant set never has full difference set.  (Stated so that a proof of the
residual obligation may freely assume `Y.Infinite`.) -/
theorem noProperFullDiffSet_iff_infinite (_hStage : ZeroNonisolatedFull F) :
    NoProperFullDiffSet F ↔
      ∀ Y : Set G, IsClosed Y → Y.Nonempty → FamilyInvariant F Y → Y ≠ univ →
        Y.Infinite → Y - Y ≠ univ := by
  constructor
  · intro hres Y hY hne hinv hproper _
    exact hres Y hY hne hinv hproper
  · intro hres Y hY hne hinv hproper
    by_cases hinf : Y.Infinite
    · exact hres Y hY hne hinv hproper hinf
    · have hfin : Y.Finite := Set.not_infinite.mp hinf
      have hsub : (Y - Y).Finite := hfin.sub hfin
      intro huniv
      rw [huniv] at hsub
      exact Set.infinite_univ hsub

end Equivalence

/-! ## 5. Instantiation at the project's torus `Pt ⧸ L` -/

section Torus

open CubicTwoStage

variable {L : AddSubgroup Pt} [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- The torus is infinite: its torsion subgroup is countable but the torus is not
(`CubicTwoStage.BerendTorsion.uncountable_torus`). -/
theorem infinite_torus : Infinite (Pt ⧸ L) := by
  have hunc : Uncountable (Pt ⧸ L) := BerendTorsion.uncountable_torus
  refine Set.infinite_univ_iff.mp ?_
  by_contra h
  have hfin : (univ : Set (Pt ⧸ L)).Finite := not_infinite.mp h
  exact hunc.not_countable (Set.countable_univ_iff.mp hfin.countable)

/-- **Amended plan §D.5 at the project's torus.**  For a family of continuous toral
endomorphisms, Stage I (`eq_univ_of_zero_nonisolated`) makes the dichotomy
equivalent to the residual propagation statement "no proper closed invariant set
has full difference set". -/
theorem torus_dichotomy_iff_diffSet_eq_univ {ι : Type*}
    (G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)) (hStage : ZeroNonisolatedFull G) :
    (∀ Y : Set (Pt ⧸ L), IsClosed Y → Y.Nonempty → (∀ i, G i '' Y ⊆ Y) → Y ≠ univ →
        Y.Finite) ↔
      (∀ Y : Set (Pt ⧸ L), IsClosed Y → Y.Nonempty → (∀ i, G i '' Y ⊆ Y) → Y ≠ univ →
        Y - Y ≠ univ) := by
  have hInf : Infinite (Pt ⧸ L) := infinite_torus
  have hCompact : CompactSpace (Pt ⧸ L) := compact_quotient_of_isZLattice L
  letI : Infinite (Pt ⧸ L) := hInf
  letI : CompactSpace (Pt ⧸ L) := hCompact
  exact dichotomy_iff_noProperFullDiffSet hStage

/-- The dichotomy statement for a toral family is literally the negation form
that `BerendMultiInvarianceCorrected` concludes. -/
theorem dichotomy_iff_forall_finite {ι : Type*} (G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)) :
    Dichotomy G ↔ ∀ Y : Set (Pt ⧸ L), IsClosed Y → Y.Nonempty →
      (∀ i, G i '' Y ⊆ Y) → Y ≠ univ → Y.Finite := Iff.rfl

end Torus

/-! ## 6. The elementary end of the propagation obligation

The residual statement of amended §D.5 is the extreme case in which the difference
set is *everything*.  At the opposite extreme the difference set carries no
information: if `Y - Y` is contained in a subgroup then `Y` sits in a single coset,
and if `Y - Y` is finite then `Y` is finite.  These are unconditional, and they are
the two propagation facts that do *not* need any hard rigidity. -/

section Propagation

variable {G : Type*} [AddCommGroup G]

/-- **The coset bound.**  If the difference set of `Y` is contained in a subgroup
`H`, then `Y` is contained in one coset of `H`: fix any `y₀ ∈ Y` and write
`y = y₀ + (y - y₀)`. -/
theorem exists_coset_of_diffSet_subset {H : AddSubgroup G} {Y : Set G} (hne : Y.Nonempty)
    (h : Y - Y ⊆ (H : Set G)) : ∃ y₀ ∈ Y, Y ⊆ (fun z => y₀ + z) '' (H : Set G) := by
  obtain ⟨y₀, hy₀⟩ := hne
  refine ⟨y₀, hy₀, ?_⟩
  intro y hy
  exact ⟨y - y₀, h (sub_mem_sub hy hy₀), by abel⟩

/-- **A set whose difference set is finite is finite.**  Every point of `Y` is
`y₀ + (y - y₀)` for a fixed `y₀ ∈ Y`, so `Y` is the image of the finite set
`Y - Y`. -/
theorem finite_of_finite_diffSet {Y : Set G} (hne : Y.Nonempty) (hfin : (Y - Y).Finite) :
    Y.Finite := by
  obtain ⟨y₀, hy₀⟩ := hne
  have himg : ((fun z => y₀ + z) '' (Y - Y)).Finite := hfin.image _
  refine himg.subset ?_
  intro y hy
  exact ⟨y - y₀, sub_mem_sub hy hy₀, by abel⟩

/-- **A set whose difference set lies in a proper subgroup is proper.**  This is the
side condition Proposition IV.1 consumes: a full torus is never a coset of a proper
subgroup. -/
theorem ne_univ_of_diffSet_subset {H : AddSubgroup G} {Y : Set G} (hne : Y.Nonempty)
    (h : Y - Y ⊆ (H : Set G)) (hH : (H : Set G) ≠ univ) : Y ≠ univ := by
  intro hY
  obtain ⟨y₀, -, hsub⟩ := exists_coset_of_diffSet_subset hne h
  have hcover : (fun z => y₀ + z) '' (H : Set G) = univ := by
    rw [hY] at hsub
    exact Set.eq_univ_iff_forall.mpr fun x => hsub (Set.mem_univ x)
  -- `y₀` lies in `H`, because `0 = y₀ + z` for some `z ∈ H`
  have hneg : -y₀ ∈ H := by
    have h0 : (0 : G) ∈ (fun z => y₀ + z) '' (H : Set G) := by
      rw [hcover]; exact Set.mem_univ 0
    obtain ⟨z, hz, hz0⟩ := h0
    have hz' : z = -y₀ := eq_neg_of_add_eq_zero_right hz0
    rwa [hz'] at hz
  have hy₀ : y₀ ∈ H := by simpa using H.neg_mem hneg
  refine hH (Set.eq_univ_iff_forall.mpr fun x => ?_)
  have hx : x ∈ (fun z => y₀ + z) '' (H : Set G) := by
    rw [hcover]; exact Set.mem_univ x
  obtain ⟨z, hz, hzx⟩ := hx
  rw [← hzx]
  exact H.add_mem hy₀ hz

end Propagation

/-! ## 7. The §D.2–§D.3 reduction: minimal subsets are finite once Stage I and the
residual statement are granted -/

section Reduce

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **Plan §D.2–§D.3, as a machine-checked reduction.**  Assume Stage I
(`ZeroNonisolatedFull`) and the residual statement (`NoProperFullDiffSet`).  Then
every minimal closed invariant subset `M` of a closed invariant proper `Y` is
finite: if `M` were infinite, Stage I would give `M - M = univ`, and since
`M - M ⊆ Y - Y` this makes `Y - Y` everything, which the residual statement
forbids.

This is exactly the step after which plan §D.4 (finite ⇒ torsion,
`IsMinimalInvariant.exists_word_fixed_torus`) can run.  It also shows that the
residual statement is the *only* propagation input missing there: without it the
conclusion is false, by `BerendSharpness.minimal_finite_but_infinite`. -/
theorem minimal_finite_of_stage_one_and_residual (hStage : ZeroNonisolatedFull F)
    (hres : NoProperFullDiffSet F) {Y M : Set G} (hY : IsClosed Y) (hproper : Y ≠ univ)
    (hinv : FamilyInvariant F Y) (hMY : M ⊆ Y)
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M) :
    M.Finite := by
  by_contra hnotfin
  have hinf : M.Infinite := Set.not_finite.mp hnotfin
  have hclosedM : IsClosed (M - M) := BerendMinimal.isClosed_sub hM.closed
  have hneM : (M - M).Nonempty := ⟨0, BerendMinimal.zero_mem_sub hM.ne⟩
  have haccM : (0 : G) ∈ closure ((M - M) \ {0}) :=
    BerendMinimal.zero_mem_closure_sdiff hM.closed hinf
  have hinvM : FamilyInvariant F (M - M) := by
    intro i
    exact BerendMinimal.isInvariantFamily_sub (G := F) (M := M) (fun i => hM.inv i) i
  have hfull : M - M = univ := hStage (M - M) hclosedM hneM haccM hinvM
  have hsub : M - M ⊆ Y - Y :=
    fun z ⟨a, ha, b, hb, hz⟩ => ⟨a, hMY ha, b, hMY hb, hz⟩
  have hYfull : Y - Y = univ :=
    Set.eq_univ_iff_forall.mpr fun z => hsub (by rw [hfull]; exact Set.mem_univ z)
  exact hres Y hY (hM.ne.mono hMY) hinv hproper hYfull

/-- The same reduction in the form in which plan §D.2 states it: a closed
invariant `Y` that is *not* the whole group contains a finite minimal closed
invariant subset. -/
theorem exists_finite_minimal_of_stage_one_and_residual [Nonempty ι]
    (hStage : ZeroNonisolatedFull F) (hres : NoProperFullDiffSet F) {Y : Set G}
    (hY : IsClosed Y) (hne : Y.Nonempty) (hinv : FamilyInvariant F Y) (hproper : Y ≠ univ) :
    ∃ M : Set G, M ⊆ Y ∧ BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M ∧
      M.Finite := by
  obtain ⟨M, hMY, hM⟩ :=
    BerendMinimal.exists_minimal_invariant hY hne (F := fun i => (F i : G → G)) hinv
  exact ⟨M, hMY, hM,
    minimal_finite_of_stage_one_and_residual hStage hres hY hproper hinv hMY hM⟩

end Reduce

/-! ## 8. The side condition of Proposition IV.1, and the link to the project's
deep `Prop` -/

section SideCondition

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **A nontrivial full group is never minimal invariant.**  `{0}` is a proper closed
nonempty invariant subset of `univ`, so `univ` is not minimal.

This is the side condition `BEREND_PROOF_PLAN.md` §D notes for Proposition IV.1:
"`{0}` is invariant, so a nontrivial full torus is never minimal.  This supplies the
side condition that the literal arbitrary-map formulation would otherwise need." -/
theorem not_isMinimalInvariant_univ [Nontrivial G] [Nonempty ι] :
    ¬ BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) (univ : Set G) := by
  intro hM
  have hsub : ({0} : Set G) ⊆ (univ : Set G) := subset_univ _
  have hinv : BerendMinimal.IsInvariantFamily (fun i => (F i : G → G)) ({0} : Set G) := by
    intro i z hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mem_singleton_iff] at hy ⊢
    rw [hy]
    show (F i) 0 = 0
    exact map_zero _
  have hEq : ({0} : Set G) = univ :=
    hM.minimal {0} hsub (singleton_nonempty 0) isClosed_singleton hinv
  obtain ⟨a, ha⟩ := exists_ne (0 : G)
  have : a ∈ ({0} : Set G) := hEq ▸ Set.mem_univ a
  exact ha (mem_singleton_iff.mp this)

/-- **The residual statement implies Proposition IV.1** in the form the plan uses: a
*minimal* closed invariant set never has full difference set.  (`M ≠ univ` because in
a nontrivial group with a nonempty family the whole group is not minimal.)

So the residual obligation of amended §D.5 subsumes Proposition IV.1; the converse
fails (`BerendSharpness.minimal_finite_but_infinite`), which is why the residual is
the separate final obligation. -/
theorem not_diffSet_eq_univ_of_minimal [Nontrivial G] [Nonempty ι] [T2Space G]
    (hres : NoProperFullDiffSet F) {M : Set G}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M) :
    M - M ≠ univ := by
  intro hfull
  have hproper : M ≠ univ := by
    intro hEq
    exact not_isMinimalInvariant_univ (F := F) (hEq ▸ hM)
  exact hres M hM.closed hM.ne hM.inv hproper hfull

end SideCondition

end BerendDichotomy

end CubicTwoStage

/-! ## 6. Axiom audit -/

#print axioms CubicTwoStage.BerendDichotomy.dichotomy_iff_noProperFullDiffSet
#print axioms CubicTwoStage.BerendDichotomy.dichotomy_of_noProperFullDiffSet
#print axioms CubicTwoStage.BerendDichotomy.noProperFullDiffSet_of_dichotomy
#print axioms CubicTwoStage.BerendDichotomy.torus_dichotomy_iff_diffSet_eq_univ
#print axioms CubicTwoStage.BerendDichotomy.dichotomy_iff_infinite_eq_univ
#print axioms CubicTwoStage.BerendDichotomy.noProperFullDiffSet_iff_infinite
#print axioms CubicTwoStage.BerendDichotomy.exists_coset_of_diffSet_subset
#print axioms CubicTwoStage.BerendDichotomy.finite_of_finite_diffSet
#print axioms CubicTwoStage.BerendDichotomy.ne_univ_of_diffSet_subset
#print axioms CubicTwoStage.BerendDichotomy.minimal_finite_of_stage_one_and_residual
#print axioms CubicTwoStage.BerendDichotomy.exists_finite_minimal_of_stage_one_and_residual
#print axioms CubicTwoStage.BerendDichotomy.not_isMinimalInvariant_univ
#print axioms CubicTwoStage.BerendDichotomy.not_diffSet_eq_univ_of_minimal

