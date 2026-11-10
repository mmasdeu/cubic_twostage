/-
# Package B on the project's torus `Torus L = Pt ⧸ L`

This file instantiates the abstract results of `BerendMinimal.lean` on the torus
of the project (`Pt = Fin 3 → ℝ`, `L = σ(𝒪_K) ⊂ Pt`).  It supplies the two
topological facts the abstract theory asks for:

* `Torus L` is **compact** (already in `CubicTwoStage.Lattice`;
  `compact_quotient_of_isZLattice`);
* `Torus L` is **Hausdorff** (`instT2Space_torus`), because the lattice `L` is
  closed.  Closedness of `L` is a consequence of discreteness
  (`isClosed_lattice`), which is one half of the `IsZLattice` hypothesis.

With those, stage B of `BEREND_PROOF_PLAN.md` is available for every commuting
family of toral endomorphisms, in the exact form the later stages consume:

* `exists_minimal_invariant_torus`: a nonempty closed forward-invariant subset of
  the torus contains a minimal closed forward-invariant one;
* `IsMinimalInvariant.diff_data_torus`: for an infinite minimal `M`, the
  difference set `M - M` is closed, forward-invariant, and `0` is a non-isolated
  point of it — the hypothesis of stage C (`eq_univ_of_zero_nonisolated`);
* `IsMinimalInvariant.exists_word_fixed_torus`: a finite minimal `M` consists of
  points periodic under a nonempty word of the family — the torsion input of
  stage D.4.

Nothing here imports `CubicTwoStage.Berend`, so the old axiom is untouched.
-/
import CubicTwoStage.Lattice
import CubicTwoStage.BerendMinimal

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CubicTwoStage

open Set

open scoped Pointwise

noncomputable section

/-! ## The torus is Hausdorff -/

section Topology

variable {L : AddSubgroup Pt}

/-- The lattice is closed in `Pt`: it is discrete, and `Pt` is Hausdorff. -/
theorem isClosed_lattice [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    IsClosed (L : Set Pt) := by
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  exact AddSubgroup.isClosed_of_discrete

instance instT1Space_torus [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    T1Space (Pt ⧸ L) := by
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  haveI : IsClosed (L : Set Pt) := isClosed_lattice
  infer_instance

/-- **The project's torus is Hausdorff.** -/
instance instT2Space_torus [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    T2Space (Pt ⧸ L) := by
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  haveI : IsClosed (L : Set Pt) := isClosed_lattice
  haveI : T1Space (Pt ⧸ L) := inferInstance
  infer_instance

end Topology

/-! ## Stage B on the torus -/

section Torus

variable {L : AddSubgroup Pt} [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- **Existence of minimal closed invariant subsets of the torus.**  Any nonempty
closed set `Y ⊆ Torus L` carried into itself by every map of a family of
continuous toral endomorphisms contains a minimal one. -/
theorem exists_minimal_invariant_torus {ι : Type*} {G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)}
    {Y : Set (Pt ⧸ L)} (hY : IsClosed Y) (hne : Y.Nonempty) (hinv : ∀ i, (G i) '' Y ⊆ Y) :
    ∃ M : Set (Pt ⧸ L), M ⊆ Y ∧
      BerendMinimal.IsMinimalInvariant (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L))) M := by
  haveI : CompactSpace (Pt ⧸ L) := compact_quotient_of_isZLattice L
  exact BerendMinimal.exists_minimal_invariant hY hne hinv

/-- **Stage D input on the torus.**  For an infinite minimal closed invariant set
`M` of the torus, the difference set `M - M` is closed and forward invariant,
and `0` is a non-isolated point of it. -/
theorem IsMinimalInvariant.diff_data_torus {ι : Type*} {G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)}
    {M : Set (Pt ⧸ L)}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L))) M)
    (hinf : M.Infinite) :
    IsClosed (M - M) ∧
      BerendMinimal.IsInvariantFamily (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L))) (M - M) ∧
      (0 : Pt ⧸ L) ∈ M - M ∧ (0 : Pt ⧸ L) ∈ closure ((M - M) \ {0}) := by
  haveI : CompactSpace (Pt ⧸ L) := compact_quotient_of_isZLattice L
  exact ⟨BerendMinimal.isClosed_sub hM.closed,
    BerendMinimal.isInvariantFamily_sub hM.inv,
    BerendMinimal.zero_mem_sub hM.ne,
    BerendMinimal.zero_mem_closure_sdiff hM.closed hinf⟩

/-- **Torsion input on the torus.**  Every point of a finite minimal closed
invariant set of the torus is periodic under a nonempty word of the family. -/
theorem IsMinimalInvariant.exists_word_fixed_torus {ι : Type*}
    [Nonempty ι] {G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)} {M : Set (Pt ⧸ L)}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L))) M)
    (hfin : M.Finite) {x : Pt ⧸ L} (hx : x ∈ M) :
    ∃ l : List ι, l ≠ [] ∧ BerendMinimal.wordApply (fun i => (G i : Pt ⧸ L → Pt ⧸ L)) l x = x :=
  BerendMinimal.IsMinimalInvariant.exists_word_fixed hM hfin hx

/-- In a minimal set of the torus, the semigroup orbit of every point is
dense. -/
theorem IsMinimalInvariant.closure_semigroupOrbit_torus {ι : Type*}
    {G : ι → (Pt ⧸ L) →+ (Pt ⧸ L)} (hcont : ∀ i, Continuous (G i)) {M : Set (Pt ⧸ L)}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (G i : (Pt ⧸ L) → (Pt ⧸ L))) M)
    {x : Pt ⧸ L} (hx : x ∈ M) :
    closure (BerendMinimal.semigroupOrbit (fun i => (G i : Pt ⧸ L → Pt ⧸ L)) x) = M :=
  BerendMinimal.IsMinimalInvariant.closure_semigroupOrbit
    (fun i => hcont i) hM hx

end Torus

end

end CubicTwoStage
