/-
d10: the torsion structure of the project's torus `Pt ⧸ L`, `L` a ℤ-lattice.

This is the arithmetic side of plan items A.4 and D.4 that does not depend on the
eigenvalue theory: *which* points of the torus can be torsion, how many there are,
and what that says about their difference sets.

Nothing here imports `CubicTwoStage.Berend`, so the old axiom cannot leak in.

Main results (all axiom free):

* `countable_lattice`: a ℤ-lattice in `Pt = Fin 3 → ℝ` is countable
  (`ZLattice.module_finite` + `Finsupp.Countable.of_moduleFinite`).
* `countable_torsionSet`: the torsion points of `Pt ⧸ L` form a countable set.
  The `m`-torsion of `Pt ⧸ L` is the image of `(1/m) • L` — division by `m` is
  available because `Pt` is a real vector space — hence countable, and a countable
  union of countable sets is countable.
* `uncountable_torus`: `Pt ⧸ L` is uncountable, because the fibres of the
  quotient map are the cosets `a + L`, which are countable.
* `diffSet_ne_univ_of_subset_torsion`: a set of torsion points never has full
  difference set.  This is a genuine instance of the amended plan's residual
  obligation ("no closed invariant `Y` with `diffSet Y = univ`"), namely the
  instance in which `Y` consists of torsion points — exactly the class that the
  finite/torsion analysis of §5 produces.
-/
import CubicTwoStage.Lattice

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise
open Set Filter Topology

namespace CubicTwoStage.BerendTorsion

variable {L : AddSubgroup Pt}

/-! ## The lattice is countable and the torus is not -/

/-- A ℤ-lattice in `Pt` is countable. -/
theorem countable_lattice [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] : Countable ↥L := by
  haveI : Module.Finite ℤ ↥L :=
    ZLattice.module_finite ℝ (AddSubgroup.toIntSubmodule L)
  exact Finsupp.Countable.of_moduleFinite (M := ↥L) (R := ℤ)

/-- **The torus is uncountable.**  The fibres of the quotient map are the cosets
`a + L`, which are countable, so a countable torus would make `Pt` a countable
union of countable sets. -/
theorem uncountable_torus [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] : Uncountable (Pt ⧸ L) := by
  have hL : Countable ↥L := countable_lattice
  refine not_countable_iff.mp ?_
  intro hq
  have hfib : ∀ q : Pt ⧸ L, {a : Pt | QuotientAddGroup.mk' L a = q}.Countable := by
    intro q
    obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk'_surjective L q
    have hsub : {a : Pt | QuotientAddGroup.mk' L a = q} ⊆
        (fun l : ↥L => a₀ + (l : Pt)) '' (Set.univ : Set ↥L) := by
      intro a ha
      have hmem : a - a₀ ∈ L := by
        rw [← QuotientAddGroup.eq_iff_sub_mem (x := a) (y := a₀)]
        rw [← QuotientAddGroup.mk'_apply (N := L) (x := a),
          ← QuotientAddGroup.mk'_apply (N := L) (x := a₀)]
        exact ha.trans ha₀.symm
      exact ⟨⟨a - a₀, hmem⟩, trivial, by simp⟩
    exact Set.Countable.mono hsub (Set.countable_univ.image _)
  have hcover : (Set.univ : Set Pt) ⊆
      ⋃ q : (Pt ⧸ L), {a : Pt | QuotientAddGroup.mk' L a = q} := by
    intro a _
    exact Set.mem_iUnion.mpr ⟨QuotientAddGroup.mk' L a, rfl⟩
  have hPt : Countable Pt :=
    Set.countable_univ_iff.mp (Set.Countable.mono hcover (Set.countable_iUnion hfib))
  haveI : Uncountable (Fin 3 → ℝ) :=
    Function.Injective.uncountable (f := fun t : ℝ => fun _ : Fin 3 => t)
      (fun a b h => by simpa using congrFun h 0)
  exact (Uncountable.not_countable : ¬ Countable (Fin 3 → ℝ)) hPt

/-! ## The torsion points -/

/-- The set of torsion points of the torus. -/
def torsionSet (L : AddSubgroup Pt) : Set (Pt ⧸ L) := {x | ∃ m : ℕ, 0 < m ∧ m • x = 0}

/-- **The torsion points of the torus are countable.** -/
theorem countable_torsionSet [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] : (torsionSet L).Countable := by
  have hL : Countable ↥L := countable_lattice
  refine Set.Countable.mono ?_ (Set.countable_iUnion fun m : ℕ =>
    Set.Countable.image (Set.countable_univ_iff.mpr hL)
      (fun l : ↥L => QuotientAddGroup.mk' L ((m : ℝ)⁻¹ • (l : Pt))))
  rintro x ⟨m, hm, hx⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective L x
  have hma : m • a ∈ L := by
    have h1 : QuotientAddGroup.mk' L (m • a) = 0 := by
      rw [map_nsmul, hx]
    have hker : m • a ∈ AddMonoidHom.ker (QuotientAddGroup.mk' L : Pt →+ Pt ⧸ L) :=
      AddMonoidHom.mem_ker.mpr h1
    rwa [QuotientAddGroup.ker_mk'] at hker
  refine Set.mem_iUnion.mpr ⟨m, ?_⟩
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hinv : (m : ℝ)⁻¹ • (m • a) = a := by
    rw [← Nat.cast_smul_eq_nsmul ℝ m a, inv_smul_smul₀ hmR]
  refine ⟨⟨m • a, hma⟩, trivial, ?_⟩
  have hgoal : (fun l : ↥L => QuotientAddGroup.mk' L ((m : ℝ)⁻¹ • (l : Pt))) ⟨m • a, hma⟩
      = QuotientAddGroup.mk' L ((m : ℝ)⁻¹ • (m • a)) := rfl
  rw [hgoal, hinv]

/-! ## The torsion points form an invariant subgroup -/

theorem torsionSet_zero : (0 : Pt ⧸ L) ∈ torsionSet L := ⟨1, one_pos, by simp⟩

theorem torsionSet_add {x y : Pt ⧸ L} (hx : x ∈ torsionSet L) (hy : y ∈ torsionSet L) :
    x + y ∈ torsionSet L := by
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨n, hn, hny⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have hx' : (m * n) • x = 0 := by rw [mul_comm m n, mul_smul, hmx, smul_zero]
  have hy' : (m * n) • y = 0 := by rw [mul_smul, hny, smul_zero]
  rw [nsmul_add, hx', hy', add_zero]

theorem torsionSet_sub {x y : Pt ⧸ L} (hx : x ∈ torsionSet L) (hy : y ∈ torsionSet L) :
    x - y ∈ torsionSet L := by
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨n, hn, hny⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have hx' : (m * n) • x = 0 := by rw [mul_comm m n, mul_smul, hmx, smul_zero]
  have hy' : (m * n) • y = 0 := by rw [mul_smul, hny, smul_zero]
  rw [nsmul_sub, hx', hy', sub_zero]

/-- Endomorphisms of the torus send torsion points to torsion points. -/
theorem torsionSet_map (f : (Pt ⧸ L) →+ (Pt ⧸ L)) {x : Pt ⧸ L} (hx : x ∈ torsionSet L) :
    f x ∈ torsionSet L := by
  obtain ⟨m, hm, hmx⟩ := hx
  exact ⟨m, hm, by rw [← map_nsmul, hmx, map_zero]⟩

/-! ## The residual obligation for torsion sets -/

/-- The plan's `diffSet`: the pointwise difference set `Y - Y`.  It is written as
an abbreviation here so that this module stays self-contained (it does not import
the §5 module); the two are definitionally equal. -/
abbrev diffSet (Y : Set (Pt ⧸ L)) : Set (Pt ⧸ L) := Y - Y

/-- A countable subset of the uncountable torus has a countable, hence proper,
difference set. -/
theorem diffSet_ne_univ_of_countable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] {Y : Set (Pt ⧸ L)} (hY : Y.Countable) :
    diffSet Y ≠ Set.univ := by
  haveI : Uncountable (Pt ⧸ L) := uncountable_torus
  intro h
  have huniv : (Set.univ : Set (Pt ⧸ L)).Countable := by
    rw [← h]
    have himg : diffSet Y = (fun p : (Pt ⧸ L) × (Pt ⧸ L) => p.1 - p.2) '' (Y ×ˢ Y) := by
      ext z
      simp only [Set.mem_sub, Set.mem_image, Set.mem_prod, Prod.exists]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
      · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [himg]
    exact Set.Countable.image (hY.prod hY) _
  exact (Uncountable.not_countable : ¬ Countable (Pt ⧸ L)) (Set.countable_univ_iff.mp huniv)

/-- **A set of torsion points never has full difference set.**  This is the
instance of the amended plan's residual obligation ("no closed invariant `Y` with
`diffSet Y = univ`") in which `Y` consists of torsion points — the class produced
by the finite/torsion analysis of §5. -/
theorem diffSet_ne_univ_of_subset_torsion [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] {Y : Set (Pt ⧸ L)}
    (hY : Y ⊆ torsionSet L) : Y - Y ≠ Set.univ :=
  diffSet_ne_univ_of_countable (countable_torsionSet.mono hY)

end CubicTwoStage.BerendTorsion
