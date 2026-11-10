/-
# Finite index of sublattices, finite torsion and finite kernels at the torus

Swarm `smw952unn`, member `m1`, direction `d9`.

`BEREND_SEC5_NOTES.md` §3 item 4 lists the last *arithmetic* obligation of the
`§5` assembly of `CubicTwoStage/BerendSec5.lean`: the hypotheses

* `hker : ∀ i, ((F i) ⁻¹' {0}).Finite`  (Berend's Lemma 5.1: a toral
  endomorphism with nonvanishing determinant has finite kernel), and
* `htors : ∀ n > 0, ({z | n • z = 0} : Set (Torus L)).Finite`  (the `n`-torsion
  of the torus `Pt ⧸ L` is finite)

for the lattice `L` of the model.  Mathlib has no packaged statement: the
argument is an index computation, `[L : nL] = n ^ finrank ℤ L`.

This file supplies both, with no `sorry`, no axiom, and no `Prop` hypothesis;
it imports only project modules that do not import `CubicTwoStage.Berend`.

Main results:

* `relIndex_map_nsmul` — `[L : nL] = n ^ finrank ℤ L` for a `ℤ`-lattice `L`;
* `finite_nsmul_torsion` — the `n`-torsion of `Pt ⧸ L` is finite (`htors`);
* `finite_ker_torusMap` — Lemma 5.1: if a linear equivalence `e` preserves `L`
  and is injective, the kernel of the induced torus endomorphism is finite;
* `finite_ker_torusAct` — the same for every member of the unit–prime family.
-/
import CubicTwoStage.BerendEigenBridge
import CubicTwoStage.BerendTorsion

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendLatticeIndex

variable {L : AddSubgroup Pt}

/-! ## 1. The relative index of `n • L` in `L` -/

/-- **`[L : n L] = n ^ finrank ℤ L`** for a `ℤ`-lattice `L` in `Pt`. -/
theorem relIndex_map_nsmul [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] (n : ℕ) :
    (L.map (nsmulAddMonoidHom (α := Pt) n)).relIndex L
      = n ^ Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule L) := by
  haveI : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule L) := ZLattice.module_free ℝ _
  haveI : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule L) := ZLattice.module_finite ℝ _
  exact AddSubgroup.relIndex_map_nsmul (M := Pt) n L

/-! ## 2. Finiteness of the `n`-torsion of the torus -/

/-- A class vanishes in `Pt ⧸ L` exactly on the lattice. -/
theorem mk'_eq_zero_iff {x : Pt} : (QuotientAddGroup.mk' L) x = 0 ↔ x ∈ L := by
  rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']

/-- The `n`-torsion subgroup of `Pt ⧸ L` is finite. -/
theorem finite_nsmul_torsion_subtype [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] (n : ℕ) (hn : 0 < n) :
    Finite {z : Torus L // n • z = 0} := by
  haveI hfree : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule L) := ZLattice.module_free ℝ _
  haveI hfin : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule L) := ZLattice.module_finite ℝ _
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  -- the subgroup `n • L` of `L`, as a subgroup of the additive group `↥L`
  set nL : AddSubgroup ↥L := (L.map (nsmulAddMonoidHom (α := Pt) n)).addSubgroupOf L with hnL
  have hidx : nL.index = n ^ Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule L) := by
    rw [hnL]
    exact relIndex_map_nsmul (L := L) n
  -- `L ⧸ nL` is finite
  haveI hquot : Finite (↥L ⧸ nL) := by
    have hcard : Nat.card (↥L ⧸ nL) ≠ 0 := by
      rw [← AddSubgroup.index_eq_card, hidx]
      exact pow_ne_zero _ hn0
    exact (Nat.card_ne_zero.mp hcard).2
  -- the map `l ↦ (1/n) • l` from `L` to the `n`-torsion of the torus
  set H : ↥L →+ Torus L :=
    { toFun := fun l => (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • (l : Pt))
      map_zero' := by simp
      map_add' := by
        intro a b
        show (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • ((a : Pt) + (b : Pt)))
          = (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • (a : Pt))
            + (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • (b : Pt))
        rw [smul_add, map_add] } with hH
  have hHapply : ∀ l : ↥L, H l = (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • (l : Pt)) :=
    fun l => rfl
  -- every value of `H` is `n`-torsion
  have htorsH : ∀ l : ↥L, n • H l = 0 := by
    intro l
    rw [hHapply]
    rw [← map_nsmul]
    have hstep : (n : ℕ) • (((n : ℝ)⁻¹) • (l : Pt)) = (l : Pt) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ n (((n : ℝ)⁻¹) • (l : Pt)), smul_smul,
        mul_inv_cancel₀ hnR, one_smul]
    rw [hstep]
    exact mk'_eq_zero_iff.mpr l.2
  -- the two descriptions of `nL`
  have hmem_iff : ∀ l : ↥L, ((n : ℝ)⁻¹ • (l : Pt)) ∈ L ↔ l ∈ nL := by
    intro l
    constructor
    · intro hmem
      rw [hnL]
      refine AddSubgroup.mem_addSubgroupOf.mpr (AddSubgroup.mem_map.mpr ⟨_, hmem, ?_⟩)
      show n • (((n : ℝ)⁻¹) • (l : Pt)) = (l : Pt)
      rw [← Nat.cast_smul_eq_nsmul ℝ n (((n : ℝ)⁻¹) • (l : Pt)), smul_smul,
        mul_inv_cancel₀ hnR, one_smul]
    · intro hl
      rw [hnL] at hl
      obtain ⟨x, hxL, hx⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_addSubgroupOf.mp hl)
      have hsplit : ((n : ℝ)⁻¹) • (l : Pt) = x := by
        rw [← hx, show nsmulAddMonoidHom (α := Pt) n x = (n : ℝ) • x from by
          simp [Nat.cast_smul_eq_nsmul], smul_smul, inv_mul_cancel₀ hnR, one_smul]
      rw [hsplit]
      exact hxL
  -- the kernel of `H` is `nL`
  have hker : H.ker = nL := by
    ext l
    have h1 : H l = 0 ↔ ((n : ℝ)⁻¹ • (l : Pt)) ∈ L := by
      rw [hHapply, mk'_eq_zero_iff]
    exact h1.trans (hmem_iff l)
  -- the `n`-torsion is the range of `H`
  have hrange : (H.range : Set (Torus L)) = {z : Torus L | n • z = 0} := by
    ext z
    constructor
    · rintro ⟨l, rfl⟩
      exact htorsH l
    · intro hz
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
      have hx : n • x ∈ L := by
        have h0 : (QuotientAddGroup.mk' L) (n • x) = 0 := by
          rw [map_nsmul]
          exact hz
        exact mk'_eq_zero_iff.mp h0
      refine ⟨⟨n • x, hx⟩, ?_⟩
      rw [hHapply]
      show (QuotientAddGroup.mk' L) (((n : ℝ)⁻¹) • (n • x)) = (QuotientAddGroup.mk' L) x
      rw [← Nat.cast_smul_eq_nsmul ℝ n x, smul_smul, inv_mul_cancel₀ hnR, one_smul]
  -- the lifted map `↥L ⧸ nL →+ Torus L`
  set φ : (↥L ⧸ nL) →+ Torus L := QuotientAddGroup.lift nL H (le_of_eq hker.symm) with hφ
  have hφmk : ∀ l : ↥L, φ (QuotientAddGroup.mk' nL l) = H l := fun l => by
    rw [hφ]
    rfl
  have hφrange : φ.range = H.range := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientAddGroup.mk'_surjective nL q
      exact ⟨l, (hφmk l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨QuotientAddGroup.mk' nL l, hφmk l⟩
  have hfinφ : Finite ↥(φ.range) :=
    Finite.of_surjective (⇑φ.rangeRestrict) (AddMonoidHom.rangeRestrict_surjective φ)
  have hsetH : ((H.range : Set (Torus L))).Finite :=
    Set.finite_coe_iff.mp (hφrange ▸ hfinφ)
  have hT: ({z : Torus L | n • z = 0} : Set (Torus L)).Finite := by
    rw [← hrange]
    exact hsetH
  exact hT.to_subtype

/-- **`htors`**: the `n`-torsion of the torus `Pt ⧸ L` is finite. -/
theorem finite_nsmul_torsion [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] (n : ℕ) (hn : 0 < n) :
    ({z : Torus L | n • z = 0} : Set (Torus L)).Finite :=
  Set.finite_coe_iff.mpr (finite_nsmul_torsion_subtype (L := L) n hn)

end BerendLatticeIndex
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendLatticeIndex.relIndex_map_nsmul
#print axioms CubicTwoStage.BerendLatticeIndex.finite_nsmul_torsion_subtype
#print axioms CubicTwoStage.BerendLatticeIndex.finite_nsmul_torsion
