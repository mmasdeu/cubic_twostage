/-
# Quotient coverings and torus-to-ambient path lifting

A discrete additive subgroup of a topological real vector space gives a genuine
covering quotient, not merely an open quotient.  Consequently a continuous
segment in a torus can be lifted through the open quotient once its starting
point is lifted.  This module isolates that topological input for the planar
arc/net assembly.
-/
import CubicTwoStage.Lattice
import Mathlib.Topology.Homotopy.Lifting

open Set Filter Topology

namespace CubicTwoStage
namespace BerendQuotientLift

variable {V : Type*} [NormedAddCommGroup V]

/-- `QuotientAddGroup.mk' L` is a covering map when `L` is discrete. -/
theorem isQuotientCoveringMap_mk' (L : AddSubgroup V) [DiscreteTopology L] :
    IsAddQuotientCoveringMap
    (⇑(QuotientAddGroup.mk' L : V →+ V ⧸ L) : V → V ⧸ L) L := by
  exact AddSubgroup.isAddQuotientCoveringMap_of_comm L DiscreteTopology.isDiscrete

/-- The same quotient as an ordinary covering map. -/
theorem isCoveringMap_mk' (L : AddSubgroup V) [DiscreteTopology L] :
    IsCoveringMap (⇑(QuotientAddGroup.mk' L : V →+ V ⧸ L) : V → V ⧸ L) :=
  (isQuotientCoveringMap_mk' L).isCoveringMap

/-- Any continuous interval path through the torus lifts once an ambient
representative of its starting point is chosen. -/
theorem exists_path_lift (L : AddSubgroup V) [DiscreteTopology L]
    (γ : C(unitInterval, V ⧸ L)) {x : V}
    (hx : (QuotientAddGroup.mk' L) x = γ 0) :
    ∃ Γ : C(unitInterval, V),
      (QuotientAddGroup.mk' L) ∘ Γ = γ ∧ Γ 0 = x := by
  exact (isCoveringMap_mk' L).exists_path_lifts γ x hx.symm

section Straight

variable [NormedSpace ℝ V]

/-- The torus path parametrizing a segment of length parameter `T`,
reparametrized on `unitInterval`. -/
noncomputable def torusStraightPath (L : AddSubgroup V) (b : V ⧸ L) (e : V)
    (T : ℝ) : C(unitInterval, V ⧸ L) where
  toFun t := b + (QuotientAddGroup.mk' L) ((T * (t : ℝ)) • e)
  continuous_toFun :=
    continuous_const.add (QuotientAddGroup.continuous_mk.comp
      ((continuous_const.mul continuous_subtype_val).smul continuous_const))

/-- The corresponding straight path in the ambient space. -/
noncomputable def straightPath (x e : V) (T : ℝ) : C(unitInterval, V) where
  toFun t := x + (T * (t : ℝ)) • e
  continuous_toFun := by fun_prop

@[simp] theorem torusStraightPath_zero (L : AddSubgroup V) (b : V ⧸ L) (e : V)
    (T : ℝ) : torusStraightPath L b e T 0 = b := by
  simp [torusStraightPath]

@[simp] theorem straightPath_zero (x e : V) (T : ℝ) : straightPath x e T 0 = x := by
  simp [straightPath]

/-- The straight ambient path really is a lift of the torus path. -/
theorem comp_straightPath (L : AddSubgroup V) (b : V ⧸ L) (x e : V) (T : ℝ)
    (hx : (QuotientAddGroup.mk' L) x = b) :
    (QuotientAddGroup.mk' L) ∘ straightPath x e T = torusStraightPath L b e T := by
  funext t
  change (QuotientAddGroup.mk' L) (x + (T * (t : ℝ)) • e) =
    b + (QuotientAddGroup.mk' L) ((T * (t : ℝ)) • e)
  rw [map_add, hx]

/-- A straight torus segment lifts to the straight ambient segment with the
chosen initial representative.  Since the path is affine, the lift is explicit;
covering-path lifting and lattice discreteness are not needed for this special
case. -/
theorem mem_preimage_straightPath (L : AddSubgroup V)
    {Y : Set (V ⧸ L)} {b : V ⧸ L} {x e : V} (T : ℝ)
    (hx : (QuotientAddGroup.mk' L) x = b)
    (h : ∀ t : unitInterval, torusStraightPath L b e T t ∈ Y) :
    ∀ t : unitInterval, straightPath x e T t ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  intro t
  change (QuotientAddGroup.mk' L) (straightPath x e T t) ∈ Y
  have ht := congrFun (comp_straightPath L b x e T hx) t
  change (QuotientAddGroup.mk' L) (straightPath x e T t) = torusStraightPath L b e T t at ht
  rw [ht]
  exact h t

/-- A torus ray in a set lifts to the corresponding straight ray in its full
preimage, starting at any representative of the torus basepoint. -/
theorem mem_preimage_straight_ray (L : AddSubgroup V)
    {Y : Set (V ⧸ L)} {b : V ⧸ L} {x e : V}
    (hx : (QuotientAddGroup.mk' L) x = b)
    (h : ∀ s : ℝ, 0 ≤ s → b + (QuotientAddGroup.mk' L) (s • e) ∈ Y) :
    ∀ s : ℝ, 0 ≤ s → x + s • e ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  intro s hs
  rcases hs.eq_or_lt with rfl | hs
  · simp only [zero_smul, add_zero]
    change (QuotientAddGroup.mk' L) x ∈ Y
    rw [hx]
    simpa using h 0 le_rfl
  · have hpath : ∀ t : unitInterval, torusStraightPath L b e s t ∈ Y := by
      intro t
      exact h (s * (t : ℝ)) (mul_nonneg hs.le t.2.1)
    have hlift := mem_preimage_straightPath (Y := Y) L s hx hpath
      (⟨1, unitInterval.one_mem⟩ : unitInterval)
    simpa [straightPath] using hlift

end Straight

end BerendQuotientLift
end CubicTwoStage

#print axioms CubicTwoStage.BerendQuotientLift.isQuotientCoveringMap_mk'
#print axioms CubicTwoStage.BerendQuotientLift.isCoveringMap_mk'
#print axioms CubicTwoStage.BerendQuotientLift.exists_path_lift
#print axioms CubicTwoStage.BerendQuotientLift.comp_straightPath
#print axioms CubicTwoStage.BerendQuotientLift.mem_preimage_straightPath
#print axioms CubicTwoStage.BerendQuotientLift.mem_preimage_straight_ray
