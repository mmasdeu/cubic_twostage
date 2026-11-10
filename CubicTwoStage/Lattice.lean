/-
# Compact quotient tori from ℤ-lattices

Mathlib's `IsZLattice.isCompact_range_of_periodic` proves that the range of a
periodic continuous map on a finite-dimensional real vector space is compact.
Applying it to the quotient map `V → V ⧸ L` gives compactness of every torus
`V ⧸ L` for a full ℤ-lattice `L`.

This isolates the *only* remaining hypothesis behind compactness in the proof of
Theorem 3.6: of the actual lattice `L = σ(𝒪)`, one needs that it is a full
ℤ-lattice (`IsZLattice ℝ`), i.e. that it is discrete and spans `ℝ × ℂ`.
-/
import CubicTwoStage.Basic

open scoped Pointwise

namespace CubicTwoStage

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Compactness of the torus `V ⧸ L`.**  Periodic maps are compactly ranged. -/
theorem compact_quotient_of_isZLattice (L : AddSubgroup V)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] :
    CompactSpace (V ⧸ L) := by
  have hper : ∀ (z w : V), w ∈ AddSubgroup.toIntSubmodule L →
      (QuotientAddGroup.mk' L) (z + w) = (QuotientAddGroup.mk' L) z := by
    intro z w hw
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [show z + w - z = w by abel]
    exact hw
  have h : IsCompact (Set.range (QuotientAddGroup.mk' L)) :=
    IsZLattice.isCompact_range_of_periodic (AddSubgroup.toIntSubmodule L)
      (QuotientAddGroup.mk' L) QuotientAddGroup.continuous_mk hper
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective L)] at h
  exact ⟨h⟩

end CubicTwoStage
