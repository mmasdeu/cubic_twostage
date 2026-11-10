import CubicTwoStage.BerendCanonicalSubsequence
import CubicTwoStage.BerendCanonicalB1
import CubicTwoStage.BerendMinimalTorus

noncomputable section

open Set Filter Topology Module

namespace CubicTwoStage
namespace BerendProp43Canonical
namespace CanonicalProp43

/-- **Proposition 4.3 for the canonical complex-cubic unit-prime model.**
The selected endomorphism is one of the B1 witnesses `(1,1)` or `(ε,1)`. -/
theorem exists_canonical_unitPrime_net
    {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    {p : ℕ} (hp : p.Prime) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1) :
    ∃ i : (numberFieldO K)ˣ × ℕ,
      ∀ H : AddSubgroup (Torus (NumberFieldCubic.canonicalFieldModel K hK).lattice),
        Infinite H → IsClosed (H : Set (Torus (NumberFieldCubic.canonicalFieldModel K hK).lattice)) →
        ∀ δ : ℝ, 0 < δ → ∃ n : ℕ,
          ∀ x : Torus (NumberFieldCubic.canonicalFieldModel K hK).lattice,
            ∃ h' ∈ H, dist x
              ((((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).torusAct
                i)^[n] h') < δ := by
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K hK).lattice) :=
    NumberFieldCubic.discreteTopology_canonicalFieldModel_lattice K hK
  letI : IsZLattice ℝ (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K hK).lattice) :=
    NumberFieldCubic.isZLattice_canonicalFieldModel_lattice K hK
  letI : IsClosed ((NumberFieldCubic.canonicalFieldModel K hK).lattice : Set Pt) :=
    isClosed_lattice
  obtain ⟨i, B1⟩ := BerendCanonicalB1.exists_canonical_B1_intLact
    hK ε π hπO hπ0 hp hπN hεpow
  refine ⟨i, ?_⟩
  intro H hHinf hHclosed δ hδ
  exact exists_net_of_infinite_closed
    ((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0)
    i B1 H hHinf hHclosed hδ

end CanonicalProp43
end BerendProp43Canonical
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.exists_canonical_unitPrime_net
