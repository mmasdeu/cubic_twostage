/-
# From the tangent-net limit to an ambient straight ray

`BerendTangentNet.exists_ray_subset` produces a whole affine ray in the torus,
with nonzero tangent in `cplxPlane`.  Its ambient lift is explicit: choose a
representative of the basepoint and use the same affine parametrization.  The
general discrete-lattice covering and path-lifting results are in
`BerendQuotientLift`; discreteness is not needed for this affine specialization.

The basepoint produced by compactness is not asserted to lie in `cplxPlane`.
Consequently this module does not claim the planar-base and endpoint-gap inputs
of `BerendTangentNet.torus_eq_univ_of_segment_data`.  The independent orbit-net
`BerendPlaneNet` and the B3 phase-vector dictionary are not used.
-/
import CubicTwoStage.BerendTangentNet
import CubicTwoStage.BerendQuotientLift

open Set Filter Topology

namespace CubicTwoStage
namespace BerendSegmentLift

open BerendBlockLastMile BerendTangentNet

/-- Lift the tangent-net limit ray to a straight ray in the full preimage of
`Y`.  The direction is planar and nonzero; no planarity claim is made for the
basepoint `x`. -/
theorem exists_lifted_ray_subset {L : AddSubgroup Pt} [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (x e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s : ℝ, 0 ≤ s → x + s • e ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  obtain ⟨b, e, heplane, he, hray⟩ :=
    exists_ray_subset hY hρ hw₀ hc0 hc1 ht' hinv harc
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective L b
  exact ⟨x, e, heplane, he, BerendQuotientLift.mem_preimage_straight_ray L hx hray⟩

/-- The unit-prime form of `exists_lifted_ray_subset`. -/
theorem exists_lifted_ray_subset_torusAct {K : Type*} [Field K]
    {L : AddSubgroup Pt} {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪)
    (u : 𝒪ˣ) (j : ℕ) (hC : 16 ≤ normC (D.mult u j)) [CompactSpace (Torus L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {w₀ c : ℂ} {t' : ℝ} (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      (QuotientAddGroup.mk' L) (arcThrough w₀ c t) ∈ Y) :
    ∃ (x e : Pt), e ∈ cplxPlane ∧ e ≠ 0 ∧
      ∀ s : ℝ, 0 ≤ s → x + s • e ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  obtain ⟨b, e, heplane, he, hray⟩ :=
    exists_ray_subset_torusAct D u j hC hY hinv hw₀ hc0 hc1 ht' harc
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective L b
  exact ⟨x, e, heplane, he, BerendQuotientLift.mem_preimage_straight_ray L hx hray⟩

/-- If an ambient straight ray has a planar basepoint as well as a planar
direction, it is a complex affine ray.  This is a conversion lemma, not a proof
that the compactness-selected basepoint is planar. -/
theorem exists_complex_ray_of_lifted_ray {L : AddSubgroup Pt} {Y : Set (Torus L)}
    {x e : Pt} (hx : x ∈ cplxPlane) (he : e ∈ cplxPlane)
    (hray : ∀ s : ℝ, 0 ≤ s → x + s • e ∈ (QuotientAddGroup.mk' L) ⁻¹' Y) :
    ∀ s : ℝ, 0 ≤ s →
      ofCplx (cplxOf x + (s : ℂ) * cplxOf e) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  intro s hs
  have hid : ofCplx (cplxOf x + (s : ℂ) * cplxOf e) = x + s • e := by
    rw [ofCplx_add, ofCplx_real_smul, eq_ofCplx_cplxOf hx, eq_ofCplx_cplxOf he]
  rw [hid]
  exact hray s hs

end BerendSegmentLift
end CubicTwoStage

#print axioms CubicTwoStage.BerendSegmentLift.exists_lifted_ray_subset
#print axioms CubicTwoStage.BerendSegmentLift.exists_lifted_ray_subset_torusAct
#print axioms CubicTwoStage.BerendSegmentLift.exists_complex_ray_of_lifted_ray
