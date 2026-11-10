import CubicTwoStage.BerendTransitive
import CubicTwoStage.BerendPropIV1
import CubicTwoStage.BerendStageIClosure

open Set Filter Topology
open scoped Pointwise TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendFibre

section General

variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V]

/-- **A discrete subgroup `M ⊇ L` has finite image in the torus `V ⧸ L`, provided
every coset of `L` has a representative of norm at most `Dc`.**

Every class of `M/L` is represented by `m - l` with `m ∈ M`, `l ∈ L` and
`‖m - l‖ ≤ Dc`; those representatives lie in the bounded closed ball, where `M`
has only finitely many points because it is discrete and closed. -/
theorem finite_mk_image_of_discrete (L M : AddSubgroup V) (hLM : L ≤ M)
    (hM : ∃ ε > 0, ∀ m ∈ M, ‖m‖ < ε → m = 0)
    (Dc : ℝ) (hDc : ∀ x : V, ∃ l ∈ L, ‖x - l‖ ≤ Dc) :
    (QuotientAddGroup.mk' L '' (M : Set V)).Finite := by
  obtain ⟨ε, hε, hMε⟩ := hM
  have hMdisc : IsDiscrete (M : Set V) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro m hm
    refine ⟨Metric.ball m ε, Metric.isOpen_ball, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hxM⟩
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have hsub : x - m ∈ M := M.sub_mem hxM hm
      have hzero : x - m = 0 := hMε _ hsub hx
      exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hzero)
    · rintro rfl
      exact ⟨Metric.mem_ball_self hε, hm⟩
  haveI : DiscreteTopology ↥M := isDiscrete_iff_discreteTopology.mp hMdisc
  have hMclosed : IsClosed (M : Set V) := AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall (0 : V) Dc ∩ (M : Set V)).Finite :=
    Metric.finite_isBounded_inter_isClosed hMdisc Metric.isBounded_closedBall hMclosed
  refine Set.Finite.subset (hfin.image (QuotientAddGroup.mk' L)) ?_
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨l, hl, hld⟩ := hDc m
  have hmem : m - l ∈ M := M.sub_mem hm (hLM hl)
  refine ⟨m - l, ⟨?_, hmem⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hld
  · have h0 : (QuotientAddGroup.mk' L) l = 0 :=
      (QuotientAddGroup.eq_zero_iff l).mpr hl
    rw [map_sub, h0, sub_zero]

/-- A continuous injective additive map preserving a discrete lattice has finite
kernel on the compact quotient.  The kernel is the image of the discrete group
`L.comap f`. -/
theorem finite_preimage_zero_of_continuous_injective
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [CompactSpace (V ⧸ L)] (f : V →+ V) (hf : Continuous f)
    (hinj : Function.Injective f) (hL : L ≤ L.comap f) :
    ((QuotientAddGroup.map L L f hL) ⁻¹' {0}).Finite := by
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  obtain ⟨δ, hδ, hLδ⟩ : ∃ δ > 0, ∀ l ∈ L, ‖l‖ < δ → l = 0 := by
    have hLd : IsDiscrete (L : Set V) := DiscreteTopology.isDiscrete
    rw [isDiscrete_iff_forall_mem_exists_isOpen] at hLd
    obtain ⟨U, hU, hU0⟩ := hLd 0 L.zero_mem
    have hmem : (0 : V) ∈ U ∩ (L : Set V) := by rw [hU0]; exact Set.mem_singleton 0
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU 0 hmem.1
    refine ⟨δ, hδ, fun l hl hsmall => ?_⟩
    have hlU : l ∈ U := hδU (by simpa [Metric.mem_ball, dist_zero_right] using hsmall)
    have hl0 : l ∈ ({0} : Set V) := by rw [← hU0]; exact ⟨hlU, hl⟩
    exact hl0
  have hcont0 := (hf.continuousAt (x := (0 : V))).tendsto
  rw [map_zero] at hcont0
  obtain ⟨ε, hε, hεf⟩ := (Metric.tendsto_nhds_nhds).1 hcont0 δ hδ
  have hM : ∃ ε > 0, ∀ m ∈ L.comap f, ‖m‖ < ε → m = 0 := by
    refine ⟨ε, hε, fun m hm hsmall => ?_⟩
    have hfm : f m ∈ L := hm
    have hsmall' : dist (f m) 0 < δ := hεf (by simpa [dist_eq_norm] using hsmall)
    have hzero : f m = 0 := hLδ _ hfm (by simpa [dist_eq_norm] using hsmall')
    exact hinj (hzero.trans (map_zero f).symm)
  obtain ⟨R, hR, hcov⟩ := BerendInteriorFull.exists_cover_radius (L := L)
  have hDc : ∀ x : V, ∃ l ∈ L, ‖x - l‖ ≤ R := by
    intro x
    have hx : (QuotientAddGroup.mk' L) x ∈
        (QuotientAddGroup.mk' L) '' Metric.ball (0 : V) R := by
      rw [hcov]
      exact Set.mem_univ _
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨x - y, ?_, ?_⟩
    · apply (QuotientAddGroup.eq_zero_iff (x - y)).mp
      change (QuotientAddGroup.mk' L) x - (QuotientAddGroup.mk' L) y = 0
      rw [hyx, sub_self]
    · rw [Metric.mem_ball, dist_zero_right] at hy
      rw [show x - (x - y) = y by abel]
      exact hy.le
  have hfin := finite_mk_image_of_discrete L (L.comap f) hL hM R hDc
  have heq : (QuotientAddGroup.mk' L) '' ((L.comap f : AddSubgroup V) : Set V) =
      (QuotientAddGroup.map L L f hL) ⁻¹' {0} := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    constructor
    · rintro ⟨m, hm, hmx⟩
      have hfm : f m ∈ L := hm
      rw [← hmx]
      change (QuotientAddGroup.mk' L) (f m) ∈ ({0} : Set (V ⧸ L))
      exact (QuotientAddGroup.eq_zero_iff (f m)).mpr hfm
    · intro hx
      refine ⟨x, ?_, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff (f x)).mp hx
  rwa [← heq]

end General

section UnitPrimeModel

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- Every unit–prime torus endomorphism has finite kernel. -/
theorem finite_ker_torusAct [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    ((D.torusAct i) ⁻¹' {0}).Finite := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  let f : Pt →+ Pt := ((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom
  have hL : L ≤ L.comap f := fun _ h => D.linFam_preserves i _ h
  have h := finite_preimage_zero_of_continuous_injective f
    (LinearMap.continuous_of_finiteDimensional (D.linFam i : Pt →ₗ[ℝ] Pt))
    (D.linFam i).injective hL
  simpa [f, UnitPrimeModel.torusAct, torusMap] using h

end UnitPrimeModel

end BerendFibre
end CubicTwoStage

#print axioms CubicTwoStage.BerendFibre.finite_mk_image_of_discrete
#print axioms CubicTwoStage.BerendFibre.finite_preimage_zero_of_continuous_injective
#print axioms CubicTwoStage.BerendFibre.finite_ker_torusAct
