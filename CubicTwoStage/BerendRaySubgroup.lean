/-
# Compact ray closures and Berend's Proposition 4.2 subgroup

A ray in a compact torus is an additive subsemigroup, but not necessarily a
subgroup before closure.  Its closure is a subgroup by the standard compact
subsemigroup argument: compactness gives return times `n_j • x → 0`, and the
predecessor sequence converges to `-x`.

`exists_translate_raySubgroup` applies this to the full ray produced by
`BerendTangentNet.exists_ray_subset`.  It yields a closed additive subgroup
whose translate by the limiting basepoint lies in the closed invariant set.
This is the translated-subgroup input of Berend's Proposition 4.2, without an
annulus, a planar-base assumption, or an independent line-density hypothesis.
Infinitude follows from preconnectedness and lattice discreteness.  No B1-density
claim is made here.
-/
import CubicTwoStage.BerendSegmentLift
import CubicTwoStage.BerendMinimalTorus
import CubicTwoStage.BerendCoordDense

open Set Filter Topology

namespace CubicTwoStage
namespace BerendRaySubgroup

section AddClosure

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]

/-- Addition passes to the closure of an additively closed set. -/
theorem add_mem_closure {S : Set T}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x + y ∈ closure S := by
  intro x hx y hy
  have hclosed : IsClosed {z : T | z + y ∈ closure S} :=
    isClosed_closure.preimage (continuous_id.add continuous_const)
  refine closure_minimal ?_ hclosed hx
  intro z hz
  have hclosed' : IsClosed {w : T | z + w ∈ closure S} :=
    isClosed_closure.preimage (continuous_const.add continuous_id)
  apply closure_minimal (s := S) (t := {w : T | z + w ∈ closure S}) ?_ hclosed' hy
  intro w hw
  exact subset_closure (hS z hz w hw)

end AddClosure

section CompactAddSubsemigroup

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [T2Space T] [FirstCountableTopology T]

/-- A compact additive subsemigroup of a Hausdorff topological additive group
is closed under negation. -/
theorem neg_mem_of_isCompact {K : Set T} (hK : IsCompact K) (h0 : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) {x : T} (hx : x ∈ K) : -x ∈ K := by
  have hxn : ∀ n : ℕ, n • x ∈ K := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul]; exact hadd _ ih _ hx
  obtain ⟨a, haK, φ, hφ, hlim⟩ :=
    hK.isSeqCompact (x := fun n : ℕ => n • x) (fun n => hxn n)
  have hshift : Tendsto (fun j : ℕ => (φ (j + 1) : ℕ) • x) atTop (𝓝 a) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_add_atTop_nat 1)
  have hreturn : Tendsto (fun j : ℕ => (φ (j + 1) - φ j) • x) atTop (𝓝 0) := by
    have hsum := hshift.add hlim.neg
    rw [add_neg_cancel] at hsum
    refine hsum.congr' (Eventually.of_forall fun j => ?_)
    change φ (j + 1) • x + -(φ j • x) = (φ (j + 1) - φ j) • x
    rw [sub_nsmul x (hφ.monotone (Nat.le_succ j))]
  have hpositive : ∀ j : ℕ, 1 ≤ φ (j + 1) - φ j := by
    intro j
    have h : φ j < φ (j + 1) := hφ (by omega)
    omega
  have hpredecessor : Tendsto (fun j : ℕ => (φ (j + 1) - φ j - 1) • x + x)
      atTop (𝓝 0) := by
    refine hreturn.congr' (Eventually.of_forall fun j => ?_)
    change (φ (j + 1) - φ j) • x = (φ (j + 1) - φ j - 1) • x + x
    rw [← succ_nsmul, Nat.sub_add_cancel (hpositive j)]
  have hlast : Tendsto (fun j : ℕ => (φ (j + 1) - φ j - 1) • x)
      atTop (𝓝 (-x)) := by
    have h := hpredecessor.add_const (-x)
    rw [zero_add] at h
    refine h.congr' (Eventually.of_forall fun j => ?_)
    change (φ (j + 1) - φ j - 1) • x + x + -x = (φ (j + 1) - φ j - 1) • x
    rw [add_neg_cancel_right]
  exact hK.isClosed.mem_of_tendsto hlast
    (Eventually.of_forall fun j => hxn (φ (j + 1) - φ j - 1))

/-- Package a compact additive subsemigroup containing zero as an additive
subgroup. -/
noncomputable def compactAddSubgroup (K : Set T) (hK : IsCompact K) (h0 : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) : AddSubgroup T where
  carrier := K
  zero_mem' := h0
  add_mem' := fun hx hy => hadd _ hx _ hy
  neg_mem' := fun hx => neg_mem_of_isCompact hK h0 hadd hx

@[simp] theorem coe_compactAddSubgroup {K : Set T} (hK : IsCompact K) (h0 : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) :
    (compactAddSubgroup K hK h0 hadd : Set T) = K := rfl

theorem isClosed_compactAddSubgroup {K : Set T} (hK : IsCompact K) (h0 : 0 ∈ K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) :
    IsClosed (compactAddSubgroup K hK h0 hadd : Set T) := hK.isClosed

end CompactAddSubsemigroup

/-! ## The closure of a torus ray -/

/-- The image in `Torus L` of the nonnegative ray in direction `e`. -/
def torusRay (L : AddSubgroup Pt) (e : Pt) : Set (Torus L) :=
  {y | ∃ s : ℝ, 0 ≤ s ∧ (QuotientAddGroup.mk' L) (s • e) = y}

theorem zero_mem_torusRay (L : AddSubgroup Pt) (e : Pt) : 0 ∈ torusRay L e := by
  refine ⟨0, le_rfl, ?_⟩
  simp

theorem add_mem_torusRay {L : AddSubgroup Pt} {e : Pt} :
    ∀ x ∈ torusRay L e, ∀ y ∈ torusRay L e, x + y ∈ torusRay L e := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  refine ⟨s + t, add_nonneg hs ht, ?_⟩
  rw [add_smul, map_add]

/-- The closed additive subgroup generated by the closure of a torus ray. -/
noncomputable def torusRaySubgroup (L : AddSubgroup Pt) (e : Pt)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    AddSubgroup (Torus L) :=
  compactAddSubgroup (closure (torusRay L e))
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
    (subset_closure (zero_mem_torusRay L e))
    (add_mem_closure add_mem_torusRay)

@[simp] theorem coe_torusRaySubgroup (L : AddSubgroup Pt) (e : Pt)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    (torusRaySubgroup L e : Set (Torus L)) = closure (torusRay L e) := rfl

theorem torusRay_subset (L : AddSubgroup Pt) (e : Pt) [CompactSpace (Torus L)]
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    torusRay L e ⊆ (torusRaySubgroup L e : Set (Torus L)) := subset_closure

theorem isClosed_torusRaySubgroup (L : AddSubgroup Pt) (e : Pt)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    IsClosed (torusRaySubgroup L e : Set (Torus L)) := isClosed_closure

/-- A nonzero direction has arbitrarily small positive multiples outside the
 discrete lattice. -/
theorem exists_torusRay_ne_zero (L : AddSubgroup Pt)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)] {e : Pt} (he : e ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ (QuotientAddGroup.mk' L) (s • e) ≠ 0 := by
  obtain ⟨ε, hε, hiso⟩ := @BerendCoordDense.isolatedZero_of_discreteTopology Pt _ L
    ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  let s : ℝ := ε / (2 * ‖e‖)
  have hs : 0 < s := div_pos hε (by positivity)
  have hnorm : ‖s • e‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hmul : s * ‖e‖ = ε / 2 := by
      dsimp [s]
      field_simp
    rw [hmul]
    linarith
  refine ⟨s, hs, ?_⟩
  intro hq
  have hmem : s • e ∈ L := QuotientAddGroup.eq_zero_iff (s • e) |>.mp hq
  have hzero : s • e = 0 := hiso _ hmem hnorm
  exact (smul_ne_zero (ne_of_gt hs) he) hzero

/-- Ray closure is preconnected. -/
theorem isPreconnected_torusRaySubgroup (L : AddSubgroup Pt) (e : Pt)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    IsPreconnected (torusRaySubgroup L e : Set (Torus L)) := by
  have hcont : Continuous (fun s : ℝ => (QuotientAddGroup.mk' L) (s • e)) :=
    QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const)
  have himage : (fun s : ℝ => (QuotientAddGroup.mk' L) (s • e)) '' Ici 0 = torusRay L e := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hpre := (isPreconnected_Ici (a := (0 : ℝ))).image
    (fun s : ℝ => (QuotientAddGroup.mk' L) (s • e)) hcont.continuousOn
  rw [himage] at hpre
  exact hpre.closure

/-- The closed subgroup generated by a nonzero torus ray is infinite. -/
theorem infinite_torusRaySubgroup (L : AddSubgroup Pt) (e : Pt)
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (he : e ≠ 0) : Infinite (torusRaySubgroup L e) := by
  obtain ⟨s, hs, hq⟩ := exists_torusRay_ne_zero L he
  have hnonzero : (QuotientAddGroup.mk' L) (s • e) ∈ torusRaySubgroup L e :=
    torusRay_subset L e ⟨s, hs.le, rfl⟩
  have hnontrivial : (torusRaySubgroup L e : Set (Torus L)).Nontrivial := by
    refine ⟨(QuotientAddGroup.mk' L) (s • e), hnonzero, 0, zero_mem _, hq⟩
  have hinf : (torusRaySubgroup L e : Set (Torus L)).Infinite :=
    (isPreconnected_torusRaySubgroup L e).infinite_of_nontrivial hnontrivial
  exact Set.infinite_coe_iff.mpr hinf

/-- **Proposition 4.2's translated infinite closed subgroup, from a torus ray.** -/
theorem exists_translate_raySubgroup {L : AddSubgroup Pt} [CompactSpace (Torus L)]
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    {Y : Set (Torus L)} (hY : IsClosed Y) {b : Torus L} {e : Pt} (he : e ≠ 0)
    (hray : ∀ s : ℝ, 0 ≤ s → b + (QuotientAddGroup.mk' L) (s • e) ∈ Y) :
    ∃ H : AddSubgroup (Torus L), Infinite H ∧ IsClosed (H : Set (Torus L)) ∧
      (∀ s : ℝ, 0 ≤ s → (QuotientAddGroup.mk' L) (s • e) ∈ H) ∧
      (∀ h ∈ H, b + h ∈ Y) := by
  let H := torusRaySubgroup L e
  have hmap : ((fun h : Torus L => b + h) '' (H : Set (Torus L))) =
      closure ((fun y : Torus L => b + y) '' torusRay L e) := by
    exact Homeomorph.image_closure (Homeomorph.addLeft b) (torusRay L e)
  have hsub : ((fun y : Torus L => b + y) '' torusRay L e) ⊆ Y := by
    rintro _ ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact hray s hs
  have hInf : Infinite H := by
    dsimp [H]
    exact infinite_torusRaySubgroup L e he
  refine ⟨H, hInf, isClosed_torusRaySubgroup L e, ?_, ?_⟩
  · intro s hs
    exact torusRay_subset L e ⟨s, hs, rfl⟩
  · intro h hh
    have hmem : b + h ∈ (fun h : Torus L => b + h) '' (H : Set (Torus L)) :=
      ⟨h, hh, rfl⟩
    rw [hmap] at hmem
    exact closure_minimal hsub hY hmem

/-- Compose the tangent-net limiting ray with
`exists_translate_raySubgroup`. -/
theorem exists_translate_raySubgroup_of_arc {L : AddSubgroup Pt}
    [CompactSpace (Torus L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    {Y : Set (Torus L)} (hY : IsClosed Y)
    {a : Pt} {w₀ c : ℂ} {t' : ℝ}
    (hρ : 1 < ‖cplxOf a‖) (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ht' : 0 < t')
    (hinv : ∀ x : Pt, (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (ptMul a x) ∈ Y)
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      (QuotientAddGroup.mk' L) (BerendTangentNet.arcThrough w₀ c t) ∈ Y) :
    ∃ (b : Torus L) (e : Pt) (H : AddSubgroup (Torus L)),
      e ∈ BerendBlockLastMile.cplxPlane ∧ e ≠ 0 ∧ Infinite H ∧
      IsClosed (H : Set (Torus L)) ∧
      (∀ s : ℝ, 0 ≤ s → (QuotientAddGroup.mk' L) (s • e) ∈ H) ∧
      (∀ h ∈ H, b + h ∈ Y) := by
  obtain ⟨b, e, heplane, he, hray⟩ :=
    BerendTangentNet.exists_ray_subset hY hρ hw₀ hc0 hc1 ht' hinv harc
  obtain ⟨H, hInf, hHclosed, hrayH, htranslate⟩ := exists_translate_raySubgroup hY he hray
  exact ⟨b, e, H, heplane, he, hInf, hHclosed, hrayH, htranslate⟩

end BerendRaySubgroup
end CubicTwoStage

#print axioms CubicTwoStage.BerendRaySubgroup.neg_mem_of_isCompact
#print axioms CubicTwoStage.BerendRaySubgroup.infinite_torusRaySubgroup
#print axioms CubicTwoStage.BerendRaySubgroup.exists_translate_raySubgroup
#print axioms CubicTwoStage.BerendRaySubgroup.exists_translate_raySubgroup_of_arc
