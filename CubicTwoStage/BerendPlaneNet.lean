/-
# Stage I for the block model: the planar branch is closed by density at the
complex place

Swarm `smw97otfd`, member `m3`, direction `d3` (Stage I planar net).

`CubicTwoStage/BerendStageIBlockAxis.lean` closes the *axis* branch of Stage I for
the unit–prime model unconditionally from two arithmetic densities, and isolates
the remaining case as `hplanar`: a closed invariant `Y ⊆ Pt ⧸ L` whose lift
accumulates at `0` inside the invariant complex plane `{x | x 0 = 0}`.

This file **closes that planar branch**, and therefore Stage I itself, modulo
exactly three printed arithmetic density hypotheses — with no new axioms, no
`sorry`, and no use of `berend_multi_invariance`.

The mathematical point (Berend's Lemma 4.6 read in the block model).  The plane
`cplxPlane` is invariant under every family multiplier, and on it the multiplier
`μ_{u,j} = D.mult u j` acts as multiplication by the *complex number*
`cplxOf (D.mult u j) = σ₂(u) σ₂(π)^j`.  Hence if the set of these complex
multipliers is **dense in `ℂ`** then, for a single nonzero plane point `x`, the
orbit `{μ_{u,j} · x}` is already dense in the whole plane — one point expands to
an ε-net for the plane, which is the block-model form of "expanding images of an
arc are ε-nets for arbitrarily long segments".  The lattice `L` then transports
that net to all of `Pt ⧸ L` (`dense_cplxPlane_add`), so `Y = univ`.

So the depth of Berend §4 disappears in the block model and is replaced by one
arithmetic statement about the complex embeddings of the unit and the prime.
Everything dynamic is discharged here; what remains are the densities

* `hscal  : Dense (range fun i => (D.mult i.1 i.2) 0)` (real place, direction (A);
  since this run, proved outright in `BerendStageIScalar.lean` by member m1),
* `haxis  : Dense (coord {0} + L)`                  (complex-place lattice, direction (B)),
* `hC : CplxMultiplierDense D` — `{σ₂(u) σ₂(π)^j}` dense in `ℂ*` (complex place; new
  here, and *sharper* than density in `ℂ`: it is the exact condition
  "log ‖σ₂π‖ / log ‖σ₂ε‖ irrational and one normalized phase irrational"),

plus `CofinalPlane L`, which `BerendCofinalityConcrete` proves for the canonical
complex cubic with no hypotheses at all.

The file also records a defect of the compiled target file: the planar residual
`hplanar` of `BerendStageIBlockAxis.lean` is *refutable* as stated
(`not_weakPlanar`), because it only receives accumulation of `π⁻¹' Y`, not of
`π⁻¹' (Y \ {0})`.  `eq_univ_of_plane_acc` / `eq_univ_of_plane_acc_cplx` are the
corrected forms.
-/
import CubicTwoStage.BerendStageIBlockAxis
import CubicTwoStage.BerendCofinalityConcrete

open Set Filter Topology
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace CubicTwoStage
namespace BerendStageIPlane

open BerendBlockLastMile

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-! ## 1. `ofCplx` and the plane as the complex line -/

/-- The plane of the block model is the coordinate plane `x 0 = 0`. -/
theorem cplxPlane_eq_coord_zero : cplxPlane = {x : Pt | x 0 = 0} := rfl

theorem ofCplx_zero : ofCplx (0 : ℂ) = 0 := by
  funext i
  fin_cases i <;> simp [ofCplx]

theorem ofCplx_add (a b : ℂ) : ofCplx (a + b) = ofCplx a + ofCplx b := by
  funext i
  fin_cases i <;> simp [ofCplx]

theorem ofCplx_sub (a b : ℂ) : ofCplx (a - b) = ofCplx a - ofCplx b := by
  funext i
  fin_cases i <;> simp [ofCplx]

/-- On the plane, the supremum norm is bounded by the complex modulus.  (Already
in `BerendBlockLastMile` for plane points; here in the `ofCplx` form used below.) -/
theorem norm_ofCplx_le (z : ℂ) : ‖ofCplx z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (x := ofCplx z) (r := ‖z‖) (hr := norm_nonneg z)).mpr ?_
  intro i
  fin_cases i
  · simp [ofCplx]
  · simpa [ofCplx] using Complex.abs_re_le_norm z
  · simpa [ofCplx] using Complex.abs_im_le_norm z

/-! ## 2. The planar net: one nonzero plane point, all complex multipliers -/

/-- **The expanding images of a single plane point fill the plane.**  If the
complex multipliers `cplxOf (D.mult u j)` are dense in `ℂ`, then for every
nonzero plane point `x` the orbit `{μ · x}` is dense in the plane `cplxPlane`.

This is the block-model form of Berend's Lemma 4.6: the family of multipliers is
a net, so a *single* orbit point already generates an ε-net for any bounded piece
of the plane. -/
theorem cplxPlane_subset_closure_range (D : UnitPrimeModel L 𝒪)
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2)))
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0) :
    cplxPlane ⊆ closure (Set.range fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x) := by
  have hx' : x = ofCplx (cplxOf x) := (eq_ofCplx_cplxOf hx).symm
  have hz : cplxOf x ≠ 0 := by
    intro h
    apply hx0
    rw [hx', h, ofCplx_zero]
  intro w hw
  have hw' : w = ofCplx (cplxOf w) := (eq_ofCplx_cplxOf hw).symm
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hzpos : 0 < ‖cplxOf x‖ := norm_pos_iff.mpr hz
  obtain ⟨y, hyball, i, hi⟩ :=
    Metric.dense_iff.mp hscalC (cplxOf w / cplxOf x) (ε / (2 * ‖cplxOf x‖))
      (by positivity)
  rw [Metric.mem_ball, dist_eq_norm] at hyball
  refine ⟨ptMul (D.mult i.1 i.2) x, ⟨i, rfl⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hsub : ptMul (D.mult i.1 i.2) x - w
      = ofCplx (cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w) := by
    rw [hx', hw', ptMul_ofCplx, ofCplx_sub, cplxOf_ofCplx, cplxOf_ofCplx]
  rw [hsub]
  have hstep : ‖ofCplx (cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w)‖
      ≤ ‖cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w‖ := norm_ofCplx_le _
  refine lt_of_le_of_lt hstep ?_
  have hkey : cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w
      = cplxOf x * (cplxOf (D.mult i.1 i.2) - cplxOf w / cplxOf x) := by
    field_simp
  rw [hkey, norm_mul]
  have hd : ‖cplxOf (D.mult i.1 i.2) - cplxOf w / cplxOf x‖ < ε / (2 * ‖cplxOf x‖) := by
    have hi' : cplxOf (D.mult i.1 i.2) = y := hi
    rw [hi']
    exact hyball
  have h2 : ‖cplxOf x‖ * (ε / (2 * ‖cplxOf x‖)) = ε / 2 := by
    field_simp
  calc ‖cplxOf x‖ * ‖cplxOf (D.mult i.1 i.2) - cplxOf w / cplxOf x‖
      < ‖cplxOf x‖ * (ε / (2 * ‖cplxOf x‖)) := by
        exact mul_lt_mul_of_pos_left hd hzpos
    _ = ε / 2 := h2
    _ < ε := by linarith

/-- **Finite ε-nets for compact pieces of the plane**, from the expanding images
of a single nonzero plane point: the "ε-net for arbitrarily long segments"
conclusion of Berend's Lemma 4.6, here for a compact piece of the invariant
plane. -/
theorem exists_finset_net (D : UnitPrimeModel L 𝒪)
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2)))
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    {Ks : Set Pt} (hK : IsCompact Ks) (hKsub : Ks ⊆ cplxPlane)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (𝒪ˣ × ℕ), ∀ y ∈ Ks, ∃ i ∈ F, ‖ptMul (D.mult i.1 i.2) x - y‖ < ε := by
  have hcl := cplxPlane_subset_closure_range D hscalC hx hx0
  have hcov : Ks ⊆ ⋃ i : 𝒪ˣ × ℕ, {y : Pt | ‖ptMul (D.mult i.1 i.2) x - y‖ < ε} := by
    intro y hy
    have hmem := hcl (hKsub hy)
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨z, hz, hzd⟩ := hmem ε hε
    obtain ⟨i, rfl⟩ := hz
    refine mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm] at hzd
    rw [norm_sub_rev]
    exact hzd
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun i : 𝒪ˣ × ℕ => {y : Pt | ‖ptMul (D.mult i.1 i.2) x - y‖ < ε})
    (fun i => isOpen_lt (continuous_const.sub continuous_id).norm continuous_const) hcov
  refine ⟨F, fun y hy => ?_⟩
  have hy' := hF hy
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hy'
  obtain ⟨i, hiF, hiy⟩ := hy'
  exact ⟨i, hiF, hiy⟩

/-! ## 3. The plane point forces `Y = univ` -/

/-- The family action on the lift of a nonzero plane point is the complex
multiplication by the corresponding multiplier. -/
theorem torusAct_mk_plane (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) {x : Pt}
    (hx : x ∈ cplxPlane) :
    D.torusAct i ((QuotientAddGroup.mk' L) x)
      = (QuotientAddGroup.mk' L) (ptMul (D.mult i.1 i.2) x) := by
  rw [D.torusAct_mk', D.family_apply]
  rfl

/-- **A nonzero plane point in a closed invariant set fills the lift with the
whole plane.** -/
theorem cplxPlane_subset_preimage (D : UnitPrimeModel L 𝒪)
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2)))
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    cplxPlane ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  have hclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsub : Set.range (fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x)
      ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rintro z ⟨i, rfl⟩
    show (QuotientAddGroup.mk' L) (ptMul (D.mult i.1 i.2) x) ∈ Y
    rw [← torusAct_mk_plane D i hx]
    exact hinv i ⟨_, hxY, rfl⟩
  calc cplxPlane ⊆ closure (Set.range fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x) :=
        cplxPlane_subset_closure_range D hscalC hx hx0
    _ ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := closure_minimal hsub hclosed

/-- **Stage I, plane branch.**  A closed family-invariant `Y` whose lift contains
the class of one nonzero point of the invariant complex plane is everything. -/
theorem eq_univ_of_plane_point (D : UnitPrimeModel L 𝒪)
    (hc : CofinalPlane L)
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2)))
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    Y = univ := by
  have hpre : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsat : ∀ l ∈ L, ∀ z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      z + l ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro l hl z hz
    show (QuotientAddGroup.mk' L) (z + l) ∈ Y
    rw [map_add]
    have h0 : (QuotientAddGroup.mk' L) l = 0 := by
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa using hl
    rw [h0, add_zero]
    exact hz
  have hplane := cplxPlane_subset_preimage D hscalC hY hinv hx hx0 hxY
  have hE : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    eq_univ_of_unboundedPlane_subset (L := L) hc hpre hsat (R := 0)
      (fun w hw _ => hplane hw)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have hz : z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by rw [hE]; exact mem_univ z
  exact hz

/-- **Stage I, planar accumulation.**  This is exactly the hypothesis `hplanar`
left open by `BerendStageIBlock_zeroNonisolatedFull_of_planar_acc`: accumulation
at `0` along the invariant complex plane. -/
theorem eq_univ_of_plane_acc (D : UnitPrimeModel L 𝒪)
    (hc : CofinalPlane L)
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2)))
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hacc : (0 : Pt) ∈
      closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    Y = univ := by
  obtain ⟨x, hx, -⟩ := mem_closure_iff_seq_limit.mp hacc
  have hxP : x 0 ∈ cplxPlane := (hx 0).2
  have hxY : (QuotientAddGroup.mk' L) (x 0) ∈ Y := (hx 0).1.1
  have hx0 : x 0 ≠ 0 := by
    intro h
    apply (hx 0).1.2
    rw [h]
    exact map_zero _
  exact eq_univ_of_plane_point D hc hscalC hY hinv hxP hx0 hxY

/-! ## 4. Stage I with all dynamical content discharged

The three printed hypotheses below are arithmetic: they say that the unit and the
prime have images whose multiplicative semigroup is dense at the real place, at
the complex place, and that the real-coordinate projection of the lattice is
dense (which with `CofinalPlane` also gives `Dense (cplxPlane + L)`).  Nothing
here is a dynamical assertion about `Y`. -/

/-- **Stage I for the unit–prime family.**  A closed family-invariant set of which
`0` is a non-isolated point is the whole torus, granted

* a unit `ε` expanding the real coordinate (`1 < |ε 0|`, with `|normR ε| = 1`),
* `CofinalPlane L`,
* density of the real scalars `(D.mult u j) 0` in `ℝ`,
* density of `coord {0} + L` in `Pt`,
* density of the complex multipliers `cplxOf (D.mult u j)` in `ℂ`.

Both branches of Berend's Lemma 4.1 are used: off the plane by
`eq_univ_of_nonplanar_acc` (term balancing), on it by `eq_univ_of_plane_acc`
(the planar net). -/
theorem zeroNonisolatedFull_of_density (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hε1 : 1 < |D.unit_image ε 0|)
    (hεN : |normR (D.unit_image ε)| = 1)
    (hc : CofinalPlane L)
    (hscal : Dense (Set.range fun i : 𝒪ˣ × ℕ => (D.mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt)))
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2))) :
    BerendDichotomy.ZeroNonisolatedFull D.torusAct := by
  intro Y hY _hne hacc hinv
  have hopen : IsOpenMap (QuotientAddGroup.mk' L : Pt → Torus L) :=
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have hcont : Continuous (QuotientAddGroup.mk' L : Pt → Torus L) :=
    QuotientAddGroup.isOpenQuotientMap_mk.continuous
  have hlift : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0})) := by
    rw [← IsOpenMap.preimage_closure_eq_closure_preimage hopen hcont]
    simpa using hacc
  rcases BerendStageIBlock.closure_inter_axis_dichotomy hlift with hoff | hon
  · have hsub : (QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ {x : Pt | x 0 ≠ 0}
        ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y ∩ {x : Pt | x 0 ≠ 0} :=
      fun x hx => ⟨Set.preimage_mono Set.sdiff_subset hx.1, hx.2⟩
    exact BerendStageIBlock.eq_univ_of_nonplanar_acc D ε hε1 hεN hY hinv hscal haxis
      (closure_mono hsub hoff)
  · exact eq_univ_of_plane_acc D hc hscalC hY hinv hon

end BerendStageIPlane

namespace BerendStageIPlane

open BerendBlockLastMile

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- **The arithmetic residual, in its sharp form**: the complex multipliers are
dense in `ℂ*` (density at the complex place).  This is what the character
computation for the multiplicative group gives: `{σ₂(ε)^m σ₂(π)^j}` is dense in
`ℂ*` iff `log σ₂π / log σ₂ε ∉ ℝ`.  It is implied by density in `ℂ`
(`cplxMultiplierDense_of_dense`) but does not require arbitrarily small
multipliers. -/
def CplxMultiplierDense (D : UnitPrimeModel L 𝒪) : Prop :=
  ∀ z : ℂ, z ≠ 0 → ∀ ε : ℝ, 0 < ε →
    ∃ i : 𝒪ˣ × ℕ, ‖cplxOf (D.mult i.1 i.2) - z‖ < ε

theorem cplxMultiplierDense_of_dense (D : UnitPrimeModel L 𝒪)
    (h : Dense (Set.range fun i : 𝒪ˣ × ℕ => cplxOf (D.mult i.1 i.2))) :
    CplxMultiplierDense D := by
  intro z _ ε hε
  obtain ⟨y, hball, i, hi⟩ := Metric.dense_iff.mp h z ε hε
  rw [Metric.mem_ball, dist_eq_norm] at hball
  refine ⟨i, ?_⟩
  have hi' : cplxOf (D.mult i.1 i.2) = y := hi
  rw [hi']
  exact hball

/-- The complex-multiplier form of the planar net: for a nonzero plane point `x`,
the orbit `{μ · x}` is dense in `ℂ* · x`, i.e. in the punctured plane. -/
theorem cplxPlane_ne_zero_subset_closure_range (D : UnitPrimeModel L 𝒪)
    (hC : CplxMultiplierDense D)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0) :
    cplxPlane \ {0} ⊆
      closure (Set.range fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x) := by
  have hx' : x = ofCplx (cplxOf x) := (eq_ofCplx_cplxOf hx).symm
  have hz : cplxOf x ≠ 0 := by
    intro h
    apply hx0
    rw [hx', h, ofCplx_zero]
  intro w hw
  have hw0 : w ≠ 0 := hw.2
  have hw' : w = ofCplx (cplxOf w) := (eq_ofCplx_cplxOf hw.1).symm
  have hzw : cplxOf w ≠ 0 := by
    intro h
    apply hw0
    rw [hw', h, ofCplx_zero]
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hzpos : 0 < ‖cplxOf x‖ := norm_pos_iff.mpr hz
  obtain ⟨i, hi⟩ := hC (cplxOf w / cplxOf x) (div_ne_zero hzw hz)
    (ε / (2 * ‖cplxOf x‖)) (by positivity)
  refine ⟨ptMul (D.mult i.1 i.2) x, ⟨i, rfl⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hsub : ptMul (D.mult i.1 i.2) x - w
      = ofCplx (cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w) := by
    rw [hx', hw', ptMul_ofCplx, ofCplx_sub, cplxOf_ofCplx, cplxOf_ofCplx]
  rw [hsub]
  have hstep : ‖ofCplx (cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w)‖
      ≤ ‖cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w‖ := norm_ofCplx_le _
  refine lt_of_le_of_lt hstep ?_
  have hkey : cplxOf (D.mult i.1 i.2) * cplxOf x - cplxOf w
      = cplxOf x * (cplxOf (D.mult i.1 i.2) - cplxOf w / cplxOf x) := by
    field_simp
  rw [hkey, norm_mul]
  have h2 : ‖cplxOf x‖ * (ε / (2 * ‖cplxOf x‖)) = ε / 2 := by field_simp
  calc ‖cplxOf x‖ * ‖cplxOf (D.mult i.1 i.2) - cplxOf w / cplxOf x‖
      < ‖cplxOf x‖ * (ε / (2 * ‖cplxOf x‖)) := by
        exact mul_lt_mul_of_pos_left hi hzpos
    _ = ε / 2 := h2
    _ < ε := by linarith

/-- The punctured plane is in the lift, from the complex-multiplier net. -/
theorem cplxPlane_ne_zero_subset_preimage (D : UnitPrimeModel L 𝒪)
    (hC : CplxMultiplierDense D)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    cplxPlane \ {0} ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := by
  have hclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsub : Set.range (fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x)
      ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rintro z ⟨i, rfl⟩
    show (QuotientAddGroup.mk' L) (ptMul (D.mult i.1 i.2) x) ∈ Y
    rw [← torusAct_mk_plane D i hx]
    exact hinv i ⟨_, hxY, rfl⟩
  calc cplxPlane \ {0}
      ⊆ closure (Set.range fun i : 𝒪ˣ × ℕ => ptMul (D.mult i.1 i.2) x) :=
        cplxPlane_ne_zero_subset_closure_range D hC hx hx0
    _ ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y := closure_minimal hsub hclosed

/-- **Stage I, plane branch, sharp form.**  A closed family-invariant `Y` whose
lift contains the class of one nonzero point of the invariant complex plane is
everything, granted that the complex multipliers are dense in `ℂ*`. -/
theorem eq_univ_of_plane_point_cplx (D : UnitPrimeModel L 𝒪)
    (hc : CofinalPlane L) (hC : CplxMultiplierDense D)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    {x : Pt} (hx : x ∈ cplxPlane) (hx0 : x ≠ 0)
    (hxY : (QuotientAddGroup.mk' L) x ∈ Y) :
    Y = univ := by
  have hpre : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage continuous_quotient_mk'
  have hsat : ∀ l ∈ L, ∀ z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      z + l ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro l hl z hz
    show (QuotientAddGroup.mk' L) (z + l) ∈ Y
    rw [map_add]
    have h0 : (QuotientAddGroup.mk' L) l = 0 := by
      have hk : l ∈ (QuotientAddGroup.mk' L : Pt →+ Torus L).ker := by
        rw [QuotientAddGroup.ker_mk']
        exact hl
      rw [AddMonoidHom.mem_ker] at hk
      exact hk
    rw [h0, add_zero]
    exact hz
  have hplane := cplxPlane_ne_zero_subset_preimage D hC hY hinv hx hx0 hxY
  have hne : ∀ w : Pt, w ∈ cplxPlane → (1 : ℝ) ≤ ‖w‖ → w ≠ 0 := by
    intro w _ h1 h
    rw [h] at h1
    simp at h1
    linarith
  have hE : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    eq_univ_of_unboundedPlane_subset (L := L) hc hpre hsat (R := 1)
      (fun w hw h1 => hplane ⟨hw, hne w hw h1⟩)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have hz : z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by rw [hE]; exact mem_univ z
  exact hz

/-- **Stage I, planar accumulation, sharp form.** -/
theorem eq_univ_of_plane_acc_cplx (D : UnitPrimeModel L 𝒪)
    (hc : CofinalPlane L) (hC : CplxMultiplierDense D)
    {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ i, D.torusAct i '' Y ⊆ Y)
    (hacc : (0 : Pt) ∈
      closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    Y = univ := by
  obtain ⟨x, hx, -⟩ := mem_closure_iff_seq_limit.mp hacc
  have hxP : x 0 ∈ cplxPlane := (hx 0).2
  have hxY : (QuotientAddGroup.mk' L) (x 0) ∈ Y := (hx 0).1.1
  have hx0 : x 0 ≠ 0 := by
    intro h
    apply (hx 0).1.2
    rw [h]
    exact map_zero _
  exact eq_univ_of_plane_point_cplx D hc hC hY hinv hxP hx0 hxY

end BerendStageIPlane

namespace BerendStageIPlane

open BerendBlockLastMile

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- **Stage I for the unit–prime family, sharp residual.**  The complex-place
input is `CplxMultiplierDense D` (density of `{σ₂(u) σ₂(π)^j}` in `ℂ*`), not
density in `ℂ`. -/
theorem zeroNonisolatedFull_of_cplxDensity (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hε1 : 1 < |D.unit_image ε 0|)
    (hεN : |normR (D.unit_image ε)| = 1)
    (hc : CofinalPlane L)
    (hscal : Dense (Set.range fun i : 𝒪ˣ × ℕ => (D.mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (L : Set Pt)))
    (hC : CplxMultiplierDense D) :
    BerendDichotomy.ZeroNonisolatedFull D.torusAct := by
  intro Y hY _hne hacc hinv
  have hopen : IsOpenMap (QuotientAddGroup.mk' L : Pt → Torus L) :=
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have hcont : Continuous (QuotientAddGroup.mk' L : Pt → Torus L) :=
    QuotientAddGroup.isOpenQuotientMap_mk.continuous
  have hlift : (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' (Y \ {0})) := by
    rw [← IsOpenMap.preimage_closure_eq_closure_preimage hopen hcont]
    simpa using hacc
  rcases BerendStageIBlock.closure_inter_axis_dichotomy hlift with hoff | hon
  · have hsub : (QuotientAddGroup.mk' L) ⁻¹' (Y \ {0}) ∩ {x : Pt | x 0 ≠ 0}
        ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y ∩ {x : Pt | x 0 ≠ 0} :=
      fun x hx => ⟨Set.preimage_mono Set.sdiff_subset hx.1, hx.2⟩
    exact BerendStageIBlock.eq_univ_of_nonplanar_acc D ε hε1 hεN hY hinv hscal haxis
      (closure_mono hsub hoff)
  · exact eq_univ_of_plane_acc_cplx D hc hC hY hinv hon

end BerendStageIPlane

namespace BerendStageIPlane

open BerendBlockLastMile

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- **The planar residual `hplanar` of the compiled target file is too weak — it
is refutable.**  `BerendStageIBlock.zeroNonisolatedFull_of_planar_acc` feeds
`hplanar` the hypothesis `0 ∈ closure (π⁻¹' Y ∩ cplxPlane)`, but that hypothesis is
satisfied by `Y = {0}` (since `0 ∈ L`), so the weak form would force `{0} = univ`.
The correct hypothesis is accumulation of `Y \ {0}`, which is what
`eq_univ_of_plane_acc` uses. -/
theorem not_weakPlanar (D : UnitPrimeModel L 𝒪) [T1Space (Torus L)]
    (hL : ∃ x : Pt, x ∉ L) :
    ¬ (∀ Y : Set (Torus L), IsClosed Y → (∀ i, D.torusAct i '' Y ⊆ Y) →
        (0 : Pt) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' Y ∩ cplxPlane) → Y = univ) := by
  intro H
  have hclosed : IsClosed ({0} : Set (Torus L)) := isClosed_singleton
  have hinv : ∀ i, D.torusAct i '' ({0} : Set (Torus L)) ⊆ {0} := by
    rintro i y ⟨z, hz, rfl⟩
    simp only [Set.mem_singleton_iff] at hz ⊢
    rw [hz, map_zero]
  have hacc : (0 : Pt) ∈
      closure ((QuotientAddGroup.mk' L) ⁻¹' ({0} : Set (Torus L)) ∩ cplxPlane) := by
    refine subset_closure ⟨?_, rfl⟩
    show (QuotientAddGroup.mk' L) (0 : Pt) = 0
    exact map_zero _
  have huniv := H {0} hclosed hinv hacc
  obtain ⟨x, hx⟩ := hL
  have hx0 : (QuotientAddGroup.mk' L) x ≠ 0 := by
    intro h
    apply hx
    have hk : x ∈ (QuotientAddGroup.mk' L : Pt →+ Torus L).ker := by
      rw [AddMonoidHom.mem_ker]
      exact h
    rwa [QuotientAddGroup.ker_mk'] at hk
  have hmem : (QuotientAddGroup.mk' L) x ∈ ({0} : Set (Torus L)) := by
    rw [huniv]
    exact mem_univ _
  exact hx0 (by simpa using hmem)

end BerendStageIPlane

namespace BerendStageIPlane

open NumberField
open BerendBlockLastMile

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- **Stage I, `FieldModel` form.**  The norm hypothesis is `FieldModel.abs_normR_unit`;
only the three arithmetic densities are carried. -/
theorem zeroNonisolatedFull_fieldModel_of_density (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ)
    (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hε1 : 1 < |FM.σ (((ε : 𝒪) : K)) 0|)
    (hc : CofinalPlane FM.lattice)
    (hscal : Dense (Set.range fun i : 𝒪ˣ × ℕ =>
      ((FM.toModel ε π hπO hπ0).mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hscalC : Dense (Set.range fun i : 𝒪ˣ × ℕ =>
      cplxOf ((FM.toModel ε π hπO hπ0).mult i.1 i.2))) :
    BerendDichotomy.ZeroNonisolatedFull (FM.toModel ε π hπO hπ0).torusAct :=
  zeroNonisolatedFull_of_density (FM.toModel ε π hπO hπ0) ε hε1
    (FM.abs_normR_unit ε) hc hscal haxis hscalC

/-- **Stage I, `FieldModel` form, sharp residual.**  The complex-place input is
`CplxMultiplierDense` (density of `{σ₂(u) σ₂(π)^j}` in `ℂ*`). -/
theorem zeroNonisolatedFull_fieldModel_of_cplxDensity (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ)
    (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hε1 : 1 < |FM.σ (((ε : 𝒪) : K)) 0|)
    (hc : CofinalPlane FM.lattice)
    (hscal : Dense (Set.range fun i : 𝒪ˣ × ℕ =>
      ((FM.toModel ε π hπO hπ0).mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) + (FM.lattice : Set Pt)))
    (hC : CplxMultiplierDense (FM.toModel ε π hπO hπ0)) :
    BerendDichotomy.ZeroNonisolatedFull (FM.toModel ε π hπO hπ0).torusAct :=
  zeroNonisolatedFull_of_cplxDensity (FM.toModel ε π hπO hπ0) ε hε1
    (FM.abs_normR_unit ε) hc hscal haxis hC

end BerendStageIPlane

namespace BerendStageIPlane

open NumberField NumberFieldCubic
open BerendBlockLastMile

variable {K : Type*} [Field K] [NumberField K]

/-- **A nonzero plane point is not a lattice point of the canonical model**: the
real embedding is injective, so an element whose real coordinate vanishes is zero.
This is the input `∃ x, x ∉ L` of `not_weakPlanar`. -/
theorem ofCplx_one_not_mem_canonical_lattice (h : IsComplexCubic K) :
    ofCplx (1 : ℂ) ∉ (canonicalFieldModel K h).lattice := by
  intro hmem
  obtain ⟨g, hg⟩ := (canonicalFieldModel K h).mem_lattice.mp hmem
  have h0 : realEmbedding K h (((g : numberFieldO K)) : K) = 0 := by
    have h2 : ((canonicalFieldModel K h).σ (((g : numberFieldO K)) : K)) 0 = 0 := by
      rw [hg]
      rfl
    rw [← σ_apply_zero (K := K) (h := h)]
    exact h2
  have hg0 : (((g : numberFieldO K)) : K) = 0 :=
    (realEmbedding K h).injective (by simpa using h0)
  have hz : ((canonicalFieldModel K h).σ (((g : numberFieldO K)) : K)) = 0 := by
    rw [hg0]
    exact (canonicalFieldModel K h).σ_zero
  rw [hg] at hz
  have hcoord : (ofCplx (1 : ℂ)) 1 = (0 : Pt) 1 := by rw [hz]
  simp [ofCplx] at hcoord

/-- **Instantiation of the refutation at the canonical complex cubic**: the planar
hypothesis of `BerendStageIBlockAxis.lean` is false for the canonical model, so
that file's `zeroNonisolatedFull_..._of_planar` cannot be applied as stated; the
corrected form is `zeroNonisolatedFull_canonical_of_density`. -/
theorem not_weakPlanar_canonical (h : IsComplexCubic K) (ε : (numberFieldO K)ˣ)
    (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0) :
    ¬ (∀ Y : Set (Torus (canonicalFieldModel K h).lattice), IsClosed Y →
        (∀ i, ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i '' Y ⊆ Y) →
        (0 : Pt) ∈ closure ((QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) ⁻¹'
          Y ∩ cplxPlane) → Y = univ) := by
  haveI : DiscreteTopology ↥((canonicalFieldModel K h).lattice) :=
    discreteTopology_canonicalFieldModel_lattice (K := K) h
  haveI : IsClosed ((canonicalFieldModel K h).lattice : Set Pt) :=
    AddSubgroup.isClosed_of_discrete
  exact not_weakPlanar ((canonicalFieldModel K h).toModel ε π hπO hπ0)
    ⟨ofCplx 1, ofCplx_one_not_mem_canonical_lattice h⟩

/-- **Stage I for the canonical complex cubic.**  `CofinalPlane` is discharged by
`BerendCofinality.cofinalPlane_canonicalFieldModel_of_isComplexCubic`, so the only
hypotheses left are the three arithmetic densities at the real place, at the
complex place, and along the real axis of the lattice. -/
theorem zeroNonisolatedFull_canonical_of_density (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hε1 : 1 < |(canonicalFieldModel K h).σ (((ε : numberFieldO K) : K)) 0|)
    (hscal : Dense (Set.range fun i : (numberFieldO K)ˣ × ℕ =>
      (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) +
      ((canonicalFieldModel K h).lattice : Set Pt)))
    (hscalC : Dense (Set.range fun i : (numberFieldO K)ˣ × ℕ =>
      cplxOf (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2))) :
    BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  zeroNonisolatedFull_fieldModel_of_density (canonicalFieldModel K h) ε π hπO hπ0 hε1
    (BerendCofinality.cofinalPlane_canonicalFieldModel_of_isComplexCubic K h)
    hscal haxis hscalC

/-- **Stage I for the canonical complex cubic, sharp residual.**  Only the three
arithmetic densities remain: `hscal` (real place), `haxi` (`coord {0} + L`), and
`hC` (`{σ₂(u) σ₂(π)^j}` dense in `ℂ*`). -/
theorem zeroNonisolatedFull_canonical_of_cplxDensity (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hε1 : 1 < |(canonicalFieldModel K h).σ (((ε : numberFieldO K) : K)) 0|)
    (hscal : Dense (Set.range fun i : (numberFieldO K)ˣ × ℕ =>
      (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2) 0))
    (haxis : Dense ((BerendSec4.coord ({0} : Set (Fin 3)) : Set Pt) +
      ((canonicalFieldModel K h).lattice : Set Pt)))
    (hC : CplxMultiplierDense ((canonicalFieldModel K h).toModel ε π hπO hπ0)) :
    BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
  zeroNonisolatedFull_fieldModel_of_cplxDensity (canonicalFieldModel K h) ε π hπO hπ0 hε1
    (BerendCofinality.cofinalPlane_canonicalFieldModel_of_isComplexCubic K h)
    hscal haxis hC

end BerendStageIPlane
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendStageIPlane.ofCplx_zero
#print axioms CubicTwoStage.BerendStageIPlane.norm_ofCplx_le
#print axioms CubicTwoStage.BerendStageIPlane.cplxPlane_subset_closure_range
#print axioms CubicTwoStage.BerendStageIPlane.exists_finset_net
#print axioms CubicTwoStage.BerendStageIPlane.cplxPlane_subset_preimage
#print axioms CubicTwoStage.BerendStageIPlane.eq_univ_of_plane_point
#print axioms CubicTwoStage.BerendStageIPlane.eq_univ_of_plane_acc
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_of_density
#print axioms CubicTwoStage.BerendStageIPlane.not_weakPlanar
#print axioms CubicTwoStage.BerendStageIPlane.ofCplx_one_not_mem_canonical_lattice
#print axioms CubicTwoStage.BerendStageIPlane.not_weakPlanar_canonical
#print axioms CubicTwoStage.BerendStageIPlane.CplxMultiplierDense
#print axioms CubicTwoStage.BerendStageIPlane.cplxMultiplierDense_of_dense
#print axioms CubicTwoStage.BerendStageIPlane.cplxPlane_ne_zero_subset_closure_range
#print axioms CubicTwoStage.BerendStageIPlane.cplxPlane_ne_zero_subset_preimage
#print axioms CubicTwoStage.BerendStageIPlane.eq_univ_of_plane_point_cplx
#print axioms CubicTwoStage.BerendStageIPlane.eq_univ_of_plane_acc_cplx
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_of_cplxDensity
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_fieldModel_of_density
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_canonical_of_density
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_fieldModel_of_cplxDensity
#print axioms CubicTwoStage.BerendStageIPlane.zeroNonisolatedFull_canonical_of_cplxDensity
