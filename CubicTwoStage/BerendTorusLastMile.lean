/-
# Berend §4, the torus last mile (`BEREND_PROOF_PLAN.md` §C.6–§C.7)

Stage C of the plan has to pass from the diagonalized linear model `ι → ℝ` back
to the torus `(ι → ℝ) ⧸ L`.  `BerendRankTwoDiag.acc_coord_subset_sub` produces,
for a minimal accumulating coordinate set `{i}` on which one family element
expands and another contracts with multiplicatively independent multipliers,

  `coord {i} ⊆ prec E - prec E`,   where `prec E = mk' L ⁻¹' E`.

This file supplies the two steps that turn that into the conclusion stage D
consumes (`E - E = univ`):

* **§1–§2, the transfer.**  The image in `(ι → ℝ) ⧸ L` of the difference set of
  the preimage of `E` is `E - E`; so any subset `C` of that difference set
  whose sum with the lattice is dense forces `E - E = univ` (the torus is
  compact Hausdorff, so `E - E` is closed).

* **§3–§4, the irrational coordinate criterion.**  If the coordinate subspace is
  the *complement of a single coordinate* `j` (`S = univ.erase j`), then
  `coord S + L` is the full preimage of the `j`-th coordinate projection of `L`,
  so it is dense as soon as that projection is; and the projection is dense when
  `L` contains two elements whose `j`-th coordinates have irrational ratio
  (`dense_addSubgroupClosure_pair_iff`, i.e. density of `ℤ + ℤθ` for irrational
  `θ`).  This is the "irrational coordinate line" of §C.7.

* **§5, the assembled theorem.**  `torus_sub_eq_univ_of_acc_coord`: a closed
  `E ⊆ (ι → ℝ) ⧸ L` whose preimage accumulates at `0` on the one-dimensional
  coordinate set `{i}`, together with the expanding/contracting pair of
  `BerendRankTwoDiag` and the density of `coord {i} + L`, has `E - E = univ`.
  A second version derives the density from the irrational coordinate criterion
  when `{i}` is the complement of a single coordinate.

No `sorry`, no `axiom`, no new assumption: every hypothesis is printed.

## What is *not* here

* §5 assumes the output of Berend Lemmas 4.2–4.4 (the minimal coordinate set
  `{i}` together with its expanding/contracting pair with independent
  multipliers) and the one-dimensional rank-two input `acc_coord_subset_sub`.
* §3 covers only the case where the accumulating coordinate subspace misses a
  *single* coordinate.  The general criterion — `W + L` dense for a coordinate
  subspace `W` of codimension `≥ 2`, which needs the structure theory of closed
  subgroups of `ℝ ^ d` (equivalently: no nonzero lattice functional vanishes on
  `W`) — is **not** proved here.  In the cubic model it is the statement that a
  nonzero `β ∈ 𝒪_K` cannot have a vanishing embedding, and it is the one
  remaining input of the §C.7 last mile.
-/
import CubicTwoStage.BerendRankTwoDiag
import CubicTwoStage.BerendMinimalTorus
import CubicTwoStage.BerendCovering

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendTorusLastMile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Difference sets upstairs and downstairs -/

section Difference

variable {V : Type*} [AddCommGroup V] {L : AddSubgroup V}

/-- **The image of the difference set of the preimage is the difference set.**
`mk' L` is surjective and additive, so `prec E - prec E` and `E - E` have the
same image along the quotient map. -/
theorem mk_image_preimage_sub (E : Set (V ⧸ L)) :
    QuotientAddGroup.mk' L '' ((QuotientAddGroup.mk' L ⁻¹' E) - (QuotientAddGroup.mk' L ⁻¹' E))
      = E - E := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.1 hw
    exact Set.mem_sub.2 ⟨x, hx, y, hy, map_sub (QuotientAddGroup.mk' L) x y⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective L b
    refine ⟨x - y, Set.mem_sub.2 ⟨x, ha, y, hb, rfl⟩, ?_⟩
    exact map_sub (QuotientAddGroup.mk' L) x y

/-- A set contained in the difference set of the preimage has its image in the
difference set of the quotient set. -/
theorem image_subset_sub {E : Set (V ⧸ L)} {C : Set V}
    (hC : C ⊆ (QuotientAddGroup.mk' L ⁻¹' E) - (QuotientAddGroup.mk' L ⁻¹' E)) :
    QuotientAddGroup.mk' L '' C ⊆ E - E := by
  rw [← mk_image_preimage_sub E]
  exact Set.image_mono hC

/-- The quotient map identifies `C` and `C + L` inside the torus. -/
theorem image_add_subgroup {C : Set V} :
    QuotientAddGroup.mk' L '' (C + (L : Set V)) = QuotientAddGroup.mk' L '' C := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨c, ⟨x, hx, g, hg, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    simpa using hg
  · exact Set.image_mono (by
      intro x hx
      exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩)

end Difference

/-! ## 2. A dense subset of the difference set forces `E - E = univ` -/

section LastMile

variable {L : AddSubgroup (ι → ℝ)}

/-- The image of a dense set under a continuous surjection is dense. -/
theorem Dense.image_of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {f : X → Y} (hd : Dense s) (hsurj : Function.Surjective f)
    (hcont : Continuous f) :
    Dense (f '' s) := by
  rw [dense_iff_closure_eq] at hd ⊢
  have h1 : f '' closure s ⊆ closure (f '' s) := image_closure_subset_closure_image hcont
  rw [hd, Set.image_univ, Set.range_eq_univ.mpr hsurj] at h1
  exact Set.univ_subset_iff.mp h1

/-- **The last mile of stage C.**  Let `E ⊆ (ι → ℝ) ⧸ L` be closed, and let
`C ⊆ (mk' L)⁻¹ E - (mk' L)⁻¹ E` have dense sum with the lattice.  If the torus
is compact and Hausdorff then `E - E` is the whole torus. -/
theorem sub_eq_univ_of_dense [CompactSpace ((ι → ℝ) ⧸ L)] [T2Space ((ι → ℝ) ⧸ L)]
    {E : Set ((ι → ℝ) ⧸ L)} (hE : IsClosed E) {C : Set (ι → ℝ)}
    (hC : C ⊆ (QuotientAddGroup.mk' L ⁻¹' E) - (QuotientAddGroup.mk' L ⁻¹' E))
    (hdense : Dense ((C + (L : Set (ι → ℝ))) : Set (ι → ℝ))) :
    E - E = univ := by
  have hsub : QuotientAddGroup.mk' L '' C ⊆ E - E := image_subset_sub hC
  have himg_dense : Dense (QuotientAddGroup.mk' L '' C) := by
    have hdense' : Dense (QuotientAddGroup.mk' L '' ((C + (L : Set (ι → ℝ))))) :=
      Dense.image_of_surjective hdense (QuotientAddGroup.mk'_surjective L)
        QuotientAddGroup.continuous_mk
    rwa [image_add_subgroup] at hdense'
  have hclosed : IsClosed (E - E) := BerendMinimal.isClosed_sub hE
  have hdens : Dense (E - E) := Dense.mono hsub himg_dense
  rwa [dense_iff_closure_eq, hclosed.closure_eq] at hdens

end LastMile

/-! ## 3. The irrational coordinate criterion (codimension one) -/

section Coord

/-- The coordinate subspace off a single coordinate is the hyperplane `x j = 0`. -/
theorem coord_erase_eq (j : ι) :
    (BerendSec4.coord ((Finset.univ.erase j : Finset ι) : Set ι) : Set (ι → ℝ))
      = {x : ι → ℝ | x j = 0} := by
  ext x
  constructor
  · intro hx
    exact BerendSec4.mem_coord.1 hx j (by simp)
  · intro hx i hi
    have hij : i = j := by
      by_contra h
      exact hi (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩)
    rw [hij]
    exact hx

/-- The sum of the hyperplane `x j = 0` with the lattice is the full preimage of
the `j`-th coordinate projection of the lattice. -/
theorem erase_add_subgroup_eq (j : ι) (L : AddSubgroup (ι → ℝ)) :
    ({x : ι → ℝ | x j = 0} : Set (ι → ℝ)) + (L : Set (ι → ℝ))
      = {x : ι → ℝ | x j ∈ Set.range (fun l : L => (l : ι → ℝ) j)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hx
    have haj : a j = 0 := ha
    refine Set.mem_range.2 ⟨⟨b, hb⟩, ?_⟩
    show b j = (a + b) j
    rw [Pi.add_apply, haj, zero_add]
  · intro hx
    obtain ⟨l, hl⟩ := Set.mem_range.1 hx
    refine Set.mem_add.2 ⟨x - (l : ι → ℝ), ?_, (l : ι → ℝ), l.2, ?_⟩
    · show (x - (l : ι → ℝ)) j = 0
      rw [Pi.sub_apply, hl, sub_self]
    · abel

/-- A dense projection on one coordinate makes its full preimage dense. -/
theorem dense_preimage_of_dense_proj {L : AddSubgroup (ι → ℝ)} {j : ι}
    (hd : Dense (Set.range (fun l : L => (l : ι → ℝ) j))) :
    Dense ({x : ι → ℝ | x j ∈ Set.range (fun l : L => (l : ι → ℝ) j)}) := by
  set e : ι → ℝ := Pi.single j (1 : ℝ) with he
  have hej : e j = 1 := Pi.single_eq_same j 1
  have hnorm : (0 : ℝ) < ‖e‖ := by
    have h2 : (1 : ℝ) ≤ ‖e‖ := by
      have h3 := norm_le_pi_norm e j
      rwa [Real.norm_eq_abs, hej, abs_one] at h3
    linarith
  rw [Metric.dense_iff] at hd ⊢
  intro x r hr
  obtain ⟨y, hyball, hy⟩ := hd (x j) (r / ‖e‖) (by positivity)
  have hxy : |y - x j| < r / ‖e‖ := by
    rw [Metric.mem_ball, Real.dist_eq] at hyball
    exact hyball
  obtain ⟨l, hl⟩ := hy
  have hl' : (l : ι → ℝ) j = y := hl
  refine ⟨x + (y - x j) • e, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : x + (y - x j) • e - x = (y - x j) • e := by abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, mul_comm]
    calc ‖e‖ * |y - x j| < ‖e‖ * (r / ‖e‖) := mul_lt_mul_of_pos_left hxy hnorm
      _ = r := by field_simp
  · show (x + (y - x j) • e) j ∈ Set.range (fun l : L => (l : ι → ℝ) j)
    refine Set.mem_range.2 ⟨l, ?_⟩
    rw [hl', Pi.add_apply, Pi.smul_apply, hej, smul_eq_mul, mul_one]
    ring

/-- The full coordinate subspace is everything. -/
theorem coord_univ_eq_top :
    (BerendSec4.coord ((Finset.univ : Finset ι) : Set ι) : Submodule ℝ (ι → ℝ)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact BerendSec4.mem_coord.2 (by intro i hi; simp at hi)

/-- The full coordinate subspace is everything, so its sum with the lattice is
trivially dense.  (This is the `S = univ` case of the density requirement.) -/
theorem dense_coord_univ_add (L : AddSubgroup (ι → ℝ)) :
    Dense ((BerendSec4.coord ((Finset.univ : Finset ι) : Set ι) : Set (ι → ℝ))
      + (L : Set (ι → ℝ))) := by
  refine Dense.mono ?_ (dense_univ : Dense (Set.univ : Set (ι → ℝ)))
  intro x _
  refine Set.mem_add.2 ⟨x, ?_, 0, L.zero_mem, add_zero x⟩
  rw [coord_univ_eq_top]
  exact Submodule.mem_top

/-- **The codimension-one density criterion.**  If the accumulating coordinate
subspace misses exactly the coordinate `j`, then its sum with the lattice is
dense as soon as the `j`-th coordinate projection of the lattice is dense. -/
theorem dense_coord_erase_add_of_dense_proj {L : AddSubgroup (ι → ℝ)} {j : ι}
    (hd : Dense (Set.range (fun l : L => (l : ι → ℝ) j))) :
    Dense ((BerendSec4.coord ((Finset.univ.erase j : Finset ι) : Set ι) : Set (ι → ℝ))
      + (L : Set (ι → ℝ))) := by
  rw [coord_erase_eq, erase_add_subgroup_eq]
  exact dense_preimage_of_dense_proj hd

end Coord

/-! ## 4. An irrational ratio of two lattice coordinates -/

section Irrational

/-- **The irrational ratio criterion.**  If the lattice contains elements whose
`j`-th coordinates have irrational ratio, then the `j`-th coordinate projection
of the lattice is dense in `ℝ`.  (The one-dimensional input is the density of
`ℤ + ℤθ` for irrational `θ`, `dense_addSubgroupClosure_pair_iff`.) -/
theorem dense_range_coord_of_irrational {L : AddSubgroup (ι → ℝ)} {j : ι} {l l' : L}
    (hirr : Irrational ((l : ι → ℝ) j / (l' : ι → ℝ) j)) :
    Dense (Set.range (fun m : L => (m : ι → ℝ) j)) := by
  have hpair : Dense (AddSubgroup.closure ({(l : ι → ℝ) j, (l' : ι → ℝ) j} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  refine Dense.mono ?_ hpair
  intro y hy
  obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.1 hy
  refine ⟨p • l + q • l', ?_⟩
  show ((p • l + q • l' : L) : ι → ℝ) j = y
  rw [← hpq]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, Pi.add_apply, Pi.smul_apply]

end Irrational

/-! ## 5. Stage C, last mile, assembled -/

section Assembled

variable {L : AddSubgroup (ι → ℝ)}

/-- **Stage C, last mile on the torus.**  Let `E ⊆ (ι → ℝ) ⧸ L` be closed.  If

* its preimage accumulates at `0` on the one-dimensional coordinate set `{i}`
  (`BerendSec4.Acc`, output of Berend Lemmas 4.1–4.3),
* one family element expands on coordinate `i` and another contracts there, with
  multiplicatively independent multipliers (corrected (B3)); this is exactly the
  hypothesis of `BerendRankTwoDiag.acc_coord_subset_sub`, and
* `coord {i} + L` is dense in `ι → ℝ` (the irrational coordinate line),

then `E - E` is the whole torus. -/
theorem torus_sub_eq_univ_of_acc_coord [CompactSpace ((ι → ℝ) ⧸ L)]
    [T2Space ((ι → ℝ) ⧸ L)] {E : Set ((ι → ℝ) ⧸ L)} (hE : IsClosed E)
    {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L ⁻¹' E),
      BerendSec4.diag lam x ∈ (QuotientAddGroup.mk' L ⁻¹' E))
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L ⁻¹' E),
      BerendSec4.diag mu x ∈ (QuotientAddGroup.mk' L ⁻¹' E))
    {i : ι} (hlam : 1 < lam i) (hmu0 : 0 < mu i) (hmu1 : mu i < 1)
    (hind : ∀ m n : ℤ, lam i ^ m = mu i ^ n → m = 0 ∧ n = 0)
    (hacc : BerendSec4.Acc (QuotientAddGroup.mk' L ⁻¹' E) {i})
    (hdense : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    E - E = univ := by
  have hpre_closed : IsClosed (QuotientAddGroup.mk' L ⁻¹' E) :=
    hE.preimage QuotientAddGroup.continuous_mk
  have hcoord : (BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) ⊆
      (QuotientAddGroup.mk' L ⁻¹' E) - (QuotientAddGroup.mk' L ⁻¹' E) :=
    BerendRankTwo.acc_coord_subset_sub hpre_closed hinv1 hinv2 hlam hmu0 hmu1 hind hacc
  exact sub_eq_univ_of_dense hE hcoord hdense

/-- **Stage C, last mile, with the density discharged.**  Same as
`torus_sub_eq_univ_of_acc_coord`, with the density of `coord {i} + L` derived
from the irrational coordinate criterion in the case where `{i}` is the
complement of the single coordinate `j`. -/
theorem torus_sub_eq_univ_of_acc_coord_erase [CompactSpace ((ι → ℝ) ⧸ L)]
    [T2Space ((ι → ℝ) ⧸ L)] {E : Set ((ι → ℝ) ⧸ L)} (hE : IsClosed E)
    {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L ⁻¹' E),
      BerendSec4.diag lam x ∈ (QuotientAddGroup.mk' L ⁻¹' E))
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L ⁻¹' E),
      BerendSec4.diag mu x ∈ (QuotientAddGroup.mk' L ⁻¹' E))
    {i j : ι} (hS : ({i} : Finset ι) = Finset.univ.erase j)
    (hlam : 1 < lam i) (hmu0 : 0 < mu i) (hmu1 : mu i < 1)
    (hind : ∀ m n : ℤ, lam i ^ m = mu i ^ n → m = 0 ∧ n = 0)
    (hacc : BerendSec4.Acc (QuotientAddGroup.mk' L ⁻¹' E) {i})
    {l l' : L} (hirr : Irrational ((l : ι → ℝ) j / (l' : ι → ℝ) j)) :
    E - E = univ := by
  have hd : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ))) := by
    rw [show ({i} : Set ι) = ((Finset.univ.erase j : Finset ι) : Set ι) by
      rw [← hS, Finset.coe_singleton]]
    exact dense_coord_erase_add_of_dense_proj (dense_range_coord_of_irrational hirr)
  exact torus_sub_eq_univ_of_acc_coord hE hinv1 hinv2 hlam hmu0 hmu1 hind hacc hd

end Assembled

end BerendTorusLastMile
end CubicTwoStage
