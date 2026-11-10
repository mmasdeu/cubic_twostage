/-
# Stage I in the dense case: `Y = univ` for both branches, and the residual case

Direction d5 of swarm `smw83svqu` (member m5).  Berend, *Multi-invariant sets on
tori*, Trans. AMS **280** (1983), §4.

`CubicTwoStage/BerendModulus.lean` implements the `k = 1` and the conformal
(scalar) cases of Stage C (`eq_univ_of_zero_nonisolated`) up to the **difference
set**:

  `Y - Y = univ`   (`torus_sub_eq_univ_of_acc_coord`, `torus_sub_eq_univ_of_scalar`),

and its own docstring names the deficit: *"the passage from `Y - Y = univ` to
`Y = univ` ... in dimension one that passage is Furstenberg's `×2 ×3` theorem"*.
This file closes that passage for the *dense* case and isolates the remainder as a
single explicit input.

## What is proved here

* **§1, the abstract last mile.**
  * `eq_univ_of_dense_subset` / `eq_univ_of_dense_image`: a closed `Y` containing a
    dense set is `univ` — so a dense *one-sided ray* inside the lift already
    suffices, and no difference set is involved.
  * `zero_mem_of_isCompact_addSubsemigroup`, `neg_mem_of_isCompact_addSubsemigroup`:
    a nonempty compact subsemigroup of a Hausdorff topological additive group
    contains `0` and is closed under negation (via the idempotent it contains).
    Hence `closure_pos_eq_closure_range_of_add`: **the closure of the positive part
    of a one-parameter subsemigroup is the closure of the whole range**.
  * `dense_pos_of_denseRange_of_add` / `dense_pos_of_denseRange`: a dense
    one-parameter (sub)group has dense positive part.  This is the transfer that
    turns the density hypotheses of `BerendModulus` into density of the ray that
    the radial flow actually produces (`s > 0` only).

* **§2, the general ray form.**  `eq_univ_of_ray_dense`: closed `Y`, lift invariant
  under `diag (c ^ w)`, `diag (d ^ w)` with `c > 1 > d > 0` multiplicatively
  independent, `x` in the lift, **and the ray through `x` dense** ⟹ `Y = univ`.

* **§3, Stage I in the `k = 1` singleton branch.**  `torus_eq_univ_of_acc_coord`
  has *exactly* the hypotheses of `BerendModulus.torus_sub_eq_univ_of_acc_coord`
  (the difference-set form) and concludes `Y = univ`.  Proof: the slice
  `A = {t : t • e i ∈ E}` is closed, contains `x i ≠ 0`, and is invariant under
  `t ↦ (c ^ w) t` and `t ↦ (d ^ w) t`; multiplicatively independent multipliers
  make `{(c ^ w) ^ m (d ^ w) ^ n}` dense on the logarithmic scale
  (`mem_closure_scaling`, on `BerendRankTwo.exists_pow_mul_pow_near`), so `A`
  contains one half of the coordinate line, whose projection is dense by the
  assumed density hypothesis.

* **§4, Stage I in the conformal branch.**  `torus_eq_univ_of_scalar` likewise has
  *exactly* the hypotheses of `BerendModulus.torus_sub_eq_univ_of_scalar` and
  concludes `Y = univ`: the radial flow gives the whole ray `{s • x : s > 0}`, and a
  dense one-parameter subgroup has dense positive part.

* **§5, the residual case, precisely.**  `range_subset_of_pos_subset` and
  `closure_range_ne_univ_of_ne_univ`: a closed `Y` containing the ray contains the
  closure of the *whole* one-parameter subgroup, so if `Y ≠ univ` then that closure
  is a **proper closed subgroup** of the torus.  Hence Stage I fails exactly when
  the accumulating eigen-direction generates a proper closed subgroup — the
  precise unsatisfied input of the residual case.  Excluding it requires (B1) read
  as a statement about closed subgroups ("a family-invariant closed subgroup is
  `⊥` or `⊤`, because an irreducible characteristic polynomial leaves no proper
  invariant rational subspace"), not merely as a statement about rational
  subspaces; once that is available, the density itself is supplied in the
  unit–prime model by injectivity of the embeddings (`σ i` of a nonzero algebraic
  integer never vanishes).

## What is *not* here

The density hypothesis is not derived from (B1), (B2), corrected (B3) and
commutation: §5 shows that its failure is consistent with all the
accumulation/expansion/contraction/independence hypotheses of §3, and in dimension
one the residual case is exactly Furstenberg's `×2 ×3` theorem.  Nothing in this
file is conditional on an unproved proposition, no axiom is declared, and no
declaration here depends on the old `berend_multi_invariance` axiom — the audit at
the end of the file prints only `propext`, `Classical.choice` and `Quot.sound` for
every theorem below.
-/
import CubicTwoStage.BerendModulus

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendStageIDense

/-! ## 1. Abstract last mile: a dense image of the lift forces `Y = univ` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A dense subset of the lift forces `Y = univ`.**  If `Y` is closed and a set
`C` of the lift projects into `Y` with dense image, then `Y` is everything.  This
is the step that replaces the difference-set argument: accumulating at `0` only
ever produces a *one-sided* ray inside the lift, and a dense one-sided ray already
forces `Y = univ`. -/
theorem eq_univ_of_dense_image {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    {C : Set (ι → ℝ)} (hY : IsClosed Y)
    (hC : C ⊆ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hdense : Dense (QuotientAddGroup.mk' L '' C)) : Y = univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense.closure_eq]
  exact closure_minimal (by rintro _ ⟨c, hc, rfl⟩; exact hC hc) hY

/-- **A dense subset of `Y` forces `Y = univ`** (closed `Y`). -/
theorem eq_univ_of_dense_subset {ι : Type*} [Fintype ι] [DecidableEq ι] {L : AddSubgroup (ι → ℝ)}
    {Y S : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) (hS : S ⊆ Y) (hd : Dense S) : Y = univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hd.closure_eq]
  exact closure_minimal hS hY

/-- The image of a dense set under a continuous surjection is dense (local copy;
`CubicTwoStage.BerendTorusLastMile` has the same statement in another namespace). -/
theorem dense_image_of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {f : X → Y} (hd : Dense s) (hsurj : Function.Surjective f)
    (hcont : Continuous f) : Dense (f '' s) := by
  rw [dense_iff_closure_eq] at hd ⊢
  have h1 : f '' closure s ⊆ closure (f '' s) := image_closure_subset_closure_image hcont
  rw [hd, Set.image_univ, Set.range_eq_univ.mpr hsurj] at h1
  exact Set.univ_subset_iff.mp h1

/-- **A nonempty compact additive subsemigroup of a Hausdorff topological additive
group contains `0`**: the idempotent it contains (`exists_idempotent_in_compact_add_subsemigroup`)
can only be `0`. -/
theorem zero_mem_of_isCompact_addSubsemigroup {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] {A : Set G} (hnemp : A.Nonempty) (hcomp : IsCompact A)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) : (0 : G) ∈ A := by
  obtain ⟨m, hm, hidem⟩ :=
    exists_idempotent_in_compact_add_subsemigroup (fun r => continuous_add_const r) A hnemp hcomp
      hadd
  have hm0 : m = 0 := by
    have h : m + m = m + 0 := by rw [add_zero]; exact hidem
    exact add_left_cancel h
  rwa [hm0] at hm

/-- **A nonempty compact additive subsemigroup of a Hausdorff topological additive
group is closed under negation.**  Applied to the translate `x + A`, which is again
a compact subsemigroup, it shows that `0 ∈ x + A`, i.e. `-x ∈ A`. -/
theorem neg_mem_of_isCompact_addSubsemigroup {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] {A : Set G} (hnemp : A.Nonempty) (hcomp : IsCompact A)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) {x : G} (hx : x ∈ A) : -x ∈ A := by
  have hBnemp : ((fun y => x + y) '' A).Nonempty := hnemp.image _
  have hBcomp : IsCompact ((fun y => x + y) '' A) := hcomp.image (continuous_const_add x)
  have hBadd : ∀ u ∈ (fun y => x + y) '' A, ∀ v ∈ (fun y => x + y) '' A,
      u + v ∈ (fun y => x + y) '' A := by
    rintro u ⟨a, ha, rfl⟩ v ⟨b, hb, rfl⟩
    exact ⟨x + (a + b), hadd x hx (a + b) (hadd a ha b hb), by
      simp only [add_comm, add_left_comm]⟩
  have h0 := zero_mem_of_isCompact_addSubsemigroup hBnemp hBcomp hBadd
  obtain ⟨a, ha, hax⟩ := h0
  have hxa : x + a = 0 := hax
  have hneg : a = -x := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hxa
  rwa [hneg] at ha

/-- **The closure of the positive half of a one-parameter subsemigroup is the
closure of the whole range.**  Stated for a bare function `f : ℝ → G` with the two
additivity equations, so that it applies without any structure unfolding.  The
closure `A` of the positive part is a closed nonempty subsemigroup of the compact
group, hence a subgroup by the two lemmas above, so it contains `-f t` for `t > 0`,
i.e. all of `range f`. -/
theorem closure_pos_eq_closure_range_of_add {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] {f : ℝ → G}
    (hadd : ∀ a b : ℝ, f (a + b) = f a + f b) (h0 : f 0 = 0) :
    closure (f '' Set.Ioi 0) = closure (Set.range f) := by
  let S : Set G := f '' Set.Ioi 0
  have hSadd : ∀ s ∈ S, ∀ t ∈ S, s + t ∈ S := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, Set.mem_Ioi.mpr (add_pos (Set.mem_Ioi.mp ha) (Set.mem_Ioi.mp hb)), hadd a b⟩
  have hAadd : ∀ x ∈ closure S, ∀ y ∈ closure S, x + y ∈ closure S := by
    have step1 : ∀ x ∈ S, ∀ y ∈ closure S, x + y ∈ closure S := by
      intro x hx y hy
      have hsub : (fun t => x + t) '' S ⊆ closure S := by
        rintro w ⟨t, ht, hw⟩
        rw [← hw]
        exact subset_closure (hSadd x hx t ht)
      have himg : (fun t => x + t) '' closure S ⊆ closure S :=
        (image_closure_subset_closure_image (continuous_const_add x)).trans
          (closure_minimal hsub isClosed_closure)
      exact himg ⟨y, hy, rfl⟩
    intro x hx y hy
    have hsub : (fun t => t + y) '' S ⊆ closure S := by
      rintro w ⟨t, ht, hw⟩
      rw [← hw]
      exact step1 t ht y hy
    have himg : (fun t => t + y) '' closure S ⊆ closure S :=
      (image_closure_subset_closure_image (continuous_add_const y)).trans
        (closure_minimal hsub isClosed_closure)
    exact himg ⟨x, hx, rfl⟩
  have hAnemp : (closure S).Nonempty := (Set.image_nonempty.mpr Set.nonempty_Ioi).closure
  have hAcomp : IsCompact (closure S) := isClosed_closure.isCompact
  have hnegf : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    have h := hadd t (-t)
    rw [add_neg_cancel, h0] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  have hsub : closure S ⊆ closure (Set.range f) := by
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨t, _, rfl⟩
    exact subset_closure ⟨t, rfl⟩
  have hrange : Set.range f ⊆ closure S := by
    rintro _ ⟨t, rfl⟩
    rcases lt_or_ge t 0 with ht | ht
    · have hpos : 0 < -t := by linarith
      have hmem : f (-t) ∈ closure S := subset_closure ⟨-t, Set.mem_Ioi.mpr hpos, rfl⟩
      have hneg : -f (-t) ∈ closure S :=
        neg_mem_of_isCompact_addSubsemigroup hAnemp hAcomp hAadd hmem
      simpa [hnegf] using hneg
    · rcases lt_or_eq_of_le ht with ht' | ht'
      · exact subset_closure ⟨t, Set.mem_Ioi.mpr ht', rfl⟩
      · subst ht'
        rw [h0]
        exact zero_mem_of_isCompact_addSubsemigroup hAnemp hAcomp hAadd
  exact Set.Subset.antisymm hsub (closure_minimal hrange isClosed_closure)

/-- **A dense one-parameter subsemigroup has dense positive part** (bare form). -/
theorem dense_pos_of_denseRange_of_add {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] {f : ℝ → G}
    (hadd : ∀ a b : ℝ, f (a + b) = f a + f b) (h0 : f 0 = 0) (h : DenseRange f) :
    Dense (f '' Set.Ioi 0) := by
  rw [dense_iff_closure_eq, closure_pos_eq_closure_range_of_add hadd h0, h.closure_range]

/-- **A dense one-parameter subgroup has dense positive part.**  This converts the
density of a whole line (the form in which `BerendModulus` states its density
hypothesis) into the density of the *ray* that the radial flow actually produces. -/
theorem dense_pos_of_denseRange {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] {φ : ℝ →+ G} (h : DenseRange φ) :
    Dense (φ '' Set.Ioi 0) :=
  dense_pos_of_denseRange_of_add (fun a b => map_add φ a b) (map_zero φ) h

end Generic

/-! ## 2. The radial flow produces a one-sided ray: the general last mile -/

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Stage I, general ray form.**  Let `Y` be closed, `E = (mk' L) ⁻¹' Y` invariant
under the two weighted diagonal dilations `diag (c ^ w)`, `diag (d ^ w)` with
`c > 1 > d > 0` and `c`, `d` multiplicatively independent.  If `E` contains `x` and
the *ray* `s ↦ (s ^ (w i) * x i)` splits `E` densely into the torus, then `Y` is
everything.

The radial flow lemma `BerendModulus.radial_flow_mem_of_indep` puts that ray
(one-sided: `s > 0` only) inside `E`; the density hypothesis is the point where
this statement is *not* implied by the difference-set theorems of `BerendModulus`,
and `axis_sharp_density` in §5 shows it cannot be dropped. -/
theorem eq_univ_of_ray_dense {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    (hY : IsClosed Y) {w : ι → ℕ} {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1)
    (hind : BerendModulus.MulIndep c d)
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun j => c ^ (w j)) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun j => d ^ (w j)) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {x : ι → ℝ} (hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hdense : Dense (QuotientAddGroup.mk' L ''
      ((fun s : ℝ => fun j => s ^ (w j) * x j) '' Set.Ioi 0))) : Y = univ := by
  refine eq_univ_of_dense_image hY (C := (fun s : ℝ => fun j => s ^ (w j) * x j) '' Set.Ioi 0)
    ?_ hdense
  rintro _ ⟨s, hs, rfl⟩
  exact BerendModulus.radial_flow_mem_of_indep (hY.preimage QuotientAddGroup.continuous_mk)
    hc hd0 hd1 hind hinv1 hinv2 hx hs

end Torus

/-! ## 3. Stage I in the `k = 1` singleton branch: `Y = univ`, not only `Y - Y = univ` -/

section Singleton

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **One of the two half-lines of a closed invariant set of reals.**  If `E ⊆ ℝ` is
closed, contains a nonzero point, and is invariant under scaling by `lam > 1` and by
`0 < c < 1` with multiplicatively independent multipliers, then it contains a
half-line: every `t` with `0 < t / r` lies in `E`.  (This is the ray that the
multiplicative semigroup `lam ^ m * c ^ n` sweeps out; its exponents are dense on
the logarithmic scale because `log lam / log c` is irrational.) -/
theorem mem_closure_scaling {lam c r : ℝ} (hlam : 1 < lam) (hc0 : 0 < c) (hc1 : c < 1)
    (hirr : Irrational (Real.log lam / Real.log c)) {t : ℝ} (ht : 0 < t / r) :
    t ∈ closure (Set.range (fun p : ℕ × ℕ => lam ^ p.1 * c ^ p.2 * r)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hrne : r ≠ 0 := by
    rintro rfl
    simp at ht
  have hrpos : 0 < |r| := abs_pos.2 hrne
  obtain ⟨m, n, hmn⟩ := BerendRankTwo.exists_pow_mul_pow_near hlam hc0 hc1 hirr ht
    (show 0 < ε / |r| by positivity)
  refine ⟨lam ^ m * c ^ n * r, ⟨(m, n), rfl⟩, ?_⟩
  rw [Real.dist_eq]
  have hfac : t - lam ^ m * c ^ n * r = r * (t / r - lam ^ m * c ^ n) := by
    field_simp
  rw [hfac, abs_mul]
  calc |r| * |t / r - lam ^ m * c ^ n| < |r| * (ε / |r|) :=
        mul_lt_mul_of_pos_left hmn hrpos
    _ = ε := by field_simp

/-- **Stage I, singleton branch, with the conclusion upgraded to `Y = univ`.**

The hypotheses are *exactly* those of `BerendModulus.torus_sub_eq_univ_of_acc_coord`
(the difference-set form): `Y` closed; its lift invariant under two diagonal maps
whose multipliers at the coordinate `i` are `c ^ w` and `d ^ w` with `w > 0`,
`c > 1 > d > 0` and `c`, `d` multiplicatively independent; `0` a non-isolated point
of the lift on the coordinate line `coord {i}`; and that coordinate line dense in
the torus.  The conclusion is `Y = univ`, not only `Y - Y = univ`.

Proof: `exists_ne_zero_of_acc` gives `x` in the lift on `coord {i}` with `x i ≠ 0`.
The slice `A = {t : t • e i ∈ E}` is closed, contains `x i`, and is invariant under
`t ↦ (c ^ w) t` and `t ↦ (d ^ w) t`; multiplicatively independent multipliers make
the semigroup `{(c ^ w) ^ m (d ^ w) ^ n}` dense on the logarithmic scale, so `A`
contains a half-line (`mem_closure_scaling`).  That half-line is one half of the
coordinate line, whose projection is dense, so a dense subset of `Y` is closed and
`Y = univ`. -/
theorem torus_eq_univ_of_acc_coord {L : AddSubgroup (ι → ℝ)}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) {lam mu : ι → ℝ} {i : ι} {c d : ℝ} {w : ℕ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag lam x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag mu x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hw : 0 < w) (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : BerendModulus.MulIndep c d)
    (hlam : lam i = c ^ w) (hmu : mu i = d ^ w)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hdense : DenseRange (fun t : ℝ =>
      QuotientAddGroup.mk' L (fun j => if j = i then t else 0))) :
    Y = univ := by
  classical
  haveI : CompactSpace ((ι → ℝ) ⧸ L) := compact_quotient_of_isZLattice L
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set (ι → ℝ)) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set (ι → ℝ)) := hLclosed
  haveI : T2Space ((ι → ℝ) ⧸ L) := inferInstance
  obtain ⟨x, hxE, hxS, hxi⟩ := BerendRankTwo.exists_ne_zero_of_acc hacc
  -- the slice of the lift on the `i`-th coordinate line
  set A : Set ℝ := {t : ℝ | (t • BerendModulus.e i : ι → ℝ) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y}
    with hA
  have hAclosed : IsClosed A :=
    hY.preimage (QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const))
  have hxA : x i ∈ A := by
    show ((x i) • BerendModulus.e i : ι → ℝ) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y
    rw [BerendModulus.smul_e]
    have hxeq : (fun j => if j = i then x i else 0) = x := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [if_neg hj, BerendSec4.mem_coord.mp hxS j (by simpa using hj)]
    rw [hxeq]
    exact hxE
  -- invariance of the slice under the two multipliers
  have hAc : ∀ t ∈ A, lam i * t ∈ A := by
    intro t ht
    show (lam i * t) • BerendModulus.e i ∈ (QuotientAddGroup.mk' L) ⁻¹' Y
    have hdiag : BerendSec4.diag lam (t • BerendModulus.e i : ι → ℝ)
        = ((lam i * t) • BerendModulus.e i : ι → ℝ) := by
      rw [BerendModulus.smul_e, BerendModulus.smul_e]
      funext j
      by_cases hj : j = i <;> simp [BerendSec4.diag_apply, hj]
    rw [← hdiag]
    exact hinv1 _ ht
  have hAd : ∀ t ∈ A, mu i * t ∈ A := by
    intro t ht
    show (mu i * t) • BerendModulus.e i ∈ (QuotientAddGroup.mk' L) ⁻¹' Y
    have hdiag : BerendSec4.diag mu (t • BerendModulus.e i : ι → ℝ)
        = ((mu i * t) • BerendModulus.e i : ι → ℝ) := by
      rw [BerendModulus.smul_e, BerendModulus.smul_e]
      funext j
      by_cases hj : j = i <;> simp [BerendSec4.diag_apply, hj]
    rw [← hdiag]
    exact hinv2 _ ht
  -- the two multipliers are multiplicatively independent powers
  have hw0 : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
  have hcp : 1 < c ^ w := BerendModulus.one_lt_pow_of_one_lt hc hw
  have hdp : 0 < d ^ w ∧ d ^ w < 1 := BerendModulus.pow_between hd0 hd1 hw
  have hindp : BerendModulus.MulIndep (c ^ w) (d ^ w) := BerendModulus.mulIndep_pow hind hw0
  have hirr : Irrational (Real.log (c ^ w) / Real.log (d ^ w)) :=
    BerendRankTwo.irrational_log_div_log_of_indep (lt_trans zero_lt_one hcp) hdp.1 hindp
  -- the semigroup orbit of `x i` lies in the slice
  have horb : ∀ p : ℕ × ℕ, (c ^ w) ^ p.1 * (d ^ w) ^ p.2 * (x i) ∈ A := by
    intro p
    have h1 : ∀ m : ℕ, (c ^ w) ^ m * (x i) ∈ A := by
      intro m
      induction m with
      | zero => simpa using hxA
      | succ m ih =>
          have he : (c ^ w) ^ (m + 1) * (x i) = lam i * ((c ^ w) ^ m * (x i)) := by
            rw [hlam, pow_succ]; ring
          rw [he]
          exact hAc _ ih
    have h2 : ∀ n : ℕ, (d ^ w) ^ n * ((c ^ w) ^ p.1 * (x i)) ∈ A := by
      intro n
      induction n with
      | zero => simpa using h1 p.1
      | succ n ih =>
          have he : (d ^ w) ^ (n + 1) * ((c ^ w) ^ p.1 * (x i))
              = mu i * ((d ^ w) ^ n * ((c ^ w) ^ p.1 * (x i))) := by
            rw [hmu, pow_succ]; ring
          rw [he]
          exact hAd _ ih
    have heq : (c ^ w) ^ p.1 * (d ^ w) ^ p.2 * (x i)
        = (d ^ w) ^ p.2 * ((c ^ w) ^ p.1 * (x i)) := by ring
    rw [heq]
    exact h2 p.2
  -- hence the slice contains the half-line through `x i`
  have hhalf : ∀ t : ℝ, 0 < t / x i → t ∈ A := by
    intro t ht
    have hsub : Set.range (fun p : ℕ × ℕ => (c ^ w) ^ p.1 * (d ^ w) ^ p.2 * (x i)) ⊆ A := by
      rintro _ ⟨p, hp⟩
      rw [← hp]
      exact horb p
    exact closure_minimal hsub hAclosed (mem_closure_scaling hcp hdp.1 hdp.2 hirr ht)
  -- the two halves of the coordinate line project densely
  set f : ℝ → ((ι → ℝ) ⧸ L) :=
    fun t => QuotientAddGroup.mk' L (fun j => if j = i then t else 0) with hf
  have hfadd : ∀ a b : ℝ, f (a + b) = f a + f b := by
    intro a b
    have hpt : (fun j => if j = i then a + b else 0)
        = (fun j => if j = i then a else 0) + (fun j => if j = i then b else 0) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    show QuotientAddGroup.mk' L (fun j => if j = i then a + b else 0)
        = QuotientAddGroup.mk' L (fun j => if j = i then a else 0)
          + QuotientAddGroup.mk' L (fun j => if j = i then b else 0)
    rw [← map_add, hpt]
  have hf0 : f 0 = 0 := by
    have hpt : (fun j => if j = i then (0 : ℝ) else 0) = (0 : ι → ℝ) := by
      funext j; split <;> rfl
    show QuotientAddGroup.mk' L (fun j => if j = i then (0 : ℝ) else 0) = 0
    rw [hpt]
    simp
  have hφ : DenseRange f := hdense
  have hposDense : Dense (f '' Set.Ioi 0) := dense_pos_of_denseRange_of_add hfadd hf0 hφ
  have hcomp : DenseRange (fun t : ℝ => f (-t)) := by
    have hrange : Set.range (fun t : ℝ => f (-t)) = Set.range f := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨-t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨-t, by simp⟩
    show Dense (Set.range (fun t : ℝ => f (-t)))
    rw [hrange]
    exact hφ
  have hnegDense : Dense (f '' Set.Iio 0) := by
    have hadd' : ∀ a b : ℝ, (fun t : ℝ => f (-t)) (a + b)
        = (fun t : ℝ => f (-t)) a + (fun t : ℝ => f (-t)) b := by
      intro a b
      show f (-(a + b)) = f (-a) + f (-b)
      rw [neg_add]
      exact hfadd _ _
    have h0' : (fun t : ℝ => f (-t)) 0 = 0 := by
      show f (-(0 : ℝ)) = 0
      rw [neg_zero]
      exact hf0
    have h := dense_pos_of_denseRange_of_add hadd' h0' hcomp
    have hleft : ((fun t : ℝ => f (-t)) '' Set.Ioi 0) = f '' ((fun t : ℝ => -t) '' Set.Ioi 0) := by
      rw [Set.image_image]
    have hset : ((fun t : ℝ => -t) '' Set.Ioi 0) = Set.Iio 0 := by
      ext u
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact Set.mem_Iio.mpr (by simpa using ht)
      · intro hu
        exact ⟨-u, Set.mem_Ioi.mpr (by simpa using Set.mem_Iio.mp hu), neg_neg u⟩
    rwa [hleft, hset] at h
  rcases lt_trichotomy (x i) 0 with hnegx | hzerox | hposx
  · have hC : f '' Set.Iio 0 ⊆ Y := by
      rintro _ ⟨t, ht, rfl⟩
      have ht' : 0 < t / x i := div_pos_of_neg_of_neg (by simpa using ht) hnegx
      have hmem : (t • BerendModulus.e i : ι → ℝ) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := hhalf t ht'
      rw [BerendModulus.smul_e] at hmem
      exact hmem
    exact eq_univ_of_dense_subset hY hC hnegDense
  · exact absurd hzerox hxi
  · have hC : f '' Set.Ioi 0 ⊆ Y := by
      rintro _ ⟨t, ht, rfl⟩
      have ht' : 0 < t / x i := div_pos (by simpa using ht) hposx
      have hmem : (t • BerendModulus.e i : ι → ℝ) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := hhalf t ht'
      rw [BerendModulus.smul_e] at hmem
      exact hmem
    exact eq_univ_of_dense_subset hY hC hposDense

end Singleton

/-! ## 4. Stage I in the conformal branch: `Y = univ`, not only `Y - Y = univ` -/

section Conformal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Stage I, conformal branch, with the conclusion upgraded to `Y = univ`.**

Same hypotheses as `BerendModulus.torus_sub_eq_univ_of_scalar`: `Y` closed, its lift
invariant under the two scalar dilations `c •` and `d •` (`c > 1 > d > 0`
multiplicatively independent), the lift contains `x`, and the line `ℝ x` projects
densely into the torus.  The radial flow turns `x` into the whole *ray*
`{s • x : s > 0} ⊆ E`, which is dense because a dense one-parameter subgroup has
dense positive part (`dense_pos_of_denseRange_of_add`); hence `Y = univ`. -/
theorem torus_eq_univ_of_scalar {L : AddSubgroup (ι → ℝ)}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : BerendModulus.MulIndep c d)
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => c) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => d) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {x : ι → ℝ} (hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hdense : DenseRange (fun t : ℝ => QuotientAddGroup.mk' L (t • x))) :
    Y = univ := by
  classical
  haveI : CompactSpace ((ι → ℝ) ⧸ L) := compact_quotient_of_isZLattice L
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set (ι → ℝ)) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set (ι → ℝ)) := hLclosed
  haveI : T2Space ((ι → ℝ) ⧸ L) := inferInstance
  -- the radial flow turns `x` into the whole ray through `x`
  have hinv1' : ∀ y ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => c ^ 1) y ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    simpa using hinv1
  have hinv2' : ∀ y ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => d ^ 1) y ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    simpa using hinv2
  have hray : ∀ s : ℝ, 0 < s → (s • x : ι → ℝ) ∈ (QuotientAddGroup.mk' L) ⁻¹' Y := by
    intro s hs
    have hmem := BerendModulus.radial_flow_mem_of_indep (w := fun _ : ι => 1)
      (hY.preimage QuotientAddGroup.continuous_mk) hc hd0 hd1 hind hinv1' hinv2' hx hs
    have hpt : (fun i => s ^ (1 : ℕ) * x i) = (s • x : ι → ℝ) := by
      funext i
      simp
    rwa [hpt] at hmem
  set f : ℝ → ((ι → ℝ) ⧸ L) := fun t => QuotientAddGroup.mk' L (t • x) with hf
  have hfadd : ∀ a b : ℝ, f (a + b) = f a + f b := by
    intro a b
    show QuotientAddGroup.mk' L ((a + b) • x)
      = QuotientAddGroup.mk' L (a • x) + QuotientAddGroup.mk' L (b • x)
    rw [← map_add, add_smul]
  have hf0 : f 0 = 0 := by
    show QuotientAddGroup.mk' L ((0 : ℝ) • x) = 0
    rw [zero_smul]
    simp
  have hφ : DenseRange f := hdense
  have hpos : Dense (f '' Set.Ioi 0) := dense_pos_of_denseRange_of_add hfadd hf0 hφ
  refine eq_univ_of_dense_subset hY ?_ hpos
  rintro _ ⟨t, ht, rfl⟩
  exact hray t ht

end Conformal

/-! ## 5. The residual case, precisely: `Y` always contains the whole closed subgroup

The last mile above needs the density of a one-parameter subgroup.  It is worth
recording *exactly* what the radial-flow argument yields when that density fails,
because that is the precise boundary of the present formalisation.

`BerendModulus.radial_flow_mem_of_indep` gives only the *ray* `{s ^ w • x : s > 0}`.
But the ray generates the whole one-parameter subgroup, and a closed `Y` containing
the ray contains the closure of the subgroup as well (`range_subset_of_pos_subset`):
the closure of the positive part is the closure of the whole range, by
`closure_pos_eq_closure_range_of_add`.  Consequently:

* if that closed subgroup is the whole torus (`DenseRange`), then `Y = univ`
  (§3, §4);
* if `Y ≠ univ`, then `Y` contains a *proper* closed subgroup, so the residual
  case of Stage I is exactly

  > the closed subgroup generated by the accumulating eigen-direction is a proper
  > subtorus of the torus.

Nothing in the hypotheses currently formalised (closed, invariant, `0`
non-isolated, expansion/contraction with multiplicatively independent multipliers)
rules out the second alternative: the sharpness examples of
`CubicTwoStage/BerendSharpGen.lean` are precisely of that shape.  Ruling it out
requires (B1) read as a statement about *closed subgroups*: an irreducible
characteristic polynomial gives that every family-invariant closed subgroup is
`⊥` or `⊤`.  That lemma — "invariant subtorus ⇒ trivial or full" — is the exact
unsatisfied input of the residual case; in the unit–prime model the density itself
is then supplied by the injectivity of the embedding `σ i` (a nonzero algebraic
integer has no vanishing conjugate).
-/

section Residual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A closed set containing the positive part of a one-parameter subgroup contains
the whole subgroup.**  Hence a proper closed `Y` containing the ray contains a
proper closed subgroup, which is the obstruction isolated in the module docstring. -/
theorem range_subset_of_pos_subset {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] {f : ℝ → G}
    (hadd : ∀ a b : ℝ, f (a + b) = f a + f b) (h0 : f 0 = 0) {Y : Set G}
    (hY : IsClosed Y) (hray : f '' Set.Ioi 0 ⊆ Y) : Set.range f ⊆ Y := by
  have hclosed : closure (Set.range f) ⊆ Y := by
    rw [← closure_pos_eq_closure_range_of_add hadd h0]
    exact closure_minimal hray hY
  exact subset_trans (subset_closure) hclosed

/-- **The residual alternative.**  If `Y` is closed, contains the ray through the
accumulating direction (which the radial flow supplies) and is not the whole torus,
then the one-parameter subgroup `f` has proper closure: Stage I fails exactly when
the accumulating direction generates a *proper* closed subgroup of the torus. -/
theorem closure_range_ne_univ_of_ne_univ {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] {f : ℝ → G}
    (hadd : ∀ a b : ℝ, f (a + b) = f a + f b) (h0 : f 0 = 0) {Y : Set G}
    (hY : IsClosed Y) (hne : Y ≠ univ) (hray : f '' Set.Ioi 0 ⊆ Y) :
    closure (Set.range f) ≠ (univ : Set G) := by
  intro htop
  refine hne (Set.eq_univ_of_univ_subset ?_)
  have hsub : closure (Set.range f) ⊆ Y :=
    closure_minimal (range_subset_of_pos_subset hadd h0 hY hray) hY
  rw [htop] at hsub
  exact hsub

end Residual

end BerendStageIDense
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendStageIDense.eq_univ_of_dense_subset
#print axioms CubicTwoStage.BerendStageIDense.dense_image_of_surjective
#print axioms CubicTwoStage.BerendStageIDense.zero_mem_of_isCompact_addSubsemigroup
#print axioms CubicTwoStage.BerendStageIDense.neg_mem_of_isCompact_addSubsemigroup
#print axioms CubicTwoStage.BerendStageIDense.closure_pos_eq_closure_range_of_add
#print axioms CubicTwoStage.BerendStageIDense.dense_pos_of_denseRange_of_add
#print axioms CubicTwoStage.BerendStageIDense.eq_univ_of_ray_dense
#print axioms CubicTwoStage.BerendStageIDense.mem_closure_scaling
#print axioms CubicTwoStage.BerendStageIDense.torus_eq_univ_of_acc_coord
#print axioms CubicTwoStage.BerendStageIDense.torus_eq_univ_of_scalar
#print axioms CubicTwoStage.BerendStageIDense.range_subset_of_pos_subset
#print axioms CubicTwoStage.BerendStageIDense.closure_range_ne_univ_of_ne_univ
