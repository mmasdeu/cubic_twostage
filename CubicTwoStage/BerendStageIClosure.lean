/-
# Stage I: the exact residual is local fullness at the origin

`BEREND_PROOF_PLAN.md` §C isolates Stage I of Berend's Theorem 2.1
(D. Berend, *Multi-invariant sets on tori*, Trans. AMS **280** (1983), §4):

> a closed family-invariant `E` with `0` as a *non-isolated* point is everything.

The integrated modules of the project now supply, unconditionally and axiom
free, the whole §4 toolkit on the diagonalized model `ι → ℝ`:

* `BerendSec4` — Lemma 4.1 (every invariant subspace is a coordinate subspace)
  and Lemma 4.2 (the expanding/nonexpanding dichotomy on a minimal accumulating
  coordinate set);
* `BerendFullCone` — points of `E` in the full cone over the minimal set, at
  every scale;
* `BerendOrbit` — Lemma 4.3, the backward orbit and `supp (w 0) = S`;
* `BerendRate` — Lemma 4.4, proportional logarithmic growth rates;
* `BerendModulus` — `radial_flow` (proportional rates integrate to the whole
  positive radial flow), and the two torus projection theorems
  (`torus_sub_eq_univ_of_acc_coord`, `torus_sub_eq_univ_of_scalar`);
* `BerendTorusLastMile` — the density of `coord {i} + L` in the lift, and the
  transfer of the difference-set statements to `Y - Y`;
* `BerendRankTwoDiag`, `BerendRankTwo` — the one-dimensional `×2 ×3` step.

**What those theorems conclude is a difference-set statement**, `Y - Y = univ`.
What Stage I needs is `Y = univ`. The gap between the two is not bookkeeping, and
this file does two things about it.

## 1. The gap is exactly *local fullness*, and the last step is unconditional

`LocalFull lam` below says: the lift `E` of the invariant set contains a
coordinate box around `0`. The main structural theorem of this file is

  `zeroNonisolatedFull_iff_localFull`,

i.e. **Stage I for a diagonal family is equivalent to local fullness at `0`**,
*provided* the family contains one member whose multipliers are all `> 1` by a
uniform factor (`1 < m ≤ lam i₀ k`). The non-trivial direction is a genuine
one-line-at-the-limit argument: from a box of radius `r` inside `E`, iterating
the expanding diagonal map produces boxes of radius `r * m ^ k`, whose union is
all of `ι → ℝ` (`eq_univ_of_closedBox_subset`). So the *last* step of §4 needs
no rigidity at all; the whole rigidity content of Stage I is concentrated in
`LocalFull`.

This is a real sharpening: it says that any proof of §4 may be replaced, with no
loss, by a proof that the accumulation is *locally full*, and that no further
work on expansion, cones or the torus projection is needed afterwards.

## 2. Why the integrated difference-set theorems do not give `LocalFull`

`BerendRankTwo.sub_eq_univ_of_invariant` — the accepted one-dimensional
`×2 ×3` step, and the arithmetic core of `BerendModulus` — concludes `E - E = ℝ`
from "`E` is closed, invariant under `x ↦ λx` (`λ > 1`) and `x ↦ cx`
(`0 < c < 1`) and contains a nonzero point". Its proof actually produces more:
the whole **half-line** through that point lies in `E`.

`sharpness_halfLine` below is the exact witness that this is not enough: the
half-line `[0, ∞)` is closed, is invariant under `x ↦ 2x` and `x ↦ x / 3`,
contains `0` as a non-isolated point, has `E - E = ℝ`, and yet is neither
everything nor locally full at `0`. So no amount of extra bookkeeping on
difference sets upgrades §C.5 to Stage I: the missing input is the *lattice
saturation* `E + L = E` together with the density of the coordinate line, which
`BerendTorusLastMile` supplies, **plus** the Furstenberg-type density of the
directions of `E` that makes the half-line's projection wrap around. That last
statement is the genuinely deep input of §4 and is *not* available in the
current toolkit; this file states it exactly rather than assuming it.

## 3. Assembly (plan §E, item (4))

`berendMultiInvarianceCorrected_of_stageI_of_residual` feeds Stage I, at the
project's own torus `Pt ⧸ L`, into `BerendDichotomy.dichotomy_of_noProperFullDiffSet`
and produces `BerendMultiInvarianceCorrected` with the *single* remaining input
`NoProperFullDiffSet` (amended plan §D.5, the later propagation step). It uses no
axiom, makes no new assumption, and its hypotheses are printed.

## Trust

No `axiom`, no `sorry`, no assumed `Prop`; `#print axioms` at the end reports
`propext`, `Classical.choice`, `Quot.sound` for every declaration.
-/
import CubicTwoStage.BerendModulus
import CubicTwoStage.BerendDichotomy

open Set Filter Topology
open scoped Pointwise TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendStageIClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Coordinate boxes and the last step of Stage I -/

/-- The open coordinate box of radius `r` around the origin in `ι → ℝ`. -/
def box (r : ℝ) : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Ioo (-r) r)

/-- The closed coordinate box of radius `r` around the origin in `ι → ℝ`. -/
def closedBox (r : ℝ) : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Icc (-r) r)

theorem mem_box_iff {r : ℝ} {x : ι → ℝ} : x ∈ box r ↔ ∀ i, x i ∈ Set.Ioo (-r) r := by
  rw [box, Set.mem_pi]
  simp

theorem mem_closedBox_iff {r : ℝ} {x : ι → ℝ} :
    x ∈ closedBox r ↔ ∀ i, x i ∈ Set.Icc (-r) r := by
  rw [closedBox, Set.mem_pi]
  simp

theorem zero_mem_box {r : ℝ} (hr : 0 < r) : (0 : ι → ℝ) ∈ box (ι := ι) r := by
  rw [mem_box_iff]
  intro i
  refine Set.mem_Ioo.2 ⟨?_, ?_⟩
  · simpa using hr
  · simpa using hr

theorem isOpen_box (r : ℝ) : IsOpen (box (ι := ι) r) := by
  rw [box]
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioo

/-- The open coordinate boxes form a neighbourhood basis of `0` in `ι → ℝ`. -/
theorem exists_box_subset_of_mem_nhds {W : Set (ι → ℝ)} (hW : W ∈ 𝓝 (0 : ι → ℝ)) :
    ∃ r : ℝ, 0 < r ∧ box r ⊆ W := by
  classical
  rw [mem_nhds_iff] at hW
  obtain ⟨O, hOW, hOopen, h0O⟩ := hW
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hOopen 0 h0O
  simp only [Pi.zero_apply] at hu
  -- each `u a` (`a ∈ I`) is an open neighbourhood of `0`
  have hru : ∀ a : ι, ∃ r : ℝ, (a ∈ I → 0 < r) ∧ (a ∈ I → Set.Ioo (-r) r ⊆ u a) := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨l, u', hmem, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.1
        (IsOpen.mem_nhds (hu a ha).1 (hu a ha).2)
      obtain ⟨h1, h2⟩ := hmem
      refine ⟨min (-l) u', fun _ => lt_min (by linarith) h2, fun _ => ?_⟩
      intro t ht
      rw [Set.mem_Ioo] at ht
      exact hsub' (Set.mem_Ioo.2 ⟨by
        have := min_le_left (-l) u'
        linarith, by
        have := min_le_right (-l) u'
        linarith⟩)
    · exact ⟨1, fun h => absurd h ha, fun h => absurd h ha⟩
  choose r hr0 hrsub using hru
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · -- no constraints: any positive radius works
    refine ⟨1, one_pos, ?_⟩
    intro x _
    refine hOW (hsub ?_)
    rw [Set.mem_pi]
    intro a ha
    exact absurd ha (by simp)
  · refine ⟨I.inf' hIne r, ?_, ?_⟩
    · exact Finset.lt_inf'_iff hIne |>.2 (fun b hb => hr0 b hb)
    · intro x hx
      rw [mem_box_iff] at hx
      refine hOW (hsub ?_)
      rw [Set.mem_pi]
      intro a ha
      refine hrsub a ha ?_
      rw [Set.mem_Ioo]
      exact ⟨by linarith [(hx a).1, Finset.inf'_le r ha],
        by linarith [(hx a).2, Finset.inf'_le r ha]⟩

theorem closedBox_mono {r r' : ℝ} (h : r' ≤ r) :
    closedBox (ι := ι) r' ⊆ closedBox (ι := ι) r := by
  intro x hx
  rw [mem_closedBox_iff] at hx ⊢
  intro i
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

/-- **A diagonal dilation by at least `m` in every coordinate grows the closed box
by the factor `m`.**  This is the elementary engine behind the last step of
Stage I. -/
theorem closedBox_subset_diag_image {lam : ι → ℝ} {m r : ℝ} (hm0 : 0 < m)
    (hm : ∀ i, m ≤ lam i) (hr : 0 ≤ r) :
    closedBox (r * m) ⊆ BerendSec4.diag lam '' closedBox r := by
  intro z hz
  rw [mem_closedBox_iff] at hz
  have hlam : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le hm0 (hm i)
  refine ⟨fun i => z i / lam i, ?_, ?_⟩
  · rw [mem_closedBox_iff]
    intro i
    have hzi := hz i
    have hzi' : |z i| ≤ r * m := abs_le.2 ⟨hzi.1, hzi.2⟩
    have h2 : |z i / lam i| ≤ r := by
      rw [abs_div, abs_of_pos (hlam i), div_le_iff₀ (hlam i)]
      calc |z i| ≤ r * m := hzi'
        _ ≤ r * lam i := by nlinarith [hm i]
    exact abs_le.1 h2
  · funext i
    rw [BerendSec4.diag_apply]
    exact mul_div_cancel₀ (z i) (ne_of_gt (hlam i))

/-- Iterating the dilation grows the closed box by `m ^ k`. -/
theorem closedBox_subset_iterate_diag_image {lam : ι → ℝ} {m r : ℝ} (hm0 : 0 < m)
    (hm : ∀ i, m ≤ lam i) (hr : 0 ≤ r) (k : ℕ) :
    closedBox (r * m ^ k) ⊆ (BerendSec4.diag lam)^[k] '' closedBox r := by
  induction k with
  | zero =>
      intro z hz
      rw [pow_zero, mul_one] at hz
      exact ⟨z, hz, rfl⟩
  | succ k ih =>
      intro z hz
      have hrk : (0 : ℝ) ≤ r * m ^ k := by positivity
      have hstep : closedBox (r * m ^ (k + 1)) ⊆
          BerendSec4.diag lam '' closedBox (r * m ^ k) := by
        have : r * m ^ (k + 1) = (r * m ^ k) * m := by ring
        rw [this]
        exact closedBox_subset_diag_image hm0 hm hrk
      obtain ⟨y, hy, hyz⟩ := hstep hz
      obtain ⟨w, hw, hwy⟩ := ih hy
      refine ⟨w, hw, ?_⟩
      have h1 : (BerendSec4.diag lam)^[k + 1] w =
          BerendSec4.diag lam ((BerendSec4.diag lam)^[k] w) :=
        Function.iterate_succ_apply' (BerendSec4.diag lam) k w
      rw [h1, hwy, hyz]

/-- Iterates of a dilation applied to a point of the invariant set stay in it. -/
theorem iterate_mem_of_image_subset {E : Set (ι → ℝ)} {lam : ι → ℝ}
    (hinv : BerendSec4.diag lam '' E ⊆ E) (k : ℕ) {x : ι → ℝ} (hx : x ∈ E) :
    (BerendSec4.diag lam)^[k] x ∈ E := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hinv (Set.mem_image_of_mem _ ih)

/-- **The last step of Stage I.**  A closed set invariant under a diagonal
dilation that expands every coordinate by a uniform factor `m > 1`, and
containing a coordinate box around `0`, is everything. -/
theorem eq_univ_of_closedBox_subset {E : Set (ι → ℝ)} (_hE : IsClosed E) {lam : ι → ℝ}
    {m r : ℝ} (hm1 : 1 < m) (hm : ∀ i, m ≤ lam i) (hr : 0 < r)
    (hinv : BerendSec4.diag lam '' E ⊆ E) (hbox : closedBox r ⊆ E) : E = univ := by
  classical
  refine Set.eq_univ_of_forall fun z => ?_
  have hm0 : 0 < m := lt_trans zero_lt_one hm1
  -- a bound for the coordinates of `z`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ i, |z i| ≤ B :=
    ⟨∑ i, |z i|, fun i => Finset.single_le_sum (f := fun i => |z i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, B < m ^ k * r := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B / r) hm1
    exact ⟨k, by rw [div_lt_iff₀ hr] at hk; linarith [hk]⟩
  have hz : z ∈ closedBox (r * m ^ k) := by
    rw [mem_closedBox_iff]
    intro i
    have h1 : |z i| < r * m ^ k := lt_of_le_of_lt (hB i) (by linarith [hk])
    exact abs_le.1 (le_of_lt h1)
  obtain ⟨y, hy, hyz⟩ := closedBox_subset_iterate_diag_image hm0 hm (le_of_lt hr) k hz
  rw [← hyz]
  exact iterate_mem_of_image_subset hinv k (hbox hy)

/-! ## 2. Local fullness: the exact residual of Stage I -/

section LocalFull

variable {κ : Type*}

/-- A set of multipliers `lam i : ι → ℝ`; the diagonal family acts on the lift
`ι → ℝ` by `x ↦ fun k => lam i k * x k`. -/
def LiftInvariant (lam : κ → ι → ℝ) (E : Set (ι → ℝ)) : Prop :=
  ∀ i, BerendSec4.diag (lam i) '' E ⊆ E

/-- **Local fullness at the origin.**  Every closed invariant lift `E` with `0` as
a non-isolated point contains a coordinate box around `0`.  By
`zeroNonisolatedFull_iff_localFull` this is *equivalent* to Stage I, so it is the
exact statement Berend's §4 has to prove and the exact statement the
difference-set theorems of `BerendModulus` do not provide
(`sharpness_halfLine`). -/
def LocalFull (lam : κ → ι → ℝ) : Prop :=
  ∀ E : Set (ι → ℝ), IsClosed E → (0 : ι → ℝ) ∈ closure (E \ {0}) →
    LiftInvariant lam E → ∃ r : ℝ, 0 < r ∧ closedBox r ⊆ E

/-- Stage I on the lift, in the diagonal model. -/
def ZeroNonisolatedFullLift (lam : κ → ι → ℝ) : Prop :=
  ∀ E : Set (ι → ℝ), IsClosed E → (0 : ι → ℝ) ∈ closure (E \ {0}) →
    LiftInvariant lam E → E = univ

/-- **Local fullness gives Stage I**, by the box-growth argument; `i₀` is the
member of the family that expands every coordinate by the uniform factor
`m > 1`. -/
theorem zeroNonisolatedFullLift_of_localFull {lam : κ → ι → ℝ} {i₀ : κ} {m : ℝ}
    (hm1 : 1 < m) (hlam : ∀ k, m ≤ lam i₀ k) (h : LocalFull lam) :
    ZeroNonisolatedFullLift lam := by
  intro E hE hacc hinv
  obtain ⟨r, hr, hbox⟩ := h E hE hacc hinv
  exact eq_univ_of_closedBox_subset hE hm1 hlam hr (hinv i₀) hbox

/-- Conversely, Stage I trivially gives local fullness: if `E = univ` then the
lift contains every box. -/
theorem localFull_of_zeroNonisolatedFullLift {lam : κ → ι → ℝ}
    (h : ZeroNonisolatedFullLift lam) : LocalFull lam := by
  intro E hE hacc hinv
  rw [h E hE hacc hinv]
  exact ⟨1, one_pos, Set.subset_univ _⟩

/-- **Stage I for a diagonal family is equivalent to local fullness at `0`.**  So
the whole remaining content of Berend's §4 is a single local statement about the
accumulation set, and no further expansion/cone/projection work is needed once it
is available. -/
theorem zeroNonisolatedFullLift_iff_localFull {lam : κ → ι → ℝ} {i₀ : κ} {m : ℝ}
    (hm1 : 1 < m) (hlam : ∀ k, m ≤ lam i₀ k) :
    ZeroNonisolatedFullLift lam ↔ LocalFull lam :=
  ⟨localFull_of_zeroNonisolatedFullLift,
    zeroNonisolatedFullLift_of_localFull hm1 hlam⟩

end LocalFull

/-! ## 3. From the lift to the torus `(ι → ℝ) ⧸ L` -/

section Torus

/-- The toral endomorphism induced by a diagonal map preserving the lattice. -/
noncomputable def diagTorusEnd (L : AddSubgroup (ι → ℝ)) (lam : ι → ℝ)
    (hL : ∀ x ∈ L, BerendSec4.diag lam x ∈ L) : (ι → ℝ) ⧸ L →+ (ι → ℝ) ⧸ L :=
  QuotientAddGroup.map L L (BerendSec4.diag lam).toAddMonoidHom fun _ hx => hL _ hx

theorem diagTorusEnd_mk' (L : AddSubgroup (ι → ℝ)) (lam : ι → ℝ)
    (hL : ∀ x ∈ L, BerendSec4.diag lam x ∈ L) (x : ι → ℝ) :
    diagTorusEnd L lam hL (QuotientAddGroup.mk' L x) =
      QuotientAddGroup.mk' L (BerendSec4.diag lam x) :=
  QuotientAddGroup.map_mk' L L _ _ x

/-- The diagonal family of toral endomorphisms. -/
noncomputable def diagTorus (L : AddSubgroup (ι → ℝ)) (lam : κ → ι → ℝ)
    (hL : ∀ i, ∀ x ∈ L, BerendSec4.diag (lam i) x ∈ L) :
    κ → (ι → ℝ) ⧸ L →+ (ι → ℝ) ⧸ L :=
  fun i => diagTorusEnd L (lam i) (hL i)

variable {L : AddSubgroup (ι → ℝ)} {lam : κ → ι → ℝ}
  {hL : ∀ i, ∀ x ∈ L, BerendSec4.diag (lam i) x ∈ L}

theorem familyInvariant_lift {Y : Set ((ι → ℝ) ⧸ L)}
    (hinv : BerendDichotomy.FamilyInvariant (diagTorus L lam hL) Y) :
    LiftInvariant lam ((QuotientAddGroup.mk' L) ⁻¹' Y) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Set.mem_preimage] at hy ⊢
  have h := hinv i (Set.mem_image_of_mem (diagTorus L lam hL i) hy)
  rwa [diagTorus, diagTorusEnd_mk'] at h

/-- The accumulation hypothesis transfers from the torus to the lift: a non-
isolated class at `0` lifts to non-isolated points at `0` in `ι → ℝ`.  The lift
is used because the box formulation of local fullness lives in `ι → ℝ`; the
quotient map is open, so a neighbourhood of `0` upstairs still meets the
preimage set. -/
theorem acc_preimage {Y : Set ((ι → ℝ) ⧸ L)}
    (hacc : (0 : (ι → ℝ) ⧸ L) ∈ closure (Y \ {0})) :
    (0 : ι → ℝ) ∈ closure ((QuotientAddGroup.mk' L) ⁻¹' Y \ {0}) := by
  rw [mem_closure_iff_nhds] at hacc ⊢
  intro W hW
  have hopen : IsOpenMap (QuotientAddGroup.mk' L) := QuotientAddGroup.isOpenMap_coe
  have himg : (QuotientAddGroup.mk' L) '' W ∈ 𝓝 (0 : (ι → ℝ) ⧸ L) := by
    simpa using hopen.image_mem_nhds hW
  obtain ⟨y, hyW, hyY⟩ := hacc _ himg
  obtain ⟨x, hxW, rfl⟩ := hyW
  refine ⟨x, hxW, Set.mem_preimage.2 hyY.1, ?_⟩
  intro h0
  exact hyY.2 (by simp [Set.mem_singleton_iff.1 h0])

/-- **Stage I on the torus follows from local fullness on the lift.** -/
theorem zeroNonisolatedFull_of_localFull {i₀ : κ} {m : ℝ}
    (hm1 : 1 < m) (hlam : ∀ k, m ≤ lam i₀ k) (h : LocalFull lam) :
    BerendDichotomy.ZeroNonisolatedFull (diagTorus L lam hL) := by
  intro Y hY _ hacc hinv
  have hEclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage QuotientAddGroup.continuous_mk
  have hEuniv : (QuotientAddGroup.mk' L) ⁻¹' Y = univ :=
    zeroNonisolatedFullLift_of_localFull hm1 hlam h _ hEclosed
      (acc_preimage hacc)
      (familyInvariant_lift hinv)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  exact Set.mem_preimage.1 (by rw [hEuniv]; exact Set.mem_univ x)

end Torus

/-! ## 4. Sharpness: what the difference-set theorems cannot give -/

/-- **The half-line is a counterexample to every difference-set upgrade of
Stage I.**  `E = [0, ∞)` is closed, invariant under `x ↦ 2x` and `x ↦ x / 3`
(the hypotheses of the accepted one-dimensional `×2 ×3` theorem
`BerendRankTwo.sub_eq_univ_of_invariant`), has `0` as a non-isolated point, and
has full difference set `E - E = ℝ` — yet it is not everything and `0` is not an
interior point of it.

So the conclusions the integrated modules actually produce (`E - E = univ`, plus
the half-line inside `E` obtained on the way) are *consistent with the negation
of Stage I*.  Stage I additionally needs the lattice saturation `E + L = E`
together with the density of the coordinate line (as in
`BerendTorusLastMile`), and then the direction-density of `E` around `0`. -/
theorem sharpness_halfLine :
    ∃ E : Set ℝ, IsClosed E ∧ (0 : ℝ) ∈ closure (E \ {0}) ∧
      (∀ x ∈ E, 2 * x ∈ E) ∧ (∀ x ∈ E, x / 3 ∈ E) ∧
      E - E = univ ∧ E ≠ univ ∧ (0 : ℝ) ∉ interior E := by
  refine ⟨Set.Ici (0 : ℝ), isClosed_Ici, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0` is not isolated in `[0, ∞)`
    refine mem_closure_iff_nhds.2 fun t ht => ?_
    obtain ⟨l, u, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 ht
    obtain ⟨h1, h2⟩ := h0
    have hpos : (0 : ℝ) < min (u / 2) 1 := lt_min (by linarith) one_pos
    have hlt : min (u / 2) 1 < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact ⟨min (u / 2) 1, hsub (Set.mem_Ioo.2 ⟨by linarith, hlt⟩),
      mem_Ici.2 hpos.le, ne_of_gt hpos⟩
  · intro x hx
    exact mem_Ici.2 (by linarith [mem_Ici.1 hx])
  · intro x hx
    exact mem_Ici.2 (by linarith [mem_Ici.1 hx])
  · refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : (0 : ℝ) ≤ y
    · exact Set.mem_sub.2 ⟨y, mem_Ici.2 hy, 0, mem_Ici.2 le_rfl, by ring⟩
    · push Not at hy
      exact Set.mem_sub.2 ⟨0, mem_Ici.2 le_rfl, -y, mem_Ici.2 (by linarith), by ring⟩
  · intro h
    have h1 : (-1 : ℝ) ∈ Set.Ici (0 : ℝ) := by rw [h]; exact Set.mem_univ _
    exact absurd (mem_Ici.1 h1) (by norm_num)
  · intro h
    rw [mem_interior_iff_mem_nhds] at h
    obtain ⟨l, u, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 h
    obtain ⟨h1, h2⟩ := h0
    have : l / 2 ∈ Set.Ici (0 : ℝ) := hsub (Set.mem_Ioo.2 ⟨by linarith, by linarith⟩)
    have := mem_Ici.1 this
    linarith

/-! ## 5. Assembly (plan §E, item (4)): `BerendMultiInvarianceCorrected` from
Stage I and the residual propagation statement -/

section Assembly

variable {κ : Type*} (f : κ → Pt ≃ₗ[ℝ] Pt) (L : AddSubgroup Pt)
  (hpres : ∀ (i : κ) (g : Pt), g ∈ L → f i g ∈ L)
  [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))

/-- The family of toral endomorphisms attached to a family `f : κ → Pt ≃ₗ[ℝ] Pt`
of lattice-preserving linear equivalences.  This is the family the corrected
Berend statement `BerendMultiInvarianceCorrected` is about. -/
noncomputable def modelFamily : κ → (Pt ⧸ L) →+ (Pt ⧸ L) :=
  fun i => torusEnd L ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i)

variable {f L hpres}

/-- Stage I and the residual propagation statement, *for the very family the
corrected Berend statement quantifies over*, already give the corrected Berend
statement.  Nothing else is used: no axiom, no extra hypothesis on the model. -/
theorem berendMultiInvarianceCorrected_of_stageI_of_residual
    (hStage : BerendDichotomy.ZeroNonisolatedFull (modelFamily f L hpres))
    (hres : BerendDichotomy.NoProperFullDiffSet (modelFamily f L hpres)) :
    BerendMultiInvarianceCorrected κ f L hpres hZ B1 B2 B3 hcomm := by
  haveI : CompactSpace (Pt ⧸ L) := compact_quotient_of_isZLattice L
  haveI : Infinite (Pt ⧸ L) := BerendDichotomy.infinite_torus (L := L)
  exact BerendDichotomy.dichotomy_of_noProperFullDiffSet hStage hres

variable {K : Type*} [Field K] {𝒪 : Subring K}

/-- The unit–prime model form: Stage I plus the residual propagation statement
for `D.torusEndAct` give `UnitPrimeModel.berend_corrected`. -/
theorem unitPrimeModel_berend_corrected_of_stageI_of_residual (D : UnitPrimeModel L 𝒪)
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lactZ i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair D.linFam)
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusEndAct)
    (hres : BerendDichotomy.NoProperFullDiffSet D.torusEndAct) :
    BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZ B1 B2 B3
      D.linFam_comm := by
  haveI : CompactSpace (Pt ⧸ L) := compact_quotient_of_isZLattice L
  haveI : Infinite (Pt ⧸ L) := BerendDichotomy.infinite_torus (L := L)
  exact BerendDichotomy.dichotomy_of_noProperFullDiffSet hStage hres

end Assembly

/-! ## 6. Axiom audit -/

#print axioms zeroNonisolatedFullLift_iff_localFull
#print axioms eq_univ_of_closedBox_subset
#print axioms zeroNonisolatedFull_of_localFull
#print axioms sharpness_halfLine
#print axioms berendMultiInvarianceCorrected_of_stageI_of_residual
#print axioms unitPrimeModel_berend_corrected_of_stageI_of_residual

end BerendStageIClosure
end CubicTwoStage
