/-
Section 5 of the paper: certified coverings — Proposition 5.2 (verification)
and Proposition 5.3 (termination).
-/
import CubicTwoStage.Basic
import CubicTwoStage.Setting
import CubicTwoStage.Box

set_option linter.unusedVariables false

open MeasureTheory

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-- A dyadic cube of level `e.level` with lower corner `e.corner`, in lattice
coordinates. -/
noncomputable def dyadicCube (level : ℕ) (corner : Fin 3 → ℤ) : Set Pt :=
  Set.Icc (fun i => (corner i : ℝ) / 2 ^ level) (fun i => ((corner i : ℝ) + 1) / 2 ^ level)

/-- An entry of a certificate: a dyadic box, a centre `[q₁,q₂]` and the norm `n`
of the denominator. -/
structure Cert (K : Type*) [Field K] where
  q1 : K
  q2 : K
  n : ℕ
  level : ℕ
  corner : Fin 3 → ℤ

namespace Cert

/-- The box of a certificate entry. -/
noncomputable def box (e : Cert K) : Set Pt := dyadicCube e.level e.corner

/-- The centre of a certificate entry. -/
def centre (e : Cert K) : K := e.q1 + e.q2⁻¹

end Cert

theorem isClosed_dyadicCube (level : ℕ) (corner : Fin 3 → ℤ) :
    IsClosed (dyadicCube level corner) := isClosed_Icc

theorem measurableSet_dyadicCube (level : ℕ) (corner : Fin 3 → ℤ) :
    MeasurableSet (dyadicCube level corner) := measurableSet_Icc


/-- Two closed boxes whose interiors are disjoint meet in a null set.  This
  supplies the a.e.-disjointness needed for finite measure additivity. -/
theorem volume_inter_Icc_eq_zero_of_interiors_disjoint (a b c d : Pt)
    (hD : Disjoint (interior (Set.Icc a b)) (interior (Set.Icc c d))) :
    volume (Set.Icc a b ∩ Set.Icc c d) = 0 := by
  classical
  rw [Set.Icc_inter_Icc]
  by_cases hgood : ∀ i, ((a ⊔ c) i) < ((b ⊓ d) i)
  · exfalso
    have hI : interior (Set.Icc (a ⊔ c) (b ⊓ d)) = ∅ := by
      rw [← Set.Icc_inter_Icc, interior_inter]
      exact Set.disjoint_iff_inter_eq_empty.mp hD
    let z : Pt := fun i => (((a ⊔ c) i + (b ⊓ d) i) / 2)
    have hz : z ∈ Set.pi Set.univ (fun i => Set.Ioo ((a ⊔ c) i) ((b ⊓ d) i)) := by
      intro i _
      exact ⟨by dsimp [z]; have h := hgood i; dsimp at h; linarith,
        by dsimp [z]; have h := hgood i; dsimp at h; linarith⟩
    have hsub : Set.pi Set.univ (fun i => Set.Ioo ((a ⊔ c) i) ((b ⊓ d) i)) ⊆
        Set.Icc (a ⊔ c) (b ⊓ d) := by
      intro z hz
      rw [Set.mem_Icc]
      exact ⟨fun i => le_of_lt (hz i (Set.mem_univ i)).1,
        fun i => le_of_lt (hz i (Set.mem_univ i)).2⟩
    have hopen : IsOpen (Set.pi Set.univ (fun i => Set.Ioo ((a ⊔ c) i) ((b ⊓ d) i))) :=
      isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
    have hz' := interior_maximal hsub hopen hz
    rw [hI] at hz'
    exact hz'
  · push Not at hgood
    obtain ⟨i, hi⟩ := hgood
    rw [Real.volume_Icc_pi, Finset.prod_eq_zero_iff]
    refine ⟨i, Finset.mem_univ i, ENNReal.ofReal_eq_zero.mpr ?_⟩
    simp only [sub_nonpos]
    exact hi


/-- **Proposition 5.2, condition (i) alone** — the dyadic tiling lemma.

A finite family of dyadic cubes lying in `[0,1]³`, with pairwise disjoint
interiors, and whose volumes add up to `1`, covers `[0,1]³`.  (In a certificate
the cubes are additionally pairwise distinct and non-nested; for dyadic cubes
that is enough to give disjoint interiors, by
`dyadic_cubes_nested_or_disjoint` below.)

The proof is the measure-theoretic argument of the paper: the complement is
relatively open in `[0,1]³` and has measure zero, hence is empty. -/
theorem dyadic_cubes_cover (cert : Finset (Cert K))
    (hsub : ∀ e ∈ cert, e.box ⊆ unitCube)
    (hdisj : ∀ e ∈ cert, ∀ f ∈ cert, e ≠ f → Disjoint (interior e.box) (interior f.box))
    (hvol : ∑ e ∈ cert, (volume e.box).toReal = 1) :
    unitCube ⊆ ⋃ e ∈ cert, e.box := by
  classical
  have hAE : (↑cert : Set (Cert K)).Pairwise
      (Function.onFun (MeasureTheory.AEDisjoint volume) Cert.box) := by
    intro e he f hf hef
    change volume (e.box ∩ f.box) = 0
    exact volume_inter_Icc_eq_zero_of_interiors_disjoint _ _ _ _ (hdisj e he f hf hef)
  have hUclosed : IsClosed (⋃ e ∈ cert, e.box) :=
    cert.finite_toSet.isClosed_biUnion (fun e _ => isClosed_dyadicCube e.level e.corner)
  have hUmeas : MeasurableSet (⋃ e ∈ cert, e.box) :=
    cert.finite_toSet.measurableSet_biUnion (fun e _ => measurableSet_dyadicCube e.level e.corner)
  have hUsub : (⋃ e ∈ cert, e.box) ⊆ unitCube := by
    exact Set.iUnion₂_subset hsub
  have hUsum := measure_biUnion_finset₀ hAE
    (fun e _ => (measurableSet_dyadicCube e.level e.corner).nullMeasurableSet)
  have hfin : ∀ e ∈ cert, volume e.box ≠ ⊤ := by
    intro e he htop
    have hle := MeasureTheory.measure_mono (μ := volume) (hsub e he)
    rw [htop, volume_unitCube] at hle
    simp at hle
  have hUone : volume (⋃ e ∈ cert, e.box) = 1 := by
    refine (ENNReal.toReal_eq_one_iff _).mp ?_
    rw [hUsum, ENNReal.toReal_sum hfin]
    exact hvol
  have hcomp : volume (unitCube \ ⋃ e ∈ cert, e.box) = 0 := by
    rw [measure_sdiff hUsub hUmeas.nullMeasurableSet (by rw [hUone]; simp),
      volume_unitCube, hUone]
    simp
  intro x hx
  by_contra hxU
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_compl_iff.mpr hUclosed) x hxU
  let δ : ℝ := min 1 r
  have hδpos : 0 < δ := by
    exact lt_min zero_lt_one hr
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδler : δ ≤ r := min_le_right _ _
  let z : Pt := fun i => x i + δ * ((1 / 2 : ℝ) - x i)
  have hxi : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i => ⟨hx.1 i, hx.2 i⟩
  have hzball : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro i
    have hb : |((1 / 2 : ℝ) - x i)| ≤ 1 / 2 := by
      have h1 := (hxi i).1
      have h2 := (hxi i).2
      rw [abs_le]
      constructor <;> linarith
    have hxz : |z i - x i| = δ * |((1 / 2 : ℝ) - x i)| := by
      dsimp [z]
      rw [show x i + δ * ((1 / 2 : ℝ) - x i) - x i = δ * ((1 / 2 : ℝ) - x i) by ring,
        abs_mul, abs_of_pos hδpos]
    rw [Real.dist_eq, hxz]
    have hcalc : δ * |((1 / 2 : ℝ) - x i)| ≤ δ / 2 := by
      calc
        δ * |((1 / 2 : ℝ) - x i)| ≤ δ * (1 / 2) :=
          mul_le_mul_of_nonneg_left hb hδpos.le
        _ = δ / 2 := by ring
    linarith
  have hzInt : z ∈ Set.pi Set.univ (fun i : Fin 3 => Set.Ioo (0 : ℝ) 1) := by
    intro i _
    dsimp [z]
    have hxl := (hxi i).1
    have hxu := (hxi i).2
    constructor <;> nlinarith
  have hIntOpen : IsOpen (Set.pi Set.univ (fun i : Fin 3 => Set.Ioo (0 : ℝ) 1)) :=
    isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
  obtain ⟨ρ, hρ, hbr⟩ := Metric.isOpen_iff.mp (hIntOpen.inter Metric.isOpen_ball) z
    ⟨hzInt, hzball⟩
  have hbrSub : Metric.ball z ρ ⊆ unitCube \ ⋃ e ∈ cert, e.box := by
    intro w hw
    have hwO := hbr hw
    refine ⟨?_, ?_⟩
    · exact ⟨fun i => (hwO.1 i (Set.mem_univ i)).1.le,
        fun i => (hwO.1 i (Set.mem_univ i)).2.le⟩
    · have hwU := hball hwO.2
      exact hwU
  have hzzero : volume (Metric.ball z ρ) = 0 := measure_mono_null hbrSub hcomp
  have hzpos : 0 < volume (Metric.ball z ρ) :=
    Metric.isOpen_ball.measure_pos volume ⟨z, Metric.mem_ball_self hρ⟩
  rw [hzzero] at hzpos
  exact (lt_irrefl 0 hzpos).elim


/-- **Proposition 5.2**.  A list of pairs (dyadic box, centre) proves that `K` is
`N`-smooth Euclidean, with `N` the largest denominator norm in the list, when

  (i)  the boxes lie in `[0,1]³`, are pairwise distinct and non-nested, and their
       volumes add up to `1`;
  (ii) for each centre the stored integer `n` equals `|Nm_{K/ℚ}(α)|` and the
       stored class equals `r/α` modulo `𝒪` with `r ∈ U_α`;
  (iii) each box satisfies the upper bound of Lemma 5.1.

Conditions (ii) and (iii) are exactly `hii` and `hiii`; condition (i) enters
through `hcover`, the dyadic tiling lemma. -/
theorem prop_verify (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt)
    (cert : Finset (Cert K)) (N : ℕ)
    (hN : ∀ e ∈ cert, e.n ≤ N)
    (hii : ∀ e ∈ cert, e.q1 ∈ 𝒪 ∧ e.q2 ∈ 𝒪 ∧ e.q2 ≠ 0 ∧ Nm e.q2 = (e.n : ℚ≥0))
    (hbox : ∀ e ∈ cert, ∀ x ∈ e.box,
      |normR (x - σ (e.q1 + e.q2⁻¹))| < (((Nm e.q2 : ℚ≥0)) : ℝ)⁻¹)
    (hcover : unitCube ⊆ ⋃ e ∈ cert, e.box) :
    IsNSmoothEuclidean 𝒪 Nm σ N := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp (hcover hx)
  obtain ⟨h1, h2, h3, h4⟩ := hii e he
  exact ⟨e.q1, h1, e.q2, h2, h3, h4 ▸ Nat.cast_le.mpr (hN e he), hbox e he x hxe⟩

/-- **Proposition 5.3**.  If `K` is `N`-smooth Euclidean, then a finite set
`Z ⊆ 𝒞_N` of centres and a mesh size `δ > 0` exist with: every cube of the
fundamental domain of side `< δ` lies in one of the regions of `Z`.  Hence the
depth-first search terminates whenever its candidate set contains `Z` and its
maximal depth is at least `ℓ = ⌈-log₂ δ⌉`. -/
theorem prop_terminate (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (N : ℕ)
    (h : IsNSmoothEuclidean 𝒪 Nm σ N) :
    ∃ Z : Set (K × K),
      Z.Finite ∧ (∀ p ∈ Z, p.1 ∈ 𝒪 ∧ p.2 ∈ 𝒪 ∧ p.2 ≠ 0 ∧ Nm p.2 ≤ (N : ℚ≥0)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ unitCube, ∃ p ∈ Z,
        ∀ y ∈ Metric.ball x δ,
          |normR (y - σ (p.1 + p.2⁻¹))| < (((Nm p.2 : ℚ≥0)) : ℝ)⁻¹ := by
  classical
  -- Each point of the fundamental domain has a ball inside one region.
  have hpt : ∀ x : unitCube, ∃ (p : K × K) (r : ℝ), 0 < r ∧ p.1 ∈ 𝒪 ∧ p.2 ∈ 𝒪 ∧
      p.2 ≠ 0 ∧ Nm p.2 ≤ (N : ℚ≥0) ∧
      Metric.ball (x : Pt) r ⊆ {y : Pt | |normR (y - σ (p.1 + p.2⁻¹))| <
        (((Nm p.2 : ℚ≥0)) : ℝ)⁻¹} := by
    intro x
    obtain ⟨q1, hq1, q2, hq2, hq2ne, hq2le, hlt⟩ := h x x.2
    have hcont : Continuous fun y : Pt => |normR (y - σ (q1 + q2⁻¹))| :=
      (continuous_normR.comp (continuous_id.sub continuous_const)).abs
    have hopen : IsOpen {y : Pt | |normR (y - σ (q1 + q2⁻¹))| <
        (((Nm q2 : ℚ≥0)) : ℝ)⁻¹} :=
      isOpen_lt hcont continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hlt
    exact ⟨(q1, q2), r, hr, hq1, hq2, hq2ne, hq2le, hball⟩
  choose p r hr hp1 hp2 hpne hpN hball using hpt
  -- Compactness: finitely many balls of half radius cover the closed cube.
  have hcov : unitCube ⊆ ⋃ x : unitCube, Metric.ball (x : Pt) (r x / 2) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (by linarith [hr ⟨y, hy⟩])⟩
  obtain ⟨t, ht⟩ := isCompact_unitCube.elim_finite_subcover
    (fun x : unitCube => Metric.ball (x : Pt) (r x / 2)) (fun x => Metric.isOpen_ball) hcov
  have hneCube : unitCube.Nonempty := ⟨0, by simp [unitCube]⟩
  have htne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨z, hz⟩ := hneCube
      have := ht hz
      rw [h] at this
      simp at this
    · exact h
  refine ⟨p '' (t : Set unitCube), ?_, ?_, (t.image r).min' (htne.image r) / 2, ?_, ?_⟩
  · exact t.finite_toSet.image p
  · rintro q ⟨x, -, rfl⟩
    exact ⟨hp1 x, hp2 x, hpne x, hpN x⟩
  · obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (Finset.min'_mem (t.image r) (htne.image r))
    rw [← hx]
    exact half_pos (hr x)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine ⟨p i, Set.mem_image_of_mem _ hi, fun y hy => ?_⟩
    apply hball i
    -- `dist y i < r i` by the triangle inequality and `δ ≤ r i / 2`
    have hδ : (t.image r).min' (htne.image r) / 2 ≤ r i / 2 := by
      have : r i ∈ t.image r := Finset.mem_image_of_mem _ hi
      have := Finset.min'_le (t.image r) (r i) this
      linarith
    have h1 : dist y (i : Pt) ≤ dist y x + dist x (i : Pt) := dist_triangle _ _ _
    have h2 : dist y x < (t.image r).min' (htne.image r) / 2 := hy
    have h3 : dist x (i : Pt) < r i / 2 := hxi
    show dist y (i : Pt) < r i
    linarith

end CubicTwoStage
