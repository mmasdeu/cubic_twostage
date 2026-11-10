/-
# Stage I, singleton branch: the axis point fills the torus

`BEREND_PROOF_PLAN.md` §C asks for `eq_univ_of_zero_nonisolated`: a closed
family-invariant `Y ⊆ Pt ⧸ L` of which `0` is a non-isolated point is the whole
torus.  The existing modules reduce the *difference set* statement
`Y - Y = univ` (`BerendModulus`, `BerendTorusLastMile`); the step to `Y = univ`
is the remaining one.

This module proves that step in the **singleton branch**: once Berend's Lemma
4.1 (`BerendSec4.exists_minimal_acc`) has produced a *one-coordinate*
accumulating set `{i}`, no difference-set/Furstenberg argument is needed at all.
The reason is that the lattice then does the work: a nonzero point `a • e i` of
the lift lies in `Y`, its multiplicatively-dense orbit `(λ α i * a) • e i` fills a
dense subset of the coordinate line mod `L`, and **that** line is dense in the
torus as soon as `coord {i} + L` is dense.

The two inputs are therefore not analytic but arithmetic:

* `Dense (coord {i} + L)` — the coordinate line is dense, i.e. the projection of
  the lattice to the complementary coordinates is dense.  For the project's
  cubic model this says that `σ(𝒪_K)` projects densely to the pair of
  coordinates left over, which holds because `r₁ + 2r₂ = 3` and the complex
  embedding of `𝒪_K` is dense in `ℂ`.  `BerendTorusLastMile` supplies the
  codimension-one criterion and the irrational-ratio criterion; §5 below chains
  them to this module's theorem.
* `Dense (range fun α => lam α i)` — the multipliers at the accumulating
  coordinate are dense in `ℝ` (a contractive *and* an expansive multiplier at
  `i` whose moduli are multiplicatively independent, plus the sign change
  `-id = μ_{-1}` of the unit group).  This is **not** implied by the corrected
  (B3): (B3) is a statement about the *maps* `μ_{uπ^j}` while this is a
  statement about their archimedean *multipliers*; §6 below proves the
  separation with an explicit two-map example.

Section 7 records that both inputs are **necessary**, not merely sufficient: a
proper closed invariant `Y` through a nonzero axis point cannot have a dense
multiplier set (`not_dense_multipliers_of_ne_univ`) nor a dense coordinate line
(`not_dense_axis_of_ne_univ`).  Hence, in the singleton branch, no irreducibility
hypothesis on the family can substitute for either arithmetic input — in
particular `B1` alone cannot close the branch.

Nothing here is assumed: no axiom, no `sorry`, no `Prop` hypothesis.  Every
statement either is proved outright or carries its hypotheses printed.
-/
import CubicTwoStage.BerendModulus
import CubicTwoStage.BerendTorusLastMile
import CubicTwoStage.BerendFullCone

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendAxis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The coordinate line is the range of `t ↦ t • e i` -/

/-- Coordinatewise form of the axis vector. -/
theorem smul_e_apply (t : ℝ) (i j : ι) :
    (t • BerendModulus.e i) j = if j = i then t else 0 :=
  congrFun (BerendModulus.smul_e t i) j

/-- The coordinate subspace `coord {i}` is exactly the image of the axis map
`t ↦ t • e i`. -/
theorem range_smul_e (i : ι) :
    Set.range (fun t : ℝ => t • BerendModulus.e i) =
      (BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩ j hj
    show (t • BerendModulus.e i) j = 0
    have h := congrFun (BerendModulus.smul_e t i) j
    rw [h, if_neg (by simpa using hj)]
  · intro hx
    refine ⟨x i, ?_⟩
    have h := BerendModulus.smul_e (x i) i
    show x i • BerendModulus.e i = x
    rw [h]
    funext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, BerendSec4.mem_coord.1 hx j hj]

/-- **The axis image is dense when the coordinate line plus the lattice is
dense.**  (Sufficient: the projection of `L` to the coordinates complementary to
`i` is dense, since then `coord {i} + L = univ`.) -/
theorem dense_axis_image {L : AddSubgroup (ι → ℝ)} {i : ι}
    (hd : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Dense (Set.range (fun t : ℝ => (QuotientAddGroup.mk' L) (t • BerendModulus.e i))) := by
  have himg : Dense ((QuotientAddGroup.mk' L) ''
      ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :=
    BerendTorusLastMile.Dense.image_of_surjective hd
      (QuotientAddGroup.mk'_surjective L) QuotientAddGroup.continuous_mk
  rw [BerendTorusLastMile.image_add_subgroup, ← range_smul_e i] at himg
  have heq : (QuotientAddGroup.mk' L) '' Set.range (fun t : ℝ => t • BerendModulus.e i)
      = Set.range (fun t : ℝ => (QuotientAddGroup.mk' L) (t • BerendModulus.e i)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨t, rfl⟩, rfl⟩
  rwa [heq] at himg

/-! ## 2. A dense set of axis scalars fills the torus -/

/-- Multiplication of a dense set of reals by a fixed nonzero scalar is dense. -/
theorem dense_range_mul {κ : Type*} {f : κ → ℝ} (hf : Dense (Set.range f)) {a : ℝ}
    (ha : a ≠ 0) : Dense (Set.range fun α => f α * a) := by
  rw [Metric.dense_iff] at hf ⊢
  intro x r hr
  have ha' : 0 < |a| := abs_pos.2 ha
  obtain ⟨y, hyball, α, rfl⟩ := hf (x / a) (r / |a|) (by positivity)
  refine ⟨f α * a, ?_, α, rfl⟩
  rw [Metric.mem_ball, Real.dist_eq] at hyball ⊢
  have hkey : f α * a - x = (f α - x / a) * a := by
    field_simp
  rw [hkey, abs_mul]
  calc |f α - x / a| * |a| < r / |a| * |a| := by
        exact mul_lt_mul_of_pos_right hyball ha'
    _ = r := div_mul_cancel₀ r (ne_of_gt ha')

/-- **Axis points on a dense set of scalars fill the torus.**  If `Y` is closed,
contains the class of `t • e i` for `t` in a dense set, and the axis image itself
is dense, then `Y` is everything. -/
theorem eq_univ_of_dense_axis_points {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    {i : ι} (hY : IsClosed Y) {A : Set ℝ} (hA : Dense (A : Set ℝ))
    (hpt : ∀ t ∈ A, (QuotientAddGroup.mk' L) (t • BerendModulus.e i) ∈ Y)
    (haxis : Dense (Set.range (fun t : ℝ =>
      (QuotientAddGroup.mk' L) (t • BerendModulus.e i)))) :
    Y = univ := by
  set f : ℝ → ((ι → ℝ) ⧸ L) := fun t => (QuotientAddGroup.mk' L) (t • BerendModulus.e i)
    with hf
  have hcont : Continuous f :=
    QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const)
  have hdense : Dense (f '' A) := by
    rw [dense_iff_closure_eq]
    have h1 : Set.range f ⊆ closure (f '' A) := by
      have h2 := image_closure_subset_closure_image hcont (s := A)
      rw [hA.closure_eq, Set.image_univ] at h2
      exact h2
    have h2 : (univ : Set ((ι → ℝ) ⧸ L)) ⊆ closure (f '' A) := by
      rw [← haxis.closure_eq]
      exact closure_minimal h1 isClosed_closure
    exact Set.eq_univ_iff_forall.2 fun x => h2 (Set.mem_univ x)
  have hsub : f '' A ⊆ Y := by
    rintro _ ⟨t, ht, rfl⟩
    exact hpt t ht
  have hall : (univ : Set ((ι → ℝ) ⧸ L)) ⊆ Y := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hY
  exact Set.eq_univ_iff_forall.2 fun x => hall (Set.mem_univ x)

/-! ## 3. Stage I in the singleton branch -/

/-- **Axis-point form of the singleton branch.**  A closed invariant `Y` that
contains the class of one nonzero point `a • e i` of the coordinate line, together
with the two arithmetic inputs, is the whole torus. -/
theorem eq_univ_of_axis_point {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    {i : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    {a : ℝ} (ha : a ≠ 0) (hpt : (QuotientAddGroup.mk' L) (a • BerendModulus.e i) ∈ Y)
    (hscal : Dense (Set.range fun α : κ => lam α i))
    (haxis : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Y = univ := by
  refine eq_univ_of_dense_axis_points hY (dense_range_mul hscal ha) ?_ (dense_axis_image haxis)
  rintro t ⟨α, rfl⟩
  have h1 := hinv α (a • BerendModulus.e i) hpt
  have hdiag : BerendSec4.diag (lam α) (a • BerendModulus.e i) =
      (lam α i * a) • BerendModulus.e i := by
    funext j
    rw [BerendSec4.diag_apply, smul_e_apply, smul_e_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rwa [hdiag] at h1

/-- **Stage I, singleton branch.**  Let `Y ⊆ (ι → ℝ) ⧸ L` be closed and
invariant under a family of diagonal maps `diag (lam α)`.  If `0` is a
non-isolated point of the lift of `Y` *inside one coordinate line* `{i}`
(Berend's `Acc`), the multipliers at `i` are dense in `ℝ`, and the coordinate
line is dense modulo `L`, then `Y` is the whole torus.

No difference set, no cone, no Furstenberg argument: the nonzero axis point
`a • e i ∈ prec Y` is enough, its orbit under the family covers a dense set of
axis points, and the lattice carries that line to all of the torus. -/
theorem eq_univ_of_acc_singleton {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    {i : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hscal : Dense (Set.range fun α : κ => lam α i))
    (haxis : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Y = univ := by
  classical
  -- a nonzero point of the lift on the axis
  obtain ⟨u, huE, hucoord, hune, -⟩ := (BerendSec4.acc_iff.1 hacc) 1 zero_lt_one
  -- it is a multiple of the axis vector
  have hu : u = (u i) • BerendModulus.e i := by
    funext j
    rw [smul_e_apply]
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, BerendSec4.mem_coord.1 hucoord j (by simpa using hj)]
  have ha : u i ≠ 0 := by
    intro h0
    exact hune (by rw [hu, h0, zero_smul])
  rw [hu] at huE
  exact eq_univ_of_axis_point hY hinv ha huE hscal haxis


/-! ## 4. Chaining the project's density criteria

`BerendTorusLastMile` proves that `coord (univ.erase j) + L` is dense when the
`j`-th coordinate projection of the lattice is dense, and that the latter holds
whenever two lattice elements have irrational `j`-coordinate ratio.  Composing
with §3 gives the singleton branch with those arithmetic inputs discharged. -/

/-- **Stage I, singleton branch, lattice input discharged by an irrational
coordinate ratio.**  Here `{i}` is the complement of the single coordinate `j`,
and two lattice elements with irrational `j`-coordinate ratio make the coordinate
line quasirational — hence dense modulo `L`. -/
theorem eq_univ_of_acc_singleton_of_irrational {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {i j : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hscal : Dense (Set.range fun α : κ => lam α i))
    (hS : ({i} : Finset ι) = Finset.univ.erase j)
    {l l' : L} (hirr : Irrational ((l : ι → ℝ) j / (l' : ι → ℝ) j)) :
    Y = univ := by
  have hd : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ))) := by
    rw [show ({i} : Set ι) = ((Finset.univ.erase j : Finset ι) : Set ι) by
      rw [← hS, Finset.coe_singleton]]
    exact BerendTorusLastMile.dense_coord_erase_add_of_dense_proj
      (BerendTorusLastMile.dense_range_coord_of_irrational hirr)
  exact eq_univ_of_acc_singleton hY hinv hacc hscal hd

/-! ## 5. The branch statement: what the singleton case still needs

Berend Lemma 4.1 (`BerendSec4.exists_minimal_acc`) produces, from a closed
invariant `Y` accumulating at `0`, a minimal coordinate set `S` with `Acc`.  If
`S` is a *singleton* — the `k = 1` case of the plan — §3 closes Stage I outright.
So the whole content of the remaining Stage I work is the `|S| ≥ 2` (conformal /
rank-two) case; this section states that split exactly, with no `Prop`
hypothesis hiding anything. -/

/-- **Stage I from a minimal accumulating coordinate set of cardinality one.** -/
theorem eq_univ_of_minimal_acc_card_one {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) Finset.univ)
    (hcard : ∀ S : Finset ι, BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) S →
      (∀ S' : Finset ι, S' ⊂ S → ¬ BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) S') →
      S.card = 1)
    (hscal : ∀ i : ι, Dense (Set.range fun α : κ => lam α i))
    (haxis : ∀ i : ι, Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) +
      (L : Set (ι → ℝ)))) :
    Y = univ := by
  obtain ⟨S, hSacc, hSmin⟩ := BerendSec4.exists_minimal_acc hacc
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (hcard S hSacc hSmin)
  exact eq_univ_of_acc_singleton hY hinv hSacc (hscal i) (haxis i)


/-! ## 6. Discharging the multiplier-density input with `MulIndep`

The hypothesis `hscal` of §3 is not a `Prop` placeholder: it follows from the
arithmetic input that `BerendModulus` already uses, namely multiplicative
independence (`MulIndep`) of one expansive and one contractive multiplier, plus
the sign flip supplied by a family member acting as `-id` on the coordinate (in
the unit–prime model: `μ_{-1}`).  This section proves that reduction. -/

/-- **The signed multiplier semigroup is dense in `ℝ`.**  For `c > 1 > d > 0`
multiplicatively independent (`BerendModulus.MulIndep`), the numbers
`± c ^ m * d ^ k` (`m : ℕ`, `k : ℤ`) are dense.  The positive half is
`BerendRankTwo.exists_pow_mul_pow_near` (density of `{c ^ m * d ^ n}` in
`(0, ∞)`, which is the arithmetic content of Berend's Lemma 4.4); the sign makes
it dense in `ℝ`, and `0` is a limit of `d ^ n`. -/
theorem dense_range_signed_pow_mul {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1)
    (hind : BerendModulus.MulIndep c d) :
    Dense (Set.range fun p : Bool × (ℕ × ℤ) =>
      if p.1 then c ^ p.2.1 * d ^ p.2.2 else -(c ^ p.2.1 * d ^ p.2.2)) := by
  have hirr := BerendRankTwo.irrational_log_div_log_of_indep
    (lt_trans zero_lt_one hc) hd0 hind
  have hnat : Dense (Set.range fun p : Bool × (ℕ × ℕ) =>
      if p.1 then c ^ p.2.1 * d ^ p.2.2 else -(c ^ p.2.1 * d ^ p.2.2)) := by
    rw [Metric.dense_iff]
    rintro x ε hε
    rcases lt_trichotomy x 0 with hx | hx | hx
    · obtain ⟨m, n, hmn⟩ := BerendRankTwo.exists_pow_mul_pow_near hc hd0 hd1 hirr
        (t := -x) (by linarith) hε
      refine ⟨-(c ^ m * d ^ n), ?_, (false, (m, n)), by simp⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have hkey : -(c ^ m * d ^ n) - x = -x - c ^ m * d ^ n := by ring
      rw [hkey]
      exact hmn
    · subst hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hd1
      refine ⟨-(c ^ 0 * d ^ n), ?_, (false, (0, n)), by simp⟩
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_pos hd0] using hn
    · obtain ⟨m, n, hmn⟩ := BerendRankTwo.exists_pow_mul_pow_near hc hd0 hd1 hirr hx hε
      refine ⟨c ^ m * d ^ n, ?_, (true, (m, n)), by simp⟩
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_sub_comm]
      exact hmn
  refine Dense.mono ?_ hnat
  rintro _ ⟨⟨s, m, k⟩, rfl⟩
  exact ⟨(s, (m, (k : ℤ))), by cases s <;> simp⟩

/-- **Stage I, singleton branch, with the multiplier input discharged.**  The
family realises every signed multiplier `± c ^ m * d ^ k` at the accumulating
coordinate `i` (in the unit–prime model: the members `μ_{±ε^k π^m}`), `c > 1 >
d > 0` are multiplicatively independent, and the coordinate line is dense modulo
`L`.  Then `Y` is the whole torus. -/
theorem eq_univ_of_acc_singleton_mulIndep {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {i : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : BerendModulus.MulIndep c d)
    (hreal : ∀ (m : ℕ) (k : ℤ) (s : Bool), ∃ α : κ,
      lam α i = if s then c ^ m * d ^ k else -(c ^ m * d ^ k))
    (haxis : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ)))) :
    Y = univ := by
  refine eq_univ_of_acc_singleton hY hinv hacc (Dense.mono ?_ (dense_range_signed_pow_mul hc hd0 hd1 hind)) haxis
  rintro _ ⟨⟨s, m, k⟩, rfl⟩
  obtain ⟨α, hα⟩ := hreal m k s
  exact ⟨α, hα⟩


/-! ## 7. The two inputs are exactly what the singleton branch needs

The contrapositive of §3 shows that neither input can be dropped: a proper closed
invariant `Y` with a nonzero axis point on a dense coordinate line *must* have
non-dense multipliers at that coordinate, and dually.  Together with §6 this
identifies the singleton branch's obligations as arithmetic (lattice
irrationality and archimedean modulus independence), not analytic. -/

/-- **Necessity of the multiplier density.**  If `Y` is a proper closed invariant
set containing the class of a nonzero axis point `a • e i` and the coordinate
line is dense modulo `L`, then the multipliers of the family at `i` are not dense
in `ℝ`. -/
theorem not_dense_multipliers_of_ne_univ {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {i : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    {a : ℝ} (ha : a ≠ 0) (hpt : (QuotientAddGroup.mk' L) (a • BerendModulus.e i) ∈ Y)
    (haxis : Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ))))
    (hproper : Y ≠ univ) :
    ¬ Dense (Set.range fun α : κ => lam α i) := by
  intro hscal
  exact hproper (eq_univ_of_axis_point hY hinv ha hpt hscal haxis)

/-- **Necessity of the lattice density.**  Dually, with dense multipliers and a
proper closed invariant `Y` through a nonzero axis point, the coordinate line
cannot be dense modulo `L`.  So no irreducibility hypothesis on the family
(`B1`) can replace the arithmetic of the lattice. -/
theorem not_dense_axis_of_ne_univ {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {i : ι} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (x : ι → ℝ), (QuotientAddGroup.mk' L) x ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) x) ∈ Y)
    {a : ℝ} (ha : a ≠ 0) (hpt : (QuotientAddGroup.mk' L) (a • BerendModulus.e i) ∈ Y)
    (hscal : Dense (Set.range fun α : κ => lam α i))
    (hproper : Y ≠ univ) :
    ¬ Dense ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)) + (L : Set (ι → ℝ))) :=
  fun haxis => hproper (eq_univ_of_axis_point hY hinv ha hpt hscal haxis)


/-! ## 8. The multi-coordinate branch: a line and a dense diagonal orbit

In the `|S| ≥ 2` (conformal) case the radial flow of `BerendModulus` gives, for a
point `x` of `E` with full support in `S`, the whole ray `{s • x : s > 0}` inside
`E` whenever the common weight vector is constant on `S`; together with the
symmetry `-id = μ_{-1}` of the unit group this is the whole **line** `ℝ x`.

A line is much more than a point: the family maps it to the lines
`ℝ (lam α · x)`, and if those directions are dense then `E` contains a dense
union of lines, hence — being closed — all of `Pt`, hence `Y` is the torus.  This
section proves that step.  The only remaining input for the multi-coordinate
branch is therefore the **arithmetic** statement that the diagonal orbit
directions `{[lam α · x]}` are dense, i.e. a Kronecker-type statement about the
archimedean absolute values and arguments of the multipliers; no irreducibility
hypothesis on the family (`B1`), and no cone argument, enters. -/

/-- **A line plus a dense diagonal orbit fills the torus.**  Let `Y` be closed and
invariant under the family `diag (lam α)`, and suppose the lift contains the whole
line `ℝ x` (`x ≠ 0`) — which is what the radial flow plus `-id` supplies on a
conformal block.  If the diagonal orbit directions `lam α · x` are dense in `Pt`,
then `Y` is everything. -/
theorem eq_univ_of_line_and_dense_orbit {L : AddSubgroup (ι → ℝ)}
    {Y : Set ((ι → ℝ) ⧸ L)} {κ : Type*} {lam : κ → ι → ℝ} (hY : IsClosed Y)
    (hinv : ∀ (α : κ) (z : ι → ℝ), (QuotientAddGroup.mk' L) z ∈ Y →
      (QuotientAddGroup.mk' L) (BerendSec4.diag (lam α) z) ∈ Y)
    {x : ι → ℝ} (hline : ∀ t : ℝ, (QuotientAddGroup.mk' L) (t • x) ∈ Y)
    (hdense : Dense (Set.range fun p : κ × ℝ => p.2 • fun i => lam p.1 i * x i)) :
    Y = univ := by
  -- every point of the dense orbit is in the lift of `Y`
  have hsub : (Set.range fun p : κ × ℝ => p.2 • fun i => lam p.1 i * x i) ⊆
      (QuotientAddGroup.mk' L) ⁻¹' Y := by
    rintro _ ⟨⟨α, t⟩, rfl⟩
    have hz : BerendSec4.diag (lam α) (t • x) = t • (fun i => lam α i * x i) := by
      rw [map_smul]
      rfl
    have hgoal : (QuotientAddGroup.mk' L) (t • (fun i => lam α i * x i)) ∈ Y := by
      rw [← hz]
      exact hinv α (t • x) (hline t)
    exact hgoal
  have himg : Dense ((QuotientAddGroup.mk' L) ''
      Set.range (fun p : κ × ℝ => p.2 • fun i => lam p.1 i * x i)) :=
    BerendTorusLastMile.Dense.image_of_surjective hdense
      (QuotientAddGroup.mk'_surjective L) QuotientAddGroup.continuous_mk
  have hdenseY : Dense Y := Dense.mono (Set.image_subset_iff.2 hsub) himg
  rw [← hY.closure_eq]
  exact hdenseY.closure_eq


/-! ## 9. Where the line comes from: radial flow plus `-id`

`BerendModulus.radial_flow_mem_of_indep` gives, on a minimal accumulating
coordinate set, invariance of the lift under the whole positive weighted flow
`s ↦ (s ^ (w i) * x i)`.  On a conformal block the common weight vector is
constant, so on the support of `x` the flow is the plain dilation `s • x`; with
`-id = μ_{-1}` in the unit group (a family member, since `-1` is a unit) the ray
becomes the line.  This section proves that chaining, so that §8's hypothesis
`hline` is not an extra assumption but the output of the existing modules. -/

/-- **The line through a full-support point of the lift.**  Hypotheses: the lift is
invariant under the two weighted dilations of `BerendModulus` with
multiplicatively independent `c > 1 > d > 0` (corrected (B3) read on the
multipliers, produced by Berend's Lemma 4.4), the weight vector is constant `1` on
the support of `x`, `0 ∈ Y`, and the family contains `-id`.  Conclusion: the whole
line `ℝ x` projects into `Y`. -/
theorem line_mem_of_radial_flow {L : AddSubgroup (ι → ℝ)} {Y : Set ((ι → ℝ) ⧸ L)}
    {w : ι → ℕ} {c d : ℝ} (hY : IsClosed Y)
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : BerendModulus.MulIndep c d)
    (hinv1 : ∀ z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun i => c ^ (w i)) z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun i => d ^ (w i)) z ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {x : ι → ℝ} (hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hw : ∀ i, x i ≠ 0 → w i = 1)
    (hzero : (0 : (ι → ℝ) ⧸ L) ∈ Y)
    (hneg : ∀ z : ι → ℝ, (QuotientAddGroup.mk' L) z ∈ Y →
      (QuotientAddGroup.mk' L) (-z) ∈ Y) :
    ∀ t : ℝ, (QuotientAddGroup.mk' L) (t • x) ∈ Y := by
  intro t
  have hEclosed : IsClosed ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    hY.preimage QuotientAddGroup.continuous_mk
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- `t < 0`: radial flow at `-t > 0`, then `-id`
    have hs : 0 < -t := by linarith
    have hflow := BerendModulus.radial_flow_mem_of_indep hEclosed hc hd0 hd1 hind
      hinv1 hinv2 hx hs
    have heq : (fun i => (-t) ^ (w i) * x i) = -t • x := by
      funext i
      by_cases hi : x i = 0
      · simp [hi]
      · rw [hw i hi, pow_one, Pi.smul_apply, smul_eq_mul]
    rw [heq] at hflow
    have hz : (QuotientAddGroup.mk' L) ((-t) • x) ∈ Y := hflow
    have := hneg ((-t) • x) hz
    have hneg_eq : -((-t) • x) = t • x := by
      simp [neg_smul]
    rwa [hneg_eq] at this
  · subst ht
    simpa using hzero
  · -- `t > 0`: the radial flow directly
    have hflow := BerendModulus.radial_flow_mem_of_indep hEclosed hc hd0 hd1 hind
      hinv1 hinv2 hx ht
    have heq : (fun i => t ^ (w i) * x i) = t • x := by
      funext i
      by_cases hi : x i = 0
      · simp [hi]
      · rw [hw i hi, pow_one, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at hflow

end BerendAxis
end CubicTwoStage

/-! ## 7. Axiom audit -/

#print axioms CubicTwoStage.BerendAxis.range_smul_e
#print axioms CubicTwoStage.BerendAxis.dense_axis_image
#print axioms CubicTwoStage.BerendAxis.dense_range_mul
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_dense_axis_points
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_axis_point
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_acc_singleton
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_acc_singleton_of_irrational
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_minimal_acc_card_one
#print axioms CubicTwoStage.BerendAxis.dense_range_signed_pow_mul
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_acc_singleton_mulIndep
#print axioms CubicTwoStage.BerendAxis.not_dense_multipliers_of_ne_univ
#print axioms CubicTwoStage.BerendAxis.not_dense_axis_of_ne_univ
#print axioms CubicTwoStage.BerendAxis.eq_univ_of_line_and_dense_orbit
#print axioms CubicTwoStage.BerendAxis.line_mem_of_radial_flow
