/-
# Modulus independence, weighted multipliers, and the `k = 1` stage-C milestone

Direction d7 of swarm `smw801o7v` (member m2).  Berend, *Multi-invariant sets on
tori*, Trans. AMS **280** (1983), §4.

Three ingredients, all axiom free (`propext`, `Classical.choice`, `Quot.sound`):

1. **Modulus independence.**  In the common eigenbasis every member of the
   family is a diagonal map `diag lam`.  The paper's Lemma 4.4 concludes that the
   logarithmic growth-rate vectors of the family on a minimal accumulating
   coordinate set `S` are *proportional*: there are `c d : ℝ` and a weight vector
   `w : ι → ℕ` with `lam i = c ^ w i`, `mu i = d ^ w i`.  The one-dimensional
   theorem `BerendRankTwo.acc_coord_subset_sub` needs incomparability of the
   *scalars* `lam i` and `mu i` at a single coordinate `i`.  Section 1 shows that
   rational independence of `c` and `d` (Berend's corrected (B3) read on the
   multipliers) passes to the powers `c ^ w i`, `d ^ w i`, and that `c > 1 > d > 0`
   with `w i > 0` produces the expansion/contraction the theorem asks for.  This
   is the arithmetic step the plan calls "unit `ε`/`ε⁻¹` contraction and modulus
   independence from `rational_independence_corrected`".

2. **The `k = 1` case of stage C, up to the difference set.**  Composing 1 with
   the accepted one-dimensional theorem gives `coord {i} ⊆ E - E`, i.e. the whole
   coordinate line lies in the difference set of the lift.

3. **Lattice saturation.**  The lift `E = π ⁻¹' Y` of a torus set is closed under
   adding lattice vectors, so 2 upgrades to `coord {i} + L ⊆ E - E`, and hence
   `π '' coord {i} ⊆ Y - Y`.  If the projection of that coordinate line is dense
   — the "irrational-coordinate-line" hypothesis — then `Y - Y` is the whole
   torus.  This is exactly the `k = 1` output of §4 that the amended plan §D.5
   consumes as the negation of `NoProperFullDiffSet`.

What is *not* here: the passage from `Y - Y = univ` to `Y = univ`.  In dimension
one that passage is Furstenberg's `×2 ×3` theorem (the base-`2` Cantor set is
closed, `×2`-invariant, has `0` as a non-isolated point and full difference set,
and is not the circle), so §4's last step is the genuinely deep one; see the
board posting of this direction for the exact statement of the deficit.
-/
import CubicTwoStage.BerendRankTwoDiag
import CubicTwoStage.BerendMinimalTorus

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendModulus

variable {ι : Type*}

/-! ## 1. Modulus independence -/

/-- **Multiplicative (rational) independence of two positive reals**: no
nontrivial integer power of one is an integer power of the other, the zeroth
powers included.  This is Berend's corrected (B3) read on the scalar
multipliers of a diagonal map. -/
def MulIndep (c d : ℝ) : Prop := ∀ m n : ℤ, c ^ m = d ^ n → m = 0 ∧ n = 0

/-- Neither scalar of a multiplicatively independent pair is `1`. -/
theorem MulIndep.ne_one_left {c d : ℝ} (h : MulIndep c d) : c ≠ 1 := by
  intro hc
  exact absurd (h 1 0 (by rw [hc, one_zpow, zpow_zero])).1 one_ne_zero

/-- Neither scalar of a multiplicatively independent pair is `1`. -/
theorem MulIndep.ne_one_right {c d : ℝ} (h : MulIndep c d) : d ≠ 1 := by
  intro hd
  exact absurd (h 0 1 (by rw [hd, one_zpow, zpow_zero])).2 one_ne_zero

/-- **Modulus independence passes to positive powers.**  If `c` and `d` are
multiplicatively independent then so are `c ^ w` and `d ^ w` for every `w ≠ 0`.
This is the step that turns the common log-growth-ratio vector of Lemma 4.4
into independence of the multipliers at a single coordinate. -/
theorem mulIndep_pow {c d : ℝ} (h : MulIndep c d) {w : ℕ} (hw : w ≠ 0) :
    MulIndep (c ^ w) (d ^ w) := by
  intro m n hmn
  have hcast : ((w : ℤ)) ≠ 0 := by
    simpa using hw
  have hpow : c ^ ((w : ℤ) * m) = d ^ ((w : ℤ) * n) := by
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    exact hmn
  obtain ⟨h1, h2⟩ := h _ _ hpow
  exact ⟨mul_eq_zero.1 h1 |>.resolve_left hcast,
    mul_eq_zero.1 h2 |>.resolve_left hcast⟩

/-- **Expansion at a weighted coordinate.** -/
theorem one_lt_pow_of_one_lt {c : ℝ} (hc : 1 < c) {w : ℕ} (hw : 0 < w) :
    1 < c ^ w := one_lt_pow₀ hc hw.ne'

/-- **Contraction at a weighted coordinate.** -/
theorem pow_between {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) {w : ℕ} (hw : 0 < w) :
    0 < d ^ w ∧ d ^ w < 1 :=
  ⟨pow_pos hd0 w, pow_lt_one₀ hd0.le hd1 hw.ne'⟩

/-! ## 2. The one-dimensional theorem with weighted multipliers -/

variable [Fintype ι] [DecidableEq ι]

/-- **Stage C.5 in the `k = 1` case, with the multipliers produced from a common
weight vector.**  `E ⊆ ι → ℝ` is closed and invariant under two diagonal maps
whose multipliers at the coordinate `i` are `c ^ w` and `d ^ w` with `w > 0`,
`c > 1 > d > 0`, and `c`, `d` multiplicatively independent.  If `E` accumulates
at `0` on the coordinate line `{i}`, then the whole line lies in `E - E`.

This composes `BerendRankTwo.acc_coord_subset_sub` (the accepted accepted
one-dimensional theorem) with the modulus arithmetic of §1; it is the exact
form in which the paper's Lemma 4.4 conclusion feeds the rank-two argument. -/
theorem coord_subset_sub_of_weights
    {E : Set (ι → ℝ)} (hE : IsClosed E) {lam mu : ι → ℝ}
    (hinv1 : ∀ x ∈ E, BerendSec4.diag lam x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag mu x ∈ E)
    {i : ι} {c d : ℝ} {w : ℕ} (hw : 0 < w)
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hlam : lam i = c ^ w) (hmu : mu i = d ^ w)
    (hacc : BerendSec4.Acc E {i}) :
    ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) ⊆ E - E := by
  refine BerendRankTwo.acc_coord_subset_sub hE hinv1 hinv2 ?_ ?_ ?_ ?_ hacc
  · rw [hlam]; exact one_lt_pow_of_one_lt hc hw
  · rw [hmu]; exact (pow_between hd0 hd1 hw).1
  · rw [hmu]; exact (pow_between hd0 hd1 hw).2
  · rw [hlam, hmu]
    intro m n hmn
    exact mulIndep_pow hind (Nat.pos_iff_ne_zero.1 hw) m n hmn

/-! ## 3. Lattice saturation of the lift -/

/-- The lift `E = π ⁻¹' Y` of a subset of the torus is closed under adding
lattice vectors. -/
def LSaturated (L : AddSubgroup (ι → ℝ)) (E : Set (ι → ℝ)) : Prop :=
  ∀ l ∈ L, ∀ x ∈ E, x + l ∈ E

/-- The lift of any torus subset is `L`-saturated. -/
theorem lSaturated_preimage (L : AddSubgroup (ι → ℝ)) (Y : Set ((ι → ℝ) ⧸ L)) :
    LSaturated L ((QuotientAddGroup.mk' L) ⁻¹' Y) := by
  intro l hl x hx
  rw [Set.mem_preimage] at hx ⊢
  have hzero : (QuotientAddGroup.mk' L) l = 0 := by
    have h1 : ((l : ι → ℝ) : (ι → ℝ) ⧸ L) = ((0 : ι → ℝ) : (ι → ℝ) ⧸ L) := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      simpa using hl
    simpa using h1
  have hsame : (QuotientAddGroup.mk' L) (x + l) = (QuotientAddGroup.mk' L) x := by
    rw [map_add, hzero, add_zero]
  rwa [hsame]

/-- **Lattice saturation upgrades a line inside the difference set to the
saturated line.**  If `coord {i} ⊆ E - E` and `E` is `L`-saturated, then every
translate `v + l` of a point `v` of the coordinate line by a lattice vector lies
in `E - E`. -/
theorem coord_add_lattice_subset_sub {L : AddSubgroup (ι → ℝ)} {E : Set (ι → ℝ)}
    (hE : LSaturated L E) {i : ι}
    (hsub : ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) ⊆ E - E) :
    ∀ v ∈ (BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ)), ∀ l ∈ L, v + l ∈ E - E := by
  intro v hv l hl
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 (hsub hv)
  refine Set.mem_sub.2 ⟨a + l, hE l hl a ha, b, hb, ?_⟩
  calc a + l - b = (a - b) + l := by abel
    _ = v + l := by rw [hab]

/-! ## 4. The `k = 1` case of stage C: the difference set is everything -/

/-- The `i`-th standard basis vector as an element of `ι → ℝ`. -/
noncomputable def e (i : ι) : ι → ℝ := fun j => if j = i then 1 else 0

theorem e_mem_coord (i : ι) : e i ∈ BerendSec4.coord ({i} : Set ι) := by
  intro j hj
  simp only [e]
  rw [if_neg]
  simpa using hj

theorem smul_e (t : ℝ) (i : ι) :
    (t • e i : ι → ℝ) = fun j => if j = i then t else 0 := by
  funext j
  by_cases hj : j = i <;> simp [e, hj]

/-- **Stage C, `k = 1`, difference-set form.**  Let `Y` be a closed subset of the
torus whose lift `E = π ⁻¹' Y` is invariant under two diagonal maps and
accumulates at `0` on a single coordinate line.  Then the difference set `Y - Y`
contains the whole projection of that line; if that projection is dense — the
irrational-coordinate-line hypothesis — then `Y - Y` is the whole torus. -/
theorem torus_sub_eq_univ_of_acc_coord {L : AddSubgroup (ι → ℝ)}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) {lam mu : ι → ℝ} {i : ι}
    {c d : ℝ} {w : ℕ}
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag lam x ∈
      (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y, BerendSec4.diag mu x ∈
      (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hw : 0 < w) (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hlam : lam i = c ^ w) (hmu : mu i = d ^ w)
    (hacc : BerendSec4.Acc ((QuotientAddGroup.mk' L) ⁻¹' Y) {i})
    (hdense : DenseRange (fun t : ℝ =>
      QuotientAddGroup.mk' L (fun j => if j = i then t else 0))) :
    Y - Y = univ := by
  classical
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set (ι → ℝ)) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set (ι → ℝ)) := hLclosed
  haveI : T2Space ((ι → ℝ) ⧸ L) := inferInstance
  have : CompactSpace ((ι → ℝ) ⧸ L) := compact_quotient_of_isZLattice L
  -- the line lies in the difference set of the lift
  have hline : ((BerendSec4.coord ({i} : Set ι) : Set (ι → ℝ))) ⊆
      ((QuotientAddGroup.mk' L) ⁻¹' Y) - ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    coord_subset_sub_of_weights (hY.preimage QuotientAddGroup.continuous_mk)
      hinv1 hinv2 hw hc hd0 hd1 hind hlam hmu hacc
  -- and so does every lattice translate of it
  have hsat := coord_add_lattice_subset_sub (lSaturated_preimage L Y) hline
  -- projection: the whole dense family is in `Y - Y`
  have hrange : Set.range (fun t : ℝ =>
      QuotientAddGroup.mk' L (fun j => if j = i then t else 0)) ⊆ Y - Y := by
    rintro _ ⟨t, rfl⟩
    have hmem : (t • e i : ι → ℝ) ∈ ((QuotientAddGroup.mk' L) ⁻¹' Y) -
        ((QuotientAddGroup.mk' L) ⁻¹' Y) := by
      have h := hsat (t • e i) (Submodule.smul_mem _ t (e_mem_coord i)) 0 L.zero_mem
      simpa using h
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hmem
    rw [Set.mem_preimage] at ha hb
    have hdiff : (QuotientAddGroup.mk' L) a - (QuotientAddGroup.mk' L) b =
        (QuotientAddGroup.mk' L) (fun j => if j = i then t else 0) := by
      rw [← map_sub, hab, smul_e]
    change (QuotientAddGroup.mk' L) (fun j => if j = i then t else 0) ∈ Y - Y
    rw [← hdiff]
    exact Set.sub_mem_sub ha hb
  -- `Y - Y` is closed, and the range is dense
  have hclosed : IsClosed (Y - Y) := BerendMinimal.isClosed_sub hY
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense.closure_range]
  exact closure_minimal hrange hclosed

/-! ## 5. Axiom audit -/

/-- Iterating a weighted diagonal dilation `diag (u ^ w)` `k` times multiplies
the point by `(u ^ k) ^ w` coordinatewise. -/
theorem iterate_diag_pow (u : ℝ) (w : ι → ℕ) (k : ℕ) (x : ι → ℝ) :
    (BerendSec4.diag (fun i => u ^ (w i)))^[k] x
      = fun i => (u ^ k) ^ (w i) * x i := by
  induction k with
  | zero =>
      funext i
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i
      simp only [BerendSec4.diag_apply, pow_succ]
      ring

/-- Membership of the iterate. -/
theorem iterate_mem_of_invariant {E : Set (ι → ℝ)} {u : ℝ} {w : ι → ℕ}
    (hinv : ∀ x ∈ E, BerendSec4.diag (fun i => u ^ (w i)) x ∈ E)
    (k : ℕ) {x : ι → ℝ} (hx : x ∈ E) :
    (fun i => (u ^ k) ^ (w i) * x i) ∈ E := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      have hmem := hinv _ ih
      have hfun : (BerendSec4.diag (fun i => u ^ (w i)))
          (fun i => (u ^ k) ^ (w i) * x i) = fun i => (u ^ (k + 1)) ^ (w i) * x i := by
        funext i
        simp only [BerendSec4.diag_apply, pow_succ]
        ring
      rw [hfun] at hmem
      exact hmem

/-- **The radial flow of the equal-rate case.**  Let `E` be closed and invariant
under the two weighted diagonal dilations `diag (c ^ w)` and `diag (d ^ w)`, with
`c > 1 > d > 0` multiplicatively independent (`log c / log d` irrational) and
`w` a fixed weight vector.  Then `E` is invariant under the *whole* positive
radial flow `x ↦ (s ^ (w i) * x i)` (`s > 0`).

This is the step after Berend's Lemma 4.4: once the logarithmic growth-rate
vectors of the family on the minimal coordinate set are proportional, the
multipliers are powers of one weight vector, and multiplicatively independent
scalars generate a dense set of radial factors, so closedness upgrades the
semigroup action to the full flow. -/
theorem radial_flow_mem {E : Set (ι → ℝ)} (hE : IsClosed E) {w : ι → ℕ} {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1)
    (hirr : Irrational (Real.log c / Real.log d))
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (w i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (w i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) {s : ℝ} (hs : 0 < s) :
    (fun i => s ^ (w i) * x i) ∈ E := by
  classical
  -- the semigroup orbit: every `(c ^ m * d ^ n) ^ w * x` is in `E`
  have hmem : ∀ m n : ℕ, (fun i => (c ^ m * d ^ n) ^ (w i) * x i) ∈ E := by
    intro m n
    have h1 : (fun i => (c ^ m) ^ (w i) * x i) ∈ E :=
      iterate_mem_of_invariant hinv1 m hx
    have h2 : (fun i => (d ^ n) ^ (w i) * ((c ^ m) ^ (w i) * x i)) ∈ E :=
      iterate_mem_of_invariant hinv2 n h1
    have hfun : (fun i => (d ^ n) ^ (w i) * ((c ^ m) ^ (w i) * x i))
        = fun i => (c ^ m * d ^ n) ^ (w i) * x i := by
      funext i
      rw [mul_pow]
      ring
    rwa [hfun] at h2
  -- a sequence of radial factors converging to `s`
  have hseq : ∀ k : ℕ, ∃ m n : ℕ, |s - c ^ m * d ^ n| < 1 / ((k : ℝ) + 1) :=
    fun k => BerendRankTwo.exists_pow_mul_pow_near hc hd0 hd1 hirr hs (by positivity)
  choose m n hmn using hseq
  have htend : Tendsto (fun k : ℕ => c ^ (m k) * d ^ (n k)) atTop (𝓝 s) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    have hKε : 1 < (K : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hK
      linarith
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have h1 : |s - c ^ (m k) * d ^ (n k)| < 1 / ((k : ℝ) + 1) := hmn k
    have hk' : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith
    have h3 : 1 / ((K : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- continuity of the radial action at `s > 0`
  have hcont : Tendsto (fun t : ℝ => fun i => t ^ (w i) * x i) (𝓝 s)
      (𝓝 (fun i => s ^ (w i) * x i)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact ((continuousAt_id.pow (w i)).mul_const (x i))
  exact hE.mem_of_tendsto (hcont.comp htend)
    (Filter.Eventually.of_forall fun k => hmem (m k) (n k))


/-- **The radial flow from corrected (B3).**  Same statement as `radial_flow_mem`,
with the arithmetic hypothesis in Berend's exponent-independence form: no
nontrivial integer power of `c` equals an integer power of `d`. -/
theorem radial_flow_mem_of_indep {E : Set (ι → ℝ)} (hE : IsClosed E) {w : ι → ℕ} {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (w i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (w i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) {s : ℝ} (hs : 0 < s) :
    (fun i => s ^ (w i) * x i) ∈ E :=
  radial_flow_mem hE hc hd0 hd1
    (BerendRankTwo.irrational_log_div_log_of_indep (lt_trans zero_lt_one hc) hd0 hind)
    hinv1 hinv2 hx hs

/-- **The whole positive ray through a point of `E` lies in `E`.** -/
theorem radial_ray_subset {E : Set (ι → ℝ)} (hE : IsClosed E) {w : ι → ℕ} {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun i => c ^ (w i)) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun i => d ^ (w i)) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) :
    (fun s : ℝ => fun i => s ^ (w i) * x i) '' (Set.Ioi 0) ⊆ E := by
  rintro _ ⟨s, hs, rfl⟩
  exact radial_flow_mem_of_indep hE hc hd0 hd1 hind hinv1 hinv2 hx hs


/-! ## 6. The conformal (scalar) case: every line through a point of `E` is in `E - E` -/

/-- **The scalar case of the minimal accumulating pair.**  If the two family
elements act on the minimal coordinate subspace as *scalars* `c · id` and
`d · id` (`c > 1 > d > 0` multiplicatively independent) — the conformal case left
over by Berend's Lemma 4.4, e.g. the conjugate pair of a complex place — then the
whole line through any point of `E` lies in `E - E`.

Proof: the slice `A = {t : t • x ∈ E}` is closed, contains `1`, and is invariant
under `t ↦ c t` and `t ↦ d t`, so the accepted one-dimensional theorem
`BerendRankTwo.sub_eq_univ_of_invariant_of_indep` gives `A - A = ℝ`; every
`t • x` is thus a difference of two points of `E`. -/
theorem line_subset_sub_of_scalar {E : Set (ι → ℝ)} (hE : IsClosed E) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ E, BerendSec4.diag (fun _ : ι => c) x ∈ E)
    (hinv2 : ∀ x ∈ E, BerendSec4.diag (fun _ : ι => d) x ∈ E)
    {x : ι → ℝ} (hx : x ∈ E) :
    (Submodule.span ℝ {x} : Set (ι → ℝ)) ⊆ E - E := by
  classical
  intro y hy
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  by_cases hx0 : x = 0
  · subst hx0
    simp only [smul_zero]
    exact Set.mem_sub.2 ⟨0, hx, 0, hx, by simp⟩
  set A : Set ℝ := {t : ℝ | t • x ∈ E} with hA
  have hAclosed : IsClosed A := hE.preimage (continuous_id.smul continuous_const)
  have hAexp : ∀ t ∈ A, c * t ∈ A := by
    intro t ht
    have hc1 : BerendSec4.diag (fun _ : ι => c) (t • x) = c • (t • x) := by
      funext i
      simp [BerendSec4.diag_apply, smul_eq_mul]
    have hE' : c • (t • x) ∈ E := hc1 ▸ hinv1 _ ht
    simpa [hA, smul_smul, mul_comm] using hE'
  have hAcon : ∀ t ∈ A, d * t ∈ A := by
    intro t ht
    have hc1 : BerendSec4.diag (fun _ : ι => d) (t • x) = d • (t • x) := by
      funext i
      simp [BerendSec4.diag_apply, smul_eq_mul]
    have hE' : d • (t • x) ∈ E := hc1 ▸ hinv2 _ ht
    simpa [hA, smul_smul, mul_comm] using hE'
  have h1 : (1 : ℝ) ∈ A := by
    show (1 : ℝ) • x ∈ E
    simpa using hx
  have hAA : A - A = Set.univ :=
    BerendRankTwo.sub_eq_univ_of_invariant_of_indep hc hd0 hd1 hind hAclosed hAexp hAcon h1
      one_ne_zero
  have hmem : t ∈ A - A := by rw [hAA]; exact Set.mem_univ t
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hmem
  refine Set.mem_sub.2 ⟨a • x, ha, b • x, hb, ?_⟩
  rw [← sub_smul, hab]


/-- **The conformal case of stage C on the torus.**  If the family acts on the
minimal coordinate subspace by *scalars* `c · id`, `d · id` (`c > 1 > d > 0`,
multiplicatively independent), the lift of `Y` contains a point `x`, and the
projection of the line `ℝ x` is dense in the torus, then `Y - Y` is the whole
torus.

Proof: `line_subset_sub_of_scalar` puts every `t • x` in `E - E`, hence its class
in `Y - Y`; the classes `π (t • x)` are dense and `Y - Y` is closed. -/
theorem torus_sub_eq_univ_of_scalar {L : AddSubgroup (ι → ℝ)}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    {Y : Set ((ι → ℝ) ⧸ L)} (hY : IsClosed Y) {c d : ℝ}
    (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (hind : MulIndep c d)
    (hinv1 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => c) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hinv2 : ∀ x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y,
      BerendSec4.diag (fun _ : ι => d) x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    {x : ι → ℝ} (hx : x ∈ (QuotientAddGroup.mk' L) ⁻¹' Y)
    (hdense : DenseRange (fun t : ℝ => QuotientAddGroup.mk' L (t • x))) :
    Y - Y = univ := by
  classical
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set (ι → ℝ)) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set (ι → ℝ)) := hLclosed
  haveI : T2Space ((ι → ℝ) ⧸ L) := inferInstance
  have : CompactSpace ((ι → ℝ) ⧸ L) := compact_quotient_of_isZLattice L
  have hline : (Submodule.span ℝ {x} : Set (ι → ℝ)) ⊆
      ((QuotientAddGroup.mk' L) ⁻¹' Y) - ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
    line_subset_sub_of_scalar (hY.preimage QuotientAddGroup.continuous_mk)
      hc hd0 hd1 hind hinv1 hinv2 hx
  have hrange : Set.range (fun t : ℝ => QuotientAddGroup.mk' L (t • x)) ⊆ Y - Y := by
    rintro _ ⟨t, rfl⟩
    have hmem : (t • x : ι → ℝ) ∈ ((QuotientAddGroup.mk' L) ⁻¹' Y) -
        ((QuotientAddGroup.mk' L) ⁻¹' Y) :=
      hline (Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_singleton x)))
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hmem
    rw [Set.mem_preimage] at ha hb
    have hdiff : (QuotientAddGroup.mk' L) a - (QuotientAddGroup.mk' L) b =
        (QuotientAddGroup.mk' L) (t • x) := by
      rw [← map_sub, hab]
    change (QuotientAddGroup.mk' L) (t • x) ∈ Y - Y
    rw [← hdiff]
    exact Set.sub_mem_sub ha hb
  have hclosed : IsClosed (Y - Y) := BerendMinimal.isClosed_sub hY
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hdense.closure_range]
  exact closure_minimal hrange hclosed

#print axioms mulIndep_pow
#print axioms coord_subset_sub_of_weights
#print axioms coord_add_lattice_subset_sub
#print axioms torus_sub_eq_univ_of_acc_coord
#print axioms radial_flow_mem
#print axioms radial_flow_mem_of_indep
#print axioms radial_ray_subset
#print axioms line_subset_sub_of_scalar
#print axioms torus_sub_eq_univ_of_scalar

end BerendModulus
end CubicTwoStage
