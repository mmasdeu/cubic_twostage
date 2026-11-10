/-
# Berend §4: the full-cone accumulation point (plan step C.4, first half)

This file continues `CubicTwoStage/BerendSec4.lean`.  That module stops at
`exists_minimal_and_expanding`: a closed invariant set `E ⊆ ι → ℝ` that
accumulates at `0` contains a *minimal* accumulating coordinate set `S`, and
some single family member `diag μ` is uniformly expanding on all of `S`
(`1 < |μ i|` for `i ∈ S`).

Plan §C.4 then asks for the cone/open-neighbourhood argument.  Here is the
first, genuinely elementary half of it, proved unconditionally:

* `mem_cone` and friends: the **full cone** `cone S` over a coordinate set,
  i.e. the points of the coordinate subspace `coord S` all of whose `S`
  coordinates are nonzero.  `mem_coord_erase_iff` identifies it as the
  complement, inside `coord S`, of the union of the *proper* coordinate
  subspaces `coord (S.erase i)`.
* `acc_cone`: **minimality of `S` makes `0` an accumulation point of the cone
  points of `E`.**  This is the first use of minimality in the cone argument:
  if points of `E ∩ coord S` tending to `0` had a vanishing coordinate `i ∈ S`
  at arbitrarily small scales, those points would live in the smaller
  coordinate subspace `coord (S.erase i)`, where — by minimality — the norm is
  bounded below.  Hence eventually *every* `S` coordinate is nonzero: a point
  of the invariant set in a full open cone, at every scale.
* `exists_mem_cone_ge` / `exists_mem_cone_annulus`: *expansion* pushes such a
  cone point back up to any prescribed scale, with the annulus bound
  `a ≤ ‖v‖ ≤ N a` supplied by a Lipschitz constant `N` of `diag μ`.  This is
  the "compactness of coefficient annuli" half of §C.4, and it uses the
  expanding family member produced by `exists_minimal_and_expanding`.
* `exists_minimal_and_expanding_cone`: §C.2 + §C.3 + the two steps above, in
  the exact form the remaining (deep) part of §C.4 consumes.

## What is *not* here, and a sharp obstruction

The second half of §C.4 — from a cone point to a *nonempty open subset* of
`coord S` — is **not** a consequence of the configuration that
`exists_minimal_and_expanding` produces, because that configuration contains
Furstenberg's `×2 ×3` theorem as a special case.  This file records the
obstruction formally:

`diagonal_counterexample` exhibits `E = {x : Fin 2 → ℝ // x 0 = x 1}` with the
single multiplier `diag (fun _ => 2)`: `E` is closed, invariant, `0` is a
non-isolated point of it, `S = univ` is the unique minimal accumulating
coordinate set, `diag 2` is uniformly expanding on it, and yet `interior E = ∅`
(`E ≠ coord univ = univ`).  So the missing ingredient for the openness step is
*not* "one expanding multiplier on a minimal accumulating coordinate set": it
is the rational independence of (B3) — in dimension one, the openness step
literally *is* the `×2 ×3` theorem.  Consequently any correct rendering of
§C.4's openness half must consume (B3) (Berend's condition (3)), and §C.5's
rank-two rigidity is where the depth of stage C lives.

Nothing here uses an axiom, and nothing is `sorry`.  Imports only
`CubicTwoStage.BerendSec4`.

## The two barriers, and where the deep content must live

* §7 `diagonal_counterexample`: minimality plus one uniformly expanding family
  member does **not** give an interior point, so the openness half of §C.4
  must consume (B3).
* §8 `halfLine_counterexample`: in the *linear* model `ι → ℝ` the whole
  conclusion `E = coord S` is false, with (B1), (B2) and (B3) all satisfied
  (`irreducible_charpoly_two_int`, `two_zpow_eq_three_zpow`).  Stage C is
  therefore a statement about expansion *wrapping around* the lattice, i.e.
  about `Pt ⧸ L`; the bridge from the torus to its lift is
  `acc_preimage_quotient`.
-/
import CubicTwoStage.BerendSec4

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendSec4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The full cone over a coordinate set -/

/-- The **full cone** over the coordinate set `S`: the points of the coordinate
subspace `coord S` whose `S`-coordinates are all nonzero.

This is Berend's "point of the invariant set in a full open cone" (plan §C.4):
in the diagonal model the cone is invariant under every `diag lam` with nonzero
multipliers, and the remaining (deep) part of §C.4 has to upgrade a point of
this cone to an interior point. -/
def cone (S : Finset ι) : Set (ι → ℝ) :=
  {x | x ∈ coord (S : Set ι) ∧ ∀ i ∈ S, x i ≠ 0}

theorem mem_cone {S : Finset ι} {x : ι → ℝ} :
    x ∈ cone S ↔ x ∈ coord (S : Set ι) ∧ ∀ i ∈ S, x i ≠ 0 := Iff.rfl

theorem cone_subset_coord (S : Finset ι) : cone S ⊆ coord (S : Set ι) :=
  fun _ hx => hx.1

theorem zero_not_mem_cone {S : Finset ι} (hS : S.Nonempty) : (0 : ι → ℝ) ∉ cone S := by
  obtain ⟨i, hi⟩ := hS
  exact fun h => h.2 i hi rfl

/-- `cone S` is the complement, inside `coord S`, of all the *proper* coordinate
subspaces `coord (S.erase i)` (`i ∈ S`).  This is the form in which minimality of
`S` is consumed: a point of `E ∩ coord S` that lies in no proper coordinate
subspace has all its `S`-coordinates nonzero. -/
theorem mem_coord_erase_iff {S : Finset ι} {x : ι → ℝ} (hx : x ∈ coord (S : Set ι))
    {i : ι} : x ∈ coord ((S.erase i : Finset ι) : Set ι) ↔ x i = 0 := by
  constructor
  · intro h
    exact h i (by simp)
  · intro h j hj
    by_cases hji : j = i
    · subst hji; exact h
    · exact hx j fun hjS => hj (Finset.mem_erase.2 ⟨hji, hjS⟩)

theorem diag_mem_cone (lam : ι → ℝ) {S : Finset ι} (hne : ∀ i ∈ S, lam i ≠ 0)
    {x : ι → ℝ} (hx : x ∈ cone S) : diag lam x ∈ cone S := by
  refine ⟨diag_mem_coord lam hx.1, fun i hi => ?_⟩
  rw [diag_apply]
  exact mul_ne_zero (hne i hi) (hx.2 i hi)

/-! ## 2. `Acc` in the empty coordinate set -/

/-- Nothing accumulates at `0` inside the coordinate subspace `coord ∅ = {0}`. -/
theorem not_acc_empty {E : Set (ι → ℝ)} : ¬ Acc E (∅ : Finset ι) := by
  intro h
  obtain ⟨u, -, hu, hune, -⟩ := acc_iff.1 h 1 one_pos
  exact hune (funext fun i => hu i (by simp))

/-- An accumulating coordinate set is nonempty. -/
theorem acc_nonempty {E : Set (ι → ℝ)} {S : Finset ι} (h : Acc E S) : S.Nonempty := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact absurd (hS ▸ h) not_acc_empty
  · exact hS

/-! ## 3. Minimality gives a scale-free lower bound off every proper coordinate
subspace -/

/-- **Minimality, in the form the cone argument uses.**  If `S` is minimal among
the coordinate sets in which `E` accumulates, then for `i ∈ S` the nonzero
points of `E` inside the smaller coordinate subspace `coord (S.erase i)` are
bounded away from `0`. -/
theorem exists_lower_bound_erase {E : Set (ι → ℝ)} {S : Finset ι}
    (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') {i : ι} (hi : i ∈ S) :
    ∃ d : ℝ, 0 < d ∧ ∀ v : ι → ℝ, v ∈ E →
      v ∈ coord ((S.erase i : Finset ι) : Set ι) → v ≠ 0 → d ≤ ‖v‖ :=
  not_acc_iff.1 (hmin (S.erase i) (Finset.erase_ssubset hi))

/-! ## 4. The cone accumulation lemma (plan §C.4, first half) -/

/-- **Berend §4, C.4, cone step.**  Let `E` accumulate at `0` inside the
coordinate subspace `coord S`, and let `S` be minimal with that property.  Then
the cone points of `E` also accumulate at `0`: for every `ε > 0` there is a
nonzero `v ∈ E ∩ cone S` with `‖v‖ < ε`.

Proof: take `u ∈ E ∩ coord S`, `u ≠ 0`, `‖u‖ < ε`.  If `u i = 0` for some
`i ∈ S`, then `u ∈ coord (S.erase i)`, so minimality bounds `‖u‖` from below by
some `d i > 0`; choosing `‖u‖ < min d` as well rules this out.  (Neither
closedness of `E` nor invariance is needed: this is pure minimality.) -/
theorem acc_cone {E : Set (ι → ℝ)} {S : Finset ι} (hacc : Acc E S)
    (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') :
    ∀ ε : ℝ, 0 < ε → ∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ v ≠ 0 ∧ ‖v‖ < ε := by
  classical
  have hSne := acc_nonempty hacc
  have hbound : ∀ i ∈ S, ∃ d : ℝ, 0 < d ∧ ∀ v : ι → ℝ, v ∈ E →
      v ∈ coord ((S.erase i : Finset ι) : Set ι) → v ≠ 0 → d ≤ ‖v‖ :=
    fun i hi => exists_lower_bound_erase hmin hi
  choose d hd using hbound
  -- the minimal lower bound over the finitely many `i ∈ S`
  set D : ι → ℝ := fun i => if h : i ∈ S then d i h else 1 with hD
  obtain ⟨i₀, hi₀, hmin₀⟩ := Finset.exists_min_image S D hSne
  have hDval : ∀ i (h : i ∈ S), D i = d i h := fun i h => by simp [hD, h]
  have hd₀ : 0 < d i₀ hi₀ := (hd i₀ hi₀).1
  intro ε hε
  obtain ⟨u, huE, huS, hune, hult⟩ := acc_iff.1 hacc (min ε (d i₀ hi₀))
    (lt_min hε hd₀)
  refine ⟨u, huE, ⟨huS, fun i hi => ?_⟩, hune, lt_of_lt_of_le hult (min_le_left _ _)⟩
  intro hzero
  have hmem : u ∈ coord ((S.erase i : Finset ι) : Set ι) :=
    (mem_coord_erase_iff huS).2 hzero
  have hle : d i hi ≤ ‖u‖ := (hd i hi).2 u huE hmem hune
  have hle0 : d i₀ hi₀ ≤ d i hi := by
    have := hmin₀ i hi
    rwa [hDval i₀ hi₀, hDval i hi] at this
  have hlt : ‖u‖ < min ε (d i₀ hi₀) := hult
  have := lt_of_lt_of_le hlt (min_le_right ε (d i₀ hi₀))
  linarith

/-- The closure form of `acc_cone`: `0` lies in the closure of the cone points
of `E`, minus `0`. -/
theorem zero_mem_closure_cone {E : Set (ι → ℝ)} {S : Finset ι} (hacc : Acc E S)
    (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') :
    (0 : ι → ℝ) ∈ closure ((E ∩ cone S) \ {0}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hvE, hvc, hvne, hvlt⟩ := acc_cone hacc hmin ε hε
  exact ⟨v, ⟨⟨hvE, hvc⟩, hvne⟩, by simpa [dist_zero_right] using hvlt⟩

/-! ## 5. Expansion along the cone: any prescribed scale -/

/-- **Berend §4, C.4, scale step.**  An expanding member `diag μ` of the family
(`1 < |μ i|` on `S`) carries the cone point of `acc_cone` up to any prescribed
scale `a`, staying inside `E` and inside the cone.  The proof is the "least
iterate landing above `a`" of the paper's Lemma 4.2. -/
theorem exists_mem_cone_ge {E : Set (ι → ℝ)} {S : Finset ι} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, diag lam x ∈ E) (hexp : ∀ i ∈ S, 1 < |lam i|)
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {a : ℝ} (ha : 0 < a) :
    ∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ a ≤ ‖v‖ := by
  classical
  have hSne := acc_nonempty hacc
  obtain ⟨i₀, hi₀⟩ := hSne
  obtain ⟨v₀, hv₀E, hv₀c, hv₀ne, hv₀lt⟩ := acc_cone hacc hmin a ha
  have hlamne : ∀ i ∈ S, lam i ≠ 0 := fun i hi =>
    abs_pos.1 (lt_trans zero_lt_one (hexp i hi))
  have hiter : ∀ k : ℕ, ((diag lam)^[k]) v₀ ∈ E := by
    intro k
    induction k with
    | zero => simpa using hv₀E
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hinv _ ih
  have hcone : ∀ k : ℕ, ((diag lam)^[k]) v₀ ∈ cone S := by
    intro k
    induction k with
    | zero => simpa using hv₀c
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact diag_mem_cone lam hlamne ih
  have hgt : 1 < |lam i₀| := hexp i₀ hi₀
  have hz : 0 < |v₀ i₀| := abs_pos.2 (hv₀c.2 i₀ hi₀)
  have htend : Tendsto (fun k : ℕ => |lam i₀| ^ k * |v₀ i₀|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hz
  obtain ⟨b, hb⟩ := (tendsto_atTop_atTop.1 htend) a
  refine ⟨((diag lam)^[b]) v₀, hiter b, hcone b, ?_⟩
  have hcoord : |lam i₀| ^ b * |v₀ i₀| = ‖(((diag lam)^[b]) v₀) i₀‖ := by
    rw [diag_iterate_apply, Real.norm_eq_abs, abs_mul, abs_pow]
  have h2 : |lam i₀| ^ b * |v₀ i₀| ≤ ‖((diag lam)^[b]) v₀‖ := by
    rw [hcoord]
    exact norm_le_pi_norm _ i₀
  linarith [hb b le_rfl]

/-- **Berend §4, C.4, annulus step**: the cone point can be placed in the
annulus `a ≤ ‖·‖ ≤ N a`, where `N` is any Lipschitz constant of `diag μ`.  This
is exactly the "compactness of coefficient annuli" used in the paper. -/
theorem exists_mem_cone_annulus {E : Set (ι → ℝ)} {S : Finset ι} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, diag lam x ∈ E) (hexp : ∀ i ∈ S, 1 < |lam i|)
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {a N : ℝ} (ha : 0 < a) (hNpos : 0 < N) (hN : ∀ x : ι → ℝ, ‖diag lam x‖ ≤ N * ‖x‖) :
    ∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a := by
  classical
  have hSne := acc_nonempty hacc
  obtain ⟨i₀, hi₀⟩ := hSne
  obtain ⟨v₀, hv₀E, hv₀c, hv₀ne, hv₀lt⟩ := acc_cone hacc hmin a ha
  have hlamne : ∀ i ∈ S, lam i ≠ 0 := fun i hi =>
    abs_pos.1 (lt_trans zero_lt_one (hexp i hi))
  have hiter : ∀ k : ℕ, ((diag lam)^[k]) v₀ ∈ E := by
    intro k
    induction k with
    | zero => simpa using hv₀E
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hinv _ ih
  have hcone : ∀ k : ℕ, ((diag lam)^[k]) v₀ ∈ cone S := by
    intro k
    induction k with
    | zero => simpa using hv₀c
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact diag_mem_cone lam hlamne ih
  have hgt : 1 < |lam i₀| := hexp i₀ hi₀
  have hz : 0 < |v₀ i₀| := abs_pos.2 (hv₀c.2 i₀ hi₀)
  have htend : Tendsto (fun k : ℕ => |lam i₀| ^ k * |v₀ i₀|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hz
  have hex : ∃ k : ℕ, a ≤ ‖((diag lam)^[k]) v₀‖ := by
    obtain ⟨b, hb⟩ := (tendsto_atTop_atTop.1 htend) a
    refine ⟨b, ?_⟩
    have hcoord : |lam i₀| ^ b * |v₀ i₀| = ‖(((diag lam)^[b]) v₀) i₀‖ := by
      rw [diag_iterate_apply, Real.norm_eq_abs, abs_mul, abs_pow]
    have h2 : |lam i₀| ^ b * |v₀ i₀| ≤ ‖((diag lam)^[b]) v₀‖ := by
      rw [hcoord]
      exact norm_le_pi_norm _ i₀
    linarith [hb b le_rfl]
  set k : ℕ := Nat.find hex with hkdef
  have hkspec : a ≤ ‖((diag lam)^[k]) v₀‖ := Nat.find_spec hex
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h] at hkspec
      simp only [Function.iterate_zero, id] at hkspec
      exact absurd hkspec (not_le.2 hv₀lt)
    · exact h
  have hkmin : ‖((diag lam)^[k - 1]) v₀‖ < a := by
    have hlt : k - 1 < k := Nat.sub_one_lt_of_lt hkpos
    exact not_le.1 (Nat.find_min hex hlt)
  refine ⟨((diag lam)^[k]) v₀, hiter k, hcone k, hkspec, ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 hkpos)
  have hstep : ((diag lam)^[k]) v₀ = diag lam (((diag lam)^[m]) v₀) := by
    rw [hm, Function.iterate_succ_apply']
  rw [hstep]
  have hm' : ‖((diag lam)^[m]) v₀‖ < a := by
    have hkm : k - 1 = m := by omega
    rwa [hkm] at hkmin
  exact le_trans (hN _) (le_of_lt (mul_lt_mul_of_pos_left hm' hNpos))

/-! ## 6. Assembled from `exists_minimal_and_expanding` -/

/-- **Plan §C.4, first half, in the configuration of
`exists_minimal_and_expanding`.**  From a closed invariant `E` that accumulates
at `0`, one gets a minimal accumulating coordinate set `S` with an expanding
family member, together with the two cone facts: cone points of `E` accumulate
at `0`, and (by expansion) `E` meets the cone at every prescribed scale.

The remaining, deep part of §C.4 has to turn such a point into an interior point
of `E` in `coord S`; see `diagonal_counterexample` below for the reason this
needs (B3) and not merely the present hypotheses. -/
theorem exists_minimal_and_expanding_cone
    {E : Set (ι → ℝ)} (hE : IsClosed E) (hacc : Acc E Finset.univ)
    {κ : Type*} {fam : κ → ι → ℝ} (hinv : ∀ k, ∀ x ∈ E, diag (fam k) x ∈ E)
    (hB2 : ∀ i : ι, ∃ k : κ, 1 < |fam k i|) {a : ℝ} (ha : 0 < a) :
    ∃ (S : Finset ι) (k : κ), S.Nonempty ∧ Acc E S ∧
      (∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') ∧
      (∀ i ∈ S, 1 < |fam k i|) ∧
      (∀ ε : ℝ, 0 < ε → ∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ v ≠ 0 ∧ ‖v‖ < ε) ∧
      (∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ a ≤ ‖v‖) := by
  obtain ⟨S, hne, hSacc, hSmin, k, hexp⟩ := exists_minimal_and_expanding hE hacc hinv hB2
  exact ⟨S, k, hne, hSacc, hSmin, hexp, acc_cone hSacc hSmin,
    exists_mem_cone_ge (hinv k) hexp hSacc hSmin ha⟩

/-! ## 7. The obstruction: minimality plus one expanding multiplier does not give
an interior point -/

/-- **No accumulation inside a diagonal set.**  If all coordinates of the points
of `E` are equal (a "diagonal" set) and `S` is a *proper* set of coordinates,
then nothing accumulates at `0` in `coord S`: a point of `E ∩ coord S` has all
its coordinates equal to the — vanishing — coordinate outside `S`. -/
theorem acc_false_of_subset_diag {E : Set (ι → ℝ)} {S : Finset ι}
    (hS : S ≠ Finset.univ) (hdiag : ∀ x ∈ E, ∀ i j : ι, x i = x j) : ¬ Acc E S := by
  intro h
  obtain ⟨u, huE, huS, hune, -⟩ := acc_iff.1 h 1 one_pos
  have hex : ∃ i : ι, i ∉ S := by
    by_contra hc
    push Not at hc
    exact hS (Finset.eq_univ_of_forall hc)
  obtain ⟨i, hi⟩ := hex
  have hui : u i = 0 := huS i (by simpa using hi)
  exact hune (funext fun j => by rw [hdiag u huE j i, hui]; rfl)

/-- **The configuration of `exists_minimal_and_expanding` does not force an
interior point.**  Take `E = {x : Fin 2 → ℝ | x 0 = x 1}` and the single
multiplier `diag (fun _ => 2)`.  Then

* `E` is closed, `0` is a non-isolated point of `E`, and `E` is invariant;
* `S = univ` is the unique minimal coordinate set in which `E` accumulates;
* `diag 2` is uniformly expanding on `S` (both coordinates have `|2| > 1`);

and yet `E` has **empty interior**, so the second half of §C.4 ("then in a
nonempty open subset of the selected invariant subspace") fails for reasons that
no amount of annulus compactness can repair: the missing hypothesis is (B3),
the rational independence of two family members.  In dimension one the openness
step is exactly Furstenberg's `×2 ×3` theorem. -/
theorem diagonal_counterexample :
    ∃ (E : Set (Fin 2 → ℝ)) (fam : Unit → Fin 2 → ℝ) (S : Finset (Fin 2)),
      IsClosed E ∧ S.Nonempty ∧ Acc E S ∧
      (∀ S' : Finset (Fin 2), S' ⊂ S → ¬ Acc E S') ∧
      (∀ k, ∀ x ∈ E, diag (fam k) x ∈ E) ∧
      (∃ k, ∀ i ∈ S, 1 < |fam k i|) ∧
      interior E = ∅ := by
  classical
  refine ⟨{x : Fin 2 → ℝ | x 0 = x 1}, fun _ _ => 2, Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- closed: the coincidence set of two continuous coordinate projections
    have h : {x : Fin 2 → ℝ | x 0 = x 1}
        = {x : Fin 2 → ℝ | (fun y => y 0) x = (fun y => y 1) x} := rfl
    rw [h]
    exact isClosed_eq (continuous_apply 0) (continuous_apply 1)
  · exact Finset.univ_nonempty
  · -- `0` is a non-isolated point: the constant points `c` with `c → 0`
    rw [acc_iff]
    intro ε hε
    set c : ℝ := min (ε / 2) (1 / 2) with hc
    have hcpos : 0 < c := lt_min (by positivity) (by norm_num)
    have hcle : c ≤ ε / 2 := min_le_left _ _
    refine ⟨fun _ => c, rfl, fun i hi => absurd hi (by simp), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp only [Pi.zero_apply] at this
      linarith
    · have hle : ‖(fun _ : Fin 2 => c)‖ ≤ |c| := by
        rw [pi_norm_le_iff_of_nonneg (abs_nonneg c)]
        intro i
        simp [Real.norm_eq_abs]
      rw [abs_of_pos hcpos] at hle
      linarith
  · -- minimality: every proper subset of `univ` misses a coordinate
    intro S' hS'
    have hne : S' ≠ Finset.univ := by
      intro h'; rw [h'] at hS'; exact absurd hS' (lt_irrefl _)
    refine acc_false_of_subset_diag hne (fun x hx i j => ?_)
    fin_cases i <;> fin_cases j <;> simp_all
  · -- invariance under `x ↦ 2 • x`
    intro k x hx
    show (diag (fun _ : Fin 2 => (2:ℝ)) x) 0 = (diag (fun _ : Fin 2 => (2:ℝ)) x) 1
    simp only [diag_apply]
    rw [hx]
  · exact ⟨(), fun i _ => by rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]; norm_num⟩
  · -- empty interior: a small displacement of the first coordinate leaves `E`
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_interior_iff_mem_nhds] at hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hx
    set δ : ℝ := min (ε / 2) (1 / 2) with hδ
    have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδlt : δ < ε := by
      have h1 : δ ≤ ε / 2 := min_le_left _ _
      linarith
    set y : Fin 2 → ℝ := fun i => if i = 0 then x 0 + δ else x i with hy
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : y - x = fun i : Fin 2 => if i = 0 then δ else 0 := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp [hy]
        · simp [hy, hi]
      rw [hdiff]
      have hnorm : ‖(fun i : Fin 2 => if i = 0 then δ else (0:ℝ))‖ = |δ| := by
        refine le_antisymm ?_ ?_
        · rw [pi_norm_le_iff_of_nonneg (abs_nonneg δ)]
          intro i
          by_cases hi : i = 0
          · subst hi; simp [Real.norm_eq_abs]
          · simp [hi]
        · calc |δ| = ‖(fun i : Fin 2 => if i = 0 then δ else (0:ℝ)) 0‖ := by simp
            _ ≤ ‖(fun i : Fin 2 => if i = 0 then δ else (0:ℝ))‖ :=
                norm_le_pi_norm (fun i : Fin 2 => if i = 0 then δ else (0:ℝ)) 0
      rw [hnorm, abs_of_pos hδpos]
      exact hδlt
    have hyE : y ∈ {x : Fin 2 → ℝ | x 0 = x 1} := hball hyball
    have hyE' : y 0 = y 1 := hyE
    have hxE : x 0 = x 1 := hball (Metric.mem_ball_self hε)
    have h1 : y 1 = x 1 := by
      simp only [hy]
      rw [if_neg (by norm_num : (1 : Fin 2) ≠ 0)]
    have h0 : y 0 = x 0 + δ := by simp [hy]
    rw [h0, h1] at hyE'
    linarith


/-! ## 8. Why stage C cannot live in the linear model: the half-line barrier

`diagonal_counterexample` refutes the *openness* half of §C.4 inside the
diagonal model.  The next theorem shows something stronger and simpler: the
*conclusion* of stage C (`E = coord S`) is **false** in the linear model
`ι → ℝ` even for the most favourable one-dimensional family, the pair of
multipliers `2` and `3` of Berend's condition (3).  The reason is structural,
not a technicality: in the linear model multiplication by `2` and by `3` only
moves points *away* from `0`, so a closed invariant set can be a half-line;
`0` is then a non-isolated point and all of (B1), (B2), (B3) hold in dimension
one, yet the set is not the whole space.  What stage C really uses is that on
the *torus* expansion wraps around; the corresponding statement for the linear
model must be about the quotient (or about sets invariant under the lattice),
and that is where the `×2 ×3` rigidity of §C.5 enters.

So any formalisation that tries to derive `E = coord S` from
`exists_minimal_and_expanding` alone — or from (B2) plus *one* expanding map in
`ι → ℝ` — is refuted, and the deep content of stage C has to be stated on the
torus `Pt ⧸ L`. -/

/-- Berend's (B1) in dimension one: the multiplier `2` has characteristic
polynomial `X - 2`, which is irreducible (over `ℤ` and over `ℝ`). -/
theorem irreducible_charpoly_two : Irreducible (Polynomial.X - Polynomial.C (2 : ℝ)) :=
  Polynomial.irreducible_X_sub_C 2

/-- The same statement over `ℤ`, which is literally Berend's (B1) in dimension
one: the characteristic polynomial of the lattice endomorphism `n ↦ 2n` of
`ℤ ⊆ ℝ` is `X - 2`, irreducible. -/
theorem irreducible_charpoly_two_int : Irreducible (Polynomial.X - Polynomial.C (2 : ℤ)) :=
  Polynomial.irreducible_X_sub_C 2

/-- Unique factorisation, first form: `2^a = 3^b` for `a b : ℕ` forces both
exponents to vanish. -/
theorem two_pow_eq_three_pow_nat {a b : ℕ} (h : (2 : ℝ) ^ a = (3 : ℝ) ^ b) :
    a = 0 ∧ b = 0 := by
  have hnat : (2 : ℕ) ^ a = 3 ^ b := by exact_mod_cast h
  constructor
  · by_contra ha
    have hd : (2 : ℕ) ∣ 3 ^ b := by
      rw [← hnat]
      exact dvd_pow_self 2 ha
    have h2 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
    omega
  · by_contra hb
    have hd : (3 : ℕ) ∣ 2 ^ a := by
      rw [hnat]
      exact dvd_pow_self 3 hb
    have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega

/-- **Berend's rational independence (B3) for the multipliers `2` and `3`**:
`2^l = 3^k` with `l k : ℤ` forces `l = k = 0`.  This is the arithmetic content
of condition (3) in dimension one, and it is what makes the half-line barrier
`halfLine_counterexample` immune to the objection that the family `{2, 3}` is
rationally dependent. -/
theorem two_zpow_eq_three_zpow {l k : ℤ} (h : (2 : ℝ) ^ l = (3 : ℝ) ^ k) :
    l = 0 ∧ k = 0 := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg l
  · subst hm
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
    · subst hn
      rw [zpow_natCast, zpow_natCast] at h
      obtain ⟨h1, h2⟩ := two_pow_eq_three_pow_nat h
      exact ⟨by omega, by omega⟩
    · subst hn
      rw [zpow_natCast, zpow_neg, zpow_natCast] at h
      have hm0 : m = 0 := by
        by_contra hmne
        have hge : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
          have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hmne
          calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
            _ ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm1
        have hle : ((3 : ℝ) ^ n)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
        linarith
      have hn0 : n = 0 := by
        subst hm0
        simp only [pow_zero] at h
        have h3 : (3 : ℝ) ^ n = 1 := inv_eq_one.1 h.symm
        by_contra hnne
        have := one_lt_pow₀ (by norm_num : (1 : ℝ) < 3) hnne
        linarith
      exact ⟨by omega, by omega⟩
  · subst hm
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
    · subst hn
      rw [zpow_neg, zpow_natCast, zpow_natCast] at h
      have hn0 : n = 0 := by
        by_contra hnne
        have hge : (3 : ℝ) ≤ (3 : ℝ) ^ n := by
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hnne
          calc (3 : ℝ) = (3 : ℝ) ^ 1 := by norm_num
            _ ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn1
        have hle : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        linarith
      have hm0 : m = 0 := by
        subst hn0
        simp only [pow_zero] at h
        have h2 : (2 : ℝ) ^ m = 1 := inv_eq_one.1 h
        by_contra hmne
        have := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hmne
        linarith
      exact ⟨by omega, by omega⟩
    · subst hn
      rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast] at h
      have hinv : (2 : ℝ) ^ m = (3 : ℝ) ^ n := inv_inj.1 h
      obtain ⟨h1, h2⟩ := two_pow_eq_three_pow_nat hinv
      exact ⟨by omega, by omega⟩

/-- **The half-line barrier.**  In the linear one-dimensional model
`ι → ℝ` with `ι = Unit`, the family `{fun _ => 2, fun _ => 3}` has the
following closed invariant set with `0` as a non-isolated point:

`E = {x : Unit → ℝ | 0 ≤ x ()}`.

All the hypotheses of `exists_minimal_and_expanding` hold — `E` is closed,
`0` is a non-isolated point of it, `E` is invariant under both multipliers,
`S = univ` is its unique minimal accumulating coordinate set, and `diag 2` is
uniformly expanding on `S` (Berend's (B2)) — and yet `E ≠ univ = coord univ`.

Consequently stage C (`0` non-isolated ⟹ `E = univ`) is **not** a statement
about the linear model: the missing ingredient is the wrapping of expansion
around the lattice, i.e. the quotient `Pt ⧸ L`.  (Berend's (B3) also holds
here — `2^l = 3^k` with `l k : ℤ` forces `l = k = 0`, see
`two_zpow_eq_three_zpow` — which is exactly why the barrier is not an artefact
of a degenerate family; it is formalised
below as `two_zpow_eq_three_zpow`.) -/
theorem halfLine_counterexample :
    ∃ (E : Set (Unit → ℝ)) (fam : Bool → Unit → ℝ),
      IsClosed E ∧ Acc E Finset.univ ∧
      (∀ k, ∀ x ∈ E, diag (fam k) x ∈ E) ∧
      (∀ i : Unit, ∃ k : Bool, 1 < |fam k i|) ∧
      Irreducible (Polynomial.X - Polynomial.C (2 : ℤ)) ∧
      (∀ l k : ℤ, (2 : ℝ) ^ l = (3 : ℝ) ^ k → l = 0 ∧ k = 0) ∧
      E ≠ Set.univ := by
  classical
  refine ⟨{x : Unit → ℝ | 0 ≤ x ()}, fun b _ => if b then 3 else 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- closed: a half-space, the preimage of `[0, ∞)`
    have h : {x : Unit → ℝ | 0 ≤ x ()}
        = (fun x : Unit → ℝ => x ()) ⁻¹' Set.Ici (0 : ℝ) := rfl
    rw [h]
    exact isClosed_Ici.preimage (continuous_apply ())
  · -- `0` is a non-isolated point: the nonzero points `ε/2`
    rw [acc_iff]
    intro ε hε
    set c : ℝ := ε / 2 with hc
    have hcpos : 0 < c := by positivity
    refine ⟨fun _ => c, ?_, fun i hi => absurd hi (by simp), ?_, ?_⟩
    · show (0 : ℝ) ≤ c
      exact le_of_lt hcpos
    · intro h
      have := congrFun h ()
      simp only [Pi.zero_apply] at this
      linarith
    · have hle : ‖(fun _ : Unit => c)‖ ≤ |c| := by
        rw [pi_norm_le_iff_of_nonneg (abs_nonneg c)]
        intro i
        simp [Real.norm_eq_abs]
      rw [abs_of_pos hcpos] at hle
      linarith
  · -- invariance under the multipliers `2` and `3`
    intro k x hx
    show (0 : ℝ) ≤ diag (fun _ : Unit => if k then 3 else 2) x ()
    rw [diag_apply]
    have hpos : (0 : ℝ) < (if k then 3 else 2) := by
      by_cases hk : k
      · rw [if_pos hk]; norm_num
      · rw [if_neg hk]; norm_num
    exact mul_nonneg (le_of_lt hpos) hx
  · -- (B2): both multipliers expand the only coordinate
    intro i
    exact ⟨false, by norm_num⟩
  · -- (B1) in dimension one
    exact irreducible_charpoly_two_int
  · -- (B3) in dimension one
    exact fun l k h => two_zpow_eq_three_zpow h
  · -- not everything: the negative half-line is missed
    intro h
    have hmem : (fun _ : Unit => (-1 : ℝ)) ∈ {x : Unit → ℝ | 0 ≤ x ()} := by
      rw [h]; exact Set.mem_univ _
    have h1 : (0 : ℝ) ≤ (-1 : ℝ) := hmem
    norm_num at h1

/-! ## 9. Glue, the self-contained annulus form, and the torus-lift bridge -/

/-- `Acc` is monotone in the set. -/
theorem acc_mono {E E' : Set (ι → ℝ)} {S : Finset ι} (hE : Acc E S) (hsub : E ⊆ E') :
    Acc E' S := by
  rw [acc_iff] at hE ⊢
  intro ε hε
  obtain ⟨v, hvE, hvS, hvne, hvlt⟩ := hE ε hε
  exact ⟨v, hsub hvE, hvS, hvne, hvlt⟩

/-- `Acc` passes from a set to its closure. -/
theorem acc_closure {E : Set (ι → ℝ)} {S : Finset ι} (h : Acc E S) : Acc (closure E) S :=
  acc_mono h subset_closure


/-- **The annulus form with the Lipschitz constant supplied automatically.**
No constant has to be provided by the caller: `exists_norm_bound` produces one. -/
theorem exists_mem_cone_annulus' {E : Set (ι → ℝ)} {S : Finset ι} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, diag lam x ∈ E) (hexp : ∀ i ∈ S, 1 < |lam i|)
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {a : ℝ} (ha : 0 < a) :
    ∃ (N : ℝ) (v : ι → ℝ), 1 ≤ N ∧ v ∈ E ∧ v ∈ cone S ∧ a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a := by
  obtain ⟨N, hN1, hN⟩ := exists_norm_bound (ι := ι) lam
  obtain ⟨v, hvE, hvc, hge, hle⟩ :=
    exists_mem_cone_annulus hinv hexp hacc hmin ha (lt_of_lt_of_le zero_lt_one hN1) hN
  exact ⟨N, v, hN1, hvE, hvc, hge, hle⟩

/-- **Plan §C.4, first half, with the annulus bound**, in the output
configuration of `exists_minimal_and_expanding`: a minimal accumulating
coordinate set `S`, an expanding family member, and a point of `E` in the full
cone over `S` whose norm lies in `[a, N a]` for a single absolute constant `N`.
This is the exact form in which the "compactness of coefficient annuli" step of
Berend §4 is consumed. -/
theorem exists_minimal_and_expanding_cone_annulus
    {E : Set (ι → ℝ)} (hE : IsClosed E) (hacc : Acc E Finset.univ)
    {κ : Type*} {fam : κ → ι → ℝ} (hinv : ∀ k, ∀ x ∈ E, diag (fam k) x ∈ E)
    (hB2 : ∀ i : ι, ∃ k : κ, 1 < |fam k i|) {a : ℝ} (ha : 0 < a) :
    ∃ (S : Finset ι) (k : κ) (N : ℝ), S.Nonempty ∧ Acc E S ∧
      (∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S') ∧ (∀ i ∈ S, 1 < |fam k i|) ∧ 1 ≤ N ∧
      (∃ v : ι → ℝ, v ∈ E ∧ v ∈ cone S ∧ a ≤ ‖v‖ ∧ ‖v‖ ≤ N * a) := by
  obtain ⟨S, hne, hSacc, hSmin, k, hexp⟩ := exists_minimal_and_expanding hE hacc hinv hB2
  obtain ⟨N, v, hN1, hvE, hvc, hge, hle⟩ :=
    exists_mem_cone_annulus' (hinv k) hexp hSacc hSmin ha
  exact ⟨S, k, N, hne, hSacc, hSmin, hexp, hN1, v, hvE, hvc, hge, hle⟩

/-- **Bridge from the torus to its lift.**  If `0` is a non-isolated point of a
set `E` of the quotient `(ι → ℝ) ⧸ L` — the honest setting of stage C, see
`halfLine_counterexample` — then `0` is a non-isolated point of the preimage of
`E` in the linear model `ι → ℝ`, which is where the cone machinery of §1–§6
lives.

This is the transport that any completion of stage C has to perform first; the
lift additionally satisfies `F + L = F`, which is exactly the property that
rules out the half-line of `halfLine_counterexample`. -/
theorem acc_preimage_quotient {L : AddSubgroup (ι → ℝ)}
    [NormedAddCommGroup ((ι → ℝ) ⧸ L)]
    {E : Set ((ι → ℝ) ⧸ L)}
    (h : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, x ≠ 0 ∧ ‖x‖ < ε) :
    Acc ((QuotientAddGroup.mk' L) ⁻¹' E) Finset.univ := by
  rw [acc_iff]
  intro ε hε
  obtain ⟨x, hxE, hxne, hxlt⟩ := h (ε / 2) (by positivity)
  obtain ⟨y, hyx, hynorm⟩ := QuotientAddGroup.exists_norm_mk_lt (S := L) x (by positivity : (0:ℝ) < ε/2)
  have hyE : y ∈ (QuotientAddGroup.mk' L) ⁻¹' E := by
    rw [Set.mem_preimage]
    have h2 : (QuotientAddGroup.mk' L) y = x := hyx
    rw [h2]
    exact hxE
  have hyne : y ≠ 0 := by
    intro h0
    apply hxne
    calc x = (↑y : (ι → ℝ) ⧸ L) := hyx.symm
      _ = ((0 : ι → ℝ) : (ι → ℝ) ⧸ L) := by rw [h0]
      _ = 0 := rfl
  refine ⟨y, hyE, fun i hi => absurd hi (by simp), hyne, ?_⟩
  linarith

end BerendSec4

end CubicTwoStage
