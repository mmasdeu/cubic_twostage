/-
# Berend §5 (Trans. AMS **280** (1983), 509–532): the final propagation

This module formalizes the *last* part of the sufficiency proof of Berend's
Theorem 2.1, i.e. the passage from sets with `0` as a non-isolated point
(§4 = `BerendDichotomy.ZeroNonisolatedFull`) to arbitrary closed invariant sets.
It follows the published argument of Berend, §5 (pp. 529–531), which is *not*
the difference-set statement `NoProperFullDiffSet` of `BEREND_PROOF_PLAN.md`
§D.5.  In Berend's own text the final step runs:

* `E` infinite, closed, `Σ`-invariant.  Let `E'` be the set of accumulation
  points of `E`.  By Lemma 5.1 (an epimorphism of `T^r` has finite kernel, all
  of whose elements are torsion) `E'` is again `Σ`-invariant; it is closed, and
  nonempty because `E` is infinite and closed in a compact space.
* `E'` contains a `Σ`-minimal subset `M`; by Proposition 5.1 `M` is a finite set
  of **torsion** elements.  Pick `x ∈ E'` of order `l`.
* Then `lE` is closed, `Σ`-invariant, and `0` is a non-isolated point of it, so
  §4 gives `lE = T^r`.  This yields `T^r = E + T^r[l]` (given `y`, hit `l • y`
  by `l • e`, then `y - e` is `l`-torsion), a **finite** union of closed sets.
* Baire: one of the translates `E + k` has nonempty interior, hence so does `E`.
* An ergodic — here: topologically transitive — member of `Σ` then forces
  `E = T^r`.

## What is proved here

* §1 the `n`-fold multiple endomorphism `nsmulEnd`;
* §2 the accumulation set `derivedSet E`, its closedness, nonemptiness for
  infinite closed `E`, and its invariance under a member with finite kernel;
* §3 a torsion accumulation point `x` of `E` makes `0` a non-isolated point of
  `n • E`;
* §4 `n • E = univ` plus finiteness of the `n`-torsion subgroup gives
  `E` nonempty interior (Baire, `dense_biUnion_interior_of_closed`);
* §5 closed invariant + nonempty interior + one topologically transitive member
  gives `E = univ`;
* §6 the assembly `dichotomy_of_stageI_of_minimal_torsion`: **Stage I + "every
  minimal closed invariant set contains a torsion point" ⇒ Berend's dichotomy**,
  and its corollary `noProperFullDiffSet_of_stageI_of_minimal_torsion`: the
  residual statement of `BEREND_PROOF_PLAN.md` §D.5 is *derived*, so it is not a
  second deep obligation;
* §7 Berend Lemma 5.2 (`torsion_of_finite_invariant`) and the variant
  `dichotomy_of_stageI_of_minimal_finite`, which needs only "minimal sets are
  finite" plus the spectral input "`g^m - g^n` has finite kernel for `m ≠ n`";
* §8 `finite_of_minimal_of_nsmul_eq_zero`: a minimal set containing one torsion
  point is finite, so "minimal sets contain a torsion point" and "minimal sets are
  finite sets of torsion elements" (Proposition 5.1) are equivalent given
  finiteness of the torsion subgroups.

The single deep input left is Berend's Proposition 5.1 (`hmin` below); the
difference-set residual `NoProperFullDiffSet` is *not* used and is not needed.
See `BEREND_SEC5_NOTES.md` for the paper's own §4/§5 structure and the precise
list of remaining obligations.
-/
import CubicTwoStage.BerendDichotomy

open Set Filter Topology
open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendSec5

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {ι : Type*} {F : ι → G →+ G}

/-! ## 1. The `n`-fold multiple endomorphism -/

/-- `x ↦ n • x` as an additive endomorphism of `G`. -/
def nsmulEnd (n : ℕ) : G →+ G where
  toFun := fun x => n • x
  map_zero' := nsmul_zero n
  map_add' := fun a b => nsmul_add a b n

@[simp] theorem nsmulEnd_apply (n : ℕ) (x : G) : nsmulEnd n x = n • x := rfl

theorem continuous_nsmulEnd (n : ℕ) : Continuous (nsmulEnd (G := G) n) :=
  continuous_nsmul n

/-! ## 2. The set of accumulation points -/

/-- The accumulation points of `E` that lie in `E`.  For closed `E` this is
Berend's `E'` (§5). -/
def derivedSet (E : Set G) : Set G := E ∩ {x | AccPt x (𝓟 E)}

theorem mem_derivedSet {E : Set G} {x : G} :
    x ∈ derivedSet E ↔ x ∈ E ∧ AccPt x (𝓟 E) := Iff.rfl

theorem derivedSet_subset (E : Set G) : derivedSet E ⊆ E := inter_subset_left

/-- **An infinite closed set has an accumulation point in itself** (Berend §5,
first line of the final argument). -/
theorem derivedSet_nonempty {E : Set G} (hE : IsClosed E) (hinf : E.Infinite) :
    (derivedSet E).Nonempty := by
  obtain ⟨a, ha, hacc⟩ := BerendMinimal.exists_accPt_of_infinite_isClosed hE hinf
  exact ⟨a, ha, hacc⟩

/-- **The accumulation set of a closed set is closed.** -/
theorem isClosed_derivedSet {E : Set G} (hE : IsClosed E) : IsClosed (derivedSet E) := by
  have hopen : IsOpen (derivedSet E)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    by_cases hxE : x ∈ E
    · have hnot : ¬ AccPt x (𝓟 E) := fun h => hx ⟨hxE, h⟩
      have hnot' := hnot
      rw [accPt_iff_nhds] at hnot'
      push Not at hnot'
      obtain ⟨U, hU, hUsub⟩ := hnot'
      refine Filter.mem_of_superset (interior_mem_nhds.mpr hU) ?_
      intro y hy hy'
      have hyU : y ∈ U := interior_subset hy
      have hyx : y = x := hUsub y ⟨hyU, hy'.1⟩
      rw [hyx] at hy'
      exact hnot hy'.2
    · refine Filter.mem_of_superset (hE.isOpen_compl.mem_nhds hxE) ?_
      intro y hy hy'
      exact hy (derivedSet_subset E hy')
  exact isOpen_compl_iff.mp hopen

/-- **Accumulation points propagate forward through a member with finite
kernel**: if `x` is an accumulation point of an `A`-invariant `E`, then so is
`A x`, because `A y = A x` can only happen for the finitely many `y ∈ x + ker A`. -/
theorem accPt_map {E : Set G} {A : G →+ G} (hcont : Continuous A)
    (hker : (A ⁻¹' {(0 : G)}).Finite) (hE : A '' E ⊆ E) {x : G}
    (hx : AccPt x (𝓟 E)) : AccPt (A x) (𝓟 E) := by
  rw [accPt_iff_nhds] at hx ⊢
  intro U hU
  set K : Set G := A ⁻¹' {(0 : G)} with hK
  have hKfin : (({x} : Set G) + K).Finite := by
    rw [Set.singleton_add]
    exact hker.image (fun k => x + k)
  have hW : A ⁻¹' U ∩ ((({x} : Set G) + K) \ {x})ᶜ ∈ 𝓝 x := by
    refine Filter.inter_mem (hcont.continuousAt.preimage_mem_nhds hU) ?_
    exact ((hKfin.sdiff).isClosed.isOpen_compl).mem_nhds (by simp)
  obtain ⟨y, ⟨hyW, hyE⟩, hyx⟩ := hx _ hW
  refine ⟨A y, ⟨hyW.1, hE ⟨y, hyE, rfl⟩⟩, ?_⟩
  intro hEq
  have hsub : y - x ∈ K := by
    show A (y - x) = 0
    rw [map_sub, hEq, sub_self]
  have hyK : y ∈ ({x} : Set G) + K := by
    rw [Set.singleton_add]
    exact ⟨y - x, hsub, by abel⟩
  exact hyW.2 ⟨hyK, by simpa using hyx⟩

/-- **`E'` is invariant** under every member with finite kernel (Berend §5,
using Lemma 5.1). -/
theorem derivedSet_image_subset {E : Set G} (hE : BerendDichotomy.FamilyInvariant F E)
    {i : ι} (hcont : Continuous (F i)) (hker : ((F i) ⁻¹' {(0 : G)}).Finite) :
    (F i) '' derivedSet E ⊆ derivedSet E := by
  rintro _ ⟨x, ⟨hxE, hxacc⟩, rfl⟩
  exact ⟨hE i ⟨x, hxE, rfl⟩, accPt_map hcont hker (hE i) hxacc⟩

variable (F) in
/-- **`E'` is invariant** (family form). -/
theorem derivedSet_familyInvariant {E : Set G}
    (hE : BerendDichotomy.FamilyInvariant F E) (hcont : ∀ i, Continuous (F i))
    (hker : ∀ i, ((F i) ⁻¹' {(0 : G)}).Finite) :
    BerendDichotomy.FamilyInvariant F (derivedSet E) :=
  fun i => derivedSet_image_subset hE (hcont i) (hker i)

/-! ## 3. A torsion accumulation point makes `0` non-isolated in `n • E` -/

/-- **Berend §5, the step `x ∈ E'` of order `l` ⇒ `0` is a non-isolated point of
`lE`.**  The only points of `E` near `x` that are killed by `n • ·` are the
finitely many points of `x + ker (n • ·)`. -/
theorem accPt_zero_nsmulEnd {E : Set G} {x : G} {n : ℕ} (hxE : x ∈ E)
    (hx : AccPt x (𝓟 E)) (hnx : n • x = 0)
    (htors : ({z : G | n • z = 0} : Set G).Finite) :
    (0 : G) ∈ closure ((nsmulEnd n '' E) \ {0}) := by
  set K : Set G := {z : G | n • z = 0} with hK
  have hxK : x ∈ K := hnx
  -- `x` is still an accumulation point of `E \ K`
  have hacc : x ∈ closure (E \ K) := by
    rw [mem_closure_iff]
    intro o ho hxo
    rw [accPt_iff_nhds] at hx
    have hKclosed : IsClosed (K \ {x}) := (htors.sdiff).isClosed
    have hmem : o ∩ ((K \ {x})ᶜ) ∈ 𝓝 x :=
      (ho.inter hKclosed.isOpen_compl).mem_nhds ⟨hxo, by simp⟩
    obtain ⟨y, ⟨hyW, hyE⟩, hyx⟩ := hx _ hmem
    exact ⟨y, hyW.1, hyE, fun hyK => hyW.2 ⟨hyK, by simpa using hyx⟩⟩
  -- push forward
  have himg : nsmulEnd n '' (E \ K) ⊆ (nsmulEnd n '' E) \ {0} := by
    rintro _ ⟨y, ⟨hyE, hyK⟩, rfl⟩
    refine ⟨⟨y, hyE, rfl⟩, ?_⟩
    simp only [nsmulEnd_apply]
    intro h0
    exact hyK h0
  have h0 : (0 : G) ∈ closure (nsmulEnd n '' (E \ K)) := by
    have hmem : (0 : G) = nsmulEnd n x := by rw [nsmulEnd_apply, hnx]
    rw [hmem]
    exact image_closure_subset_closure_image (continuous_nsmulEnd n) ⟨x, hacc, rfl⟩
  exact closure_mono himg h0

/-! ## 4. `n • E = univ` and finite `n`-torsion give interior (Baire) -/

/-- **Berend §5, the pigeonhole step**: `lE = T^r` implies that the translates of
`E` by the `l`-torsion points cover `T^r`, whence `E` has nonempty interior. -/
theorem interior_nonempty_of_nsmulEnd_image_eq_univ {E : Set G} (hE : IsClosed E) {n : ℕ}
    (htors : ({z : G | n • z = 0} : Set G).Finite)
    (hfull : nsmulEnd n '' E = univ) : (interior E).Nonempty := by
  set K : Set G := {z : G | n • z = 0} with hK
  have hcover : (⋃ k ∈ K, (E + ({k} : Set G))) = univ := by
    rw [← univ_subset_iff]
    intro y _
    have hy : n • y ∈ nsmulEnd n '' E := by rw [hfull]; exact mem_univ _
    obtain ⟨e, heE, he⟩ := hy
    have he' : n • e = n • y := he
    have hmem : n • y - n • e = 0 := by rw [← he', sub_self]
    have hsub : y - e ∈ K := by
      show n • (y - e) = 0
      rw [nsmul_sub]
      exact hmem
    exact mem_biUnion hsub ⟨e, heE, y - e, rfl, by abel⟩
  have hclosed : ∀ k ∈ K, IsClosed (E + ({k} : Set G)) := by
    intro k _
    rw [Set.add_singleton]
    exact (hE.isCompact.image (by fun_prop)).isClosed
  have hdense : Dense (⋃ k ∈ K, interior (E + ({k} : Set G))) :=
    dense_biUnion_interior_of_closed hclosed htors.countable hcover
  have hne : (⋃ k ∈ K, interior (E + ({k} : Set G))).Nonempty := hdense.nonempty
  obtain ⟨p, hp⟩ := hne
  rw [mem_iUnion] at hp
  obtain ⟨k, hp⟩ := hp
  rw [mem_iUnion] at hp
  obtain ⟨_hkK, hpk⟩ := hp
  have himg : (Homeomorph.addRight k) '' interior E = interior (E + ({k} : Set G)) := by
    rw [Homeomorph.image_interior, Set.add_singleton]
    rfl
  rw [← himg] at hpk
  obtain ⟨q, hq, _⟩ := hpk
  exact ⟨q, hq⟩

/-! ## 5. Closed invariant with interior and one transitive member is everything -/

/-- Topological transitivity of a self-map: every nonempty open set is eventually
carried into every nonempty open set.  (For toral endomorphisms this is implied
by ergodicity w.r.t. Haar measure.) -/
def TopologicallyTransitive (f : G → G) : Prop :=
  ∀ U : Set G, IsOpen U → U.Nonempty → ∀ V : Set G, IsOpen V → V.Nonempty →
    ∃ n : ℕ, (((f)^[n]) '' U ∩ V).Nonempty

/-- **Berend §5, last line**: a closed invariant set with nonempty interior, under
a topologically transitive member, is everything. -/
theorem eq_univ_of_isClosed_of_interior_of_transitive {f : G →+ G} {E : Set G}
    (hE : IsClosed E) (hinv : f '' E ⊆ E) (hint : (interior E).Nonempty)
    (htrans : TopologicallyTransitive (⇑f)) : E = univ := by
  by_contra hne
  have hVne : (Eᶜ).Nonempty := Set.nonempty_compl.mpr hne
  obtain ⟨n, x, ⟨u, hu, rfl⟩, hxV⟩ :=
    htrans (interior E) isOpen_interior hint Eᶜ hE.isOpen_compl hVne
  have hiter : BerendMinimal.IsInvariant (⇑f) E := hinv
  have huE : u ∈ E := interior_subset hu
  exact hxV (hiter.mem_iterate huE n)

/-! ## 6. Assembly: Stage I + Berend Prop 5.1 ⇒ the dichotomy -/

/-- **Berend §5 in full, with the two deep inputs made explicit.**

* `hStage` — §4: a closed invariant set of which `0` is a non-isolated point is
  everything (`BerendDichotomy.ZeroNonisolatedFull`);
* `hmin` — Proposition 5.1: every minimal closed invariant set contains a
  torsion point (in Berend's paper, is a finite set of torsion elements);
* `hker` — Lemma 5.1: each member has finite kernel (automatic for toral
  endomorphisms of non-zero determinant);
* `htors` — the `n`-torsion subgroup of the torus is finite;
* `htrans` — some member is topologically transitive (Berend: `Σ` contains an
  ergodic endomorphism, Proposition 3.2).

Conclusion: every closed nonempty invariant proper set is finite, i.e.
`BerendDichotomy.Dichotomy F`.  No difference-set statement is used. -/
theorem dichotomy_of_stageI_of_minimal_torsion
    (hStage : BerendDichotomy.ZeroNonisolatedFull F)
    (hcont : ∀ i, Continuous (F i))
    (hker : ∀ i, ((F i) ⁻¹' {(0 : G)}).Finite)
    (htors : ∀ n : ℕ, 0 < n → ({z : G | n • z = 0} : Set G).Finite)
    (hmin : ∀ M : Set G, IsClosed M → M.Nonempty →
      BerendMinimal.IsInvariantFamily (fun i => (F i : G → G)) M →
      BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M →
      ∃ x ∈ M, ∃ n : ℕ, 0 < n ∧ n • x = 0)
    (htrans : ∃ i, TopologicallyTransitive (⇑(F i))) :
    BerendDichotomy.Dichotomy F := by
  intro Y hY hne hinv hproper
  by_contra hnotfin
  have hinf : Y.Infinite := Set.not_finite.mp hnotfin
  -- the accumulation set
  have h'ne : (derivedSet Y).Nonempty := derivedSet_nonempty hY hinf
  have h'closed : IsClosed (derivedSet Y) := isClosed_derivedSet hY
  have h'inv : BerendDichotomy.FamilyInvariant F (derivedSet Y) :=
    derivedSet_familyInvariant F hinv hcont hker
  -- a minimal set inside it, and a torsion point in that minimal set
  obtain ⟨M, hMsub, hMmin⟩ :=
    BerendMinimal.exists_minimal_invariant h'closed h'ne h'inv
  obtain ⟨x, hxM, n, hn, hnx⟩ := hmin M hMmin.closed hMmin.ne hMmin.inv hMmin
  have hxE : x ∈ Y := derivedSet_subset Y (hMsub hxM)
  have hxacc : AccPt x (𝓟 Y) := (mem_derivedSet.mp (hMsub hxM)).2
  -- Stage I applies to `n • Y`
  have hclosed : IsClosed (nsmulEnd n '' Y) :=
    (hY.isCompact.image (continuous_nsmulEnd n)).isClosed
  have hne' : (nsmulEnd n '' Y).Nonempty := ⟨nsmulEnd n x, ⟨x, hxE, rfl⟩⟩
  have hacc : (0 : G) ∈ closure ((nsmulEnd n '' Y) \ {0}) :=
    accPt_zero_nsmulEnd hxE hxacc hnx (htors n hn)
  have hinv' : BerendDichotomy.FamilyInvariant F (nsmulEnd n '' Y) := by
    rintro i _ ⟨y, ⟨y₀, hy₀, rfl⟩, rfl⟩
    refine ⟨(F i) y₀, hinv i ⟨y₀, hy₀, rfl⟩, ?_⟩
    show n • (F i) y₀ = (F i) (n • y₀)
    exact (map_nsmul (F i) n y₀).symm
  have hfull : nsmulEnd n '' Y = univ := hStage _ hclosed hne' hacc hinv'
  -- Baire: `Y` has interior
  have hint : (interior Y).Nonempty :=
    interior_nonempty_of_nsmulEnd_image_eq_univ hY (htors n hn) hfull
  -- a transitive member forces `Y = univ`
  obtain ⟨i, hi⟩ := htrans
  have hYi : (F i) '' Y ⊆ Y := hinv i
  exact hproper (eq_univ_of_isClosed_of_interior_of_transitive hY hYi hint hi)

/-- **The plan's residual `NoProperFullDiffSet` (§D.5) is a corollary, not a
second deep obligation.**  Under exactly the hypotheses of
`dichotomy_of_stageI_of_minimal_torsion` (in particular with `G` infinite, as the
project's torus is), no closed nonempty invariant proper set has full difference
set.  So the amended §D.5 residual cannot be used to *replace* Berend's §5
argument: it is implied by it. -/
theorem noProperFullDiffSet_of_stageI_of_minimal_torsion [Infinite G]
    (hStage : BerendDichotomy.ZeroNonisolatedFull F)
    (hcont : ∀ i, Continuous (F i))
    (hker : ∀ i, ((F i) ⁻¹' {(0 : G)}).Finite)
    (htors : ∀ n : ℕ, 0 < n → ({z : G | n • z = 0} : Set G).Finite)
    (hmin : ∀ M : Set G, IsClosed M → M.Nonempty →
      BerendMinimal.IsInvariantFamily (fun i => (F i : G → G)) M →
      BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M →
      ∃ x ∈ M, ∃ n : ℕ, 0 < n ∧ n • x = 0)
    (htrans : ∃ i, TopologicallyTransitive (⇑(F i))) :
    BerendDichotomy.NoProperFullDiffSet F :=
  BerendDichotomy.noProperFullDiffSet_of_dichotomy
    (dichotomy_of_stageI_of_minimal_torsion hStage hcont hker htors hmin htrans)

/-! ## 7. Berend Lemma 5.2: finite invariant sets consist of torsion points -/

/-- Iterates of an additive endomorphism, repackaged as additive endomorphisms so
that differences of powers are again additive. -/
def iterHom (g : G →+ G) : ℕ → (G →+ G)
  | 0 => AddMonoidHom.id G
  | (k + 1) => (iterHom g k).comp g

theorem iterHom_apply (g : G →+ G) : ∀ (k : ℕ) (x : G), iterHom g k x = (g^[k]) x
  | 0, _ => rfl
  | (k + 1), x => by
      show (iterHom g k) (g x) = (g^[k + 1]) x
      rw [iterHom_apply g k (g x), Function.iterate_succ_apply]

/-- **Every element of a finite additive subgroup is a torsion element** (the
"finite kernel is torsion" half of Berend's Lemma 5.1, used in Lemma 5.2). -/
theorem exists_nsmul_eq_zero_of_finite_addSubgroup {K : AddSubgroup G} (hK : Finite K)
    {x : G} (hx : x ∈ K) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  haveI := hK
  obtain ⟨m, k, hmk, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => (⟨j • x, K.nsmul_mem hx j⟩ : K))
  have heq' : m • x = k • x := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hmk with hlt | hlt
  · refine ⟨k - m, by omega, ?_⟩
    have hsplit : k • x = m • x + (k - m) • x := by
      rw [← add_nsmul, Nat.add_sub_of_le hlt.le]
    rw [hsplit] at heq'
    exact add_left_cancel (a := m • x) (by rw [add_zero]; exact heq'.symm)
  · refine ⟨m - k, by omega, ?_⟩
    have hsplit : m • x = k • x + (m - k) • x := by
      rw [← add_nsmul, Nat.add_sub_of_le hlt.le]
    rw [hsplit] at heq'
    exact add_left_cancel (a := k • x) (by rw [add_zero]; exact heq')

/-- **Berend Lemma 5.2, abstract core.**  If `M` is finite, invariant under a
member `g` all of whose power differences `g^m - g^n` (`m ≠ n`) have finite
kernel, then every point of `M` is a torsion point.  (In Berend's toral setting
`g^m - g^n` is an epimorphism, so Lemma 5.1 supplies the finite kernel.) -/
theorem torsion_of_finite_invariant {g : G →+ G} {M : Set G} (hM : M.Finite)
    (hinv : ∀ x ∈ M, g x ∈ M)
    (hdiff : ∀ m n : ℕ, m ≠ n → ((iterHom g m - iterHom g n) ⁻¹' {(0 : G)}).Finite)
    {x : G} (hx : x ∈ M) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  haveI : Finite M := hM
  have horb : ∀ k : ℕ, (g^[k]) x ∈ M := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih
  obtain ⟨m, n, hmn, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨(g^[k]) x, horb k⟩ : M))
  have heq' : (g^[m]) x = (g^[n]) x := congrArg Subtype.val heq
  have hmem : x ∈ AddMonoidHom.ker (iterHom g m - iterHom g n) := by
    rw [AddMonoidHom.mem_ker]
    show iterHom g m x - iterHom g n x = 0
    rw [iterHom_apply, iterHom_apply, heq', sub_self]
  exact exists_nsmul_eq_zero_of_finite_addSubgroup
    (K := AddMonoidHom.ker (iterHom g m - iterHom g n)) (hdiff m n hmn) hmem

/-- **Berend §5 with Proposition 5.1 in the form he actually proves it**: every
minimal closed invariant set is *finite* (finiteness), plus the spectral input of
Lemma 5.2 (`g^m - g^n` has finite kernel).  The conclusion is again the
dichotomy, so the torsion half of Proposition 5.1 is derived, not assumed. -/
theorem dichotomy_of_stageI_of_minimal_finite
    (hStage : BerendDichotomy.ZeroNonisolatedFull F)
    (hcont : ∀ i, Continuous (F i))
    (hker : ∀ i, ((F i) ⁻¹' {(0 : G)}).Finite)
    (htors : ∀ n : ℕ, 0 < n → ({z : G | n • z = 0} : Set G).Finite)
    (hminFin : ∀ M : Set G, IsClosed M → M.Nonempty →
      BerendMinimal.IsInvariantFamily (fun i => (F i : G → G)) M →
      BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M → M.Finite)
    (hdiff : ∃ i, ∀ m n : ℕ, m ≠ n →
      ((iterHom (F i) m - iterHom (F i) n) ⁻¹' {(0 : G)}).Finite)
    (htrans : ∃ i, TopologicallyTransitive (⇑(F i))) :
    BerendDichotomy.Dichotomy F := by
  obtain ⟨i, hi⟩ := hdiff
  refine dichotomy_of_stageI_of_minimal_torsion hStage hcont hker htors
    (fun M hcl hMne hinv hMmin => ?_) htrans
  have hfin : M.Finite := hminFin M hcl hMne hinv hMmin
  obtain ⟨x, hx⟩ := hMne
  exact ⟨x, hx, torsion_of_finite_invariant hfin
    (fun y hy => hinv i ⟨y, hy, rfl⟩) (fun m n hmn => hi m n hmn) hx⟩


/-! ## 8. A minimal set containing a torsion point is finite (Prop. 5.1, last step) -/

/-- Finite words of additive endomorphisms preserve `n`-torsion. -/
theorem nsmul_wordApply {n : ℕ} {y : G} (hy : n • y = 0) (l : List ι) :
    n • BerendMinimal.wordApply (fun i => (F i : G → G)) l y = 0 := by
  induction l generalizing y with
  | nil => simpa using hy
  | cons i l ih =>
      rw [BerendMinimal.wordApply_cons]
      refine ih ?_
      show n • (F i) y = 0
      rw [← map_nsmul, hy, map_zero]

/-- **Berend §5 / Proposition 5.1, last step.**  A minimal closed invariant set
that contains a single torsion point is finite: its semigroup orbit is contained in
the finite `n`-torsion subgroup, and minimality makes `M` the closure of that
orbit.  In particular "every minimal set contains a torsion point"
(`hmin` of `dichotomy_of_stageI_of_minimal_torsion`) plus finiteness of the
torsion subgroups is the same as "every minimal set is a finite set of torsion
elements", which is the conclusion of Berend's Proposition 5.1. -/
theorem finite_of_minimal_of_nsmul_eq_zero {M : Set G}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M)
    (hcont : ∀ i, Continuous (F i))
    (htors : ∀ n : ℕ, 0 < n → ({z : G | n • z = 0} : Set G).Finite)
    {x : G} {n : ℕ} (hn : 0 < n) (hnx : n • x = 0) (hx : x ∈ M) : M.Finite := by
  have hsub : BerendMinimal.semigroupOrbit (fun i => (F i : G → G)) x ⊆
      {z : G | n • z = 0} := by
    rintro y ⟨l, rfl⟩
    exact nsmul_wordApply (F := F) hnx l
  have hfin : (BerendMinimal.semigroupOrbit (fun i => (F i : G → G)) x).Finite :=
    (htors n hn).subset hsub
  rw [← hM.closure_semigroupOrbit hcont hx, hfin.isClosed.closure_eq]
  exact hfin


end BerendSec5
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendSec5.derivedSet_nonempty
#print axioms CubicTwoStage.BerendSec5.isClosed_derivedSet
#print axioms CubicTwoStage.BerendSec5.accPt_map
#print axioms CubicTwoStage.BerendSec5.accPt_zero_nsmulEnd
#print axioms CubicTwoStage.BerendSec5.interior_nonempty_of_nsmulEnd_image_eq_univ
#print axioms CubicTwoStage.BerendSec5.eq_univ_of_isClosed_of_interior_of_transitive
#print axioms CubicTwoStage.BerendSec5.dichotomy_of_stageI_of_minimal_torsion
#print axioms CubicTwoStage.BerendSec5.noProperFullDiffSet_of_stageI_of_minimal_torsion
#print axioms CubicTwoStage.BerendSec5.exists_nsmul_eq_zero_of_finite_addSubgroup
#print axioms CubicTwoStage.BerendSec5.torsion_of_finite_invariant
#print axioms CubicTwoStage.BerendSec5.dichotomy_of_stageI_of_minimal_finite
#print axioms CubicTwoStage.BerendSec5.nsmul_wordApply
#print axioms CubicTwoStage.BerendSec5.finite_of_minimal_of_nsmul_eq_zero
