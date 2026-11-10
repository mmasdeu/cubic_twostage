/-
# Berend's multi-invariance theorem with the corrected (B3), axiom-free

This module implements the **statement layer and final transport** of
`BEREND_PROOF_PLAN.md` (package **E**: the corrected (B3), plan item E.1-E.3)
together with the generic corrected-(B3) lemmas.  It declares **no axiom**, and
**no theorem below depends on an axiom** other than `propext`,
`Classical.choice` and `Quot.sound` (audited in
`CubicTwoStage/BerendCheck.lean`).  Be precise about the import: the axiom
`CubicTwoStage.berend_multi_invariance` *is* imported transitively --
`RationalIndependence` -> `FieldModel` -> `Uncovered` -> `Berend` -- but it is
never used, and `#print axioms` shows its absence from every declaration here.

## Why the old (B3) had to be corrected

`CubicTwoStage.berend_multi_invariance` asked for

`B3 : ∃ i j, ∀ l k : ℤ, l ≠ 0 → k ≠ 0 → (f i)^l ≠ (f j)^k`.

That condition is satisfied by `Σ = {A, -id}` with `A` hyperbolic and
`A^l ≠ ±1` for `l ≠ 0` — `det A^l = 30^l ≠ ±1` — while the survivor set of `A`
about a small symmetric ball is a closed, infinite, proper, `A`- and
`-id`-invariant set.  See `.ultramath/smw68xy68/m5/refutation.md`.  The repair
adopted here is the plan's:

`B3 : ∃ i j, ∀ l k : ℤ, (f i)^l = (f j)^k → l = 0 ∧ k = 0`

(`RationallyIndependentPair`), which forbids a member of finite order:
`not_rationallyIndependentPair_bool` below shows that a family indexed by `Bool`
one of whose members is an involution never satisfies it.

## What is proved here (unconditional)

* `RationallyIndependentPair.toOld` — the corrected (B3) implies the old one, so
  existing call sites keep working;
* `RationallyIndependentPair.exists_ne`, `.torsionFree` — the two witnesses are
  distinct and torsion-free;
* `not_rationallyIndependentPair_bool` — no family of two maps, one of them of
  finite order, satisfies the corrected (B3); this is exactly what excludes
  `{A, -id}`;
* `not_rationallyIndependentPair_negId` — the concrete family
  `{A, -id}` of m5's refutation fails the corrected (B3), for every `A`;
* `zpow_eq_one_imp_eq_zero` — the elementary integer-power lemma used to peel
  off the exponents;
* **`rational_independence_corrected`** — *the corrected (B3) holds for the
  unit–prime semigroup `Σ = {μ_{uπ^j}}`*, with witnesses `μ_ε` and `μ_π`, from
  `hεpow` (`ε` has infinite order) and `Nm π = p > 1`;

and, conditional only on the single explicitly stated proposition
`BerendMultiInvarianceCorrected` (never on an axiom):

* `berend_multi_invariance_corrected` — its unpacked form;
* `UnitPrimeModel.berend_corrected` — the torus-level form for the
  unit–prime model;
* `finite_torus_image_of_orbit_avoid_corrected` — **the §3 use site**: the
  torus image of the uncovered set is finite.  This is
  `CubicTwoStage.finite_torus_image_of_orbit_avoid` with the axiom replaced by
  the hypothesis `H`.

## What is *not* proved here

The proposition `BerendMultiInvarianceCorrected` itself.  That is Berend,
Trans. AMS **280** (1983), Theorem 2.1 (sufficiency) — stages **C** (zero
non-isolated implies full) and **D** (Proposition IV.1, disjointness of
minimal sets) of the plan.  It contains Furstenberg's `×2 ×3` theorem, and
nothing in this file discharges it.  In particular no theorem here is a
`Prop`-valued restatement of stage C or D: `H` is a hypothesis, printed in the
statement of every theorem that uses it, and `#print axioms` on the theorems
above returns only `[propext, Classical.choice, Quot.sound]`.

## Relation to `CubicTwoStage/Berend.lean`

The definitions `torusEnd`, `latticeActZ`, `lactZ`, `torusEndAct` are verbatim
copies of `torusMap`, `latticeAct`, `lact`, `torusAct`, under new names so that
this module never mentions the names of the axiom module.
`CubicTwoStage/BerendBridge.lean` proves each copy equal to the original by
`rfl`, so `BerendMultiInvarianceCorrected` discharges the conclusion of
`UnitPrimeModel.berend` with no rewriting.
-/
import CubicTwoStage.RationalIndependence

set_option linter.unusedVariables false

open scoped TensorProduct

namespace CubicTwoStage

/-! ## 1. Rational independence, generically -/

/-- Two members of an indexed family in a group are **rationally independent**
in Berend's corrected sense: no nontrivial integer power of one equals a
nontrivial integer power of the other, including the zeroth powers.

This is the corrected (B3) of `BEREND_PROOF_PLAN.md`.  The old (B3) only
required `l ≠ 0` and `k ≠ 0`, which is satisfied by families containing a map of
finite order (e.g. `{A, -id}`), and those refute the conclusion. -/
def RationallyIndependentPair {G : Type*} [Group G] {ι : Type*} (f : ι → G) : Prop :=
  ∃ i j : ι, ∀ l k : ℤ, f i ^ l = f j ^ k → l = 0 ∧ k = 0

/-- The **old** (B3) of `CubicTwoStage/Berend.lean`. -/
def RationallyIndependentPairOld {G : Type*} [Group G] {ι : Type*} (f : ι → G) : Prop :=
  ∃ i j : ι, ∀ l k : ℤ, l ≠ 0 → k ≠ 0 → f i ^ l ≠ f j ^ k

/-- The corrected (B3) implies the old one: restrict to nonzero exponents. -/
theorem RationallyIndependentPair.toOld {G : Type*} [Group G] {ι : Type*} {f : ι → G}
    (h : RationallyIndependentPair f) : RationallyIndependentPairOld f := by
  obtain ⟨i, j, hij⟩ := h
  refine ⟨i, j, fun l k hl hk heq => hl (hij l k heq).1⟩

/-- In a rationally independent pair the two indices must be distinct: at
`l = k = 1` the corrected condition would read `f i ≠ f i`. -/
theorem RationallyIndependentPair.exists_ne {G : Type*} [Group G] {ι : Type*} {f : ι → G}
    (h : RationallyIndependentPair f) : ∃ i j : ι, i ≠ j := by
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := by
    rintro rfl
    exact absurd (hij 1 1 rfl).1 one_ne_zero
  exact ⟨i, j, hne⟩

/-- Both members of a rationally independent pair have infinite order: at `l = 0`
against a trivial power of the other member. -/
theorem RationallyIndependentPair.torsionFree {G : Type*} [Group G] {ι : Type*} {f : ι → G}
    (h : RationallyIndependentPair f) :
    ∃ i j : ι, (∀ l : ℤ, f i ^ l = 1 → l = 0) ∧ (∀ k : ℤ, f j ^ k = 1 → k = 0) := by
  obtain ⟨i, j, hij⟩ := h
  refine ⟨i, j, ?_, ?_⟩
  · intro l hl
    have := (hij l 0 (by rw [hl, zpow_zero])).1
    exact this
  · intro k hk
    have := (hij 0 k (by rw [hk, zpow_zero])).2
    exact this

/-- Two indices of a rationally independent pair are never equal as group
elements when the second has order exactly... (convenience form). -/
theorem RationallyIndependentPair.pow_right_ne_one {G : Type*} [Group G] {ι : Type*}
    {f : ι → G} (h : RationallyIndependentPair f) :
    ∃ i j : ι, ∀ k : ℤ, k ≠ 0 → f j ^ k ≠ 1 := by
  obtain ⟨i, j, _, h2⟩ := h.torsionFree
  exact ⟨i, j, fun k hk h1 => hk (h2 k h1)⟩

/-- **The corrected (B3) excludes any family indexed by `Bool` in which one
member has finite order** — in particular the counterexample family
`{A, -id}` of `.ultramath/smw68xy68/m5/refutation.md`, where the second member
is an involution (`m = 2`). -/
theorem not_rationallyIndependentPair_bool {G : Type*} [Group G] (f : Bool → G)
    {m : ℕ} (hm : m ≠ 0) (h : f false ^ m = 1) : ¬ RationallyIndependentPair f := by
  rintro ⟨i, j, hij⟩
  have hne : i ≠ j := by
    rintro rfl
    exact absurd (hij 1 1 rfl).1 one_ne_zero
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  cases j with
  | false =>
      have h1 : f i ^ (0 : ℤ) = f false ^ (m : ℤ) := by
        rw [zpow_zero, zpow_natCast]; exact h.symm
      exact absurd (hij 0 (m : ℤ) h1).2 hmz
  | true =>
      have hi : i = false := by cases i <;> simp_all
      subst hi
      have h1 : f false ^ (m : ℤ) = f true ^ (0 : ℤ) := by
        rw [zpow_zero, zpow_natCast]; exact h
      exact absurd (hij (m : ℤ) 0 h1).1 hmz

/-! ## 2. Integer powers of fields elements -/

/-- If no positive power of `a` is `1` then `a ^ l = 1` forces `l = 0`, for
integer exponents. -/
theorem zpow_eq_one_imp_eq_zero {K : Type*} [Field K] {a : K}
    (h : ∀ n : ℕ, 0 < n → a ^ n ≠ 1) {l : ℤ} (hl : a ^ l = 1) : l = 0 := by
  rcases lt_trichotomy l 0 with hneg | hzero | hpos
  · have h2 : a ^ (-l) = 1 := by
      have h1 : (a ^ l)⁻¹ = 1 := by rw [hl, inv_one]
      rw [zpow_neg, h1]
    have h3 : a ^ ((-l).toNat) = 1 := by
      rw [← zpow_natCast, show (((-l).toNat : ℤ)) = -l from by omega, h2]
    exact absurd h3 (h _ (by omega))
  · exact hzero
  · have h3 : a ^ (l.toNat) = 1 := by
      rw [← zpow_natCast, show (((l.toNat : ℤ))) = l from by omega, hl]
    exact absurd h3 (h _ (by omega))

/-! ## 3. The corrected (B3) for the unit–prime model -/

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- **The corrected (B3) holds for the unit–prime semigroup.**  With
`i = (ε, 0)` (`μ_ε`) and `j = (1, 1)` (`μ_π`), an equality
`μ_ε ^ l = μ_π ^ k` evaluated at `1` gives `ε ^ l = π ^ k`; taking norms gives
`1 = p ^ k`, hence `k = 0`, and then `ε ^ l = 1`, hence `l = 0` by `hεpow`.

This is the stricter form of `rational_independence`: it also excludes the
zeroth powers, so a map of finite order can no longer be paired with `μ_ε`. -/
theorem rational_independence_corrected (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0)) :
    RationallyIndependentPair (FM.toModel ε π hπO hπ0).linFam := by
  refine ⟨(ε, 0), (1, 1), ?_⟩
  intro l k hEq
  have hEq' := congrArg (fun f : Pt ≃ₗ[ℝ] Pt => f oneC) hEq
  rw [linFam_eval_one, linFam_eval_one] at hEq'
  simp only [pow_zero, mul_one, Units.val_one, Subring.coe_one, one_mul, pow_one] at hEq'
  have hinj : ∀ a b : K, FM.σ a = FM.σ b → a = b := by
    intro a b h
    have hz : FM.σ (a - b) = 0 := by rw [FM.σ_sub, h, sub_self]
    exact sub_eq_zero.mp (FM.σ_eq_zero hz)
  have hEl : (((ε : 𝒪) : K)) ^ l = π ^ k := hinj _ _ hEq'
  have hOne : Nm (π ^ k) = 1 := by
    rw [← hEl, map_zpow₀, FM.Nm_unit ε, one_zpow]
  rw [map_zpow₀, hπN] at hOne
  have hR : ((p : ℝ)) ^ k = 1 := by
    convert congrArg (fun x : ℚ≥0 => (x : ℝ)) hOne
    push_cast
    all_goals norm_num
  have hk : k = 0 := by
    by_contra hk
    exact absurd hR (zpow_ne_one_of_gt_one (a := (p : ℝ)) (by exact_mod_cast hp) hk)
  refine ⟨?_, hk⟩
  refine zpow_eq_one_imp_eq_zero (a := (((ε : 𝒪) : K))) hεpow ?_
  rw [hEl, hk, zpow_zero]


/-! ## 3' The concrete counterexample family `{A, -id}` is excluded -/

/-- The real-linear equivalence `x ↦ -x` of `ℝ × ℂ`. -/
noncomputable def negPt : Pt ≃ₗ[ℝ] Pt where
  toFun := fun x => -x
  invFun := fun x => -x
  map_add' := fun x y => neg_add x y
  map_smul' := fun c x => (smul_neg c x).symm
  left_inv := fun x => neg_neg x
  right_inv := fun x => neg_neg x

@[simp] lemma negPt_apply (x : Pt) : negPt x = -x := rfl

/-- `-id` is an involution. -/
lemma negPt_sq : (negPt : Pt ≃ₗ[ℝ] Pt) ^ 2 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  simp [pow_two, negPt_apply]

/-- **The corrected (B3) excludes the counterexample family `{A, -id}`** of
`.ultramath/smw68xy68/m5/refutation.md`, for *every* endomorphism `A`.  The old
(B3) is satisfied by this family whenever `A^l ≠ ±1` for `l ≠ 0` (for `A` with
`det A = 30` that is the determinant computation of m5 §4), so this is exactly
the strengthening the plan adopts. -/
theorem not_rationallyIndependentPair_negId (A : Pt ≃ₗ[ℝ] Pt) :
    ¬ RationallyIndependentPair (fun b : Bool => if b then A else negPt) := by
  refine not_rationallyIndependentPair_bool (fun b : Bool => if b then A else negPt)
    (m := 2) (by norm_num) ?_
  show (negPt : Pt ≃ₗ[ℝ] Pt) ^ 2 = 1
  exact negPt_sq

/-! ## 4. The torus layer

These definitions are the ones of `CubicTwoStage/Berend.lean`
(`torusMap`, `torusAct`, `lact`) repeated verbatim under different names, so
that this module does **not** import `CubicTwoStage.Berend` and therefore cannot
use the axiom `berend_multi_invariance`.  The bridge file
`BridgeCheck.lean` proves `torusEnd = torusMap`, `torusEndAct = torusAct`,
`latticeActZ = latticeAct` and `lactZ = lact` by `rfl`, so the two copies are
interchangeable in the assembled development. -/

variable {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The endomorphism of `Pt ⧸ L` induced by an additive map preserving `L`. -/
noncomputable def torusEnd (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L) :
    Pt ⧸ L →+ Pt ⧸ L :=
  QuotientAddGroup.map L L f fun _ hg => hf _ hg

@[simp] lemma torusEnd_mk (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L)
    (x : Pt) : torusEnd L f hf (QuotientAddGroup.mk x) = QuotientAddGroup.mk (f x) :=
  QuotientAddGroup.map_mk L L f _ x

lemma torusEnd_mk' (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L)
    (x : Pt) : torusEnd L f hf ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' L) (f x) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, torusEnd_mk]

lemma continuous_torusEnd (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L)
    (hcont : Continuous f) : Continuous (torusEnd L f hf) := by
  refine (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr ?_
  have h : ((torusEnd L f hf : Pt ⧸ L →+ Pt ⧸ L) : Pt ⧸ L → Pt ⧸ L) ∘
      (QuotientAddGroup.mk : Pt → Pt ⧸ L) = (QuotientAddGroup.mk : Pt → Pt ⧸ L) ∘ f := by
    funext x
    exact torusEnd_mk L f hf x
  rw [h]
  exact QuotientAddGroup.continuous_mk.comp hcont

/-- The integral restriction of a real-linear lattice endomorphism. -/
noncomputable def latticeActZ (L : AddSubgroup Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  LinearMap.restrict (LinearMap.restrictScalars ℤ f)
    (p := AddSubgroup.toIntSubmodule L) (q := AddSubgroup.toIntSubmodule L) hf

/-- The restriction of `μ_{uπ^j}` to the integral lattice. -/
noncomputable def UnitPrimeModel.lactZ (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  latticeActZ L ((D.linFam i : Pt →ₗ[ℝ] Pt)) (fun x hx => D.lattice_linFam i hx)

/-- The torus endomorphism induced by `μ_{uπ^j}`. -/
noncomputable def UnitPrimeModel.torusEndAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Pt ⧸ L →+ Pt ⧸ L :=
  torusEnd L ((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (D.linFam_preserves i)

lemma UnitPrimeModel.torusEndAct_mk' (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (x : Pt) :
    D.torusEndAct i ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' L) (D.family.act i x) := by
  rw [UnitPrimeModel.torusEndAct, torusEnd_mk', UnitPrimeModel.family_apply]
  rfl

lemma UnitPrimeModel.torusEndAct_applyList (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (l : List (𝒪ˣ × ℕ)) (x : Pt) :
    D.torusEndAct i ((QuotientAddGroup.mk' L) (D.applyList l x)) =
      (QuotientAddGroup.mk' L) (D.applyList (l ++ [i]) x) := by
  rw [D.torusEndAct_mk', D.applyList_append_singleton]

lemma UnitPrimeModel.continuous_torusEndAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Continuous (D.torusEndAct i) := by
  refine continuous_torusEnd L _ (D.linFam_preserves i) ?_
  have h : (((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom : Pt → Pt) =
      fun x => D.mult i.1 i.2 ⋆ x := rfl
  rw [h]
  exact continuous_mulC _

/-! ## 5. The corrected Berend statement, as a proposition -/

/-- **Berend's multi-invariance theorem with the corrected (B3)**, stated as a
`Prop` rather than as an axiom.

The only difference from `berend_multi_invariance` in
`CubicTwoStage/Berend.lean` is that the commutation hypothesis is an explicit
argument and that (B3) is `RationallyIndependentPair f`, which also forbids
pairing an infinite-order map with one of finite order.  The conclusion is
unchanged. -/
def BerendMultiInvarianceCorrected (ι : Type*) (f : ι → Pt ≃ₗ[ℝ] Pt) (L : AddSubgroup Pt)
    (hpres : ∀ (i : ι) (g : Pt), g ∈ L → f i g ∈ L)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : ι, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeActZ L ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : ι → ℂ), x ≠ 0 →
      (∀ i : ι, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : ι, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x)) : Prop :=
  ∀ (Y : Set (Pt ⧸ L)), IsClosed Y → Y.Nonempty →
      (∀ i : ι, (torusEnd L ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i)) '' Y ⊆ Y) →
      Y ≠ Set.univ → Y.Finite

/-- Unpacking: a proof of the corrected statement gives the dichotomy. -/
theorem berend_multi_invariance_corrected (ι : Type*) (f : ι → Pt ≃ₗ[ℝ] Pt)
    (L : AddSubgroup Pt) (hpres : ∀ (i : ι) (g : Pt), g ∈ L → f i g ∈ L)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : ι, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((latticeActZ L ((f i : Pt →ₗ[ℝ] Pt)) (hpres i)) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : ι → ℂ), x ≠ 0 →
      (∀ i : ι, LinearMap.baseChange ℂ ((f i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : ι, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair f)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    (H : BerendMultiInvarianceCorrected ι f L hpres hZ B1 B2 B3 hcomm)
    (Y : Set (Pt ⧸ L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : ι, (torusEnd L ((f i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (hpres i)) '' Y ⊆ Y) :
    Y ≠ Set.univ → Y.Finite :=
  H Y hclosed hne hinv

/-- **The torus-level form of the corrected Berend theorem for the unit–prime
semigroup.**  Same conclusion as `UnitPrimeModel.berend`, with the corrected
(B3) and without invoking the axiom. -/
theorem UnitPrimeModel.berend_corrected (D : UnitPrimeModel L 𝒪)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lactZ i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair D.linFam)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZ B1 B2 B3
      D.linFam_comm)
    (Y : Set (Pt ⧸ L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : 𝒪ˣ × ℕ, D.torusEndAct i '' Y ⊆ Y) :
    Y ≠ Set.univ → Y.Finite :=
  H Y hclosed hne hinv

/-! ## 6. The §3 use site: finiteness of the torus image of the uncovered set -/

theorem finite_torus_image_of_orbit_avoid_corrected (𝒪 : Subring K) (Nm : AbsNorm K)
    (σ : K → Pt) (L : AddSubgroup Pt) (D : UnitPrimeModel L 𝒪) (W : Set Pt)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lactZ i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair D.linFam)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZL B1 B2 B3
      D.linFam_comm)
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty)
    (hWtrans : ∀ g ∈ L, ∀ x : Pt, (x ∈ W ↔ x - g ∈ W))
    (havoid : ∀ y ∈ uncovered 𝒪 Nm σ, ∀ l, D.applyList l y ∉ W) :
    Set.Finite ((fun x : Pt => (QuotientAddGroup.mk' L) x) '' uncovered 𝒪 Nm σ) := by
  classical
  by_cases hZ : (uncovered 𝒪 Nm σ).Nonempty
  · set U : Set Pt := uncovered 𝒪 Nm σ with hUdef
    set q : Pt → Torus L := fun x => (QuotientAddGroup.mk' L) x with hqdef
    set F : List (𝒪ˣ × ℕ) → Set (Torus L) :=
      fun l => q '' (D.applyList l '' U) with hFdef
    set S : Set (Torus L) := ⋃ l, F l with hSdef
    have hSmem : ∀ (l : List (𝒪ˣ × ℕ)) (x : Pt), x ∈ U → q (D.applyList l x) ∈ S := by
      intro l x hx
      exact Set.mem_iUnion.mpr ⟨l, ⟨D.applyList l x, ⟨x, hx, rfl⟩, rfl⟩⟩
    -- every point of `S` is a class that misses `W`
    have hSavoid : ∀ z ∈ S, z ∉ q '' W := by
      intro z hz hzW
      obtain ⟨l, hzl⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hzl
      obtain ⟨w, hw, hzw⟩ := hzW
      have hmem : D.applyList l x - w ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp hzw.symm
      have hiff := hWtrans (D.applyList l x - w) hmem (D.applyList l x)
      refine havoid x hx l (hiff.mpr ?_)
      simpa using hw
    -- the image of `W` in the torus is open
    have hWqopen : IsOpen (q '' W) :=
      QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap W hWopen
    -- the closure of `S` is invariant
    have hSinv : ∀ i : 𝒪ˣ × ℕ, D.torusEndAct i '' S ⊆ S := by
      intro i z hz
      obtain ⟨z₀, hz₀, rfl⟩ := hz
      obtain ⟨l, hzl⟩ := Set.mem_iUnion.mp hz₀
      obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hzl
      exact (D.torusEndAct_applyList i l x).symm ▸ hSmem (l ++ [i]) x hx
    have hnonempty : (closure S).Nonempty :=
      hZ.elim fun x hx => ⟨_, subset_closure (hSmem [] x hx)⟩
    have hinv : ∀ i : 𝒪ˣ × ℕ, D.torusEndAct i '' closure S ⊆ closure S := by
      intro i z hz
      have h1 : D.torusEndAct i '' closure S ⊆ closure (D.torusEndAct i '' S) :=
        image_closure_subset_closure_image (D.continuous_torusEndAct i)
      exact closure_mono (hSinv i) (h1 hz)
    have hproper : closure S ≠ Set.univ := by
      intro hfull
      obtain ⟨w, hw⟩ := hWnonempty
      have hmem : q w ∈ closure S := by rw [hfull]; exact Set.mem_univ _
      obtain ⟨s, hsW, hsS⟩ := (mem_closure_iff).mp hmem _ hWqopen ⟨w, hw, rfl⟩
      exact hSavoid s hsS hsW
    have hfin : (closure S).Finite := H _ isClosed_closure hnonempty hinv hproper
    refine hfin.subset ?_
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact subset_closure (hSmem [] x hx)
  · rw [Set.not_nonempty_iff_eq_empty.mp hZ]
    simp



end CubicTwoStage
