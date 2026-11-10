/-
# Berend §5 / Furstenberg Proposition IV.1: minimal sets are finite torsion sets

Swarm `smw8wfugr`, member m2, direction d1.  This module formalises the part of
Berend, *Multi-invariant sets on tori* (Trans. AMS 280, 1983), **§5** that turns
Furstenberg's disjointness proposition into the statement the project's plan calls
`minimal_isFinite`, together with Berend's Lemmas 5.1–5.2 (finite invariant sets
consist of torsion points).

## What is proved

`PropIV1 F` is Furstenberg's **Proposition IV.1** in the formulation Berend quotes
in §5 ([Furstenberg 1967, p. 45], rephrased):

> Let `Σ` be a commutative semigroup of endomorphisms of the torus satisfying
> (i) some member is ergodic and (ii) some prime `q` is coprime to all
> determinants.  If `M`, `B` are closed `Σ`-invariant sets, `M` minimal, and
> `M + B = univ`, then `B = univ`.

Conditions (i), (ii) are hypotheses *on the semigroup*: they are not needed to
state the conclusion, so the conclusion is what `PropIV1` records, and (i)/(ii)
are exactly what a proof of `PropIV1` for a concrete family has to supply.

From `PropIV1` and the project's Stage I statement
(`BerendDichotomy.ZeroNonisolatedFull`) this module derives

* `IsMinimalInvariant.finite_of_propIV1` — **Berend's Proposition 5.1**: every
  nonempty minimal closed invariant set is **finite** (Furstenberg's Prop. IV.2 in
  dimension `r`, whose proof is: `M - M` is closed invariant and, `M` being
  infinite, has `0` as a non-isolated point; Stage I gives `M - M = univ`; then
  `PropIV1` with `B = -M` gives `-M = univ`, i.e. `M = univ`, contradicting
  minimality because `{0}` is a proper closed invariant subset);

* `diffHom`, `finite_invariant_isTorsion` — **Berend's Lemma 5.2**: a finite set
  invariant under an endomorphism `σ` whose difference maps
  `x ↦ σ^[n] x - σ^[m] x` (`n ≠ m`) have finite fibres consists of torsion
  points.  (Berend's Lemma 5.1 is what supplies the finite fibres: the kernel of
  an epimorphism `σ` of `T^r` is finite, and `σ^m - σ^n` is an epimorphism as soon
  as no eigenvalue of `σ` is `0` or a root of unity.)

* `exists_pos_nsmul_eq_zero_of_mem_minimal` — the combination: for a family
  member with finite difference fibres, every point of a minimal closed invariant
  set is torsion.

Everything is axiom free (`#print axioms` at the end reports only `propext`,
`Classical.choice`, `Quot.sound`); nothing imports the old axiom.

## What is *not* here (the honest deficit)

`PropIV1` itself is not proved: its proof is Furstenberg's, and its only
non-elementary input is the ergodicity of a toral endomorphism with no
root-of-unity eigenvalue with respect to Haar measure (`K^{(n)}` closed invariant
with non-empty interior is everything).  See `README.md` in this directory for
the reduction of that input to the expansion estimate `A '' ball ⊆ ball` in the
lift and the precise reason that estimate does not apply to the unit–prime family
without passing through Haar measure.
-/
import CubicTwoStage.BerendDichotomy
import CubicTwoStage.BerendMinimal

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendPropIV1

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable {ι : Type*}

/-! ## 1. Furstenberg's Proposition IV.1 as an explicit statement -/

/-- **Furstenberg's Proposition IV.1** (quoted in Berend 1983, §5): if `M` is a
minimal closed invariant set and `B` a closed invariant set with `M + B` the
whole group, then `B` is the whole group.

The semigroup hypotheses of the published proposition (an ergodic member; a prime
coprime to all determinants) are hypotheses used to *prove* this statement for a
concrete family; they do not occur in its formulation, so they are not part of
this definition. -/
def PropIV1 (F : ι → G →+ G) : Prop :=
  ∀ M B : Set G, M.Nonempty → IsClosed M → IsClosed B →
    BerendDichotomy.FamilyInvariant F M → BerendDichotomy.FamilyInvariant F B →
    BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M →
    M + B = univ → B = univ

/-! ## 2. Berend's Proposition 5.1: minimal sets are finite -/

section Minimal

variable {F : ι → G →+ G}

/-- `M + (-M) = M - M`, the form in which Proposition IV.1 is applied. -/
theorem add_neg_eq_sub (M : Set G) : M + -M = M - M := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_neg] at hb
    refine ⟨a, ha, -b, hb, ?_⟩
    change a - (-b) = a + b
    abel
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, -b, by simpa using hb, ?_⟩
    change a + -b = a - b
    abel

/-- **Berend (1983), Proposition 5.1** (Furstenberg's Proposition IV.2 in
dimension `r`): assuming Stage I and Proposition IV.1, every nonempty minimal
closed invariant set is finite. -/
theorem minimal_finite_of_propIV1 [CompactSpace G] [T2Space G] [Nontrivial G]
    (hStage : BerendDichotomy.ZeroNonisolatedFull F) (hIV1 : PropIV1 F)
    {M : Set G} (hM : BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M) :
    M.Finite := by
  by_contra hfin
  have hinf : M.Infinite := Set.not_finite.mp hfin
  -- `M - M` is closed, nonempty, invariant, and has `0` as a non-isolated point
  have hclosed : IsClosed (M - M) := BerendMinimal.isClosed_sub hM.closed
  have hne : (M - M).Nonempty := ⟨0, BerendMinimal.zero_mem_sub hM.ne⟩
  have hacc : (0 : G) ∈ closure ((M - M) \ {0}) :=
    BerendMinimal.zero_mem_closure_sdiff hM.closed hinf
  have hinv : BerendDichotomy.FamilyInvariant F (M - M) := fun i =>
    BerendMinimal.isInvariantFamily_sub hM.inv i
  -- Stage I: the difference set is everything
  have hfull : M - M = univ := hStage (M - M) hclosed hne hacc hinv
  -- `-M` is closed and invariant
  have hnegclosed : IsClosed (-M) := by
    have h : (-M : Set G) = Neg.neg '' M := by
      ext z
      simp [Set.mem_neg]
    rw [h]
    exact (hM.closed.isCompact.image continuous_neg).isClosed
  have hneginv : BerendDichotomy.FamilyInvariant F (-M) := by
    rintro i z ⟨m, hm, rfl⟩
    rw [Set.mem_neg] at hm ⊢
    simpa using hM.inv i ⟨-m, hm, rfl⟩
  have hsum : M + -M = univ := by rw [add_neg_eq_sub]; exact hfull
  -- Proposition IV.1 turns `M + (-M) = univ` into `-M = univ`
  have hneg : (-M) = univ :=
    hIV1 M (-M) hM.ne hM.closed hnegclosed hM.inv hneginv hM hsum
  have hMfull : M = univ := by
    have := congrArg Neg.neg hneg
    simpa using this
  -- but `{0}` is a proper closed invariant set, contradicting minimality
  have hsingclosed : IsClosed ({0} : Set G) := isClosed_singleton
  have hsinginv : BerendDichotomy.FamilyInvariant F ({0} : Set G) := by
    rintro i z hz
    have hz0 : z = 0 := by simpa using hz
    subst hz0
    simpa using map_zero (F i)
  have h0sub : ({0} : Set G) ⊆ M := by rw [hMfull]; exact subset_univ _
  have heq : ({0} : Set G) = M := hM.minimal {0} h0sub ⟨0, rfl⟩ hsingclosed hsinginv
  exact Set.singleton_ne_univ 0 (heq.trans hMfull)

end Minimal

/-! ## 3. Berend's Lemma 5.2: finite invariant sets are torsion -/

section Torsion

/-- Iterates of an additive endomorphism are additive. -/
theorem iterate_add (σ : G →+ G) (n : ℕ) (a b : G) :
    σ^[n] (a + b) = σ^[n] a + σ^[n] b := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_add]

/-- Iterates of an additive endomorphism preserve zero. -/
theorem iterate_zero (σ : G →+ G) (n : ℕ) : σ^[n] (0 : G) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

/-- The difference map `x ↦ σ^[n] x - σ^[m] x` as an additive endomorphism. -/
noncomputable def diffHom (σ : G →+ G) (n m : ℕ) : G →+ G where
  toFun x := σ^[n] x - σ^[m] x
  map_zero' := by
    rw [iterate_zero, iterate_zero, sub_self]
  map_add' a b := by
    simp only [iterate_add]
    abel

@[simp] theorem diffHom_apply (σ : G →+ G) (n m : ℕ) (x : G) :
    diffHom σ n m x = σ^[n] x - σ^[m] x := rfl

/-- **Berend (1983), Lemma 5.2.**  A finite set `F` invariant under an
endomorphism `σ`, all of whose difference maps `σ^[n] - σ^[m]` (`n ≠ m`) have
finite fibres, consists of torsion points.

(Berend's Lemma 5.1 supplies the hypothesis in the toral case: the kernel of a
difference of powers of an epimorphism `σ` with no eigenvalue equal to `0` or a
root of unity is finite, and the fibres of an additive map are cosets of its
kernel.) -/
theorem finite_invariant_isTorsion (σ : G →+ G)
    (hfib : ∀ m n : ℕ, m ≠ n → ∀ y : G, {x : G | diffHom σ n m x = y}.Finite)
    {F : Set G} (hF : F.Finite) (hinv : σ '' F ⊆ F) {x : G} (hx : x ∈ F) :
    ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  classical
  -- the forward orbit of `x` stays in the finite set `F`
  have hiter : ∀ k : ℕ, σ^[k] x ∈ F := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hinv ⟨_, ih, rfl⟩
  obtain ⟨a, b, hab, hEq⟩ :=
    hF.exists_lt_map_eq_of_forall_mem (f := fun k : ℕ => σ^[k] x) hiter
  -- hence `x` lies in the kernel of the difference map `σ^[b] - σ^[a]`
  have hx0 : diffHom σ b a x = 0 := by
    simp only [diffHom_apply, hEq, sub_self]
  -- that kernel is a finite subgroup, so the multiples of `x` repeat
  let K : AddSubgroup G := (diffHom σ b a).ker
  have hKfin : (K : Set G).Finite := hfib a b (Nat.ne_of_lt hab) 0
  have hxK : x ∈ K := hx0
  have hmem : ∀ k : ℕ, (k • x : G) ∈ (K : Set G) := by
    intro k
    induction k with
    | zero => simpa using K.zero_mem
    | succ k ih => rw [succ_nsmul]; exact K.add_mem ih hxK
  obtain ⟨p, q, hpq, hEq2⟩ :=
    hKfin.exists_lt_map_eq_of_forall_mem (f := fun k : ℕ => k • x) hmem
  refine ⟨q - p, by omega, ?_⟩
  have hq : q • x = p • x + (q - p) • x := by
    rw [← add_nsmul, Nat.add_sub_cancel' hpq.le]
  have hzero : (q - p) • x = 0 := by
    have h1 : p • x + (0 : G) = p • x + (q - p) • x := by
      rw [add_zero, ← hq]; exact hEq2
    exact (add_left_cancel h1).symm
  exact hzero

/-- **Minimal sets of the family are finite torsion sets** (Berend §5,
Propositions 5.1 + Lemma 5.2): if Stage I and Proposition IV.1 hold for the
family and the chosen member `F i` has finite difference fibres, then every point
of a minimal closed invariant set is a torsion point. -/
theorem exists_pos_nsmul_eq_zero_of_mem_minimal [CompactSpace G] [T2Space G] [Nontrivial G]
    (hStage : BerendDichotomy.ZeroNonisolatedFull F) (hIV1 : PropIV1 F) (i : ι)
    (hfib : ∀ m n : ℕ, m ≠ n → ∀ y : G,
      {x : G | diffHom (F i) n m x = y}.Finite)
    {M : Set G} (hM : BerendMinimal.IsMinimalInvariant (fun i => (F i : G → G)) M)
    {x : G} (hx : x ∈ M) : ∃ k : ℕ, 0 < k ∧ k • x = 0 :=
  finite_invariant_isTorsion (F i) hfib (minimal_finite_of_propIV1 hStage hIV1 hM) (hM.inv i) hx

end Torsion

/-! ## 4. Axiom audit -/

#print axioms CubicTwoStage.BerendPropIV1.minimal_finite_of_propIV1
#print axioms CubicTwoStage.BerendPropIV1.finite_invariant_isTorsion
#print axioms CubicTwoStage.BerendPropIV1.exists_pos_nsmul_eq_zero_of_mem_minimal

end BerendPropIV1
end CubicTwoStage
