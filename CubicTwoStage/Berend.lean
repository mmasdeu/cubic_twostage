/-
Tori, their induced endomorphisms, and lattice integral restrictions.

The former literal `berend_multi_invariance` axiom here was false in general and
has been removed.  The corrected proposition and its canonical proof use
`BerendCorrected`, `BerendCompleteDichotomy`, and the normalized Stage-I
modules.  The declarations below concern quotient maps, continuous unit-prime
torus actions, and the integer lattice action used to state B1.

The quotient viewpoint is essential: the lattice itself is a closed proper
infinite invariant subset of `ℝ × ℂ`, but the multi-invariance dichotomy is
about subsets of the torus.
-/
import CubicTwoStage.Setting
import CubicTwoStage.Lattice

open scoped TensorProduct

namespace CubicTwoStage

/-! ## The torus and its endomorphisms -/

/-- The torus `(ℝ × ℂ)/L`, where `L` is the lattice `σ(𝒪_K)`. -/
abbrev Torus (L : AddSubgroup Pt) : Type := Pt ⧸ L

/-- The endomorphism of the torus induced by an additive map of `ℝ × ℂ` that
preserves `L`. -/
noncomputable def torusMap (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L) :
    Torus L →+ Torus L :=
  QuotientAddGroup.map L L f fun _ hg => hf _ hg

/-- The induced endomorphism on classes. -/
@[simp] lemma torusMap_mk (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L)
    (x : Pt) :
    torusMap L f hf (QuotientAddGroup.mk x) = QuotientAddGroup.mk (f x) :=
  QuotientAddGroup.map_mk L L f _ x

/-- Two torus endomorphisms that agree on `ℝ × ℂ` agree on the torus. -/
lemma torusMap_congr (L : AddSubgroup Pt) {f f' : Pt →+ Pt} (hff' : ∀ x, f x = f' x)
    (hf : ∀ g ∈ L, f g ∈ L) (hf' : ∀ g ∈ L, f' g ∈ L) :
    torusMap L f hf = torusMap L f' hf' := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | _ x => rw [torusMap_mk, torusMap_mk, hff']

/-- An induced torus endomorphism is continuous. -/
lemma continuous_torusMap (L : AddSubgroup Pt) (f : Pt →+ Pt) (hf : ∀ g ∈ L, f g ∈ L)
    (hcont : Continuous f) : Continuous (torusMap L f hf) := by
  refine (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr ?_
  have h : ((torusMap L f hf : Torus L →+ Torus L) : Torus L → Torus L) ∘
      (QuotientAddGroup.mk : Pt → Torus L) = (QuotientAddGroup.mk : Pt → Torus L) ∘ f := by
    funext x
    exact torusMap_mk L f hf x
  rw [h]
  exact QuotientAddGroup.continuous_mk.comp hcont

/-! ## The endomorphisms attached to the unit–prime model -/

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The multiplier of `linFam` preserves the lattice. -/
lemma UnitPrimeModel.linFam_preserves (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    ∀ g ∈ L, ((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom g ∈ L :=
  fun _ hg => D.lattice_linFam i hg

/-- The endomorphism of the torus induced by `μ_{u π^j}`.  This is the element
`s` of Berend's semigroup `Σ = {μ_{uπ^j} : u ∈ 𝒪ˣ, j ≥ 0}`. -/
noncomputable def UnitPrimeModel.torusAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Torus L →+ Torus L :=
  torusMap L ((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom (D.linFam_preserves i)

/-- The induced endomorphism on classes is multiplication by the multiplier. -/
lemma UnitPrimeModel.torusAct_mk (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (x : Pt) :
    D.torusAct i (QuotientAddGroup.mk x) = QuotientAddGroup.mk (D.family.act i x) := by
  rw [UnitPrimeModel.torusAct, torusMap_mk]
  congr 1

/-- The same on the coercions `Pt → Torus L`. -/
lemma UnitPrimeModel.torusAct_mk' (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (x : Pt) :
    D.torusAct i ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' L) (D.family.act i x) := by
  rw [QuotientAddGroup.mk'_apply, D.torusAct_mk, QuotientAddGroup.mk'_apply]

/-- On the index `(u, 0)` the torus action is induced by the unit action. -/
lemma UnitPrimeModel.torusAct_mk'_unit (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (x : Pt) :
    D.torusAct (u, 0) ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' L) (D.actU u x) := by
  rw [D.torusAct_mk', D.family_act_zero]

/-- The action of `(u, j)` on classes composes as `applyList` does. -/
lemma UnitPrimeModel.torusAct_applyList (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (l : List (𝒪ˣ × ℕ)) (x : Pt) :
    D.torusAct i ((QuotientAddGroup.mk' L) (D.applyList l x)) =
      (QuotientAddGroup.mk' L) (D.applyList (l ++ [i]) x) := by
  rw [D.torusAct_mk', D.applyList_append_singleton]

/-- The induced endomorphism is continuous. -/
lemma UnitPrimeModel.continuous_torusAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Continuous (D.torusAct i) := by
  refine continuous_torusMap L _ (D.linFam_preserves i) ?_
  have h : (((D.linFam i : Pt →ₗ[ℝ] Pt)).toAddMonoidHom : Pt → Pt) =
      fun x => D.mult i.1 i.2 ⋆ x := rfl
  rw [h]
  exact continuous_mulC _

/-- **The integral restriction of a real-linear lattice endomorphism**: its
characteristic polynomial is over ℤ, which is the polynomial Berend's (B1)
refers to. -/
noncomputable def latticeAct (L : AddSubgroup Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  LinearMap.restrict (LinearMap.restrictScalars ℤ f)
    (p := AddSubgroup.toIntSubmodule L) (q := AddSubgroup.toIntSubmodule L) hf

/-- **The restriction of `μ_{uπ^j}` to the integral lattice `L`. -/
noncomputable def UnitPrimeModel.lact (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  latticeAct L ((D.linFam i : Pt →ₗ[ℝ] Pt)) (fun x hx => D.lattice_linFam i hx)

/-! ## Berend's theorem -/

/- The literal general statement formerly declared here was false.  The proved
  development uses `BerendMultiInvarianceCorrected`; canonical instances are
  constructed from `BerendCanonicalB1`, `zeroNonisolatedFull_canonical`, and
  Proposition IV.1. -/

end CubicTwoStage
