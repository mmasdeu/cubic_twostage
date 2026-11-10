import CubicTwoStage.BerendCanonicalAnnihilator
import CubicTwoStage.BerendProp43Finite

noncomputable section

open Set Filter Topology Module

namespace CubicTwoStage
namespace BerendProp43Canonical
namespace CanonicalProp43

section Iterates

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The canonical torus endomorphism iterated by composition. -/
noncomputable def torusIterate (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    ℕ → ((Torus L) →+ (Torus L))
  | 0 => AddMonoidHom.id _
  | n + 1 => (D.torusEndAct i).comp (torusIterate D i n)

@[simp] theorem torusIterate_apply (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (n : ℕ) (z : Torus L) :
    torusIterate D i n z = (D.torusEndAct i)^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [torusIterate, AddMonoidHom.comp_apply, ih, Function.iterate_succ_apply']

theorem continuous_torusIterate (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (n : ℕ) :
    Continuous (torusIterate D i n) := by
  have h : (torusIterate D i n : Torus L → Torus L) = (D.torusEndAct i)^[n] :=
    funext (torusIterate_apply D i n)
  rw [h]
  exact (D.continuous_torusEndAct i).iterate n

/-- The image of `H` under the `n`-th canonical iterate. -/
noncomputable def iteratedImageSubgroup (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (H : AddSubgroup (Torus L)) (n : ℕ) : AddSubgroup (Torus L) :=
  H.map (torusIterate D i n)

@[simp] theorem mem_annihilator_iteratedImage_iff
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (H : AddSubgroup (Torus L))
    (χ : latticeCharacters L) (n : ℕ) :
    χ ∈ latticeCharacterAnnihilator (iteratedImageSubgroup D i H n) ↔
      (dualCharacterAct D i)^[n] χ ∈ latticeCharacterAnnihilator H := by
  simp only [mem_latticeCharacterAnnihilator]
  constructor
  · intro h x hx
    rw [characterOf_dualCharacterAct_iterate_apply]
    rw [← torusIterate_apply]
    apply h (torusIterate D i n x)
    exact ⟨x, hx, rfl⟩
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [torusIterate_apply, ← characterOf_dualCharacterAct_iterate_apply]
    exact h x hx

theorem isCompact_iteratedImageSubgroup [CompactSpace (Torus L)]
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (H : AddSubgroup (Torus L))
    (hH : IsClosed (H : Set (Torus L))) (n : ℕ) :
    IsCompact (iteratedImageSubgroup D i H n : Set (Torus L)) := by
  exact hH.isCompact.image (continuous_torusIterate D i n)

theorem isClosed_iteratedImageSubgroup [CompactSpace (Torus L)] [T2Space (Torus L)]
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (H : AddSubgroup (Torus L))
    (hH : IsClosed (H : Set (Torus L))) (n : ℕ) :
    IsClosed (iteratedImageSubgroup D i H n : Set (Torus L)) := by
  exact (isCompact_iteratedImageSubgroup D i H hH n).isClosed

/-- The canonical torus endomorphism is surjective since it lifts a real-linear
equivalence. -/
theorem surjective_torusEndAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Function.Surjective (D.torusEndAct i) := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  refine ⟨(QuotientAddGroup.mk' L) ((D.linFam i).symm x), ?_⟩
  rw [D.torusEndAct_mk']
  congr 1
  exact (D.linFam i).apply_symm_apply x

/-- Every canonical torus iterate is surjective. -/
theorem surjective_torusIterate (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (n : ℕ) :
    Function.Surjective (torusIterate D i n) := by
  have h : (torusIterate D i n : Torus L → Torus L) = (D.torusEndAct i)^[n] :=
    funext (torusIterate_apply D i n)
  rw [h]
  exact (surjective_torusEndAct D i).iterate n

/-- Precomposition with a surjective canonical iterate is injective on nonzero
lattice characters. -/
theorem dualCharacterAct_iterate_ne_zero
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) {χ : latticeCharacters L}
    (hχ : χ ≠ 0) (n : ℕ) : (dualCharacterAct D i)^[n] χ ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ : ∃ z, characterOf χ z ≠ 0 := by
    by_contra h
    push_neg at h
    apply characterOf_ne_zero hχ
    apply AddMonoidHom.ext
    intro z
    exact h z
  obtain ⟨y, hy⟩ := surjective_torusIterate D i n z
  have hm : characterOf ((dualCharacterAct D i)^[n] χ) y = 0 := by
    rw [hzero]
    change characterHom 0 y = 0
    simp
  rw [characterOf_dualCharacterAct_iterate_apply] at hm
  rw [torusIterate_apply] at hy
  rw [hy] at hm
  exact hz hm

end Iterates

section RationalNoCover

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- Rationalization sends canonical character iterates to powers of the dual
rational action. -/
theorem ratifyLinear_dualCharacterAct_iterate
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (χ : latticeCharacters L) (n : ℕ) :
    ratifyLinear ((dualCharacterAct D i)^[n] χ) =
      ((ratAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt)
        (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)).dualMap ^ n)
        (ratifyLinear χ) := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply,
        ratifyLinear_dualCharacterAct, ih]

/-- A rationalized annihilator character lies in the annihilator span. -/
theorem ratifyLinear_mem_rationalAnnihilatorSpan
    {H : AddSubgroup (Torus L)} {χ : latticeCharacters L}
    (hχ : χ ∈ latticeCharacterAnnihilator H) :
    ratifyLinear χ ∈ rationalAnnihilatorSpan H := by
  apply Submodule.subset_span
  refine ⟨⟨ratifyLinear χ, ?_⟩, rfl⟩
  exact ⟨χ, hχ, rfl⟩

/-- **Canonical algebraic Proposition 4.3 obstruction.**  No finite set of
nonzero lattice characters can have one of its members annihilate every
positive iterate of an infinite subgroup. -/
theorem not_finite_cover_latticeCharacter_annihilator
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite)
    {κ : Type*} [Finite κ] (γ : κ → latticeCharacters L) (hγ : ∀ j, γ j ≠ 0) :
    ¬ (∀ m : ℕ, 0 < m → ∃ j, γ j ∈ latticeCharacterAnnihilator
      (iteratedImageSubgroup D i H m)) := by
  intro hcover
  let f : ratSpan (AddSubgroup.toIntSubmodule L) →ₗ[ℚ]
      ratSpan (AddSubgroup.toIntSubmodule L) :=
    ratAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt)
      (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)
  have hB1Q : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (f ^ n)) := by
    exact irreducible_charpoly_ratAct_of_b1 _ _ _ B1
  have hγQ : ∀ j, ratifyLinear (γ j) ≠ 0 := by
    intro j hz
    apply hγ j
    apply ratifyLinear_injective
    simpa only [map_zero] using hz
  have hr : Module.finrank ℚ (rationalAnnihilatorSpan H) <
      Module.finrank ℚ (ratSpan (AddSubgroup.toIntSubmodule L)) := by
    rw [finrank_ratSpan_eq_three]
    exact finrank_rationalAnnihilatorSpan_lt H hH
  apply BerendProp43Finite.not_finite_cover_comp_pow_mem f
    (surjective_ratAct D i) hB1Q (fun j => ratifyLinear (γ j)) hγQ
    (rationalAnnihilatorSpan H) hr
  intro m hm
  obtain ⟨j, hj⟩ := hcover m hm
  refine ⟨j, ?_⟩
  have hj' : (dualCharacterAct D i)^[m] (γ j) ∈ latticeCharacterAnnihilator H :=
    (mem_annihilator_iteratedImage_iff D i H (γ j) m).mp hj
  have hmem := ratifyLinear_mem_rationalAnnihilatorSpan hj'
  rw [ratifyLinear_dualCharacterAct_iterate] at hmem
  change ((f ^ m).dualMap) (ratifyLinear (γ j)) ∈ rationalAnnihilatorSpan H
  rw [dualMap_pow]
  exact hmem

/-- Every finite family of nonzero characters has arbitrarily late times at
which all of its members are nontrivial on the corresponding image subgroup. -/
theorem exists_gt_forall_not_mem_annihilator
    (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite)
    {κ : Type*} [Finite κ] (γ : κ → latticeCharacters L) (hγ : ∀ j, γ j ≠ 0)
    (N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∀ j, γ j ∉ latticeCharacterAnnihilator
      (iteratedImageSubgroup D i H m) := by
  classical
  by_contra h
  push_neg at h
  let δ : κ → latticeCharacters L := fun j => (dualCharacterAct D i)^[N] (γ j)
  have hδ : ∀ j, δ j ≠ 0 := by
    intro j
    exact dualCharacterAct_iterate_ne_zero D i (hγ j) N
  apply not_finite_cover_latticeCharacter_annihilator D i B1 H hH δ hδ
  intro m hm
  obtain ⟨j, hj⟩ := h (N + m) (by omega)
  refine ⟨j, ?_⟩
  rw [mem_annihilator_iteratedImage_iff] at hj ⊢
  change (dualCharacterAct D i)^[m] ((dualCharacterAct D i)^[N] (γ j)) ∈
    latticeCharacterAnnihilator H
  rw [← Function.iterate_add_apply, Nat.add_comm m N]
  exact hj

end RationalNoCover

end CanonicalProp43
end BerendProp43Canonical
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.mem_annihilator_iteratedImage_iff
#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.ratifyLinear_dualCharacterAct_iterate
#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.not_finite_cover_latticeCharacter_annihilator
