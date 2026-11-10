import CubicTwoStage.BerendCanonicalProp43

noncomputable section

open Set Filter Topology Module

namespace CubicTwoStage
namespace BerendProp43Canonical
namespace CanonicalProp43

section Subsequence

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- Integer-dual values on a lattice basis are countable. -/
theorem countable_latticeCharacters : Countable (latticeCharacters L) := by
  let f : (latticeCharacters L) → (Fin 3 → ℤ) := fun χ i =>
    restrictLatticeDual χ (latticeDualBasis (L := L) i)
  have hf : Function.Injective f := by
    intro χ ψ h
    apply (latticeCharacterDualEquiv (L := L)).injective
    apply (latticeDualBasis (L := L)).ext
    intro i
    exact congrFun h i
  exact hf.countable

local instance : Countable (latticeCharacters L) := countable_latticeCharacters
local instance : Encodable (latticeCharacters L) := Encodable.ofCountable _

/-- The nonzero characters occurring among the first `k` encoded values. -/
noncomputable def characterPrefix (k : ℕ) : Finset (latticeCharacters L) := by
  classical
  exact ((Finset.range k).image
    (fun n => (Encodable.decode n).getD (0 : latticeCharacters L))).filter (fun χ => χ ≠ 0)

/-- Every nonzero character enters the prefix just after its encode index. -/
theorem mem_characterPrefix_of_encode_lt {χ : latticeCharacters L} (hχ : χ ≠ 0)
    {k : ℕ} (hk : Encodable.encode χ < k) : χ ∈ characterPrefix (L := L) k := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_, hχ⟩
  apply Finset.mem_image.mpr
  refine ⟨Encodable.encode χ, Finset.mem_range.mpr hk, ?_⟩
  simp [Encodable.encodek]

section Sequence

variable (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
variable (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
variable (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite)

include D i B1 H hH

/-- Arbitrarily late times which are good for a whole encoded prefix. -/
theorem exists_gt_good_prefix (k N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∀ χ ∈ characterPrefix (L := L) k,
      χ ∉ latticeCharacterAnnihilator (iteratedImageSubgroup D i H m) := by
  classical
  let γ : {χ // χ ∈ characterPrefix (L := L) k} → latticeCharacters L := fun χ => χ.1
  have hγ : ∀ χ, γ χ ≠ 0 := by
    intro χ
    exact (Finset.mem_filter.mp χ.property).2
  obtain ⟨m, hm, hgood⟩ := exists_gt_forall_not_mem_annihilator
    D i B1 H hH γ hγ N
  refine ⟨m, hm, ?_⟩
  intro χ hχ
  exact hgood ⟨χ, hχ⟩

/-- The least good time for a prefix beyond a prescribed bound. -/
noncomputable def nextGood (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite) (k N : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_gt_good_prefix D i B1 H hH k N)

/-- A recursively increasing sequence of good times. -/
noncomputable def goodTime (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
    (H : AddSubgroup (Torus L)) (hH : (H : Set (Torus L)).Infinite) : ℕ → ℕ
  | 0 => nextGood D i B1 H hH 0 0
  | k + 1 => nextGood D i B1 H hH (k + 1) (goodTime D i B1 H hH k)

theorem goodTime_lt_succ (k : ℕ) : goodTime D i B1 H hH k < goodTime D i B1 H hH (k + 1) := by
  classical
  exact (Nat.find_spec (exists_gt_good_prefix D i B1 H hH (k + 1)
    (goodTime D i B1 H hH k))).1

theorem strictMono_goodTime : StrictMono (goodTime D i B1 H hH) :=
  strictMono_nat_of_lt_succ (goodTime_lt_succ D i B1 H hH)

/-- Every member of a prefix is nontrivial on that prefix's selected image. -/
theorem not_mem_annihilator_goodTime (k : ℕ) {χ : latticeCharacters L}
    (hχ : χ ∈ characterPrefix (L := L) k) :
    χ ∉ latticeCharacterAnnihilator
      (iteratedImageSubgroup D i H (goodTime D i B1 H hH k)) := by
  classical
  cases k with
  | zero =>
      exact (Nat.find_spec (exists_gt_good_prefix D i B1 H hH 0 0)).2 χ hχ
  | succ k =>
      exact (Nat.find_spec (exists_gt_good_prefix D i B1 H hH (k + 1)
        (goodTime D i B1 H hH k))).2 χ hχ

/-- **Canonical Proposition 4.3 character subsequence.** -/
theorem exists_strictMono_eventually_character_nontrivial :
    ∃ m : ℕ → ℕ, StrictMono m ∧ ∀ χ : latticeCharacters L, χ ≠ 0 →
      ∀ᶠ n in atTop, ∃ h ∈ iteratedImageSubgroup D i H (m n), characterOf χ h ≠ 0 := by
  classical
  refine ⟨goodTime D i B1 H hH, strictMono_goodTime D i B1 H hH, ?_⟩
  intro χ hχ
  apply eventually_atTop.mpr
  refine ⟨Encodable.encode χ + 1, ?_⟩
  intro n hn
  have hmem : χ ∈ characterPrefix (L := L) n :=
    mem_characterPrefix_of_encode_lt hχ (by omega)
  have hgood := not_mem_annihilator_goodTime D i B1 H hH n hmem
  rw [mem_latticeCharacterAnnihilator] at hgood
  push_neg at hgood
  exact hgood

end Sequence

section Net

variable (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
variable (B1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((D.intLact i) ^ n)))
variable [CompactSpace (Torus L)] [T2Space (Torus L)]
  [SecondCountableTopology (Torus L)] [IsClosed (L : Set Pt)]

include B1

open BerendLatticeDensity

/-- **Berend Proposition 4.3 for the canonical torus model.**  Every infinite
closed subgroup has arbitrarily fine nets among its images under the selected
canonical endomorphism. -/
theorem exists_net_of_infinite_closed
    (H : AddSubgroup (Torus L)) (hHinf : Infinite H)
    (hHclosed : IsClosed (H : Set (Torus L))) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : Torus L, ∃ h ∈ H,
      dist x ((D.torusAct i)^[n] h) < ε := by
  have hH : (H : Set (Torus L)).Infinite := Set.infinite_coe_iff.mp hHinf
  obtain ⟨m, hmono, hchar⟩ := exists_strictMono_eventually_character_nontrivial
    D i B1 H hH
  let G : ℕ → AddSubgroup (Torus L) := fun n => iteratedImageSubgroup D i H (m n)
  letI : ∀ n, CompactSpace (G n) := fun n =>
    isCompact_iff_compactSpace.mp (isCompact_iteratedImageSubgroup
      D i H hHclosed (m n))
  have hG : ∀ n, IsClosed (G n : Set (Torus L)) := by
    intro n
    exact isClosed_iteratedImageSubgroup D i H hHclosed (m n)
  obtain ⟨n, hn⟩ := exists_net_of_latticeCharacter_nontrivial_eventually
    (latticeDualBasis (L := L)) G hG hchar hε
  refine ⟨m n, ?_⟩
  intro x
  obtain ⟨y, hy, hdist⟩ := hn x
  obtain ⟨h, hh, rfl⟩ := hy
  refine ⟨h, hh, ?_⟩
  rw [torusIterate_apply] at hdist
  exact hdist

end Net

end Subsequence

end CanonicalProp43
end BerendProp43Canonical
end CubicTwoStage

#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.exists_strictMono_eventually_character_nontrivial
#print axioms CubicTwoStage.BerendProp43Canonical.CanonicalProp43.exists_net_of_infinite_closed
