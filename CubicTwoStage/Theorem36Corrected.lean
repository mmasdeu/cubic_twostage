/-
# Theorem 3.6 with the corrected (B3), axiom-free apart from one explicit `Prop`

The project uses Berend's theorem at exactly one place:
`CubicTwoStage.finite_torus_image_of_orbit_avoid` (`Uncovered.lean`), which
calls the axiom `berend_multi_invariance` once.  `CubicTwoStage/BerendCorrected.lean`
replaces it by `finite_torus_image_of_orbit_avoid_corrected`, which takes a
proof `H` of the explicitly stated proposition
`BerendMultiInvarianceCorrected` instead of appealing to an axiom, and whose
(B3) is the corrected `RationallyIndependentPair`, *proved* for the unit–prime
model by `rational_independence_corrected`.

This module re-runs the §3 chain with that substitution:

* `thm_uncovered_corrected` — Theorem 3.6 (torus form) from `H`;
* `thm_uncovered_field_corrected` — Theorem 3.6 from field data, with the
  corrected (B3) *discharged* from `Nm π = p > 1` and `ε` of infinite order;
* `thm_intro_equiv_corrected` — Theorems 3.3 and 3.6 assembled, from `H`.

Every theorem is proved; the only hypothesis that is not derived from the
project's data is `H`.  `#print axioms` on all three returns
`[propext, Classical.choice, Quot.sound]` (see `CubicTwoStage/BerendCheck.lean`),
so the axiom `berend_multi_invariance` is not used.  The two rigidity stages used to construct `H` for the canonical
model are completed in the normalized Stage-I modules and the canonical
Proposition-4.3 assembly.
-/
import CubicTwoStage.Main
import CubicTwoStage.BerendCorrected

open scoped TensorProduct

set_option linter.unusedVariables false

namespace CubicTwoStage

variable {K : Type*} [Field K]

theorem thm_uncovered_corrected (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (L : AddSubgroup Pt)
    (D : UnitPrimeModel L 𝒪) (W : Set Pt) (ε : 𝒪ˣ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lact i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (B3 : RationallyIndependentPair D.linFam)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZL B1 B2 B3
      D.linFam_comm)
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty)
    (hWtrans : ∀ g ∈ L, ∀ x : Pt, (x ∈ W ↔ x - g ∈ W))
    (havoid : ∀ y ∈ uncovered 𝒪 Nm σ, ∀ l, D.applyList l y ∉ W)
    (hstable : ∀ x ∈ uncovered 𝒪 Nm σ, ∀ u : 𝒪ˣ, D.actU u x ∈ uncovered 𝒪 Nm σ)
    (hact : ∀ (z : K) (n : ℕ), D.actU (ε ^ n) (σ z) = σ ((ε : K) ^ n * z))
    (hσadd : ∀ a b : K, σ (a + b) = σ a + σ b)
    (hσneg : ∀ a : K, σ (-a) = -σ a)
    (hne : ∀ n : ℕ, 0 < n → ∀ z : Pt, D.actU (ε ^ n) z = z → z = 0)
    (hdenom : ∀ n : ℕ, 0 < n → (ε : K) ^ n - 1 ≠ 0)
    (hLσ : ∀ w ∈ L, ∃ g : 𝒪, σ g = w) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered 𝒪 Nm σ, ∃ c ∈ F,
      (∃ y : K, c = σ y) ∧ x - c ∈ L := by
  classical
  have hfin := finite_torus_image_of_orbit_avoid_corrected 𝒪 Nm σ L D W hZL B1 B2 B3 H
    hWopen hWnonempty hWtrans havoid
  set Z : Set (Torus L) := (fun x : Pt => (QuotientAddGroup.mk' L) x) '' uncovered 𝒪 Nm σ
    with hZdef
  -- a choice of uncovered representative for each class of the finite set `Z`
  let rep : Torus L → Pt := fun z => if h : z ∈ Z then Classical.choose h else 0
  have hrep : ∀ z (h : z ∈ Z), rep z ∈ uncovered 𝒪 Nm σ ∧ (QuotientAddGroup.mk' L) (rep z) = z := by
    intro z hz
    dsimp only [rep]
    rw [dif_pos hz]
    exact Classical.choose_spec hz
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro x hx
  have hxZ : (QuotientAddGroup.mk' L) x ∈ Z := ⟨x, hx, rfl⟩
  obtain ⟨hrepU, hrepq⟩ := hrep _ hxZ
  refine ⟨rep ((QuotientAddGroup.mk' L) x),
    Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hxZ, rfl⟩, ?_, ?_⟩
  · exact representative_of_periodic_unit 𝒪 Nm σ L D ε hact hσadd hσneg hne hdenom _
      hrepU (unit_period_of_finite_torus_image 𝒪 Nm σ L D ε hfin hstable hLσ hrepU)
  · exact QuotientAddGroup.eq_iff_sub_mem.mp hrepq.symm


theorem thm_uncovered_field_corrected {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}
    (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (m : ℕ)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : 𝒪), ∃ k : ℕ, ∃ h ∈ 𝒪,
      (1 + π ^ m * ((g : 𝒪) : K)) - ((ε : 𝒪) : K) ^ k = π ^ (m + j) * h)
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    (hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly (((FM.toModel ε π hπO hπ0).lact i) ^ n)))
    (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ,
        LinearMap.baseChange ℂ (((FM.toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt)) x =
          μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) (FM.toModel ε π hπO hπ0).linFam FM.lattice
      (FM.toModel ε π hπO hπ0).linFam_preserves hZL B1 B2
      (rational_independence_corrected FM ε π hπO hπ0 hεpow p hp hπN)
      (FM.toModel ε π hπO hπ0).linFam_comm) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered 𝒪 Nm FM.σ, ∃ c ∈ F,
      (∃ y : K, c = FM.σ y) ∧ x - c ∈ FM.lattice := by
  refine thm_uncovered_corrected 𝒪 Nm FM.σ FM.lattice (FM.toModel ε π hπO hπ0) (FM.W π m) ε
    hZL B1 B2 (rational_independence_corrected FM ε π hπO hπ0 hεpow p hp hπN) H
      (FM.W_open π m) (FM.W_nonempty π m hπ0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `W` is a union of classes
    intro g hg x
    obtain ⟨g₀, hg₀⟩ := FM.lattice_eq_image g hg
    rw [← hg₀]
    exact FM.W_trans π m g₀ x
  · -- the orbit avoids `W`
    exact fun y hy l => FM.orbit_avoid ε π m hπO hπ0 hpadic hy l
  · -- units preserve the uncovered set
    intro x hx u
    exact FM.uncovered_actU u hx
  · -- the unit action on `σ`-images
    exact fun z n => FM.actU_hact ε π hπO hπ0 z n
  · exact FM.σ_add
  · exact FM.σ_neg
  · -- no nonzero fixed vectors
    intro n hn z hz
    exact FM.actU_eq_self hπO hπ0 (hεpow n hn) hz
  · -- `εⁿ - 1 ≠ 0`
    intro n hn
    exact FieldModel.denom_ne_zero (hεpow n hn)
  · -- `L = σ(𝒪)`
    exact fun w hw => FM.lattice_eq_image w hw


theorem thm_intro_equiv_corrected {K : Type*} [Field K] (𝒪 : Subring K) (N : AbsNorm K)
    (FM : FieldModel K 𝒪 N) (ε : 𝒪ˣ) (π : K) (m : ℕ)
    (hfrac : ∀ x : K, ∃ α ∈ 𝒪, ∃ β ∈ 𝒪, β ≠ 0 ∧ x = α / β)
    (C : Set Pt) (V : Pt → Set Pt)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : 𝒪), ∃ k : ℕ, ∃ h ∈ 𝒪,
      (1 + π ^ m * ((g : 𝒪) : K)) - ((ε : 𝒪) : K) ^ k = π ^ (m + j) * h)
    (hVopen : ∀ c, IsOpen (V c))
    (hVtrans : ∀ c g, g ∈ FM.lattice → ∀ x, x ∈ V (c + g) ↔ x - g ∈ V c)
    (hCtrans : ∀ c ∈ C, ∀ g ∈ FM.lattice, c + g ∈ C)
    (hfund : ∀ x : Pt, ∃ g ∈ FM.lattice, x - g ∈ unitCube)
    (hBerend : (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧
        N (x - (q1 + q2⁻¹)) < (N q2)⁻¹) →
      (∀ x : Pt, ∃ c ∈ C, x ∈ V c))
    (hsub : (∀ x : Pt, ∃ c ∈ C, x ∈ V c) →
      (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧
        N (x - (q1 + q2⁻¹)) < (N q2)⁻¹))
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    (hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice))
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly (((FM.toModel ε π hπO hπ0).lact i) ^ n)))
    (p : ℕ) (hp : 1 < p) (hπN : N π = (p : ℚ≥0))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : 𝒪ˣ × ℕ,
        LinearMap.baseChange ℂ (((FM.toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt)) x =
          μ i • x) →
      ∃ i : 𝒪ˣ × ℕ, 1 < ‖μ i‖)
    (H : BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) (FM.toModel ε π hπO hπ0).linFam FM.lattice
      (FM.toModel ε π hπO hπ0).linFam_preserves hZL B1 B2
      (rational_independence_corrected FM ε π hπO hπ0 hεpow p hp (hπN)) 
      (FM.toModel ε π hπO hπ0).linFam_comm) :
    (∃ F : Finset Pt, ∀ x ∈ uncovered 𝒪 N FM.σ, ∃ c ∈ F,
      (∃ y : K, c = FM.σ y) ∧ x - c ∈ FM.lattice) ∧
      (IsTwoStageEuclidean 𝒪 N ↔
        ∃ F : Finset Pt, (∀ c ∈ F, c ∈ C) ∧ unitCube ⊆ ⋃ c ∈ F, V c) :=
  ⟨thm_uncovered_field_corrected FM ε π m hπO hπ0 hεpow hpadic hZL B1 p hp hπN B2 H,
    (thm_equiv 𝒪 N hfrac FM.lattice C V hVopen hVtrans hCtrans hfund hBerend hsub).2⟩


end CubicTwoStage
