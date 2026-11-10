/-
The multi-invariance argument of §3: Berend's theorem applied to the image of
the uncovered set in the torus `(ℝ × ℂ)/L`, the periodic unit orbits, and the
recovery of a representative in `σ(K)`.

The statement lives on the torus.  It cannot be stated on `ℝ × ℂ` directly:
the lattice `L = σ(𝒪_K)` is itself closed, invariant under the whole semigroup
and proper, and it is infinite, so "every closed invariant proper subset of
`ℝ × ℂ` is finite" is false there.  What Berend gives is that the *image* in
the torus is finite, hence that the uncovered set lies in finitely many cosets
of `L`.
-/
import CubicTwoStage.Berend
import CubicTwoStage.Periodic

open scoped TensorProduct

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-! ### Iterates of the unit action on the torus -/

section Torus
variable {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- A left inverse of an endomorphism of `ℝ × ℂ` that preserves the lattice
induces a left inverse on the torus. -/
lemma torusMap_leftInverse (L : AddSubgroup Pt) {f g : Pt →+ Pt}
    (hf : ∀ x ∈ L, f x ∈ L) (hg : ∀ x ∈ L, g x ∈ L) (h : ∀ x, g (f x) = x) :
    Function.LeftInverse (torusMap L g hg) (torusMap L f hf) := by
  intro z
  induction z using QuotientAddGroup.induction_on with
  | _ a => rw [torusMap_mk, torusMap_mk, h]

/-- The `n`-th iterate of the torus action of `ε` on a class is the class of the
`n`-th iterate of the unit action on `ℝ × ℂ`. -/
lemma UnitPrimeModel.torusAct_iterate_mk (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ) (n : ℕ)
    (x : Pt) :
    (D.torusAct (ε, 0))^[n] ((QuotientAddGroup.mk' L) x) =
      (QuotientAddGroup.mk' L) ((D.actU ε)^[n] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        UnitPrimeModel.torusAct_mk'_unit]

/-- The torus action of a unit is injective: `unit_inv u` inverts it on the
lattice, and `L` is invariant under both. -/
lemma UnitPrimeModel.torusAct_unit_injective (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) :
    Function.Injective (D.torusAct (u, 0)) := by
  refine Function.LeftInverse.injective (torusMap_leftInverse L
    (f := ((D.linFam (u, 0) : Pt →ₗ[ℝ] Pt)).toAddMonoidHom)
    (g := addHomMulC (D.unit_inv u)) (D.linFam_preserves (u, 0))
    (fun g hg => D.lattice_unit_inv u g hg) ?_)
  intro x
  show D.unit_inv u ⋆ (D.mult u 0 ⋆ x) = x
  rw [D.mult_zero, ← mulC_assoc, D.unit_inv_mul', oneC_mulC]

end Torus

/-! ### Finiteness of the torus image of the uncovered set -/

/- The finite uncovered image theorem is proved under the corrected Berend
  proposition in `BerendCorrected.finite_torus_image_of_orbit_avoid_corrected`. -/

/-! ### Periodic unit orbits on the finite torus image -/

/-- Each uncovered point is fixed by some positive power of the unit modulo the
lattice: its class is a point of the finite set `q '' uncovered`, on which `ε`
acts injectively. -/
theorem unit_period_of_finite_torus_image (𝒪 : Subring K) (Nm : AbsNorm K)
    (σ : K → Pt) (L : AddSubgroup Pt) (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hfin : Set.Finite ((fun x : Pt => (QuotientAddGroup.mk' L) x) '' uncovered 𝒪 Nm σ))
    (hstable : ∀ x ∈ uncovered 𝒪 Nm σ, ∀ u : 𝒪ˣ, D.actU u x ∈ uncovered 𝒪 Nm σ)
    (hLσ : ∀ w ∈ L, ∃ g : 𝒪, σ g = w)
    {x : Pt} (hx : x ∈ uncovered 𝒪 Nm σ) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : 𝒪, D.actU (ε ^ n) x - x = σ g := by
  classical
  have hmap : ∀ z ∈ (fun x : Pt => (QuotientAddGroup.mk' L) x) '' uncovered 𝒪 Nm σ,
      D.torusAct (ε, 0) z ∈ (fun x : Pt => (QuotientAddGroup.mk' L) x) '' uncovered 𝒪 Nm σ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨D.actU ε y, hstable y hy ε, (D.torusAct_mk'_unit ε y).symm⟩
  obtain ⟨n, hn, hper⟩ := periodic_of_finite_image hfin hmap
    (D.torusAct_unit_injective ε) ⟨x, hx, rfl⟩
  have hper' : (QuotientAddGroup.mk' L) ((D.actU ε)^[n] x) =
      (QuotientAddGroup.mk' L) x := by
    rw [← UnitPrimeModel.torusAct_iterate_mk]
    exact hper
  have hmem : D.actU (ε ^ n) x - x ∈ L := by
    rw [D.actU_pow ε n x]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (by simpa using hper')
  obtain ⟨g, hg⟩ := hLσ _ hmem
  exact ⟨n, hn, g, hg.symm⟩

/-! ### Representatives in `σ(K)` -/

/-- A periodic unit orbit has a representative in `K`: if
`act(εⁿ) x - x = σ g` then `x = σ(g / (εⁿ - 1))`.  The condition `hne`
eliminates the possibility that a nontrivial unit has a fixed vector, and
`hdenom` supplies the nonzero denominator used in that representative. -/
theorem representative_of_periodic_unit (𝒪 : Subring K) (Nm : AbsNorm K)
    (σ : K → Pt) (L : AddSubgroup Pt) (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ)
    (hact : ∀ (z : K) (n : ℕ), D.actU (ε ^ n) (σ z) = σ ((ε : K) ^ n * z))
    (hσadd : ∀ a b : K, σ (a + b) = σ a + σ b)
    (hσneg : ∀ a : K, σ (-a) = -σ a)
    (hne : ∀ n : ℕ, 0 < n → ∀ z : Pt, D.actU (ε ^ n) z = z → z = 0)
    (hdenom : ∀ n : ℕ, 0 < n → (ε : K) ^ n - 1 ≠ 0) :
    ∀ x ∈ uncovered 𝒪 Nm σ,
      (∃ n : ℕ, 0 < n ∧ ∃ g : 𝒪, D.actU (ε ^ n) x - x = σ g) →
      ∃ y : K, x = σ y := by
  intro x hx hperiod
  obtain ⟨n, hn, g, heq⟩ := hperiod
  let y : K := g / ((ε : K) ^ n - 1)
  have hy : D.actU (ε ^ n) (σ y) - σ y = σ g := by
    calc
      D.actU (ε ^ n) (σ y) - σ y = σ ((ε : K) ^ n * y - y) := by
        rw [hact]
        simp only [sub_eq_add_neg, hσadd, hσneg]
      _ = σ g := by
        congr 1
        dsimp [y]
        have hc := mul_div_cancel₀ (b := (ε : K) ^ n - 1) g (hdenom n hn)
        convert hc using 1 <;> ring
  have hdiff : D.actU (ε ^ n) x - D.actU (ε ^ n) (σ y) = x - σ y := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp (heq.trans hy.symm)
  refine ⟨y, ?_⟩
  have hfixed := hne n hn (x - σ y)
  apply sub_eq_zero.mp
  apply hfixed
  rw [map_sub, hdiff]

end CubicTwoStage
