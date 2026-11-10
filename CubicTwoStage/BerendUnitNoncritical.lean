/-
# Infinite-order units are non-critical at the real place

For an infinite-order unit `ε` in the lattice of a `FieldModel`, the real
archimedean modulus is not one.  If it were, the norm identity would force
both other eigen-moduli to be one as well.  Every coordinate of every power
`ε^n` would then be bounded by one.  The images of these powers would lie in
the intersection of a bounded ball with the discrete lattice, a finite set,
but `hεpow` makes that sequence injective.

This is a discrete-lattice proof of the required special case of Kronecker's
Lemma.  It does not use the old Berend axiom or add any assumptions to the
unit–prime model.
-/
import CubicTwoStage.BerendCofinality
import CubicTwoStage.BerendTransitive

open Set

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendUnitNoncritical

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- The coordinate embedding is injective. -/
theorem sigma_injective (FM : FieldModel K 𝒪 Nm) : Function.Injective FM.σ := by
  intro a b hab
  apply sub_eq_zero.mp
  apply FM.σ_eq_zero
  rw [FM.σ_sub, hab, sub_self]

/-- All eigen-moduli of a power of a critical unit are one. -/
theorem lamAbs_pow_eq_one_of_real_eq_one (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ)
    (hU : lamAbs (FM.σ (((u : 𝒪) : K))) 0 = 1) (n : ℕ) (i : Fin 3) :
    lamAbs (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) i = 1 := by
  have h0 : lamAbs (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) 0 = 1 := by
    rw [BerendCofinality.lamAbs_sigma_pow, hU, one_pow]
  have hprod := BerendCofinality.lamAbs_sigma_unit_product FM (u ^ n)
  rw [h0, one_mul] at hprod
  have h1 : lamAbs (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) 1 = 1 := by
    nlinarith [lamAbs_nonneg (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) 1]
  have h2 : lamAbs (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) 2 = 1 := by
    rw [← lamAbs_one_eq_two]
    exact h1
  fin_cases i <;> assumption

/-- If the real modulus is one, every power has sup norm at most one. -/
theorem norm_sigma_pow_le_one_of_real_eq_one (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ)
    (hU : lamAbs (FM.σ (((u : 𝒪) : K))) 0 = 1) (n : ℕ) :
    ‖FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => ?_)
  rw [Real.norm_eq_abs]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · rw [← lamAbs_zero_eq_abs]
    exact le_of_eq (lamAbs_pow_eq_one_of_real_eq_one FM u hU n 0)
  · change |(cplxOf (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K)))).re| ≤ 1
    rw [← lamAbs_pow_eq_one_of_real_eq_one FM u hU n 1]
    exact Complex.abs_re_le_norm _
  · change |(cplxOf (FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K)))).im| ≤ 1
    rw [← lamAbs_pow_eq_one_of_real_eq_one FM u hU n 1]
    exact Complex.abs_im_le_norm _

/-- An infinite-order unit is not of real-modulus one. -/
theorem lamAbs_real_ne_one (FM : FieldModel K 𝒪 Nm)
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)] (u : 𝒪ˣ)
    (hpow : ∀ n : ℕ, 0 < n → (((u : 𝒪) : K)) ^ n ≠ 1) :
    lamAbs (FM.σ (((u : 𝒪) : K))) 0 ≠ 1 := by
  intro hU
  have hfin : (Metric.closedBall (0 : Pt) 1 ∩ (FM.lattice : Set Pt)).Finite := by
    haveI : DiscreteTopology FM.lattice :=
      ‹DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)›
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  have hsubset : (Set.range fun n : ℕ => FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) ⊆
      Metric.closedBall (0 : Pt) 1 ∩ (FM.lattice : Set Pt) := by
    rintro w ⟨n, rfl⟩
    exact ⟨by simpa [Metric.mem_closedBall] using norm_sigma_pow_le_one_of_real_eq_one FM u hU n,
      FM.mem_lattice.mpr ⟨u ^ n, rfl⟩⟩
  have hfinite : (Set.range fun n : ℕ => FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))).Finite :=
    hfin.subset hsubset
  have hnf : ¬ IsOfFinOrder u := by
    intro hfin
    obtain ⟨n, hn, hu⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    apply hpow n hn
    exact congrArg (fun v : 𝒪ˣ => (v : K)) hu
  have hinj : Function.Injective (fun n : ℕ => FM.σ ((((u ^ n : 𝒪ˣ) : 𝒪) : K))) := by
    intro n m hnm
    dsimp only at hnm
    have hcoe : (((u ^ n : 𝒪ˣ) : 𝒪) : K) = (((u : 𝒪) : K)) ^ n := by
      rw [Units.val_pow_eq_pow_val]
      rfl
    have hcoem : (((u ^ m : 𝒪ˣ) : 𝒪) : K) = (((u : 𝒪) : K)) ^ m := by
      rw [Units.val_pow_eq_pow_val]
      rfl
    rw [hcoe, hcoem] at hnm
    have hp : (((u : 𝒪) : K)) ^ n = (((u : 𝒪) : K)) ^ m := by
      apply sigma_injective FM
      simpa only [FM.σ_mul_pow] using hnm
    apply (injective_pow_iff_not_isOfFinOrder (x := u).mpr hnf)
    apply Units.ext
    apply Subtype.ext
    simpa using hp
  exact Set.infinite_range_of_injective hinj hfinite

/-- The expanding multiplier exists from the paper's infinite-order-unit
hypothesis, without adding a separate non-criticality premise. -/
theorem exists_mult_margin_of_pow_ne_one (FM : FieldModel K 𝒪 Nm)
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)] (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < (p : ℝ)) (hπN : Nm π = (p : ℚ≥0)) :
    ∃ (u : 𝒪ˣ) (j : ℕ), 0 < j ∧
      4 ≤ |(FM.toModel ε π hπO hπ0).mult u j 0| ∧
      16 ≤ normC ((FM.toModel ε π hπO hπ0).mult u j) :=
  exists_mult_margin_fieldModel_of_ne_one FM ε π hπO hπ0 p hp hπN
    (lamAbs_real_ne_one FM ε hεpow)

/-- A topologically transitive member exists from the paper's unit/prime
arithmetic alone, once lattice discreteness is supplied. -/
theorem exists_topologicallyTransitive_of_pow_ne_one (FM : FieldModel K 𝒪 Nm)
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    [CompactSpace (Pt ⧸ FM.lattice)] (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p : ℕ) (hp : 1 < (p : ℝ)) (hπN : Nm π = (p : ℚ≥0)) :
    ∃ i : 𝒪ˣ × ℕ, BerendSec5.TopologicallyTransitive
      (⇑((FM.toModel ε π hπO hπ0).torusAct i)) :=
  BerendTransitive.exists_topologicallyTransitive_fieldModel FM ε π hπO hπ0 p hp hπN
    (lamAbs_real_ne_one FM ε hεpow)

end BerendUnitNoncritical
end CubicTwoStage

#print axioms CubicTwoStage.BerendUnitNoncritical.lamAbs_real_ne_one
#print axioms CubicTwoStage.BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
#print axioms CubicTwoStage.BerendUnitNoncritical.exists_topologicallyTransitive_of_pow_ne_one
