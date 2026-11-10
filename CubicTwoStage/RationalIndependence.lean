/-
# Rational independence of the unit and the prime (Berend's B3)

Berend's hypothesis (B3) is the only one of the three whose verification is a
direct norm computation: if `μ_ε^l = μ_π^k` then `ε^l = π^k`, so
`|Nm ε|^l = |Nm π|^k`.  With `|Nm ε| = 1` this gives `1 = p^k`, impossible for
nonzero `k` and `p > 1`.

The only substantive step is evaluating an integer power of `D.linFam` at
`oneC`: `Model.mulC_zpow` reduces it to computing `powC` of `σ(b)` and `σ(b⁻¹)`,
which is `σ(b^n)` or `σ((b⁻¹)^n)` by multiplicativity of the embedding.
-/
import CubicTwoStage.FieldModel

namespace CubicTwoStage

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- **Interaction of `σ` with inverses** (used in negative powers). -/
lemma linFam_eval_one (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (u : 𝒪ˣ) (j : ℕ) (l : ℤ) :
    ((FM.toModel ε π hπO hπ0).linFam (u, j) ^ l) oneC =
      FM.σ ((((u : 𝒪) : K) * π ^ j) ^ l) := by
  set D := FM.toModel ε π hπO hπ0 with hD
  have hmult : D.mult u j = FM.σ (((u : 𝒪) : K) * π ^ j) := by
    show FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j = FM.σ (((u : 𝒪) : K) * π ^ j)
    rw [← FM.σ_mul_pow, ← FM.σ_mul]
  have he : ∀ x : Pt, (D.linFam (u, j)) x = D.mult u j ⋆ x := fun _ => rfl
  have heinv : ∀ x : Pt, ((D.linFam (u, j))⁻¹) x =
      D.unit_inv u ⋆ powC D.prime_inv j ⋆ x := fun _ => rfl
  have hinv : D.mult u j ⋆ (D.unit_inv u ⋆ powC D.prime_inv j) = oneC :=
    D.mult_mul_inv u j
  have hpow := mulC_zpow (D.mult u j)
    (D.unit_inv u ⋆ powC D.prime_inv j)
    (D.linFam (u, j)) he heinv hinv l oneC
  rw [hpow, mulC_oneC]
  by_cases hl : 0 ≤ l
  · rw [if_pos hl, hmult, ← FM.σ_mul_pow]
    congr 1
    rw [← Int.natAbs_of_nonneg hl, zpow_natCast]
    norm_cast
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp hl)
    have hif : ¬ (0 ≤ (Int.negSucc n : ℤ)) := by
      have hneg : (Int.negSucc n : ℤ) = -(n + 1) := by rfl
      rw [hneg]
      omega
    rw [if_neg hif, Int.natAbs_negSucc]
    have hc' : D.unit_inv u ⋆ powC D.prime_inv j = FM.σ ((((u : 𝒪) : K) * π ^ j)⁻¹) := by
      rw [mul_inv, ← inv_pow]
      show FM.σ (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) ⋆ powC (FM.σ π⁻¹) j =
        FM.σ (((u : 𝒪) : K)⁻¹ * (π⁻¹)^j)
      rw [← FM.σ_mul_pow, ← FM.σ_mul, FieldModel.coe_units_inv]
    rw [hc', ← FM.σ_mul_pow]
    congr 1
    rw [show (Int.negSucc n : ℤ) = -(↑n + 1) from rfl, zpow_neg]
    norm_cast
    exact (inv_pow ((((u : 𝒪) : K) * π ^ j)) (n + 1))

/-- If `p > 1`, no nonzero integer power of `p` equals one. -/
lemma zpow_ne_one_of_gt_one {a : ℝ} (ha : 1 < a) {k : ℤ} (hk : k ≠ 0) :
    a ^ k ≠ 1 := by
  intro hEq
  by_cases hkpos : 0 < k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hkpos)
    have hn : n ≠ 0 := by omega
    have h1 : 1 < a ^ n := one_lt_pow₀ ha hn
    rw [zpow_natCast] at hEq
    rw [hEq] at h1
    exact lt_irrefl _ h1
  · have hlt : a ^ k < 1 := by
      have hkneg : k < 0 := lt_of_le_of_ne (not_lt.mp hkpos) hk
      obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hkneg
      rw [show (Int.negSucc n : ℤ) = -(↑n + 1) from rfl, zpow_neg, inv_eq_one_div]
      have hp : 1 < a ^ (n + 1) := one_lt_pow₀ ha (by positivity)
      have hz : 0 < a ^ (n + 1) := by positivity
      field_simp
      exact hp
    rw [hEq] at hlt
    exact lt_irrefl _ hlt

/-- **Berend's (B3), for the unit–prime semigroup**: `μ_ε` and `μ_π` are
rationally independent.  The input `Nm π = p` with `p > 1` is the degree-one
prime residue valuation; `Nm ε = 1` comes from `FieldModel.Nm_unit`. -/
theorem rational_independence (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < p)
    (hπN : Nm π = (p : ℚ≥0)) :
    ∃ i j : 𝒪ˣ × ℕ, ∀ l k : ℤ, l ≠ 0 → k ≠ 0 →
      ((FM.toModel ε π hπO hπ0).linFam i) ^ l ≠
        ((FM.toModel ε π hπO hπ0).linFam j) ^ k := by
  refine ⟨(ε, 0), (1, 1), ?_⟩
  intro l k hl hk hEq
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
  exact zpow_ne_one_of_gt_one (a := (p : ℝ)) (by exact_mod_cast hp) hk hR


end CubicTwoStage
