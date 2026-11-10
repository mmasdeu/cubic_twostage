/-
# Canonical B1 for the complex-cubic unit-prime model

Standalone consolidation of Core.lean, Bridge.lean and Public.lean (member m3).
-/
import CubicTwoStage.BerendEigenBridge
import CubicTwoStage.BerendPrimeNorm
import CubicTwoStage.ComplexCubic
import CubicTwoStage.BerendAlgebra
import CubicTwoStage.BerendCorrected

open Set Polynomial
open scoped TensorProduct

namespace CubicTwoStage
namespace BerendCanonicalB1

lemma exists_cube_root_of_cube_eq_prime_pow {m n p : ℕ} (hp : p.Prime)
    (h : m ^ 3 = p ^ n) : ∃ r : ℕ, n = 3 * r ∧ m = p ^ r := by
  have hmdvd : m ∣ p ^ n := ⟨m ^ 2, by rw [← h]; ring⟩
  obtain ⟨r, hr, hm⟩ := (Nat.dvd_prime_pow hp).mp hmdvd
  subst m
  refine ⟨r, ?_, rfl⟩
  apply Nat.pow_right_injective hp.two_le
  calc
    p ^ n = (p ^ r) ^ 3 := h.symm
    _ = p ^ (3 * r) := by rw [← pow_mul]; congr 1; omega

lemma eq_one_or_neg_one_of_real_embedding_pow {K : Type*} [Field K]
    (φ : K →+* ℝ) {x : K} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    x = 1 ∨ x = -1 := by
  have hx' : (φ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  have habs : |φ x| = 1 := (abs_pow_eq_one (φ x) hn).mp (by rw [hx', abs_one])
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · exact Or.inl (φ.injective (by simpa using h))
  · exact Or.inr (φ.injective (by simpa using h))

lemma cube_eq_pm_of_pow_eq_int {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) {α : K} (hα : IsIntegral ℤ α)
    {p : ℕ} (hp : p.Prime) (hαN : numberFieldAbsNorm K α = (p : ℚ≥0))
    {n : ℕ} (hn : 0 < n) {z : ℤ} (hz : α ^ n = (z : K)) :
    α ^ 3 = (p : K) ∨ α ^ 3 = -(p : K) := by
  have hnorm := congrArg (fun x : K => numberFieldAbsNorm K x) hz
  rw [map_pow, hαN] at hnorm
  have hnormz : numberFieldAbsNorm K (z : K) = (z.natAbs ^ 3 : ℕ) := by
    apply NNRat.coe_inj.mp
    change |Algebra.norm ℚ (z : K)| = ((z.natAbs ^ 3 : ℕ) : ℚ)
    rw [show (z : K) = (((z : ℚ) : K)) by norm_cast]
    change |Algebra.norm ℚ (algebraMap ℚ K (z : ℚ))| = ((z.natAbs ^ 3 : ℕ) : ℚ)
    rw [Algebra.norm_algebraMap, hK.1]
    simp only [Int.cast_natCast, abs_pow, Nat.cast_pow, Nat.cast_natAbs]
    norm_cast
  have hnorm' : (p : ℚ) ^ n = ((z.natAbs ^ 3 : ℕ) : ℚ) := by
    have h := congrArg (fun x : ℚ≥0 => (x : ℚ)) hnorm
    rw [hnormz] at h
    simpa using h
  have hnat : z.natAbs ^ 3 = p ^ n := by exact_mod_cast hnorm'.symm
  obtain ⟨r, hn_eq, hz_abs⟩ := exists_cube_root_of_cube_eq_prime_pow hp hnat
  have hzsign : z = (p ^ r : ℕ) ∨ z = -(p ^ r : ℕ) := by
    have habs : z.natAbs = (p ^ r : ℕ) := hz_abs
    exact Int.natAbs_eq_iff.mp habs
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let β : K := α ^ 3 / (p : K)
  have hβ : β ^ (2 * r) = 1 := by
    have hr : 0 < r := by
      by_contra hr0
      have hrz : r = 0 := Nat.eq_zero_of_not_pos hr0
      subst r
      simp at hn_eq
      omega
    have hpow : (α ^ n) = ((z : ℤ) : K) := hz
    rw [hn_eq, pow_mul] at hpow
    have hαcube : ((α ^ 3) / (p : K)) ^ r = (z : K) / (p : K) ^ r := by
      rw [div_pow]
      exact congrArg (fun x : K => x / (p : K) ^ r) hpow
    have hβr : β ^ r = 1 ∨ β ^ r = -1 := by
      change ((α ^ 3) / (p : K)) ^ r = 1 ∨ ((α ^ 3) / (p : K)) ^ r = -1
      rw [hαcube]
      rcases hzsign with hz' | hz' <;> rw [hz']
      · left
        push_cast
        exact div_self (pow_ne_zero r hp0)
      · right
        push_cast
        rw [neg_div, div_self (pow_ne_zero r hp0)]
    rcases hβr with h | h <;> rw [mul_comm 2 r, pow_mul, h] <;> norm_num

  have hβsign : β = 1 ∨ β = -1 :=
    eq_one_or_neg_one_of_real_embedding_pow (NumberFieldCubic.realEmbedding K hK)
      (by omega) hβ
  rcases hβsign with h | h
  · left
    apply (div_eq_one_iff_eq hp0).mp
    exact h
  · right
    have hh : α ^ 3 / (p : K) = -1 := h
    have heq := (div_eq_iff hp0).mp hh
    simpa using heq

end BerendCanonicalB1
end CubicTwoStage

namespace CubicTwoStage
namespace BerendCanonicalB1

lemma cube_eq_pm_of_pow_eq_rat {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) {α : K} (hα : IsIntegral ℤ α)
    {p : ℕ} (hp : p.Prime) (hαN : numberFieldAbsNorm K α = (p : ℚ≥0))
    {n : ℕ} (hn : 0 < n) {q : ℚ} (hq : α ^ n = (q : K)) :
    α ^ 3 = (p : K) ∨ α ^ 3 = -(p : K) := by
  have hqK : IsIntegral ℤ (q : K) := by
    rw [← hq]
    exact hα.pow n
  have hqQ : IsIntegral ℤ q := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := K)
      (algebraMap ℚ K).injective).mp
    change IsIntegral ℤ (q : K)
    exact hqK
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqQ
  apply cube_eq_pm_of_pow_eq_int hK hα hp hαN hn (z := z)
  rw [hq, ← hz]
  norm_cast

lemma unit_pow_six_eq_one_of_cube_sq {K : Type*} [Field K] {e π p : K}
    (hp0 : p ≠ 0) (hπ : (π ^ 3) ^ 2 = p ^ 2) (heπ : ((e * π) ^ 3) ^ 2 = p ^ 2) :
    e ^ 6 = 1 := by
  have hpowπ : π ^ 6 = p ^ 2 := by
    calc
      π ^ 6 = (π ^ 3) ^ 2 := by ring
      _ = p ^ 2 := hπ
  have hpoweπ : e ^ 6 * π ^ 6 = p ^ 2 := by
    calc
      e ^ 6 * π ^ 6 = (e * π) ^ 6 := (mul_pow e π 6).symm
      _ = ((e * π) ^ 3) ^ 2 := by ring
      _ = p ^ 2 := heπ
  rw [hpowπ] at hpoweπ
  apply mul_right_cancel₀ (pow_ne_zero 2 hp0)
  simpa using hpoweπ

lemma exists_prime_or_unit_prime_no_rat_pow {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) {π : K}
    (hπO : π ∈ numberFieldO K) {p : ℕ} (hp : p.Prime)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1) :
    (∀ (n : ℕ), 0 < n → ∀ q : ℚ, π ^ n ≠ (q : K)) ∨
      (∀ (n : ℕ), 0 < n → ∀ q : ℚ,
        ((((ε : numberFieldO K) : K)) * π) ^ n ≠ (q : K)) := by
  let e : K := ((ε : numberFieldO K) : K)
  have heint : IsIntegral ℤ e := (ε : numberFieldO K).2
  have heπint : IsIntegral ℤ (e * π) := heint.mul hπO
  have heπN : numberFieldAbsNorm K (e * π) = (p : ℚ≥0) := by
    rw [map_mul, (NumberFieldCubic.canonicalFieldModel K hK).Nm_unit ε, hπN, one_mul]
  by_cases hπgood : ∀ (n : ℕ), 0 < n → ∀ q : ℚ, π ^ n ≠ (q : K)
  · exact Or.inl hπgood
  · right
    push_neg at hπgood
    obtain ⟨n, hn, q, hq⟩ := hπgood
    have hπcube := cube_eq_pm_of_pow_eq_rat hK hπO hp hπN hn hq
    intro m hm r hr
    have heπcube := cube_eq_pm_of_pow_eq_rat hK heπint hp heπN hm hr
    have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hπsq : (π ^ 3) ^ 2 = (p : K) ^ 2 := by
      rcases hπcube with h | h <;> rw [h] <;> ring
    have heπsq : ((e * π) ^ 3) ^ 2 = (p : K) ^ 2 := by
      rcases heπcube with h | h <;> rw [h] <;> ring
    exact hεpow 6 (by norm_num) (unit_pow_six_eq_one_of_cube_sq hp0 hπsq heπsq)

end BerendCanonicalB1
end CubicTwoStage

open Set Polynomial
open scoped TensorProduct

namespace CubicTwoStage
namespace BerendCanonicalB1

lemma map_pow_mem_intAct {M : Submodule ℤ Pt} (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (n : ℕ) : ∀ x ∈ M, (f ^ n) x ∈ M := by
  induction n with
  | zero => simp
  | succ n ih =>
      intro x hx
      rw [pow_succ]
      exact ih _ (hf _ hx)

lemma intAct_apply {M : Submodule ℤ Pt} (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (x : M) :
    intAct M f hf x = ⟨f (x : Pt), hf _ x.2⟩ := rfl

lemma intAct_pow {M : Submodule ℤ Pt} (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (n : ℕ) :
    (intAct M f hf) ^ n = intAct M (f ^ n) (map_pow_mem_intAct f hf n) := by
  induction n with
  | zero =>
      ext x
      simp [intAct]
  | succ n ih =>
      rw [pow_succ, ih]
      ext x i
      change (f ^ n) (f (x : Pt)) i = (f ^ (n + 1)) (x : Pt) i
      rw [pow_succ]
      rfl

lemma charpoly_intAct_map_real {M : Submodule ℤ Pt}
    [DiscreteTopology M] [IsZLattice ℝ M]
    (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    (LinearMap.charpoly (intAct M f hf)).map (Int.castRingHom ℝ) =
      LinearMap.charpoly f := by
  let b : Module.Basis (Fin 3) ℤ M := IsZLattice.basis M
  have hmat : ((LinearMap.toMatrix b b (intAct M f hf)).map (Int.castRingHom ℝ)) =
      LinearMap.toMatrix (b.ofZLatticeBasis ℝ) (b.ofZLatticeBasis ℝ) f := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      intAct_apply, Module.Basis.ofZLatticeBasis_apply]
    conv_rhs =>
      rw [show f ↑(b j) = ↑(⟨f ↑(b j), hf _ (b j).2⟩ : M) from rfl]
    rw [Module.Basis.ofZLatticeBasis_repr_apply]
    rfl
  calc
    (LinearMap.charpoly (intAct M f hf)).map (Int.castRingHom ℝ) =
        ((LinearMap.toMatrix b b (intAct M f hf)).map (Int.castRingHom ℝ)).charpoly := by
      rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    _ = (LinearMap.toMatrix (b.ofZLatticeBasis ℝ) (b.ofZLatticeBasis ℝ) f).charpoly := by
      rw [hmat]
    _ = LinearMap.charpoly f := LinearMap.charpoly_toMatrix _ _

lemma lamVec_canonical_zero {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (x : K) :
    lamVec ((NumberFieldCubic.canonicalFieldModel K hK).σ x) 0 =
      (NumberFieldCubic.realEmbedding K hK x : ℂ) := by
  rfl

lemma lamVec_canonical_one {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (x : K) :
    lamVec ((NumberFieldCubic.canonicalFieldModel K hK).σ x) 1 =
      NumberFieldCubic.complexEmbedding K hK x := by
  apply Complex.ext <;> rfl

lemma lamVec_canonical_two {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (x : K) :
    lamVec ((NumberFieldCubic.canonicalFieldModel K hK).σ x) 2 =
      (starRingEnd ℂ) (NumberFieldCubic.complexEmbedding K hK x) := by
  apply Complex.ext <;> simp [lamVec, NumberFieldCubic.canonicalFieldModel,
    NumberFieldCubic.σ]

end BerendCanonicalB1
end CubicTwoStage

namespace CubicTwoStage
namespace BerendCanonicalB1

lemma charpoly_intAct_pow_map_complex {M : Submodule ℤ Pt}
    [DiscreteTopology M] [IsZLattice ℝ M]
    (a : Pt) (ha : ∀ x ∈ M, ptMul a x ∈ M) (n : ℕ) :
    (((intAct M (ptMul a) ha) ^ n).charpoly.map (Int.castRingHom ℂ)) =
      (ptMulC (powC a n)).charpoly := by
  have hreal : (((intAct M (ptMul a) ha) ^ n).charpoly.map (Int.castRingHom ℝ)) =
      ((ptMul a) ^ n).charpoly := by
    rw [intAct_pow, charpoly_intAct_map_real]
  calc
    (((intAct M (ptMul a) ha) ^ n).charpoly.map (Int.castRingHom ℂ)) =
        ((((intAct M (ptMul a) ha) ^ n).charpoly.map (Int.castRingHom ℝ)).map
          (algebraMap ℝ ℂ)) := by
      rw [Polynomial.map_map]
      congr 1
    _ = (((ptMul a) ^ n).charpoly.map (algebraMap ℝ ℂ)) := by rw [hreal]
    _ = (LinearMap.baseChange ℂ ((ptMul a) ^ n)).charpoly :=
      (LinearMap.charpoly_baseChange ((ptMul a) ^ n) ℂ).symm
    _ = (cEquiv.conj (LinearMap.baseChange ℂ ((ptMul a) ^ n))).charpoly :=
      (LinearEquiv.charpoly_conj cEquiv _).symm
    _ = (cEquiv.conj (LinearMap.baseChange ℂ (ptMul (powC a n)))).charpoly := by
      rw [ptMul_pow]
    _ = (ptMulC (powC a n)).charpoly := by rw [conj_baseChange_ptMul]

lemma no_rat_root_intAct_pow_of_lamVec {M : Submodule ℤ Pt}
    [DiscreteTopology M] [IsZLattice ℝ M]
    (a : Pt) (ha : ∀ x ∈ M, ptMul a x ∈ M) (n : ℕ)
    (h : ∀ q : ℚ, ∀ k : Fin 3, (q : ℂ) ≠ lamVec (powC a n) k)
    (q : ℚ) : ¬ ((((intAct M (ptMul a) ha) ^ n).charpoly.map
      (Int.castRingHom ℚ)).IsRoot q) := by
  intro hq
  have hc : ((((intAct M (ptMul a) ha) ^ n).charpoly.map
      (Int.castRingHom ℂ)).IsRoot (q : ℂ)) := by
    have heq : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
      ext z
      simp
    rw [← heq, ← Polynomial.map_map]
    exact Polynomial.IsRoot.map (f := algebraMap ℚ ℂ) hq
  rw [charpoly_intAct_pow_map_complex, ptMulC_charpoly, Polynomial.IsRoot,
    Polynomial.eval_prod] at hc
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hc
  apply h q k
  exact sub_eq_zero.mp (by simpa using hk)

lemma irreducible_intAct_pow_of_lamVec {M : Submodule ℤ Pt}
    [DiscreteTopology M] [IsZLattice ℝ M]
    (a : Pt) (ha : ∀ x ∈ M, ptMul a x ∈ M) (n : ℕ)
    (h : ∀ q : ℚ, ∀ k : Fin 3, (q : ℂ) ≠ lamVec (powC a n) k) :
    Irreducible (((intAct M (ptMul a) ha) ^ n).charpoly) := by
  have hQ : Irreducible ((((intAct M (ptMul a) ha) ^ n).charpoly).map
      (Int.castRingHom ℚ)) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective),
        LinearMap.charpoly_natDegree, ZLattice.rank ℝ M]
      simp
    · exact no_rat_root_intAct_pow_of_lamVec a ha n h
  exact (irreducible_map_rat_iff (LinearMap.charpoly_monic _)).mp hQ

end BerendCanonicalB1
end CubicTwoStage

namespace CubicTwoStage
namespace BerendCanonicalB1

lemma no_rat_lamVec_canonical {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (u : (numberFieldO K)ˣ) (j n : ℕ)
    (hpow : ∀ q : ℚ, ((((u : numberFieldO K) : K) * π ^ j) ^ n) ≠ (q : K))
    (q : ℚ) (k : Fin 3) :
    (q : ℂ) ≠ lamVec (powC
      (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).mult u j) n) k := by
  let FM := NumberFieldCubic.canonicalFieldModel K hK
  let D := FM.toModel ε π hπO hπ0
  have hmult : D.mult u j = FM.σ (((u : numberFieldO K) : K) * π ^ j) := by
    change FM.σ (((u : numberFieldO K) : K)) ⋆ powC (FM.σ π) j = _
    rw [← FM.σ_mul_pow, ← FM.σ_mul]
  have hpowmult : powC (D.mult u j) n =
      FM.σ ((((u : numberFieldO K) : K) * π ^ j) ^ n) := by
    rw [hmult, ← FM.σ_mul_pow]
  intro hk
  change (q : ℂ) = lamVec (powC (D.mult u j) n) k at hk
  rw [hpowmult] at hk
  fin_cases k <;> dsimp [FM] at hk
  · apply hpow q
    apply (NumberFieldCubic.realEmbedding K hK).injective
    have hh := congrArg Complex.re hk
    simpa [FM, NumberFieldCubic.canonicalFieldModel, NumberFieldCubic.σ] using hh.symm
  · apply hpow q
    apply (NumberFieldCubic.complexEmbedding K hK).injective
    simpa [FM, NumberFieldCubic.canonicalFieldModel, NumberFieldCubic.σ] using hk.symm
  · apply hpow q
    apply (NumberFieldCubic.complexEmbedding K hK).injective
    apply Complex.ext
    · have hh := congrArg (fun z : ℂ => ((starRingEnd ℂ) z).re) hk
      simpa [FM, NumberFieldCubic.canonicalFieldModel, NumberFieldCubic.σ] using hh.symm
    · have hh := congrArg (fun z : ℂ => ((starRingEnd ℂ) z).im) hk
      simpa [FM, NumberFieldCubic.canonicalFieldModel, NumberFieldCubic.σ] using hh.symm

lemma irreducible_canonical_intLact_of_no_rat_pow {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (u : (numberFieldO K)ˣ) (j n : ℕ)
    (hpow : ∀ q : ℚ, ((((u : numberFieldO K) : K) * π ^ j) ^ n) ≠ (q : K)) :
    Irreducible (LinearMap.charpoly
      (((((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).intLact
        (u, j)) ^ n))) := by
  let FM := NumberFieldCubic.canonicalFieldModel K hK
  let D := FM.toModel ε π hπO hπ0
  change Irreducible (((intAct (AddSubgroup.toIntSubmodule FM.lattice)
    (ptMul (D.mult u j)) (fun x hx => D.lattice_linFam (u, j) hx)) ^ n).charpoly)
  apply irreducible_intAct_pow_of_lamVec
    (a := D.mult u j) (ha := fun x hx => D.lattice_linFam (u, j) hx) n
  exact no_rat_lamVec_canonical hK ε π hπO hπ0 u j n hpow

lemma exists_canonical_B1_intLact {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0) {p : ℕ} (hp : p.Prime)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1) :
    ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).intLact i ^ n)) := by
  rcases exists_prime_or_unit_prime_no_rat_pow hK ε hπO hp hπN hεpow with h | h
  · refine ⟨(1, 1), ?_⟩
    intro n hn
    apply irreducible_canonical_intLact_of_no_rat_pow hK ε π hπO hπ0 1 1 n
    intro q
    simpa using h n hn q
  · refine ⟨(ε, 1), ?_⟩
    intro n hn
    apply irreducible_canonical_intLact_of_no_rat_pow hK ε π hπO hπ0 ε 1 n
    intro q
    simpa using h n hn q

end BerendCanonicalB1
end CubicTwoStage

open Set Polynomial
open scoped TensorProduct

namespace CubicTwoStage
namespace BerendCanonicalB1

/-- The canonical complex-cubic unit--prime model has a B1 member.
The witness is either `(1, 1)` (multiplication by `π`) or `(ε, 1)`
(multiplication by `επ`). -/
theorem exists_canonical_B1 {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0) {p : ℕ} (hp : p.Prime)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1) :
    ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).lact i ^ n)) := by
  simpa only [UnitPrimeModel.lact, UnitPrimeModel.intLact, latticeAct, intAct] using
    (exists_canonical_B1_intLact hK ε π hπO hπ0 hp hπN hεpow)

/-- The same canonical B1 theorem in the corrected Stage-I spelling. -/
theorem exists_canonical_B1_lactZ {K : Type*} [Field K] [NumberField K]
    (hK : IsComplexCubic K) (ε : (numberFieldO K)ˣ) (π : K)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0) {p : ℕ} (hp : p.Prime)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1) :
    ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).lactZ i ^ n)) := by
  simpa only [UnitPrimeModel.lactZ, UnitPrimeModel.intLact, latticeActZ, intAct] using
    (exists_canonical_B1_intLact hK ε π hπO hπ0 hp hπN hεpow)

end BerendCanonicalB1
end CubicTwoStage

#print axioms CubicTwoStage.BerendCanonicalB1.exists_prime_or_unit_prime_no_rat_pow
#print axioms CubicTwoStage.BerendCanonicalB1.irreducible_intAct_pow_of_lamVec
#print axioms CubicTwoStage.BerendCanonicalB1.exists_canonical_B1_intLact
#print axioms CubicTwoStage.BerendCanonicalB1.exists_canonical_B1
#print axioms CubicTwoStage.BerendCanonicalB1.exists_canonical_B1_lactZ
