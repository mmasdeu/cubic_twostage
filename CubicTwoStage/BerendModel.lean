/-
# Checks on the *corrected* (B3) of `BEREND_PROOF_PLAN.md`

`CubicTwoStage/Berend.lean` states Berend's multi-invariance theorem with a
hypothesis (B3) that two of the maps are "rationally independent", literally

```lean
B3 : ∃ i j, ∀ l k : ℤ, l ≠ 0 → k ≠ 0 → (f i) ^ l ≠ (f j) ^ k .
```

`BEREND_PROOF_PLAN.md` replaces it by the corrected

```lean
B3 : ∃ i j : ι, ∀ l k : ℤ, (f i) ^ l = (f j) ^ k → l = 0 ∧ k = 0 .
```

This module checks, in Lean and with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` (see the `#print axioms` block at the end),
the two things a corrected hypothesis needs before a proof can be built on it.

## 1. The correction is necessary (not cosmetic)

With `A = !![0,0,30; 1,0,-39; 0,1,12]` (charpoly `X³ - 12X² + 39X - 30`):

* `old_B3_neg_one` : the **old** (B3) holds for the family `A, -id`;
* `not_corrected_B3_neg_one` : the **corrected** (B3) fails for it, at
  `l = 0, k = 2` (`A ^ 0 = 1 = (-1) ^ 2`).

So the correction removes exactly the witness of the counterexample in
`.ultramath/smw68xy68/m5/refutation.md`, and `corrected_B3_fails_of_torsion`
records the general reason: a generator of finite order kills the corrected
condition, and does not kill the old one.

## 2. The corrected hypothesis is consistent with (B1) and (B2)

With the same `A` and the second map `7 • id` (`fA`, `fB : Pt ≃ₗ[ℝ] Pt`):

* `model_B1` : for every `n ≥ 1` the characteristic polynomial of the `n`-th power
  of the **integral restriction** `latticeActZ L3 fA` to the standard lattice
  `L3 = ℤ³ ⊂ Pt` is irreducible — (B1) in the lattice form of the axiom
  (`model_B1` is derived from the matrix statement `charpoly_pow_irreducible`
  through the transport lemma `charpoly_latticeActZ_map`, which identifies the
  characteristic polynomial of an integral restriction with the real one using
  any `ℤ`-basis of the lattice; no coordinates are needed);
* `model_B2` : every common eigenvector of the family in `ℂ ⊗[ℝ] Pt` has an
  eigenvalue of modulus `> 1` — (B2) as stated for the axiom;
* `model_B3` : `A ^ l = (7 • id) ^ k` forces `l = k = 0` — the corrected (B3);
* `model_comm` : the two maps commute.

`model_hypotheses` bundles all four.  The lattice `L3 = ℤ³` also carries the
Mathlib instances needed by the axiom (`instDiscL3 : DiscreteTopology` from
`ZSpan`, `instZLLattice3 : IsZLattice ℝ`).

The proof of `model_B3` is determinant-based: `det A = 30`, `det (7 • id) = 343`,
`det` is a monoid hom on `Pt ≃ₗ[ℝ] Pt` (`LinearEquiv.det`) and commutes with
integer powers (`map_zpow`), so `A ^ l = (7 • id) ^ k` forces
`30 ^ l = 343 ^ k` in `ℝ`, hence in `ℚ`, where `v₇` (Mathlib's `padicValRat`)
gives `l = k = 0`.  The same machinery gives `corrected_B3_implies_old_B3`:
the corrected condition is strictly stronger than the old one.

## Deficits (what this module does *not* do)

* `latticeActZ` is a restatement of `CubicTwoStage.latticeAct` with the same
  definition (`LinearMap.restrict ∘ restrictScalars`).  This module does not
  import `CubicTwoStage.Berend` (which declares the old axiom), so the
  definitional identity `latticeActZ = latticeAct` is not stated here; it is
  `rfl` in any module that imports both (m3's `BerendBridge` does this).
* Nothing here proves the conclusion of Berend's theorem for any invariant set;
  this module only validates the hypothesis side (and certifies that the
  hypotheses are not vacuous).

The matrix/polynomial part (B1) and (B2) is adapted, with the same statements,
from the checked fragment `.ultramath/smw68xy68/m5/lean/Refute.lean` (copied
into this project-owned module, not imported).
-/
import CubicTwoStage.Basic

set_option linter.unusedSimpArgs false

open Polynomial Matrix
open scoped TensorProduct

namespace CubicTwoStage
namespace BerendModel

/-! ## The polynomial -/

/-- `p` as an integer polynomial. -/
noncomputable def P : ℤ[X] := X^3 - 12*X^2 + 39*X - 30

/-- `p` over `ℚ`. -/
noncomputable def pQ : ℚ[X] := X^3 - 12*X^2 + 39*X - 30

/-- `p` over `ℝ`. -/
noncomputable def pR : ℝ[X] := pQ.map (algebraMap ℚ ℝ)

lemma pQ_eq_map : pQ = P.map (Int.castRingHom ℚ) := by
  simp [pQ, P]

lemma pR_eq : pR = X^3 - 12*X^2 + 39*X - 30 := by
  simp [pR, pQ]

lemma pR_natDegree : pR.natDegree = 3 := by
  rw [pR_eq]; compute_degree!

lemma pQ_natDegree : pQ.natDegree = 3 := by
  rw [pQ]; compute_degree!

lemma P_monic : P.Monic := by
  have h : P = X^3 + (-12*X^2 + 39*X - 30 : ℤ[X]) := by rw [P]; ring
  rw [h]
  exact monic_X_pow_add (by compute_degree!)

/-! ### `p` has no rational root -/

lemma P_eval_ne_zero_of_nonpos {k : ℤ} (hk : k ≤ 0) : P.eval k ≠ 0 := by
  simp only [P, eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
  intro h
  nlinarith [sq_nonneg k, sq_nonneg (k-6), sq_nonneg (k+1)]

lemma P_eval_ne_zero_of_ge {k : ℤ} (hk : 11 ≤ k) : P.eval k ≠ 0 := by
  simp only [P, eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
  intro h
  nlinarith [sq_nonneg k, sq_nonneg (k-6), sq_nonneg (k-11)]

lemma P_eval_ne_zero_mid {k : ℤ} (hk : k ∈ Finset.Icc 1 10) : P.eval k ≠ 0 := by
  rw [Finset.mem_Icc] at hk
  obtain ⟨h1, h2⟩ := hk
  interval_cases k <;> (simp only [P]; norm_num)

lemma P_no_int_root : ∀ k : ℤ, P.eval k ≠ 0 := by
  intro k
  by_cases h1 : k ≤ 0
  · exact P_eval_ne_zero_of_nonpos h1
  · by_cases h2 : 11 ≤ k
    · exact P_eval_ne_zero_of_ge h2
    · rw [not_le] at h2
      exact P_eval_ne_zero_mid (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

lemma pQ_eval_eq_aeval (x : ℚ) : pQ.eval x = aeval x P := by
  rw [pQ_eq_map, Polynomial.eval_map, Polynomial.aeval_def]
  rfl

lemma pQ_no_ratRoot : ∀ x : ℚ, ¬ pQ.IsRoot x := by
  intro x hx
  rw [Polynomial.IsRoot] at hx
  have hx' : aeval x P = 0 := by rw [← pQ_eval_eq_aeval]; exact hx
  obtain ⟨k, hk⟩ := isInteger_of_is_root_of_monic P_monic (A := ℤ) (K := ℚ) hx'
  rw [← hk] at hx'
  have h2 : ((P.eval k : ℤ) : ℚ) = 0 := by
    rw [Polynomial.aeval_def] at hx'
    simpa using hx'
  exact P_no_int_root k (by exact_mod_cast h2)

lemma pQ_irreducible : Irreducible pQ := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [pQ_natDegree]; decide
  · exact pQ_no_ratRoot

/-! ### Two explicit real roots of `p` -/

lemma exists_root_12 : ∃ z ∈ Set.Ioo (1:ℝ) 2, pR.eval z = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => pR.eval x) (Set.Icc (1:ℝ) 2) :=
    pR.continuous.continuousOn
  have h1 : pR.eval 1 < 0 := by rw [pR_eq]; norm_num
  have h2 : (0:ℝ) < pR.eval 2 := by rw [pR_eq]; norm_num
  have hmem : (0:ℝ) ∈ Set.Ioo (pR.eval 1) (pR.eval 2) := ⟨h1, h2⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo (f := fun x : ℝ => pR.eval x)
    (show (1:ℝ) ≤ 2 by norm_num) hcont hmem
  exact ⟨z, hz, hz0⟩

lemma exists_root_35 : ∃ z ∈ Set.Ioo (3:ℝ) 5, pR.eval z = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => pR.eval x) (Set.Icc (3:ℝ) 5) :=
    pR.continuous.continuousOn
  have h1 : (0:ℝ) < pR.eval 3 := by rw [pR_eq]; norm_num
  have h2 : pR.eval 5 < 0 := by rw [pR_eq]; norm_num
  have hmem : (0:ℝ) ∈ Set.Ioo (pR.eval 5) (pR.eval 3) := ⟨h2, h1⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' (f := fun x : ℝ => pR.eval x)
    (show (3:ℝ) ≤ 5 by norm_num) hcont hmem
  exact ⟨z, hz, hz0⟩

lemma exists_root_610 : ∃ z ∈ Set.Ioo (6:ℝ) 10, pR.eval z = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => pR.eval x) (Set.Icc (6:ℝ) 10) :=
    pR.continuous.continuousOn
  have h1 : pR.eval 6 < 0 := by rw [pR_eq]; norm_num
  have h2 : (0:ℝ) < pR.eval 10 := by rw [pR_eq]; norm_num
  have hmem : (0:ℝ) ∈ Set.Ioo (pR.eval 6) (pR.eval 10) := ⟨h1, h2⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo (f := fun x : ℝ => pR.eval x)
    (show (6:ℝ) ≤ 10 by norm_num) hcont hmem
  exact ⟨z, hz, hz0⟩


/-- **(B2) content**: every complex root of `p` exceeds `1` in modulus.  `p` has degree 3 and
three distinct real roots `z₁ ∈ (1,2)`, `z₂ ∈ (3,5)`, `z₃ ∈ (6,10)`, so its root set is exactly
`{z₁,z₂,z₃}` and each has modulus `> 1`. -/
lemma root_norm_gt_one (μ : ℂ) (hμ : (pR.map (algebraMap ℝ ℂ)).eval μ = 0) : 1 < ‖μ‖ := by
  have hp0 : pR.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval (0:ℂ)) h
    simp [pR_eq] at this
  obtain ⟨z1, hz1, hz1'⟩ := exists_root_12
  obtain ⟨z2, hz2, hz2'⟩ := exists_root_35
  obtain ⟨z3, hz3, hz3'⟩ := exists_root_610
  have h12 : z1 < z2 := by linarith [hz1.2, hz2.1]
  have h23 : z2 < z3 := by linarith [hz2.2, hz3.1]
  have hmem : ∀ z : ℝ, pR.eval z = 0 → (z:ℂ) ∈ (pR.map (algebraMap ℝ ℂ)).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot]
    rw [Polynomial.eval_map]
    have hzeq : ((z:ℂ)) = algebraMap ℝ ℂ z := rfl
    rw [hzeq, Polynomial.eval₂_at_apply, hz]
    simp
  have hcard : (pR.map (algebraMap ℝ ℂ)).roots.toFinset.card ≤ 3 := by
    have h1 : (pR.map (algebraMap ℝ ℂ)).roots.toFinset.card ≤ (pR.map (algebraMap ℝ ℂ)).roots.card :=
      Multiset.toFinset_card_le _
    have h2 : (pR.map (algebraMap ℝ ℂ)).roots.card ≤ (pR.map (algebraMap ℝ ℂ)).natDegree :=
      Polynomial.card_roots' (pR.map (algebraMap ℝ ℂ))
    have h3 : (pR.map (algebraMap ℝ ℂ)).natDegree ≤ pR.natDegree := Polynomial.natDegree_map_le
    have h4 : pR.natDegree = 3 := pR_natDegree
    omega
  have hsub : ({((z1:ℂ)), (z2:ℂ), (z3:ℂ)} : Finset ℂ) ⊆ (pR.map (algebraMap ℝ ℂ)).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem z1 hz1'
    · exact hmem z2 hz2'
    · exact hmem z3 hz3'
  have hcard3 : ({((z1:ℂ)), (z2:ℂ), (z3:ℂ)} : Finset ℂ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [Complex.ofReal_inj, ne_comm.mpr (ne_of_gt h23)]
    · simp [Complex.ofReal_inj]
      exact ⟨ne_of_lt h12, ne_of_lt (by linarith)⟩
  have heq : ({((z1:ℂ)), (z2:ℂ), (z3:ℂ)} : Finset ℂ) = (pR.map (algebraMap ℝ ℂ)).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    omega
  have hmemμ : μ ∈ (pR.map (algebraMap ℝ ℂ)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot]
    exact hμ
  rw [← heq] at hmemμ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmemμ
  rcases hmemμ with rfl | rfl | rfl
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hz1.1])]; linarith [hz1.1]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hz2.1])]; linarith [hz2.1]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hz3.1])]; linarith [hz3.1]

/-! ## The matrix -/


/-- The companion matrix of `p`. -/
def A : Matrix (Fin 3) (Fin 3) ℤ := !![0,0,30; 1,0,-39; 0,1,12]

/-- `A` over `ℚ`. -/
def Aq : Matrix (Fin 3) (Fin 3) ℚ := A.map (Int.castRingHom ℚ)

lemma charpoly_A : A.charpoly = P := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [Matrix.charmatrix, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val, Fin.isValue]
  simp [A, P]
  ring

lemma Aq_charpoly : Aq.charpoly = pQ := by
  rw [Aq, pQ_eq_map, Matrix.charpoly_map, charpoly_A]

lemma aeval_Aq : aeval Aq pQ = 0 := by
  rw [← Aq_charpoly]
  exact Matrix.aeval_self_charpoly Aq

/-- `pQ` does not divide `X^n - s` for `s` rational and `n ≥ 1`. -/
lemma not_dvd (n : ℕ) (hn : 1 ≤ n) (s : ℚ) : ¬ pQ ∣ (X^n - C s) := by
  rintro ⟨g, hg⟩
  obtain ⟨z1, hz1, hz1'⟩ := exists_root_12
  obtain ⟨z2, hz2, hz2'⟩ := exists_root_610
  have key : ∀ z : ℝ, pR.eval z = 0 → z^n = (s:ℝ) := by
    intro z hz
    have hmap : ((X^n - C s : ℚ[X]).map (algebraMap ℚ ℝ)).eval z = 0 := by
      rw [hg, Polynomial.map_mul, Polynomial.eval_mul, show Polynomial.map (algebraMap ℚ ℝ) pQ = pR from rfl, hz, zero_mul]
    simp at hmap
    exact sub_eq_zero.mp hmap
  have hlt : z1 < z2 := by linarith [hz1.2, hz2.1]
  have hpos : (0:ℝ) < z1 := by linarith [hz1.1]
  have heq : z1^n = z2^n := by rw [key z1 hz1', key z2 hz2']
  have hlt' : z1^n < z2^n := pow_lt_pow_left₀ hlt (le_of_lt hpos) (by omega)
  linarith


/-- **The engine.** For `n ≥ 1` and `s : ℚ`, the matrix `s • 1 - Aq^n` is invertible:
`pQ` is irreducible and does not divide `X^n - C s`, so the two are coprime, Bézout
gives `1 = pQ * a + (X^n - C s) * b`, and evaluating at `Aq` (which satisfies `pQ` by
Cayley–Hamilton) exhibits `Aq^n - s • 1` as a unit. -/
lemma not_singular (n : ℕ) (hn : 1 ≤ n) (s : ℚ) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℚ) - Aq^n).det ≠ 0 := by
  set f : ℚ[X] := X^n - C s with hfdef
  have hnotdvd : ¬ pQ ∣ f := not_dvd n hn s
  have hcop : IsCoprime pQ f := (pQ_irreducible.coprime_iff_not_dvd).mpr hnotdvd
  obtain ⟨a, b, hab⟩ := hcop
  have hfeval : aeval Aq f = Aq^n - algebraMap ℚ (Matrix (Fin 3) (Fin 3) ℚ) s := by
    simp [hfdef]
  have hmat : aeval Aq b * (Aq^n - algebraMap ℚ (Matrix (Fin 3) (Fin 3) ℚ) s) = 1 := by
    have h := congrArg (Polynomial.aeval Aq) hab
    simpa [aeval_Aq, hfeval] using h
  have hdetprod : (aeval Aq b).det *
      (Aq^n - algebraMap ℚ (Matrix (Fin 3) (Fin 3) ℚ) s).det = 1 := by
    rw [← Matrix.det_mul, hmat, Matrix.det_one]
  have hdet : (Aq^n - algebraMap ℚ (Matrix (Fin 3) (Fin 3) ℚ) s).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetprod
    exact zero_ne_one hdetprod
  have hneg : (s • (1 : Matrix (Fin 3) (Fin 3) ℚ) - Aq^n) =
      -(Aq^n - algebraMap ℚ (Matrix (Fin 3) (Fin 3) ℚ) s) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hneg, Matrix.det_neg, Fintype.card_fin]
  have h3 : (-1 : ℚ)^3 = -1 := by norm_num
  rw [h3, neg_one_mul]
  exact neg_ne_zero.mpr hdet

/-- `charpoly (Aq^n)` has no rational root. -/
lemma no_rat_root (n : ℕ) (hn : 1 ≤ n) (s : ℚ) : (Aq^n).charpoly.eval s ≠ 0 := by
  rw [Matrix.eval_charpoly]
  have hscalar : (s • (1 : Matrix (Fin 3) (Fin 3) ℚ)) = Matrix.scalar (Fin 3) s := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [← hscalar]
  exact not_singular n hn s


lemma Aq_pow_charpoly (n : ℕ) :
    (Aq^n).charpoly = ((A^n).charpoly).map (Int.castRingHom ℚ) := by
  rw [Aq, ← Matrix.map_pow, Matrix.charpoly_map]

/-- **Berend's (B1) holds for the one-element family `{A}`**: for every `n ≥ 1`,
`charpoly (A^n)` is irreducible (over `ℤ`, hence over `ℚ`). -/
theorem charpoly_pow_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible ((A^n).charpoly) := by
  have hq : Irreducible (((A^n).charpoly).map (Int.castRingHom ℚ)) := by
    rw [← Aq_pow_charpoly]
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have h3 : (Aq^n).charpoly.natDegree = 3 := by
        rw [Matrix.charpoly_natDegree_eq_dim]
        simp
      rw [h3]; decide
    · intro x hx
      rw [Polynomial.IsRoot] at hx
      exact no_rat_root n hn x hx
  have hprim : ((A^n).charpoly).IsPrimitive := (Matrix.charpoly_monic (A^n)).isPrimitive
  exact hprim.irreducible_iff_irreducible_map_fraction_map.mpr hq

/-- `A` has infinite order: `det A = 30 > 1`, so `A^l = A^k` forces `l = k`. -/
theorem pow_injective_nat : ∀ l k : ℕ, (A^l : Matrix (Fin 3) (Fin 3) ℤ) = A^k → l = k := by
  intro l k h
  have hdet := congrArg Matrix.det h
  simp only [Matrix.det_pow] at hdet
  have h30 : A.det = 30 := by decide
  rw [h30] at hdet
  have hnat : (30:ℕ)^l = 30^k := by exact_mod_cast hdet
  have hinj : Function.Injective (fun x : ℕ => (30:ℕ) ^ x) := Nat.pow_right_injective (by norm_num)
  exact hinj hnat

/-- (B3) for the pair `(A, -Id)`, exponent `l ≥ 1`: `A^l ≠ 1` since `det A^l = 30^l > 1`. -/
lemma A_pow_ne_one (l : ℕ) (hl : 0 < l) : (A^l : Matrix (Fin 3) (Fin 3) ℤ) ≠ 1 := by
  intro h
  have hdet := congrArg Matrix.det h
  simp only [Matrix.det_pow, Matrix.det_one] at hdet
  have h30 : A.det = 30 := by decide
  rw [h30] at hdet
  have h21 : (2:ℤ) ≤ 2^l := by
    have h' : (2:ℤ)^1 ≤ 2^l := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hl
    simpa using h'
  have h23 : (2:ℤ)^l ≤ 30^l := pow_le_pow_left₀ (a := (2:ℤ)) (b := 30) (by norm_num) (by norm_num) l
  omega

/-- (B3) for the pair `(A, -Id)`, exponent `l ≥ 1`: `A^l ≠ -1` since `det A^l = 30^l > 0`
while `det (-1) = -1`. -/
lemma A_pow_ne_neg_one (l : ℕ) (_hl : 0 < l) :
    (A^l : Matrix (Fin 3) (Fin 3) ℤ) ≠ -1 := by
  intro h
  have hdet := congrArg Matrix.det h
  simp only [Matrix.det_pow, Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at hdet
  have h30 : A.det = 30 := by decide
  rw [h30] at hdet
  have hpos : (0:ℤ) < 30^l := pow_pos (by norm_num) l
  rw [hdet] at hpos
  norm_num at hpos




def AmatR : Matrix (Fin 3) (Fin 3) ℝ := A.map (Int.castRingHom ℝ)

lemma AmatR_det : AmatR.det = 30 := by
  rw [AmatR, A, Matrix.det_fin_three]
  simp

/-- `p` read over `ℝ`, via `ℤ`. -/
lemma pR_eq_map' : pR = P.map (Int.castRingHom ℝ) := by
  rw [pR, pQ_eq_map, Polynomial.map_map]
  congr 1

/-- The characteristic polynomial of `A` over `ℝ` is `p`. -/
lemma AmatR_charpoly : AmatR.charpoly = pR := by
  rw [pR_eq_map', AmatR, Matrix.charpoly_map, charpoly_A]

noncomputable def linOf (M : GL (Fin 3) ℝ) : Pt ≃ₗ[ℝ] Pt :=
  (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun ℝ (Fin 3)) M).toLinearEquiv

lemma basisFun_repr_apply (v : Pt) : (Pi.basisFun ℝ (Fin 3)).repr v = v := by
  ext i; simp [Pi.basisFun_repr]

lemma basisFun_comb (w : Pt) :
    Fintype.linearCombination ℝ (⇑(Pi.basisFun ℝ (Fin 3))) w = w := by
  rw [Fintype.linearCombination_apply]
  simpa [Pi.basisFun_apply, Pi.basisFun_repr] using (Pi.basisFun ℝ (Fin 3)).sum_repr w

lemma linOf_apply (M : GL (Fin 3) ℝ) (v : Pt) :
    linOf M v = Matrix.toLin' (M : Matrix (Fin 3) (Fin 3) ℝ) v := by
  simp only [linOf, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  rw [basisFun_repr_apply, basisFun_comb]

noncomputable def gA : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero AmatR (by rw [AmatR_det]; norm_num)

lemma gA_val : (gA : Matrix (Fin 3) (Fin 3) ℝ) = AmatR := by
  simp [gA, Matrix.GeneralLinearGroup.mkOfDetNeZero]

noncomputable def fA : Pt ≃ₗ[ℝ] Pt := linOf gA

lemma det_fA : (LinearEquiv.det fA : ℝ) = 30 := by
  rw [LinearEquiv.coe_det]
  have h : (fA : Pt →ₗ[ℝ] Pt) = Matrix.toLin' AmatR := by
    refine LinearMap.ext fun v => ?_
    show linOf gA v = Matrix.toLin' AmatR v
    rw [linOf_apply, gA_val]
  rw [h, LinearMap.det_toLin', AmatR_det]

lemma fA_toLin : (fA : Pt →ₗ[ℝ] Pt) = Matrix.toLin' AmatR := by
  refine LinearMap.ext fun v => ?_
  show linOf gA v = Matrix.toLin' AmatR v
  rw [linOf_apply, gA_val]

/-- The underlying linear map of `fA` has characteristic polynomial `p` over `ℝ`. -/
lemma hchar_fA : LinearMap.charpoly (fA : Pt →ₗ[ℝ] Pt) = pR := by
  rw [fA_toLin, Matrix.charpoly_toLin', AmatR_charpoly]

lemma scalarMat_det_ne (c : ℝˣ) : ((c:ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  exact pow_ne_zero 3 c.ne_zero

noncomputable def gScalar (c : ℝˣ) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((c:ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (scalarMat_det_ne c)

lemma gScalar_val (c : ℝˣ) : (gScalar c : Matrix (Fin 3) (Fin 3) ℝ) = (c:ℝ) • 1 := by
  simp [gScalar, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The scalar map `c • id`. -/
noncomputable def linScalar (c : ℝˣ) : Pt ≃ₗ[ℝ] Pt := linOf (gScalar c)

lemma linScalar_apply (c : ℝˣ) (v : Pt) : linScalar c v = (c : ℝ) • v := by
  rw [linScalar, linOf_apply, Matrix.toLin'_apply, gScalar_val, Matrix.smul_mulVec, Matrix.one_mulVec]

lemma det_linScalar (c : ℝˣ) : (LinearEquiv.det (linScalar c) : ℝ) = (c : ℝ) ^ 3 := by
  rw [LinearEquiv.coe_det]
  have h : (linScalar c : Pt →ₗ[ℝ] Pt) = (c : ℝ) • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    exact linScalar_apply c v
  rw [h, LinearMap.det_smul, Module.finrank_fintype_fun_eq_card]
  have hone : LinearMap.det (LinearMap.id : Pt →ₗ[ℝ] Pt) = 1 := map_one LinearMap.det
  rw [hone, mul_one]
  norm_num




lemma padicValRat_zpow {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) (n : ℤ) :
    padicValRat p (q ^ n) = n * padicValRat p q := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hm : padicValRat p (q ^ (i:ℤ) * q) = padicValRat p (q ^ (i:ℤ)) + padicValRat p q :=
      padicValRat.mul (p := p) (q := q ^ (i:ℤ)) (r := q) (zpow_ne_zero _ hq) hq
    rw [zpow_add_one₀ hq, hm, ih]
    push_cast
    ring
  | pred i ih =>
    have hm : padicValRat p (q ^ (-(i:ℤ)) * q⁻¹) =
        padicValRat p (q ^ (-(i:ℤ))) + padicValRat p q⁻¹ :=
      padicValRat.mul (p := p) (q := q ^ (-(i:ℤ))) (r := q⁻¹) (zpow_ne_zero _ hq) (inv_ne_zero hq)
    rw [zpow_sub_one₀ hq, hm, padicValRat.inv, ih]
    push_cast
    ring

lemma padicValRat_nat (p n : ℕ) [Fact p.Prime] (h : ¬ p ∣ n) : padicValRat p ((n:ℕ):ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

lemma padicValRat_30 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    padicValRat p (30:ℚ) = 0 := by
  have h : (30:ℚ) = ((30:ℕ):ℚ) := by norm_num
  rw [h, padicValRat_nat]
  intro hdvd
  have hpge : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have h30 : (30:ℕ) = 2 * 3 * 5 := by norm_num
  rw [h30] at hdvd
  have hp := Fact.out (p := Nat.Prime p)
  rcases hp.dvd_mul.mp hdvd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h with h1 | h1
      · omega
      · exact hp2 h1
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h1
      · omega
      · exact hp3 h1
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | h1
    · omega
    · exact hp5 h1

lemma padicValRat_thirty (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (n : ℤ) : padicValRat p ((30:ℚ) ^ n) = 0 := by
  rw [padicValRat_zpow (by norm_num) n, padicValRat_30 p hp2 hp3 hp5, mul_zero]

lemma padicValRat_343 : padicValRat 7 (343:ℚ) = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h : (343:ℚ) = ((7:ℕ):ℚ)^3 := by norm_num
  rw [h, padicValRat.pow]
  have h7 : padicValRat 7 (((7:ℕ):ℚ)) = 1 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat_self (p := 7)
  rw [h7]
  norm_num

theorem thirty_zpow_eq_343_zpow {l k : ℤ} (h : (30:ℚ)^l = (343:ℚ)^k) : l = 0 ∧ k = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 := congrArg (padicValRat 7) h
  rw [padicValRat_thirty 7 (by norm_num) (by norm_num) (by norm_num) l,
    padicValRat_zpow (p := 7) (q := (343:ℚ)) (by norm_num) k, padicValRat_343] at h7
  have hk : k = 0 := by omega
  subst hk
  simp only [zpow_zero] at h
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h2 := congrArg (padicValRat 2) h
  have hv2 : padicValRat 2 (30:ℚ) = 1 := by
    have h : (30:ℚ) = ((2:ℕ):ℚ) * ((15:ℕ):ℚ) := by norm_num
    rw [h, padicValRat.mul (by norm_num) (by norm_num)]
    have h2' : padicValRat 2 (((2:ℕ):ℚ)) = 1 := by
      rw [padicValRat.of_nat]; exact_mod_cast padicValNat_self (p := 2)
    rw [h2', padicValRat_nat 2 15 (by norm_num)]
    norm_num
  rw [padicValRat_zpow (by norm_num) l, hv2] at h2
  have h1 : padicValRat 2 (1:ℚ) = 0 := by
    have h : (1:ℚ) = ((1:ℕ):ℚ) := by norm_num
    rw [h, padicValRat_nat 2 1 (by norm_num)]
  rw [h1] at h2
  omega



lemma padicValRat_thirty_two : padicValRat 2 (30:ℚ) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : (30:ℚ) = ((2:ℕ):ℚ) * ((15:ℕ):ℚ) := by norm_num
  rw [h, padicValRat.mul (by norm_num) (by norm_num)]
  have h2' : padicValRat 2 (((2:ℕ):ℚ)) = 1 := by
    rw [padicValRat.of_nat]; exact_mod_cast padicValNat_self (p := 2)
  rw [h2', padicValRat_nat 2 15 (by norm_num)]
  norm_num

/-- `v₂(-1) = 0`. -/
lemma padicValRat_neg_one : padicValRat 2 ((-1:ℚ)) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h1 : padicValRat 2 (1:ℚ) = 0 := by
    have h : (1:ℚ) = ((1:ℕ):ℚ) := by norm_num
    rw [h, padicValRat_nat 2 1 (by norm_num)]
  rw [show (-1:ℚ) = -(1:ℚ) by norm_num, padicValRat.neg, h1]

/-- `(30 : ℝ) ^ m = ± 1` forces `m = 0`. -/
lemma thirty_zpow_sq_eq_one {m : ℤ} (h : ((30:ℝ)^m)^2 = 1) : m = 0 := by
  have h' : (30:ℝ)^(m*2) = 1 := by
    rw [_root_.zpow_mul]
    exact h
  have hq : (30:ℚ)^(m*2) = 1 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact h'
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hh := congrArg (padicValRat 2) hq
  rw [padicValRat_zpow (by norm_num) (m*2), padicValRat_thirty_two, mul_one] at hh
  have h1 : padicValRat 2 (1:ℚ) = 0 := by
    have h : (1:ℚ) = ((1:ℕ):ℚ) := by norm_num
    rw [h, padicValRat_nat 2 1 (by norm_num)]
  rw [h1] at hh
  omega

lemma neg_one_zpow_mul_two (k : ℤ) : (-1:ℝ)^(k*2) = 1 := by
  rw [show k*2 = 2*k by ring, _root_.zpow_mul]
  norm_num

/-! ## The two families of torus endomorphisms -/

/-- The second generator of the model: `7 • id`. -/
noncomputable def seven : ℝˣ := Units.mk0 7 (by norm_num)

/-- The second generator of the model: `7 • id`. -/
noncomputable def fB : Pt ≃ₗ[ℝ] Pt := linScalar seven

lemma seven_val : (seven : ℝ) = 7 := rfl

lemma det_fB : (LinearEquiv.det fB : ℝ) = 343 := by
  rw [fB, det_linScalar, seven_val]
  norm_num

/-- The map `-id` — the second generator of the refuting family. -/
noncomputable def gNeg : Pt ≃ₗ[ℝ] Pt := linScalar (Units.mk0 (-1) (by norm_num))

lemma det_gNeg : (LinearEquiv.det gNeg : ℝ) = -1 := by
  rw [gNeg, det_linScalar]
  norm_num

/-- The model family, indexed by `Bool`: `true ↦ A`, `false ↦ 7 • id`. -/
noncomputable def famA : Bool → Pt ≃ₗ[ℝ] Pt
  | true => fA
  | false => fB

@[simp] lemma famA_true : famA true = fA := rfl
@[simp] lemma famA_false : famA false = fB := rfl

/-! ## Non-vacuity: the corrected (B3) holds for `A, 7 • id` -/

/-- **Corrected (B3) for the model.**  For all integers `l k`, `A ^ l = (7 • id) ^ k`
forces `l = k = 0`: the determinants are `30 ^ l` and `343 ^ k`, and `7` does not
divide any power of `30`. -/
theorem model_B3 (l k : ℤ) (h : (fA ^ l : Pt ≃ₗ[ℝ] Pt) = fB ^ k) : l = 0 ∧ k = 0 := by
  have hdet : (LinearEquiv.det fA) ^ l = (LinearEquiv.det fB) ^ k := by
    rw [← map_zpow, ← map_zpow, h]
  have hval : (30:ℝ)^l = (343:ℝ)^k := by
    have hv := congrArg Units.val hdet
    rwa [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, det_fA, det_fB] at hv
  have hq : (30:ℚ)^l = (343:ℚ)^k := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hval
  exact thirty_zpow_eq_343_zpow hq





/-! ## Why the correction excludes finite order -/

/-- **Any generator of finite order kills the corrected (B3).**  If `f j` has
finite order (`(f j)^m = 1` with `m ≠ 0`) then for every `i` the pair `(i, j)`
fails the corrected condition, because `(f i)^0 = 1 = (f j)^m` with `m ≠ 0`.
This is exactly the defect the old (B3) failed to exclude. -/
theorem corrected_B3_fails_of_torsion {ι : Type*} {f : ι → Pt ≃ₗ[ℝ] Pt} {j : ι} {m : ℤ}
    (hm : m ≠ 0) (h : (f j) ^ m = 1) (i : ι) :
    ¬ (∀ l k : ℤ, (f i) ^ l = (f j) ^ k → l = 0 ∧ k = 0) := by
  intro hB3
  have h0 : (f i) ^ (0:ℤ) = (f j) ^ m := by rw [zpow_zero, h]
  exact hm (hB3 0 m h0).2

/-! ## The correction implies the old hypothesis -/

/-- **The corrected (B3) implies the old (B3).**  Hence any theorem proved from
the corrected hypothesis is at least as strong as the old axiom's conclusion,
and the correction only removes witnesses such as `A, -id` above. -/
theorem corrected_B3_implies_old_B3 {ι : Type*} {f : ι → Pt ≃ₗ[ℝ] Pt}
    (B3 : ∃ i j : ι, ∀ l k : ℤ, (f i) ^ l = (f j) ^ k → l = 0 ∧ k = 0) :
    ∃ i j : ι, ∀ l k : ℤ, l ≠ 0 → k ≠ 0 → (f i) ^ l ≠ (f j) ^ k := by
  obtain ⟨i, j, hij⟩ := B3
  exact ⟨i, j, fun l k hl _ h => hl (hij l k h).1⟩

/-- **The two generators of the model commute.** -/
theorem model_comm (x : Pt) : fA (fB x) = fB (fA x) := by
  simp only [fB, linScalar_apply, map_smul]

/-- **(B2) for the model.**  For every common eigenvector of `A` and `7 • id` in
the complexification, the `A`-eigenvalue is a root of `p`, hence has modulus
`> 1`; so (B2) holds with witness `true`. -/
theorem model_B2 (x : ℂ ⊗[ℝ] Pt) (μ : Bool → ℂ) (hx : x ≠ 0)
    (h : ∀ i, LinearMap.baseChange ℂ ((famA i : Pt →ₗ[ℝ] Pt)) x = μ i • x) :
    ∃ i, 1 < ‖μ i‖ := by
  refine ⟨true, ?_⟩
  have hev : Module.End.HasEigenvector (LinearMap.baseChange ℂ (fA : Pt →ₗ[ℝ] Pt)) (μ true) x := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simpa using h true, hx⟩
  have hroot : (LinearMap.charpoly (LinearMap.baseChange ℂ (fA : Pt →ₗ[ℝ] Pt))).IsRoot (μ true) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
      (Module.End.hasEigenvalue_of_hasEigenvector hev)
  rw [LinearMap.charpoly_baseChange, hchar_fA] at hroot
  exact root_norm_gt_one (μ true) hroot

/-! ## Necessity: the old (B3) holds for `A, -id`, the corrected one fails -/

/-- The old (B3) holds for `A` and `-id`. -/
theorem old_B3_neg_one (l k : ℤ) (hl : l ≠ 0) (hk : k ≠ 0) :
    (fA ^ l : Pt ≃ₗ[ℝ] Pt) ≠ gNeg ^ k := by
  intro h
  have hdet : (LinearEquiv.det fA) ^ l = (LinearEquiv.det gNeg) ^ k := by
    rw [← map_zpow, ← map_zpow, h]
  have hval : (30:ℝ)^l = (-1:ℝ)^k := by
    have hv := congrArg Units.val hdet
    rwa [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, det_fA, det_gNeg] at hv
  have hq : (30:ℚ)^l = (-1:ℚ)^k := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hval
  have hzero := congrArg (padicValRat 2) hq
  rw [padicValRat_zpow (p := 2) (by norm_num) l, padicValRat_thirty_two, mul_one,
      padicValRat_zpow (p := 2) (q := (-1:ℚ)) (by norm_num) k, padicValRat_neg_one, mul_zero] at hzero
  omega

/-- The corrected (B3) fails for `A` and `-id`: `A ^ 0 = 1 = (-1) ^ 2`. -/
theorem not_corrected_B3_neg_one :
    ¬ (∀ l k : ℤ, (fA ^ l : Pt ≃ₗ[ℝ] Pt) = gNeg ^ k → l = 0 ∧ k = 0) := by
  intro h
  have h0 : (fA ^ (0:ℤ) : Pt ≃ₗ[ℝ] Pt) = gNeg ^ (2:ℤ) := by
    rw [zpow_zero, zpow_ofNat, pow_two]
    refine LinearEquiv.ext fun x => ?_
    simp [gNeg, linScalar_apply, smul_smul]
  have hh := h 0 2 h0
  omega

section Lattice

/-- The standard lattice `ℤ³ ⊂ Pt`, as a submodule. -/
abbrev L3s : Submodule ℤ Pt := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

/-- The standard lattice `ℤ³ ⊂ Pt`, as an additive subgroup. -/
abbrev L3 : AddSubgroup Pt := L3s.toAddSubgroup

lemma L3_toInt : AddSubgroup.toIntSubmodule L3 = L3s := rfl

instance instDiscL3 : DiscreteTopology (AddSubgroup.toIntSubmodule L3) :=
  show DiscreteTopology L3s from inferInstance

instance instZLLattice3 : IsZLattice ℝ (AddSubgroup.toIntSubmodule L3) :=
  show IsZLattice ℝ L3s from inferInstance

/-- A `ℤ`-basis of `ℤ³`. -/
noncomputable def L3basis : Module.Basis (Fin 3) ℤ (AddSubgroup.toIntSubmodule L3) :=
  IsZLattice.basis (AddSubgroup.toIntSubmodule L3)

/-- The integral restriction of a real-linear lattice endomorphism.  This is the
same definition as `CubicTwoStage.latticeAct`; it is restated here so that this
module does not import the module that declares the old axiom. -/
noncomputable def latticeActZ (L : AddSubgroup Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  LinearMap.restrict (LinearMap.restrictScalars ℤ f)
    (p := AddSubgroup.toIntSubmodule L) (q := AddSubgroup.toIntSubmodule L) hf

lemma latticeActZ_apply {L : AddSubgroup Pt} {f : Pt →ₗ[ℝ] Pt}
    {hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L} (x : AddSubgroup.toIntSubmodule L) :
    latticeActZ L f hf x = ⟨f (x : Pt), hf _ x.2⟩ := rfl

/-- **The characteristic polynomial of the integral restriction**, mapped to `ℝ`,
is the characteristic polynomial of the real-linear map.  Stated for an arbitrary
`ℤ`-basis of the lattice; no coordinates are needed. -/
lemma charpoly_latticeActZ_map (L : AddSubgroup Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ L, f x ∈ AddSubgroup.toIntSubmodule L)
    (b : Module.Basis (Fin 3) ℤ (AddSubgroup.toIntSubmodule L))
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)] :
    (LinearMap.charpoly (latticeActZ L f hf)).map (Int.castRingHom ℝ) = LinearMap.charpoly f := by
  have hmat : ((LinearMap.toMatrix b b (latticeActZ L f hf)).map (Int.castRingHom ℝ)) =
      LinearMap.toMatrix (b.ofZLatticeBasis ℝ) (b.ofZLatticeBasis ℝ) f := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, latticeActZ_apply,
      Module.Basis.ofZLatticeBasis_apply]
    conv_rhs =>
      rw [show f ↑(b j) = ↑(⟨f ↑(b j), hf _ (b j).2⟩ : AddSubgroup.toIntSubmodule L) from rfl]
    rw [Module.Basis.ofZLatticeBasis_repr_apply]
    rfl
  calc (LinearMap.charpoly (latticeActZ L f hf)).map (Int.castRingHom ℝ)
      = ((LinearMap.toMatrix b b (latticeActZ L f hf)).map (Int.castRingHom ℝ)).charpoly := by
        rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    _ = (LinearMap.toMatrix (b.ofZLatticeBasis ℝ) (b.ofZLatticeBasis ℝ) f).charpoly := by
        rw [hmat]
    _ = LinearMap.charpoly f := LinearMap.charpoly_toMatrix _ _

lemma single_mem (i : Fin 3) : (Pi.single i (1:ℝ) : Pt) ∈ L3s := by
  refine Submodule.subset_span ?_
  exact ⟨i, by rw [Pi.basisFun_apply]⟩

lemma fA_single (i : Fin 3) :
    (fA : Pt →ₗ[ℝ] Pt) (Pi.single i (1:ℝ)) =
      ∑ k, ((A k i : ℤ) : ℝ) • (Pi.single k (1:ℝ) : Pt) := by
  rw [fA_toLin, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  funext m
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single m]
  · simp [AmatR, A]
  · intro k _ hk; simp [Ne.symm hk]
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-- `fA` preserves the standard lattice `ℤ³`. -/
lemma fA_mem : ∀ g ∈ L3s, (fA : Pt →ₗ[ℝ] Pt) g ∈ L3s := by
  have hmap : Submodule.map (LinearMap.restrictScalars ℤ (fA : Pt →ₗ[ℝ] Pt)) L3s ≤ L3s := by
    rw [show L3s = Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) from rfl, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    rw [LinearMap.coe_restrictScalars,
      show (Pi.basisFun ℝ (Fin 3)) i = (Pi.single i (1:ℝ) : Pt) from Pi.basisFun_apply ℝ (Fin 3) i,
      fA_single]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (single_mem k)
  intro g hg
  exact hmap (Submodule.mem_map_of_mem hg)

/-- `fA` preserves the standard lattice. -/
lemma hfA_mem : ∀ x ∈ L3, (fA : Pt →ₗ[ℝ] Pt) x ∈ AddSubgroup.toIntSubmodule L3 := fA_mem

lemma hfA_mem_pow (n : ℕ) :
    ∀ x ∈ AddSubgroup.toIntSubmodule L3,
      ((fA : Pt →ₗ[ℝ] Pt) ^ n) x ∈ AddSubgroup.toIntSubmodule L3 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact ih _ (fA_mem x hx)

lemma latticeActZ_pow_apply (n : ℕ) (x : AddSubgroup.toIntSubmodule L3) :
    (((latticeActZ L3 (fA : Pt →ₗ[ℝ] Pt) hfA) ^ n) x : Pt) =
      ((fA : Pt →ₗ[ℝ] Pt) ^ n) (x : Pt) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
    show (fA : Pt →ₗ[ℝ] Pt)
      ((((latticeActZ L3 (fA : Pt →ₗ[ℝ] Pt) hfA) ^ n) x : AddSubgroup.toIntSubmodule L3) : Pt) =
        ((fA : Pt →ₗ[ℝ] Pt) ^ (n+1)) (x : Pt)
    rw [ih, pow_succ', Module.End.mul_apply]

lemma latticeActZ_pow_eq (n : ℕ) :
    (latticeActZ L3 (fA : Pt →ₗ[ℝ] Pt) hfA) ^ n =
      latticeActZ L3 ((fA : Pt →ₗ[ℝ] Pt) ^ n) (hfA_mem_pow n) := by
  refine LinearMap.ext fun x => ?_
  refine Subtype.ext ?_
  rw [latticeActZ_pow_apply n x]
  rfl

lemma charpoly_fA_pow (n : ℕ) :
    LinearMap.charpoly ((fA : Pt →ₗ[ℝ] Pt) ^ n) = ((A ^ n).charpoly).map (Int.castRingHom ℝ) := by
  have h1 : ((fA : Pt →ₗ[ℝ] Pt) ^ n) = Matrix.toLin' (AmatR ^ n) := by
    rw [fA_toLin]
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
    | succ n ih => rw [pow_succ', pow_succ', Matrix.toLin'_mul, ih]; rfl
  rw [h1, Matrix.charpoly_toLin', AmatR, ← Matrix.map_pow, Matrix.charpoly_map]

/-- **(B1) for the model, in the lattice form of the axiom.**  For every `n ≥ 1`
the characteristic polynomial of the `n`-th power of the integral restriction of
`A` to `ℤ³` is irreducible. -/
theorem model_B1 (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (LinearMap.charpoly ((latticeActZ L3 (fA : Pt →ₗ[ℝ] Pt) hfA) ^ n)) := by
  rw [latticeActZ_pow_eq]
  have hmap : (LinearMap.charpoly (latticeActZ L3 ((fA : Pt →ₗ[ℝ] Pt) ^ n) (hfA_mem_pow n))).map
        (Int.castRingHom ℝ) = ((A ^ n).charpoly).map (Int.castRingHom ℝ) := by
    rw [charpoly_latticeActZ_map L3 ((fA : Pt →ₗ[ℝ] Pt) ^ n) (hfA_mem_pow n) L3basis,
      charpoly_fA_pow]
  have heq : LinearMap.charpoly (latticeActZ L3 ((fA : Pt →ₗ[ℝ] Pt) ^ n) (hfA_mem_pow n)) =
      (A ^ n).charpoly :=
    Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective hmap
  rw [heq]
  exact charpoly_pow_irreducible n hn

end Lattice

/-- **The hypothesis bundle of the corrected statement holds for the model.**
With `L = ℤ³ ⊂ Pt` and the family `true ↦ A`, `false ↦ 7 • id`:

* the two maps commute;
* (B1) holds in the axiom's lattice form, for the integral restriction `latticeActZ`
  (the same definition as `CubicTwoStage.latticeAct`);
* (B2) holds in the axiom's form;
* the corrected (B3) holds.

So the corrected hypotheses are consistent: no obstruction prevents a model,
and the correction is not vacuous. -/
theorem model_hypotheses :
    (∀ x : Pt, fA (fB x) = fB (fA x)) ∧
    (∀ n : ℕ, 1 ≤ n → Irreducible
      (LinearMap.charpoly ((latticeActZ L3 (fA : Pt →ₗ[ℝ] Pt) hfA) ^ n))) ∧
    (∀ (x : ℂ ⊗[ℝ] Pt) (μ : Bool → ℂ), x ≠ 0 →
      (∀ i, LinearMap.baseChange ℂ ((famA i : Pt →ₗ[ℝ] Pt)) x = μ i • x) →
      ∃ i, 1 < ‖μ i‖) ∧
    (∃ i j : Bool, ∀ l k : ℤ, (famA i) ^ l = (famA j) ^ k → l = 0 ∧ k = 0) :=
  ⟨model_comm, fun n hn => model_B1 n hn, model_B2,
    ⟨true, false, fun l k h => model_B3 l k (by simpa using h)⟩⟩

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendModel.model_hypotheses
#print axioms CubicTwoStage.BerendModel.model_B1
#print axioms CubicTwoStage.BerendModel.charpoly_latticeActZ_map
#print axioms CubicTwoStage.BerendModel.model_B2
#print axioms CubicTwoStage.BerendModel.model_B3
#print axioms CubicTwoStage.BerendModel.model_comm
#print axioms CubicTwoStage.BerendModel.corrected_B3_fails_of_torsion
#print axioms CubicTwoStage.BerendModel.old_B3_neg_one
#print axioms CubicTwoStage.BerendModel.not_corrected_B3_neg_one
#print axioms CubicTwoStage.BerendModel.charpoly_pow_irreducible
#print axioms CubicTwoStage.BerendModel.root_norm_gt_one

end BerendModel
end CubicTwoStage
