/-
# The eigen-model of the unit–prime family, and the trace-norm relations

Swarm `smw83svqu`, member m8, direction **d3** = item (3) of the Stage I plan:
"bridge the diagonal model to the actual `UnitPrimeModel` eigenbasis via
`BerendA3`/`FieldModel` and carry the trace-norm relations `|Nm π| = p > 1` and
`|Nm ε| = 1`".

This module is self-contained, project-owned, contains no `sorry` and proves
nothing from the old axiom (see the audit at the end).  It imports only
`CubicTwoStage.FieldModel`.

## What the model algebra is

`Pt = Fin 3 → ℝ` is the algebra `ℝ × ℂ` under `⋆ = mulC`: a real coordinate `x 0`
and one complex coordinate `x 1 + i x 2`.  The unit–prime family is
`x ↦ μ_{u π^j} ⋆ x` with `μ_{u π^j} = σ(u) ⋆ σ(π)^j` (`UnitPrimeModel.mult`).

## What is proved here

1. **The multiplication operators** `ptMul a : Pt →ₗ[ℝ] Pt`, `x ↦ a ⋆ x`, forming a
   commutative monoid of linear maps (`ptMul_mul`, `ptMul_pow`), agreeing with the
   projective family (`ptMul_toAddMonoidHom`, `UnitPrimeModel.linFam_eq_ptMul`,
   `UnitPrimeModel.family_act_eq_ptMul`).
2. **The block form** (`ptMul_apply_zero`, `cplxOf_ptMul`, `normC_ptMul`): in the
   *standard* coordinates the map is `x 0 ↦ (a 0) x 0` on the real line and
   `z ↦ (a 1 + i a 2) z` on the complex line.  This is the exact, real form of the
   action; it needs no eigenbasis.
3. **The determinant** `LinearMap.det (ptMul a) = normR a = a 0 (a 1² + a 2²)`
   (`ptMul_det`), i.e. the product of the three eigenvalues equals the extended
   norm.  This is the structural fact behind every trace-norm relation below.
4. **The eigen-model** (the "actual eigenbasis"): the eigenvalue vector
   `lamVec a = (a 0, a 1 + i a 2, a 1 - i a 2)` (`lamVec`), which is
   *multiplicative* (`lamVec_mulC`, `lamVec_powC`), has product `normR a`
   (`prod_lamVec`), and whose three entries are exactly the eigenvalues of
   `ptMul a` on `ℂ ⊗[ℝ] Pt` with eigenlines `e 0`, `e 1 - i e 2`, `e 1 + i e 2`
   (`eigVec`, `baseChange_ptMul_eigen`).  The list is complete: every eigenvalue is
   one of the three (`baseChange_eigenvalue_mem`), with characteristic polynomial
   `∏ i, (X - lamVec a i)` (`ptMulC_charpoly`).  The construction is *explicit* —
   it does not need (B1) — and `cEquiv`/`conj_baseChange_ptMul` identify the
   complexified action with the matrix model `ptMulC`.
5. **The trace-norm relations in eigen-multiplier form**, for the model
   `D = FM.toModel ε π hπO hπ0` of a `FieldModel`
   (`FM.normR_abs` gives `|Nm|` explicitly, `FieldModel.Nm_unit` gives the unit
   norm one, `hπN : Nm π = p` is the arithmetic input):
   * `|normR (D.mult u j)| = p ^ j` (`abs_normR_mult`),
   * the same on the determinant: `|det (ptMul (D.mult u j))| = p ^ j`
     (`abs_det_mult`),
   * the product of the three eigen-moduli is `p ^ j` and the product for a unit
     is `1` (`prod_lamAbs_mult`, `prod_lamAbs_unit`),
   * split over the two real radial coordinates: `|x 0| * normC = p ^ j`
     (`abs_fst_mul_normC_mult`),
   * the two complex eigen-moduli coincide (`lamAbs_one_eq_two`) and some place
     expands whenever `j > 0` (`exists_one_lt_lamAbs_mult`) — the arithmetic
     content of (B2) for the prime direction,
   * the eigen-multiplier vector of a family element is `τ(u) τ(π)^j`
     (`lamVec_mult`, `UnitPrimeModel.linFam_eigenvalue`, `UnitPrimeModel.lamAbs_family`),
   * the eigen-multiplier vector separates points
     (`lamVec_σ_injective`) and transfers power relations back to the field
     (`lamVec_pow_eq_imp_pow_eq`), so multiplicative independence in the field —
     which the corrected (B3) supplies for `(ε, π)` via
     `BerendCorrected.rational_independence_corrected` — is an independence of the
     whole multiplier vector, not of one coordinate at a time.

## What is *not* proved here, and the precise obstruction (important)

The abstract diagonal model of `BerendSec4`/`BerendModulus` is the family
`diag lam` on `ι → ℝ` with **real** multipliers.  For the concrete unit–prime
model such a presentation does **not** exist in general, and this is not a gap in
the formalisation but a fact about the model:

* `ptMul_real_eigenvector_axis`: if the complex coordinate of a multiplier is
  non-real (`a 2 ≠ 0`), then the *only* real eigenline of `ptMul a` is the real
  axis `{x : x 1 = x 2 = 0}` (`ptMul_single_zero` shows that one always exists).
  Hence for a cubic field with a genuinely complex place — e.g. `π` with
  `K = ℚ(π)`, `μ_π` non-real at the complex place — the family is not diagonal in
  any real basis: two of its three eigenvalues are a non-real conjugate pair.

So the transfer to the diagonal model must go through one of
(a) the complexification (`eigVec`, `baseChange_ptMul_eigen` here — but the lattice
and the torus are real, so compactness/density arguments do not transfer
verbatim), (b) the block model of §2 (real coordinate plus complex coordinate,
with `normC_ptMul` giving the radial scaling and the phase rotating), or (c) an
extra hypothesis forcing every family multiplier to be totally real (all three
conjugates real, which is *not* implied by (B1)).  Whatever route is taken, the
"multiplicatively independent scalars at each coordinate" hypothesis `MulIndep
(lam i) (mu i)` of `BerendRankTwoDiag.acc_coord_subset_sub` is *not* derivable
per coordinate: `lamVec_pow_eq_imp_pow_eq` shows only that a power relation
holding at *all three* places forces `ε ^ m = π ^ n` (which (B3) then kills).  A
relation at a single place is not excluded by (B1), (B2) or (B3).

Consequently this module supplies the eigenbasis, the eigenvalue completeness, the
trace-norm relations and the per-place multiplier formulas — the arithmetic layer
that every Stage I branch consumes — but it does **not** prove
`eq_univ_of_zero_nonisolated`, and it identifies the missing input precisely: a
real (or block) diagonalisation, equivalently a substitute for `MulIndep` at a
single coordinate.
-/
import CubicTwoStage.FieldModel

set_option linter.unusedSimpArgs false

open scoped TensorProduct

namespace CubicTwoStage

/-! ## 1. Multiplication by a model element, as a real-linear map -/

/-- Multiplication by `a` in the model algebra `ℝ × ℂ`, as a real-linear map. -/
noncomputable def ptMul (a : Pt) : Pt →ₗ[ℝ] Pt where
  toFun := fun x => a ⋆ x
  map_add' := fun x y => mulC_add a x y
  map_smul' := fun r x => smul_mulC r a x

@[simp] lemma ptMul_apply (a x : Pt) : ptMul a x = a ⋆ x := rfl

@[simp] lemma ptMul_one : ptMul oneC = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [oneC_mulC]

lemma ptMul_comp (a b : Pt) : (ptMul a).comp (ptMul b) = ptMul (a ⋆ b) := by
  ext x
  simp only [LinearMap.comp_apply, ptMul_apply, mulC_assoc]

@[simp] lemma ptMul_mul (a b : Pt) : ptMul a * ptMul b = ptMul (a ⋆ b) := ptMul_comp a b

lemma ptMul_pow (a : Pt) (n : ℕ) : (ptMul a) ^ n = ptMul (powC a n) := by
  induction n with
  | zero => rw [powC_zero, ptMul_one]; exact Module.End.one_eq_id
  | succ n ih =>
      rw [pow_succ, ih, ptMul_mul, mulC_comm, ← powC_succ]

/-- `ptMul` agrees with the additive-hom family used by `UnitPrimeModel`. -/
lemma ptMul_toAddMonoidHom (a : Pt) :
    (ptMul a).toAddMonoidHom = addHomMulC a := rfl

/-! ## 2. The block form: a real coordinate and one complex coordinate -/

/-- The complex coordinate of a point of the model algebra `ℝ × ℂ`. -/
def cplxOf (x : Pt) : ℂ := ⟨x 1, x 2⟩

@[simp] lemma cplxOf_re (x : Pt) : (cplxOf x).re = x 1 := rfl
@[simp] lemma cplxOf_im (x : Pt) : (cplxOf x).im = x 2 := rfl

lemma cplxOf_mulC (a b : Pt) : cplxOf (a ⋆ b) = cplxOf a * cplxOf b := by
  apply Complex.ext <;> simp [cplxOf, Complex.mul_re, Complex.mul_im]

lemma cplxOf_add (a b : Pt) : cplxOf (a + b) = cplxOf a + cplxOf b := by
  apply Complex.ext <;> simp [cplxOf]

lemma cplxOf_smul (r : ℝ) (a : Pt) : cplxOf (r • a) = ⟨r, 0⟩ * cplxOf a := by
  apply Complex.ext <;> simp [cplxOf]

lemma ptMul_apply_zero (a x : Pt) : ptMul a x 0 = a 0 * x 0 := by
  simp

/-- The complex block is multiplication by the complex coordinate of `a`. -/
lemma cplxOf_ptMul (a x : Pt) : cplxOf (ptMul a x) = cplxOf a * cplxOf x := by
  simp [cplxOf_mulC]

/-- The squared modulus of the complex coordinate. -/
def normC (x : Pt) : ℝ := x 1 ^ 2 + x 2 ^ 2

lemma normC_eq_normSq (x : Pt) : normC x = Complex.normSq (cplxOf x) := by
  simp [normC, cplxOf, Complex.normSq_apply, sq]

lemma normC_mulC (a b : Pt) : normC (a ⋆ b) = normC a * normC b := by
  rw [normC_eq_normSq, cplxOf_mulC, Complex.normSq_mul, ← normC_eq_normSq, ← normC_eq_normSq]

lemma normC_ptMul (a x : Pt) : normC (ptMul a x) = normC a * normC x :=
  normC_mulC a x

lemma normR_eq_mul_normC (x : Pt) : normR x = x 0 * normC x := rfl

/-! ## 3. The determinant is the extended norm -/

section Determinant

lemma ptMul_toMatrix' (a : Pt) :
    LinearMap.toMatrix' (ptMul a) = !![a 0, 0, 0; 0, a 1, -a 2; 0, a 2, a 1] := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  fin_cases i <;> fin_cases j <;> simp [ptMul_apply, mulC]

/-- **The determinant of multiplication by `a` is the extended norm `Nm(u,w) = u|w|²`.**
In the eigen-picture below this says that the product of the three eigenvalues
`a 0`, `a 1 + i a 2`, `a 1 - i a 2` is `normR a`. -/
theorem ptMul_det (a : Pt) : LinearMap.det (ptMul a) = normR a := by
  rw [← LinearMap.det_toMatrix' (ptMul a), ptMul_toMatrix', Matrix.det_fin_three]
  simp [normR]
  ring

lemma ptMul_det_apply_base (a : Pt) : |LinearMap.det (ptMul a)| = |normR a| := by
  rw [ptMul_det]

end Determinant

/-! ## 4. The unit–prime family: the trace-norm relations -/

section UnitPrime

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

lemma normC_nonneg (x : Pt) : 0 ≤ normC x := by
  have := sq_nonneg (x 1); have := sq_nonneg (x 2)
  simp only [normC]; linarith

lemma abs_normR_powC (a : Pt) (n : ℕ) : |normR (powC a n)| = |normR a| ^ n := by
  induction n with
  | zero => simp [normR_oneC]
  | succ n ih =>
      rw [powC_succ, normR_mulC, abs_mul, ih, pow_succ']

/-- **The trace-norm relation for the prime multiplier.**  For the unit–prime
model attached to a `FieldModel`, every family element `μ_{uπ^j}` has
`|Nm (μ_{uπ^j})| = p ^ j`, because units have norm one (`FieldModel.Nm_unit`) and
`Nm π = p`.  This is the product of the three eigen-multipliers
`τ(uπ^j)`, `τ ∈ {σ₁, σ₂, σ̄₂}`, read through `ptMul_det`. -/
theorem abs_normR_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (p : ℕ) (hπN : Nm π = (p : ℚ≥0)) (u : 𝒪ˣ) (j : ℕ) :
    |normR ((FM.toModel ε π hπO hπ0).mult u j)| = (p : ℝ) ^ j := by
  have hπR : |normR (FM.σ π)| = (p : ℝ) := by
    rw [FM.normR_abs, hπN]
    push_cast
    ring
  have huR : |normR (FM.σ (((u : 𝒪) : K)))| = 1 := FM.abs_normR_unit u
  show |normR (FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j)| = (p : ℝ) ^ j
  rw [normR_mulC, abs_mul, abs_normR_powC, huR, hπR, one_mul]

/-- The same relation read on the determinant of the linear map `ptMul`. -/
theorem abs_det_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (p : ℕ) (hπN : Nm π = (p : ℚ≥0)) (u : 𝒪ˣ) (j : ℕ) :
    |LinearMap.det (ptMul ((FM.toModel ε π hπO hπ0).mult u j))| = (p : ℝ) ^ j := by
  rw [ptMul_det, abs_normR_mult FM ε π hπO hπ0 p hπN u j]

/-- The same relation split over the two *radial* coordinates: the real
coordinate `x ↦ x 0` and the complex modulus `|z|²`.  These are the two real
multipliers of the block-diagonal action of the family. -/
theorem abs_fst_mul_normC_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (p : ℕ) (hπN : Nm π = (p : ℚ≥0)) (u : 𝒪ˣ) (j : ℕ) :
    |((FM.toModel ε π hπO hπ0).mult u j) 0| * normC ((FM.toModel ε π hπO hπ0).mult u j)
      = (p : ℝ) ^ j := by
  have h := abs_normR_mult FM ε π hπO hπ0 p hπN u j
  rw [normR_eq_mul_normC, abs_mul, abs_of_nonneg (normC_nonneg _)] at h
  exact h

/-- The family action is multiplication by `D.mult i.1 i.2`. -/
lemma UnitPrimeModel.family_act_eq_ptMul {L : AddSubgroup Pt} (D : UnitPrimeModel L 𝒪)
    (i : 𝒪ˣ × ℕ) : D.family.act i = (ptMul (D.mult i.1 i.2)).toAddMonoidHom := rfl

end UnitPrime

/-! ## 5. The eigen-model: three eigenlines with eigenvalues `a 0`, `a 1 + i a 2`,
`a 1 - i a 2`

The model algebra `ℝ × ℂ` has three characters when complexified: the real
coordinate `a ↦ a 0` and the two conjugate complex coordinates `a ↦ a 1 ± i a 2`.
They are the eigenvalues of `ptMul a` on `ℂ ⊗[ℝ] Pt`; the eigenlines are
`e 0`, `e 1 - i e 2` and `e 1 + i e 2`.  This is the concrete form of the common
eigenbasis used by Stage I: in these coordinates the whole unit–prime family is
diagonal, with multipliers `τ(u π^j)` at the place `τ`. -/

open Polynomial

/-- The eigenvalue vector of multiplication by `a`, indexed by the three
characters of `ℝ × ℂ` (the three places of the cubic field in the intended
model): `0 ↦ a 0` (the real place), `1 ↦ a 1 + i a 2` and `2 ↦ a 1 - i a 2`
(the complex place and its conjugate). -/
noncomputable def lamVec (a : Pt) : Fin 3 → ℂ :=
  ![⟨a 0, 0⟩, ⟨a 1, a 2⟩, ⟨a 1, -a 2⟩]

@[simp] lemma lamVec_zero (a : Pt) : lamVec a 0 = ⟨a 0, 0⟩ := rfl
@[simp] lemma lamVec_one (a : Pt) : lamVec a 1 = ⟨a 1, a 2⟩ := rfl
@[simp] lemma lamVec_two (a : Pt) : lamVec a 2 = ⟨a 1, -a 2⟩ := rfl

/-- The eigenvalue vector is multiplicative. -/
theorem lamVec_mulC (a b : Pt) : lamVec (a ⋆ b) = fun i => lamVec a i * lamVec b i := by
  funext i
  fin_cases i <;>
    simp [lamVec, Complex.ext_iff, Complex.mul_re, Complex.mul_im, mulC_apply_zero,
      mulC_apply_one, mulC_apply_two]
    <;> ring

/-- The product of the eigenvalues is the extended norm `Nm(u,w) = u|w|²`, i.e. the
determinant of `ptMul`. -/
theorem prod_lamVec (a : Pt) : (∏ i, lamVec a i) = ⟨normR a, 0⟩ := by
  simp [lamVec, normR, Fin.prod_univ_three, Complex.ext_iff]
  constructor <;> ring

/-- The modulus vector of the eigenvalues: the three archimedean absolute values of
the corresponding field element. -/
noncomputable def lamAbs (a : Pt) : Fin 3 → ℝ := fun i => ‖lamVec a i‖

/-- The modulus of a real complex number. -/
lemma norm_realC (x : ℝ) : ‖(⟨x, 0⟩ : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [mul_zero, add_zero]
  rw [show x * x = x ^ 2 by ring, Real.sqrt_sq_eq_abs]

theorem prod_lamAbs (a : Pt) : (∏ i, lamAbs a i) = |normR a| := by
  have h : (∏ i, lamAbs a i) = ‖∏ i, lamVec a i‖ := by
    simpa only [lamAbs] using (norm_prod (Finset.univ : Finset (Fin 3)) (lamVec a)).symm
  rw [h, prod_lamVec, norm_realC]

theorem lamAbs_mulC (a b : Pt) : lamAbs (a ⋆ b) = fun i => lamAbs a i * lamAbs b i := by
  funext i
  simp [lamAbs, lamVec_mulC]


/-! ### The eigen-coordinates and the conjugation to the matrix model -/

open Complex in
/-- The matrix model of the complexified multiplication: multiplication by
`a` on `Fin 3 → ℂ`, in the coordinates in which it is lower block triangular. -/
noncomputable def ptMulC (a : Pt) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  Matrix.toLin' !![(a 0 : ℂ), 0, 0; 0, (a 1 : ℂ), -(a 2 : ℂ); 0, (a 2 : ℂ), (a 1 : ℂ)]

/-- The complex coordinate equivalence `ℂ ⊗[ℝ] Pt ≃ₗ[ℂ] (Fin 3 → ℂ)`. -/
noncomputable def cEquiv : ℂ ⊗[ℝ] Pt ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  TensorProduct.piScalarRight ℝ ℂ ℂ (Fin 3)

lemma cEquiv_symm_single (x : ℂ) (j : Fin 3) :
    cEquiv.symm (Pi.single j x) = x ⊗ₜ[ℝ] Pi.single j 1 := by
  simp [cEquiv]

lemma cEquiv_tmul (x : ℂ) (y : Pt) : cEquiv (x ⊗ₜ[ℝ] y) = fun k => y k • x := by
  simp [cEquiv]

/-- **The conjugation identity.**  In the coordinates `Fin 3 → ℂ` the complexified
multiplication map is the explicit matrix model `ptMulC a`. -/
theorem conj_baseChange_ptMul (a : Pt) :
    cEquiv.conj ((ptMul a).baseChange ℂ) = ptMulC a := by
  have h : LinearMap.toMatrix' (cEquiv.conj ((ptMul a).baseChange ℂ))
      = !![(a 0 : ℂ), 0, 0; 0, (a 1 : ℂ), -(a 2 : ℂ); 0, (a 2 : ℂ), (a 1 : ℂ)] := by
    ext i j
    rw [LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply, cEquiv_symm_single,
      LinearMap.baseChange_tmul, cEquiv_tmul]
    fin_cases i <;> fin_cases j <;> simp [ptMul_apply, mulC]
  rw [ptMulC, ← h, Matrix.toLin'_toMatrix']

/-- The eigenvalue equations in the matrix model, at the three eigenlines
`e 0`, `e 1 - i e 2`, `e 1 + i e 2`. -/
theorem ptMulC_eigen (a : Pt) (i : Fin 3) :
    ptMulC a (![Pi.single 0 1, Pi.single 1 1 - Complex.I • Pi.single 2 1,
      Pi.single 1 1 + Complex.I • Pi.single 2 1] i)
      = lamVec a i • (![Pi.single 0 1, Pi.single 1 1 - Complex.I • Pi.single 2 1,
      Pi.single 1 1 + Complex.I • Pi.single 2 1] i) := by
  fin_cases i
  · ext k
    fin_cases k <;>
      simp [ptMulC, Matrix.toLin'_apply, Matrix.mulVec, lamVec, Complex.ext_iff]
  · ext k
    fin_cases k <;>
      simp [ptMulC, Matrix.toLin'_apply, Matrix.mulVec, lamVec, Complex.ext_iff] <;> ring
  · ext k
    fin_cases k <;>
      simp [ptMulC, Matrix.toLin'_apply, Matrix.mulVec, lamVec, Complex.ext_iff] <;> ring

/-- The three eigenlines of the complexified action, in `ℂ ⊗[ℝ] Pt`. -/
noncomputable def eigVec (i : Fin 3) : ℂ ⊗[ℝ] Pt :=
  cEquiv.symm (![Pi.single 0 1, Pi.single 1 1 - Complex.I • Pi.single 2 1,
    Pi.single 1 1 + Complex.I • Pi.single 2 1] i)

/-- **The eigen-equations for the complexified unit–prime action.**  In the
complexification of `Pt` the multiplication map has the three eigenvalues
`a 0`, `a 1 + i a 2`, `a 1 - i a 2` with the eigenlines `e 0`, `e 1 - i e 2`,
`e 1 + i e 2`. -/
theorem baseChange_ptMul_eigen (a : Pt) (i : Fin 3) :
    (ptMul a).baseChange ℂ (eigVec i) = lamVec a i • eigVec i := by
  refine cEquiv.injective ?_
  rw [map_smul]
  simp only [eigVec]
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.conj_apply_apply, conj_baseChange_ptMul]
  exact ptMulC_eigen a i

theorem lamVec_powC (a : Pt) (n : ℕ) : lamVec (powC a n) = fun i => (lamVec a i) ^ n := by
  induction n with
  | zero =>
      funext i
      fin_cases i <;> simp [powC_zero, lamVec, oneC, Complex.ext_iff]
  | succ n ih =>
      rw [powC_succ, lamVec_mulC, ih]
      funext i
      simp [pow_succ, mul_comm]

/-- The eigenvalue vector of the whole unit–prime family is multiplicative in the
index: `τ(u π^j)` at the place `τ`. -/
theorem lamVec_mult {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}
    (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (u : 𝒪ˣ) (j : ℕ) :
    lamVec ((FM.toModel ε π hπO hπ0).mult u j)
      = fun i => lamVec (FM.σ (((u : 𝒪) : K))) i * (lamVec (FM.σ π) i) ^ j := by
  show lamVec (FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j) = _
  rw [lamVec_mulC]
  funext i
  rw [lamVec_powC]

section Arithmetic

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-- Two of the three eigen-moduli coincide: the complex place and its conjugate. -/
theorem lamAbs_one_eq_two (a : Pt) : lamAbs a 1 = lamAbs a 2 := by
  have h : Complex.normSq (lamVec a 1) = Complex.normSq (lamVec a 2) := by
    simp only [lamVec_one, lamVec_two, Complex.normSq_apply]
    ring
  simp only [lamAbs]
  rw [Complex.norm_def, Complex.norm_def, h]

/-- The eigen-moduli are nonnegative. -/
theorem lamAbs_nonneg (a : Pt) (i : Fin 3) : 0 ≤ lamAbs a i := norm_nonneg _

/-- **`|Nm π| = p > 1` in eigen-multiplier form**: the product of the three
archimedean absolute values of the prime multiplier is `p`. -/
theorem prod_lamAbs_prime (FM : FieldModel K 𝒪 Nm) (π : K) (p : ℕ)
    (hπN : Nm π = (p : ℚ≥0)) : (∏ i, lamAbs (FM.σ π) i) = (p : ℝ) := by
  rw [prod_lamAbs, FM.normR_abs, hπN]
  push_cast
  ring

/-- **`|Nm ε| = 1` in eigen-multiplier form**: the product of the three
archimedean absolute values of a unit multiplier is `1`. -/
theorem prod_lamAbs_unit (FM : FieldModel K 𝒪 Nm) (u : 𝒪ˣ) :
    (∏ i, lamAbs (FM.σ (((u : 𝒪) : K))) i) = 1 := by
  rw [prod_lamAbs, FM.abs_normR_unit]

/-- The eigen-multiplier vector of a family element: pointwise `τ(u π^j)`. -/
theorem lamAbs_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (u : 𝒪ˣ) (j : ℕ) (i : Fin 3) :
    lamAbs ((FM.toModel ε π hπO hπ0).mult u j) i
      = lamAbs (FM.σ (((u : 𝒪) : K))) i * (lamAbs (FM.σ π) i) ^ j := by
  simp only [lamAbs, lamVec_mult, Pi.pow_apply, norm_mul, norm_pow]

/-- The product of the eigen-moduli of a family element is `p ^ j`. -/
theorem prod_lamAbs_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪)
    (hπ0 : π ≠ 0) (p : ℕ) (hπN : Nm π = (p : ℚ≥0)) (u : 𝒪ˣ) (j : ℕ) :
    (∏ i, lamAbs ((FM.toModel ε π hπO hπ0).mult u j) i) = (p : ℝ) ^ j := by
  rw [prod_lamAbs, abs_normR_mult FM ε π hπO hπ0 p hπN u j]

/-- **Expansion is forced somewhere**: if `j > 0` then some place has
eigen-modulus `> 1`, because the product of the three moduli is `p ^ j > 1`.
This is the arithmetic input behind hypothesis (B2) for the prime direction. -/
theorem exists_one_lt_lamAbs_mult (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (u : 𝒪ˣ) (j : ℕ) (hj : 0 < j) :
    ∃ i : Fin 3, 1 < lamAbs ((FM.toModel ε π hπO hπ0).mult u j) i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hpos : (0 : ℝ) < (p : ℝ) ^ j := by
    have : (0 : ℝ) < p := by exact_mod_cast lt_trans Nat.zero_lt_one hp
    positivity
  have hle : (∏ i, lamAbs ((FM.toModel ε π hπO hπ0).mult u j) i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => lamAbs_nonneg _ i) (fun i _ => h i)
  rw [prod_lamAbs_mult FM ε π hπO hπ0 p hπN u j] at hle
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hgt : (1 : ℝ) < (p : ℝ) ^ j := one_lt_pow₀ h1 (by omega)
  linarith

/-! ### The eigen-multiplier vector determines the field element -/

/-- The three eigen-multipliers of `σ a` determine `a`: the characters separate
points of the field.  This is what lets the multiplier vector of the family be a
faithful model of the field element. -/
theorem lamVec_σ_injective (FM : FieldModel K 𝒪 Nm) {a b : K}
    (h : ∀ i, lamVec (FM.σ a) i = lamVec (FM.σ b) i) : a = b := by
  have h0 : FM.σ a 0 = FM.σ b 0 := by
    have := congrArg Complex.re (h 0); simpa using this
  have h1 : FM.σ a 1 = FM.σ b 1 := by
    have := congrArg Complex.re (h 1); simpa using this
  have h2 : FM.σ a 2 = FM.σ b 2 := by
    have := congrArg Complex.im (h 1); simpa using this
  have hEq : FM.σ a = FM.σ b := by
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hzero : FM.σ (a - b) = 0 := by rw [FM.σ_sub, hEq, sub_self]
  exact sub_eq_zero.mp (FM.σ_eq_zero hzero)

/-- **Multiplicative independence transfers from the field to the eigen-multiplier
vector**: if no eigen-place separates a nontrivial power relation on `a, b`, then
the relation already holds in the field.  Combined with the corrected (B3) for
`(ε, π)` this is the independence input of the cone/radial arguments. -/
theorem lamVec_pow_eq_imp_pow_eq (FM : FieldModel K 𝒪 Nm) {a b : K} {m n : ℕ}
    (h : ∀ i, (lamVec (FM.σ a) i) ^ m = (lamVec (FM.σ b) i) ^ n) : a ^ m = b ^ n := by
  have h' : ∀ i, lamVec (FM.σ (a ^ m)) i = lamVec (FM.σ (b ^ n)) i := by
    intro i
    rw [FM.σ_mul_pow, FM.σ_mul_pow, lamVec_powC, lamVec_powC]
    exact h i
  exact lamVec_σ_injective FM h'

end Arithmetic

/-! ### The characteristic polynomial and completeness of the eigenvalue list -/

/-- The characteristic polynomial of the block matrix `diag(x, [y,-z;z,y])`. -/
theorem charpoly_block (x y z : ℂ) :
    (!![x, 0, 0; 0, y, -z; 0, z, y] : Matrix (Fin 3) (Fin 3) ℂ).charpoly
      = (X - C x) * (X - C (y + Complex.I * z)) * (X - C (y - Complex.I * z)) := by
  rw [Matrix.charpoly]
  simp only [Matrix.charmatrix, Matrix.det_fin_three, Matrix.of_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply]
  simp
  ring_nf
  rw [show (C Complex.I : ℂ[X]) ^ 2 = -1 by rw [← map_pow, Complex.I_sq, map_neg, map_one]]
  ring

theorem re_add_I_mul_im (a : Pt) :
    (⟨a 1, a 2⟩ : ℂ) = (a 1 : ℂ) + Complex.I * (a 2 : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem re_sub_I_mul_im (a : Pt) :
    (⟨a 1, -a 2⟩ : ℂ) = (a 1 : ℂ) - Complex.I * (a 2 : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- **The characteristic polynomial of the complexified model** is the product over
the three places: `∏ τ (X - τ(a))`. -/
theorem ptMulC_charpoly (a : Pt) :
    LinearMap.charpoly (ptMulC a) = ∏ i, (X - C (lamVec a i)) := by
  rw [ptMulC, Matrix.charpoly_toLin', charpoly_block]
  simp only [Fin.prod_univ_three, lamVec_zero, lamVec_one, lamVec_two, re_add_I_mul_im,
    re_sub_I_mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mk.injEq]
  rfl

/-- **The eigenvalue list is complete.**  Every eigenvalue of the complexified
multiplication map on `ℂ ⊗[ℝ] Pt` is one of the three place-multipliers
`a 0`, `a 1 + i a 2`, `a 1 - i a 2`. -/
theorem baseChange_eigenvalue_mem (a : Pt) {z : ℂ ⊗[ℝ] Pt} {μ : ℂ} (hz : z ≠ 0)
    (h : (ptMul a).baseChange ℂ z = μ • z) : ∃ i, μ = lamVec a i := by
  have heig : Module.End.HasEigenvalue ((ptMul a).baseChange ℂ) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h, hz⟩
  have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mp heig
  rw [← LinearEquiv.charpoly_conj cEquiv ((ptMul a).baseChange ℂ), conj_baseChange_ptMul,
    ptMulC_charpoly, Polynomial.IsRoot, Polynomial.eval_prod] at hroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  exact ⟨i, sub_eq_zero.mp (by simpa using hi)⟩

/-! ### The family on the model: `linFam` is `ptMul`, and the family is diagonal -/

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The invertible linear map underlying the family is multiplication by the
modulus element, as a linear map. -/
lemma UnitPrimeModel.linFam_eq_ptMul (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (D.linFam i : Pt →ₗ[ℝ] Pt) = ptMul (D.mult i.1 i.2) := rfl

/-- **The actual unit–prime family is diagonal in the eigenbasis**, with
eigenvalue `τ(u π^j)` at the place `τ`. -/
theorem UnitPrimeModel.linFam_eigen (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (k : Fin 3) :
    LinearMap.baseChange ℂ (D.linFam i : Pt →ₗ[ℝ] Pt) (eigVec k)
      = lamVec (D.mult i.1 i.2) k • eigVec k := by
  rw [D.linFam_eq_ptMul]
  exact baseChange_ptMul_eigen (D.mult i.1 i.2) k

/-- The eigen-multiplier vector of the family element `i = (u,j)` at the place `τ`
is `τ(u) τ(π)^j`. -/
theorem UnitPrimeModel.linFam_eigenvalue (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    (k : Fin 3) : lamVec (D.mult i.1 i.2) k = lamVec (D.unit_image i.1) k *
      (lamVec (D.prime_image D.prime) k) ^ i.2 := by
  show lamVec (D.unit_image i.1 ⋆ powC (D.prime_image D.prime) i.2) k = _
  rw [lamVec_mulC]
  simp only [Pi.mul_apply, lamVec_powC, Pi.pow_apply]

/-- The moduli of the family multipliers: at the place `τ` the modulus is
`τ(u) τ(π)^j`. -/
theorem UnitPrimeModel.lamAbs_family (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (k : Fin 3) :
    lamAbs (D.mult i.1 i.2) k
      = lamAbs (D.unit_image i.1) k * (lamAbs (D.prime_image D.prime) k) ^ i.2 := by
  simp only [lamAbs, UnitPrimeModel.linFam_eigenvalue, norm_mul, norm_pow]

/-! ### What a real eigenbasis can see: the single real eigenline

For a multiplier with non-real complex coordinate `a 1 + i a 2` the real map
`ptMul a` has exactly one real eigenline, the coordinate axis `{x : x 1 = x 2 = 0}`.
Consequently the family cannot be carried by a real linear change of coordinates
into a diagonal model `diag lam` on three real coordinates: the abstract diagonal
model `ι → ℝ` of `BerendSec4`/`BerendModulus` is *not* conjugate to the concrete
unit–prime model unless every family multiplier has real complex coordinate.
The real content that *is* available is the block form of §2 (a real coordinate and
one complex coordinate) plus the eigen-model over `ℂ`. -/

/-- The real coordinate axis is always a real eigenline (eigenvalue `a 0`). -/
theorem ptMul_single_zero (a : Pt) : ptMul a (Pi.single 0 1) = a 0 • Pi.single 0 1 := by
  funext j
  fin_cases j <;> simp [ptMul_apply]

/-- **The only real eigenline, when the complex coordinate is non-real.**  If
`a 2 ≠ 0` then every real eigenvector of `ptMul a` lies on the real axis. -/
theorem ptMul_real_eigenvector_axis (a : Pt) (ha : a 2 ≠ 0) {x : Pt} {r : ℝ}
    (h : ptMul a x = r • x) : x 1 = 0 ∧ x 2 = 0 := by
  have h1 : a 1 * x 1 - a 2 * x 2 = r * x 1 := by
    have := congrArg (fun y : Pt => y 1) h
    simpa using this
  have h2 : a 1 * x 2 + a 2 * x 1 = r * x 2 := by
    have := congrArg (fun y : Pt => y 2) h
    simpa using this
  have e1 : (a 1 - r) * x 1 = a 2 * x 2 := by
    have h' : a 1 * x 1 - r * x 1 = a 2 * x 2 := by linarith
    rw [sub_mul]; exact h'
  have e2 : (a 1 - r) * x 2 = -a 2 * x 1 := by
    have h' : a 1 * x 2 - r * x 2 = -a 2 * x 1 := by linarith
    rw [sub_mul]; exact h'
  have key : (a 1 - r) * (x 1 ^ 2 + x 2 ^ 2) = 0 := by
    have expand : (a 1 - r) * (x 1 ^ 2 + x 2 ^ 2)
        = ((a 1 - r) * x 1) * x 1 + ((a 1 - r) * x 2) * x 2 := by ring
    rw [expand, e1, e2]
    ring
  rcases eq_or_ne (a 1 - r) 0 with hc | hc
  · have har : a 1 = r := by linarith
    have hx2 : x 2 = 0 := by
      have h' : a 2 * x 2 = 0 := by rw [har] at h1; linarith
      exact (mul_eq_zero.mp h').resolve_left ha
    have hx1 : x 1 = 0 := by
      have h' : a 2 * x 1 = 0 := by rw [har] at h2; linarith
      exact (mul_eq_zero.mp h').resolve_left ha
    exact ⟨hx1, hx2⟩
  · have hsum : x 1 ^ 2 + x 2 ^ 2 = 0 := (mul_eq_zero.mp key).resolve_left hc
    constructor <;> nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]

/-! ### The radial multiplier vectors are logarithmically independent

The two *real* radial coordinates of the model are `x 0` and `normC x = |z|²`.  Both
family elements `μ_ε` and `μ_π` scale them by positive factors, and the
trace-norm relations say that the *products* of the two factors are `|Nm ε| = 1`
and `|Nm π| = p`.  Consequently the two radial multiplier vectors are linearly
independent in log coordinates as soon as `|ε 0| ≠ 1`: the two vectors lie on the
parallel lines `{a + b = 0}` and `{a + b = log p}`, and `|ε 0| ≠ 1` puts the first
one off the direction `(1,-1)`.  This is the density input that a cone/radial-flow
argument on the radial coordinates consumes. -/

/-- The product of the two radial coordinates of `a` is `|normR a|`. -/
theorem abs_fst_mul_normC (a : Pt) : |a 0| * normC a = |normR a| := by
  rw [normR_eq_mul_normC, abs_mul, abs_of_nonneg (normC_nonneg a)]

/-- **Logarithmic independence of two radial multiplier vectors** with distinct
radial products `1` and `p > 1`, the first one not of the shape `(1,1)`. -/
theorem radial_log_indep {u0 u2 v0 v2 p : ℝ} (hu0 : 0 < u0) (hu2 : 0 < u2)
    (hv0 : 0 < v0) (hv2 : 0 < v2) (hu : u0 * u2 = 1) (hv : v0 * v2 = p)
    (hp1 : 1 < p) (hu1 : u0 ≠ 1) :
    ∀ m n : ℤ, m * Real.log u0 = n * Real.log v0 →
      m * Real.log u2 = n * Real.log v2 → m = 0 ∧ n = 0 := by
  intro m n h1 h2
  have hlog1 : Real.log u0 + Real.log u2 = 0 := by
    rw [← Real.log_mul hu0.ne' hu2.ne', hu, Real.log_one]
  have hlog2 : Real.log v0 + Real.log v2 = Real.log p := by
    rw [← Real.log_mul hv0.ne' hv2.ne', hv]
  have hsum : (m : ℝ) * 0 = (n : ℝ) * Real.log p := by
    have h : (m : ℝ) * (Real.log u0 + Real.log u2)
        = (n : ℝ) * (Real.log v0 + Real.log v2) := by
      rw [mul_add, mul_add, h1, h2]
    rwa [hlog1, hlog2] at h
  rw [mul_zero] at hsum
  have hlogp : Real.log p ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have hn : n = 0 := by
    rcases mul_eq_zero.mp hsum.symm with h | h
    · exact_mod_cast h
    · exact absurd h hlogp
  have hlogu : Real.log u0 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hu0 hu1
  have hm : m = 0 := by
    have h : (m : ℝ) * Real.log u0 = 0 := by rw [h1, hn]; simp
    rcases mul_eq_zero.mp h with h' | h'
    · exact_mod_cast h'
    · exact absurd h' hlogu
  exact ⟨hm, hn⟩

/-- **The two radial multiplier vectors of `(μ_ε, μ_π)` are logarithmically
independent.**  Hypotheses: `Nm π = p > 1`, `|Nm ε| = 1` (both used through the
`FieldModel` norm compatibility), and `|ε 0| ≠ 1` at the real place.  In the
intended arithmetic model the last condition follows from `hεpow`: `|ε 0| = 1`
together with `|Nm ε| = 1` forces the real conjugate of `ε` to be `±1`, hence
`ε = ±1` because the minimal polynomial of `ε` then has degree one; that argument
needs `[Algebra ℚ K]` and is not formalised here, so the condition is carried
explicitly (this is the only arithmetic hypothesis of this module that is not
already an input of the project). -/
theorem radial_log_indep_unit_prime (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < p) (hπN : Nm π = (p : ℚ≥0))
    (hε1 : |(FM.σ (((ε : 𝒪) : K))) 0| ≠ 1) :
    ∀ m n : ℤ,
      m * Real.log |(FM.σ (((ε : 𝒪) : K))) 0| = n * Real.log |(FM.σ π) 0| →
      m * Real.log (normC (FM.σ (((ε : 𝒪) : K)))) = n * Real.log (normC (FM.σ π)) →
      m = 0 ∧ n = 0 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hu : |(FM.σ (((ε : 𝒪) : K))) 0| * normC (FM.σ (((ε : 𝒪) : K))) = 1 := by
    rw [abs_fst_mul_normC, FM.abs_normR_unit ε]
  have hv : |(FM.σ π) 0| * normC (FM.σ π) = (p : ℝ) := by
    rw [abs_fst_mul_normC, FM.normR_abs, hπN]
    push_cast
    ring
  have hu0 : 0 < |(FM.σ (((ε : 𝒪) : K))) 0| :=
    abs_pos.mpr fun h0 => by rw [h0, abs_zero, zero_mul] at hu; linarith
  have hu2 : 0 < normC (FM.σ (((ε : 𝒪) : K))) := by
    rcases lt_trichotomy (normC (FM.σ (((ε : 𝒪) : K)))) 0 with h | h | h
    · exact absurd h (not_lt.mpr (normC_nonneg _))
    · rw [h, mul_zero] at hu; linarith
    · exact h
  have hv0 : 0 < |(FM.σ π) 0| :=
    abs_pos.mpr fun h0 => by rw [h0, abs_zero, zero_mul] at hv; linarith
  have hv2 : 0 < normC (FM.σ π) := by
    rcases lt_trichotomy (normC (FM.σ π)) 0 with h | h | h
    · exact absurd h (not_lt.mpr (normC_nonneg _))
    · rw [h, mul_zero] at hv; linarith
    · exact h
  exact radial_log_indep hu0 hu2 hv0 hv2 hu hv hpR hε1

end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.ptMul_mul
#print axioms CubicTwoStage.ptMul_det
#print axioms CubicTwoStage.lamVec_mulC
#print axioms CubicTwoStage.prod_lamVec
#print axioms CubicTwoStage.baseChange_ptMul_eigen
#print axioms CubicTwoStage.ptMulC_charpoly
#print axioms CubicTwoStage.baseChange_eigenvalue_mem
#print axioms CubicTwoStage.abs_normR_mult
#print axioms CubicTwoStage.abs_det_mult
#print axioms CubicTwoStage.prod_lamAbs_mult
#print axioms CubicTwoStage.exists_one_lt_lamAbs_mult
#print axioms CubicTwoStage.lamVec_σ_injective
#print axioms CubicTwoStage.lamVec_pow_eq_imp_pow_eq
#print axioms CubicTwoStage.UnitPrimeModel.linFam_eigen
#print axioms CubicTwoStage.ptMul_real_eigenvector_axis
#print axioms CubicTwoStage.radial_log_indep
#print axioms CubicTwoStage.radial_log_indep_unit_prime
