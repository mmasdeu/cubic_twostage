/-
# Berend §3 algebraic core: base change ℤ → ℚ, base-change dictionary, A2

Implementation of packages **A1** and **A2** of `BEREND_PROOF_PLAN.md`
("integral-to-field base change and invariant subspaces").

Contents:

* §1 field-level algebra: irreducible `charpoly` ⟹ no proper invariant subspace,
  no eigenvalue, no fixed vector, `f - 1` injective;
* §2 base change: `charpoly (g.baseChange ℚ) = (charpoly g).map (Int.castRingHom ℚ)`
  (`LinearMap.charpoly_baseChange`) and Gauss's lemma
  (`Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`), so Berend's
  (B1) for the *integral* endomorphism of the lattice gives irreducibility over `ℚ`;
* §3 the base-change dictionary `ℚ ⊗[ℤ] M ≃ₗ[ℚ] span_ℚ M` (`q ⊗ m ↦ q • m`) and
  `charpoly (ratAct M f hf) = (charpoly (intAct M f hf)).map (Int.castRingHom ℚ)`,
  which turns the abstract dichotomy into a statement about `f`-invariant
  `ℚ`-subspaces of `Pt = Fin 3 → ℝ`;
* §4 **A2**: under (B1) the only invariant `ℚ`-subspaces of `span_ℚ σ(𝒪)` are
  `⊥` and `⊤`;
* §5 the same, specialised to `UnitPrimeModel`;
* §6 a note: irreducibility does *not* survive base change to `ℂ` (a cubic
  irreducible over `ℚ` splits there); only the characteristic polynomial does.

No `sorry`; only `propext`, `Classical.choice`, `Quot.sound`.  The axiom
`berend_multi_invariance` is neither imported nor used (this module imports only
`CubicTwoStage.Basic`).
-/
import CubicTwoStage.Basic
import CubicTwoStage.Setting
set_option linter.style.haveILetI false

namespace CubicTwoStage

open Polynomial Module

/-! ## 1. Field-level algebra

These are the two facts every later stage consumes from (B1): an irreducible
characteristic polynomial makes the ambient space a *simple* module over
`K[X]` (no proper invariant subspace), and it forbids invariant lines, fixed
vectors, and gives invertibility of `f - 1`. -/

section FieldAlg

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- **Compatibility of polynomial evaluation with restriction.**  For an
`f`-invariant submodule `W`, the inclusion `W → V` intertwines the action of any
polynomial in `f|W` with the action of the same polynomial in `f`. -/
theorem subtype_comp_aeval_restrict {f : V →ₗ[𝕜] V} {W : Submodule 𝕜 V}
    (hW : ∀ x ∈ W, f x ∈ W) (q : 𝕜[X]) :
    W.subtype.comp (aeval (f.restrict hW) q) = (aeval f q).comp W.subtype := by
  have hsub : W.subtype.comp (f.restrict hW) = f.comp W.subtype := by
    ext x
    rfl
  have hpow : ∀ n : ℕ,
      W.subtype.comp ((f.restrict hW) ^ n) = (f ^ n).comp W.subtype := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
        LinearMap.comp_id, LinearMap.id_comp]
    | succ n ih =>
        rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
          ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hsub,
          ← LinearMap.comp_assoc]
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
        LinearMap.comp_smul, LinearMap.smul_comp, hpow n]

/-- **A polynomial killing `f` kills its restriction to an invariant
submodule.** -/
theorem aeval_restrict_eq_zero {f : V →ₗ[𝕜] V} {W : Submodule 𝕜 V}
    (hW : ∀ x ∈ W, f x ∈ W) {p : 𝕜[X]} (hp : aeval f p = 0) :
    aeval (f.restrict hW) p = 0 := by
  have key := subtype_comp_aeval_restrict hW p
  rw [hp, LinearMap.zero_comp] at key
  ext x
  have := LinearMap.congr_fun key x
  simpa using this

end FieldAlg

section FieldIrreducible

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Irreducible characteristic polynomial ⇒ no proper invariant subspace.**
If `charpoly f` is irreducible then the only subspaces carried into themselves
by `f` are `⊥` and `⊤`: `V` is a simple module over `𝕜[X]`. -/
theorem submodule_eq_bot_or_top_of_irreducible_charpoly (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f)) (W : Submodule 𝕜 V)
    (hW : ∀ x ∈ W, f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  rcases eq_bot_or_bot_lt W with h | h
  · exact Or.inl h
  right
  obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_of_gt h)
  have hnt : Nontrivial W :=
    ⟨⟨w, hwmem⟩, 0, fun hc => hwne (by simpa using congrArg Subtype.val hc)⟩
  haveI := hnt
  -- the characteristic polynomial of `f` is the minimal polynomial of `f|W`
  have hzero : aeval (f.restrict hW) (LinearMap.charpoly f) = 0 :=
    aeval_restrict_eq_zero hW (LinearMap.aeval_self_charpoly f)
  have hmin : LinearMap.charpoly f = minpoly 𝕜 (f.restrict hW) :=
    minpoly.eq_of_irreducible_of_monic hirr hzero (LinearMap.charpoly_monic f)
  -- hence it annihilates `f|W`, so it has degree at most `dim W`
  have hdvd : minpoly 𝕜 (f.restrict hW) ∣ LinearMap.charpoly (f.restrict hW) :=
    LinearMap.minpoly_dvd_charpoly _
  have hdeg : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 W := by
    have hle := Polynomial.natDegree_le_of_dvd hdvd
      (LinearMap.charpoly_monic (f.restrict hW)).ne_zero
    rwa [← hmin, LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hle
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) hdeg)

/-- **Berend's (B1) ⇒ no proper invariant subspace.** -/
theorem submodule_eq_bot_or_top_of_b1 (f : V →ₗ[𝕜] V)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (f ^ n)))
    (W : Submodule 𝕜 V) (hW : ∀ x ∈ W, f x ∈ W) : W = ⊥ ∨ W = ⊤ :=
  submodule_eq_bot_or_top_of_irreducible_charpoly f (by simpa using hB1 1 (by norm_num)) W hW

/-- (B1) forbids eigenvalues: if the characteristic polynomial is irreducible
and its degree is not `1`, then no `μ` is an eigenvalue. -/
theorem not_hasEigenvalue_of_irreducible_charpoly (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f)) (hdeg : (LinearMap.charpoly f).natDegree ≠ 1)
    (μ : 𝕜) : ¬ Module.End.HasEigenvalue f μ := by
  intro hμ
  have hroot : (LinearMap.charpoly f).IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mp hμ
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hchar : LinearMap.charpoly f ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hchar hq
  have hnd : (LinearMap.charpoly f).natDegree = 1 + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C μ).ne_zero hqne,
      Polynomial.natDegree_X_sub_C]
  rcases hirr.isUnit_or_isUnit hq with hunit | hunit
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; norm_num) hunit
  · rw [Polynomial.natDegree_eq_zero_of_isUnit hunit, add_zero] at hnd
    exact hdeg hnd

/-- (B1) forbids invariant lines: `f x = μ • x` forces `x = 0`. -/
theorem eq_zero_of_invariant_line_of_irreducible_charpoly (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f))
    (hdeg : (LinearMap.charpoly f).natDegree ≠ 1)
    {μ : 𝕜} {x : V} (hx : f x = μ • x) : x = 0 := by
  by_contra hne
  refine not_hasEigenvalue_of_irreducible_charpoly f hirr hdeg μ
    (Module.End.hasEigenvalue_iff.mpr fun hbot => ?_)
  have hmem : x ∈ Module.End.eigenspace f μ := Module.End.mem_eigenspace_iff.mpr hx
  rw [hbot] at hmem
  exact hne (by simpa using hmem)

/-- Consequently (B1) forbids fixed vectors. -/
theorem eq_zero_of_fixed_of_irreducible_charpoly (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f))
    (hdeg : (LinearMap.charpoly f).natDegree ≠ 1)
    {x : V} (hx : f x = x) : x = 0 :=
  eq_zero_of_invariant_line_of_irreducible_charpoly f hirr hdeg (μ := 1) (x := x)
    (by simpa using hx)

/-- `f - 1` has trivial kernel. -/
theorem eq_zero_of_sub_one_apply_eq_zero (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f))
    (hdeg : (LinearMap.charpoly f).natDegree ≠ 1)
    {x : V} (hx : (f - (1 : V →ₗ[𝕜] V)) x = 0) : x = 0 := by
  have h' : f x - x = 0 := by simpa using hx
  exact eq_zero_of_fixed_of_irreducible_charpoly f hirr hdeg (sub_eq_zero.mp h')

/-- Hence `f - 1` is injective, so invertible in finite dimension. -/
theorem injective_sub_one_of_irreducible_charpoly (f : V →ₗ[𝕜] V)
    (hirr : Irreducible (LinearMap.charpoly f))
    (hdeg : (LinearMap.charpoly f).natDegree ≠ 1) :
    Function.Injective (f - (1 : V →ₗ[𝕜] V)) := by
  intro x y hxy
  have h : (f - (1 : V →ₗ[𝕜] V)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_sub_one_apply_eq_zero f hirr hdeg h)

end FieldIrreducible

/-! ## 2. Base change ℤ → ℚ (A1)

`LinearMap.charpoly_baseChange` gives the characteristic-polynomial transport
for free; Gauss's lemma gives the irreducibility transport.  Together they turn
Berend's (B1), stated for the *integral* lattice endomorphism, into the
hypothesis `Irreducible (charpoly (f.baseChange ℚ))` that §1 consumes. -/

section BaseChangeInt

variable {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- **Characteristic polynomial of the ℚ-base-change.** -/
theorem charpoly_baseChange_rat (g : M →ₗ[ℤ] M) :
    (g.baseChange ℚ).charpoly = g.charpoly.map (Int.castRingHom ℚ) :=
  LinearMap.charpoly_baseChange g ℚ

/-- **Gauss's lemma, in the form used by Berend's §3.**  A monic integer
polynomial is irreducible over `ℤ` iff its image in `ℚ[X]` is irreducible. -/
theorem irreducible_map_rat_iff {p : ℤ[X]} (hp : p.Monic) :
    Irreducible (p.map (Int.castRingHom ℚ)) ↔ Irreducible p :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp.isPrimitive).symm

/-- A `ℤ`-polynomial with irreducible image over `ℚ` is itself irreducible. -/
theorem irreducible_of_irreducible_map_rat {p : ℤ[X]} (hp : p.Monic)
    (h : Irreducible (p.map (Int.castRingHom ℚ))) : Irreducible p :=
  (irreducible_map_rat_iff hp).mp h

/-- **A1, first form.**  Irreducibility of the integral characteristic
polynomial transfers to the `ℚ`-base-changed endomorphism. -/
theorem irreducible_charpoly_baseChange_of_irreducible (g : M →ₗ[ℤ] M)
    (hirr : Irreducible g.charpoly) : Irreducible (g.baseChange ℚ).charpoly := by
  rw [charpoly_baseChange_rat]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (LinearMap.charpoly_monic g).isPrimitive).mp hirr

/-- **A1, the form consumed later.**  Berend's (B1) for the integral
endomorphism implies irreducibility of the characteristic polynomial of the
`ℚ`-base-change (take `n = 1`). -/
theorem irreducible_charpoly_baseChange_of_B1 (g : M →ₗ[ℤ] M)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (g ^ n))) :
    Irreducible (g.baseChange ℚ).charpoly :=
  irreducible_charpoly_baseChange_of_irreducible g (by simpa using hB1 1 (by norm_num))

end BaseChangeInt/-! ## 3. The geometric bridge `ℚ ⊗[ℤ] M ≃ span_ℚ M` on `Pt = Fin 3 → ℝ` -/

/-- The `ℚ`-span of an integral lattice `M ≤ Pt`, i.e. the underlying `ℚ`-vector
space of Berend's "rational structure". -/
noncomputable def ratSpan (M : Submodule ℤ Pt) : Submodule ℚ Pt :=
  Submodule.span ℚ (M : Set Pt)

/-- **The integral restriction** of an `ℝ`-linear endomorphism of `Pt` that
preserves the lattice `M`.  This is Berend's `σ` on the lattice; it is
definitionally the same map as `latticeAct`/`UnitPrimeModel.lact` in
`CubicTwoStage/Berend.lean`. -/
noncomputable def intAct (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    M →ₗ[ℤ] M :=
  LinearMap.restrict (p := M) (q := M) (LinearMap.restrictScalars ℤ f) hf

@[simp] theorem intAct_apply_coe (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (x : M) : ((intAct M f hf x : M) : Pt) = f x := rfl

/-- `f` preserves the `ℚ`-span of the lattice. -/
theorem map_mem_ratSpan (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    ∀ x ∈ ratSpan M, f x ∈ ratSpan M := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (hf y hy)
  | zero => simp
  | add y z _ _ ihy ihz => simpa [map_add] using Submodule.add_mem (ratSpan M) ihy ihz
  | smul a y _ ihy =>
      have h : f (a • y) = a • f y := map_smul (f.restrictScalars ℚ) a y
      rw [h]
      exact Submodule.smul_mem _ a ihy

/-- **`f` restricted to the `ℚ`-span of the lattice**, as a `ℚ`-linear map. -/
noncomputable def ratAct (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    ratSpan M →ₗ[ℚ] ratSpan M :=
  LinearMap.restrict (p := ratSpan M) (q := ratSpan M) (LinearMap.restrictScalars ℚ f)
    (map_mem_ratSpan M f hf)

@[simp] theorem ratAct_apply_coe (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (x : ratSpan M) : ((ratAct M f hf x : ratSpan M) : Pt) = f x := rfl

/-- The set underlying the lattice inside its own `ℚ`-span. -/
def latticeInRatSpan (M : Submodule ℤ Pt) : Set (ratSpan M) := {x | (x : Pt) ∈ M}

/-- The universal bilinear map `ℚ × M → span_ℚ M`, `(q, m) ↦ q • m`, linear over
`ℚ` in the first and over `ℤ` in the second variable. -/
noncomputable def smulIntoRatSpan (M : Submodule ℤ Pt) : ℚ →ₗ[ℚ] M →ₗ[ℤ] ratSpan M where
  toFun q :=
    AddMonoidHom.toIntLinearMap
      { toFun := fun m => ⟨q • (m : Pt), Submodule.smul_mem _ q (Submodule.subset_span m.2)⟩
        map_zero' := by
          refine Subtype.ext ?_
          simp
        map_add' := by
          intro m n
          refine Subtype.ext ?_
          simp }
  map_add' := by
    intro q q'
    refine LinearMap.ext fun m => ?_
    refine Subtype.ext ?_
    exact add_smul q q' (m : Pt)
  map_smul' := by
    intro q' q
    refine LinearMap.ext fun m => ?_
    refine Subtype.ext ?_
    exact mul_smul q' q (m : Pt)

/-- **The base-change dictionary** `ℚ ⊗[ℤ] M →ₗ[ℚ] span_ℚ M`, `q ⊗ m ↦ q • m`. -/
noncomputable def tensorToRatSpan (M : Submodule ℤ Pt) : TensorProduct ℤ ℚ M →ₗ[ℚ] ratSpan M :=
  TensorProduct.AlgebraTensorModule.lift (smulIntoRatSpan M)

@[simp] theorem tensorToRatSpan_tmul (M : Submodule ℤ Pt) (q : ℚ) (m : M) :
    tensorToRatSpan M (q ⊗ₜ[ℤ] m) =
      ⟨q • (m : Pt), Submodule.smul_mem _ q (Submodule.subset_span m.2)⟩ :=
  rfl

/-- The lattice, viewed inside its `ℚ`-span, spans it over `ℚ`. -/
theorem span_latticeInRatSpan (M : Submodule ℤ Pt) :
    Submodule.span ℚ (latticeInRatSpan M) = ⊤ := by
  have hmap : Submodule.map (Submodule.subtype (ratSpan M))
      (Submodule.span ℚ (latticeInRatSpan M)) = ratSpan M := by
    rw [Submodule.map_span]
    have himg : (Submodule.subtype (ratSpan M)) '' latticeInRatSpan M = (M : Set Pt) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
    rw [himg, ratSpan]
  have htop : Submodule.map (Submodule.subtype (ratSpan M)) (⊤ : Submodule ℚ (ratSpan M)) =
      ratSpan M := by
    rw [Submodule.map_top, Submodule.range_subtype]
  have hinj := Submodule.map_injective_of_injective (Submodule.subtype_injective (ratSpan M))
  exact hinj (by rw [hmap, htop])

/-- **Surjectivity of the base-change dictionary.** -/
theorem tensorToRatSpan_surjective (M : Submodule ℤ Pt) :
    Function.Surjective (tensorToRatSpan M) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hspan := span_latticeInRatSpan M
  rw [← hspan]
  refine Submodule.span_le.mpr ?_
  intro x hx
  refine ⟨1 ⊗ₜ[ℤ] (⟨x, hx⟩ : M), ?_⟩
  rw [tensorToRatSpan_tmul]
  refine Subtype.ext ?_
  simp

/-- The `ℚ`-base change of a free, finitely generated `ℤ`-module is finite over `ℚ`. -/
instance instFiniteTensorRat (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.Finite ℚ (TensorProduct ℤ ℚ M) :=
  Finite.of_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ)

/-- The `ℚ`-span of a free, finitely generated lattice in `Pt` is finite over `ℚ`
(it is a quotient of `ℚ ⊗[ℤ] M`). -/
instance instFiniteRatSpan (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.Finite ℚ (ratSpan M) :=
  Module.Finite.of_surjective (σ := RingHom.id ℚ) (M := TensorProduct ℤ ℚ M) (P := ratSpan M)
    (tensorToRatSpan M) (tensorToRatSpan_surjective M)

/-- **Kernel of the base-change dictionary**, from the `ℚ`-linear independence of
a `ℤ`-basis of the lattice inside `Pt`. -/
theorem tensorToRatSpan_eq_zero (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
    {z : TensorProduct ℤ ℚ M} (hz : tensorToRatSpan M z = 0) : z = 0 := by
  classical
  set b := Module.Free.chooseBasis ℤ M with hb
  -- the `ℤ`-basis of the lattice is `ℚ`-linearly independent inside `Pt`
  have hliZ : LinearIndependent ℤ (fun i => ((b i : M) : Pt)) :=
    b.linearIndependent.map' (Submodule.subtype M) (by simp)
  have hliQ : LinearIndependent ℚ (fun i => ((b i : M) : Pt)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  -- a term of the sum, computed through the dictionary
  have hterm : ∀ i : Module.Free.ChooseBasisIndex ℤ M,
      ((tensorToRatSpan M) ((b.baseChange ℚ).repr z i • (b.baseChange ℚ) i) : Pt) =
        (b.baseChange ℚ).repr z i • ((b i : M) : Pt) := by
    intro i
    rw [map_smul (tensorToRatSpan M) ((b.baseChange ℚ).repr z i) ((b.baseChange ℚ) i),
      Module.Basis.baseChange_apply, tensorToRatSpan_tmul]
    simp
  -- `Φ z = 0` forces the `ℚ`-linear combination of the basis vectors to vanish
  have hΦ : (∑ i, (tensorToRatSpan M)
      ((b.baseChange ℚ).repr z i • (b.baseChange ℚ) i)) = 0 := by
    have hsum : (∑ i, (b.baseChange ℚ).repr z i • (b.baseChange ℚ) i) = z :=
      Module.Basis.sum_repr _ z
    rw [← map_sum, hsum, hz]
  have hΦ' : (∑ i, ((tensorToRatSpan M)
      ((b.baseChange ℚ).repr z i • (b.baseChange ℚ) i) : Pt)) = 0 := by
    simpa using congrArg (Submodule.subtype (ratSpan M)) hΦ
  have h0 : (∑ i, (b.baseChange ℚ).repr z i • ((b i : M) : Pt)) = 0 := by
    calc (∑ i, (b.baseChange ℚ).repr z i • ((b i : M) : Pt))
        = ∑ i, ((tensorToRatSpan M)
            ((b.baseChange ℚ).repr z i • (b.baseChange ℚ) i) : Pt) :=
          Finset.sum_congr rfl fun i _ => (hterm i).symm
      _ = 0 := hΦ'
  -- hence all coordinates vanish, so `z = 0`
  have hc0 : ∀ i, (b.baseChange ℚ).repr z i = 0 := by
    intro i
    refine (linearIndependent_iff').mp hliQ Finset.univ
      (fun i => (b.baseChange ℚ).repr z i) ?_ i (Finset.mem_univ i)
    simpa using h0
  rw [← Module.Basis.sum_repr (b.baseChange ℚ) z]
  simp [hc0]

/-- **Injectivity of the base-change dictionary.** -/
theorem tensorToRatSpan_injective (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M] :
    Function.Injective (tensorToRatSpan M) := by
  intro x y hxy
  have h : tensorToRatSpan M (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h' : x - y = 0 := tensorToRatSpan_eq_zero M h
  exact sub_eq_zero.mp h'

/-- **The base-change dictionary**, as a `ℚ`-linear equivalence. -/
noncomputable def tensorEquivRatSpan (M : Submodule ℤ Pt) [Module.Free ℤ M]
    [Module.Finite ℤ M] : TensorProduct ℤ ℚ M ≃ₗ[ℚ] ratSpan M :=
  LinearEquiv.ofBijective (tensorToRatSpan M)
    ⟨tensorToRatSpan_injective M, tensorToRatSpan_surjective M⟩

@[simp] theorem tensorEquivRatSpan_apply (M : Submodule ℤ Pt) [Module.Free ℤ M]
    [Module.Finite ℤ M] (z : TensorProduct ℤ ℚ M) :
    tensorEquivRatSpan M z = tensorToRatSpan M z := rfl

/-- The `ℚ`-base change of the lattice endomorphism, transported by the
dictionary, is the restriction of `f` to the `ℚ`-span. -/
theorem tensorEquivRatSpan_conj_apply (M : Submodule ℤ Pt) (f : Pt →ₗ[ℝ] Pt)
    (hf : ∀ x ∈ M, f x ∈ M) (z : TensorProduct ℤ ℚ M) :
    tensorToRatSpan M ((intAct M f hf).baseChange ℚ z) =
      ratAct M f hf (tensorToRatSpan M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul q m =>
      refine Subtype.ext ?_
      have h : (f.restrictScalars ℚ) (q • (m : Pt)) = q • f (m : Pt) := map_smul _ q _
      simpa using h.symm
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Conjugacy of the base-changed lattice endomorphism with `ratAct`. -/
theorem tensorEquivRatSpan_conj (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    (tensorEquivRatSpan M).conj ((intAct M f hf).baseChange ℚ) = ratAct M f hf := by
  refine LinearMap.ext fun z => ?_
  have h1' : (tensorEquivRatSpan M) ((tensorEquivRatSpan M).symm z) = z :=
    LinearEquiv.apply_symm_apply _ z
  have h1 : (tensorToRatSpan M) ((tensorEquivRatSpan M).symm z) = z := h1'
  calc (tensorEquivRatSpan M).conj ((intAct M f hf).baseChange ℚ) z
      = (tensorToRatSpan M) ((intAct M f hf).baseChange ℚ ((tensorEquivRatSpan M).symm z)) := rfl
    _ = ratAct M f hf ((tensorToRatSpan M) ((tensorEquivRatSpan M).symm z)) :=
        tensorEquivRatSpan_conj_apply M f hf _
    _ = ratAct M f hf z := by rw [h1]

/-- **A1 in the geometric setting: the characteristic polynomial of `f` on the
`ℚ`-span of the lattice is the `ℚ`-image of the characteristic polynomial of the
integral endomorphism.** -/
theorem charpoly_ratAct (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) :
    (ratAct M f hf).charpoly = ((intAct M f hf).charpoly).map (Int.castRingHom ℚ) := by
  haveI hT : Module.Finite ℚ (TensorProduct ℤ ℚ M) :=
    Finite.of_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ)
  haveI hS : Module.Finite ℚ (ratSpan M) :=
    Module.Finite.of_surjective (σ := RingHom.id ℚ) (M := TensorProduct ℤ ℚ M)
      (P := ratSpan M) (tensorToRatSpan M) (tensorToRatSpan_surjective M)
  calc (ratAct M f hf).charpoly
      = ((tensorEquivRatSpan M).conj ((intAct M f hf).baseChange ℚ)).charpoly := by
        rw [tensorEquivRatSpan_conj M f hf]
    _ = ((intAct M f hf).baseChange ℚ).charpoly := LinearEquiv.charpoly_conj _ _
    _ = ((intAct M f hf).charpoly).map (Int.castRingHom ℚ) := charpoly_baseChange_rat _

/-- **Dimension of the `ℚ`-span**: it equals the `ℤ`-rank of the lattice. -/
theorem finrank_ratSpan (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℚ (ratSpan M) = Module.finrank ℤ M := by
  rw [← (tensorEquivRatSpan M).finrank_eq,
    Module.finrank_eq_card_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ),
    Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ M)]

/-- For a full ℤ-lattice in `Pt = ℝ³`, the `ℚ`-span has dimension `3`. -/
theorem finrank_ratSpan_of_isZLattice (M : Submodule ℤ Pt) [DiscreteTopology M]
    [IsZLattice ℝ M] : Module.finrank ℚ (ratSpan M) = Module.finrank ℝ Pt := by
  rw [finrank_ratSpan, ZLattice.rank ℝ M]

/-- **Dimension three**, the numerical form used by Berend's §3. -/
theorem finrank_ratSpan_eq_three (M : Submodule ℤ Pt) [DiscreteTopology M]
    [IsZLattice ℝ M] : Module.finrank ℚ (ratSpan M) = 3 := by
  rw [finrank_ratSpan_of_isZLattice]
  simp

/-! ## 4. A2: no proper invariant `ℚ`-subspace under Berend's (B1) -/

/-- **A2.**  If the integral lattice endomorphism satisfies Berend's (B1), then
the only `f`-invariant `ℚ`-subspaces of the `ℚ`-span of the lattice are `⊥` and
`⊤`.  This is the "no proper invariant subtorus" input of Berend's §3. -/
theorem submodule_eq_bot_or_top_of_B1_rat (M : Submodule ℤ Pt) [Module.Free ℤ M]
    [Module.Finite ℤ M] (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((intAct M f hf) ^ n)))
    (W : Submodule ℚ (ratSpan M)) (hW : ∀ x ∈ W, ratAct M f hf x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  haveI hT : Module.Finite ℚ (TensorProduct ℤ ℚ M) :=
    Finite.of_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ)
  haveI hS : Module.Finite ℚ (ratSpan M) :=
    Module.Finite.of_surjective (σ := RingHom.id ℚ) (M := TensorProduct ℤ ℚ M)
      (P := ratSpan M) (tensorToRatSpan M) (tensorToRatSpan_surjective M)
  refine submodule_eq_bot_or_top_of_irreducible_charpoly (ratAct M f hf) ?_ W hW
  rw [charpoly_ratAct M f hf]
  have h := irreducible_charpoly_baseChange_of_B1 (intAct M f hf) hB1
  rwa [charpoly_baseChange_rat] at h

/-- **A2, eigenvalue form.**  Under (B1) (in characteristic-polynomial form) the
restriction of `f` to the `ℚ`-span has no nonzero invariant line. -/
theorem eq_zero_of_invariant_line_rat (M : Submodule ℤ Pt) [Module.Free ℤ M]
    [Module.Finite ℤ M] (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)
    (hirr : Irreducible ((intAct M f hf).charpoly))
    (hdeg : ((intAct M f hf).charpoly).natDegree ≠ 1)
    {μ : ℚ} {x : ratSpan M} (hx : ratAct M f hf x = μ • x) : x = 0 := by
  haveI hT : Module.Finite ℚ (TensorProduct ℤ ℚ M) :=
    Finite.of_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ)
  haveI hS : Module.Finite ℚ (ratSpan M) :=
    Module.Finite.of_surjective (σ := RingHom.id ℚ) (M := TensorProduct ℤ ℚ M)
      (P := ratSpan M) (tensorToRatSpan M) (tensorToRatSpan_surjective M)
  have hirr' : Irreducible (LinearMap.charpoly (ratAct M f hf)) := by
    rw [charpoly_ratAct M f hf]
    have h := irreducible_charpoly_baseChange_of_irreducible (intAct M f hf) hirr
    rwa [charpoly_baseChange_rat] at h
  have hdeg' : (LinearMap.charpoly (ratAct M f hf)).natDegree ≠ 1 := by
    rw [charpoly_ratAct M f hf,
      Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) (intAct M f hf).charpoly]
    exact hdeg
  exact eq_zero_of_invariant_line_of_irreducible_charpoly (ratAct M f hf) hirr' hdeg'
    (x := x) hx

/-- **A2, fixed-point form**: under (B1), `f` has no nonzero fixed point in the
`ℚ`-span of the lattice, so `f - 1` is injective there. -/
theorem injective_sub_one_ratAct (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)
    (hirr : Irreducible ((intAct M f hf).charpoly))
    (hdeg : ((intAct M f hf).charpoly).natDegree ≠ 1) :
    Function.Injective (ratAct M f hf - (1 : ratSpan M →ₗ[ℚ] ratSpan M)) := by
  haveI hT : Module.Finite ℚ (TensorProduct ℤ ℚ M) :=
    Finite.of_basis ((Module.Free.chooseBasis ℤ M).baseChange ℚ)
  haveI hS : Module.Finite ℚ (ratSpan M) :=
    Module.Finite.of_surjective (σ := RingHom.id ℚ) (M := TensorProduct ℤ ℚ M)
      (P := ratSpan M) (tensorToRatSpan M) (tensorToRatSpan_surjective M)
  have hirr' : Irreducible (LinearMap.charpoly (ratAct M f hf)) := by
    rw [charpoly_ratAct M f hf]
    have h := irreducible_charpoly_baseChange_of_irreducible (intAct M f hf) hirr
    rwa [charpoly_baseChange_rat] at h
  have hdeg' : (LinearMap.charpoly (ratAct M f hf)).natDegree ≠ 1 := by
    rw [charpoly_ratAct M f hf,
      Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) (intAct M f hf).charpoly]
    exact hdeg
  exact injective_sub_one_of_irreducible_charpoly (ratAct M f hf) hirr' hdeg'

/-! ## 5. Specialisation to the unit–prime model of `CubicTwoStage` -/

section UnitPrimeModel

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The integral lattice endomorphism of the unit–prime model.  It is
definitionally the map called `UnitPrimeModel.lact` in
`CubicTwoStage/Berend.lean` (`latticeAct L` is the same `LinearMap.restrict` of
`f.restrictScalars ℤ`). -/
noncomputable def UnitPrimeModel.intLact (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    (AddSubgroup.toIntSubmodule L) →ₗ[ℤ] (AddSubgroup.toIntSubmodule L) :=
  intAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt) (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx)

variable (D : UnitPrimeModel L 𝒪) [DiscreteTopology (AddSubgroup.toIntSubmodule L)]

/-- (B1) in the unit–prime model gives irreducible characteristic polynomial for
the `ℚ`-base change of the selected endomorphism. -/
theorem UnitPrimeModel.exists_irreducible_charpoly_baseChange
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, Irreducible (LinearMap.charpoly ((D.intLact i).baseChange ℚ)) := by
  obtain ⟨i, hi⟩ := B1
  exact ⟨i, irreducible_charpoly_baseChange_of_B1 (D.intLact i) hi⟩

/-- (B1) in the unit–prime model gives the invariant-subspace dichotomy for the
`ℚ`-span of the lattice `σ(𝒪)`. -/
theorem UnitPrimeModel.exists_submodule_eq_bot_or_top_rat
    (B1 : ∃ i : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ i : 𝒪ˣ × ℕ, ∀ W : Submodule ℚ (ratSpan (AddSubgroup.toIntSubmodule L)),
      (∀ x ∈ W, ratAct (AddSubgroup.toIntSubmodule L) (D.linFam i : Pt →ₗ[ℝ] Pt)
        (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx) x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  obtain ⟨i, hi⟩ := B1
  exact ⟨i, fun W hW => submodule_eq_bot_or_top_of_B1_rat (AddSubgroup.toIntSubmodule L)
    (D.linFam i : Pt →ₗ[ℝ] Pt) (fun x hx => D.lattice_linFam i (g := (x : Pt)) hx) hi W hW⟩

end UnitPrimeModel

/-! ## 6. Correction of the plan's wording on "irreducibility over `ℂ`"

None of the above transports irreducibility to `ℂ`, and it must not: a cubic
irreducible over `ℚ` splits over `ℂ` into three linear factors, so
`Irreducible (charpoly (f.baseChange ℂ))` is *false* in the intended dimension-3
instance.  What survives base change to `ℂ` is only the *characteristic
polynomial* (`LinearMap.charpoly_baseChange` with `A = ℂ`), which is what §3 of
Berend's proof uses when it speaks of the three eigenvalues. -/

/-- Characteristic polynomial transport all the way to `ℂ` (no irreducibility
claim; the polynomial factors there). -/
theorem charpoly_baseChange_complex (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (g : M →ₗ[ℤ] M) :
    (g.baseChange ℂ).charpoly = g.charpoly.map (Int.castRingHom ℂ) :=
  LinearMap.charpoly_baseChange g ℂ

/-! ## 7. From (B1) to three distinct complex eigenvalues

Irreducibility itself does *not* survive base change to `ℂ` (a cubic irreducible
over `ℚ` splits into three linear factors there).  The correct statement — the
one Berend's §3 needs and the one that feeds simultaneous diagonalisation — is
that the complexified characteristic polynomial factors into three **distinct**
linear factors.  That is what is proved here, from (B1) over `ℤ`. -/

/-- **An irreducible monic cubic over `ℚ` splits over `ℂ` into three distinct
linear factors.** -/
theorem exists_distinct_roots_of_irreducible_cubic {p : ℚ[X]} (hp : p.Monic)
    (hirr : Irreducible p) (hdeg : p.natDegree = 3) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧
      p.map (algebraMap ℚ ℂ) = ∏ i, (X - C (μ i)) := by
  classical
  set P : ℂ[X] := p.map (algebraMap ℚ ℂ) with hP
  have hPmonic : P.Monic := hp.map _
  have hPdeg : P.natDegree = 3 := by
    rw [hP, Polynomial.natDegree_map, hdeg]
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hsep : P.Separable := (separable_map (algebraMap ℚ ℂ)).mpr hirr.separable
  have hnodup : P.roots.Nodup :=
    (nodup_roots_iff_of_splits hPmonic.ne_zero hsplit).mpr hsep
  have hcard : P.roots.card = 3 := by
    rw [← hsplit.natDegree_eq_card_roots, hPdeg]
  obtain ⟨a, b, c, habc⟩ : ∃ a b c : ℂ, P.roots = {a, b, c} :=
    Multiset.card_eq_three.mp hcard
  have hnodup' : ({a, b, c} : Multiset ℂ).Nodup := habc ▸ hnodup
  have hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    simp only [show ({a, b, c} : Multiset ℂ) = a ::ₘ b ::ₘ c ::ₘ 0 from rfl,
      Multiset.nodup_cons, Multiset.mem_cons, not_or] at hnodup'
    exact ⟨hnodup'.1.1, hnodup'.1.2.1, hnodup'.2.1.1⟩
  refine ⟨![a, b, c], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [hsplit.eq_prod_roots_of_monic hPmonic, habc]
    simp [Fin.prod_univ_three, mul_assoc]

/-- **From Berend's (B1) to three distinct complex eigenvalues.**  If the
integral lattice endomorphism satisfies (B1) and its characteristic polynomial
has degree three, then the characteristic polynomial of the `ℚ`-base change
splits over `ℂ` into three distinct linear factors. -/
theorem exists_distinct_roots_charpoly_of_B1 {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (g : M →ₗ[ℤ] M)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (g ^ n)))
    (hdeg : (LinearMap.charpoly g).natDegree = 3) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧
      ((g.baseChange ℚ).charpoly).map (algebraMap ℚ ℂ) = ∏ i, (X - C (μ i)) := by
  set p : ℚ[X] := (LinearMap.charpoly g).map (Int.castRingHom ℚ) with hp
  have hpmonic : p.Monic := (LinearMap.charpoly_monic g).map _
  have hpirr : Irreducible p := by
    have h := irreducible_charpoly_baseChange_of_B1 g hB1
    rwa [charpoly_baseChange_rat] at h
  have hpdeg : p.natDegree = 3 := by
    rw [hp, Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hdeg
  obtain ⟨μ, hinj, hprod⟩ := exists_distinct_roots_of_irreducible_cubic hpmonic hpirr hpdeg
  exact ⟨μ, hinj, by rw [charpoly_baseChange_rat, ← hp]; exact hprod⟩

/-- **Project form of the eigenvalue statement**: for the restriction of `f` to
the `ℚ`-span of the lattice, the complexified characteristic polynomial splits
into three distinct linear factors. -/
theorem exists_distinct_roots_charpoly_ratAct (M : Submodule ℤ Pt) [Module.Free ℤ M]
    [Module.Finite ℤ M] (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((intAct M f hf) ^ n)))
    (hdeg : (LinearMap.charpoly (intAct M f hf)).natDegree = 3) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧
      (LinearMap.charpoly (ratAct M f hf)).map (algebraMap ℚ ℂ) = ∏ i, (X - C (μ i)) := by
  obtain ⟨μ, hinj, hprod⟩ := exists_distinct_roots_charpoly_of_B1 (intAct M f hf) hB1 hdeg
  refine ⟨μ, hinj, ?_⟩
  rw [charpoly_ratAct]
  rwa [charpoly_baseChange_rat] at hprod

/-! ## 8. Plan C.1: invariant subspaces in an eigenbasis are coordinate spans

Berend §4 (stage C of the plan) works in the common eigenbasis supplied by §3
and uses: *in that basis, an invariant subspace is the span of the coordinate
subset it occupies*, and a nonzero invariant subspace contains an eigenvector.
Both are proved here for an arbitrary field (no algebraic closure needed), from
the distinctness of the eigenvalues and the Lagrange projectors
`∏_{j ≠ i} (X - μ j)/(μ i - μ j)`. -/

section CoordinateSpan

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Powers of an invariant-preserving map preserve the invariant subspace. -/
theorem pow_apply_mem {s : V →ₗ[K] V} {W : Submodule K V} (hW : ∀ x ∈ W, s x ∈ W) :
    ∀ (n : ℕ) {x : V}, x ∈ W → (s ^ n) x ∈ W := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hW _ (ih hx)

/-- A subspace invariant under `s` is invariant under every polynomial in `s`. -/
theorem aeval_mem_of_invariant {s : V →ₗ[K] V} {W : Submodule K V}
    (hW : ∀ x ∈ W, s x ∈ W) (q : K[X]) : ∀ x ∈ W, aeval s q x ∈ W := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro x hx
      simp only [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hp x hx) (hq x hx)
  | monomial n a =>
      intro x hx
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        LinearMap.smul_apply]
      exact Submodule.smul_mem _ a (pow_apply_mem hW n hx)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lagrange projector at `i` for the eigenvalue family `μ`. -/
noncomputable def lagrange (μ : ι → K) (i : ι) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, (C ((μ i - μ j)⁻¹) * (X - C (μ j)))

variable {s : V →ₗ[K] V} {b : Module.Basis ι K V} {μ : ι → K}

omit [Fintype ι] [DecidableEq ι] in
/-- One linear factor of the Lagrange projector, evaluated on an eigenvector. -/
theorem aeval_factor_apply (hb : ∀ i, s (b i) = μ i • b i) (c : K) (jj j : ι) :
    aeval s (C c * (X - C (μ jj))) (b j) = (c * (μ j - μ jj)) • b j := by
  have hX : aeval s (X - C (μ jj)) (b j) = (μ j - μ jj) • b j := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, hb j,
      ← sub_smul]
  calc aeval s (C c * (X - C (μ jj))) (b j)
      = (aeval s (C c)) (aeval s (X - C (μ jj)) (b j)) := by
        rw [map_mul, Module.End.mul_apply]
    _ = (algebraMap K (V →ₗ[K] V) c) ((μ j - μ jj) • b j) := by
        rw [Polynomial.aeval_C, hX]
    _ = c • ((μ j - μ jj) • b j) := by
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    _ = (c * (μ j - μ jj)) • b j := by rw [smul_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- A product of linear factors acts on an eigenvector by the product of scalars. -/
theorem aeval_prod_apply (hb : ∀ i, s (b i) = μ i • b i) (i j : ι) (t : Finset ι) :
    aeval s (∏ jj ∈ t, (C ((μ i - μ jj)⁻¹) * (X - C (μ jj)))) (b j)
      = (∏ jj ∈ t, ((μ i - μ jj)⁻¹ * (μ j - μ jj))) • b j := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, Module.End.mul_eq_comp,
      LinearMap.comp_apply, ih, map_smul, aeval_factor_apply hb, smul_smul]
    congr 1
    ring

/-- The Lagrange projector is the `i`-th coordinate projection in the eigenbasis. -/
theorem aeval_lagrange_apply (hb : ∀ i, s (b i) = μ i • b i) (hinj : Function.Injective μ)
    (i j : ι) : aeval s (lagrange μ i) (b j) = if i = j then b j else 0 := by
  classical
  rw [lagrange, aeval_prod_apply hb]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.prod_eq_one]
    · simp
    · intro jj hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hji, -⟩ := hj
      have hne : μ i - μ jj ≠ 0 := by
        intro h
        exact hji (hinj (sub_eq_zero.mp h)).symm
      exact inv_mul_cancel₀ hne
  · rw [if_neg hij]
    have hmem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [Finset.prod_eq_zero hmem]
    · simp
    · simp

/-- The Lagrange projector picks out the `i`-th coordinate of any vector. -/
theorem aeval_lagrange_eq_smul (hb : ∀ i, s (b i) = μ i • b i) (hinj : Function.Injective μ)
    (i : ι) (x : V) : aeval s (lagrange μ i) x = (b.repr x i) • b i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [map_smul, aeval_lagrange_apply hb hinj, if_pos rfl]
  · intro j _ hji
    rw [map_smul, aeval_lagrange_apply hb hinj, if_neg (Ne.symm hji), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Plan C.1, algebraic core.**  In an eigenbasis `b` with distinct eigenvalues
`μ`, every invariant subspace is the span of the eigenvectors it contains. -/
theorem exists_finset_eq_span_of_invariant (hb : ∀ i, s (b i) = μ i • b i)
    (hinj : Function.Injective μ) (W : Submodule K V) (hW : ∀ x ∈ W, s x ∈ W) :
    ∃ S : Finset ι, W = Submodule.span K (b '' (S : Set ι)) := by
  classical
  refine ⟨Finset.univ.filter (fun i => ∃ x ∈ W, b.repr x i ≠ 0), ?_⟩
  set S := Finset.univ.filter (fun i => ∃ x ∈ W, b.repr x i ≠ 0) with hS
  have h1 : W ≤ Submodule.span K (b '' (S : Set ι)) := by
    intro x hx
    conv_rhs => rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : b.repr x i = 0
    · simp [hi]
    · have hiS : i ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, x, hx, hi⟩
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, by simpa using hiS, rfl⟩)
  have h2 : Submodule.span K (b '' (S : Set ι)) ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hiS, rfl⟩
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hiS
    obtain ⟨-, x, hx, hxi⟩ := hiS
    have hxsm : (b.repr x i) • b i ∈ W := by
      rw [← aeval_lagrange_eq_smul hb hinj i x]
      exact aeval_mem_of_invariant hW (lagrange μ i) x hx
    have : b i = (b.repr x i)⁻¹ • ((b.repr x i) • b i) := by
      rw [smul_smul, inv_mul_cancel₀ hxi, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hxsm
  exact le_antisymm h1 h2


/-- A nonzero invariant subspace contains one of the eigenvectors. -/
theorem exists_eigenvector_mem_of_ne_bot (hb : ∀ i, s (b i) = μ i • b i)
    (hinj : Function.Injective μ) {W : Submodule K V} (hW : ∀ x ∈ W, s x ∈ W)
    (hne : W ≠ ⊥) : ∃ i, b i ∈ W := by
  obtain ⟨S, hS⟩ := exists_finset_eq_span_of_invariant hb hinj W hW
  rcases S.eq_empty_or_nonempty with h | ⟨i, hi⟩
  · rw [h, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hS
    exact absurd hS hne
  · refine ⟨i, ?_⟩
    rw [hS]
    exact Submodule.subset_span ⟨i, by simpa using hi, rfl⟩

end CoordinateSpan

/-! ## 9. Assembling §7 for the unit–prime model -/

/-- The characteristic polynomial of the integral endomorphism of a ℤ-lattice of
rank three has degree three. -/
theorem charpoly_natDegree_eq_three (M : Submodule ℤ Pt) [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M) (hrank : Module.finrank ℤ M = 3) :
    (LinearMap.charpoly (intAct M f hf)).natDegree = 3 := by
  rw [LinearMap.charpoly_natDegree, hrank]

/-- A full ℤ-lattice in `Pt = ℝ³` has `ℤ`-rank three. -/
theorem finrank_eq_three_of_isZLattice (M : Submodule ℤ Pt) [DiscreteTopology M]
    [IsZLattice ℝ M] : Module.finrank ℤ M = 3 := by
  rw [ZLattice.rank ℝ M]
  simp

section UnitPrimeModelEigen

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
  (D : UnitPrimeModel L 𝒪) [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- **Three distinct complex eigenvalues for the unit–prime model.**  From (B1)
for the selected `i` (and fullness of the lattice `σ(𝒪)`), the characteristic
polynomial of the `ℚ`-base change of the integral endomorphism splits over `ℂ`
into three distinct linear factors. -/
theorem UnitPrimeModel.exists_distinct_eigenvalues (i : 𝒪ˣ × ℕ)
    (hB1 : ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.intLact i) ^ n))) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧
      (LinearMap.charpoly ((D.intLact i).baseChange ℚ)).map (algebraMap ℚ ℂ) =
        ∏ j, (X - C (μ j)) := by
  refine exists_distinct_roots_charpoly_of_B1 (D.intLact i) hB1 ?_
  rw [LinearMap.charpoly_natDegree,
    finrank_eq_three_of_isZLattice (AddSubgroup.toIntSubmodule L)]

end UnitPrimeModelEigen

/-- **The A3 input in drop-in form.**  For the *complexification* of the
restriction of `f` to the ℚ-span of the lattice, the characteristic polynomial
splits over `ℂ` into three distinct linear factors. -/
theorem exists_distinct_roots_charpoly_baseChange_complex (M : Submodule ℤ Pt)
    [Module.Free ℤ M] [Module.Finite ℤ M] (f : Pt →ₗ[ℝ] Pt) (hf : ∀ x ∈ M, f x ∈ M)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly ((intAct M f hf) ^ n)))
    (hdeg : (LinearMap.charpoly (intAct M f hf)).natDegree = 3) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧
      LinearMap.charpoly ((ratAct M f hf).baseChange ℂ) = ∏ i, (X - C (μ i)) := by
  obtain ⟨μ, hinj, hprod⟩ := exists_distinct_roots_charpoly_of_B1 (intAct M f hf) hB1 hdeg
  refine ⟨μ, hinj, ?_⟩
  rw [LinearMap.charpoly_baseChange, charpoly_ratAct, ← charpoly_baseChange_rat]
  exact hprod

end CubicTwoStage
