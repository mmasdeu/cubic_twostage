/-
# Arithmetic discharge of `propIV1_unitPrime'` (swarm `smw9665xe`, member m1, direction d1)

`CubicTwoStage/BerendIV1Model.lean` reduces Furstenberg's Proposition IV.1 for
the unit–prime family `Σ = {μ_{uπ^j}}` to three level facts, of which the only
unproved one was `hinj`:

  every multiplier `μ_{uπ^j}` acts injectively on `{x | q ^ n • x = 0}`.

This file proves it.  Mathematically the input is the standard one: `μ_{uπ^j}`
is `σ(u π^j)`, its determinant is `± p ^ j` where `p = |Nm π|`, so modulo `q`
it is invertible for `q ∤ p`; equivalently the ideals `(π)` and `(q)` of `𝓞 K`
are comaximal, and `q ^ n ∣ π ^ j y` forces `q ^ n ∣ y`.

Contents.

* §1 (`mem_of_mul_mem_of_sup_top`, `mem_span_natCast_pow_of_pow_mul_mem`,
  `dvd_of_dvd_pow_mul`) — comaximality `(x) ⊔ I = ⊤` gives saturation
  `x * y ∈ I → y ∈ I`, and `(x) ⊔ (q) = ⊤` gives the same with `x ^ j`, `q ^ n`.
* §2 (`σ`-arithmetic) — `σ` is injective, `σ ((n : ℕ) * a) = n • σ a`,
  `powC (r • oneC) n = r ^ n • oneC`, `a ⋆ (n • x) = n • (a ⋆ x)`.
* §3 (`mem_lattice_of_nsmul_mem_of_mul_mem`) — the lift: if `q ^ n • w` and
  `σ (u π ^ j) ⋆ w` are both lattice points, so is `w`.
* §4 (`torusAct_injective_on_lvlSet`, `familyHom_inj_on_lvlSet`) — injectivity
  on every `q`-primary level, in the exact shape of the `hinj` of
  `BerendIV1Model.propIV1_unitPrime'`.
* §5 — `propIV1_unitPrime'_of_coprime` (interface form: the single arithmetic
  hypothesis `(π) ⊔ (q) = ⊤`), `propIV1_unitPrime'_arith` (primality form:
  `p = |Nm π|` and `q` prime, `q ≠ p`, from
  `BerendPrimeNorm.coprime_ideals_of_absNorm_eq_prime`), and
  `propIV1_unitPrime'_canonical` (the canonical complex cubic model).
* §6 — `minimal_finite_of_stageI`: Berend's Proposition 5.1
  (`BerendPropIV1.minimal_finite_of_propIV1`) now needs only Stage I.

No `sorry`, no new axiom, no use of `berend_multi_invariance`; `#print axioms`
at the end reports `propext`, `Classical.choice`, `Quot.sound` for every
declaration.
-/
import CubicTwoStage.BerendIV1Model
import CubicTwoStage.BerendPrimeNorm
import CubicTwoStage.BerendExpandingMember
import CubicTwoStage.BerendUnitNoncritical
import CubicTwoStage.BerendInterface
import CubicTwoStage.ComplexCubic

open CubicTwoStage
open scoped NumberField Pointwise

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace CubicTwoStage
namespace BerendIV1Arith

/-! ## 1. Saturation from comaximality -/

theorem mem_of_mul_mem_of_sup_top {R : Type*} [CommRing R] {I : Ideal R} {x y : R}
    (h : Ideal.span {x} ⊔ I = ⊤) (hxy : x * y ∈ I) : y ∈ I := by
  have h1 : (1 : R) ∈ Ideal.span {x} ⊔ I := by
    rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
  have hy : y = c * (x * y) + b * y := by
    have h2 : (x * c + b) * y = y := by rw [hab]; ring
    calc y = (x * c + b) * y := h2.symm
      _ = c * (x * y) + b * y := by ring
  rw [hy]
  exact I.add_mem (I.mul_mem_left c hxy) (I.mul_mem_right y hb)

theorem mem_span_natCast_pow_of_pow_mul_mem {R : Type*} [CommRing R] {x : R} {q : ℕ}
    (hcop : Ideal.span {x} ⊔ Ideal.span {(q : R)} = ⊤)
    (j n : ℕ) {y : R} (h : x ^ j * y ∈ Ideal.span {((q : R) ^ n)}) :
    y ∈ Ideal.span {((q : R) ^ n)} := by
  have h2 : Ideal.span {x} ^ j ⊔ Ideal.span {(q : R)} = ⊤ := Ideal.pow_sup_eq_top hcop
  have h3 : Ideal.span {x} ^ j ⊔ Ideal.span {(q : R)} ^ n = ⊤ := Ideal.sup_pow_eq_top h2
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h3
  exact mem_of_mul_mem_of_sup_top h3 h

/-- Saturation, in divisibility form: if a prime `x` is coprime to `q`, then a
`q^n`-divisible multiple of `x^j` already has a `q^n`-divisible cofactor. -/
theorem dvd_of_dvd_pow_mul {R : Type*} [CommRing R] {x : R} {q : ℕ}
    (hcop : Ideal.span {x} ⊔ Ideal.span {(q : R)} = ⊤) (j n : ℕ) {y : R}
    (h : ((q : R) ^ n) ∣ x ^ j * y) : ((q : R) ^ n) ∣ y := by
  rw [← Ideal.mem_span_singleton] at h ⊢
  exact mem_span_natCast_pow_of_pow_mul_mem hcop j n h

/-! ## 2. `σ`-arithmetic of a `FieldModel` -/

section Sigma

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

variable (FM : FieldModel K 𝒪 Nm)

theorem σ_injective : Function.Injective FM.σ := by
  intro a b hab
  have h : FM.σ (a - b) = 0 := by rw [FM.σ_sub, hab, sub_self]
  have := FM.σ_eq_zero h
  exact sub_eq_zero.mp this

theorem σ_natCast (n : ℕ) : FM.σ ((n : ℕ) : K) = n • oneC := by
  induction n with
  | zero => rw [Nat.cast_zero, FM.σ_zero, zero_nsmul]
  | succ n ih => rw [Nat.cast_succ, FM.σ_add, ih, FM.σ_one, succ_nsmul, add_comm]

theorem smul_oneC_mulC (r : ℝ) (x : Pt) : (r • oneC) ⋆ x = r • x := by
  rw [mulC_smul, oneC_mulC]

theorem powC_smul_oneC_eq (r : ℝ) (n : ℕ) : powC (r • oneC) n = r ^ n • oneC := by
  induction n with
  | zero => rw [powC_zero, pow_zero, one_smul]
  | succ n ih =>
      rw [powC_succ, ih, mulC_smul, oneC_mulC, smul_smul, ← pow_succ']

theorem powC_smul_oneC (r : ℝ) (n : ℕ) (x : Pt) :
    powC (r • oneC) n ⋆ x = r ^ n • x := by
  rw [powC_smul_oneC_eq, mulC_smul, oneC_mulC]

theorem nsmul_oneC_mulC (n : ℕ) (x : Pt) : (n • oneC) ⋆ x = n • x := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n oneC, ← Nat.cast_smul_eq_nsmul ℝ n x, smul_oneC_mulC]

theorem σ_natCast_mul (n : ℕ) (a : K) :
    FM.σ (((n : ℕ) : K) * a) = n • FM.σ a := by
  rw [FM.σ_mul, σ_natCast, nsmul_oneC_mulC]

end Sigma

/-! ## 3. Saturation in the model -/

theorem mulC_nsmul (a : Pt) (n : ℕ) (x : Pt) : a ⋆ (n • x) = n • (a ⋆ x) := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n x, ← Nat.cast_smul_eq_nsmul ℝ n (a ⋆ x), smul_mulC]

section Model

variable {K : Type*} [Field K] [NumberField K]

variable (FM : FieldModel K (numberFieldO K) (numberFieldAbsNorm K))

/-- The identity map from the `Subring` `numberFieldO K` to the type `𝓞 K`. -/
noncomputable def roiEquiv : numberFieldO K ≃+* 𝓞 K where
  toFun g := ⟨g.1, g.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv g := rfl
  right_inv x := rfl
  map_add' g h := rfl
  map_mul' g h := rfl

@[simp] theorem roiEquiv_coe (g : numberFieldO K) : ((roiEquiv g : 𝓞 K) : K) = (g : K) := rfl

/-- **Saturation of the lattice at a prime `π` coprime to `q`.**

If a point `w` of the model space becomes a lattice point after multiplying by
`q ^ n`, and also after multiplying by `σ(u π ^ j)`, then `w` is already a
lattice point.  The arithmetic content is: `(π)` is comaximal with `(q)` in
`𝓞 K`, so `q ^ n ∣ π ^ j y` forces `q ^ n ∣ y`. -/
theorem mem_lattice_of_nsmul_mem_of_mul_mem {π : K} (hπO : π ∈ numberFieldO K)
    {q : ℕ} (hq0 : q ≠ 0)
    (hcop : Ideal.span {(⟨π, hπO⟩ : 𝓞 K)} ⊔ Ideal.span {(q : 𝓞 K)} = ⊤)
    (u : (numberFieldO K)ˣ) (j n : ℕ) {w : Pt}
    (h1 : q ^ n • w ∈ FM.lattice)
    (h2 : FM.σ (((u : numberFieldO K) : K) * π ^ j) ⋆ w ∈ FM.lattice) :
    w ∈ FM.lattice := by
  obtain ⟨y, hy⟩ := FM.mem_lattice.mp h1
  obtain ⟨g, hg⟩ := FM.mem_lattice.mp h2
  set A : K := ((u : numberFieldO K) : K) * π ^ j with hA
  set U : (𝓞 K)ˣ := Units.map roiEquiv.toMonoidHom u with hU
  have hUcoe : (U : 𝓞 K) = roiEquiv (u : numberFieldO K) := Units.coe_map _ _
  -- the two descriptions of `q ^ n • (σ A ⋆ w)`
  have step1 : q ^ n • (FM.σ A ⋆ w) = FM.σ (A * (y : K)) := by
    rw [← mulC_nsmul, ← hy, ← FM.σ_mul]
  have step2 : q ^ n • (FM.σ A ⋆ w) = FM.σ (((q ^ n : ℕ) : K) * (g : K)) := by
    rw [← hg, ← σ_natCast_mul]
  have heq : A * (y : K) = ((q ^ n : ℕ) : K) * (g : K) :=
    σ_injective FM (step1.symm.trans step2)
  -- the same identity inside the subring
  have hsub : (u : numberFieldO K) * ⟨π, hπO⟩ ^ j * y
      = ((q ^ n : ℕ) : numberFieldO K) * g := by
    apply Subtype.ext
    push_cast
    simpa [hA] using heq
  -- transport to `𝓞 K`
  have hroi := congrArg roiEquiv hsub
  simp only [map_mul, map_pow, map_natCast] at hroi
  rw [Nat.cast_pow] at hroi
  -- divisibility of the cofactor
  have hdvd : (q : 𝓞 K) ^ n
      ∣ (roiEquiv ⟨π, hπO⟩) ^ j * ((U : 𝓞 K) * (roiEquiv y)) :=
    ⟨roiEquiv g, by rw [← hroi, hUcoe]; ring⟩
  obtain ⟨e, he⟩ := dvd_of_dvd_pow_mul hcop j n hdvd
  -- remove the unit
  have hyq : (q : 𝓞 K) ^ n ∣ roiEquiv y := by
    have hmul : roiEquiv y = ((U⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((U : 𝓞 K) * (roiEquiv y)) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hmul]
    exact dvd_mul_of_dvd_right ⟨e, he⟩ _
  -- back to the field
  obtain ⟨e₂, he₂⟩ := hyq
  set y' : numberFieldO K := ⟨(e₂ : K), e₂.2⟩ with hy'def
  have hyeq : y = ((q ^ n : ℕ) : numberFieldO K) * y' := by
    apply roiEquiv.injective
    rw [map_mul, map_natCast, Nat.cast_pow, he₂]
    have hone : roiEquiv y' = e₂ := rfl
    rw [hone]
  -- conclude
  have hfinal : w = FM.σ (y' : K) := by
    have h2' : q ^ n • w = q ^ n • FM.σ (y' : K) := by
      rw [← hy, ← σ_natCast_mul]
      congr 1
      rw [hyeq]
      push_cast
      ring
    have hqne : ((q ^ n : ℕ) : ℝ) ≠ 0 := by
      have hqpos : (0:ℕ) < q ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hq0)
      positivity
    rw [← Nat.cast_smul_eq_nsmul ℝ (q ^ n) w,
      ← Nat.cast_smul_eq_nsmul ℝ (q ^ n) (FM.σ (y' : K))] at h2'
    exact (smul_right_inj (M := Pt) hqne).mp h2'
  exact FM.mem_lattice.mpr ⟨y', hfinal.symm⟩

end Model

/-! ## 4. Multiplier injectivity on the `q`-primary levels -/

section Levels

variable {K : Type*} [Field K] [NumberField K]

variable (FM : FieldModel K (numberFieldO K) (numberFieldAbsNorm K))
variable (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)

/-- The multiplier of the model is `σ` of `u π ^ j`. -/
theorem toModel_mult_eq (u : (numberFieldO K)ˣ) (j : ℕ) :
    (FM.toModel ε π hπO hπ0).mult u j = FM.σ (((u : numberFieldO K) : K) * π ^ j) := by
  rw [FieldModel.toModel_mult, FieldModel.mult, ← FM.σ_mul_pow, ← FM.σ_mul]

/-- **Injectivity of every family multiplier on each `q`-primary level.** -/
theorem torusAct_injective_on_lvlSet {q : ℕ} (hq0 : q ≠ 0)
    (hcop : Ideal.span {(⟨π, hπO⟩ : 𝓞 K)} ⊔ Ideal.span {(q : 𝓞 K)} = ⊤)
    (u : (numberFieldO K)ˣ) (j n : ℕ) :
    ∀ x ∈ BerendIV1Model.lvlSet FM.lattice q n,
      ∀ y ∈ BerendIV1Model.lvlSet FM.lattice q n,
      (FM.toModel ε π hπO hπ0).torusAct (u, j) x =
        (FM.toModel ε π hπO hπ0).torusAct (u, j) y → x = y := by
  intro x hx y hy hxy
  obtain ⟨X, rfl⟩ := QuotientAddGroup.mk'_surjective FM.lattice x
  obtain ⟨Y, rfl⟩ := QuotientAddGroup.mk'_surjective FM.lattice y
  -- the two level conditions, lifted
  have hX : q ^ n • X ∈ FM.lattice := by
    have hx' : (QuotientAddGroup.mk' FM.lattice) (q ^ n • X) = 0 := by
      rw [map_nsmul]; exact hx
    exact (QuotientAddGroup.eq_zero_iff _).mp hx'
  have hY : q ^ n • Y ∈ FM.lattice := by
    have hy' : (QuotientAddGroup.mk' FM.lattice) (q ^ n • Y) = 0 := by
      rw [map_nsmul]; exact hy
    exact (QuotientAddGroup.eq_zero_iff _).mp hy' 
  -- the multiplier condition, lifted
  have hXY : (FM.toModel ε π hπO hπ0).mult u j ⋆ (X - Y) ∈ FM.lattice := by
    have h := hxy
    rw [UnitPrimeModel.torusAct_mk', UnitPrimeModel.torusAct_mk',
      UnitPrimeModel.family_apply, UnitPrimeModel.family_apply] at h
    have h2 := (QuotientAddGroup.eq_iff_sub_mem).mp h
    have h3 : (FM.toModel ε π hπO hπ0).mult u j ⋆ X -
        (FM.toModel ε π hπO hπ0).mult u j ⋆ Y =
        (FM.toModel ε π hπO hπ0).mult u j ⋆ (X - Y) := (mulC_sub _ _ _).symm
    rwa [h3] at h2
  rw [toModel_mult_eq] at hXY
  have hmem := mem_lattice_of_nsmul_mem_of_mul_mem FM hπO hq0 hcop u j n
    (w := X - Y) (by rw [smul_sub]; exact FM.lattice.sub_mem hX hY) hXY
  exact (QuotientAddGroup.eq_iff_sub_mem).mpr hmem

/-- The `hinj` hypothesis of `propIV1_unitPrime'`, discharged. -/
theorem familyHom_inj_on_lvlSet {q : ℕ} (hq0 : q ≠ 0)
    (hcop : Ideal.span {(⟨π, hπO⟩ : 𝓞 K)} ⊔ Ideal.span {(q : 𝓞 K)} = ⊤)
    (n : ℕ) :
    ∀ (s : (numberFieldO K)ˣ × Multiplicative ℕ),
      ∀ x ∈ BerendIV1Model.lvlSet FM.lattice q n,
      ∀ y ∈ BerendIV1Model.lvlSet FM.lattice q n,
      (BerendIV1Model.familyHom (FM.toModel ε π hπO hπ0) s) x =
        (BerendIV1Model.familyHom (FM.toModel ε π hπO hπ0) s) y → x = y := by
  rintro ⟨u, k⟩
  exact torusAct_injective_on_lvlSet FM ε π hπO hπ0 hq0 hcop u k.toAdd n

end Levels

/-! ## 5. The arithmetic theorem: `propIV1_unitPrime'` with no level input -/

section Final

variable {K : Type*} [Field K] [NumberField K]

variable (FM : FieldModel K (numberFieldO K) (numberFieldAbsNorm K))

/-- **Furstenberg's Proposition IV.1 for the unit–prime family, with the level
injectivity discharged arithmetically.**  The only arithmetic inputs are: a prime
element `π` of `𝓞 K` of prime absolute norm `p`, and an ordinary prime `q ≠ p`.
The expanding member is produced from the infinite-order hypothesis `hεpow`. -/
theorem propIV1_unitPrime'_arith
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice)]
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    BerendPropIV1.PropIV1 (fun i : (numberFieldO K)ˣ × ℕ =>
      (FM.toModel ε π hπO hπ0).torusAct i) := by
  have hx : numberFieldAbsNorm K (((⟨π, hπO⟩ : 𝓞 K)) : K) = (p : ℚ≥0) := hπN
  have hx0 : (⟨π, hπO⟩ : 𝓞 K) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hcop := BerendPrimeNorm.coprime_ideals_of_absNorm_eq_prime
    (x := (⟨π, hπO⟩ : 𝓞 K)) hp hq hpq hx hx0
  obtain ⟨u₀, j₀, -, ha0, hC⟩ := BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
    FM ε π hπO hπ0 hεpow p (by exact_mod_cast hp.one_lt) hπN
  refine BerendIV1Model.propIV1_unitPrime' (FM.toModel ε π hπO hπ0) q ?_ hq.two_le u₀ j₀ ha0 hC
  intro s n
  exact familyHom_inj_on_lvlSet FM ε π hπO hπ0 (Nat.Prime.ne_zero hq) hcop n s

/-- **The interface form**: `PropIV1` for the unit–prime family from the single
arithmetic obligation that `(π)` and `(q)` are comaximal in `𝓞 K`, plus `q ≥ 2`.
(Everything else — level finiteness, density, the interior step, the expanding
member — is already in the project.) -/
theorem propIV1_unitPrime'_of_coprime
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice)]
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (q : ℕ) (hq2 : 2 ≤ q)
    (hcop : Ideal.span {(⟨π, hπO⟩ : 𝓞 K)} ⊔ Ideal.span {(q : 𝓞 K)} = ⊤)
    (p : ℕ) (hp : 1 < (p : ℝ)) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    BerendPropIV1.PropIV1 (fun i : (numberFieldO K)ˣ × ℕ =>
      (FM.toModel ε π hπO hπ0).torusAct i) := by
  obtain ⟨u₀, j₀, -, ha0, hC⟩ := BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
    FM ε π hπO hπ0 hεpow p hp hπN
  refine BerendIV1Model.propIV1_unitPrime' (FM.toModel ε π hπO hπ0) q ?_ hq2 u₀ j₀ ha0 hC
  intro s n
  exact familyHom_inj_on_lvlSet FM ε π hπO hπ0 (by omega) hcop n s

/-! ## 6. Composing with Berend's Proposition 5.1 (`minimal_finite_of_propIV1`) -/

/-- **Minimal sets are finite**, conditional on Stage I only: with the level
injectivity discharged arithmetically, `BerendPropIV1.minimal_finite_of_propIV1`
needs nothing else. -/
theorem minimal_finite_of_stageI
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule FM.lattice)]
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hStage : BerendDichotomy.ZeroNonisolatedFull
      (fun i : (numberFieldO K)ˣ × ℕ => (FM.toModel ε π hπO hπ0).torusAct i))
    {M : Set (Torus FM.lattice)}
    (hM : BerendMinimal.IsMinimalInvariant
      (fun i : (numberFieldO K)ˣ × ℕ =>
        ((FM.toModel ε π hπO hπ0).torusAct i : Torus FM.lattice → Torus FM.lattice)) M) :
    M.Finite := by
  haveI : CompactSpace (Torus FM.lattice) := compact_quotient_of_isZLattice FM.lattice
  haveI : Nontrivial (Torus FM.lattice) := BerendInterface.nontrivial_torus
  exact BerendPropIV1.minimal_finite_of_propIV1 hStage
    (propIV1_unitPrime'_arith FM ε π hπO hπ0 hεpow p q hp hq hpq hπN) hM

/-- The same at the canonical model of a complex cubic field. -/
theorem propIV1_unitPrime'_canonical {K : Type*} [Field K] [NumberField K]
    (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0)) :
    BerendPropIV1.PropIV1 (fun i : (numberFieldO K)ˣ × ℕ =>
      ((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i) := by
  haveI : DiscreteTopology (AddSubgroup.toIntSubmodule (NumberFieldCubic.canonicalFieldModel K h).lattice) :=
    NumberFieldCubic.discreteTopology_canonicalFieldModel_lattice K h
  haveI : IsZLattice ℝ (AddSubgroup.toIntSubmodule (NumberFieldCubic.canonicalFieldModel K h).lattice) :=
    NumberFieldCubic.isZLattice_canonicalFieldModel_lattice K h
  exact propIV1_unitPrime'_arith (NumberFieldCubic.canonicalFieldModel K h) ε π hπO hπ0 hεpow p q hp hq hpq hπN

end Final

end BerendIV1Arith
end CubicTwoStage

/-! ## 6. Axiom audit -/

#print axioms CubicTwoStage.BerendIV1Arith.mem_of_mul_mem_of_sup_top
#print axioms CubicTwoStage.BerendIV1Arith.mem_span_natCast_pow_of_pow_mul_mem
#print axioms CubicTwoStage.BerendIV1Arith.mem_lattice_of_nsmul_mem_of_mul_mem
#print axioms CubicTwoStage.BerendIV1Arith.torusAct_injective_on_lvlSet
#print axioms CubicTwoStage.BerendIV1Arith.familyHom_inj_on_lvlSet
#print axioms CubicTwoStage.BerendIV1Arith.propIV1_unitPrime'_arith
#print axioms CubicTwoStage.BerendIV1Arith.propIV1_unitPrime'_of_coprime
#print axioms CubicTwoStage.BerendIV1Arith.minimal_finite_of_stageI
#print axioms CubicTwoStage.BerendIV1Arith.propIV1_unitPrime'_canonical