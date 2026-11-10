/-
# From a number field to the unit–prime model of §3

This file removes the conditional layer of Theorem 3.6 by *constructing* the
model from field data instead of assuming it.

The data are the paper's own: a field `K`, a subring `𝒪` (the ring of integers),
an absolute norm `Nm`, and the embedding `σ : K → ℝ × ℂ`.  The only facts
required of them are the ones that make them *that* data:

* `σ` is additive, multiplicative, sends `1` to `1` and inverses to inverses;
* `|normR (σ a)| = Nm a`, i.e. `σ` is norm-compatible;
* `Nm` takes natural-number values on `𝒪` (integrality of the absolute norm).

From these we construct the lattice `L = σ(𝒪)`, the `UnitPrimeModel` of §3, the
open set `W` of Lemma 3.8, and we **prove** the hypotheses that Theorem 3.6
previously assumed: that `L = σ(𝒪)`, that `W` is open, nonempty and a union of
classes modulo `L`, that the uncovered set is invariant under units, that
`μ_{εⁿ}` has no nonzero fixed vector, that `(εⁿ - 1) ≠ 0`, and — through the
tower lemma at the level of `ℝ × ℂ` — that the semigroup orbit of the uncovered
set avoids `W`.

What is *not* proved here, and remains a hypothesis of the final theorem, is the
number theory the paper verifies separately: the existence of the prime `π` with
its `p`-adic property (Lemma 3.7), Berend's conditions (B1)–(B3) for the
semigroup, and compactness of the quotient `(ℝ × ℂ)/σ(𝒪)`.
-/
import CubicTwoStage.Model
import CubicTwoStage.Uncovered

open scoped TensorProduct

namespace CubicTwoStage

variable {K : Type*} [Field K] {𝒪 : Subring K} {Nm : AbsNorm K}

/-! ## The data -/

/-- A number field presented in the model algebra `ℝ × ℂ`: the embedding `σ`,
together with the multiplicative and norm-compatibility properties that make it
the canonical embedding.  Nothing here is specific to degree three: the model
space already is `Pt = ℝ × ℂ`. -/
structure FieldModel (K : Type*) [Field K] (𝒪 : Subring K) (Nm : AbsNorm K) where
  /-- The embedding of `K` into `ℝ × ℂ`. -/
  σ : K → Pt
  σ_zero : σ 0 = 0
  σ_add : ∀ a b : K, σ (a + b) = σ a + σ b
  σ_mul : ∀ a b : K, σ (a * b) = σ a ⋆ σ b
  σ_one : σ 1 = oneC
  σ_inv : ∀ a : K, a ≠ 0 → σ a ⋆ σ a⁻¹ = oneC
  /-- `σ` is compatible with the absolute norm. -/
  normR_abs : ∀ a : K, |normR (σ a)| = ((Nm a : ℚ≥0) : ℝ)
  /-- The absolute norm is integral on `𝒪`. -/
  norm_nat : ∀ a ∈ 𝒪, ∃ n : ℕ, Nm a = (n : ℚ≥0)

namespace FieldModel

variable (FM : FieldModel K 𝒪 Nm)
include FM

lemma σ_neg (a : K) : FM.σ (-a) = -FM.σ a := by
  have h : FM.σ (-a) + FM.σ a = 0 := by
    rw [← FM.σ_add, neg_add_cancel, FM.σ_zero]
  exact eq_neg_iff_add_eq_zero.mpr h

lemma σ_sub (a b : K) : FM.σ (a - b) = FM.σ a - FM.σ b := by
  rw [sub_eq_add_neg, FM.σ_add, FM.σ_neg, sub_eq_add_neg]

/-- `σ` vanishes only at zero. -/
lemma σ_eq_zero {a : K} (h : FM.σ a = 0) : a = 0 := by
  have h1 : ((Nm a : ℚ≥0) : ℝ) = 0 := by
    rw [← FM.normR_abs, h]; simp [normR]
  have h2 : Nm a = 0 := by exact_mod_cast h1
  exact (AbsNorm.eq_zero_iff Nm).mp h2

lemma σ_mul_pow (a : K) (n : ℕ) : FM.σ (a ^ n) = powC (FM.σ a) n := by
  induction n with
  | zero => simpa using FM.σ_one
  | succ n ih => rw [pow_succ, FM.σ_mul, ih, powC_succ, mulC_comm]

/-- The absolute norm of a unit of `𝒪` is one. -/
theorem Nm_unit (u : 𝒪ˣ) : Nm (((u : 𝒪) : K)) = 1 := by
  obtain ⟨n, hn⟩ := FM.norm_nat (((u : 𝒪) : K)) (u : 𝒪).2
  obtain ⟨m, hm⟩ := FM.norm_nat ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) (((u⁻¹ : 𝒪ˣ) : 𝒪)).2
  have hval : ((u : 𝒪) : K) * (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) = 1 := by
    rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
  have h1 : ((n : ℚ≥0)) * ((m : ℚ≥0)) = 1 := by
    rw [← hn, ← hm, ← map_mul, hval, map_one]
  have h2 : n * m = 1 := by exact_mod_cast h1
  have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_right h2
  rw [hn, hn1]; norm_num

omit FM in
/-- The inverse of a unit of `𝒪`, as an element of `K`. -/
lemma coe_units_inv (u : 𝒪ˣ) : (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) = (((u : 𝒪) : K))⁻¹ := by
  have h : ((u : 𝒪) : K) * ((((u⁻¹ : 𝒪ˣ) : 𝒪)) : K) = 1 := by
    rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
  exact eq_inv_of_mul_eq_one_right h

/-- Units of `𝒪` have norm-one image, so multiplication by them preserves
`|normR|`. -/
lemma abs_normR_unit (u : 𝒪ˣ) : |normR (FM.σ (((u : 𝒪) : K)))| = 1 := by
  rw [FM.normR_abs, FM.Nm_unit u]; norm_num

/-! ## The lattice `σ(𝒪)` -/

/-- `σ` restricted to `𝒪`, as an additive map. -/
noncomputable def hom : 𝒪 →+ Pt where
  toFun g := FM.σ (g : K)
  map_zero' := by simpa using FM.σ_zero
  map_add' g h := by
    rw [Subring.coe_add, FM.σ_add]

@[simp] lemma hom_apply (g : 𝒪) : FM.hom g = FM.σ (g : K) := rfl

/-- The lattice `L = σ(𝒪_K)`. -/
noncomputable def lattice : AddSubgroup Pt := AddSubgroup.map FM.hom ⊤

theorem mem_lattice {w : Pt} : w ∈ FM.lattice ↔ ∃ g : 𝒪, FM.σ (g : K) = w := by
  constructor
  · intro hw
    obtain ⟨g, -, hg⟩ := AddSubgroup.mem_map.mp hw
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    exact AddSubgroup.mem_map.mpr ⟨g, trivial, hg⟩

/-- `L = σ(𝒪)`: every lattice point is the image of a ring element. -/
theorem lattice_eq_image (w : Pt) (hw : w ∈ FM.lattice) : ∃ g : 𝒪, FM.σ (g : K) = w :=
  FM.mem_lattice.mp hw

/-! ## The unit–prime model of §3 -/

/-- The multiplier `σ(u · π^j)`. -/
noncomputable def mult (π : K) (u : 𝒪ˣ) (j : ℕ) : Pt :=
  FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j

/-- The unit–prime model determined by the field data.  Its lattice is
`σ(𝒪)`, its unit multipliers are `σ(u)`, its prime multiplier is `σ(π)`. -/
noncomputable def toModel (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) :
    UnitPrimeModel FM.lattice 𝒪 where
  unit := (ε : K)
  unit_image u := FM.σ (((u : 𝒪) : K))
  unit_mul u v := by
    show FM.σ (((u * v : 𝒪ˣ) : 𝒪) : K) = FM.σ (((u : 𝒪) : K)) ⋆ FM.σ (((v : 𝒪) : K))
    rw [← FM.σ_mul]
    congr 1
  unit_one := by
    show FM.σ (((1 : 𝒪ˣ) : 𝒪) : K) = oneC
    rw [Units.val_one, Subring.coe_one, FM.σ_one]
  unit_inv u := FM.σ (((u⁻¹ : 𝒪ˣ) : 𝒪) : K)
  unit_inv_mul u := by
    show FM.σ (((u : 𝒪) : K)) ⋆ FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) = oneC
    rw [← FM.σ_mul]
    have h : ((u : 𝒪) : K) * (((u⁻¹ : 𝒪ˣ) : 𝒪) : K) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
    rw [h, FM.σ_one]
  prime := π
  prime_image _ := FM.σ π
  prime_inv := FM.σ π⁻¹
  prime_inv_mul := by
    show FM.σ π ⋆ FM.σ π⁻¹ = oneC
    rw [← FM.σ_mul, mul_inv_cancel₀ hπ0, FM.σ_one]
  lattice u j g hg := by
    obtain ⟨g', hg'⟩ := FM.mem_lattice.mp hg
    have hcoe : g = FM.σ (g' : K) := hg'.symm
    rw [hcoe]
    have hmem : (((u : 𝒪)) : K) * π ^ j * (g' : K) ∈ 𝒪 :=
      𝒪.mul_mem (𝒪.mul_mem (u : 𝒪).2 (pow_mem hπO j)) g'.2
    have hid : FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j ⋆ FM.σ ((g' : K)) =
        FM.σ ((((u : 𝒪)) : K) * π ^ j * (g' : K)) := by
      rw [← FM.σ_mul_pow, ← FM.σ_mul, ← FM.σ_mul]
    rw [hid]
    exact FM.mem_lattice.mpr ⟨⟨_, hmem⟩, rfl⟩
  lattice_unit_inv u g hg := by
    obtain ⟨g', hg'⟩ := FM.mem_lattice.mp hg
    have hcoe : g = FM.σ (g' : K) := hg'.symm
    rw [hcoe]
    have hmem : ((((u⁻¹ : 𝒪ˣ) : 𝒪)) : K) * (g' : K) ∈ 𝒪 :=
      𝒪.mul_mem ((u⁻¹ : 𝒪ˣ) : 𝒪).2 g'.2
    have hid : FM.σ ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) ⋆ FM.σ ((g' : K)) =
        FM.σ (((((u⁻¹ : 𝒪ˣ) : 𝒪)) : K) * (g' : K)) := by
      rw [← FM.σ_mul]
    rw [hid]
    exact FM.mem_lattice.mpr ⟨⟨_, hmem⟩, rfl⟩

@[simp] lemma toModel_unit_image (ε) (π hπO hπ0) (u : 𝒪ˣ) :
    (FM.toModel ε π hπO hπ0).unit_image u = FM.σ (((u : 𝒪) : K)) := rfl

@[simp] lemma toModel_prime_image (ε) (π hπO hπ0) (b : K) :
    (FM.toModel ε π hπO hπ0).prime_image b = FM.σ π := rfl

lemma toModel_mult (ε) (π hπO hπ0) (u : 𝒪ˣ) (j : ℕ) :
    (FM.toModel ε π hπO hπ0).mult u j = FM.mult π u j := rfl

/-! ## Units preserve the uncovered set -/

/-- The unit multiplier is one: `|normR (σ u)| = 1`. -/
lemma abs_normR_abs_unit (u : 𝒪ˣ) : |normR (FM.σ (((u : 𝒪) : K)))| = 1 :=
  FM.abs_normR_unit u

/-- Multiplying by a unit permutes the family of centres: the centre
`q₁ + q₂⁻¹` is the image under `σ(u)` of the centre `u⁻¹q₁ + (u q₂)⁻¹`, whose
denominator has the same norm.  Hence units preserve the uncovered set. -/
theorem uncovered_actU (u : 𝒪ˣ) {x : Pt} (hx : x ∈ uncovered 𝒪 Nm FM.σ) :
    FM.σ (((u : 𝒪) : K)) ⋆ x ∈ uncovered 𝒪 Nm FM.σ := by
  intro q1 hq1 q2 hq2 hq2ne hlt
  -- the inverse centre
  set q1' : 𝒪 := (u⁻¹ : 𝒪ˣ) * ⟨q1, hq1⟩ with hq1'
  set q2' : 𝒪 := (u : 𝒪ˣ) * ⟨q2, hq2⟩ with hq2'
  have hucoe : ((u : 𝒪ˣ) : 𝒪) = ((u : 𝒪)) := rfl
  have hu0 : ((u : 𝒪) : K) ≠ 0 := by
    intro h
    have h1 : Nm (((u : 𝒪) : K)) = 0 := by rw [h, map_zero]
    rw [FM.Nm_unit u] at h1
    exact one_ne_zero h1
  have hq2'0 : ((q2' : 𝒪) : K) ≠ 0 := by
    have h : ((q2' : 𝒪) : K) = ((u : 𝒪) : K) * q2 := by
      rw [hq2', Subring.coe_mul]
    rw [h]
    exact mul_ne_zero hu0 hq2ne
  -- the identity in `K`
  have hkey : (((u : 𝒪) : K)) * (((q1' : 𝒪) : K) + (((q2' : 𝒪) : K))⁻¹) = q1 + q2⁻¹ := by
    have h1 : ((q1' : 𝒪) : K) = (((u : 𝒪) : K))⁻¹ * q1 := by
      rw [hq1', Subring.coe_mul, coe_units_inv]
    have h2 : ((q2' : 𝒪) : K) = ((u : 𝒪) : K) * q2 := by
      rw [hq2', Subring.coe_mul]
    rw [h1, h2, mul_inv, mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul,
      one_mul]
  -- the inequality transfers
  have htrans : |normR (x - FM.σ (((q1' : 𝒪) : K) + ((q2' : 𝒪) : K)⁻¹))| <
      ((Nm ((q2' : 𝒪) : K) : ℚ≥0) : ℝ)⁻¹ := by
    have hNm : Nm ((q2' : 𝒪) : K) = Nm q2 := by
      have h : ((q2' : 𝒪) : K) = ((u : 𝒪) : K) * q2 := by
        rw [hq2', Subring.coe_mul]
      rw [h, map_mul, FM.Nm_unit u, one_mul]
    rw [hNm]
    have hsplit : FM.σ (((u : 𝒪) : K)) ⋆ x - FM.σ (q1 + q2⁻¹) =
        FM.σ (((u : 𝒪) : K)) ⋆ (x - FM.σ (((q1' : 𝒪) : K) + ((q2' : 𝒪) : K)⁻¹)) := by
      rw [mulC_sub, ← hkey, FM.σ_mul]
    rw [hsplit] at hlt
    rw [normR_mulC, abs_mul, FM.abs_normR_abs_unit u, one_mul] at hlt
    exact hlt
  exact hx _ (q1' : 𝒪).2 _ (q2' : 𝒪).2 hq2'0 htrans

/-! ## The open set `W` of Lemma 3.8 -/

/-- The union of the regions of radius `|Nm π^m|⁻¹` centred at the translates of
`σ(π^{-m})` by `σ(𝒪)`: the `W` of Lemma 3.8. -/
noncomputable def W (π : K) (m : ℕ) : Set Pt :=
  ⋃ g : 𝒪, V (FM.σ ((g : K) + (π ^ m)⁻¹)) (((Nm (π ^ m) : ℚ≥0)) : ℝ)⁻¹

lemma mem_W {π : K} {m : ℕ} {x : Pt} :
    x ∈ FM.W π m ↔ ∃ g : 𝒪,
      |normR (x - FM.σ ((g : K) + (π ^ m)⁻¹))| < (((Nm (π ^ m) : ℚ≥0)) : ℝ)⁻¹ :=
  Set.mem_iUnion

lemma W_open (π : K) (m : ℕ) : IsOpen (FM.W π m) := by
  refine isOpen_iUnion fun g => ?_
  exact isOpen_lt (continuous_abs.comp (continuous_normR.comp
    (continuous_id.sub continuous_const))) continuous_const

/-- `W` is a union of classes modulo `L = σ(𝒪)`. -/
lemma W_trans (π : K) (m : ℕ) (g₀ : 𝒪) (x : Pt) :
    x ∈ FM.W π m ↔ x - FM.σ (g₀ : K) ∈ FM.W π m := by
  rw [mem_W, mem_W]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g - g₀, ?_⟩
    have h1 : (((g - g₀ : 𝒪)) : K) + (π ^ m)⁻¹ = ((g : K) + (π ^ m)⁻¹) - (g₀ : K) := by
      push_cast
      ring
    have h2 : FM.σ ((((g - g₀ : 𝒪)) : K) + (π ^ m)⁻¹) =
        FM.σ ((g : K) + (π ^ m)⁻¹) - FM.σ (g₀ : K) := by
      rw [h1, FM.σ_sub]
    rw [h2]
    have : x - FM.σ (g₀ : K) - (FM.σ ((g : K) + (π ^ m)⁻¹) - FM.σ (g₀ : K)) =
        x - FM.σ ((g : K) + (π ^ m)⁻¹) := by abel
    rw [this]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨g + g₀, ?_⟩
    have h1 : (((g + g₀ : 𝒪)) : K) + (π ^ m)⁻¹ = ((g : K) + (π ^ m)⁻¹) + (g₀ : K) := by
      push_cast
      ring
    have h2 : FM.σ ((((g + g₀ : 𝒪)) : K) + (π ^ m)⁻¹) =
        FM.σ ((g : K) + (π ^ m)⁻¹) + FM.σ (g₀ : K) := by
      rw [h1, FM.σ_add]
    rw [h2]
    have : x - (FM.σ ((g : K) + (π ^ m)⁻¹) + FM.σ (g₀ : K)) =
        x - FM.σ (g₀ : K) - FM.σ ((g : K) + (π ^ m)⁻¹) := by abel
    rw [this]
    exact hg

/-- Multiplication by `σ(π)^j` scales `|normR|` by `|Nm π|^j`. -/
lemma abs_normR_powC (π : K) (j : ℕ) (w : Pt) :
    |normR (powC (FM.σ π) j ⋆ w)| = (((Nm π : ℚ≥0)) : ℝ) ^ j * |normR w| := by
  rw [normR_mulC, abs_mul, normR_powC, abs_pow, FM.normR_abs]

omit [Field K] FM in
lemma powC_add (a : Pt) (m n : ℕ) : powC a (m + n) = powC a m ⋆ powC a n := by
  induction n with
  | zero => rw [Nat.add_zero, powC_zero, mulC_oneC]
  | succ n ih =>
      rw [Nat.add_succ, powC_succ, powC_succ, ih, ← mulC_assoc, mulC_comm a,
        mulC_assoc]

/-- **Lemma 3.8, at the level of `ℝ × ℂ`.**  If `σ(π)^j y` lies in the open set
`W` of regions of radius `|Nm π^m|⁻¹`, then `y` lies in a region, so `y` is not
uncovered.  This is the paper's argument: with `a = 1 + π^m g` and
`s = m + j`, the point `a/π^s` is `h + (π^s ε^{-k})⁻¹` by Lemma 3.7, and
multiplication by `σ(π)^j` scales the norm distance by `|Nm π|^j`. -/
theorem tower (ε : 𝒪ˣ) (π : K) (m j : ℕ) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hpadic : ∀ g : 𝒪, ∃ k : ℕ, ∃ h ∈ 𝒪,
      (1 + π ^ m * ((g : 𝒪) : K)) - ((ε : 𝒪) : K) ^ k = π ^ (m + j) * h)
    {y : Pt} (hy : powC (FM.σ π) j ⋆ y ∈ FM.W π m) :
    y ∉ uncovered 𝒪 Nm FM.σ := by
  rw [mem_W] at hy
  obtain ⟨g, hg⟩ := hy
  -- the `p`-adic input for `a = 1 + π^m g`
  obtain ⟨k, hh, hk, hA⟩ := hpadic g
  -- the centre and its denominator
  set q2 : K := π ^ (m + j) * ((((ε⁻¹ : 𝒪ˣ) : 𝒪) : K)) ^ k with hq2
  have hq2O : q2 ∈ 𝒪 :=
    𝒪.mul_mem (pow_mem hπO (m + j)) (pow_mem (((ε⁻¹ : 𝒪ˣ) : 𝒪)).2 k)
  have hπs0 : π ^ (m + j) ≠ 0 := pow_ne_zero _ hπ0
  have hε0 : (((ε : 𝒪) : K)) ≠ 0 := by
    intro h
    have h1 : Nm (((ε : 𝒪) : K)) = 0 := by rw [h, map_zero]
    rw [FM.Nm_unit ε] at h1
    exact one_ne_zero h1
  have hεc : ((((ε⁻¹ : 𝒪ˣ) : 𝒪)) : K) = (((ε : 𝒪) : K))⁻¹ := coe_units_inv ε
  have hq20 : q2 ≠ 0 := by
    rw [hq2]
    exact mul_ne_zero hπs0 (pow_ne_zero _ (by rw [hεc]; exact inv_ne_zero hε0))
  have hq2inv : q2⁻¹ = (((ε : 𝒪) : K)) ^ k / π ^ (m + j) := by
    rw [hq2, mul_inv, div_eq_mul_inv, mul_comm]
    congr 1
    rw [hεc, inv_pow, inv_inv]
  -- the centre is `a / π^{m+j}`
  have hcentre : (hh : K) + q2⁻¹ = (1 + π ^ m * (g : K)) / π ^ (m + j) := by
    have h1 : (1 + π ^ m * (g : K)) = π ^ (m + j) * (hh : K) + ((ε : 𝒪) : K) ^ k := by
      have h2 := sub_eq_iff_eq_add.mp hA
      rw [h2]
    rw [hq2inv, h1]
    field_simp
  -- the scaled identity
  have hscale : π ^ j * ((hh : K) + q2⁻¹) = (g : K) + (π ^ m)⁻¹ := by
    rw [hcentre]
    have hl : π ^ j * ((1 + π ^ m * (g : K)) / π ^ (m + j)) =
        (1 + π ^ m * (g : K)) / π ^ m := by
      field_simp
      ring
    have hr : (g : K) + (π ^ m)⁻¹ = (1 + π ^ m * (g : K)) / π ^ m := by
      field_simp
      ring
    rw [hl, hr]
  have hσx : powC (FM.σ π) j ⋆ FM.σ ((hh : K) + q2⁻¹) = FM.σ ((g : K) + (π ^ m)⁻¹) := by
    rw [← FM.σ_mul_pow, ← FM.σ_mul, hscale]
  -- the norm inequality transfers
  have hmain : ((((Nm π : ℚ≥0)) : ℝ)) ^ j *
      |normR (y - FM.σ ((hh : K) + q2⁻¹))| <
        ((((Nm (π ^ m) : ℚ≥0)) : ℝ))⁻¹ := by
    have hsplit : powC (FM.σ π) j ⋆ y - FM.σ ((g : K) + (π ^ m)⁻¹) =
        powC (FM.σ π) j ⋆ (y - FM.σ ((hh : K) + q2⁻¹)) := by
      rw [mulC_sub, hσx]
    rw [hsplit, FM.abs_normR_powC] at hg
    exact hg
  have hq2norm : ((Nm q2 : ℚ≥0) : ℝ) = ((((Nm π : ℚ≥0)) : ℝ)) ^ (m + j) := by
    have h1 : Nm ((((ε⁻¹ : 𝒪ˣ) : 𝒪) : K)) = 1 := by
      rw [hεc, map_inv₀, FM.Nm_unit, inv_one]
    have h3 : Nm (((((ε⁻¹ : 𝒪ˣ) : 𝒪) : K)) ^ k) = 1 := by
      rw [map_pow, h1, one_pow]
    rw [hq2, map_mul, map_pow, h3, mul_one]
    push_cast
    rfl
  -- the final estimate
  have hp : (0 : ℝ) < (((Nm π : ℚ≥0)) : ℝ) := by
    have h : Nm π ≠ 0 := (AbsNorm.ne_zero_iff Nm).mpr hπ0
    exact_mod_cast (zero_lt_iff.mpr h)
  have hpj : (0 : ℝ) < ((((Nm π : ℚ≥0)) : ℝ)) ^ j := by positivity
  have hNmm : ((((Nm (π ^ m) : ℚ≥0)) : ℝ)) = ((((Nm π : ℚ≥0)) : ℝ)) ^ m := by
    rw [map_pow]
    push_cast
    rfl
  have hid : (((((Nm π : ℚ≥0)) : ℝ)) ^ (m + j))⁻¹ * ((((Nm π : ℚ≥0)) : ℝ)) ^ j =
      (((((Nm π : ℚ≥0)) : ℝ)) ^ m)⁻¹ := by
    rw [pow_add, mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpj), mul_one]
  rw [hNmm] at hmain
  have hfin : |normR (y - FM.σ ((hh : K) + q2⁻¹))| <
      (((((Nm π : ℚ≥0)) : ℝ)) ^ (m + j))⁻¹ := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hpj)
    rw [hid, mul_comm]
    exact hmain
  intro hunc
  exact hunc _ hk _ hq2O hq20 (by rw [hq2norm]; exact hfin)

/-! ## The semigroup orbit avoids `W` -/

/-- Products of multipliers are multipliers: `σ(uπ^j)σ(vπ^l) = σ(uv π^{j+l})`. -/
lemma mult_mul (π : K) (u v : 𝒪ˣ) (j l : ℕ) :
    FM.mult π u j ⋆ FM.mult π v l = FM.mult π (u * v) (j + l) := by
  show FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j ⋆
      (FM.σ (((v : 𝒪) : K)) ⋆ powC (FM.σ π) l) =
    FM.σ ((((u * v : 𝒪ˣ) : 𝒪) : K)) ⋆ powC (FM.σ π) (j + l)
  rw [mulC_mul_mul_comm, powC_add]
  congr 1
  rw [← FM.σ_mul]
  congr 1

/-- Every finite list of unit–prime actions acts by a single multiplier. -/
theorem applyList_form (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (l : List (𝒪ˣ × ℕ)) :
    ∃ (u : 𝒪ˣ) (j : ℕ), ∀ z : Pt,
      (FM.toModel ε π hπO hπ0).applyList l z = FM.mult π u j ⋆ z := by
  induction l with
  | nil =>
      refine ⟨1, 0, fun z => ?_⟩
      show z = FM.mult π 1 0 ⋆ z
      show z = FM.σ (((1 : 𝒪ˣ) : 𝒪) : K) ⋆ powC (FM.σ π) 0 ⋆ z
      rw [powC_zero, Units.val_one, Subring.coe_one, FM.σ_one, mulC_oneC, oneC_mulC]
  | cons i l ih =>
      obtain ⟨u, j, hu⟩ := ih
      obtain ⟨u₀, j₀⟩ := i
      refine ⟨u * u₀, j + j₀, fun z => ?_⟩
      have hstep : (FM.toModel ε π hπO hπ0).applyList ((u₀, j₀) :: l) z =
          (FM.toModel ε π hπO hπ0).applyList l
            ((FM.toModel ε π hπO hπ0).family.act (u₀, j₀) z) := rfl
      rw [hstep, hu]
      have hact : (FM.toModel ε π hπO hπ0).family.act (u₀, j₀) z =
          FM.mult π u₀ j₀ ⋆ z := by
        rw [UnitPrimeModel.family_apply, FM.toModel_mult]
      rw [hact, ← mulC_assoc, FM.mult_mul]

/-- The multiplier form used by the tower lemma. -/
lemma mult_eq (π : K) (u : 𝒪ˣ) (j : ℕ) (z : Pt) :
    FM.mult π u j ⋆ z = powC (FM.σ π) j ⋆ (FM.σ (((u : 𝒪) : K)) ⋆ z) := by
  show FM.σ (((u : 𝒪) : K)) ⋆ powC (FM.σ π) j ⋆ z =
    powC (FM.σ π) j ⋆ (FM.σ (((u : 𝒪) : K)) ⋆ z)
  rw [← mulC_assoc, mulC_comm (FM.σ (((u : 𝒪) : K))) (powC (FM.σ π) j), mulC_assoc]

/-- **The orbit avoidance of Theorem 3.6.**  No element of the semigroup orbit of
an uncovered point lies in the open set `W` of Lemma 3.8. -/
theorem orbit_avoid (ε : 𝒪ˣ) (π : K) (m : ℕ) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0)
    (hpadic : ∀ (j : ℕ) (g : 𝒪), ∃ k : ℕ, ∃ h ∈ 𝒪,
      (1 + π ^ m * ((g : 𝒪) : K)) - ((ε : 𝒪) : K) ^ k = π ^ (m + j) * h)
    {y : Pt} (hy : y ∈ uncovered 𝒪 Nm FM.σ) (l : List (𝒪ˣ × ℕ)) :
    (FM.toModel ε π hπO hπ0).applyList l y ∉ FM.W π m := by
  obtain ⟨u, j, hu⟩ := FM.applyList_form ε π hπO hπ0 l
  rw [hu y, FM.mult_eq]
  intro hmem
  exact FM.tower ε π m j hπO hπ0 (hpadic j) hmem (FM.uncovered_actU u hy)

/-! ## The remaining hypotheses of Theorem 3.6, proved -/

/-- The unit multiplier of `ε ^ n`. -/
lemma toModel_actU (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (n : ℕ) (z : Pt) :
    (FM.toModel ε π hπO hπ0).actU (ε ^ n) z =
      FM.σ (((ε : 𝒪) : K) ^ n) ⋆ z := by
  rw [UnitPrimeModel.actU_apply]
  congr 1

/-- `μ_{εⁿ}` has no nonzero fixed vector. -/
theorem actU_eq_self {ε : 𝒪ˣ} {π : K} (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) {n : ℕ}
    (hεpow : (ε : K) ^ n ≠ 1) {z : Pt}
    (h : (FM.toModel ε π hπO hπ0).actU (ε ^ n) z = z) : z = 0 := by
  have hcoe : (((ε : 𝒪) : K)) ^ n = (ε : K) ^ n := rfl
  have hz : FM.σ ((((ε : 𝒪) : K)) ^ n - 1) ⋆ z = 0 := by
    have h1 : FM.σ ((((ε : 𝒪) : K)) ^ n) ⋆ z = z := by
      rw [← FM.toModel_actU ε π hπO hπ0 n z]
      exact h
    have h2 : ((((ε : 𝒪) : K)) ^ n - 1) ≠ 0 := by
      rw [hcoe]; exact sub_ne_zero.mpr hεpow
    rw [FM.σ_sub, FM.σ_one, sub_mulC, h1, oneC_mulC, sub_self]
  have hnorm : normR (FM.σ ((((ε : 𝒪) : K)) ^ n - 1)) ≠ 0 := by
    intro hzero
    have h1 : |normR (FM.σ ((((ε : 𝒪) : K)) ^ n - 1))| = 0 := by rw [hzero, abs_zero]
    rw [FM.normR_abs] at h1
    have h2 : Nm ((((ε : 𝒪) : K)) ^ n - 1) = 0 := by exact_mod_cast h1
    have h3 : ((((ε : 𝒪) : K)) ^ n - 1) = 0 := (AbsNorm.eq_zero_iff Nm).mp h2
    exact (sub_ne_zero.mpr (by rw [hcoe]; exact hεpow)) h3
  exact mulC_eq_zero hnorm hz

omit FM in
/-- `(εⁿ - 1) ≠ 0`. -/
theorem denom_ne_zero {ε : 𝒪ˣ} {n : ℕ} (hεpow : (ε : K) ^ n ≠ 1) :
    (ε : K) ^ n - 1 ≠ 0 :=
  sub_ne_zero.mpr hεpow

/-- The unit action on `σ`-images is multiplication in `K`. -/
theorem actU_hact (ε : 𝒪ˣ) (π : K) (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (z : K) (n : ℕ) :
    (FM.toModel ε π hπO hπ0).actU (ε ^ n) (FM.σ z) =
      FM.σ (((ε : 𝒪) : K) ^ n * z) := by
  rw [FM.toModel_actU, ← FM.σ_mul]

/-- `W` is nonempty. -/
theorem W_nonempty (π : K) (m : ℕ) (hπ0 : π ≠ 0) : (FM.W π m).Nonempty := by
  have hp : (0 : ℝ) < ((Nm (π ^ m) : ℚ≥0) : ℝ) := by
    have h : Nm (π ^ m) ≠ 0 := (AbsNorm.ne_zero_iff Nm).mpr (pow_ne_zero _ hπ0)
    exact_mod_cast (zero_lt_iff.mpr h)
  refine ⟨FM.σ ((((0 : 𝒪)) : K) + (π ^ m)⁻¹), ?_⟩
  rw [mem_W]
  refine ⟨0, ?_⟩
  have h0 : FM.σ ((((0 : 𝒪)) : K) + (π ^ m)⁻¹) -
      FM.σ ((((0 : 𝒪)) : K) + (π ^ m)⁻¹) = 0 := sub_self _
  rw [h0]
  simpa [normR] using (inv_pos.mpr hp)

/-! ## Lemma 3.7 as the `p`-adic input of the tower argument

`Padic.lean` proves Lemma 3.7 in its residue form `lem_padic`.  The two lemmas
below show that the `p`-adic hypothesis of `tower` is exactly its conclusion:
the unit condition `lem_padic` asks for is automatic (a `p`-adic multiple of a
unit is nilpotent in `ZMod (p^s)`), and the residue of `1 + π^m g` has the
required shape `1 + p^m v` as soon as `π` maps into `p` times a unit.

What is *not* constructed here is the residue isomorphism `e` itself, i.e. that a
degree-one unramified prime of `𝒪` gives `𝒪 ⧸ π^s ≃ ZMod (p^s)`; that needs the
factorization theory of ideals in a Dedekind domain. -/

omit FM in
/-- The residue of `1 + π^m g` is of the form `1 + p^m v` as soon as `π` maps
into `p` times a unit. -/
theorem res_one_add (p j m : ℕ) (π : 𝒪)
    (e : (𝒪 ⧸ Ideal.span {π ^ (j + m)}) ≃+* ZMod (p ^ (j + m)))
    (hπ : ∃ w : ℤ, e (Ideal.Quotient.mk _ π) = (p : ZMod (p ^ (j + m))) * w)
    (g : 𝒪) :
    ∃ v : ℤ, e (Ideal.Quotient.mk _ (1 + π ^ m * g)) =
      1 + (p : ZMod (p ^ (j + m))) ^ m * v := by
  obtain ⟨w, hw⟩ := hπ
  refine ⟨(w ^ m * e (Ideal.Quotient.mk _ g)).cast, ?_⟩
  rw [ZMod.intCast_zmod_cast]
  simp only [map_add, map_one, map_mul, map_pow, hw, mul_pow]
  ring

omit FM in
/-- **Lemma 3.7 as used in the tower argument**: every `1 + π^m g` is congruent
to a power of `ε` modulo `π^(m+j)`. -/
theorem padic_step (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (ε : 𝒪ˣ) (π : 𝒪)
    (m j : ℕ) (hm : 0 < m)
    (e : (𝒪 ⧸ Ideal.span {π ^ (j + m)}) ≃+* ZMod (p ^ (j + m)))
    (he : ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      e (Ideal.Quotient.mk _ ((ε : 𝒪) ^ (p - 1))) =
        (1 + (p : ZMod (p ^ (j + m))) ^ m * u))
    (hres : ∀ g : 𝒪, ∃ v : ℤ, e (Ideal.Quotient.mk _ (1 + π ^ m * g)) =
      1 + (p : ZMod (p ^ (j + m))) ^ m * v)
    (g : 𝒪) :
    ∃ k : ℕ, ∃ h : 𝒪, (1 + π ^ m * g) - ((ε : 𝒪)) ^ k = π ^ (j + m) * h := by
  obtain ⟨v, hv⟩ := hres g
  refine lem_padic 𝒪 p hp hpodd j m hm π ε (1 + π ^ m * g) e he ⟨v, hv⟩ ?_
  rw [hv]
  exact zmod_unit_one_add_pow p (j + m) m (by omega) (by omega) v

omit FM in
/-- **Lemma 3.7 with only the prime-residue hypothesis**: if `π` maps into `p`
times a unit modulo `π^(m+j)`, then every `1 + π^m g` is congruent to a power of
`ε` modulo `π^(m+j)`. -/
theorem padic_step_of_prime (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (ε : 𝒪ˣ) (π : 𝒪)
    (m j : ℕ) (hm : 0 < m)
    (e : (𝒪 ⧸ Ideal.span {π ^ (j + m)}) ≃+* ZMod (p ^ (j + m)))
    (he : ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      e (Ideal.Quotient.mk _ ((ε : 𝒪) ^ (p - 1))) =
        (1 + (p : ZMod (p ^ (j + m))) ^ m * u))
    (hπ : ∃ w : ℤ, e (Ideal.Quotient.mk _ π) = (p : ZMod (p ^ (j + m))) * w)
    (g : 𝒪) :
    ∃ k : ℕ, ∃ h : 𝒪, (1 + π ^ m * g) - ((ε : 𝒪)) ^ k = π ^ (j + m) * h :=
  padic_step p hp hpodd ε π m j hm e he (fun g => res_one_add p j m π e hπ g) g

end FieldModel

end CubicTwoStage
