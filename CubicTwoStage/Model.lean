/-
# The model algebra `ℝ × ℂ` on the model space

The paper multiplies points of `ℝ × ℂ` by `σ(b)`, and the norm form
`Nm(u,w) = u|w|²` is multiplicative for that product.  The model space
`Pt = Fin 3 → ℝ` is therefore *not* used with its coordinatewise ring structure
(which is `ℝ³`, three real places) but with the product algebra `ℝ × ℂ`:
the first coordinate is the real multiplicity and the last two are the real and
imaginary parts of the complex one.

This file defines that multiplication (`mulC`), its inverse on units, its
powers, the induced real-linear maps, and proves that `normR` is multiplicative
for it — the identity `|(a₀,b₀)(a₁,b₁)| = |a₀||a₁| + …` that the paper uses
when it says multiplication by `σ(b)` scales the region `V(q)` by `|Nm b|`.
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

/-! ## The product algebra -/

/-- Multiplication in `ℝ × ℂ`, in the coordinates of `Pt`. -/
def mulC (a b : Pt) : Pt :=
  ![a 0 * b 0, a 1 * b 1 - a 2 * b 2, a 1 * b 2 + a 2 * b 1]

/-- The unit of the model algebra, `(1, 1)`. -/
def oneC : Pt := ![1, 1, 0]

/-- Inversion in `ℝ × ℂ`, with junk value at non-units (the formula is total,
and is an inverse exactly when `normR ≠ 0`). -/
noncomputable def invC (a : Pt) : Pt :=
  ![(a 0)⁻¹, a 1 / (a 1 ^ 2 + a 2 ^ 2), -a 2 / (a 1 ^ 2 + a 2 ^ 2)]

infixl:70 " ⋆ " => mulC

@[simp] lemma mulC_apply_zero (a b : Pt) : (a ⋆ b) 0 = a 0 * b 0 := by
  simp [mulC]

@[simp] lemma mulC_apply_one (a b : Pt) : (a ⋆ b) 1 = a 1 * b 1 - a 2 * b 2 := by
  simp [mulC]

@[simp] lemma mulC_apply_two (a b : Pt) : (a ⋆ b) 2 = a 1 * b 2 + a 2 * b 1 := by
  simp [mulC]

@[simp] lemma oneC_apply_zero : oneC 0 = 1 := by simp [oneC]
@[simp] lemma oneC_apply_one : oneC 1 = 1 := by simp [oneC]
@[simp] lemma oneC_apply_two : oneC 2 = 0 := by simp [oneC]

@[simp] lemma invC_apply_zero (a : Pt) : invC a 0 = (a 0)⁻¹ := by simp [invC]
@[simp] lemma invC_apply_one (a : Pt) : invC a 1 = a 1 / (a 1 ^ 2 + a 2 ^ 2) := by
  simp [invC]
@[simp] lemma invC_apply_two (a : Pt) : invC a 2 = -a 2 / (a 1 ^ 2 + a 2 ^ 2) := by
  simp [invC]

lemma mulC_assoc (a b c : Pt) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  funext i; fin_cases i <;> simp <;> ring

lemma mulC_comm (a b : Pt) : a ⋆ b = b ⋆ a := by
  funext i; fin_cases i <;> simp <;> ring

/-- Rearrangement of a product of two products. -/
theorem mulC_mul_mul_comm (a b c d : Pt) : (a ⋆ b) ⋆ (c ⋆ d) = (a ⋆ c) ⋆ (b ⋆ d) := by
  rw [mulC_assoc a b (c ⋆ d), ← mulC_assoc b c d, mulC_comm b c, mulC_assoc c b d,
    ← mulC_assoc a c (b ⋆ d)]

lemma mulC_add (a b c : Pt) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  funext i; fin_cases i <;> simp <;> ring

lemma mulC_sub (a b c : Pt) : a ⋆ (b - c) = a ⋆ b - a ⋆ c := by
  funext i; fin_cases i <;> simp <;> ring

lemma add_mulC (a b c : Pt) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  rw [mulC_comm, mulC_add, mulC_comm c b, mulC_comm c a, mulC_comm]

lemma sub_mulC (a b c : Pt) : (a - b) ⋆ c = a ⋆ c - b ⋆ c := by
  funext i; fin_cases i <;> simp <;> ring

lemma zero_mulC (a : Pt) : (0 : Pt) ⋆ a = 0 := by
  funext i; fin_cases i <;> simp

lemma mulC_zero (a : Pt) : a ⋆ 0 = 0 := by rw [mulC_comm, zero_mulC]

lemma mulC_oneC (a : Pt) : a ⋆ oneC = a := by
  funext i; fin_cases i <;> simp

lemma oneC_mulC (a : Pt) : oneC ⋆ a = a := by rw [mulC_comm, mulC_oneC]

lemma mulC_smul (r : ℝ) (a b : Pt) : (r • a) ⋆ b = r • (a ⋆ b) := by
  funext i; fin_cases i <;> simp <;> ring

lemma smul_mulC (r : ℝ) (a b : Pt) : a ⋆ (r • b) = r • (a ⋆ b) := by
  rw [mulC_comm, mulC_smul, mulC_comm]

/-! ## The norm form is multiplicative -/

/-- `normR` is multiplicative for the model algebra: this is
`(a₀|a₁|²)(b₀|b₁|²) = (a₀b₀)|a₁b₁|²`, i.e. the multiplicativity of the
absolute norm of `ℝ × ℂ`. -/
theorem normR_mulC (a b : Pt) : normR (a ⋆ b) = normR a * normR b := by
  simp only [normR, mulC_apply_zero, mulC_apply_one, mulC_apply_two]
  ring

theorem normR_oneC : normR oneC = 1 := by
  simp [normR, oneC]

/-- `normR` vanishes exactly at the zero divisors of `ℝ × ℂ`. -/
theorem normR_eq_zero_iff (a : Pt) :
    normR a = 0 ↔ a 0 = 0 ∨ (a 1 = 0 ∧ a 2 = 0) := by
  simp only [normR]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl h'
    · right
      constructor <;> nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]
  · rintro (h | ⟨h1, h2⟩)
    · simp [h]
    · simp [h1, h2]

lemma zero_ne_of_normR {a : Pt} (ha : normR a ≠ 0) : a 0 ≠ 0 :=
  fun h => ha ((normR_eq_zero_iff a).mpr (Or.inl h))

lemma sq_add_sq_ne_zero_of_normR {a : Pt} (ha : normR a ≠ 0) :
    a 1 ^ 2 + a 2 ^ 2 ≠ 0 := by
  intro h
  refine ha ((normR_eq_zero_iff a).mpr (Or.inr ⟨?_, ?_⟩))
  · nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]
  · nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]

/-- The units of `ℝ × ℂ` are exactly the elements of nonzero norm form. -/
theorem mulC_inv (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) :
    a ⋆ invC a = oneC := by
  funext i; fin_cases i <;> simp <;> field_simp <;> ring

theorem invC_mulC (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) :
    invC a ⋆ a = oneC := by
  rw [mulC_comm]; exact mulC_inv a h0 h1

theorem normR_invC (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) :
    normR (invC a) = (normR a)⁻¹ := by
  simp only [normR, invC_apply_zero, invC_apply_one, invC_apply_two]
  field_simp

/-- An element of nonzero norm form can be cancelled. -/
theorem mulC_cancel_left {a b c : Pt} (ha : normR a ≠ 0) (h : a ⋆ b = a ⋆ c) :
    b = c := by
  have hinv : invC a ⋆ a = oneC :=
    invC_mulC a (zero_ne_of_normR ha) (sq_add_sq_ne_zero_of_normR ha)
  calc b = oneC ⋆ b := (oneC_mulC b).symm
    _ = (invC a ⋆ a) ⋆ b := by rw [hinv]
    _ = invC a ⋆ (a ⋆ b) := mulC_assoc _ _ _
    _ = invC a ⋆ (a ⋆ c) := by rw [h]
    _ = (invC a ⋆ a) ⋆ c := (mulC_assoc _ _ _).symm
    _ = oneC ⋆ c := by rw [hinv]
    _ = c := oneC_mulC c

/-- An element of nonzero norm form is not a zero divisor on the right. -/
theorem mulC_eq_zero {a b : Pt} (ha : normR a ≠ 0) (h : a ⋆ b = 0) : b = 0 := by
  have h' : a ⋆ b = a ⋆ 0 := by rw [h, mulC_zero]
  exact mulC_cancel_left ha h'

/-! ## Powers -/

/-- The `n`-th power in the model algebra. -/
noncomputable def powC (a : Pt) (n : ℕ) : Pt := (mulC a)^[n] oneC

@[simp] lemma powC_zero (a : Pt) : powC a 0 = oneC := rfl

lemma powC_succ (a : Pt) (n : ℕ) : powC a (n + 1) = a ⋆ powC a n := by
  show (mulC a)^[n + 1] oneC = mulC a ((mulC a)^[n] oneC)
  rw [Function.iterate_succ_apply']

/-- Multiplication by the `n`-th power is the `n`-th iterate of the
multiplication. -/
theorem powC_mulC (a b : Pt) (n : ℕ) : powC a n ⋆ b = (mulC a)^[n] b := by
  induction n with
  | zero => simpa using oneC_mulC b
  | succ n ih =>
      rw [powC_succ, Function.iterate_succ_apply', ← ih]
      exact mulC_assoc a (powC a n) b

lemma powC_oneC (n : ℕ) : powC oneC n = oneC := by
  induction n with
  | zero => simp [powC]
  | succ n ih => rw [powC_succ, ih, mulC_oneC]

/-- Powers of a product are the product of the powers. -/
theorem powC_mul_powC (a b : Pt) (n : ℕ) : powC a n ⋆ powC b n = powC (a ⋆ b) n := by
  induction n with
  | zero => simp [powC, mulC_oneC]
  | succ n ih =>
      rw [powC_succ, powC_succ, powC_succ, mulC_mul_mul_comm, ih]

theorem normR_powC (a : Pt) (n : ℕ) : normR (powC a n) = (normR a) ^ n := by
  induction n with
  | zero => simp [powC, normR_oneC]
  | succ n ih => rw [powC_succ, normR_mulC, ih, pow_succ, mul_comm]

/-! ## The induced real-linear maps -/

/-- Multiplication by `a` as a real-linear endomorphism of the model space. -/
noncomputable def linC (a : Pt) : Pt →ₗ[ℝ] Pt where
  toFun := fun x => a ⋆ x
  map_add' := fun x y => mulC_add a x y
  map_smul' := fun r x => smul_mulC r a x

@[simp] lemma linC_apply (a x : Pt) : linC a x = a ⋆ x := rfl

theorem continuous_mulC (a : Pt) : Continuous fun x => a ⋆ x := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · change Continuous fun x : Pt => a 0 * x 0
    exact continuous_const.mul (continuous_apply 0)
  · change Continuous fun x : Pt => a 1 * x 1 - a 2 * x 2
    exact (continuous_const.mul (continuous_apply 1)).sub
      (continuous_const.mul (continuous_apply 2))
  · change Continuous fun x : Pt => a 1 * x 2 + a 2 * x 1
    exact (continuous_const.mul (continuous_apply 2)).add
      (continuous_const.mul (continuous_apply 1))

theorem continuous_linC (a : Pt) : Continuous (linC a) :=
  continuous_mulC a

/-- Multiplication by a unit of the model algebra is a linear equivalence. -/
noncomputable def linEquivC (a : Pt) (h0 : a 0 ≠ 0) (h1 : a 1 ^ 2 + a 2 ^ 2 ≠ 0) : Pt ≃ₗ[ℝ] Pt where
  toFun := fun x => a ⋆ x
  invFun := fun x => invC a ⋆ x
  map_add' := fun x y => mulC_add a x y
  map_smul' := fun r x => smul_mulC r a x
  left_inv := by
    intro x
    show invC a ⋆ (a ⋆ x) = x
    rw [← mulC_assoc, invC_mulC a h0 h1, oneC_mulC]
  right_inv := by
    intro x
    show a ⋆ (invC a ⋆ x) = x
    rw [← mulC_assoc, mulC_inv a h0 h1, oneC_mulC]

/-- An element of nonzero norm form is a unit of the model algebra. -/
theorem exists_invC {a : Pt} (ha : normR a ≠ 0) : ∃ b : Pt, a ⋆ b = oneC :=
  ⟨invC a, mulC_inv a (zero_ne_of_normR ha) (sq_add_sq_ne_zero_of_normR ha)⟩

/-! ## Integer powers of a unit -/

/-- The `n`-th power of the linear equivalence `(mulC c)` acts by `powC c n`. -/
lemma linEquivC_np (c : Pt) (h0 : c 0 ≠ 0) (h1 : c 1 ^ 2 + c 2 ^ 2 ≠ 0) (n : ℕ)
    (x : Pt) : (linEquivC c h0 h1 ^ n) x = powC c n ⋆ x := by
  induction n generalizing x with
  | zero => simp [powC_zero, oneC_mulC]
  | succ n ih =>
      have hstep : (linEquivC c h0 h1 ^ (n + 1)) x =
          (linEquivC c h0 h1 ^ n) (linEquivC c h0 h1 x) := by
        rw [pow_succ, LinearEquiv.mul_apply]
      rw [hstep, ih]
      show powC c n ⋆ (c ⋆ x) = powC c (n + 1) ⋆ x
      rw [← mulC_assoc, mulC_comm (powC c n) c, powC_succ, mulC_assoc]

/-- Integer powers of a linear equivalence that is left-multiplication by `c`,
in terms of the inverse multiplier `c'`. -/
lemma mulC_zpow (c c' : Pt) (e : Pt ≃ₗ[ℝ] Pt)
    (he : ∀ x, e x = c ⋆ x) (heinv : ∀ x, (e⁻¹) x = c' ⋆ x) (hinv : c ⋆ c' = oneC)
    (l : ℤ) (x : Pt) :
    (e ^ l) x = (if 0 ≤ l then powC c l.natAbs else powC c' l.natAbs) ⋆ x := by
  have hp : ∀ n : ℕ, ∀ x : Pt, (e ^ n) x = powC c n ⋆ x := by
    intro n
    induction n with
    | zero => intro x; simp [powC_zero, oneC_mulC]
    | succ n ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, ih (e x), he, ← mulC_assoc,
          mulC_comm (powC c n) c, powC_succ, mulC_assoc]
  have hi : ∀ n : ℕ, ∀ x : Pt, ((e⁻¹) ^ n) x = powC c' n ⋆ x := by
    intro n
    induction n with
    | zero => intro x; simp [powC_zero, oneC_mulC]
    | succ n ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, ih ((e⁻¹) x), heinv, ← mulC_assoc,
          mulC_comm (powC c' n) c', powC_succ, mulC_assoc]
  by_cases hl : 0 ≤ l
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    rw [if_pos (Int.natCast_nonneg n)]
    simpa using hp n x
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp hl)
    have hif : ¬ (0 ≤ (Int.negSucc n : ℤ)) := by
      have hneg : (Int.negSucc n : ℤ) = -(n + 1) := by rfl
      rw [hneg]
      omega
    rw [if_neg hif]
    show (e ^ (-(n + 1 : ℤ))) x = powC c' (n + 1) ⋆ x
    have hleft : (e ^ (↑n + 1 : ℤ)) ((e ^ (-(↑n + 1 : ℤ))) x) = x := by
      rw [← LinearEquiv.mul_apply, ← zpow_add]
      simp
    have hright : (e ^ (↑n + 1 : ℤ)) (powC c' (n + 1) ⋆ x) = x := by
      show (e ^ (n + 1 : ℕ)) (powC c' (n + 1) ⋆ x) = x
      rw [hp, ← mulC_assoc, powC_mul_powC, hinv, powC_oneC, oneC_mulC]
    exact (e ^ (↑n + 1 : ℤ)).injective (by rw [hleft, hright])

end CubicTwoStage
