/-
**Lemma 5.1** (the box bound) and **Lemma 8.2** (its form in degree `n`).
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

open Finset

variable {n : ℕ}

/-- Error term of the box bound: half the side times the `ℓ¹` norm of the row. -/
noncomputable def boxRad (m : Fin n → ℝ) (h : ℝ) : ℝ := h / 2 * ∑ j, |m j|

/-- If `x` is in a cube of centre `a` and side `h`, then any linear form is
within `boxRad` of its value at the centre.  This is the only analytic input of
Lemma 5.1. -/
theorem abs_linearForm_sub_le (m x a : Fin n → ℝ) {h : ℝ} (_hh : 0 ≤ h)
    (hx : ∀ j, |x j - a j| ≤ h / 2) :
    |∑ j, m j * (x j - a j)| ≤ boxRad m h := by
  unfold boxRad
  calc |∑ j, m j * (x j - a j)| ≤ ∑ j, |m j * (x j - a j)| := abs_sum_le_sum_abs _ _
    _ = ∑ j, |m j| * |x j - a j| := by simp only [abs_mul]
    _ ≤ ∑ j, |m j| * (h / 2) :=
        sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = h / 2 * ∑ j, |m j| := by rw [← sum_mul, mul_comm]

/-- The upper bounds `A_i` of Lemma 5.1. -/
noncomputable def boxAub (M : Fin n → Fin n → ℝ) (aB ac : Fin n → ℝ) (h : ℝ) (i : Fin n) : ℝ :=
  |∑ j, M i j * (aB j - ac j)| + boxRad (M i) h

/-- The lower bounds `a_i` of Lemma 5.1. -/
noncomputable def boxAlb (M : Fin n → Fin n → ℝ) (aB ac : Fin n → ℝ) (h : ℝ) (i : Fin n) : ℝ :=
  max (|∑ j, M i j * (aB j - ac j)| - boxRad (M i) h) 0

/-- Coordinate-wise form of both box lemmas: if each coordinate of `σ(x) - σ(c)`
is enclosed in `[a_i, A_i]` then the norm is bracketed accordingly.  For a
complex place the two coordinates are the real and the imaginary part, so that
`∏ |z_i|` is exactly `|Nm|`. -/
theorem norm_bracket {ι : Type*} [Fintype ι] (z a A : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hlo : ∀ i, a i ≤ |z i|) (hhi : ∀ i, |z i| ≤ A i) :
    (∏ i, a i) ≤ |∏ i, z i| ∧ |∏ i, z i| ≤ ∏ i, A i := by
  rw [abs_prod]
  constructor
  · exact prod_le_prod (fun i _ => ha i) (fun i _ => hlo i)
  · exact prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hhi i)

/-- **Lemma 5.1**.  Let `M` be the matrix of `σ` in the integral basis (rows
`σ₁`, `Re σ₂`, `Im σ₂`), `B` a cube of side `h` and centre `a_B` in lattice
coordinates, and `c` a centre with lattice coordinates `a_c`.  Put

  `A_i = |m_i·(a_B-a_c)| + (h/2)∑_j|m_ij|`,
  `a_i = max(|m_i·(a_B-a_c)| - (h/2)∑_j|m_ij|, 0)`.

Then for every `x ∈ B`,

  `a₁(a₂²+a₃²) ≤ |Nm(σ(x)-σ(c))| ≤ A₁(A₂²+A₃²)`. -/
theorem lem_box (M : Fin 3 → Fin 3 → ℝ) (aB ac x : Fin 3 → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hx : ∀ j, |x j - aB j| ≤ h / 2) :
    let z : Fin 3 → ℝ := fun i => ∑ j, M i j * (x j - ac j)
    boxAlb M aB ac h 0 * (boxAlb M aB ac h 1 ^ 2 + boxAlb M aB ac h 2 ^ 2)
        ≤ |z 0 * (z 1 ^ 2 + z 2 ^ 2)|
      ∧ |z 0 * (z 1 ^ 2 + z 2 ^ 2)|
        ≤ boxAub M aB ac h 0 * (boxAub M aB ac h 1 ^ 2 + boxAub M aB ac h 2 ^ 2) := by
  intro z
  -- `z i - m_i·(a_B-a_c) = m_i·(x-a_B)`, so `z i` is within `boxRad` of the centre value
  have hsplit : ∀ i, z i = (∑ j, M i j * (aB j - ac j)) + ∑ j, M i j * (x j - aB j) := by
    intro i
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    ring
  have hdev : ∀ i, |z i - ∑ j, M i j * (aB j - ac j)| ≤ boxRad (M i) h := by
    intro i
    rw [hsplit i, add_sub_cancel_left]
    exact abs_linearForm_sub_le (M i) x aB hh hx
  have hc : ∀ i, ∑ j, M i j * (aB j - ac j) = z i - (z i - ∑ j, M i j * (aB j - ac j)) := by
    intro i; ring
  have hub : ∀ i, |z i| ≤ boxAub M aB ac h i := by
    intro i
    have := abs_add_le (∑ j, M i j * (aB j - ac j))
      (z i - ∑ j, M i j * (aB j - ac j))
    rw [add_sub_cancel] at this
    unfold boxAub
    linarith [hdev i, this]
  have hlb : ∀ i, boxAlb M aB ac h i ≤ |z i| := by
    intro i
    unfold boxAlb
    refine max_le ?_ (abs_nonneg _)
    have h1 : |∑ j, M i j * (aB j - ac j)| - |z i|
        ≤ |z i - ∑ j, M i j * (aB j - ac j)| := by
      have := abs_sub_abs_le_abs_sub (∑ j, M i j * (aB j - ac j)) (z i)
      rwa [abs_sub_comm] at this
    linarith [hdev i, h1]
  have h0 : ∀ i, 0 ≤ boxAlb M aB ac h i := fun i => le_max_right _ _
  -- reduce to the coordinate-wise bracket and finish with `nlinarith`
  have k1 := hlb 0; have k2 := hlb 1; have k3 := hlb 2
  have K1 := hub 0; have K2 := hub 1; have K3 := hub 2
  have p1 := h0 0; have p2 := h0 1; have p3 := h0 2
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z 1 ^ 2 + z 2 ^ 2),
    ← sq_abs (z 1), ← sq_abs (z 2)]
  simp only [pow_two]
  have A0 : 0 ≤ boxAub M aB ac h 0 := le_trans (abs_nonneg _) K1
  have A1 : 0 ≤ boxAub M aB ac h 1 := le_trans (abs_nonneg _) K2
  have A2 : 0 ≤ boxAub M aB ac h 2 := le_trans (abs_nonneg _) K3
  have s1 : boxAlb M aB ac h 1 * boxAlb M aB ac h 1 ≤ |z 1| * |z 1| :=
    mul_le_mul k2 k2 p2 (abs_nonneg _)
  have s2 : boxAlb M aB ac h 2 * boxAlb M aB ac h 2 ≤ |z 2| * |z 2| :=
    mul_le_mul k3 k3 p3 (abs_nonneg _)
  have S1 : |z 1| * |z 1| ≤ boxAub M aB ac h 1 * boxAub M aB ac h 1 :=
    mul_le_mul K2 K2 (abs_nonneg _) A1
  have S2 : |z 2| * |z 2| ≤ boxAub M aB ac h 2 * boxAub M aB ac h 2 :=
    mul_le_mul K3 K3 (abs_nonneg _) A2
  constructor
  · have h2 : boxAlb M aB ac h 1 * boxAlb M aB ac h 1
        + boxAlb M aB ac h 2 * boxAlb M aB ac h 2
        ≤ |z 1| * |z 1| + |z 2| * |z 2| := by linarith
    calc boxAlb M aB ac h 0 * (boxAlb M aB ac h 1 * boxAlb M aB ac h 1
          + boxAlb M aB ac h 2 * boxAlb M aB ac h 2)
        ≤ |z 0| * (|z 1| * |z 1| + |z 2| * |z 2|) :=
          mul_le_mul k1 h2 (by positivity) (abs_nonneg _)
      _ = |z 0| * (|z 1| * |z 1| + |z 2| * |z 2|) := by ring
  · have h2 : |z 1| * |z 1| + |z 2| * |z 2|
        ≤ boxAub M aB ac h 1 * boxAub M aB ac h 1
          + boxAub M aB ac h 2 * boxAub M aB ac h 2 := by linarith
    calc |z 0| * (|z 1| * |z 1| + |z 2| * |z 2|)
        ≤ boxAub M aB ac h 0 * (boxAub M aB ac h 1 * boxAub M aB ac h 1
          + boxAub M aB ac h 2 * boxAub M aB ac h 2) :=
          mul_le_mul K1 h2 (by positivity) A0
      _ = boxAub M aB ac h 0 * (boxAub M aB ac h 1 * boxAub M aB ac h 1
          + boxAub M aB ac h 2 * boxAub M aB ac h 2) := by ring

/-- **Lemma 8.2**.  In degree `n` with `r₁` real places and `r₂` complex ones,
the same bracket holds for the full product, i.e. for `|Nm|`; only the shape of
the bound changes, not its proof.  Here the index set is the disjoint union of
the real coordinates and the two coordinates attached to each complex place. -/
theorem lem_gen_box {ι : Type*} [Fintype ι] (z a A : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hlo : ∀ i, a i ≤ |z i|) (hhi : ∀ i, |z i| ≤ A i) :
    (∏ i, a i) ≤ |∏ i, z i| ∧ |∏ i, z i| ≤ ∏ i, A i :=
  norm_bracket z a A ha hlo hhi

end CubicTwoStage
