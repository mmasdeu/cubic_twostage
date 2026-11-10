/-
# Berend §4, Lemma 4.4: the logarithmic growth-rate comparison

This module implements the *rate-comparison* content of Lemma 4.4 of

* D. Berend, *Multi-invariant sets on tori*, Trans. Amer. Math. Soc. **280** (1983),
  Theorem 2.1 and §4,

in the diagonalized model of `CubicTwoStage/BerendSec4.lean` (plan §C.5, the
step between Lemma 4.3 and the rank-two independence).

## The mathematical content

`BerendSec4.exists_minimal_and_expanding` produces a minimal accumulating
coordinate set `S` and one family member `diag μ` that is *uniformly expanding*
on `S` (`1 < |μ k|` for `k ∈ S`).  `BerendSec4.dichotomy` (Lemma 4.2) then says
that every single family member either expands all of `S` or is nonexpanding on
all of `S`.  What both leave open is the *strictly contracting* case: a member
`ν` with `|ν k| ≤ 1` on `S` and `|ν i| < 1` at some `i ∈ S`.

Berend's Lemma 4.4 replaces the single map by a composite `σ^m · r^n` (the
paper's "replace σ by σ^m r") and compares the two *logarithmic growth-rate
vectors*

  `A k = log |μ k|`,  `C k = log |ν k|`.

The arithmetic heart is the following observation, proved here with no
topological input (`exists_nat_mixed_of_rates`, `exists_mixed_pow`): if the two
rate vectors are **not proportional**, then some composite `μ^m ν^n` with
`m, n > 0` *contracts* one of the two coordinates and *expands* the other.
Feeding that composite to `BerendSec4.acc_of_expanding` (Lemma 4.2's annulus
argument) produces accumulation of `E` at `0` inside a *proper* coordinate subset
of the minimal set `S` — which minimality forbids.

So a strictly contracting family member can exist on a minimal accumulating set
only when the two rate vectors *are* proportional at every coordinate: the
"common ratios" alternative of Lemma 4.4.  That is formalised as
`log_rate_ratio_eq`: for every `j ∈ S`,

  `log |μ j| * log |ν i| = log |μ i| * log |ν j|`,

i.e. `log |ν j| = t · log |μ j|` with the *single* constant
`t = log |ν i| / log |μ i| < 0` for all `j ∈ S`.  In that case the whole
semigroup acts on `V_S` conformally (one rate per element), which is the
hypothesis under which the paper runs the rank-two argument on the full cone;
when `|S| = 1` there is no `j ≠ i` and the accepted one-dimensional theorem
`BerendRankTwoDiag.acc_coord_subset_sub` applies instead.  That is exactly the
"reduce the minimal coordinate subspace to one dimension, else common ratios"
dichotomy of plan §C.5.

## Trust

No `sorry`, no axiom, no import of `CubicTwoStage.Berend`; axioms are only
`propext`, `Classical.choice`, `Quot.sound`.
-/
import CubicTwoStage.BerendSec4

open Set Filter Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CubicTwoStage

namespace BerendRate

open BerendSec4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Composites of diagonal endomorphisms

The paper replaces `σ` by `σ^m · r^n`; in the diagonal model the composite is
again a diagonal map, with multiplier vector `fun k => μ k ^ m * ν k ^ n`. -/

/-- The composite of two diagonal maps is diagonal with the product multipliers. -/
theorem diag_comp_apply (mu nu : ι → ℝ) (m n : ℕ) (x : ι → ℝ) :
    diag (fun k => mu k ^ m * nu k ^ n) x = ((diag mu)^[m]) (((diag nu)^[n]) x) := by
  funext k
  rw [diag_apply, diag_iterate_apply, diag_iterate_apply]
  ring

/-- Invariance propagates to all forward iterates. -/
theorem diag_iterate_mem {E : Set (ι → ℝ)} {lam : ι → ℝ}
    (hinv : ∀ x ∈ E, diag lam x ∈ E) (k : ℕ) {x : ι → ℝ} (hx : x ∈ E) :
    ((diag lam)^[k]) x ∈ E := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih

/-- `E` is invariant under the composite `μ^m · ν^n` as soon as it is invariant
under `μ` and under `ν`.  This is the invariance part of Berend's "replace `σ`
by `σ^m r`". -/
theorem diag_comp_mem {E : Set (ι → ℝ)} {mu nu : ι → ℝ}
    (hmu : ∀ x ∈ E, diag mu x ∈ E) (hnu : ∀ x ∈ E, diag nu x ∈ E) (m n : ℕ) :
    ∀ x ∈ E, diag (fun k => mu k ^ m * nu k ^ n) x ∈ E := by
  intro x hx
  rw [diag_comp_apply]
  exact diag_iterate_mem hmu m (diag_iterate_mem hnu n hx)

/-- The modulus of a composite multiplier is the product of the moduli. -/
theorem abs_comp (mu nu : ι → ℝ) (m n : ℕ) (k : ι) :
    |mu k ^ m * nu k ^ n| = |mu k| ^ m * |nu k| ^ n := by
  rw [abs_mul, abs_pow, abs_pow]

/-! ## 2. The arithmetic core: mixed-sign composites

`exists_nat_mixed_of_rates` is the exact statement Berend's Lemma 4.4 needs:
given an expanding rate `B > 0` and a contracting rate `C < 0` in one
coordinate and arbitrary rates `A > 0`, `D` in a second one, non-proportionality
of the two rate vectors yields exponents `m, n > 0` for which the composite
contracts one coordinate and expands the other. -/

/-- A negative logarithmic size forces the product of powers to be below `1`. -/
theorem pow_mul_pow_lt_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {m n : ℕ}
    (h : (m : ℝ) * Real.log x + (n : ℝ) * Real.log y < 0) : x ^ m * y ^ n < 1 := by
  have hpos : 0 < x ^ m * y ^ n := by positivity
  have hlog : Real.log (x ^ m * y ^ n) = (m : ℝ) * Real.log x + (n : ℝ) * Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 : Real.log (x ^ m * y ^ n) < Real.log 1 := by
    rw [Real.log_one, hlog]; exact h
  exact (Real.log_lt_log_iff hpos one_pos).1 h1

/-- A positive logarithmic size forces the product of powers to exceed `1`. -/
theorem one_lt_pow_mul_pow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {m n : ℕ}
    (h : 0 < (m : ℝ) * Real.log x + (n : ℝ) * Real.log y) : 1 < x ^ m * y ^ n := by
  have hpos : 0 < x ^ m * y ^ n := by positivity
  have hlog : Real.log (x ^ m * y ^ n) = (m : ℝ) * Real.log x + (n : ℝ) * Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 : Real.log 1 < Real.log (x ^ m * y ^ n) := by
    rw [Real.log_one, hlog]; exact h
  exact (Real.log_lt_log_iff one_pos hpos).1 h1

/-- A rational in an interval of positive reals is a ratio `n / m` of positive
natural numbers.  (The exponents of a composite must be natural numbers, so the
rate comparison has to pass through rational approximation.) -/
theorem exists_nat_ratio_btwn {ρ τ : ℝ} (hρ : 0 ≤ ρ) (h : ρ < τ) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ρ < (n : ℝ) / (m : ℝ) ∧ (n : ℝ) / (m : ℝ) < τ := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h
  have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt hρ hr1
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr0
  have hnum : 0 < r.num := Rat.num_pos.mpr hrq
  have hnn : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    have h3 : ((r.num.natAbs : ℤ) : ℝ) = (r.num : ℝ) := by
      rw [Int.natCast_natAbs, abs_of_pos hnum]
    simpa using h3
  have hval : ((r.num.natAbs : ℝ)) / ((r.den : ℕ) : ℝ) = (r : ℝ) := by
    rw [hnn, ← r.cast_def]
  have hpos : 0 < r.num.natAbs := by
    have : (0 : ℤ) < r.num := hnum
    omega
  refine ⟨r.den, r.num.natAbs, r.den_pos, hpos, ?_, ?_⟩
  · rw [hval]; exact hr1
  · rw [hval]; exact hr2

/-- The construction behind Lemma 4.4: if the contracting rate `C < 0` is
relatively weaker than the expanding rate `A > 0` on the second coordinate, a
composite `μ^m ν^n` shrinks the first coordinate and grows the second. -/
theorem exists_nat_mixed_of_ratio {B C A D : ℝ} (hB : 0 < B) (hC : C < 0) (hD : D < 0)
    (hkey : B / (-C) < A / (-D)) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * B + (n : ℝ) * C < 0 ∧
      0 < (m : ℝ) * A + (n : ℝ) * D := by
  have hmC : (0 : ℝ) < -C := by linarith
  have hmD : (0 : ℝ) < -D := by linarith
  have hρ : 0 ≤ B / (-C) := le_of_lt (div_pos hB hmC)
  obtain ⟨m, n, hm, hn, hn1, hn2⟩ := exists_nat_ratio_btwn hρ hkey
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨m, n, hm, hn, ?_, ?_⟩
  · have h1 : B < ((n : ℝ) / (m : ℝ)) * (-C) := (div_lt_iff₀ hmC).1 hn1
    have h3 := mul_lt_mul_of_pos_left h1 hmR
    have h4 : (m : ℝ) * ((n : ℝ) / (m : ℝ) * (-C)) = (n : ℝ) * (-C) := by
      field_simp
    have h5 : (m : ℝ) * B < (n : ℝ) * (-C) := by rw [← h4]; exact h3
    linarith
  · have h1 : ((n : ℝ) / (m : ℝ)) * (-D) < A := (lt_div_iff₀ hmD).1 hn2
    have h3 := mul_lt_mul_of_pos_left h1 hmR
    have h4 : (m : ℝ) * ((n : ℝ) / (m : ℝ) * (-D)) = (n : ℝ) * (-D) := by
      field_simp
    have h5 : (n : ℝ) * (-D) < (m : ℝ) * A := by rw [← h4]; exact h3
    linarith

/-- **Rate comparison, logarithmic form.**  Let `A > 0` be an expanding rate,
`C < 0` a contracting one, and let `B > 0`, `D` be the rates in a second
coordinate.  If the rate vectors `(A, B)` and `(D, C)` are not proportional
(`A * C ≠ B * D`), then some composite of positive order has mixed signs: it
contracts one of the two coordinates and expands the other.

This is the arithmetic content of Berend's Lemma 4.4.  The hypothesis
`A * C ≠ B * D` *is* the assertion of "unequal logarithmic growth-rate ratios":
with `t = C / B < 0` the two vectors are proportional iff `A * C = B * D`. -/
theorem exists_nat_mixed_of_rates {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : C < 0)
    (hsep : A * C ≠ B * D) :
    (∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        (m : ℝ) * B + (n : ℝ) * C < 0 ∧ 0 < (m : ℝ) * A + (n : ℝ) * D) ∨
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        (m : ℝ) * A + (n : ℝ) * D < 0 ∧ 0 < (m : ℝ) * B + (n : ℝ) * C) := by
  rcases le_or_gt 0 D with hD | hD
  · -- the second rate is nonnegative: `m = 1` and a large `n` already work
    have hmC : (0 : ℝ) < -C := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (B / (-C))
    have hBdiv : 0 < B / (-C) := div_pos hB hmC
    have hnR : (0 : ℝ) < (n : ℝ) := lt_trans hBdiv hn
    have hnpos : 0 < n := by exact_mod_cast hnR
    refine Or.inl ⟨1, n, one_pos, hnpos, ?_, ?_⟩
    · have h2 : B < (n : ℝ) * (-C) := by
        have h := (div_lt_iff₀ hmC).1 hn
        linarith
      push_cast
      linarith
    · push_cast
      have h2 : (0 : ℝ) ≤ (n : ℝ) * D := mul_nonneg (le_of_lt hnR) hD
      linarith
  · have hmC : (0 : ℝ) < -C := by linarith
    have hmD : (0 : ℝ) < -D := by linarith
    rcases lt_or_gt_of_ne hsep with hlt | hgt
    · -- `A * C < B * D`: the composite contracts the `B`-coordinate
      have hkey : B / (-C) < A / (-D) := by
        rw [div_lt_div_iff₀ hmC hmD]
        linarith
      exact Or.inl (exists_nat_mixed_of_ratio hB hC hD hkey)
    · -- `B * D < A * C`: the composite contracts the `A`-coordinate
      have hkey : A / (-D) < B / (-C) := by
        rw [div_lt_div_iff₀ hmD hmC]
        linarith
      obtain ⟨m, n, hm, hn, h1, h2⟩ :=
        exists_nat_mixed_of_ratio (B := A) (C := D) (A := B) (D := C) hA hD hC hkey
      exact Or.inr ⟨m, n, hm, hn, h1, h2⟩

/-- **Rate comparison, power form.**  The same statement for the multipliers
themselves: if `a > 1`, `b > 1` are expanding moduli, `0 < c < 1` a contracting
one, `d > 0`, and the log-rate vectors are not proportional, then a composite
expands one of the two coordinates past `1` while shrinking the other below `1`.

This is the exact hypothesis shape of `BerendSec4.acc_of_expanding`, which needs
one composite multiplier `1 < |λ q|` on an expanding coordinate and `|λ p| < 1`
on a nonexpanding one. -/
theorem exists_mixed_pow {a b c d : ℝ} (ha : 1 < a) (hb : 1 < b) (hc0 : 0 < c)
    (hc1 : c < 1) (hd0 : 0 < d)
    (hsep : Real.log a * Real.log c ≠ Real.log b * Real.log d) :
    (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ 1 < a ^ m * d ^ n ∧ b ^ m * c ^ n < 1) ∨
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ 1 < b ^ m * c ^ n ∧ a ^ m * d ^ n < 1) := by
  have hA : 0 < Real.log a := Real.log_pos ha
  have hB : 0 < Real.log b := Real.log_pos hb
  have hC : Real.log c < 0 := Real.log_neg hc0 hc1
  rcases exists_nat_mixed_of_rates hA hB hC hsep with ⟨m, n, hm, hn, h1, h2⟩ |
    ⟨m, n, hm, hn, h1, h2⟩
  · refine Or.inl ⟨m, n, hm, hn, ?_, ?_⟩
    · exact one_lt_pow_mul_pow (by linarith : (0:ℝ) < a) hd0 h2
    · exact pow_mul_pow_lt_one (by linarith : (0:ℝ) < b) hc0 h1
  · refine Or.inr ⟨m, n, hm, hn, ?_, ?_⟩
    · exact one_lt_pow_mul_pow (by linarith : (0:ℝ) < b) hc0 h2
    · exact pow_mul_pow_lt_one (by linarith : (0:ℝ) < a) hd0 h1

/-! ## 3. The geometric step: non-proportional rates contradict minimality -/

/-- The composite step isolated: an invariant composite that expands at some
`q ∈ S` and contracts at some `p ∈ S` contradicts minimality of `S`. -/
theorem false_of_composite {E : Set (ι → ℝ)} (hE : IsClosed E) {S : Finset ι}
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {mu nu : ι → ℝ} (hmuinv : ∀ x ∈ E, diag mu x ∈ E) (hnuinv : ∀ x ∈ E, diag nu x ∈ E)
    {m n : ℕ} {p q : ι} (hpS : p ∈ S) (hqS : q ∈ S)
    (hexp : 1 < |mu q| ^ m * |nu q| ^ n) (hcontr : |mu p| ^ m * |nu p| ^ n < 1) :
    False := by
  classical
  set lam : ι → ℝ := fun k => mu k ^ m * nu k ^ n with hlam
  have hval : ∀ k, |lam k| = |mu k| ^ m * |nu k| ^ n := by
    intro k
    rw [hlam]
    exact abs_comp mu nu m n k
  have hinv : ∀ x ∈ E, diag lam x ∈ E := diag_comp_mem hmuinv hnuinv m n
  set T : Finset ι := S.filter (fun k => 1 < |lam k|) with hT
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hexpT : ∀ k ∈ T, 1 < |lam k| := fun k hk => (Finset.mem_filter.1 hk).2
  have hconT : ∀ k ∈ S, k ∉ T → |lam k| ≤ 1 := by
    intro k hkS hkT
    have h1 : ¬ (1 < |lam k|) := fun h => hkT (Finset.mem_filter.2 ⟨hkS, h⟩)
    linarith
  have hqT : q ∈ T := Finset.mem_filter.2 ⟨hqS, by rw [hval q]; exact hexp⟩
  have hpT : p ∉ T := by
    intro hp
    have h1 : 1 < |lam p| := (Finset.mem_filter.1 hp).2
    rw [hval p] at h1
    linarith
  have hTne : T.Nonempty := ⟨q, hqT⟩
  have hTssub : T ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hTS, ?_⟩
    intro heq
    exact hpT (heq ▸ hpS)
  have hnoAcc : ¬ Acc E (S \ T) := hmin (S \ T) (by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hq : q ∈ S \ T := by rw [heq]; exact hqS
    exact (Finset.mem_sdiff.1 hq).2 hqT)
  exact hmin T hTssub (acc_of_expanding hE hinv hTS hexpT hconT hTne hacc hnoAcc)

/-- **Lemma 4.4, geometric step.**  Let `E` be closed and invariant under two
family members `diag μ`, `diag ν` of the diagonal model, let `S` be a *minimal*
coordinate set in which `E` accumulates at `0`, and suppose `diag μ` is
uniformly expanding on `S`.  If `diag ν` contracts strictly at `p ∈ S` and the
two logarithmic rate vectors are not proportional at `p` and `q ∈ S`
(`q ≠ p`), then we reach a contradiction.

Proof (Berend's "replace `σ` by `σ^m r`"): `exists_mixed_pow` produces a
composite `λ = μ^m ν^n` that expands at `q` and contracts at `p`; `E` is
invariant under `diag λ`; `BerendSec4.acc_of_expanding` (Lemma 4.2's annulus
argument) then gives `Acc E T` for the nonempty set `T = {k ∈ S | 1 < |λ k|}`
of expanding coordinates; `T ⊊ S` because `p ∉ T`; minimality of `S` forbids
`Acc E T`. -/
theorem false_of_rate_separation {E : Set (ι → ℝ)} (hE : IsClosed E) {S : Finset ι}
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {mu nu : ι → ℝ} (hmuinv : ∀ x ∈ E, diag mu x ∈ E) (hnuinv : ∀ x ∈ E, diag nu x ∈ E)
    (hmu : ∀ k ∈ S, 1 < |mu k|)
    {p q : ι} (hpS : p ∈ S) (hqS : q ∈ S)
    (hnp0 : nu p ≠ 0) (hnp : |nu p| < 1) (hnq : nu q ≠ 0)
    (hsep : Real.log |mu q| * Real.log |nu p| ≠ Real.log |mu p| * Real.log |nu q|) :
    False := by
  classical
  have hnp0' : 0 < |nu p| := abs_pos.2 hnp0
  have hnq0 : 0 < |nu q| := abs_pos.2 hnq
  rcases exists_mixed_pow (a := |mu q|) (b := |mu p|) (c := |nu p|) (d := |nu q|)
      (hmu q hqS) (hmu p hpS) hnp0' hnp hnq0 hsep with
    ⟨m, n, hm, hn, hexp, hcontr⟩ | ⟨m, n, hm, hn, hexp, hcontr⟩
  · exact false_of_composite hE hacc hmin hmuinv hnuinv hpS hqS hexp hcontr
  · exact false_of_composite hE hacc hmin hmuinv hnuinv hqS hpS hexp hcontr

/-! ## 4. The "common ratios" alternative of Lemma 4.4 -/

/-- **Lemma 4.4, conclusion.**  In the situation of Lemma 4.2 with a minimal
accumulating coordinate set `S` on which `diag μ` expands uniformly, any family
member `diag ν` that is strictly contracting at some `p ∈ S` must have
*proportional* logarithmic growth rates on all of `S`:

  `log |μ j| * log |ν p| = log |μ p| * log |ν j|`   for every `j ∈ S`.

Equivalently `log |ν j| = t · log |μ j|` for all `j` with the single constant
`t = log |ν p| / log |μ p| < 0`.  So either `|S| = 1` (one-dimensional minimal
subspace, where `BerendRankTwoDiag` applies) or the semigroup acts on `V_S` with
a single rate per element — the "common ratios" case in which Berend runs the
rank-two argument on the full cone.

Note that `diag ν` is *not* assumed nonexpanding here: the theorem covers every
family member with a strictly contracting coordinate. -/
theorem log_rate_ratio_eq {E : Set (ι → ℝ)} (hE : IsClosed E) {S : Finset ι}
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {mu nu : ι → ℝ} (hmuinv : ∀ x ∈ E, diag mu x ∈ E) (hnuinv : ∀ x ∈ E, diag nu x ∈ E)
    (hmu : ∀ k ∈ S, 1 < |mu k|)
    {p : ι} (hpS : p ∈ S) (hnp : |nu p| < 1) (hnupos : ∀ k ∈ S, nu k ≠ 0) :
    ∀ j ∈ S, Real.log |mu j| * Real.log |nu p| = Real.log |mu p| * Real.log |nu j| := by
  intro j hjS
  by_contra hne
  by_cases hjp : j = p
  · exact hne (by rw [hjp])
  · exact false_of_rate_separation hE hacc hmin hmuinv hnuinv hmu hpS hjS
      (hnupos p hpS) hnp (hnupos j hjS) hne

/-- Contrapositive form of `log_rate_ratio_eq`, phrased as the exact dichotomy
of plan §C.5: on a minimal accumulating coordinate set, for each family member
with a strictly contracting coordinate, either the rates are proportional on
`S`, or `S` has no second coordinate, i.e. `S = {p}`. -/
theorem rate_dichotomy {E : Set (ι → ℝ)} (hE : IsClosed E) {S : Finset ι}
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {mu nu : ι → ℝ} (hmuinv : ∀ x ∈ E, diag mu x ∈ E) (hnuinv : ∀ x ∈ E, diag nu x ∈ E)
    (hmu : ∀ k ∈ S, 1 < |mu k|)
    {p : ι} (hpS : p ∈ S) (hnp : |nu p| < 1) (hnupos : ∀ k ∈ S, nu k ≠ 0) :
    S = {p} ∨
      ∀ j ∈ S, Real.log |mu j| * Real.log |nu p| = Real.log |mu p| * Real.log |nu j| := by
  by_cases hS : S = {p}
  · exact Or.inl hS
  · refine Or.inr ?_
    intro j hjS
    by_contra hne
    have hjp : j ≠ p := by
      rintro rfl
      exact hne rfl
    exact false_of_rate_separation hE hacc hmin hmuinv hnuinv hmu hpS hjS
      (hnupos p hpS) hnp (hnupos j hjS) hne


/-! ## 5. Two consequences: the conformal (single-rate) form, and the exclusion
of a mixed real/complex coordinate set by the norm relations -/

/-- **Lemma 4.4, conformal form.**  A strictly contracting family member on a
minimal accumulating coordinate set acts on `V_S` with a *single* negative rate:
there is `t < 0` with `log |ν j| = t * log |μ j|` for every `j ∈ S`.

This is the form in which the paper runs the rank-two argument on the full cone:
one rate per family element on `V_S`, so the semigroup acts conformally there. -/
theorem exists_common_rate {E : Set (ι → ℝ)} (hE : IsClosed E) {S : Finset ι}
    (hacc : Acc E S) (hmin : ∀ S' : Finset ι, S' ⊂ S → ¬ Acc E S')
    {mu nu : ι → ℝ} (hmuinv : ∀ x ∈ E, diag mu x ∈ E) (hnuinv : ∀ x ∈ E, diag nu x ∈ E)
    (hmu : ∀ k ∈ S, 1 < |mu k|)
    {p : ι} (hpS : p ∈ S) (hnp : |nu p| < 1) (hnupos : ∀ k ∈ S, nu k ≠ 0) :
    ∃ t : ℝ, t < 0 ∧ ∀ j ∈ S, Real.log |nu j| = t * Real.log |mu j| := by
  have hmp : 1 < |mu p| := hmu p hpS
  have hmp0 : 0 < Real.log |mu p| := Real.log_pos hmp
  have hnp0 : 0 < |nu p| := abs_pos.2 (hnupos p hpS)
  have hnp1 : Real.log |nu p| < 0 := Real.log_neg hnp0 hnp
  refine ⟨Real.log |nu p| / Real.log |mu p|, div_neg_of_neg_of_pos hnp1 hmp0, ?_⟩
  intro j hjS
  have h := log_rate_ratio_eq hE hacc hmin hmuinv hnuinv hmu hpS hnp hnupos j hjS
  field_simp at h ⊢
  linarith [h]

/-! ### The norm relations exclude the real coordinate together with a complex one

In the cubic two-stage model `V = ℝ × ℂ` the archimedean moduli of a prime
element `π` and of a unit `ε` satisfy

* `|π 1| * |π 2| ^ 2 = p` (the norm form of one real and two complex conjugate
  embeddings, `p = |Nm π| > 1`), and
* `|ε 1| * |ε 2| ^ 2 = 1` (unit).

In logarithmic form: `a1 + 2 * a2 = L` with `L = log p ≠ 0`, and
`c1 + 2 * c2 = 0`.  The next lemma says that these two relations are
*incompatible* with proportionality of the two rate vectors.  Together with
`rate_dichotomy` this excludes every minimal accumulating coordinate set that
contains the real coordinate and a complex one: `S = {1}`, or `S` inside the
conjugate pair `{2,3}` (where the rates agree automatically and the paper's
full-cone rank-two argument applies), are the only surviving cases. -/

/-- **The norm computation.**  Let `a1 + 2 a2 = L ≠ 0` and `c1 + 2 c2 = 0` with
`c1 ≠ 0`.  Then the rate vectors `(a1, a2)` and `(c1, c2)` are *not*
proportional: `a2 * c1 ≠ a1 * c2`.

Intended instantiation: `a = log |π ·|`, `c = log |ε ·|`, `L = log p`. -/
theorem not_proportional_of_trace_relations {a1 a2 c1 c2 L : ℝ} (hL : L ≠ 0)
    (hpi : a1 + 2 * a2 = L) (heps : c1 + 2 * c2 = 0) (hc1 : c1 ≠ 0) :
    a2 * c1 ≠ a1 * c2 := by
  intro h
  have h2 : c2 = -(c1 / 2) := by linarith
  rw [h2] at h
  have h3 : a1 * (-(c1 / 2)) = (-(a1 / 2)) * c1 := by ring
  rw [h3] at h
  have ha2 : a2 = -(a1 / 2) := mul_right_cancel₀ hc1 h
  have hzero : L = 0 := by rw [← hpi, ha2]; ring
  exact hL hzero

end BerendRate

end CubicTwoStage
