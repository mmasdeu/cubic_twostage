/-
# The rank-two expansion step on a one-dimensional coordinate subspace

`BerendSec4.exists_minimal_and_expanding` produces a minimal accumulating
coordinate set `S` and one family element that is uniformly expanding on it.
Stage C.4 must turn "`E` accumulates at `0` in `coord S`" into "`E - E` contains a
neighbourhood of `0`".

This file supplies the part of that upgrade which is unconditional: when the
accumulating coordinate set is a single coordinate `i` and the family also
supplies a *contracting* element on that coordinate (in the unit–prime model
`μ_ε` or `μ_ε⁻¹`, whichever contracts), with multiplicatively independent
multipliers — corrected (B3) read on the multipliers — then `E - E` contains the
whole coordinate line `coord {i}`.  For `ι` a singleton this is `E - E = univ`;
for `|ι| ≥ 2` the cone/annulus argument of §C.4 is still needed to pass from that
line to a neighbourhood of `0` in `ι → ℝ`.

Imports the project module `BerendSec4` (its `diag`/`coord`/`Acc` API is reused,
not modified).  No axiom, no `sorry`.
-/
import CubicTwoStage.BerendSec4
import CubicTwoStage.BerendRankTwo

open Set Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CubicTwoStage
namespace BerendRankTwo

open BerendSec4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector of the coordinate line `coord {i}` is the update of `0` at its own
`i`-th coordinate. -/
theorem eq_update_zero {i : ι} {x : ι → ℝ} (hx : x ∈ coord ({i} : Set ι)) :
    x = Function.update (0 : ι → ℝ) i (x i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj]
    have hxj : x j = 0 := (mem_coord.1 hx) j (by simpa using hj)
    simp [hxj]

/-- The diagonal map sends the `i`-th basis line to itself, multiplying the
`i`-th coordinate. -/
theorem diag_update_zero (lam : ι → ℝ) (i : ι) (z : ℝ) :
    diag lam (Function.update (0 : ι → ℝ) i z) = Function.update (0 : ι → ℝ) i (lam i * z) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [diag_apply]
  · simp [diag_apply, Function.update_of_ne hj]

/-- **Stage C.4 on a one-dimensional accumulating coordinate set.**  Let `E` be
closed and invariant under two elements of the diagonal family, let `i` be a
coordinate on which one element expands (`lam i > 1`) and the other contracts
(`0 < mu i < 1`), with multiplicatively independent multipliers.  If `E` contains
a nonzero point of the coordinate line `coord {i}`, then `E - E` contains all of
`coord {i}`. -/
theorem coord_subset_sub {E : Set (ι → ℝ)} (hE : IsClosed E)
    {lam mu : ι → ℝ} (hinv1 : ∀ x ∈ E, diag lam x ∈ E) (hinv2 : ∀ x ∈ E, diag mu x ∈ E)
    {i : ι} (hlam : 1 < lam i) (hmu0 : 0 < mu i) (hmu1 : mu i < 1)
    (hind : ∀ m n : ℤ, lam i ^ m = mu i ^ n → m = 0 ∧ n = 0)
    (hacc : ∃ x ∈ E, x ∈ coord ({i} : Set ι) ∧ x i ≠ 0) :
    (coord ({i} : Set ι) : Set (ι → ℝ)) ⊆ E - E := by
  classical
  -- the `i`-th coordinates of the points of `E` on the line `coord {i}`
  let A : Set ℝ := {z : ℝ | Function.update (0 : ι → ℝ) i z ∈ E}
  have hAmem : ∀ z : ℝ, z ∈ A ↔ Function.update (0 : ι → ℝ) i z ∈ E := fun z => Iff.rfl
  have hcont : Continuous fun z : ℝ => Function.update (0 : ι → ℝ) i z := by
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · have hfun : (fun a : ℝ => Function.update (0 : ι → ℝ) i a j) = id := by
        funext a
        rw [hj]
        simp
      rw [hfun]
      exact continuous_id
    · simpa [Function.update_of_ne hj] using continuous_const
  have hAclosed : IsClosed A := by
    rw [show A = (fun z : ℝ => Function.update (0 : ι → ℝ) i z) ⁻¹' E from rfl]
    exact IsClosed.preimage hcont hE
  have hAexp : ∀ z ∈ A, lam i * z ∈ A := by
    intro z hz
    rw [hAmem] at hz ⊢
    rw [← diag_update_zero lam i z]
    exact hinv1 _ hz
  have hAcon : ∀ z ∈ A, mu i * z ∈ A := by
    intro z hz
    rw [hAmem] at hz ⊢
    rw [← diag_update_zero mu i z]
    exact hinv2 _ hz
  obtain ⟨x, hxE, hxS, hxi⟩ := hacc
  have hxA : x i ∈ A := by
    rw [hAmem]
    rw [← eq_update_zero hxS]
    exact hxE
  have hAA : A - A = Set.univ :=
    sub_eq_univ_of_invariant_of_indep hlam hmu0 hmu1 hind hAclosed hAexp hAcon hxA hxi
  intro y hy
  have hmem : y i ∈ A - A := by rw [hAA]; exact mem_univ _
  obtain ⟨a, haA, b, hbA, hab⟩ := Set.mem_sub.1 hmem
  rw [hAmem] at haA hbA
  have hdiff : Function.update (0 : ι → ℝ) i a - Function.update (0 : ι → ℝ) i b
      = Function.update (0 : ι → ℝ) i (a - b) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  refine Set.mem_sub.2 ⟨_, haA, _, hbA, ?_⟩
  rw [hdiff]
  have hab' : a - b = y i := by linarith [hab]
  rw [hab']
  exact (eq_update_zero hy).symm

/-- `Acc E {i}` (accumulation at `0` on the coordinate line) supplies the nonzero
point of the line that `coord_subset_sub` needs. -/
theorem exists_ne_zero_of_acc {E : Set (ι → ℝ)} {i : ι} (h : Acc E {i}) :
    ∃ x ∈ E, x ∈ coord ({i} : Set ι) ∧ x i ≠ 0 := by
  obtain ⟨u, huE, huS, hune, -⟩ := acc_iff.1 h 1 one_pos
  have huS' : u ∈ coord ({i} : Set ι) := by simpa using huS
  refine ⟨u, huE, huS', ?_⟩
  intro hui
  refine hune (funext fun j => ?_)
  by_cases hj : j = i
  · subst hj; simpa using hui
  · exact ((mem_coord.1 huS') j (by simpa using hj)).trans (by simp)

/-- **Stage C.4 on a one-dimensional accumulating coordinate set, from `Acc`.**
Combines `exists_ne_zero_of_acc` with `coord_subset_sub`: if `0` is a
non-isolated point of `E` on the coordinate line `coord {i}`, one family element
expands there, another contracts there, and the two multipliers are
multiplicatively independent, then `E - E` contains the whole line
`coord {i}`. -/
theorem acc_coord_subset_sub {E : Set (ι → ℝ)} (hE : IsClosed E)
    {lam mu : ι → ℝ} (hinv1 : ∀ x ∈ E, diag lam x ∈ E) (hinv2 : ∀ x ∈ E, diag mu x ∈ E)
    {i : ι} (hlam : 1 < lam i) (hmu0 : 0 < mu i) (hmu1 : mu i < 1)
    (hind : ∀ m n : ℤ, lam i ^ m = mu i ^ n → m = 0 ∧ n = 0)
    (hacc : Acc E {i}) :
    (coord ({i} : Set ι) : Set (ι → ℝ)) ⊆ E - E :=
  coord_subset_sub hE hinv1 hinv2 hlam hmu0 hmu1 hind (exists_ne_zero_of_acc hacc)


end BerendRankTwo
end CubicTwoStage
