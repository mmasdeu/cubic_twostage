/-
# Periodic points of a self-map of a finite set

A forward-invariant finite set on which the map is injective contains only
periodic points: some positive iterate returns each point to itself.  This is
the combinatorial step in the proof of Theorem 3.6, where the map is
multiplication by the fundamental unit `ε` acting on the finite set of
uncovered classes modulo `σ(𝒪_K)`.
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

/-- A finite forward-invariant set of an injective self-map consists of
periodic points. -/
theorem periodic_of_finite_image {α : Type*} {S : Set α} (hfin : S.Finite) {f : α → α}
    (hmap : ∀ x ∈ S, f x ∈ S) (hinj : Function.Injective f) {x : α} (hx : x ∈ S) :
    ∃ n : ℕ, 0 < n ∧ f^[n] x = x := by
  classical
  letI := hfin.fintype
  have hmem : ∀ n : ℕ, f^[n] x ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmap _ ih
  let g : ℕ → {y : α // y ∈ S} := fun n => ⟨f^[n] x, hmem n⟩
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp (not_injective_infinite_finite g)
  have hval : f^[i] x = f^[j] x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hcancel : f^[i] (f^[j - i] x) = f^[i] x := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt), hval]
    exact hinj.iterate i hcancel
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have hcancel : f^[j] (f^[i - j] x) = f^[j] x := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt), hval]
    exact hinj.iterate j hcancel

end CubicTwoStage
