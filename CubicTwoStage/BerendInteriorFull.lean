/-
# The interior step of Furstenberg's Proposition IV.1, by expansion instead of
# ergodicity

Swarm `smw8wfugr`, member m2, direction d1 (Berend §5 / Proposition IV.1).

In the proof of Furstenberg's Proposition IV.1 (`[1, p. 45]`, quoted in Berend,
*Multi-invariant sets on tori*, Trans. AMS 280 (1983), §5) the one step that is
not combinatorial is:

> `K^{(n)}` is closed, invariant under the congruence subsemigroup `Σ^{(n)}` and
> has non-empty interior; **hence** `K^{(n)} = T^r`
> (Furstenberg: because `Σ` contains an endomorphism ergodic for Lebesgue
> measure, so a positive-measure invariant set has full measure).

This file shows that the step is a *topological* consequence of an expansion
estimate, so no measure theory and no ergodicity is needed, provided the family
contains an element which expands every direction.  That hypothesis holds for the
unit–prime family: for `u` a unit with `|σ₁ u| > 1` and `π` with `|Nm π| = p > 1`
there are `N ∈ ℤ`, `j ≥ 1` with `|σ_k(u^N π^j)| > 1` at all three places, because
`|σ₁(u)| |σ₂(u)|² = 1 = |Nm u|` and `|σ₁(π)| |σ₂(π)|² = p`.

## Main results

* `exists_cover_radius`: in a normed real vector space `V` with `V ⧸ L` compact,
  there is `R > 0` with `mk' L '' ball y R = univ` for every centre `y`.  This is
  the "covering radius" of the lattice; it is obtained from compactness of the
  quotient and openness of the quotient map, with no discreteness hypothesis.

* `eq_univ_of_expanding_of_interior`: let `A : V →L[ℝ] V` be a linear
  endomorphism with a right inverse `A'` which is a strict contraction
  (`‖A' x‖ ≤ λ⁻¹ ‖x‖`, `λ > 1`), preserving `L`; let `σ` be the induced
  endomorphism of `V ⧸ L`.  Then every closed `σ`-invariant set with non-empty
  interior is everything.

The proof is the ball computation `ball (A x) (λ * ρ) ⊆ A '' ball x ρ`
(`‖A'‖ ≤ λ⁻¹ < 1`), pushed through the iterates `A^[n]`: a ball of radius `r`
inside `E` produces balls of radius `λ^n r` inside `E`, and once `λ^n r` exceeds
the covering radius the ball is the whole torus.

Note that neither injectivity of `A` nor `A(L) = L` is needed: only `A(L) ⊆ L`
(so that `σ` exists), a right inverse of `A`, and the contraction of `A'`.  In the
unit–prime model the expanding elements `ε^N π^j` (`j ≥ 1`) are *not* injective
on the torus, which is exactly why the injective form of the argument would not
apply; this form does.

Everything is axiom free; nothing is assumed beyond the displayed hypotheses.
-/
import Mathlib

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CubicTwoStage
namespace BerendInteriorFull

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {L : AddSubgroup V}

/-- **Covering radius of a compact quotient.**  If `V ⧸ L` is compact, some ball
around any point of `V` surjects onto the whole quotient. -/
theorem exists_cover_radius [CompactSpace (V ⧸ L)] :
    ∃ R : ℝ, 0 < R ∧ ∀ y : V, (QuotientAddGroup.mk' L) '' Metric.ball y R = univ := by
  classical
  have hopen : ∀ n : ℕ, IsOpen ((QuotientAddGroup.mk' L) '' Metric.ball (0 : V) (n : ℝ)) :=
    fun n => QuotientAddGroup.isOpenMap_coe _ Metric.isOpen_ball
  have hcov : (univ : Set (V ⧸ L)) ⊆
      ⋃ n : ℕ, (QuotientAddGroup.mk' L) '' Metric.ball (0 : V) (n : ℝ) := by
    intro z _
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    refine Set.mem_iUnion.2 ⟨⌈‖y‖⌉₊ + 1, ⟨y, ?_, rfl⟩⟩
    rw [Metric.mem_ball, dist_zero_right, Nat.cast_add, Nat.cast_one]
    have h1 : ‖y‖ ≤ (⌈‖y‖⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ => (QuotientAddGroup.mk' L) '' Metric.ball (0 : V) (n : ℝ)) hopen hcov
  set N : ℕ := ∑ n ∈ s, n with hN
  have hle : ∀ n ∈ s, n ≤ N := by
    intro n hn
    exact Finset.single_le_sum (f := fun n : ℕ => n) (fun i _ => Nat.zero_le i) hn
  refine ⟨(N : ℝ) + 1, by positivity, fun y => ?_⟩
  refine Set.eq_univ_of_forall fun z => ?_
  have hz : z - QuotientAddGroup.mk' L y ∈
      ⋃ n ∈ s, (QuotientAddGroup.mk' L) '' Metric.ball (0 : V) (n : ℝ) := hs (mem_univ _)
  obtain ⟨n, hn, w, hw, hwz⟩ := Set.mem_iUnion₂.1 hz
  refine ⟨y + w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, show y + w - y = w by abel]
    have h1 : ‖w‖ < (n : ℝ) := by
      rw [Metric.mem_ball] at hw
      simpa using hw
    have h2 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle n hn
    linarith
  · rw [map_add, hwz]
    abel

/-- **The ball estimate.**  If `A'` is a right inverse of `A` with
`‖A' x‖ ≤ λ⁻¹ ‖x‖` and `λ > 1`, then the image of a ball of radius `ρ` under `A`
contains the ball of radius `λ * ρ` around the image of the centre. -/
theorem ball_subset_image_ball (A A' : V →L[ℝ] V) (hAA' : ∀ x, A (A' x) = x)
    {lam : ℝ} (hlam : 1 < lam) (hexp : ∀ x : V, ‖A' x‖ ≤ lam⁻¹ * ‖x‖)
    {x : V} {ρ : ℝ} (_hρ : 0 < ρ) :
    Metric.ball (A x) (lam * ρ) ⊆ A '' Metric.ball x ρ := by
  intro z hz
  rw [Metric.mem_ball] at hz
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hpos : (0 : ℝ) < lam⁻¹ := inv_pos.mpr hlam0
  rw [dist_eq_norm] at hz
  refine ⟨x + A' (z - A x), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, show x + A' (z - A x) - x = A' (z - A x) by abel]
    have h1 : ‖A' (z - A x)‖ ≤ lam⁻¹ * ‖z - A x‖ := hexp _
    have h2 : ‖z - A x‖ < lam * ρ := hz
    have h3 : lam⁻¹ * ‖z - A x‖ < lam⁻¹ * (lam * ρ) :=
      mul_lt_mul_of_pos_left h2 hpos
    have h4 : lam⁻¹ * (lam * ρ) = ρ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam0), one_mul]
    linarith
  · rw [map_add, hAA', add_sub_cancel]

/-- **The interior step of Proposition IV.1 by expansion.**  Let `A` preserve the
subgroup `L`, and let `σ` be the induced endomorphism of `V ⧸ L`.  If `A` has a
right inverse which is a strict contraction with constant `λ⁻¹ < 1`, then every
closed `σ`-invariant subset of `V ⧸ L` with non-empty interior is everything. -/
theorem eq_univ_of_expanding_of_interior [CompactSpace (V ⧸ L)]
    (A A' : V →L[ℝ] V) (hAA' : ∀ x, A (A' x) = x)
    {lam : ℝ} (hlam : 1 < lam) (hexp : ∀ x : V, ‖A' x‖ ≤ lam⁻¹ * ‖x‖)
    (hL : ∀ g ∈ L, A g ∈ L)
    {E : Set (V ⧸ L)} (hE : IsClosed E)
    (hinv : (QuotientAddGroup.map L L A.toAddMonoidHom hL) '' E ⊆ E)
    (hint : ∃ x₀ : V, ∃ r : ℝ, 0 < r ∧ (QuotientAddGroup.mk' L) '' Metric.ball x₀ r ⊆ E) :
    E = univ := by
  classical
  obtain ⟨x₀, r, hr, hsub⟩ := hint
  obtain ⟨R, hR, hcov⟩ := exists_cover_radius (L := L)
  -- `mk' L` intertwines `A` with the induced map `σ`
  have hmk : ∀ y : V, (QuotientAddGroup.map L L A.toAddMonoidHom hL)
      (QuotientAddGroup.mk' L y) = QuotientAddGroup.mk' L (A y) :=
    fun y => QuotientAddGroup.map_mk' L L A.toAddMonoidHom hL y
  -- one expansion step, after applying `mk' L`
  have hstep : ∀ (x : V) (ρ : ℝ), 0 < ρ →
      (QuotientAddGroup.mk' L) '' Metric.ball x ρ ⊆ E →
      (QuotientAddGroup.mk' L) '' Metric.ball (A x) (lam * ρ) ⊆ E := by
    intro x ρ hρ hx
    have h1 : Metric.ball (A x) (lam * ρ) ⊆ A '' Metric.ball x ρ :=
      ball_subset_image_ball A A' hAA' hlam hexp hρ
    have himg : (QuotientAddGroup.mk' L) '' (A '' Metric.ball x ρ) =
        (QuotientAddGroup.map L L A.toAddMonoidHom hL) ''
          ((QuotientAddGroup.mk' L) '' Metric.ball x ρ) := by
      rw [Set.image_image, Set.image_image]
      exact (congrArg (fun f : V → V ⧸ L => f '' Metric.ball x ρ) (funext hmk)).symm
    calc (QuotientAddGroup.mk' L) '' Metric.ball (A x) (lam * ρ)
        ⊆ (QuotientAddGroup.mk' L) '' (A '' Metric.ball x ρ) := Set.image_mono h1
      _ = _ := himg
      _ ⊆ (QuotientAddGroup.map L L A.toAddMonoidHom hL) '' E := Set.image_mono hx
      _ ⊆ E := hinv
  -- iterate: a sequence of balls of radii `λ ^ n * r` around `A^[n] x₀` lies in `E`
  have hmain : ∀ n : ℕ,
      (QuotientAddGroup.mk' L) '' Metric.ball (A^[n] x₀) (lam ^ n * r) ⊆ E := by
    intro n
    induction n with
    | zero => simpa using hsub
    | succ n ih =>
        have h := hstep (A^[n] x₀) (lam ^ n * r) (by positivity) ih
        have h1 : A^[n + 1] x₀ = A (A^[n] x₀) := Function.iterate_succ_apply' A n x₀
        have h2 : lam ^ (n + 1) * r = lam * (lam ^ n * r) := by ring
        rwa [h1, h2]
  -- choose `n` so that the radius exceeds the covering radius
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / r) hlam
  have hn' : R ≤ lam ^ n * r := by
    rw [div_lt_iff₀ hr] at hn
    linarith
  have hsub2 : (QuotientAddGroup.mk' L) '' Metric.ball (A^[n] x₀) R ⊆
      (QuotientAddGroup.mk' L) '' Metric.ball (A^[n] x₀) (lam ^ n * r) :=
    Set.image_mono (Metric.ball_subset_ball hn')
  rw [hcov] at hsub2
  exact Set.eq_univ_of_univ_subset (hsub2.trans (hmain n))

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendInteriorFull.exists_cover_radius
#print axioms CubicTwoStage.BerendInteriorFull.ball_subset_image_ball
#print axioms CubicTwoStage.BerendInteriorFull.eq_univ_of_expanding_of_interior

end BerendInteriorFull
end CubicTwoStage
