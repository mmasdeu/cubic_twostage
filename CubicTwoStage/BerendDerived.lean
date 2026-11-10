/-
# The Cantor–Bendixson layer for closed invariant subsets

Target file in the project: `CubicTwoStage/BerendDerived.lean` (copy verbatim).
**Axiom free**, imports only Mathlib-level topology (no `CubicTwoStage.Berend`).

## What this file is

`BEREND_PROOF_PLAN.md` §D decides the dichotomy by looking at a *minimal* closed
invariant set.  Before minimality can be used, one needs the Cantor–Bendixson
partition of a closed set into its derived part and its isolated part, and the
fact that the derived part inherits invariance.  This file provides exactly that
layer, unconditionally:

* `derived E = {x | x ∈ closure (E \ {x})}` — the derived set;
* `derived_subset_of_isClosed` : for closed `E`, `derived E ⊆ E`;
* **`isClosed_derived`**: for closed `E` in a metric space, the derived set is
  closed (so `E` is a Cantor–Bendixson union of a perfect closed set and a
  countable scattered part);
* **`nonempty_derived_of_infinite`**: an infinite compact `E` has a nonempty
  derived part, i.e. `E.Finite ∨ (derived E).Nonempty` — the finite/perfect
  dichotomy used by plan §D;
* **`derived_fwdInv`**: the derived set of an invariant closed set is invariant
  under a continuous injective self-map (in particular under an expanding toral
  endomorphism or an automorphism), so every stage of the Cantor–Bendixson
  recursion is again an invariant closed set.

## What this file does *not* do

It does not decide whether a *perfect* closed invariant set can be proper: that
is exactly the rank-two rigidity content of plan §C.5/§D.3 (Furstenberg's
`×2 ×3` theorem in dimension one), and nothing here is conditional on it.
-/
import Mathlib

open Set Filter Topology

namespace CubicTwoStage

variable {T : Type*} [MetricSpace T]

/-! ## 1. The derived set -/

/-- The derived set of `E`: the set of its accumulation points. -/
def derived (E : Set T) : Set T := {x | x ∈ closure (E \ {x})}

theorem mem_derived {E : Set T} {x : T} :
    x ∈ derived E ↔ x ∈ closure (E \ {x}) := Iff.rfl

theorem derived_subset_closure (E : Set T) : derived E ⊆ closure E := by
  intro x hx
  refine closure_mono ?_ hx
  exact fun y hy => hy.1

theorem derived_subset_of_isClosed {E : Set T} (hE : IsClosed E) : derived E ⊆ E := by
  refine (derived_subset_closure E).trans ?_
  rw [hE.closure_eq]

/-- **The derived set of a closed set is closed.** -/
theorem isClosed_derived {E : Set T} (hE : IsClosed E) : IsClosed (derived E) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_derived, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x', hx', hd'⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (by linarith)
  have hd'' : dist x' x < ε / 2 := by rw [dist_comm]; exact hd'
  by_cases hxx' : x' = x
  · have hx'' : x ∈ derived E := hxx' ▸ hx'
    obtain ⟨y, hymem, hd⟩ := Metric.mem_closure_iff.1 hx'' (ε / 2) (by linarith)
    exact ⟨y, hymem, by linarith⟩
  · obtain ⟨y, hymem, hd⟩ := Metric.mem_closure_iff.1 hx'
      (min (ε / 2) (dist x' x)) (lt_min (by linarith) (dist_pos.2 hxx'))
    obtain ⟨hyE, hyx'⟩ := hymem
    have hyx : y ≠ x := by
      rintro rfl
      exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (lt_irrefl _)
    refine ⟨y, ⟨hyE, hyx⟩, ?_⟩
    have h2 : dist x' y < ε / 2 := lt_of_lt_of_le hd (min_le_left _ _)
    calc dist x y = dist y x := dist_comm x y
      _ ≤ dist y x' + dist x' x := dist_triangle _ _ _
      _ = dist x' y + dist x' x := by rw [dist_comm y x']
      _ < ε / 2 + ε / 2 := by linarith [h2, hd'']
      _ = ε := by ring

/-! ## 2. The finite/perfect dichotomy -/

/-- **An infinite compact set has a nonempty derived set.** -/
theorem nonempty_derived_of_infinite [T2Space T] {E : Set T} (hinf : E.Infinite)
    (hc : IsCompact E) : (derived E).Nonempty := by
  obtain ⟨x, -, hx⟩ := hinf.exists_accPt_cofinite_inf_principal_of_subset_isCompact hc
    (subset_refl E)
  refine ⟨x, ?_⟩
  rw [mem_derived, Metric.mem_closure_iff]
  intro ε hε
  have hu' : Metric.ball x ε ∈ 𝓝[≠] x :=
    Filter.mem_inf_of_left (Metric.ball_mem_nhds x hε)
  have hxmem : ({x}ᶜ : Set T) ∈ (cofinite ⊓ 𝓟 E : Filter T) :=
    Filter.mem_inf_of_left (by simp)
  have hEmem : E ∈ (cofinite ⊓ 𝓟 E : Filter T) :=
    Filter.mem_inf_of_right (Filter.mem_principal_self E)
  have hdiff : (E \ {x}) ∈ (cofinite ⊓ 𝓟 E : Filter T) :=
    Filter.mem_of_superset (Filter.inter_mem hxmem hEmem) (fun y hy => ⟨hy.2, hy.1⟩)
  have h1 : Metric.ball x ε ∈ (𝓝[≠] x ⊓ (cofinite ⊓ 𝓟 E) : Filter T) := Filter.mem_inf_of_left hu'
  have h2 : (E \ {x}) ∈ (𝓝[≠] x ⊓ (cofinite ⊓ 𝓟 E) : Filter T) := Filter.mem_inf_of_right hdiff
  obtain ⟨y, hy⟩ := Filter.NeBot.nonempty_of_mem hx (Filter.inter_mem h1 h2)
  exact ⟨y, ⟨hy.2.1, hy.2.2⟩, by simpa [Metric.mem_ball, dist_comm] using hy.1⟩

/-- **Finite or not**: a closed set in a compact space is finite, or its derived
part is nonempty. -/
theorem finite_or_derived_nonempty [CompactSpace T] [T2Space T] {E : Set T}
    (hE : IsClosed E) : E.Finite ∨ (derived E).Nonempty := by
  rcases E.finite_or_infinite with h | h
  · exact Or.inl h
  · exact Or.inr (nonempty_derived_of_infinite h hE.isCompact)

/-! ## 3. Invariance of the derived set -/

/-- **The derived set of a forward-invariant closed set is forward invariant**,
for a continuous injective self-map.  In particular every stage of the
Cantor–Bendixson recursion on an expanding toral endomorphism's invariant set is
again an invariant closed set. -/
theorem derived_fwdInv {E : Set T} {f : T → T} (hf : Continuous f)
    (hinj : Function.Injective f) (_hE : IsClosed E) (h : f '' E ⊆ E) :
    f '' derived E ⊆ derived E := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_derived, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hf.continuousAt ε hε
  obtain ⟨y, hymem, hd⟩ := Metric.mem_closure_iff.1 hx δ hδ
  obtain ⟨hyE, hyx⟩ := hymem
  refine ⟨f y, ⟨h ⟨y, hyE, rfl⟩, ?_⟩, ?_⟩
  · intro hfy
    exact hyx (hinj hfy)
  · rw [dist_comm]
    exact hδ' (by rwa [dist_comm] at hd)

end CubicTwoStage
