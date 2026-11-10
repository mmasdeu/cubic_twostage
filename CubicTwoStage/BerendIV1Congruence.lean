/-
# Furstenberg's Proposition IV.1 from congruence classes: a proof

Swarm `smw93hdxd`, member m5, direction d3 (removal of the axiom
`CubicTwoStage.berend_multi_invariance`).

`CubicTwoStage.BerendPropIV1.PropIV1` records Furstenberg's Proposition IV.1
(quoted by Berend, *Multi-invariant sets on tori*, Trans. AMS **280** (1983),
p. 530) as a `def … : Prop`, i.e. as a hypothesis.  This module **proves** it
from explicit, checkable data, so that it is no longer an assumption:

> `M`, `B` closed `Σ`-invariant subsets of a compact abelian topological group,
> `M` minimal, `M + B = G`  ⟹  `B = G`.

The proof is the classical congruence-class argument, with the analytic
(ergodicity) input replaced by the two statements that an expanding member of a
congruence subsemigroup supplies in the toral case:

* `hreps` — **finiteness of `Σ / Σ⁽ⁿ⁾`**: for every level `n` there is a finite
  set `R` of representatives with `Σ = ⋃_{r ∈ R} r · Σ⁽ⁿ⁾`, where `Σ⁽ⁿ⁾` is the
  subsemigroup of members that fix the level-`n` torsion set `T n` pointwise.
  (For a toral family this is finiteness of the image of `Σ` in
  `GL_r(ℤ/qⁿℤ)`; `BerendIV1Model` derives it for the unit–prime family from
  finiteness of the torsion group and of `Perm (T n)`.)
* `hint` — **interior-full for `Σ⁽ⁿ⁾`**: every closed `Σ⁽ⁿ⁾`-invariant set with
  non-empty interior is everything.  (Supplied in the toral case by an expanding
  member of `Σ⁽ⁿ⁾`: `CubicTwoStage.BerendInteriorFull`.)

## The argument

Fix `n`, put `K = Σ⁽ⁿ⁾`, `T = T n`.

1. `M` is `K`-invariant, so it contains a closed non-empty `K`-minimal set `N`.
2. For `k ∈ K`, `k N` is closed, non-empty and `K`-invariant, and `k N ⊆ N`, so
   `k N = N` by minimality of `N`.
3. For `s ∈ Σ`, `s N` is `K`-minimal: a closed non-empty `K`-invariant
   `Z ⊆ s N` pulls back to `s⁻¹ Z ∩ N`, which is closed non-empty
   `K`-invariant, hence `= N`, hence `s N ⊆ Z`.
4. `s N` depends only on the class of `s`: if `s = r k` with `k ∈ K` then
   `s N = r (k N) = r N` by step 2.
5. Hence `Z := ⋃_{r ∈ R} r N` is closed, non-empty, `Σ`-invariant and contained
   in `M`; minimality of `M` gives `Z = M`.
6. Therefore `G = M + B = ⋃_{r ∈ R} (r N + B)` is a **finite** union of compact
   (hence closed) sets.  Baire: one member `C = r₀ N + B` has non-empty
   interior.  `C` is `K`-invariant (`k (r₀ N) = r₀ (k N) = r₀ N` and
   `k B ⊆ B`), so `C = G` by `hint`.
7. Pick `ν ∈ r₀ N`.  For `θ ∈ T` write `θ = ν' + β` with `ν' ∈ r₀ N`, `β ∈ B`.
   Every `k ∈ K` fixes `θ`, so `θ - k ν' = k β ∈ B`; as `k` ranges over `K`,
   `k ν'` is dense in the `K`-minimal set `r₀ N`, and `{x | θ - x ∈ B}` is
   closed, so `θ - x ∈ B` for every `x ∈ r₀ N`, in particular `θ - ν ∈ B`.
   Thus for each `n` there is `ν n` with `T n ⊆ ν n + B`.
8. Fix `n₀` and `θ ∈ T n₀`.  Since `T` is monotone, `θ ∈ T n` for all `n ≥ n₀`,
   so `ν n ∈ {x | θ - x ∈ B}` for all `n ≥ n₀`.  The sets
   `A N = closure {ν n | n ≥ N}` form a decreasing chain of non-empty compact
   sets, so they have a common point `ν*`; for `N = n₀` this gives
   `θ - ν* ∈ B`.  Hence `⋃_n T n ⊆ ν* + B`; the union is dense and `ν* + B` is
   closed, so `B = G`.

No `sorry`, no new axiom, no measure theory, no Fourier analysis: only
`propext`, `Classical.choice`, `Quot.sound`.
-/
import CubicTwoStage.BerendMinimal
import CubicTwoStage.BerendPropIV1

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendIV1

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {S : Type*} [CommMonoid S]

/-! ## 1. Elementary lemmas -/

section Helpers

variable (φ : S →* AddMonoid.End G)

/-- Two members of the family commute as maps (the monoid `S` is commutative). -/
theorem comp_comm (a b : S) (x : G) :
    (φ a : G → G) ((φ b : G → G) x) = (φ b : G → G) ((φ a : G → G) x) := by
  have e1 : ((φ (a * b) : AddMonoid.End G) : G → G) x =
      (φ a : G → G) ((φ b : G → G) x) := by
    rw [map_mul]; rfl
  have e2 : ((φ (b * a) : AddMonoid.End G) : G → G) x =
      (φ b : G → G) ((φ a : G → G) x) := by
    rw [map_mul]; rfl
  rw [← e1, ← e2, mul_comm]

/-- An additive endomorphism distributes over the pointwise sum of two sets. -/
theorem image_add' (f : G →+ G) (s t : Set G) : f '' (s + t) = f '' s + f '' t := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, (map_add f a b).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add f a b⟩

/-- The image of a composite is the composite of the images. -/
theorem image_comp (f g : G → G) (s : Set G) : (f ∘ g) '' s = f '' (g '' s) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Addition of sets distributes over a finite union. -/
theorem biUnion_finset_add (f : S → Set G) (R : Finset S) (B : Set G) :
    (⋃ r ∈ (R : Set S), f r) + B = ⋃ r ∈ (R : Set S), (f r + B) := by
  ext z
  constructor
  · rintro ⟨m, hm, b, hb, rfl⟩
    rw [mem_iUnion] at hm
    obtain ⟨r, hr⟩ := hm
    rw [mem_iUnion] at hr
    obtain ⟨hrR, hmr⟩ := hr
    exact mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hrR, ⟨m, hmr, b, hb, rfl⟩⟩⟩
  · intro hz
    rw [mem_iUnion] at hz
    obtain ⟨r, hz⟩ := hz
    rw [mem_iUnion] at hz
    obtain ⟨hrR, hz⟩ := hz
    obtain ⟨m, hm, b, hb, rfl⟩ := hz
    exact ⟨m, mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hrR, hm⟩⟩, b, hb, rfl⟩

end Helpers

/-! ## 2. The main theorem -/

section Main

variable (φ : S →* AddMonoid.End G)

/-- **Furstenberg's Proposition IV.1, proved from congruence data.**

`T : ℕ → Set G` is an increasing sequence of "torsion" sets with dense union,
`K n ⊆ S` is the level-`n` congruence subsemigroup (fixing `T n` pointwise),
`hreps` says `Σ = ⋃_{r ∈ R} r · K n` for a finite `R`, and `hint` says that a
closed `K n`-invariant set with non-empty interior is everything.  Then the
minimal-set disjointness statement `PropIV1` holds for the family `φ`. -/
theorem propIV1_of_congruence (hcont : ∀ s : S, Continuous (φ s))
    (T : ℕ → Set G) (hdense : Dense (⋃ n, T n)) (hTmono : ∀ n m : ℕ, n ≤ m → T n ⊆ T m)
    (K : ℕ → Set S)
    (hKone : ∀ n, (1 : S) ∈ K n)
    (hKfix : ∀ n : ℕ, ∀ k ∈ K n, ∀ θ ∈ T n, (φ k : G → G) θ = θ)
    (hreps : ∀ n, ∃ R : Finset S, ∀ m : S, ∃ r ∈ R, ∃ k ∈ K n, m = r * k)
    (hint : ∀ n, ∀ C : Set G, IsClosed C → (∀ k ∈ K n, (φ k : G → G) '' C ⊆ C) →
      (interior C).Nonempty → C = univ) :
    BerendPropIV1.PropIV1 (fun s : S => φ s) := by
  intro M B hMne hMclosed hBclosed hMinv hBinv hMmin hcover
  -- ## The level-`n` conclusion: a single point `ν` with `T n ⊆ ν + B`
  have step : ∀ n : ℕ, ∃ ν : G, ∀ θ ∈ T n, θ - ν ∈ B := by
    intro n
    obtain ⟨R, hR⟩ := hreps n
    -- the `K n`-minimal subset `N ⊆ M`
    obtain ⟨N, hNM, hNmin⟩ :=
      BerendMinimal.exists_minimal_invariant
        (F := fun k : K n => (φ (k : S) : G → G)) hMclosed hMne
        (fun k => hMinv (k : S))
    -- (2) elements of `K n` act as the identity on `N`
    have himg : ∀ k : K n, (φ (k : S) : G → G) '' N = N := by
      intro k
      refine hNmin.minimal ((φ (k : S) : G → G) '' N) (hNmin.inv k) ?_ ?_ ?_
      · exact hNmin.ne.image _
      · exact (hNmin.closed.isCompact.image (hcont (k : S))).isClosed
      · rintro k' _ ⟨y, ⟨y₀, hy₀, rfl⟩, rfl⟩
        exact ⟨(φ (k' : S) : G → G) y₀, hNmin.inv k' ⟨y₀, hy₀, rfl⟩,
          comp_comm φ (k : S) (k' : S) y₀⟩
    -- (3) images of `N` are `K n`-minimal
    have himgmin : ∀ s : S, BerendMinimal.IsMinimalInvariant
        (fun k : K n => (φ (k : S) : G → G)) ((φ s : G → G) '' N) := by
      intro s
      refine ⟨hNmin.ne.image _, ?_, ?_, ?_⟩
      · exact (hNmin.closed.isCompact.image (hcont s)).isClosed
      · rintro k _ ⟨y, ⟨y₀, hy₀, rfl⟩, rfl⟩
        exact ⟨(φ (k : S) : G → G) y₀, hNmin.inv k ⟨y₀, hy₀, rfl⟩,
          (comp_comm φ (k : S) s y₀).symm⟩
      · rintro Z hZsub hZne hZclosed hZinv
        have hWclosed : IsClosed ((φ s : G → G) ⁻¹' Z ∩ N) :=
          (hZclosed.preimage (hcont s)).inter hNmin.closed
        have hWne : ((φ s : G → G) ⁻¹' Z ∩ N).Nonempty := by
          obtain ⟨z, hz⟩ := hZne
          obtain ⟨x, hxN, hxz⟩ := hZsub hz
          exact ⟨x, mem_preimage.mpr (by rw [hxz]; exact hz), hxN⟩
        have hWinv : ∀ k : K n,
            (φ (k : S) : G → G) '' ((φ s : G → G) ⁻¹' Z ∩ N) ⊆
              ((φ s : G → G) ⁻¹' Z ∩ N) := by
          rintro k _ ⟨y, ⟨hyZ, hyN⟩, rfl⟩
          refine ⟨?_, hNmin.inv k ⟨y, hyN, rfl⟩⟩
          rw [mem_preimage, ← comp_comm φ (k : S) s y]
          exact hZinv k ⟨(φ s : G → G) y, hyZ, rfl⟩
        have hWN : (φ s : G → G) ⁻¹' Z ∩ N = N :=
          hNmin.minimal _ inter_subset_right hWne hWclosed hWinv
        refine Set.eq_of_subset_of_subset hZsub ?_
        rintro z ⟨x, hxN, rfl⟩
        have hxW : x ∈ (φ s : G → G) ⁻¹' Z ∩ N := by rw [hWN]; exact hxN
        exact hxW.1
    -- (4) the class of an element determines its image of `N`
    have hclass : ∀ r k : S, k ∈ K n → (φ (r * k) : G → G) '' N = (φ r : G → G) '' N := by
      intro r k hk
      have hcomp : (φ (r * k) : G → G) = ((φ r : G → G) ∘ (φ k : G → G)) := by
        funext x
        show ((φ (r * k) : AddMonoid.End G) : G → G) x =
          (φ r : G → G) ((φ k : G → G) x)
        rw [map_mul]; rfl
      rw [hcomp, image_comp (φ r : G → G) (φ k : G → G) N, himg ⟨k, hk⟩]
    -- (5) `Z = ⋃_{r ∈ R} r N` equals `M`
    set Z : Set G := ⋃ r ∈ (R : Set S), (φ r : G → G) '' N with hZdef
    have hRne : ((R : Set S)).Nonempty := by
      obtain ⟨r, hrR, -⟩ := hR 1
      exact ⟨r, by simpa using hrR⟩
    have hZsub : Z ⊆ M := by
      intro z hz
      rw [hZdef] at hz
      obtain ⟨r, hr⟩ := mem_iUnion.1 hz
      obtain ⟨hrR, hz⟩ := mem_iUnion.1 hr
      obtain ⟨y, hyN, rfl⟩ := hz
      exact hMinv r ⟨y, hNM hyN, rfl⟩
    have hZcompact : IsCompact Z := by
      rw [hZdef]
      exact R.finite_toSet.isCompact_biUnion
        (fun r _ => (hNmin.closed.isCompact.image (hcont r)))
    have hZclosed : IsClosed Z := hZcompact.isClosed
    have hZne : Z.Nonempty := by
      obtain ⟨r, hrR⟩ := hRne
      obtain ⟨y, hy⟩ := hNmin.ne.image ((φ r : G → G))
      exact ⟨y, mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hrR, hy⟩⟩⟩
    have hZinv : ∀ s : S, (φ s : G → G) '' Z ⊆ Z := by
      rintro s _ ⟨z, hz, rfl⟩
      rw [hZdef] at hz ⊢
      obtain ⟨r, hr⟩ := mem_iUnion.1 hz
      obtain ⟨hrR, hz⟩ := mem_iUnion.1 hr
      obtain ⟨y, hyN, rfl⟩ := hz
      obtain ⟨r', hr'R, k', hk', heq⟩ := hR (s * r)
      have hkey : (φ s : G → G) ((φ r : G → G) y) = (φ r' : G → G) ((φ k' : G → G) y) := by
        have e1 : ((φ (s * r) : AddMonoid.End G) : G → G) y =
            (φ s : G → G) ((φ r : G → G) y) := by rw [map_mul]; rfl
        have e2 : ((φ (r' * k') : AddMonoid.End G) : G → G) y =
            (φ r' : G → G) ((φ k' : G → G) y) := by rw [map_mul]; rfl
        rw [← e1, heq, e2]
      rw [hkey]
      exact mem_iUnion.2 ⟨r', mem_iUnion.2 ⟨by simpa using hr'R,
        ⟨(φ k' : G → G) y, hNmin.inv ⟨k', hk'⟩ ⟨y, hyN, rfl⟩, rfl⟩⟩⟩
    have hZM : Z = M := hMmin.minimal Z hZsub hZne hZclosed hZinv
    -- (6) the finite closed cover and Baire
    have hcover' : (⋃ r ∈ (R : Set S), ((φ r : G → G) '' N + B)) = univ := by
      rw [← biUnion_finset_add (fun r => (φ r : G → G) '' N) R B, ← hZdef, hZM]
      exact hcover
    have hCclosed : ∀ r ∈ (R : Set S), IsClosed ((φ r : G → G) '' N + B) := by
      intro r _
      exact ((hNmin.closed.isCompact.image (hcont r)).add hBclosed.isCompact).isClosed
    have hdense_int : Dense (⋃ r ∈ (R : Set S), interior ((φ r : G → G) '' N + B)) :=
      dense_biUnion_interior_of_closed (f := fun r => (φ r : G → G) '' N + B)
        hCclosed R.finite_toSet.countable hcover'
    obtain ⟨_, hx⟩ := hdense_int.nonempty
    rw [mem_iUnion] at hx
    obtain ⟨r₀, hx⟩ := hx
    rw [mem_iUnion] at hx
    obtain ⟨hr₀, hintr⟩ := hx
    -- `C` is `K n`-invariant
    have hCinv : ∀ k ∈ K n,
        (φ k : G → G) '' ((φ r₀ : G → G) '' N + B) ⊆ (φ r₀ : G → G) '' N + B := by
      have himgk : ∀ k ∈ K n,
          (φ k : G → G) '' ((φ r₀ : G → G) '' N) = (φ r₀ : G → G) '' N := by
        intro k hk
        have h1 : (φ k : G → G) '' ((φ r₀ : G → G) '' N) = (φ (k * r₀) : G → G) '' N := by
          rw [← image_comp (φ k : G → G) (φ r₀ : G → G) N]
          congr 1
          funext x
          show ((φ k : AddMonoid.End G) : G → G) (((φ r₀ : AddMonoid.End G) : G → G) x) =
            ((φ (k * r₀) : AddMonoid.End G) : G → G) x
          rw [map_mul]
          rfl
        have h2 : (φ (k * r₀) : G → G) '' N = (φ r₀ : G → G) '' N := by
          rw [mul_comm k r₀]
          exact hclass r₀ k hk
        exact h1.trans h2
      intro k hk z hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      have ha' : (φ k : G → G) a ∈ (φ r₀ : G → G) '' N := by
        rw [← himgk k hk]
        exact ⟨a, ha, rfl⟩
      exact ⟨(φ k : G → G) a, ha', (φ k : G → G) b, hBinv k ⟨b, hb, rfl⟩,
        (map_add (φ k) a b).symm⟩
    have hCuniv : (φ r₀ : G → G) '' N + B = univ :=
      hint n _ (hCclosed r₀ hr₀) hCinv ⟨_, hintr⟩
    -- (7) `T n ⊆ ν + B`
    obtain ⟨ν, hν⟩ : ((φ r₀ : G → G) '' N).Nonempty := hNmin.ne.image _
    refine ⟨ν, fun θ hθ => ?_⟩
    have hθC : θ ∈ (φ r₀ : G → G) '' N + B := by rw [hCuniv]; exact mem_univ θ
    obtain ⟨ν', hν', β, hβ, hθν⟩ := hθC
    have hθν' : θ - ν' ∈ B := by rw [← hθν, add_sub_cancel_left]; exact hβ
    -- the closed set of points `x` with `θ - x ∈ B`
    have hPclosed : IsClosed {x : G | θ - x ∈ B} :=
      hBclosed.preimage (continuous_const.sub continuous_id)
    -- every `K n`-word preserves the property
    have hstepB : ∀ x : G, θ - x ∈ B → ∀ k : K n,
        θ - (φ (k : S) : G → G) x ∈ B := by
      intro x hx k
      have hfix : (φ (k : S) : G → G) θ = θ := hKfix n (k : S) k.2 θ hθ
      have heq : θ - (φ (k : S) : G → G) x = (φ (k : S) : G → G) (θ - x) := by
        rw [map_sub, hfix]
      rw [heq]
      exact hBinv (k : S) ⟨θ - x, hx, rfl⟩
    have hword : ∀ (l : List (K n)) (x : G), θ - x ∈ B →
        θ - BerendMinimal.wordApply (fun k : K n => (φ (k : S) : G → G)) l x ∈ B := by
      intro l
      induction l with
      | nil =>
          intro x hx
          rw [BerendMinimal.wordApply_nil]
          exact hx
      | cons k l ih =>
          intro x hx
          rw [BerendMinimal.wordApply_cons]
          exact ih _ (hstepB x hx k)
    have hsub : BerendMinimal.semigroupOrbit (fun k : K n => (φ (k : S) : G → G)) ν' ⊆
        {x : G | θ - x ∈ B} := by
      rintro x ⟨l, rfl⟩
      exact hword l ν' hθν'
    have hclosure : ((φ r₀ : G → G) '' N) ⊆ {x : G | θ - x ∈ B} := by
      have h := (himgmin r₀).closure_semigroupOrbit (fun k : K n => hcont (k : S)) hν'
      rw [← h]
      exact hPclosed.closure_subset_iff.mpr hsub
    exact hclosure hν
  -- ## Assembling over the levels: a common point by compactness
  choose ν hν using step
  set A : ℕ → Set G := fun N => closure (ν '' {n : ℕ | N ≤ n}) with hAdef
  have hAclosed : ∀ N, IsClosed (A N) := fun N => isClosed_closure
  have hAanti : ∀ N, A (N + 1) ⊆ A N := by
    intro N
    refine closure_mono ?_
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Nat.le_trans (Nat.le_succ N) hm, rfl⟩
  have hAne : ∀ N, (A N).Nonempty := by
    intro N
    exact ⟨ν N, subset_closure ⟨N, mem_setOf.mpr le_rfl, rfl⟩⟩
  obtain ⟨νstar, hνstar⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hAanti hAne
      (hAclosed 0).isCompact hAclosed
  have hmain : ∀ n (θ : G), θ ∈ T n → θ - νstar ∈ B := by
    intro n θ hθ
    have hPclosed : IsClosed {x : G | θ - x ∈ B} :=
      hBclosed.preimage (continuous_const.sub continuous_id)
    have hsub : (ν '' {m : ℕ | n ≤ m}) ⊆ {x : G | θ - x ∈ B} := by
      rintro _ ⟨m, hm, rfl⟩
      exact hν m θ (hTmono n m hm hθ)
    have hAn : A n ⊆ {x : G | θ - x ∈ B} := by
      rw [hAdef]
      exact hPclosed.closure_subset_iff.mpr hsub
    exact hAn (mem_iInter.1 hνstar n)
  -- ## Density finishes
  have hclosedP : IsClosed {x : G | x - νstar ∈ B} :=
    hBclosed.preimage (continuous_id.sub continuous_const)
  have huniv : {x : G | x - νstar ∈ B} = univ := by
    have h1 : closure (⋃ n, T n) ⊆ {x : G | x - νstar ∈ B} :=
      hclosedP.closure_subset_iff.mpr (fun x hx => by
        rw [mem_iUnion] at hx
        obtain ⟨n, hn⟩ := hx
        exact hmain n x hn)
    rw [hdense.closure_eq] at h1
    exact eq_univ_of_univ_subset h1
  refine eq_univ_of_forall fun x => ?_
  have hx := huniv ▸ mem_univ (x + νstar)
  simpa using hx

end Main

end BerendIV1
end CubicTwoStage
