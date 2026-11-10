/-
**Theorem 3.3**: `2`-stage Euclideanity, covering by all regions, and covering of
the fundamental domain by finitely many regions.
-/
import CubicTwoStage.Basic
import CubicTwoStage.Cooke

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-! ### The algebraic equivalence `(i) ↔ (ii)` -/

/-- **Theorem 3.3, `(i) ↔ (ii)`**, in the algebraic model.

`(i)` `K` is 2-stage Euclidean; `(ii)` every element of `K` (i.e. every point of
`σ(K)`) lies in a region `V(q)`.  The hypothesis `hfrac` says that `K` is the
fraction field of `𝒪` (for `𝒪 = 𝓞 K` this is Mathlib's `IsFractionRing`). -/
theorem thm_equiv_i_ii (𝒪 : Subring K) (N : AbsNorm K)
    (hfrac : ∀ x : K, ∃ α ∈ 𝒪, ∃ β ∈ 𝒪, β ≠ 0 ∧ x = α / β) :
    IsTwoStageEuclidean 𝒪 N ↔
      ∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (x - (q1 + q2⁻¹)) < (N q2)⁻¹ := by
  constructor
  · intro h x
    obtain ⟨α, hα, β, hβ, hβ0, rfl⟩ := hfrac x
    exact prop_cooke 𝒪 N hα hβ hβ0 |>.mp (h α hα β hβ hβ0)
  · rintro h α hα β hβ hβ0
    exact prop_cooke 𝒪 N hα hβ hβ0 |>.mpr (h (α / β))

/-! ### The geometric equivalence `(ii) ↔ (iii)` -/

/-- **Theorem 3.3, `(ii) ↔ (iii)`**.

`C` is the set of centres and `V c` the region with centre `c`; the regions are
open, translating a centre by a lattice vector translates the region, and `C` is
closed under such translations.  The hypothesis `hfund` says that every point of
the model space is congruent modulo the lattice to a point of `unitCube`; for
`𝒪 = 𝓞 K` this holds with the basis `σ(w₁), σ(w₂), σ(w₃)`.

Note that `(ii) ⇒ (iii)` is compactness and `(iii) ⇒ (ii)` is translation
invariance — the direction `(i) ⇒ (ii)`, which is *not* compactness, is
Theorem 3.6. -/
theorem thm_equiv_ii_iii (L : AddSubgroup Pt) (C : Set Pt) (V : Pt → Set Pt)
    (hVopen : ∀ c, IsOpen (V c))
    (hVtrans : ∀ c g, g ∈ L → ∀ x, x ∈ V (c + g) ↔ x - g ∈ V c)
    (hCtrans : ∀ c ∈ C, ∀ g ∈ L, c + g ∈ C)
    (hfund : ∀ x : Pt, ∃ g ∈ L, x - g ∈ unitCube) :
    (∀ x : Pt, ∃ c ∈ C, x ∈ V c) ↔
      ∃ F : Finset Pt, (∀ c ∈ F, c ∈ C) ∧ unitCube ⊆ ⋃ c ∈ F, V c := by
  constructor
  · intro hcov
    have hc : unitCube ⊆ ⋃ c : C, V (c : Pt) := by
      intro x hx
      obtain ⟨c, hcC, hxc⟩ := hcov x
      exact Set.mem_iUnion.mpr ⟨⟨c, hcC⟩, hxc⟩
    obtain ⟨t, ht⟩ := isCompact_unitCube.elim_finite_subcover (fun c : C => V (c : Pt))
      (fun c => hVopen _) hc
    refine ⟨t.image Subtype.val, ?_, ?_⟩
    · intro c hc
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hc
      exact d.2
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact Set.mem_iUnion₂.mpr ⟨i.val, Finset.mem_image_of_mem _ hi, hxi⟩
  · rintro ⟨F, hFC, hcov⟩ x
    obtain ⟨g, hgL, hxg⟩ := hfund x
    obtain ⟨c, hcF, hxc⟩ := Set.mem_iUnion₂.mp (hcov hxg)
    exact ⟨c + g, hCtrans c (hFC c hcF) g hgL, (hVtrans c g hgL x).mpr hxc⟩

/-! ### Assembly -/

/-- **Theorem 3.3**, all three conditions together.

The two hypotheses `hBerend` and `hsub` are the bridge between the field `K` and
the model space `ℝ × ℂ`:

* `hsub` is immediate, since `σ(K) ⊆ ℝ × ℂ`;
* `hBerend` is **Theorem 3.6**, the only place where Berend's rigidity theorem
  for closed invariant subsets of tori is used.
-/
theorem thm_equiv (𝒪 : Subring K) (N : AbsNorm K)
    (hfrac : ∀ x : K, ∃ α ∈ 𝒪, ∃ β ∈ 𝒪, β ≠ 0 ∧ x = α / β)
    (L : AddSubgroup Pt) (C : Set Pt) (V : Pt → Set Pt)
    (hVopen : ∀ c, IsOpen (V c))
    (hVtrans : ∀ c g, g ∈ L → ∀ x, x ∈ V (c + g) ↔ x - g ∈ V c)
    (hCtrans : ∀ c ∈ C, ∀ g ∈ L, c + g ∈ C)
    (hfund : ∀ x : Pt, ∃ g ∈ L, x - g ∈ unitCube)
    (hBerend : (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (x - (q1 + q2⁻¹)) < (N q2)⁻¹) →
      (∀ x : Pt, ∃ c ∈ C, x ∈ V c))
    (hsub : (∀ x : Pt, ∃ c ∈ C, x ∈ V c) →
      (∀ x : K, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ N (x - (q1 + q2⁻¹)) < (N q2)⁻¹)) :
    (IsTwoStageEuclidean 𝒪 N ↔
        (∀ x : Pt, ∃ c ∈ C, x ∈ V c)) ∧
      (IsTwoStageEuclidean 𝒪 N ↔
        ∃ F : Finset Pt, (∀ c ∈ F, c ∈ C) ∧ unitCube ⊆ ⋃ c ∈ F, V c) := by
  have hii := thm_equiv_i_ii 𝒪 N hfrac
  have hbridge := thm_equiv_ii_iii L C V hVopen hVtrans hCtrans hfund
  constructor
  · constructor
    · intro h x; exact hBerend (hii.mp h) x
    · intro h; exact hii.mpr (hsub h)
  · constructor
    · intro h; exact hbridge.mp (hBerend (hii.mp h))
    · intro h; exact hii.mpr (hsub (hbridge.mpr h))

end CubicTwoStage
