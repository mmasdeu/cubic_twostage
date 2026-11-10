/-
**Lemma 3.2** (classes of centres) and the unit-coercion bookkeeping it needs.
-/
import CubicTwoStage.Basic

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-- The inverse of a unit of a subring, read in the ambient field. -/
theorem subring_unit_inv_coe (𝒪 : Subring K) (u : 𝒪ˣ) :
    ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) = (((u : 𝒪) : K))⁻¹ := by
  have h : ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) * (((u : 𝒪) : K)) = 1 := by
    calc ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) * (((u : 𝒪) : K))
        = (((((u⁻¹ : 𝒪ˣ) : 𝒪) * (u : 𝒪)) : 𝒪) : K) := (map_mul 𝒪.subtype _ _).symm
      _ = 1 := by rw [Units.inv_mul]; exact map_one 𝒪.subtype
  exact eq_inv_of_mul_eq_one_left h

/-- **Lemma 3.2**.  Let `α ∈ 𝒪`, `α ≠ 0`, and let `U_α` be the image of `𝒪ˣ` in
`𝒪/α𝒪`.  The elements `[q₁,q₂]` with `q₂𝒪 = α𝒪` are exactly the elements of
`r/α + 𝒪` with `r ∈ U_α`; equivalently (absorbing the integral part) exactly the
elements `u/α + g` with `u ∈ 𝒪ˣ` and `g ∈ 𝒪`.

In particular there are at most `#(𝒪/α)ˣ` classes of centres with denominator
generating `α𝒪`. -/
theorem lem_classes (𝒪 : Subring K) {α : 𝒪} (hα : α ≠ 0) :
    {x : K | ∃ q1 q2 : 𝒪, Ideal.span {q2} = Ideal.span {α} ∧
        x = (q1 : K) + ((q2 : K))⁻¹}
      = {x : K | ∃ u : 𝒪ˣ, ∃ g : 𝒪,
        x = (((u : 𝒪) : K)) / (((α : 𝒪) : K)) + (g : K)} := by
  have hαK : (((α : 𝒪) : K)) ≠ 0 := fun h => hα (Subtype.ext h)
  ext x
  constructor
  · rintro ⟨q1, q2, hsp, rfl⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
    -- `hu : α = q2 * u`, so `q₂ = α * u⁻¹` in `𝒪` and hence in `K`.
    have hq2 : q2 = α * (u⁻¹ : 𝒪ˣ) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨u, q1, ?_⟩
    have hq2K : ((q2 : K)) = (((α : 𝒪) : K)) * ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) := by
      rw [hq2]; exact map_mul 𝒪.subtype _ _
    have hinv : (((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)))⁻¹ = (((u : 𝒪) : K)) := by
      rw [subring_unit_inv_coe 𝒪 u, inv_inv]
    rw [hq2K, mul_inv, hinv]
    ring
  · rintro ⟨u, g, rfl⟩
    refine ⟨g, α * (u⁻¹ : 𝒪ˣ), Ideal.span_singleton_eq_span_singleton.mpr ⟨u, ?_⟩, ?_⟩
    · rw [mul_assoc, Units.inv_mul, mul_one]
    · have hqK : (((α * (u⁻¹ : 𝒪ˣ) : 𝒪) : K))
          = (((α : 𝒪) : K)) * ((((u⁻¹ : 𝒪ˣ) : 𝒪) : K)) := map_mul 𝒪.subtype _ _
      rw [hqK, subring_unit_inv_coe 𝒪 u, mul_inv, inv_inv]
      ring

end CubicTwoStage
