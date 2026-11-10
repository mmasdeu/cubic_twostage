/-
# Stage I after Proposition 4.3: translated-subgroup nets close the torus

A single iterate of `b + H` lies in the closed forward-invariant set.  If the
images of `H` under suitable iterates are arbitrarily fine nets, the same
iterates of the translate meet every ball.  Closedness therefore gives the
whole torus, with no invariance assumption on `H`.

The second theorem combines this with the canonical B1/net theorem and the
normalized-arc/Proposition-4.2 input.  The third completes the entire canonical
Stage I branch in the explicit exact-modulus-one case.
-/
import CubicTwoStage.BerendCanonicalUnitPrime
import CubicTwoStage.BerendModulusOneArc

set_option linter.style.haveILetI false

open Set Filter Topology
open CubicTwoStage.BerendBlockLastMile

namespace CubicTwoStage
namespace BerendStageIProp43

section UnitPrime

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- Iterates of an additive hom preserve addition. -/
theorem iterate_map_add {T : Type*} [AddCommGroup T] (f : T →+ T) (n : ℕ)
    (x y : T) : f^[n] (x + y) = f^[n] x + f^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

/-- **Last mile after Berend's Proposition 4.3.** -/
theorem eq_univ_of_iterate_net_translate (D : UnitPrimeModel L 𝒪)
    (i : 𝒪ˣ × ℕ) {Y : Set (Torus L)} (hY : IsClosed Y)
    (hinv : ∀ h ∈ Y, D.torusAct i h ∈ Y)
    {b : Torus L} {H : AddSubgroup (Torus L)}
    (htranslate : ∀ h ∈ H, b + h ∈ Y)
    (hnet : ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, ∀ x : Torus L,
      ∃ h ∈ H, dist x ((D.torusAct i)^[n] h) < δ) :
    Y = Set.univ := by
  have hiter : ∀ n : ℕ, ∀ y ∈ Y, (D.torusAct i)^[n] y ∈ Y := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
        intro y hy
        rw [Function.iterate_succ_apply']
        exact hinv _ (ih y hy)
  rw [← hY.closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨n, hn⟩ := hnet δ hδ
  obtain ⟨h, hh, hdist⟩ := hn (x - (D.torusAct i)^[n] b)
  have hmem : (D.torusAct i)^[n] (b + h) ∈ Y :=
    hiter n _ (htranslate h hh)
  have heq : (D.torusAct i)^[n] (b + h) =
      (D.torusAct i)^[n] b + (D.torusAct i)^[n] h :=
    iterate_map_add (D.torusAct i) n b h
  refine ⟨(D.torusAct i)^[n] (b + h), hmem, ?_⟩
  rw [heq]
  calc
    dist x ((D.torusAct i)^[n] b + (D.torusAct i)^[n] h) =
        dist ((D.torusAct i)^[n] b + (x - (D.torusAct i)^[n] b))
          ((D.torusAct i)^[n] b + (D.torusAct i)^[n] h) := by
            have hs : (D.torusAct i)^[n] b + (x - (D.torusAct i)^[n] b) = x := by
              abel
            rw [hs]
    _ = dist (x - (D.torusAct i)^[n] b) ((D.torusAct i)^[n] h) :=
      dist_add_left _ _ _
    _ < δ := hdist

end UnitPrime

/-! ## Canonical normalized-arc assembly -/

section Canonical

variable {K : Type*} [Field K] [NumberField K]

/-- **Canonical Stage I from a normalized planar arc.**  The only analytic
input is the arc itself; Proposition 4.2 and Proposition 4.3 are filled by the
existing ray-subgroup and canonical B1/net results. -/
theorem eq_univ_canonical_of_arcThrough (hK : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    {p : ℕ} (hp : p.Prime) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1)
    {Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K hK).lattice)}
    (hY : IsClosed Y)
    (hinv : ∀ i, ((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).torusAct
      i '' Y ⊆ Y)
    {w₀ c : ℂ} {t' : ℝ} (hw₀ : w₀ ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (ht' : 0 < t')
    (harc : ∀ t ∈ Set.Icc (0 : ℝ) t',
      (QuotientAddGroup.mk' (NumberFieldCubic.canonicalFieldModel K hK).lattice)
        (BerendTangentNet.arcThrough w₀ c t) ∈ Y) :
    Y = Set.univ := by
  let D := (NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K hK).lattice) :=
    NumberFieldCubic.discreteTopology_canonicalFieldModel_lattice K hK
  letI : IsZLattice ℝ (AddSubgroup.toIntSubmodule
      (NumberFieldCubic.canonicalFieldModel K hK).lattice) :=
    NumberFieldCubic.isZLattice_canonicalFieldModel_lattice K hK
  letI : IsClosed ((NumberFieldCubic.canonicalFieldModel K hK).lattice : Set Pt) :=
    CubicTwoStage.isClosed_lattice
  obtain ⟨v, j, _hj, _ha, hC⟩ :=
    BerendUnitNoncritical.exists_mult_margin_of_pow_ne_one
      (NumberFieldCubic.canonicalFieldModel K hK) ε π hπO hπ0 hεpow p (by exact_mod_cast hp.two_le) hπN
  have hρ : 1 < ‖cplxOf (D.mult v j)‖ :=
    lt_of_lt_of_le (by norm_num) (BerendBlockLastMile.two_le_norm_cplxOf_of_normC hC)
  have hinva : ∀ x : Pt,
      (QuotientAddGroup.mk' (NumberFieldCubic.canonicalFieldModel K hK).lattice) x ∈ Y →
      (QuotientAddGroup.mk' (NumberFieldCubic.canonicalFieldModel K hK).lattice)
        (ptMul (D.mult v j) x) ∈ Y := by
    intro x hx
    have hm := hinv (v, j) (Set.mem_image_of_mem (D.torusAct (v, j)) hx)
    rwa [D.torusAct_mk', D.family_act_eq_ptMul] at hm
  obtain ⟨b, e, H, heplane, he, hHinf, hHclosed, hray, htranslate⟩ :=
    BerendRaySubgroup.exists_translate_raySubgroup_of_arc
      (a := D.mult v j) hY hρ hw₀ hc0 hc1 ht' hinva harc
  obtain ⟨i, hnet⟩ := BerendProp43Canonical.CanonicalProp43.exists_canonical_unitPrime_net
    hK ε π hπO hπ0 hp hπN hεpow
  apply eq_univ_of_iterate_net_translate D i hY
    (fun y hy => hinv i ⟨_, hy, rfl⟩) htranslate
  intro δ hδ
  exact hnet H hHinf hHclosed δ hδ

/-- **Complete canonical Stage I in the exact-modulus-one branch.**  The arc is
now supplied by the circle, so all analytic and Proposition-4.3 inputs are
 discharged. -/
theorem eq_univ_canonical_of_modulus_one (hK : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    {p : ℕ} (hp : p.Prime) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hεpow : ∀ n : ℕ, 0 < n → (((ε : numberFieldO K) : K)) ^ n ≠ 1)
    {Y : Set (Torus (NumberFieldCubic.canonicalFieldModel K hK).lattice)}
    (hY : IsClosed Y)
    (hinv : ∀ i, ((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).torusAct
      i '' Y ⊆ Y)
    {l k : ℤ} (hlk : l ≠ 0 ∨ k ≠ 0)
    (hmod : ‖cplxOf (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).unit_image ε)‖ ^ l *
      ‖cplxOf (((NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0).prime_image π)‖ ^ k = 1)
    (hacc : (0 : Pt) ∈ closure ((QuotientAddGroup.mk'
      (NumberFieldCubic.canonicalFieldModel K hK).lattice) ⁻¹' (Y \ {0}) ∩ cplxPlane)) :
    Y = Set.univ := by
  let D := (NumberFieldCubic.canonicalFieldModel K hK).toModel ε π hπO hπ0
  have hB3 : BerendPlanarArc.MultIndepPair
      (cplxOf (D.unit_image ε)) (cplxOf (D.prime_image π)) :=
    BerendModulusOneArc.multIndepPair_canonicalFieldModel
      hK ε π hπO hπ0 hεpow p (by exact_mod_cast hp.two_le) hπN
  obtain ⟨w₀, hw₀, harc⟩ := BerendModulusOneArc.exists_arcThrough_I_of_modulus_one
    D ε hY hinv hB3 hlk hmod hacc
  exact eq_univ_canonical_of_arcThrough
    (c := Complex.I) (t' := 1) hK ε π hπO hπ0 hp hπN hεpow hY hinv hw₀
    (by simp) (by intro h; have hi := congrArg Complex.im h; norm_num at hi)
    zero_lt_one harc

end Canonical

end BerendStageIProp43
end CubicTwoStage

#print axioms CubicTwoStage.BerendStageIProp43.eq_univ_of_iterate_net_translate
#print axioms CubicTwoStage.BerendStageIProp43.eq_univ_canonical_of_arcThrough
#print axioms CubicTwoStage.BerendStageIProp43.eq_univ_canonical_of_modulus_one
