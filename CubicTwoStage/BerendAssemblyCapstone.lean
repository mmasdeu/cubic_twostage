/-
# Capstone: Theorem 3.6 for the canonical complex cubic model with the old axiom
  eliminated, leaving *only* Stage I

Swarm `smw9665xe`, member m4, direction d3 (assembly).

This file composes

* `CubicTwoStage.BerendAssembly` (my `Assembly.lean`): the §5 assembly, which
  turns {Stage I, Proposition IV.1, expanding margin} into Berend's dichotomy for
  the unit–prime family and then into the paper-level Theorem 3.6;
* `CubicTwoStage.BerendIV1Arith` (member m1's verified file): Furstenberg's
  Proposition IV.1 for the unit–prime family from arithmetic alone (`p ≠ q`
  primes, `Nm π = p`), with no injectivity-on-levels hypothesis.

The composition leaves exactly **one** hypothesis beyond the paper's own
number theory: the annulus input `hann` of Stage I, tied to a margin member
`(u, j)`.  Nothing here uses `berend_multi_invariance`, and there is no `sorry`
and no new axiom.

Compile with

```
LEAN_PATH="$PWD:$PWD/.ultramath/smw9665xe/m1:$PWD/.ultramath/smw9665xe/m4:$LEAN_PATH" \
  lean .ultramath/smw9665xe/m4/Assembly2.lean
```
-/
import CubicTwoStage.BerendAssembly
import CubicTwoStage.BerendIV1Arith

open Set
open scoped Pointwise TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendAssembly

open NumberField NumberFieldCubic

/-! ## 1. Minimal-set torsion at the canonical model, from Stage I alone -/

section MinimalTorsion

variable {K : Type*} [Field K] [NumberField K]

/-- **Every point of every minimal closed invariant set is a torsion point**, for
the canonical model of a complex cubic field, with no arithmetic hypothesis
beyond the paper's (`hεpow`, `Nm π = p`, distinct primes `p ≠ q`) and Stage I. -/
theorem minimal_torsion_canonical (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (i : (numberFieldO K)ˣ × ℕ)
    (ha0 : 4 ≤ |((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2 0|)
    (hC : 16 ≤ normC (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct)
    {M : Set (Torus (canonicalFieldModel K h).lattice)}
    (hM : BerendMinimal.IsMinimalInvariant
      (fun i => (((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i :
        Torus (canonicalFieldModel K h).lattice → Torus (canonicalFieldModel K h).lattice)) M)
    {x : Torus (canonicalFieldModel K h).lattice} (hx : x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  haveI hdisc : DiscreteTopology
      (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    discreteTopology_canonicalFieldModel_lattice K h
  haveI hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    isZLattice_canonicalFieldModel_lattice K h
  exact minimal_torsion_unitPrime ((canonicalFieldModel K h).toModel ε π hπO hπ0) i ha0 hC
    hStage (BerendIV1Arith.propIV1_unitPrime'_canonical h ε π hπO hπ0 hεpow p q hp hq hpq hπN)
    hM hx

end MinimalTorsion

/-! ## 2. The paper-level theorem, with Stage I the only remaining input -/

section Main

variable {K : Type*} [Field K] [NumberField K]

/-- **Theorem 3.6 for the canonical complex cubic model with Berend's theorem
proved.**  Compare `NumberFieldCubic.thm_uncovered_canonical` (which consumes the
axiom `berend_multi_invariance`) and `thm_uncovered_canonical_corrected` (which
consumes the corrected Berend proposition `H`).  Here `H` is *proved*, and the
only hypothesis beyond the paper's own number theory is the Stage I annulus
input `hann`. -/
theorem thm_uncovered_canonical_stageI (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (m : ℕ)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : numberFieldO K), ∃ k : ℕ, ∃ hh ∈ numberFieldO K,
      (1 + π ^ m * ((g : numberFieldO K) : K)) - ((ε : numberFieldO K) : K) ^ k =
        π ^ (m + j) * hh)
    (p : ℕ) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (B1 : ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        ((((canonicalFieldModel K h).toModel ε π hπO hπ0).lact i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : (numberFieldO K)ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : (numberFieldO K)ˣ × ℕ,
        LinearMap.baseChange ℂ
          (((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt) x =
            μ i • x) →
      ∃ i : (numberFieldO K)ˣ × ℕ, 1 < ‖μ i‖)
    (q : ℕ) (hq : q.Prime) (hp' : p.Prime) (hpq : p ≠ q)
    (u : (numberFieldO K)ˣ) (j : ℕ)
    (h4 : 4 ≤ |((canonicalFieldModel K h).toModel ε π hπO hπ0).mult u j 0|)
    (h16 : 16 ≤ normC (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult u j))
    (hann : ∀ Y : Set (Torus (canonicalFieldModel K h).lattice), IsClosed Y → Y.Nonempty →
      (0 : Torus (canonicalFieldModel K h).lattice) ∈ closure (Y \ {0}) →
      BerendDichotomy.FamilyInvariant
        ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct Y →
      ∃ ρ1 ρ2 : ℝ, 0 < ρ1 ∧ ρ1 ≤ ρ2 ∧
        ‖cplxOf (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult u j)‖ * ρ1 ≤ ρ2 ∧
        ∀ w : Pt, w ∈ BerendBlockLastMile.cplxPlane →
          ρ1 ≤ ‖cplxOf w‖ → ‖cplxOf w‖ ≤ ρ2 →
          (QuotientAddGroup.mk' (canonicalFieldModel K h).lattice) w ∈ Y) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered (numberFieldO K) (numberFieldAbsNorm K)
      (canonicalFieldModel K h).σ, ∃ c ∈ F,
        (∃ y : K, c = (canonicalFieldModel K h).σ y) ∧
          x - c ∈ (canonicalFieldModel K h).lattice := by
  have hp1 : 1 < p := hp'.one_lt
  haveI hdisc : DiscreteTopology
      (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    discreteTopology_canonicalFieldModel_lattice K h
  haveI hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    isZLattice_canonicalFieldModel_lattice K h
  -- the unit is not critical at the real place
  have hε : |realEmbedding K h (((ε : numberFieldO K) : K))| ≠ 1 := by
    have h1 : lamAbs ((canonicalFieldModel K h).σ (((ε : numberFieldO K) : K))) 0 ≠ 1 :=
      BerendUnitNoncritical.lamAbs_real_ne_one (canonicalFieldModel K h) ε hεpow
    rw [lamAbs_zero_eq_abs] at h1
    simpa [NumberFieldCubic.canonicalFieldModel] using h1
  -- Stage I from the annulus input
  have hStage : BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
    BerendCofinality.zeroNonisolatedFull_canonical_torusAct_of_annulusInput
      (K := K) h ε π hπO hπ0 hε u j h16 hann
  -- Proposition IV.1 from the arithmetic, with no level hypothesis
  have hIV1 : BerendPropIV1.PropIV1
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
    BerendIV1Arith.propIV1_unitPrime'_canonical h ε π hπO hπ0 hεpow p q hp' hq hpq hπN
  -- the corrected Berend statement, proved
  have H : BerendMultiInvarianceCorrected ((numberFieldO K)ˣ × ℕ)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam
      (canonicalFieldModel K h).lattice
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_preserves
      hZL B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp1 hπN)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_comm :=
    berendMultiInvarianceCorrected_unitPrime
      ((canonicalFieldModel K h).toModel ε π hπO hπ0) (u, j) hZL h4 h16 hStage hIV1
      B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp1 hπN)
  exact thm_uncovered_field_corrected (canonicalFieldModel K h) ε π m hπO hπ0 hεpow hpadic
    hZL B1 p hp1 hπN B2 H

end Main

/-! ## 2'. The same theorem with Stage I taken directly

`thm_uncovered_canonical_stageI` routes Stage I through the annulus input.  For a
worker attacking Stage I in another form (`BerendBlockLastMile.zeroNonisolatedFull_iff_unboundedPlane`
gives the equivalent unbounded-plane form), this version takes the statement
itself. -/

section MainStageI

variable {K : Type*} [Field K] [NumberField K]

/-- **Theorem 3.6 for the canonical model, from Stage I stated directly.** -/
theorem thm_uncovered_canonical_of_stageI (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (m : ℕ)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : numberFieldO K), ∃ k : ℕ, ∃ hh ∈ numberFieldO K,
      (1 + π ^ m * ((g : numberFieldO K) : K)) - ((ε : numberFieldO K) : K) ^ k =
        π ^ (m + j) * hh)
    (p : ℕ) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (B1 : ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        ((((canonicalFieldModel K h).toModel ε π hπO hπ0).lact i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : (numberFieldO K)ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : (numberFieldO K)ˣ × ℕ,
        LinearMap.baseChange ℂ
          (((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt) x =
            μ i • x) →
      ∃ i : (numberFieldO K)ˣ × ℕ, 1 < ‖μ i‖)
    (q : ℕ) (hq : q.Prime) (hp' : p.Prime) (hpq : p ≠ q)
    (i : (numberFieldO K)ˣ × ℕ)
    (ha0 : 4 ≤ |((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2 0|)
    (hC : 16 ≤ normC (((canonicalFieldModel K h).toModel ε π hπO hπ0).mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct) :
    ∃ F : Finset Pt, ∀ x ∈ uncovered (numberFieldO K) (numberFieldAbsNorm K)
      (canonicalFieldModel K h).σ, ∃ c ∈ F,
        (∃ y : K, c = (canonicalFieldModel K h).σ y) ∧
          x - c ∈ (canonicalFieldModel K h).lattice := by
  have hp1 : 1 < p := hp'.one_lt
  haveI hdisc : DiscreteTopology
      (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    discreteTopology_canonicalFieldModel_lattice K h
  haveI hZL : IsZLattice ℝ (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
    isZLattice_canonicalFieldModel_lattice K h
  have hIV1 : BerendPropIV1.PropIV1
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
    BerendIV1Arith.propIV1_unitPrime'_canonical h ε π hπO hπ0 hεpow p q hp' hq hpq hπN
  have H : BerendMultiInvarianceCorrected ((numberFieldO K)ˣ × ℕ)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam
      (canonicalFieldModel K h).lattice
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_preserves
      hZL B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp1 hπN)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_comm :=
    berendMultiInvarianceCorrected_unitPrime
      ((canonicalFieldModel K h).toModel ε π hπO hπ0) i hZL ha0 hC hStage hIV1
      B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp1 hπN)
  exact thm_uncovered_field_corrected (canonicalFieldModel K h) ε π m hπO hπ0 hεpow hpadic
    hZL B1 p hp1 hπN B2 H

end MainStageI

/-! ## 3. Axiom audit -/

#print axioms CubicTwoStage.BerendAssembly.minimal_torsion_canonical
#print axioms CubicTwoStage.BerendAssembly.thm_uncovered_canonical_stageI
#print axioms CubicTwoStage.BerendAssembly.thm_uncovered_canonical_of_stageI

end BerendAssembly
end CubicTwoStage
