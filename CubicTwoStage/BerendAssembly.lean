/-
# Assembly: Berend's Theorem 2.1 (dichotomy) for the unit–prime model, from Stage I
  and Furstenberg's Proposition IV.1

Swarm `smw9665xe`, member m4, direction d3 (part (b) of the objective: *assembly*,
not new algebra and not Stage I geometry).

The two deep inputs are

* `BerendDichotomy.ZeroNonisolatedFull D.torusAct` — Stage I (Berend §4);
* `BerendPropIV1.PropIV1 D.torusAct` — Furstenberg's Proposition IV.1, which the
  project has for this family as `BerendIV1Model.propIV1_unitPrime'`, from
  injectivity of the multipliers on the `q`-primary levels (`q` an ordinary
  prime).

This module *derives the dichotomy* for the concrete unit–prime model from those
two, discharging every intermediate hypothesis of the existing §5 assembly:

* continuity of the members (`D.continuous_torusAct`);
* finiteness of the kernels (`BerendFibre.finite_ker_torusAct`);
* finiteness of the `n`-torsion subgroups (`BerendLatticeIndex.finite_nsmul_torsion`);
* topological transitivity of the margin member
  (`BerendTransitive.topologicallyTransitive_torusAct_of_margin`);
* finiteness of every minimal closed invariant set, which is Berend's
  Proposition 5.1 from Stage I and Proposition IV.1
  (`BerendPropIV1.minimal_finite_of_propIV1`);
* **finiteness of the kernel of `g^m - g^n` for `m ≠ n`**, the one genuinely new
  computation here: on the lift, `g^m - g^n` is multiplication by
  `β = α^m - α^n`, where `α = D.mult u j` is the expanding member.  Both
  eigen-moduli of `α` are `≥ 4`, so `β` has nonzero norm form
  (`powC_sub_normR_ne`), hence multiplication by `β` is injective; discreteness
  of `L` then gives a finite kernel
  (`BerendFibre.finite_preimage_zero_of_continuous_injective`).

No `sorry`, no axiom, no use of `berend_multi_invariance`, and no new conditional
`Prop` wrapper: `hStage` and `hIV1` are the two named hypotheses of the imported
theorems, exactly as they appear in `BerendPropIV1.minimal_finite_of_propIV1`.
-/
import CubicTwoStage.BerendSec5
import CubicTwoStage.BerendPropIV1
import CubicTwoStage.BerendIV1Model
import CubicTwoStage.BerendFibre
import CubicTwoStage.BerendLatticeIndex
import CubicTwoStage.BerendExpandingMember
import CubicTwoStage.BerendBlockLastMile
import CubicTwoStage.BerendInterface
import CubicTwoStage.BerendCofinalityConcrete
import CubicTwoStage.BerendUnitNoncritical
import CubicTwoStage.ComplexCubicCorrected
import CubicTwoStage.Theorem36Corrected

open Set
open scoped Pointwise TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendAssembly

open NumberField NumberFieldCubic

/-! ## 1. `β = α^m - α^n` has nonzero norm form when the moduli of `α` are `≥ 4` -/

/-- Powers of a real number of modulus `> 1` are injective. -/
theorem real_pow_sub_ne {x : ℝ} (hx : 1 < |x|) {m n : ℕ} (hmn : m ≠ n) :
    x ^ m - x ^ n ≠ 0 := by
  intro h
  have h1 : |x ^ m| = |x ^ n| := by rw [sub_eq_zero.mp h]
  rw [abs_pow, abs_pow] at h1
  exact hmn (pow_right_injective₀ (by linarith) (ne_of_gt hx) h1)

/-- Powers of a complex number of modulus `> 1` are injective. -/
theorem complex_pow_sub_ne {z : ℂ} (hz : 1 < ‖z‖) {m n : ℕ} (hmn : m ≠ n) :
    z ^ m - z ^ n ≠ 0 := by
  intro h
  have h1 : ‖z ^ m‖ = ‖z ^ n‖ := by rw [sub_eq_zero.mp h]
  rw [norm_pow, norm_pow] at h1
  exact hmn (pow_right_injective₀ (by linarith) (ne_of_gt hz) h1)

/-- `cplxOf` is additive for the difference. -/
theorem cplxOf_sub (a b : Pt) : cplxOf (a - b) = cplxOf a - cplxOf b := by
  apply Complex.ext <;> simp [cplxOf, Pi.sub_apply]

/-- **The difference of two powers of a strongly expanding model element has
nonzero norm form.** -/
theorem powC_sub_normR_ne (a : Pt) (ha0 : 4 ≤ |a 0|) (hC : 16 ≤ normC a)
    {m n : ℕ} (hmn : m ≠ n) : normR (powC a m - powC a n) ≠ 0 := by
  have h4 : (1 : ℝ) < |a 0| := by linarith
  have hz4 : (1 : ℝ) < ‖cplxOf a‖ := by
    have hsq : (lamAbs a 1) ^ 2 = normC a := lamAbs_one_sq a
    have hnn : 0 ≤ lamAbs a 1 := lamAbs_one_nonneg a
    have hge : 4 ≤ lamAbs a 1 := by nlinarith
    rw [BerendCofinality.lamAbs_one_eq_norm_cplxOf] at hge
    linarith
  have hreal : (powC a m - powC a n) 0 = (a 0) ^ m - (a 0) ^ n := by
    simp [Pi.sub_apply, powC_apply_zero]
  have hcplx : cplxOf (powC a m - powC a n) =
      (cplxOf a) ^ m - (cplxOf a) ^ n := by
    rw [cplxOf_sub, BerendBlockLastMile.cplxOf_powC, BerendBlockLastMile.cplxOf_powC]
  intro hzero
  rw [normR_eq_zero_iff] at hzero
  rcases hzero with h0 | ⟨h1, h2⟩
  · exact real_pow_sub_ne (x := a 0) h4 hmn (by rw [← hreal]; exact h0)
  · have hne : cplxOf (powC a m - powC a n) ≠ 0 := by
      rw [hcplx]; exact complex_pow_sub_ne (z := cplxOf a) hz4 hmn
    exact hne (by apply Complex.ext <;> simp [cplxOf, h1, h2])

/-- `(a - b) ⋆ c = a ⋆ c - b ⋆ c`. -/
theorem sub_mulC (a b c : Pt) : (a - b) ⋆ c = a ⋆ c - b ⋆ c := by
  have h : (a - b) ⋆ c + b ⋆ c = a ⋆ c := by
    rw [← add_mulC, sub_add_cancel]
  rw [← h, add_sub_cancel_right]

/-! ## 2. The iterates of `D.torusAct i` on the lift -/

section Model

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The lift-level endomorphism underlying `D.torusAct i`: multiplication by the
family multiplier `D.mult i.1 i.2`. -/
noncomputable def liftAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) : Pt →+ Pt :=
  addHomMulC (D.mult i.1 i.2)

/-- `D.torusAct i` is multiplication by the multiplier on classes. -/
theorem torusAct_apply_mk' (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (x : Pt) :
    D.torusAct i (QuotientAddGroup.mk' L x) =
      QuotientAddGroup.mk' L (D.mult i.1 i.2 ⋆ x) := by
  rw [UnitPrimeModel.torusAct_mk', UnitPrimeModel.family_apply]

/-- **The `m`-th iterate of `D.torusAct i` on the lift** is multiplication by the
`m`-th power of the multiplier. -/
theorem iterate_torusAct_apply_mk' (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (m : ℕ) (x : Pt) :
    (D.torusAct i)^[m] (QuotientAddGroup.mk' L x) =
      QuotientAddGroup.mk' L (powC (D.mult i.1 i.2) m ⋆ x) := by
  induction m generalizing x with
  | zero => simp [oneC_mulC]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, torusAct_apply_mk', powC_succ, mulC_assoc]

/-- The lattice is preserved by multiplication by `α^m - α^n`. -/
theorem lattice_preserves_diff (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (m n : ℕ) :
    L ≤ L.comap (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n)) := by
  intro g hg
  show addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) g ∈ L
  show (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) ⋆ g ∈ L
  rw [sub_mulC]
  refine L.sub_mem ?_ ?_
  · rw [powC_mult]; exact D.lattice (i.1 ^ m) (i.2 * m) g hg
  · rw [powC_mult]; exact D.lattice (i.1 ^ n) (i.2 * n) g hg

/-- The kernel of `g^m - g^n` on the torus is contained in the kernel of
multiplication by `α^m - α^n`. -/
theorem diff_ker_subset (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) {m n : ℕ}
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (hL : L ≤ L.comap (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n))) :
    ((BerendSec5.iterHom (D.torusAct i) m - BerendSec5.iterHom (D.torusAct i) n) ⁻¹'
        {(0 : Torus L)}) ⊆
      ((QuotientAddGroup.map L L
        (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n)) hL) ⁻¹'
        {(0 : Torus L)}) := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
  have hzEq : (D.torusAct i)^[m] (QuotientAddGroup.mk' L x) =
      (D.torusAct i)^[n] (QuotientAddGroup.mk' L x) := by
    have h := hz
    rw [AddMonoidHom.sub_apply, BerendSec5.iterHom_apply, BerendSec5.iterHom_apply] at h
    exact sub_eq_zero.mp h
  rw [iterate_torusAct_apply_mk', iterate_torusAct_apply_mk'] at hzEq
  have hmem : (powC (D.mult i.1 i.2) m ⋆ x) - (powC (D.mult i.1 i.2) n ⋆ x) ∈ L :=
    QuotientAddGroup.eq_iff_sub_mem.mp hzEq
  show QuotientAddGroup.mk' L
    (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) x) = 0
  rw [BerendLatticeIndex.mk'_eq_zero_iff]
  show (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) ⋆ x ∈ L
  rw [sub_mulC]
  exact hmem

/-- **Finiteness of the kernel of `g^m - g^n`** for the expanding family member:
on the lift the difference of powers is multiplication by `β = α^m - α^n`, whose
norm form is nonzero, hence injective; discreteness of `L` makes the kernel in
the torus finite. -/
theorem diff_ker_finite (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    {m n : ℕ} (hmn : m ≠ n) :
    ((BerendSec5.iterHom (D.torusAct i) m - BerendSec5.iterHom (D.torusAct i) n) ⁻¹'
      {(0 : Torus L)}).Finite := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  have hβ : normR (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) ≠ 0 :=
    powC_sub_normR_ne _ ha0 hC hmn
  have hL : L ≤ L.comap
      (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n)) :=
    lattice_preserves_diff D i m n
  have hinj : Function.Injective
      (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n)) := by
    intro x y hxy
    have hzero : addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzero' : (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n) ⋆ (x - y) = 0 := hzero
    exact sub_eq_zero.mp (mulC_eq_zero hβ hzero')
  have hfin : ((QuotientAddGroup.map L L
      (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n)) hL) ⁻¹'
      {(0 : Torus L)}).Finite :=
    BerendFibre.finite_preimage_zero_of_continuous_injective
      (addHomMulC (powC (D.mult i.1 i.2) m - powC (D.mult i.1 i.2) n))
      (continuous_mulC _) hinj hL
  exact Set.Finite.subset hfin (diff_ker_subset D i hL)

end Model

/-! ## 2'. Finite fibres of an additive endomorphism with finite kernel -/

/-- An additive endomorphism with finite kernel has finite fibres: the fibre over
`y` is the translate of the kernel by any preimage of `y`. -/
theorem finite_fibre_of_finite_ker {G : Type*} [AddCommGroup G] (φ : G →+ G)
    (hker : (φ ⁻¹' {(0 : G)}).Finite) (y : G) : {x : G | φ x = y}.Finite := by
  rcases Set.eq_empty_or_nonempty {x : G | φ x = y} with hem | ⟨a, ha⟩
  · rw [hem]; exact Set.finite_empty
  · have ha' : φ a = y := ha
    have heq : {x : G | φ x = y} = (fun k => a + k) '' (φ ⁻¹' {(0 : G)}) := by
      ext x
      constructor
      · intro hx
        have hx' : φ x = y := hx
        refine ⟨x - a, ?_, by abel⟩
        show φ (x - a) = 0
        rw [map_sub, hx', ha', sub_self]
      · rintro ⟨k, hk, rfl⟩
        have hk' : φ k = 0 := hk
        show φ (a + k) = y
        rw [map_add, hk', add_zero]
        exact ha'
    rw [heq]
    exact hker.image _

/-! ## 2''. A weaker form of Stage I that suffices

Stage I asks a closed invariant set with `0` a non-isolated point to be
everything.  Given a topologically transitive member — which the margin member
supplies (`BerendTransitive.topologicallyTransitive_torusAct_of_margin`) — it is
enough that such a set have *nonempty interior*: `BerendSec5`'s last step then
promotes interior to the whole space.  This is the form a Stage I argument
reaches first (accumulation at `0` produces a bounded piece of the lift, i.e.
interior), and it is strictly weaker than the unbounded-plane form. -/

section WeakStageI

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {ι : Type*} {F : ι → G →+ G}

/-- **Stage I from its interior form.** -/
theorem zeroNonisolatedFull_of_interior_of_transitive
    (hInt : ∀ E : Set G, IsClosed E → E.Nonempty →
      (0 : G) ∈ closure (E \ {0}) → BerendDichotomy.FamilyInvariant F E →
      (interior E).Nonempty)
    (htrans : ∃ i, BerendSec5.TopologicallyTransitive (⇑(F i))) :
    BerendDichotomy.ZeroNonisolatedFull F := by
  intro E hE hne hacc hinv
  obtain ⟨i, hi⟩ := htrans
  exact BerendSec5.eq_univ_of_isClosed_of_interior_of_transitive hE
    (hinv i) (hInt E hE hne hacc hinv) hi

end WeakStageI

/-! ## 3. The dichotomy for the unit–prime model, and minimal-set torsion -/

section Assembly

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- **Berend's Theorem 2.1 (dichotomy) for the unit–prime model `Σ = {μ_{uπ^j}}`,
from Stage I and Furstenberg's Proposition IV.1.**

This is the statement of the old axiom `berend_multi_invariance` for the
concrete family, with the axiom replaced by the two deep inputs.  Every other
hypothesis of `BerendSec5.dichotomy_of_stageI_of_minimal_finite` is discharged
here: continuity, finite kernels, finite `n`-torsion, finiteness of minimal sets
(Proposition 5.1 from Proposition IV.1 + Stage I), finite kernels of `g^m - g^n`
(§2 above) and topological transitivity of the margin member. -/
theorem dichotomy_unitPrime (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hIV1 : BerendPropIV1.PropIV1 D.torusAct) :
    BerendDichotomy.Dichotomy D.torusAct := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  haveI : Nontrivial (Torus L) := BerendInterface.nontrivial_torus
  refine BerendSec5.dichotomy_of_stageI_of_minimal_finite (F := D.torusAct) hStage
    (fun i => D.continuous_torusAct i) (fun i => BerendFibre.finite_ker_torusAct D i)
    (fun n hn => BerendLatticeIndex.finite_nsmul_torsion n hn) ?_ ?_ ?_
  · intro M _ _ _ hMmin
    exact BerendPropIV1.minimal_finite_of_propIV1 hStage hIV1 hMmin
  · exact ⟨i, fun m n hmn => diff_ker_finite D i ha0 hC hmn⟩
  · exact ⟨i, BerendTransitive.topologicallyTransitive_torusAct_of_margin D i.1 i.2 ha0 hC⟩

/-- **The axiom's conclusion for the unit–prime family**, in the exact form of
`UnitPrimeModel.berend`: a closed nonempty invariant proper subset of the torus is
finite — now proved, not assumed. -/
theorem finite_of_closed_invariant_unitPrime (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hIV1 : BerendPropIV1.PropIV1 D.torusAct)
    (Y : Set (Torus L)) (hclosed : IsClosed Y) (hne : Y.Nonempty)
    (hinv : ∀ i : 𝒪ˣ × ℕ, D.torusAct i '' Y ⊆ Y) (hproper : Y ≠ univ) : Y.Finite :=
  dichotomy_unitPrime D i ha0 hC hStage hIV1 Y hclosed hne hinv hproper

/-- **Berend's Proposition 5.1 for the unit–prime family**: every nonempty minimal
closed invariant subset of the torus is finite. -/
theorem minimal_finite_unitPrime (D : UnitPrimeModel L 𝒪)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hIV1 : BerendPropIV1.PropIV1 D.torusAct)
    {M : Set (Torus L)}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (D.torusAct i : Torus L → Torus L)) M) :
    M.Finite := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  haveI : Nontrivial (Torus L) := BerendInterface.nontrivial_torus
  exact BerendPropIV1.minimal_finite_of_propIV1 hStage hIV1 hM

/-- **Every point of a minimal closed invariant set is torsion** (Berend §5,
Proposition 5.1 + Lemma 5.2) for the unit–prime family. -/
theorem minimal_torsion_unitPrime (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hIV1 : BerendPropIV1.PropIV1 D.torusAct)
    {M : Set (Torus L)}
    (hM : BerendMinimal.IsMinimalInvariant (fun i => (D.torusAct i : Torus L → Torus L)) M)
    {x : Torus L} (hx : x ∈ M) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  haveI : Nontrivial (Torus L) := BerendInterface.nontrivial_torus
  refine BerendPropIV1.exists_pos_nsmul_eq_zero_of_mem_minimal hStage hIV1 i ?_ hM hx
  intro m n hmn
  refine finite_fibre_of_finite_ker (BerendPropIV1.diffHom (D.torusAct i) n m) ?_ 
  have hEq : (BerendPropIV1.diffHom (D.torusAct i) n m) ⁻¹' {(0 : Torus L)} =
      (BerendSec5.iterHom (D.torusAct i) n - BerendSec5.iterHom (D.torusAct i) m) ⁻¹'
        {(0 : Torus L)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, BerendPropIV1.diffHom_apply,
      AddMonoidHom.sub_apply, BerendSec5.iterHom_apply]
  rw [hEq]
  exact diff_ker_finite D i ha0 hC (Ne.symm hmn)

/-- **The dichotomy from injectivity on the `q`-primary levels**, i.e. from the
arithmetic input of `BerendIV1Model.propIV1_unitPrime'` and Stage I. -/
theorem dichotomy_unitPrime_of_levelInj (D : UnitPrimeModel L 𝒪) (q : ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (hinj : ∀ (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ),
      ∀ x ∈ BerendIV1Model.lvlSet L q n, ∀ y ∈ BerendIV1Model.lvlSet L q n,
        (BerendIV1Model.familyHom D s) x = (BerendIV1Model.familyHom D s) y → x = y)
    (hq : 2 ≤ q) (i : 𝒪ˣ × ℕ)
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct) :
    BerendDichotomy.Dichotomy D.torusAct :=
  dichotomy_unitPrime D i ha0 hC hStage
    (BerendIV1Model.propIV1_unitPrime' D q hinj hq i.1 i.2 ha0 hC)

end Assembly

/-! ## 5. The corrected Berend statement for the unit–prime family

`BerendMultiInvarianceCorrected` (`CubicTwoStage/BerendCorrected.lean`) is the
*corrected* form of the old axiom: (B3) is replaced by rational independence and
commutation is explicit.  Its conclusion is the dichotomy for `D.torusEndAct`,
which is the same endomorphism as `D.torusAct`.  Hence the assembly of §3 proves
it — with `B1`, `B2`, `B3`, `hcomm` no longer used at all, and Stage I plus
Proposition IV.1 as the only inputs. -/

section Corrected

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The two names of the same torus endomorphism. -/
theorem torusAct_eq_torusEndAct (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    D.torusAct i = D.torusEndAct i := rfl

/-- **The corrected Berend statement, proved** (no axiom), for the unit–prime
family, from Stage I and Proposition IV.1 and the expanding margin. -/
theorem berendMultiInvarianceCorrected_unitPrime (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hZ : IsZLattice ℝ (AddSubgroup.toIntSubmodule L))
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hIV1 : BerendPropIV1.PropIV1 D.torusAct)
    (B1 : ∃ j : 𝒪ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly ((D.lactZ j) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : 𝒪ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ j : 𝒪ˣ × ℕ, LinearMap.baseChange ℂ ((D.linFam j : Pt →ₗ[ℝ] Pt)) x = μ j • x) →
      ∃ j : 𝒪ˣ × ℕ, 1 < ‖μ j‖)
    (B3 : RationallyIndependentPair D.linFam) :
    BerendMultiInvarianceCorrected (𝒪ˣ × ℕ) D.linFam L D.linFam_preserves hZ B1 B2 B3
      D.linFam_comm :=
  dichotomy_unitPrime D i ha0 hC hStage hIV1

end Corrected

/-! ## 6. The paper-level statement: Theorem 3.6 for the canonical model, with the
axiom replaced by the two explicit obligations

`NumberFieldCubic.thm_uncovered_canonical_corrected` takes Berend's statement as
the proposition `H`.  §5 above *proves* `H` for the unit–prime family from Stage I
and Proposition IV.1, so the paper-level theorem follows with those two inputs in
place of the axiom.  Concretely, the remaining hypotheses are

* `hinj` — injectivity of every multiplier `μ_{uπ^j}` on the `q`-primary torsion
  levels (`q` an ordinary prime); this is the arithmetic input of
  `BerendIV1Model.propIV1_unitPrime'`, i.e. the "`q ∤ p`" content;
* `hann` — the annulus input of Stage I
  (`BerendCofinality.zeroNonisolatedFull_canonical_torusAct_of_annulusInput`);
* the paper's own number-theoretic inputs `hεpow`, `hpadic`, `Nm π = p > 1`, and
  (B1), (B2) — the last two only as *inert* arguments of the corrected Berend
  proposition, since its body does not mention them. -/

section Canonical

variable {K : Type*} [Field K] [NumberField K]

/-- **Theorem 3.6 for the canonical complex cubic model, with Berend's theorem
proved** (Stage I + Proposition IV.1 instead of the axiom). -/
theorem thm_uncovered_canonical_proved (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (m : ℕ)
    (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (hεpow : ∀ n : ℕ, 0 < n → (ε : K) ^ n ≠ 1)
    (hpadic : ∀ (j : ℕ) (g : numberFieldO K), ∃ k : ℕ, ∃ hh ∈ numberFieldO K,
      (1 + π ^ m * ((g : numberFieldO K) : K)) - ((ε : numberFieldO K) : K) ^ k =
        π ^ (m + j) * hh)
    (p : ℕ) (hp : 1 < p) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (B1 : ∃ i : (numberFieldO K)ˣ × ℕ, ∀ n : ℕ, 0 < n →
      Irreducible (LinearMap.charpoly
        ((((canonicalFieldModel K h).toModel ε π hπO hπ0).lact i) ^ n)))
    (B2 : ∀ (x : ℂ ⊗[ℝ] Pt) (μ : (numberFieldO K)ˣ × ℕ → ℂ), x ≠ 0 →
      (∀ i : (numberFieldO K)ˣ × ℕ,
        LinearMap.baseChange ℂ
          (((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam i : Pt →ₗ[ℝ] Pt) x =
            μ i • x) →
      ∃ i : (numberFieldO K)ˣ × ℕ, 1 < ‖μ i‖)
    (q : ℕ) (hq : 2 ≤ q)
    (hinj : ∀ (s : (numberFieldO K)ˣ × Multiplicative ℕ) (n : ℕ),
      ∀ x ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
        ∀ y ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
          (BerendIV1Model.familyHom
              ((canonicalFieldModel K h).toModel ε π hπO hπ0) s) x =
            (BerendIV1Model.familyHom
              ((canonicalFieldModel K h).toModel ε π hπO hπ0) s) y → x = y)
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
  haveI hdisc : DiscreteTopology (AddSubgroup.toIntSubmodule (canonicalFieldModel K h).lattice) :=
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
  -- Proposition IV.1 from injectivity on the q-primary levels
  have hIV1 : BerendPropIV1.PropIV1
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct :=
    BerendIV1Model.propIV1_unitPrime'
      ((canonicalFieldModel K h).toModel ε π hπO hπ0) q hinj hq u j h4 h16
  -- the corrected Berend statement, proved
  have H : BerendMultiInvarianceCorrected ((numberFieldO K)ˣ × ℕ)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam
      (canonicalFieldModel K h).lattice
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_preserves
      hZL B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp hπN)
      ((canonicalFieldModel K h).toModel ε π hπO hπ0).linFam_comm :=
    berendMultiInvarianceCorrected_unitPrime
      ((canonicalFieldModel K h).toModel ε π hπO hπ0) (u, j) hZL h4 h16 hStage hIV1
      B1 B2
      (rational_independence_corrected (canonicalFieldModel K h) ε π hπO hπ0 hεpow p hp hπN)
  exact thm_uncovered_field_corrected (canonicalFieldModel K h) ε π m hπO hπ0 hεpow hpadic
    hZL B1 p hp hπN B2 H

end Canonical

/-! ## 7. Reducing `hinj` to the single prime multiplier

`BerendIV1Model.propIV1_unitPrime'` needs every multiplier `μ_{uπ^j}` to act
*injectively* on the `q`-primary levels.  That hypothesis is redundant: the unit
part `μ_u` is injective on the whole torus (multiplication by `u^{-1}` inverts it
and preserves `L`) and the prime part `μ_{π^j}` is the `j`-th iterate of the
single multiplier `μ_π = D.torusAct (1,1)`.  Hence it suffices to know
injectivity of `μ_π` on the levels — the form in which the arithmetic statement
"`q ∤ Nm π`" enters. -/

section LevelInj

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The diagonal multiplier `(1,1)` is the prime multiplier. -/
theorem mult_one_eq_prime (D : UnitPrimeModel L 𝒪) :
    D.mult 1 1 = D.prime_image D.prime := by
  show D.unit_image 1 ⋆ powC (D.prime_image D.prime) 1 = D.prime_image D.prime
  rw [powC_succ, powC_zero, mulC_oneC, D.unit_one, oneC_mulC]

/-- The multiplier of `(1,j)` is the `j`-th power of the prime multiplier. -/
theorem mult_one_right (D : UnitPrimeModel L 𝒪) (j : ℕ) :
    D.mult 1 j = powC (D.prime_image D.prime) j := by
  show D.unit_image 1 ⋆ powC (D.prime_image D.prime) j = _
  rw [D.unit_one, oneC_mulC]

/-- The multiplier of `(u,0)` is the unit multiplier. -/
theorem mult_zero (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) :
    D.mult u 0 = D.unit_image u := by
  show D.unit_image u ⋆ powC (D.prime_image D.prime) 0 = _
  rw [powC_zero, mulC_oneC]

/-- **`μ_{π^j}` is the `j`-th iterate of `μ_π`.** -/
theorem torusAct_one_eq_iterate_mk' (D : UnitPrimeModel L 𝒪) (j : ℕ) (x : Pt) :
    D.torusAct (1, j) (QuotientAddGroup.mk' L x) =
      (D.torusAct (1, 1))^[j] (QuotientAddGroup.mk' L x) := by
  rw [torusAct_apply_mk', iterate_torusAct_apply_mk', mult_one_eq_prime, mult_one_right]

/-- As an equality of functions. -/
theorem torusAct_one_eq_iterate (D : UnitPrimeModel L 𝒪) (j : ℕ) :
    D.torusAct (1, j) = (D.torusAct (1, 1))^[j] := by
  funext z
  induction z using QuotientAddGroup.induction_on with
  | _ x => exact torusAct_one_eq_iterate_mk' D j x

/-- **`μ_{uπ^j}` factors as `μ_u` after `μ_{π^j}`.** -/
theorem torusAct_split_mk' (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (x : Pt) :
    D.torusAct (u, j) (QuotientAddGroup.mk' L x) =
      D.torusAct (u, 0) (D.torusAct (1, j) (QuotientAddGroup.mk' L x)) := by
  show QuotientAddGroup.mk' L (D.mult u j ⋆ x) =
    QuotientAddGroup.mk' L (D.mult u 0 ⋆ (D.mult 1 j ⋆ x))
  rw [mult_zero, mult_one_right,
    show D.mult u j = D.unit_image u ⋆ powC (D.prime_image D.prime) j from rfl, mulC_assoc]

/-- As a pointwise statement on the torus. -/
theorem torusAct_split (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (z : Torus L) :
    D.torusAct (u, j) z = D.torusAct (u, 0) (D.torusAct (1, j) z) := by
  induction z using QuotientAddGroup.induction_on with
  | _ x => exact torusAct_split_mk' D u j x

/-- **The unit multiplier is injective**: multiplication by `u^{-1}` is a left
inverse on the lift and preserves the lattice. -/
theorem injective_torusAct_unit (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) :
    Function.Injective (D.torusAct (u, 0)) := by
  intro z w hzw
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective L w
  rw [torusAct_apply_mk', torusAct_apply_mk', mult_zero] at hzw
  have hmem : (D.unit_image u ⋆ x) - (D.unit_image u ⋆ y) ∈ L :=
    QuotientAddGroup.eq_iff_sub_mem.mp hzw
  have h2 : D.unit_inv u ⋆ ((D.unit_image u ⋆ x) - (D.unit_image u ⋆ y)) ∈ L :=
    D.lattice_unit_inv u _ hmem
  rw [mulC_sub, ← mulC_assoc, ← mulC_assoc, mulC_comm (D.unit_inv u) (D.unit_image u),
    D.unit_inv_mul, oneC_mulC, oneC_mulC] at h2
  exact QuotientAddGroup.eq_iff_sub_mem.mpr h2

/-- Iterates of a self-map that maps a set into itself stay in the set. -/
theorem iterate_mapsTo {G : Type*} (φ : G → G) {T : Set G} (hmaps : φ '' T ⊆ T) :
    ∀ j : ℕ, ∀ x ∈ T, φ^[j] x ∈ T := by
  intro j
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hmaps ⟨_, ih x hx, rfl⟩

/-- An iterate of a self-map that is injective on a set and maps the set into
itself is injective on the set. -/
theorem iterate_injOn_of_injOn {G : Type*} (φ : G → G) {T : Set G}
    (hmaps : φ '' T ⊆ T) (hinj : ∀ x ∈ T, ∀ y ∈ T, φ x = φ y → x = y) :
    ∀ j : ℕ, ∀ x ∈ T, ∀ y ∈ T, φ^[j] x = φ^[j] y → x = y := by
  intro j
  induction j with
  | zero =>
      intro x _ y _ h
      simpa using h
  | succ j ih =>
      intro x hx y hy h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      exact ih x hx y hy (hinj _ (iterate_mapsTo φ hmaps j x hx) _
        (iterate_mapsTo φ hmaps j y hy) h)

/-- **Injectivity of the single prime multiplier on the `q`-primary levels
implies the hypothesis `hinj` of `propIV1_unitPrime'`.** -/
theorem levelInj_of_prime_levelInj (D : UnitPrimeModel L 𝒪) (q : ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (hπ : ∀ n : ℕ, ∀ x ∈ BerendIV1Model.lvlSet L q n,
      ∀ y ∈ BerendIV1Model.lvlSet L q n,
        D.torusAct (1, 1) x = D.torusAct (1, 1) y → x = y) :
    ∀ (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ),
      ∀ x ∈ BerendIV1Model.lvlSet L q n, ∀ y ∈ BerendIV1Model.lvlSet L q n,
        (BerendIV1Model.familyHom D s) x = (BerendIV1Model.familyHom D s) y → x = y := by
  rintro ⟨u, j⟩ n x hx y hy hxy
  have hxy' : D.torusAct (u, j.toAdd) x = D.torusAct (u, j.toAdd) y := hxy
  -- step 1: cancel the unit part
  have h1 : D.torusAct (1, j.toAdd) x = D.torusAct (1, j.toAdd) y := by
    apply injective_torusAct_unit D u
    rw [← torusAct_split D u j.toAdd x, ← torusAct_split D u j.toAdd y]
    exact hxy'
  -- step 2: `μ_{π^j}` is the `j`-th iterate of `μ_π`
  have h2 : (D.torusAct (1, 1))^[j.toAdd] x = (D.torusAct (1, 1))^[j.toAdd] y := by
    rw [← torusAct_one_eq_iterate]
    exact h1
  have hmaps : D.torusAct (1, 1) '' BerendIV1Model.lvlSet L q n ⊆
      BerendIV1Model.lvlSet L q n := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact BerendIV1Model.familyHom_image_lvlSet D q (1, Multiplicative.ofAdd 1) n
      ⟨w, hw, rfl⟩
  exact iterate_injOn_of_injOn (D.torusAct (1, 1)) hmaps (hπ n) j.toAdd x hx y hy h2

end LevelInj

/-! ## 8. The residual obligation in single-generator form

Composing §7 with §6: the paper-level theorem holds as soon as the *single*
multiplier `μ_π` is injective on the `q`-primary levels and the annulus input
`hann` holds.  This is the smallest form of the arithmetic obligation that the
assembly needs. -/

section SingleGenerator

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- **The dichotomy from injectivity of `μ_π` alone** on the `q`-primary levels. -/
theorem dichotomy_unitPrime_of_primeLevelInj (D : UnitPrimeModel L 𝒪) (q : ℕ)
    [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]
    (hπ : ∀ n : ℕ, ∀ x ∈ BerendIV1Model.lvlSet L q n,
      ∀ y ∈ BerendIV1Model.lvlSet L q n,
        D.torusAct (1, 1) x = D.torusAct (1, 1) y → x = y)
    (hq : 2 ≤ q) (i : 𝒪ˣ × ℕ)
    (ha0 : 4 ≤ |D.mult i.1 i.2 0|) (hC : 16 ≤ normC (D.mult i.1 i.2))
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct) :
    BerendDichotomy.Dichotomy D.torusAct :=
  dichotomy_unitPrime D i ha0 hC hStage
    (BerendIV1Model.propIV1_unitPrime' D q (levelInj_of_prime_levelInj D q hπ) hq
      i.1 i.2 ha0 hC)

end SingleGenerator

/-! ## 9. The canonical model: `hinj` from the single prime multiplier -/

section CanonicalLevelInj

variable {K : Type*} [Field K] [NumberField K]

/-- **For the canonical model, the `hinj` hypothesis of
`thm_uncovered_canonical_proved` follows from injectivity of the single
multiplier `μ_π` on the `q`-primary levels.** -/
theorem hinj_canonical_of_primeLevelInj (h : IsComplexCubic K)
    (ε : Units (numberFieldO K)) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (q : ℕ)
    (hπ : ∀ n : ℕ,
      ∀ x ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
        ∀ y ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
          ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct (1, 1) x =
            ((canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct (1, 1) y → x = y) :
    ∀ (s : (numberFieldO K)ˣ × Multiplicative ℕ) (n : ℕ),
      ∀ x ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
        ∀ y ∈ BerendIV1Model.lvlSet (canonicalFieldModel K h).lattice q n,
          (BerendIV1Model.familyHom
              ((canonicalFieldModel K h).toModel ε π hπO hπ0) s) x =
            (BerendIV1Model.familyHom
              ((canonicalFieldModel K h).toModel ε π hπO hπ0) s) y → x = y :=
  levelInj_of_prime_levelInj
    ((canonicalFieldModel K h).toModel ε π hπO hπ0) q hπ

end CanonicalLevelInj

/-! ## 4. Axiom audit -/

#print axioms CubicTwoStage.BerendAssembly.real_pow_sub_ne
#print axioms CubicTwoStage.BerendAssembly.complex_pow_sub_ne
#print axioms CubicTwoStage.BerendAssembly.powC_sub_normR_ne
#print axioms CubicTwoStage.BerendAssembly.iterate_torusAct_apply_mk'
#print axioms CubicTwoStage.BerendAssembly.lattice_preserves_diff
#print axioms CubicTwoStage.BerendAssembly.diff_ker_subset
#print axioms CubicTwoStage.BerendAssembly.diff_ker_finite
#print axioms CubicTwoStage.BerendAssembly.finite_fibre_of_finite_ker
#print axioms CubicTwoStage.BerendAssembly.zeroNonisolatedFull_of_interior_of_transitive
#print axioms CubicTwoStage.BerendAssembly.dichotomy_unitPrime
#print axioms CubicTwoStage.BerendAssembly.finite_of_closed_invariant_unitPrime
#print axioms CubicTwoStage.BerendAssembly.minimal_finite_unitPrime
#print axioms CubicTwoStage.BerendAssembly.minimal_torsion_unitPrime
#print axioms CubicTwoStage.BerendAssembly.dichotomy_unitPrime_of_levelInj
#print axioms CubicTwoStage.BerendAssembly.torusAct_eq_torusEndAct
#print axioms CubicTwoStage.BerendAssembly.berendMultiInvarianceCorrected_unitPrime
#print axioms CubicTwoStage.BerendAssembly.thm_uncovered_canonical_proved
#print axioms CubicTwoStage.BerendAssembly.torusAct_one_eq_iterate
#print axioms CubicTwoStage.BerendAssembly.injective_torusAct_unit
#print axioms CubicTwoStage.BerendAssembly.iterate_injOn_of_injOn
#print axioms CubicTwoStage.BerendAssembly.levelInj_of_prime_levelInj
#print axioms CubicTwoStage.BerendAssembly.dichotomy_unitPrime_of_primeLevelInj
#print axioms CubicTwoStage.BerendAssembly.hinj_canonical_of_primeLevelInj
