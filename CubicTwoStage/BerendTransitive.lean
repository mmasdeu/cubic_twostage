/-
# A topologically transitive member of the unit–prime family, from expansion

Swarm `smw952unn`, member m8, direction d10.

`BEREND_SEC5_NOTES.md` §3.3 lists the last unowned input of Berend's §5
assembly: `BerendSec5.dichotomy_of_stageI_of_minimal_torsion` needs

  `htrans : ∃ i, TopologicallyTransitive (F i)`,

and Berend obtains it from (B1)+(B2)+(B3) by Proposition 3.2 (ergodicity w.r.t.
Haar measure).  For the unit–prime family of this project that route is not
needed: the family contains an element that expands the whole torus
(`BerendExpandingMember.exists_mult_margin`, `eq_univ_of_torusAct_of_margin`),
and expansion *alone* gives topological transitivity.

The reason is one line.  For a continuous self-map `f` of a compact space, if
every closed `f`-invariant set with non-empty interior is everything, then

  `K = closure (⋃ n, f^[n] '' U)`

for a non-empty open `U` is closed, `f`-invariant (by continuity), and has
non-empty interior (`U ⊆ K`), hence `K = univ`: the forward images of `U` are
dense, so they meet every non-empty open `V`.  That is exactly
`TopologicallyTransitive f`.

## Main results

* `topologicallyTransitive_of_interior_full` — the reduction above, for a
  self-map of a compact abelian topological group;
* `topologicallyTransitive_iff_interior_full` — for a continuous endomorphism of
  `Pt ⧸ L` the two properties are equivalent, so Berend's ergodic-member
  hypothesis loses nothing when replaced by the expansion estimate;
* `topologicallyTransitive_of_expanding` — an expanding toral endomorphism (`A`
  with a right inverse contracting by `λ⁻¹ < 1`) is topologically transitive;
* `exists_ball_subset_of_interior_nonempty` — a non-empty interior contains the
  image of a ball of the ambient space;
* `topologicallyTransitive_torusAct_of_pow_margin` — the same for a positive
  power `(u^m, j*m)` of the margin member, the form used inside the congruence
  subsemigroup `Σ^(n)`;
* `dichotomy_of_stageI_of_minimal_torsion_of_margin` — Berend's §5 assembly
  with its `htrans` hypothesis discharged;
* `eq_univ_of_isClosed_of_interior_of_margin` — `eq_univ_of_torusAct_of_margin`
  with its ball hypothesis replaced by "non-empty interior", using that the
  quotient map does not increase distances;
* `topologicallyTransitive_torusAct_of_margin` — the margin member
  (`4 ≤ |a 0|`, `16 ≤ normC a`) is topologically transitive on `Pt ⧸ L`;
* `exists_topologicallyTransitive_fieldModel` — for a `FieldModel` and a unit
  which is not critical at the real place, some family member `(u, j)`,
  `j > 0`, is topologically transitive.  This is the `htrans` input of
  `BerendSec5.dichotomy_of_stageI_of_minimal_torsion`, produced with no
  ergodicity, no Haar measure and no (B1) spectral argument.

No `sorry`, no axiom, no assumed `Prop`; the audit at the end prints the
axioms of every declaration.
-/
import CubicTwoStage.BerendExpandingMember
import CubicTwoStage.BerendSec5
import CubicTwoStage.ComplexCubic

open Set

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CubicTwoStage
namespace BerendTransitive

/-! ## 1. Interior-full implies topological transitivity -/

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]

/-- **Interior-full implies topological transitivity.**

If every closed set `E` with `f x ∈ E` for all `x ∈ E` and non-empty interior is
everything, then `f` is topologically transitive: the closure of the forward
images of a non-empty open set is closed, invariant and has interior. -/
theorem topologicallyTransitive_of_interior_full {f : G → G} (hf : Continuous f)
    (hfull : ∀ E : Set G, IsClosed E → (∀ x ∈ E, f x ∈ E) → (interior E).Nonempty →
      E = univ) :
    BerendSec5.TopologicallyTransitive f := by
  intro U hUo hUne V hVo hVne
  set K : Set G := closure (⋃ n : ℕ, (f^[n]) '' U) with hK
  have hUsub : U ⊆ ⋃ n : ℕ, (f^[n]) '' U :=
    fun u hu => mem_iUnion.mpr ⟨0, by simpa using hu⟩
  have hUK : U ⊆ K := fun u hu => subset_closure (hUsub hu)
  have hKclosed : IsClosed K := isClosed_closure
  have hKinv : ∀ x ∈ K, f x ∈ K := by
    intro x hx
    have hsub : f '' (⋃ n : ℕ, (f^[n]) '' U) ⊆ ⋃ n : ℕ, (f^[n]) '' U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨n, u, hu, rfl⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨n + 1, ⟨u, hu, by rw [Function.iterate_succ_apply']⟩⟩
    have h1 : f '' K ⊆ closure (f '' (⋃ n : ℕ, (f^[n]) '' U)) :=
      image_closure_subset_closure_image hf
    have h2 : closure (f '' (⋃ n : ℕ, (f^[n]) '' U)) ⊆ K := closure_mono hsub
    exact h2 (h1 ⟨x, hx, rfl⟩)
  have hKint : (interior K).Nonempty :=
    hUne.mono (interior_maximal hUK hUo)
  have hKuniv : K = univ := hfull K hKclosed hKinv hKint
  obtain ⟨v, hv⟩ := hVne
  have hvcl : v ∈ K := by rw [hKuniv]; exact mem_univ v
  rw [hK, mem_closure_iff] at hvcl
  obtain ⟨y, hyV, hyU⟩ := hvcl V hVo hv
  obtain ⟨n, hn⟩ := mem_iUnion.mp hyU
  rw [Set.mem_image] at hn
  obtain ⟨u, hu, hfu⟩ := hn
  refine ⟨n, ?_⟩
  exact ⟨(f^[n]) u, ⟨u, hu, rfl⟩, hfu ▸ hyV⟩

/-- **Equivalence, for a continuous self-map of the torus.**  `htrans` and
interior-full are the same property: this is
`BerendSec5.eq_univ_of_isClosed_of_interior_of_transitive` in one direction and
`topologicallyTransitive_of_interior_full` in the other.  So passing from
Berend's ergodic member to the expansion estimate loses nothing. -/
theorem topologicallyTransitive_iff_interior_full [CompactSpace (Torus L)] [T2Space (Torus L)]
    (f : Torus L →+ Torus L) (hf : Continuous (⇑f)) :
    BerendSec5.TopologicallyTransitive (⇑f) ↔
      ∀ E : Set (Torus L), IsClosed E → f '' E ⊆ E → (interior E).Nonempty → E = univ := by
  constructor
  · intro htr E hE hinv hint
    exact BerendSec5.eq_univ_of_isClosed_of_interior_of_transitive hE hinv hint htr
  · intro hfull
    exact topologicallyTransitive_of_interior_full hf
      (fun E hE hinv hint => hfull E hE (Set.image_subset_iff.mpr hinv) hint)

/-! ## 2. The ball form of the expansion step, in terms of the interior -/

section Model

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}

/-- The quotient map does not increase distances. -/
theorem dist_mk_le {V : Type*} [NormedAddCommGroup V] (L : AddSubgroup V) (x y : V) :
    dist ((QuotientAddGroup.mk' L) x) ((QuotientAddGroup.mk' L) y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- **A non-empty interior contains the image of a ball of the ambient space.**
This is the form in which the expansion estimate consumes "non-empty interior". -/
theorem exists_ball_subset_of_interior_nonempty {V : Type*} [NormedAddCommGroup V]
    {L : AddSubgroup V} {E : Set (V ⧸ L)} (hint : (interior E).Nonempty) :
    ∃ x₀ : V, ∃ r : ℝ, 0 < r ∧ (QuotientAddGroup.mk' L) '' Metric.ball x₀ r ⊆ E := by
  obtain ⟨y, hy⟩ := hint
  have hopen : IsOpen (interior E) := isOpen_interior
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨r, hr, hball⟩ := hopen y hy
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  refine ⟨x₀, r, hr, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  refine interior_subset (hball ?_)
  rw [Metric.mem_ball] at hw ⊢
  exact lt_of_le_of_lt (dist_mk_le L w x₀) hw

/-- **An expanding toral endomorphism is topologically transitive.**

`A : Pt → Pt` is real-linear, preserves `L`, and has a right inverse `A'` which
contracts by `λ⁻¹ < 1`.  Then the induced endomorphism of `Pt ⧸ L` is
topologically transitive — with no ergodicity, no Haar measure and no spectral
argument, only `BerendInteriorFull.eq_univ_of_expanding_of_interior`. -/
theorem topologicallyTransitive_of_expanding {L : AddSubgroup Pt}
    (A A' : Pt →L[ℝ] Pt) (hAA' : ∀ x, A (A' x) = x)
    {lam : ℝ} (hlam : 1 < lam) (hexp : ∀ x : Pt, ‖A' x‖ ≤ lam⁻¹ * ‖x‖)
    (hL : ∀ g ∈ L, A g ∈ L) [CompactSpace (Pt ⧸ L)] [T2Space (Torus L)] :
    BerendSec5.TopologicallyTransitive
      (⇑(QuotientAddGroup.map L L A.toAddMonoidHom hL)) := by
  refine topologicallyTransitive_of_interior_full
    (continuous_torusMap L A.toAddMonoidHom hL A.continuous) ?_
  intro E hE hinv hint
  obtain ⟨x₀, r, hr, hsub⟩ := exists_ball_subset_of_interior_nonempty (L := L) hint
  exact BerendInteriorFull.eq_univ_of_expanding_of_interior A A' hAA' hlam hexp hL hE
    (Set.image_subset_iff.mpr hinv) ⟨x₀, r, hr, hsub⟩

/-- **`eq_univ_of_torusAct_of_margin` with non-empty interior as the hypothesis.**
A closed set invariant under the expanding margin member and with non-empty
interior is the whole torus.  The only point is that the interior of `E`
contains the image of a ball of `Pt`, which is the form the expansion estimate
consumes. -/
theorem eq_univ_of_isClosed_of_interior_of_margin (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j))
    [CompactSpace (Pt ⧸ L)] {E : Set (Torus L)} (hE : IsClosed E)
    (hinv : D.torusAct (u, j) '' E ⊆ E) (hint : (interior E).Nonempty) :
    E = univ := by
  obtain ⟨x₀, r, hr, hsub⟩ := exists_ball_subset_of_interior_nonempty (L := L) hint
  exact eq_univ_of_torusAct_of_margin D u j ha0 hC hE hinv ⟨x₀, r, hr, hsub⟩

/-- **A margin member of the unit–prime family is topologically transitive on
the torus.** -/
theorem topologicallyTransitive_torusAct_of_margin (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j))
    [CompactSpace (Pt ⧸ L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    BerendSec5.TopologicallyTransitive (⇑(D.torusAct (u, j))) := by
  haveI : DiscreteTopology L := ‹DiscreteTopology (AddSubgroup.toIntSubmodule L)›
  have hLclosed : IsClosed (L : Set Pt) := AddSubgroup.isClosed_of_discrete
  haveI : IsClosed (L : Set Pt) := hLclosed
  haveI : T2Space (Torus L) := inferInstance
  refine topologicallyTransitive_of_interior_full (D.continuous_torusAct (u, j)) ?_
  intro E hE hinv hint
  exact eq_univ_of_isClosed_of_interior_of_margin D u j ha0 hC hE
    (fun z hz => by obtain ⟨x, hx, rfl⟩ := hz; exact hinv x hx) hint

/-- **Powers of the margin member are transitive too.**  Step (c) of Proposition
IV.1 works inside the congruence subsemigroup `Σ^(n)`, where the expanding
element has to be a positive power `(u ^ m, j * m)`; `powC_mult` and
`powC_margin` say that this is again a family multiplier with the same margin. -/
theorem topologicallyTransitive_torusAct_of_pow_margin (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j)) {m : ℕ} (hm : 0 < m)
    [CompactSpace (Pt ⧸ L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)] :
    BerendSec5.TopologicallyTransitive (⇑(D.torusAct (u ^ m, j * m))) := by
  obtain ⟨h1, h2⟩ := powC_margin (D.mult u j) ha0 hC hm
  rw [powC_mult] at h1 h2
  exact topologicallyTransitive_torusAct_of_margin D (u ^ m) (j * m) h1 h2

/-! ## 3. From the model data to a transitive member -/

variable {Nm : AbsNorm K}

/-- **A transitive member of the unit–prime family, from the model arithmetic.**
Given a `FieldModel`, a unit `ε` which is not critical at the real place, and a
prime `π` with `Nm π = p > 1`, some family member `(u, j)` with `j > 0` is
topologically transitive on `Pt ⧸ FM.lattice`.

This discharges `htrans` of `BerendSec5.dichotomy_of_stageI_of_minimal_torsion`
without ergodicity, without Haar measure and without the spectral part (B1). -/
theorem exists_topologicallyTransitive_fieldModel (FM : FieldModel K 𝒪 Nm) (ε : 𝒪ˣ) (π : K)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (p : ℕ) (hp : 1 < (p : ℝ))
    (hπN : Nm π = (p : ℚ≥0)) (hε : lamAbs (FM.σ (((ε : 𝒪) : K))) 0 ≠ 1)
    [CompactSpace (Pt ⧸ FM.lattice)]
    [DiscreteTopology (AddSubgroup.toIntSubmodule FM.lattice)] :
    ∃ i : 𝒪ˣ × ℕ,
      BerendSec5.TopologicallyTransitive (⇑((FM.toModel ε π hπO hπ0).torusAct i)) := by
  obtain ⟨u, j, hj, h1, h2⟩ :=
    exists_mult_margin_fieldModel_of_ne_one FM ε π hπO hπ0 p hp hπN hε
  exact ⟨(u, j), topologicallyTransitive_torusAct_of_margin _ u j h1 h2⟩

/-- **The `htrans` slot of Berend's §5 assembly, discharged by expansion.**

This is `BerendSec5.dichotomy_of_stageI_of_minimal_torsion` with its last
hypothesis — the existence of a topologically transitive member — supplied by
`topologicallyTransitive_torusAct_of_margin`.  Every other hypothesis is left
visible, so the statement can be consumed directly by the axiom replacement. -/
theorem dichotomy_of_stageI_of_minimal_torsion_of_margin
    (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ)
    (ha0 : 4 ≤ |D.mult u j 0|) (hC : 16 ≤ normC (D.mult u j))
    [CompactSpace (Pt ⧸ L)] [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
    (hStage : BerendDichotomy.ZeroNonisolatedFull D.torusAct)
    (hcont : ∀ i, Continuous (D.torusAct i))
    (hker : ∀ i, ((D.torusAct i) ⁻¹' {(0 : Torus L)}).Finite)
    (htors : ∀ n : ℕ, 0 < n → ({z : Torus L | n • z = 0} : Set (Torus L)).Finite)
    (hmin : ∀ M : Set (Torus L), IsClosed M → M.Nonempty →
      BerendMinimal.IsInvariantFamily (fun i => (D.torusAct i : Torus L → Torus L)) M →
      BerendMinimal.IsMinimalInvariant (fun i => (D.torusAct i : Torus L → Torus L)) M →
      ∃ x ∈ M, ∃ n : ℕ, 0 < n ∧ n • x = 0) :
    BerendDichotomy.Dichotomy D.torusAct :=
  BerendSec5.dichotomy_of_stageI_of_minimal_torsion hStage hcont hker htors hmin
    ⟨(u, j), topologicallyTransitive_torusAct_of_margin D u j ha0 hC⟩

/-! ## 4. The canonical model of a complex cubic field -/

section Canonical

variable {K : Type*} [Field K] [NumberField K]

/-- **For the canonical model of a complex cubic field, the transitive member
exists with no hypothesis beyond the model's own data.**  The lattice instances
(`DiscreteTopology` and compactness of the quotient) come from
`ComplexCubic.discreteTopology_canonicalFieldModel_lattice` and
`ComplexCubic.compactSpace_canonicalFieldModel_torus`. -/
theorem exists_topologicallyTransitive_canonical (h : IsComplexCubic K)
    (ε : (numberFieldO K)ˣ) (π : K) (hπO : π ∈ numberFieldO K) (hπ0 : π ≠ 0)
    (p : ℕ) (hp : 1 < (p : ℝ)) (hπN : numberFieldAbsNorm K π = (p : ℚ≥0))
    (hε : lamAbs ((NumberFieldCubic.canonicalFieldModel K h).σ
      (((ε : numberFieldO K) : K))) 0 ≠ 1) :
    ∃ i : (numberFieldO K)ˣ × ℕ,
      BerendSec5.TopologicallyTransitive
        (⇑(((NumberFieldCubic.canonicalFieldModel K h).toModel ε π hπO hπ0).torusAct i)) :=
  exists_topologicallyTransitive_fieldModel (NumberFieldCubic.canonicalFieldModel K h)
    ε π hπO hπ0 p hp hπN hε

end Canonical

end Model

end BerendTransitive
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendTransitive.topologicallyTransitive_of_interior_full
#print axioms CubicTwoStage.BerendTransitive.topologicallyTransitive_iff_interior_full
#print axioms CubicTwoStage.BerendTransitive.topologicallyTransitive_of_expanding
#print axioms CubicTwoStage.BerendTransitive.dist_mk_le
#print axioms CubicTwoStage.BerendTransitive.exists_ball_subset_of_interior_nonempty
#print axioms CubicTwoStage.BerendTransitive.eq_univ_of_isClosed_of_interior_of_margin
#print axioms CubicTwoStage.BerendTransitive.topologicallyTransitive_torusAct_of_margin
#print axioms CubicTwoStage.BerendTransitive.exists_topologicallyTransitive_fieldModel
#print axioms CubicTwoStage.BerendTransitive.topologicallyTransitive_torusAct_of_pow_margin
#print axioms CubicTwoStage.BerendTransitive.dichotomy_of_stageI_of_minimal_torsion_of_margin
#print axioms CubicTwoStage.BerendTransitive.exists_topologicallyTransitive_canonical
