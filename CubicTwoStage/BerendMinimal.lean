/-
# Minimal closed forward-invariant sets (Berend §5 setup, work package B)

This file is the *topological half* of the plan `BEREND_PROOF_PLAN.md`, §B.  It
contains no analysis of the specific torus: everything is stated for an abstract
compact space (or compact abelian topological group) and an arbitrary family of
self-maps, which is exactly the situation of Berend's Theorem 2.1 (a commuting
semigroup `Σ` acting on a torus).

Main formal content (no `sorry`, no axioms, `import Mathlib` only):

* `IsInvariant`, `IsInvariantFamily`, `wordApply`, `semigroupOrbit`;
* the invariant-set calculus: monotonicity, unions, arbitrary intersections,
  closure under a continuous map, composition, iterates, list-folds;
* `exists_minimal_invariant`: **every nonempty closed forward-invariant subset
  of a compact space contains a minimal one** (Zorn's lemma plus the
  finite-intersection property for chains);
* `IsMinimalInvariant.closure_semigroupOrbit`: in a minimal set the semigroup
  orbit of every point is dense;
* `exists_accPt_of_infinite_isClosed`: an infinite closed subset of a compact
  space has an accumulation point in itself;
* `accPt_zero_sub` / `zero_mem_closure_sdiff`: for an infinite closed `M` in a
  compact abelian topological group acted on by continuous additive maps, `0` is
  an accumulation point of the difference set `M - M`.  This is precisely the
  hypothesis of stage C (`eq_univ_of_zero_nonisolated`);
* `IsMinimalInvariant.diff_data`: the same bundled with closedness and
  invariance of `M - M`;
* `IsMinimalInvariant.semigroupOrbit_eq_of_finite` and
  `IsMinimalInvariant.exists_word_fixed`: a finite minimal set is the semigroup
  orbit of each of its points, and every point of it is periodic under some
  nonempty word.  This is the input of stage D.4 (finite ⇒ torsion);
* `IsMinimalInvariant.image_eq`: with commuting continuous maps and Hausdorff
  `X`, every map of the family is onto a minimal set.

Note on hypotheses: `IsMinimalInvariant` is minimality *among closed nonempty
forward-invariant subsets of `M`* for the whole family at once; it is not
minimality for a single member of the family (which would be strictly weaker and
is false for the members of a rank-two semigroup, cf. the solenoid example).
-/
import Mathlib

open scoped Pointwise Topology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace BerendMinimal

open Set

universe u v

/-! ## 1. Forward invariance -/

section Invariant

variable {X : Type*} {ι κ : Type*}

/-- A set `Y` is forward invariant under `f` if `f` maps `Y` into `Y`.  Berend's
theorem uses forward invariance (`f '' Y ⊆ Y`), never equality. -/
def IsInvariant (f : X → X) (Y : Set X) : Prop := f '' Y ⊆ Y

/-- `Y` is forward invariant under the family `F`. -/
def IsInvariantFamily (F : ι → X → X) (Y : Set X) : Prop := ∀ i, IsInvariant (F i) Y

theorem isInvariant_iff {f : X → X} {Y : Set X} :
    IsInvariant f Y ↔ ∀ x ∈ Y, f x ∈ Y :=
  image_subset_iff

theorem isInvariantFamily_iff {F : ι → X → X} {Y : Set X} :
    IsInvariantFamily F Y ↔ ∀ i x, x ∈ Y → F i x ∈ Y :=
  forall_congr' fun _ => isInvariant_iff

/-- If `f` maps `Y` into a subset of `Y`, then `Y` is invariant. -/
theorem isInvariant_of_image_subset {f : X → X} {Y Z : Set X} (h : f '' Y ⊆ Z) (hZY : Z ⊆ Y) :
    IsInvariant f Y :=
  h.trans hZY

theorem isInvariant_empty (f : X → X) : IsInvariant f ∅ := by
  simp [IsInvariant]

theorem isInvariant_univ (f : X → X) : IsInvariant f univ := by
  simp [IsInvariant]

theorem IsInvariant.union {f : X → X} {Y Z : Set X} (hY : IsInvariant f Y)
    (hZ : IsInvariant f Z) : IsInvariant f (Y ∪ Z) := by
  rw [isInvariant_iff] at *
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (hY x hx)
  · exact Or.inr (hZ x hx)

theorem IsInvariantFamily.union {F : ι → X → X} {Y Z : Set X} (hY : IsInvariantFamily F Y)
    (hZ : IsInvariantFamily F Z) : IsInvariantFamily F (Y ∪ Z) :=
  fun i => (hY i).union (hZ i)

/-- An arbitrary intersection of invariant sets is invariant. -/
theorem IsInvariant.iInter {f : X → X} {κ : Type*} {Y : κ → Set X}
    (h : ∀ i, IsInvariant f (Y i)) : IsInvariant f (⋂ i, Y i) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact mem_iInter.mpr fun i => h i ⟨y, mem_iInter.mp hy i, rfl⟩

/-- An arbitrary intersection of invariant sets is invariant (indexed by a set
of sets). -/
theorem IsInvariant.sInter {f : X → X} {S : Set (Set X)} (h : ∀ s ∈ S, IsInvariant f s) :
    IsInvariant f (⋂₀ S) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact mem_sInter.mpr fun s hs => h s hs ⟨y, mem_sInter.mp hy s hs, rfl⟩

theorem IsInvariantFamily.iInter {F : ι → X → X} {κ : Type*} {M : κ → Set X}
    (h : ∀ j i, IsInvariant (F i) (M j)) : IsInvariantFamily F (⋂ j, M j) :=
  fun i => IsInvariant.iInter fun j => h j i

theorem IsInvariantFamily.sInter {F : ι → X → X} {S : Set (Set X)}
    (h : ∀ s ∈ S, IsInvariantFamily F s) : IsInvariantFamily F (⋂₀ S) :=
  fun i => IsInvariant.sInter fun s hs => h s hs i

section Top

variable [TopologicalSpace X]

/-- A continuous map keeps the closure of an invariant set invariant. -/
theorem IsInvariant.closure {f : X → X} (hf : Continuous f) {Y : Set X}
    (h : IsInvariant f Y) : IsInvariant f (closure Y) :=
  (image_closure_subset_closure_image hf).trans (closure_mono h)

theorem IsInvariantFamily.closure {F : ι → X → X} (hcont : ∀ i, Continuous (F i)) {Y : Set X}
    (h : IsInvariantFamily F Y) : IsInvariantFamily F (closure Y) :=
  fun i => (h i).closure (hcont i)

end Top

/-- Composition of two invariant maps stays invariant. -/
theorem IsInvariant.comp {f g : X → X} {Y : Set X} (hf : IsInvariant f Y)
    (hg : IsInvariant g Y) : IsInvariant (f ∘ g) Y := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hf ⟨g y, hg ⟨y, hy, rfl⟩, rfl⟩

/-- Iterates of an invariant map are invariant. -/
theorem IsInvariant.iterate {f : X → X} {Y : Set X} (h : IsInvariant f Y) (n : ℕ) :
    IsInvariant (f^[n]) Y := by
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih => rw [Function.iterate_succ]; exact ih.comp h

theorem IsInvariant.mem_iterate {f : X → X} {Y : Set X} (h : IsInvariant f Y) {x : X}
    (hx : x ∈ Y) (n : ℕ) : (f^[n]) x ∈ Y :=
  h.iterate n ⟨x, hx, rfl⟩

end Invariant

/-! ## 2. Semigroup orbits (finite words in the family) -/

section Words

variable {X : Type*} {ι : Type*}

/-- Apply a finite word of maps to a point, left to right: `[i, j]` acts as
`F j (F i x)`.  This is the fold used by `UnitPrimeModel.applyList` in the
project, so the two compose in the same order. -/
def wordApply (F : ι → X → X) (l : List ι) (x : X) : X :=
  l.foldl (fun z i => F i z) x

@[simp]
theorem wordApply_nil (F : ι → X → X) (x : X) : wordApply F [] x = x := rfl

@[simp]
theorem wordApply_cons (F : ι → X → X) (i : ι) (l : List ι) (x : X) :
    wordApply F (i :: l) x = wordApply F l (F i x) := rfl

theorem wordApply_append_singleton (F : ι → X → X) (l : List ι) (i : ι) (x : X) :
    wordApply F (l ++ [i]) x = F i (wordApply F l x) := by
  simp [wordApply, List.foldl_append]

theorem wordApply_append (F : ι → X → X) (l l' : List ι) (x : X) :
    wordApply F (l ++ l') x = wordApply F l' (wordApply F l x) := by
  simp [wordApply, List.foldl_append]

/-- The semigroup orbit of `x`: every point reachable from `x` by a finite word
of members of the family. -/
def semigroupOrbit (F : ι → X → X) (x : X) : Set X :=
  {y | ∃ l : List ι, wordApply F l x = y}

theorem mem_semigroupOrbit_self (F : ι → X → X) (x : X) : x ∈ semigroupOrbit F x :=
  ⟨[], rfl⟩

theorem wordApply_mem_semigroupOrbit (F : ι → X → X) (l : List ι) (x : X) :
    wordApply F l x ∈ semigroupOrbit F x :=
  ⟨l, rfl⟩

/-- A forward invariant set containing `x` contains the whole semigroup orbit
of `x`. -/
theorem semigroupOrbit_subset {F : ι → X → X} {M : Set X} (hM : IsInvariantFamily F M)
    {x : X} (hx : x ∈ M) : semigroupOrbit F x ⊆ M := by
  rintro _ ⟨l, rfl⟩
  have key : ∀ (a : X), a ∈ M → ∀ l : List ι, wordApply F l a ∈ M := by
    intro a ha l
    induction l generalizing a with
    | nil => simpa using ha
    | cons i l ih =>
        rw [wordApply_cons]
        exact ih (F i a) (hM i ⟨a, ha, rfl⟩)
  exact key x hx l

/-- The semigroup orbit is forward invariant. -/
theorem isInvariantFamily_semigroupOrbit (F : ι → X → X) (x : X) :
    IsInvariantFamily F (semigroupOrbit F x) := by
  intro i z hz
  obtain ⟨y, ⟨l, rfl⟩, rfl⟩ := hz
  exact ⟨l ++ [i], wordApply_append_singleton F l i x⟩

end Words

/-! ## 3. Minimal closed invariant sets and their existence -/

section Minimal

variable {X : Type*} {ι : Type*}

/-- `M` is a **minimal closed nonempty forward-invariant set** for the family
`F`: it has the property itself, and no proper closed nonempty forward-invariant
subset does. -/
structure IsMinimalInvariant [TopologicalSpace X] (F : ι → X → X) (M : Set X) : Prop where
  /-- `M` is nonempty. -/
  ne : M.Nonempty
  /-- `M` is closed. -/
  closed : IsClosed M
  /-- `M` is forward invariant under every member of the family. -/
  inv : IsInvariantFamily F M
  /-- Minimality: no proper closed nonempty forward-invariant subset. -/
  minimal : ∀ M' : Set X, M' ⊆ M → M'.Nonempty → IsClosed M' → IsInvariantFamily F M' →
    M' = M

/-- **Existence of minimal closed invariant sets.**  In a compact space, every
nonempty closed forward-invariant set contains a minimal one.  The family of
closed nonempty forward-invariant subsets of `S` is stable under intersections
of chains (finite-intersection property), so Zorn's lemma applies.

(Continuity of the maps is *not* needed here; it is needed to know that the
closure of an invariant set is invariant, e.g. in
`IsMinimalInvariant.closure_semigroupOrbit`.) -/
theorem exists_minimal_invariant [TopologicalSpace X] [CompactSpace X] {F : ι → X → X}
    {S : Set X} (hS : IsClosed S) (hne : S.Nonempty) (hinv : IsInvariantFamily F S) :
    ∃ M : Set X, M ⊆ S ∧ IsMinimalInvariant F M := by
  classical
  set A : Set (Set X) := {M | M ⊆ S ∧ M.Nonempty ∧ IsClosed M ∧ IsInvariantFamily F M} with hA
  have hbound : ∀ c ⊆ A, IsChain (· ⊆ ·) c → ∃ lb ∈ A, ∀ s ∈ c, lb ⊆ s := by
    intro c hcA hchain
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨S, ⟨subset_rfl, hne, hS, hinv⟩, by simp⟩
    · haveI : Nonempty c := ⟨hcne.some, hcne.some_mem⟩
      have hdir : DirectedOn (· ⊇ ·) c := by
        intro a ha b hb
        rcases eq_or_ne a b with rfl | hne
        · exact ⟨a, ha, subset_rfl, subset_rfl⟩
        · rcases hchain ha hb hne with h | h
          · exact ⟨a, ha, subset_rfl, h⟩
          · exact ⟨b, hb, h, subset_rfl⟩
      refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · exact (sInter_subset_of_mem hcne.some_mem).trans (hcA hcne.some_mem).1
      · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
          (fun U hU => (hcA hU).2.1)
          (fun U hU => (hcA hU).2.2.1.isCompact)
          (fun U hU => (hcA hU).2.2.1)
      · exact isClosed_sInter fun s hs => (hcA hs).2.2.1
      · exact IsInvariantFamily.sInter fun s hs => (hcA hs).2.2.2
  obtain ⟨m, hm⟩ := zorn_superset A hbound
  refine ⟨m, hm.1.1, ⟨hm.1.2.1, hm.1.2.2.1, hm.1.2.2.2, ?_⟩⟩
  intro M' hsub hne' hcl' hinv'
  have hM'A : M' ∈ A := ⟨hsub.trans hm.1.1, hne', hcl', hinv'⟩
  exact subset_antisymm hsub (hm.2 hM'A hsub)

/-- **A minimal set for a family contains a minimal set for any subfamily.**  The
subfamily is typically the finitely generated subsemigroup generated by the B1
map, the finitely many B2 expansion witnesses and the corrected B3 pair: a set
minimal for the full semigroup need not be minimal for a subfamily, but it
always contains a subfamily-minimal closed nonempty invariant subset. -/
theorem exists_minimal_invariant_subfamily [TopologicalSpace X] [CompactSpace X]
    {F : ι → X → X} {κ : Type*} {G : κ → X → X}
    (hsub : ∀ j, ∃ i, ∀ x, G j x = F i x) {M : Set X} (hM : IsMinimalInvariant F M) :
    ∃ N : Set X, N ⊆ M ∧ IsMinimalInvariant G N := by
  have hinv : IsInvariantFamily G M := by
    intro j
    obtain ⟨i, hi⟩ := hsub j
    have hji : G j = F i := funext hi
    rw [hji]
    exact hM.inv i
  exact exists_minimal_invariant hM.closed hM.ne hinv

/-- A minimal set has no proper closed nonempty invariant subset. -/
theorem IsMinimalInvariant.eq_of_subset {F : ι → X → X} [TopologicalSpace X] {M M' : Set X}
    (hM : IsMinimalInvariant F M) (hsub : M' ⊆ M) (hne : M'.Nonempty) (hcl : IsClosed M')
    (hinv : IsInvariantFamily F M') : M' = M :=
  hM.minimal M' hsub hne hcl hinv

end Minimal

/-! ## 4. Density of semigroup orbits in a minimal set -/

section Density

variable {X : Type*} {ι : Type*} [TopologicalSpace X] {F : ι → X → X}

/-- **In a minimal closed invariant set, every semigroup orbit is dense.** -/
theorem IsMinimalInvariant.closure_semigroupOrbit (hcont : ∀ i, Continuous (F i)) {M : Set X}
    (hM : IsMinimalInvariant F M) {x : X} (hx : x ∈ M) :
    closure (semigroupOrbit F x) = M :=
  hM.minimal _
    (hM.closed.closure_subset_iff.mpr (semigroupOrbit_subset hM.inv hx))
    ⟨x, subset_closure (mem_semigroupOrbit_self F x)⟩
    isClosed_closure
    ((isInvariantFamily_semigroupOrbit F x).closure hcont)

/-- Every point of `M` lies in the closure of the semigroup orbit of every other
point of `M`. -/
theorem IsMinimalInvariant.mem_closure_semigroupOrbit (hcont : ∀ i, Continuous (F i))
    {M : Set X} (hM : IsMinimalInvariant F M) {x y : X} (hx : x ∈ M) (hy : y ∈ M) :
    y ∈ closure (semigroupOrbit F x) :=
  hM.closure_semigroupOrbit hcont hx ▸ hy

end Density

/-! ## 5. Accumulation points and difference sets -/

section AccPt

variable {A : Type*} [TopologicalSpace A]

/-- **Bolzano–Weierstrass for closed subsets of a compact space**: an infinite
closed set has an accumulation point in itself. -/
theorem exists_accPt_of_infinite_isClosed [CompactSpace A] {S : Set A} (hS : IsClosed S)
    (hinf : S.Infinite) : ∃ a ∈ S, AccPt a (Filter.principal S) :=
  hinf.exists_accPt_of_subset_isCompact hS.isCompact Subset.rfl

variable [AddCommGroup A] [IsTopologicalAddGroup A] {ι : Type*}

/-- `0` belongs to the difference set of a nonempty set. -/
theorem zero_mem_sub {M : Set A} (hne : M.Nonempty) : (0 : A) ∈ M - M := by
  obtain ⟨x, hx⟩ := hne
  simpa using sub_mem_sub hx hx

/-- The difference set `M - M` is invariant under every additive self-map that
leaves `M` invariant. -/
theorem isInvariantFamily_sub {G : ι → A →+ A} {M : Set A}
    (hM : IsInvariantFamily (fun i => (G i : A → A)) M) :
    IsInvariantFamily (fun i => (G i : A → A)) (M - M) := by
  rintro i z ⟨y, hy, rfl⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := hy
  simp only [map_sub]
  exact sub_mem_sub (hM i ⟨u, hu, rfl⟩) (hM i ⟨v, hv, rfl⟩)

/-- The difference set of a closed set is closed, in a compact Hausdorff group. -/
theorem isClosed_sub [CompactSpace A] [T2Space A] {M : Set A} (hM : IsClosed M) :
    IsClosed (M - M) := by
  have himg : (fun p : A × A => p.1 - p.2) '' (M ×ˢ M) = M - M := by
    rw [sub_image_prod]
  rw [← himg]
  exact ((hM.isCompact.prod hM.isCompact).image continuous_sub).isClosed

/-- **`0` is an accumulation point of `M - M`** for an infinite closed `M` in a
compact abelian topological group: shift a limit point of `M` to `0`. -/
theorem accPt_zero_sub [CompactSpace A] {M : Set A} (hM : IsClosed M) (hinf : M.Infinite) :
    AccPt (0 : A) (Filter.principal (M - M)) := by
  obtain ⟨a, ha, hacc⟩ := exists_accPt_of_infinite_isClosed hM hinf
  rw [accPt_iff_nhds] at hacc ⊢
  intro U hU
  have hW : {y : A | y - a ∈ U} ∈ 𝓝 a := by
    have hcont : ContinuousAt (fun y : A => y - a) a := by fun_prop
    exact hcont.preimage_mem_nhds (by simpa using hU)
  obtain ⟨y, hy, hya⟩ := hacc _ hW
  exact ⟨y - a, ⟨hy.1, sub_mem_sub hy.2 ha⟩, sub_ne_zero.mpr hya⟩

/-- Punctured-closure form: `0` is a non-isolated point of `M - M`. -/
theorem zero_mem_closure_sdiff [CompactSpace A] {M : Set A} (hM : IsClosed M)
    (hinf : M.Infinite) : (0 : A) ∈ closure ((M - M) \ {0}) := by
  rw [mem_closure_iff]
  intro U hU h0
  have hacc := accPt_zero_sub hM hinf
  rw [accPt_iff_nhds] at hacc
  obtain ⟨y, hy, hy0⟩ := hacc U (hU.mem_nhds h0)
  exact ⟨y, hy.1, hy.2, hy0⟩

end AccPt

/-! ## 6. Finite minimal sets are periodic -/

section Finite

variable {X : Type*} {ι : Type*} [TopologicalSpace X] {F : ι → X → X}

/-- In a finite minimal set, the semigroup orbit of every point is the whole
set. -/
theorem IsMinimalInvariant.semigroupOrbit_eq_of_finite [T1Space X] {M : Set X}
    (hM : IsMinimalInvariant F M) (hfin : M.Finite) {x : X} (hx : x ∈ M) :
    semigroupOrbit F x = M :=
  hM.minimal _
    (semigroupOrbit_subset hM.inv hx)
    ⟨x, mem_semigroupOrbit_self F x⟩
    ((hfin.subset (semigroupOrbit_subset hM.inv hx))).isClosed
    (isInvariantFamily_semigroupOrbit F x)

/-- **Every point of a finite minimal set is periodic** under some nonempty word
of the family.  On a torus this is the step "finite minimal ⇒ torsion point". -/
theorem IsMinimalInvariant.exists_word_fixed [T1Space X] [Nonempty ι] {M : Set X}
    (hM : IsMinimalInvariant F M) (hfin : M.Finite) {x : X} (hx : x ∈ M) :
    ∃ l : List ι, l ≠ [] ∧ wordApply F l x = x := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hy : F i x ∈ M := hM.inv i ⟨x, hx, rfl⟩
  have hEq : semigroupOrbit F (F i x) = M := hM.semigroupOrbit_eq_of_finite hfin hy
  rw [← hEq] at hx
  obtain ⟨l, hl⟩ := hx
  exact ⟨i :: l, List.cons_ne_nil i l, by rw [wordApply_cons]; exact hl⟩

end Finite

/-! ## 7. Commuting families: minimal sets are mapped onto themselves -/

section Commuting

variable {X : Type*} {ι : Type*} [TopologicalSpace X] {F : ι → X → X}

/-- With commuting continuous maps, the image of a minimal set under any member
of the family is dense in it. -/
theorem IsMinimalInvariant.closure_image (hcont : ∀ i, Continuous (F i))
    (hcomm : ∀ i j x, F i (F j x) = F j (F i x)) {M : Set X} (hM : IsMinimalInvariant F M)
    (i : ι) : closure (F i '' M) = M := by
  have hsub : F i '' M ⊆ M := hM.inv i
  have himg : ∀ j, F j '' (F i '' M) ⊆ F i '' M := by
    rintro j z ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨F j w, hM.inv j ⟨w, hw, rfl⟩, hcomm i j w⟩
  exact hM.minimal _
    (hM.closed.closure_subset_iff.mpr hsub)
    ((hM.ne.image (F i)).mono subset_closure)
    isClosed_closure
    (fun j => IsInvariant.closure (hcont j) (himg j))

/-- In a compact Hausdorff space with commuting continuous maps, every member of
the family maps a minimal set *onto* it. -/
theorem IsMinimalInvariant.image_eq [CompactSpace X] [T2Space X] (hcont : ∀ i, Continuous (F i))
    (hcomm : ∀ i j x, F i (F j x) = F j (F i x)) {M : Set X} (hM : IsMinimalInvariant F M)
    (i : ι) : F i '' M = M := by
  have hcl : IsClosed (F i '' M) :=
    ((hM.closed.isCompact).image (hcont i)).isClosed
  calc F i '' M = closure (F i '' M) := hcl.closure_eq.symm
    _ = M := hM.closure_image hcont hcomm i

end Commuting

end BerendMinimal
