/-
# Change of coordinates in Stage I and in the dichotomy

`BEREND_PROOF_PLAN.md` §C.1 says the argument is to be carried out "in the common
eigenbasis supplied by A", while the project's statement
(`BerendDichotomy.ZeroNonisolatedFull`) lives on the torus `Pt ⧸ L` in the
standard basis of `Pt = Fin 3 → ℝ`, and `BerendMultiInvarianceCorrected` is
stated for an arbitrary family `f : κ → Pt ≃ₗ[ℝ] Pt`.  Something has to connect
the eigenbasis presentation with the standard one, and this module supplies it:

* `conjFamily F φ` — the family `F` carried across an additive equivalence
  `φ : A ≃+ B`, i.e. `i ↦ φ ∘ F i ∘ φ⁻¹`;
* `familyInvariant_conj` — invariance transports;
* `zeroNonisolatedFull_of_conj` / `zeroNonisolatedFull_iff_conj` — **Stage I is
  invariant under conjugation by an additive homeomorphism**;
* `dichotomy_iff_conj` — the same for the dichotomy;
* `zeroNonisolatedFull_words_iff` / `dichotomy_words_iff` — Stage I and the
  dichotomy depend only on the **semigroup generated** by the family, so the
  family may be replaced by any family generating the same semigroup (the
  freedom used in the plan for the paper's replacement `σ ↦ σ^m · r`).

Sections 3-5 are the parts that are actually needed for the Stage I assembly:

* `torusConj Φ M : Pt ⧸ M ≃+ Pt ⧸ Φ(M)` and `torusConj_torusEnd` — the toral
  endomorphism `torusEnd M f` is carried to `torusEnd Φ(M) (Φ f Φ⁻¹)`, and
  `zeroNonisolatedFull_torusEnd_iff` / `dichotomy_torusEnd_iff` say that Stage I
  and the dichotomy are the same statement in the two bases.  This makes
  plan §C.1 ("work in the common eigenbasis") a free move;
* `commute_conjFamily`, `rationallyIndependentPair_conj` — the algebraic
  hypotheses `hcomm` and the corrected (B3) survive that change of basis;
* `acc_restrict`, `invariant_restrict` — the minimal accumulating coordinate set
  produced by `BerendSec4.exists_minimal_acc` may be taken to be the whole index
  set: restricting a closed invariant set that accumulates at `0` inside
  `coord S` to `S` gives a closed set in the model `S → ℝ` that accumulates at
  `0` in the *full* space and is invariant under the restricted diagonal family.

Nothing here is a deep rigidity statement and none of it is claimed as one: this
is the transport/reduction layer between the diagonal (eigen-) model and the
torus.  The mathematical content of §4 and §5 — Lemma 4.3, Lemma 4.4 and
Proposition IV.1 — remains open, and in particular nothing here says anything
about `ZeroNonisolatedFull` for a concrete family.

No axiom, no `sorry`, no new assumption: every declaration below is proved from
the definitions of `CubicTwoStage.BerendDichotomy` and `CubicTwoStage.BerendSec4`,
and `#print axioms` at the end reports only `propext`, `Classical.choice` and
`Quot.sound` (the import of `BerendCorrected` puts the old axiom's *name* in
scope, as it already does for `BerendDichotomy`, but nothing here depends on it).
-/
import CubicTwoStage.BerendDichotomy
import CubicTwoStage.BerendCorrected
import CubicTwoStage.BerendSec4

open Set Filter
open scoped Pointwise Topology

set_option linter.unusedSectionVars false

namespace CubicTwoStage

namespace BerendTransport

open BerendDichotomy

/-! ## 1. Conjugation by an additive equivalence -/

/-- The family `F` transported across `φ : A ≃+ B`. -/
def conjFamily {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : Type*}
    (F : ι → A →+ A) (φ : A ≃+ B) : ι → B →+ B :=
  fun i => φ.toAddMonoidHom.comp ((F i).comp φ.symm.toAddMonoidHom)

@[simp] theorem conjFamily_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : Type*}
    (F : ι → A →+ A) (φ : A ≃+ B) (i : ι) (y : B) :
    conjFamily F φ i y = φ (F i (φ.symm y)) := rfl

/-- Conjugating by `φ` and then by `φ.symm` gives back `F`. -/
theorem conjFamily_symm {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : Type*}
    (F : ι → A →+ A) (φ : A ≃+ B) :
    conjFamily (conjFamily F φ) φ.symm = F := by
  funext i
  ext y
  simp [conjFamily]

/-- Forward invariance transports across an additive equivalence: the image of an
invariant set is invariant for the conjugate family. -/
theorem familyInvariant_conj {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B} {Y : Set A}
    (h : FamilyInvariant F Y) : FamilyInvariant (conjFamily F φ) (φ '' Y) := by
  intro i z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨F i x, h i ⟨x, hx, rfl⟩, by simp⟩

/-- **Stage I transports across a homeomorphic additive equivalence.**  The proof
is the identity `φ ∘ F i = conjFamily F φ i ∘ φ`: the preimage of an invariant
set is invariant for the conjugate family. -/
theorem zeroNonisolatedFull_of_conj {A B : Type*}
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B} (hφ : Continuous φ) (hφ' : Continuous φ.symm)
    (h : ZeroNonisolatedFull F) :
    ZeroNonisolatedFull (conjFamily F φ) := by
  intro E' hcl hne hacc hinv
  set E : Set A := φ ⁻¹' E' with hEdef
  have hEcl : IsClosed E := hEdef ▸ hcl.preimage hφ
  have hEne : E.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨φ.symm y, by simpa [hEdef] using hy⟩
  have hEacc : (0 : A) ∈ closure (E \ {0}) := by
    rw [mem_closure_iff] at hacc ⊢
    intro U hU hU0
    have hmem : U ∈ 𝓝 (φ.symm (0 : B)) := by simpa using hU.mem_nhds hU0
    obtain ⟨W, hWsub, hWopen, hW0⟩ := mem_nhds_iff.1 (hφ'.continuousAt hmem)
    obtain ⟨y, hyW, hyE, hy0⟩ := hacc W hWopen hW0
    refine ⟨φ.symm y, hWsub hyW, ?_, ?_⟩
    · show φ (φ.symm y) ∈ E'
      simpa using hyE
    · intro hz
      have hφz : φ (φ.symm y) = φ (0 : A) := by rw [hz]
      exact hy0 (by simpa using hφz)
  have hEinv : FamilyInvariant F E := by
    intro i
    rintro _ ⟨y, hy, rfl⟩
    have hy' : φ y ∈ E' := hy
    have h1 : conjFamily F φ i (φ y) ∈ E' := hinv i ⟨φ y, hy', rfl⟩
    have h2 : conjFamily F φ i (φ y) = φ (F i y) := by simp [conjFamily]
    show φ (F i y) ∈ E'
    rw [← h2]
    exact h1
  have hEuniv : E = univ := h E hEcl hEne hEacc hEinv
  refine eq_univ_of_forall fun y => ?_
  have hy : φ.symm y ∈ E := hEuniv ▸ mem_univ _
  simpa [hEdef] using hy

/-- **Stage I is invariant under conjugation by an additive homeomorphism.** -/
theorem zeroNonisolatedFull_iff_conj {A B : Type*}
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B} (hφ : Continuous φ) (hφ' : Continuous φ.symm) :
    ZeroNonisolatedFull (conjFamily F φ) ↔ ZeroNonisolatedFull F := by
  constructor
  · intro h
    have h' := zeroNonisolatedFull_of_conj (A := B) (B := A) (F := conjFamily F φ)
      (φ := φ.symm) hφ' hφ h
    have hF : conjFamily (conjFamily F φ) φ.symm = F := conjFamily_symm F φ
    rwa [hF] at h'
  · exact zeroNonisolatedFull_of_conj hφ hφ'

/-- **The dichotomy transports across a homeomorphic additive equivalence.** -/
theorem dichotomy_of_conj {A B : Type*}
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B} (hφ : Continuous φ) (h : Dichotomy F) :
    Dichotomy (conjFamily F φ) := by
  intro Y hY hne hinv hproper
  have himage : Y = φ '' (φ ⁻¹' Y) := by
    ext y
    constructor
    · intro hy
      exact ⟨φ.symm y, by simpa using hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hfin : (φ ⁻¹' Y).Finite := by
    refine h (φ ⁻¹' Y) (hY.preimage hφ) ?_ ?_ ?_
    · obtain ⟨y, hy⟩ := hne
      exact ⟨φ.symm y, by simpa using hy⟩
    · intro i
      rintro _ ⟨y, hy, rfl⟩
      have hy' : φ y ∈ Y := hy
      have h1 : conjFamily F φ i (φ y) ∈ Y := hinv i ⟨φ y, hy', rfl⟩
      have h2 : conjFamily F φ i (φ y) = φ (F i y) := by simp [conjFamily]
      show φ (F i y) ∈ Y
      rw [← h2]
      exact h1
    · intro huniv
      refine hproper ?_
      rw [himage, huniv]
      simp
  rw [himage]
  exact hfin.image φ

/-- **The dichotomy is invariant under conjugation by an additive
homeomorphism.** -/
theorem dichotomy_iff_conj {A B : Type*}
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B} (hφ : Continuous φ) (hφ' : Continuous φ.symm) :
    Dichotomy (conjFamily F φ) ↔ Dichotomy F := by
  constructor
  · intro h
    have h' := dichotomy_of_conj (A := B) (B := A) (F := conjFamily F φ) (φ := φ.symm) hφ' h
    have hF : conjFamily (conjFamily F φ) φ.symm = F := conjFamily_symm F φ
    rwa [hF] at h'
  · exact dichotomy_of_conj hφ

/-! ## 2. Only the generated semigroup matters -/

/-- The endomorphism of `G` defined by a word in the family `F` (the empty word
is the identity). -/
def wordApply {G : Type*} [AddCommGroup G] {ι : Type*} (F : ι → G →+ G) :
    List ι → (G →+ G)
  | [] => AddMonoidHom.id G
  | i :: l => (F i).comp (wordApply F l)

theorem wordApply_cons {G : Type*} [AddCommGroup G] {ι : Type*} (F : ι → G →+ G)
    (i : ι) (l : List ι) : wordApply F (i :: l) = (F i).comp (wordApply F l) := rfl

@[simp] theorem wordApply_singleton {G : Type*} [AddCommGroup G] {ι : Type*}
    (F : ι → G →+ G) (i : ι) : wordApply F [i] = F i := by
  simp [wordApply]

/-- A set invariant under the family is invariant under every word. -/
theorem familyInvariant_words {G : Type*} [AddCommGroup G] {ι : Type*}
    {F : ι → G →+ G} {Y : Set G} (h : FamilyInvariant F Y) :
    FamilyInvariant (fun l : List ι => wordApply F l) Y := by
  intro l
  induction l with
  | nil => intro z hz; simpa [wordApply] using hz
  | cons i l ih =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact h i ⟨wordApply F l y, ih ⟨y, hy, rfl⟩, rfl⟩

/-- Conversely, invariance under all words gives invariance under the family. -/
theorem familyInvariant_of_words {G : Type*} [AddCommGroup G] {ι : Type*}
    {F : ι → G →+ G} {Y : Set G}
    (h : FamilyInvariant (fun l : List ι => wordApply F l) Y) : FamilyInvariant F Y := by
  intro i
  simpa using h [i]

/-- **Stage I depends only on the generated semigroup.** -/
theorem zeroNonisolatedFull_words_iff {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {ι : Type*} {F : ι → G →+ G} :
    ZeroNonisolatedFull (fun l : List ι => wordApply F l) ↔ ZeroNonisolatedFull F := by
  constructor
  · intro h E hcl hne hacc hinv
    exact h E hcl hne hacc (familyInvariant_words hinv)
  · intro h E hcl hne hacc hinv
    exact h E hcl hne hacc (familyInvariant_of_words hinv)

/-- **The dichotomy depends only on the generated semigroup.** -/
theorem dichotomy_words_iff {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {ι : Type*} {F : ι → G →+ G} :
    Dichotomy (fun l : List ι => wordApply F l) ↔ Dichotomy F := by
  constructor
  · intro h Y hY hne hinv hproper
    exact h Y hY hne (familyInvariant_words hinv) hproper
  · intro h Y hY hne hinv hproper
    exact h Y hY hne (familyInvariant_of_words hinv) hproper

/-! ## 3. The project's torus: linear change of coordinates

The toral endomorphism `torusEnd M f` of `Pt ⧸ M` depends on the basis: after a
real-linear change of coordinates `Φ` of `Pt` it becomes `torusEnd Φ(M) (Φ f Φ⁻¹)`.
The two presentations are conjugate by an additive homeomorphism, so Stage I and
the dichotomy transfer.  This is what lets a §4 argument carried out in the
common eigenbasis (`BEREND_PROOF_PLAN.md` §C.1) be applied in the standard basis
of `Pt = Fin 3 → ℝ`, where `BerendMultiInvarianceCorrected` is stated. -/

section Torus

/-- The additive equivalence `Pt ⧸ M ≃+ Pt ⧸ Φ(M)` induced by `Φ : Pt ≃ₗ[ℝ] Pt`:
the coset of `x` modulo `M` goes to the coset of `Φ x` modulo `Φ(M)`. -/
noncomputable def torusConj (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) :
    Pt ⧸ M ≃+ Pt ⧸ M.map Φ.toAddMonoidHom :=
  QuotientAddGroup.congr M (M.map Φ.toAddMonoidHom) Φ.toAddEquiv rfl

@[simp] theorem torusConj_mk (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) (x : Pt) :
    torusConj Φ M (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ x) := rfl

/-- The symm of `torusConj` is the map induced by `Φ.symm`. -/
theorem torusConj_symm_apply (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) (x : Pt) :
    (torusConj Φ M).symm (QuotientAddGroup.mk x : Pt ⧸ M.map Φ.toAddMonoidHom) =
      (QuotientAddGroup.mk (Φ.symm x) : Pt ⧸ M) := by
  have h1 : torusConj Φ M (QuotientAddGroup.mk (Φ.symm x) : Pt ⧸ M) =
      (QuotientAddGroup.mk x : Pt ⧸ M.map Φ.toAddMonoidHom) := by simp
  rw [← h1, AddEquiv.symm_apply_apply]

theorem continuous_torusConj (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) :
    Continuous (torusConj Φ M) := by
  have hc : Continuous (fun x : Pt => torusConj Φ M (QuotientAddGroup.mk x)) := by
    have h : (fun x : Pt => torusConj Φ M (QuotientAddGroup.mk x)) =
        (QuotientAddGroup.mk : Pt → Pt ⧸ M.map Φ.toAddMonoidHom) ∘ (Φ : Pt → Pt) := by
      funext x
      exact torusConj_mk Φ M x
    rw [h]
    exact QuotientAddGroup.continuous_mk.comp
      (LinearMap.continuous_of_finiteDimensional (Φ : Pt →ₗ[ℝ] Pt))
  exact (QuotientAddGroup.isQuotientMap_mk M).continuous_iff.mpr hc

theorem continuous_torusConj_symm (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) :
    Continuous (torusConj Φ M).symm := by
  have hc : Continuous (fun x : Pt =>
      (torusConj Φ M).symm (QuotientAddGroup.mk x : Pt ⧸ M.map Φ.toAddMonoidHom)) := by
    have h : (fun x : Pt =>
          (torusConj Φ M).symm (QuotientAddGroup.mk x : Pt ⧸ M.map Φ.toAddMonoidHom)) =
        (QuotientAddGroup.mk : Pt → Pt ⧸ M) ∘ (Φ.symm : Pt → Pt) := by
      funext x
      exact torusConj_symm_apply Φ M x
    rw [h]
    exact QuotientAddGroup.continuous_mk.comp
      (LinearMap.continuous_of_finiteDimensional (Φ.symm : Pt →ₗ[ℝ] Pt))
  exact (QuotientAddGroup.isQuotientMap_mk (M.map Φ.toAddMonoidHom)).continuous_iff.mpr hc

/-- `Φ(M)` is again preserved by the conjugated map `Φ f Φ⁻¹`. -/
theorem map_preserves_conj (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) (f : Pt →+ Pt)
    (hf : ∀ g ∈ M, f g ∈ M) :
    ∀ g ∈ M.map Φ.toAddMonoidHom,
      (Φ.toAddMonoidHom.comp (f.comp Φ.symm.toAddMonoidHom)) g ∈ M.map Φ.toAddMonoidHom := by
  intro g hg
  rw [AddSubgroup.mem_map] at hg ⊢
  obtain ⟨m, hm, rfl⟩ := hg
  exact ⟨f m, hf m hm, by simp⟩

/-- **The conjugation identity at the project's torus**:
`torusConj Φ M ∘ torusEnd M f = torusEnd Φ(M) (Φ ∘ f ∘ Φ⁻¹) ∘ torusConj Φ M`. -/
theorem torusConj_torusEnd (Φ : Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt) (f : Pt →+ Pt)
    (hf : ∀ g ∈ M, f g ∈ M) (y : Pt ⧸ M) :
    torusConj Φ M (torusEnd M f hf y) =
      torusEnd (M.map Φ.toAddMonoidHom)
        (Φ.toAddMonoidHom.comp (f.comp Φ.symm.toAddMonoidHom))
        (map_preserves_conj Φ M f hf) (torusConj Φ M y) := by
  induction y using QuotientAddGroup.induction_on with
  | _ x =>
    rw [torusEnd_mk, torusConj_mk, torusConj_mk, torusEnd_mk]
    simp

/-- **The conjugate family of the induced maps is the family induced by the
conjugate linear maps.** -/
theorem conjFamily_torusEnd {ι : Type*} (f : ι → Pt ≃ₗ[ℝ] Pt) (M : AddSubgroup Pt)
    (hpres : ∀ (i : ι) (g : Pt), g ∈ M → ((f i).toAddMonoidHom) g ∈ M) (Φ : Pt ≃ₗ[ℝ] Pt) :
    conjFamily (fun i => torusEnd M ((f i).toAddMonoidHom) (hpres i))
        (torusConj Φ M) =
      fun i => torusEnd (M.map Φ.toAddMonoidHom)
        (Φ.toAddMonoidHom.comp (((f i).toAddMonoidHom).comp Φ.symm.toAddMonoidHom))
        (map_preserves_conj Φ M ((f i).toAddMonoidHom) (hpres i)) := by
  funext i
  refine AddMonoidHom.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | _ x =>
    have hsym : (torusConj Φ M).symm (QuotientAddGroup.mk x) =
        (QuotientAddGroup.mk (Φ.symm x) : Pt ⧸ M) := torusConj_symm_apply Φ M x
    rw [conjFamily_apply, hsym, torusConj_torusEnd, torusConj_mk]
    simp

/-- **Stage I at the project's torus is invariant under a real-linear change of
coordinates.**  `ZeroNonisolatedFull` for the family induced by `f` on `Pt ⧸ M`
is equivalent to `ZeroNonisolatedFull` for the family induced by
`Φ ∘ f i ∘ Φ⁻¹` on `Pt ⧸ Φ(M)`. -/
theorem zeroNonisolatedFull_torusEnd_iff {ι : Type*} (f : ι → Pt ≃ₗ[ℝ] Pt)
    (M : AddSubgroup Pt) (hpres : ∀ (i : ι) (g : Pt), g ∈ M → ((f i).toAddMonoidHom) g ∈ M)
    (Φ : Pt ≃ₗ[ℝ] Pt) :
    ZeroNonisolatedFull (fun i => torusEnd M ((f i).toAddMonoidHom) (hpres i)) ↔
      ZeroNonisolatedFull (fun i => torusEnd (M.map Φ.toAddMonoidHom)
        (Φ.toAddMonoidHom.comp (((f i).toAddMonoidHom).comp Φ.symm.toAddMonoidHom))
        (map_preserves_conj Φ M ((f i).toAddMonoidHom) (hpres i))) := by
  have h := zeroNonisolatedFull_iff_conj
    (F := fun i => torusEnd M ((f i).toAddMonoidHom) (hpres i))
    (φ := torusConj Φ M) (continuous_torusConj Φ M) (continuous_torusConj_symm Φ M)
  rw [conjFamily_torusEnd] at h
  exact h.symm

/-- **The dichotomy at the project's torus is invariant under a real-linear change
of coordinates.** -/
theorem dichotomy_torusEnd_iff {ι : Type*} (f : ι → Pt ≃ₗ[ℝ] Pt)
    (M : AddSubgroup Pt) (hpres : ∀ (i : ι) (g : Pt), g ∈ M → ((f i).toAddMonoidHom) g ∈ M)
    (Φ : Pt ≃ₗ[ℝ] Pt) :
    Dichotomy (fun i => torusEnd M ((f i).toAddMonoidHom) (hpres i)) ↔
      Dichotomy (fun i => torusEnd (M.map Φ.toAddMonoidHom)
        (Φ.toAddMonoidHom.comp (((f i).toAddMonoidHom).comp Φ.symm.toAddMonoidHom))
        (map_preserves_conj Φ M ((f i).toAddMonoidHom) (hpres i))) := by
  have h := dichotomy_iff_conj
    (F := fun i => torusEnd M ((f i).toAddMonoidHom) (hpres i))
    (φ := torusConj Φ M) (continuous_torusConj Φ M) (continuous_torusConj_symm Φ M)
  rw [conjFamily_torusEnd] at h
  exact h.symm

/-- **Density of `W + L` is basis independent.**  A real-linear change of
coordinates of `Pt` carries a dense set to a dense set (it is a homeomorphism of
the finite-dimensional space).  This is what lets the density hypothesis of the
§C.7 torus last mile (`CubicTwoStage/BerendTorusLastMile.lean`, direction d3) be
established in the eigenbasis and used in the standard basis. -/
theorem dense_image_linearEquiv (Φ : Pt ≃ₗ[ℝ] Pt) {S : Set Pt} (h : Dense S) :
    Dense (Φ '' S) := by
  have hcont : Continuous (Φ : Pt → Pt) :=
    LinearMap.continuous_of_finiteDimensional (Φ : Pt →ₗ[ℝ] Pt)
  rw [dense_iff_closure_eq] at h ⊢
  refine Set.Subset.antisymm (subset_univ _) ?_
  intro x _
  obtain ⟨y, rfl⟩ := Φ.surjective x
  exact mem_closure_image (f := (Φ : Pt → Pt)) hcont.continuousAt (by rw [h]; exact mem_univ y)

/-- The image of `W + L` under a linear equivalence is `Φ W + Φ L`. -/
theorem image_add_submodule_subgroup (Φ : Pt ≃ₗ[ℝ] Pt) (W : Submodule ℝ Pt)
    (L : AddSubgroup Pt) :
    (Φ : Pt → Pt) '' (((W : Set Pt) + (L : Set Pt))) =
      ((W.map (Φ : Pt →ₗ[ℝ] Pt) : Submodule ℝ Pt) : Set Pt) +
        ((L.map Φ.toAddMonoidHom : AddSubgroup Pt) : Set Pt) := by
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, l, hl, rfl⟩, rfl⟩
    exact ⟨Φ w, Submodule.mem_map_of_mem (f := (Φ : Pt →ₗ[ℝ] Pt)) hw,
      Φ l, AddSubgroup.mem_map_of_mem (f := Φ.toAddMonoidHom) hl, by simp⟩
  · rintro ⟨w', hw', l', hl', rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hl'
    exact ⟨w + l, ⟨w, hw, l, hl, rfl⟩, by simp⟩

end Torus

/-! ## 4. The algebraic hypotheses survive the change of coordinates

`BEREND_PROOF_PLAN.md` §C.1 asks for the argument "in the common eigenbasis".  A
change of basis replaces the family `f` by `Φ f i Φ⁻¹`; the hypotheses the deep
statements consume — commutativity `hcomm` and the corrected (B3)
(`RationallyIndependentPair`) — must be invariant under that replacement.  They
are: conjugation by a fixed group element is an automorphism. -/

section Hypotheses

/-- Conjugation of a commuting family is commuting. -/
theorem commute_conjFamily {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : Type*}
    {F : ι → A →+ A} {φ : A ≃+ B}
    (hcomm : ∀ i j x, F i (F j x) = F j (F i x)) :
    ∀ i j y, conjFamily F φ i (conjFamily F φ j y) = conjFamily F φ j (conjFamily F φ i y) := by
  intro i j y
  simp only [conjFamily_apply, AddEquiv.symm_apply_apply]
  exact congrArg φ (hcomm i j (φ.symm y))

/-- Powers of a conjugate are conjugates of powers. -/
theorem zpow_conj {G : Type*} [Group G] (φ a : G) (l : ℤ) :
    (φ * a * φ⁻¹) ^ l = φ * a ^ l * φ⁻¹ := by
  induction l using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, ih]
      group
  | pred n ih =>
      rw [zpow_sub_one, ih]
      group

/-- **The corrected (B3) is invariant under conjugation** by a fixed group
element: `RationallyIndependentPair` for `i ↦ φ f i φ⁻¹` is the same condition as
for `f`. -/
theorem rationallyIndependentPair_conj {G : Type*} [Group G] {ι : Type*}
    (f : ι → G) (φ : G) :
    RationallyIndependentPair (fun i => φ * f i * φ⁻¹) ↔ RationallyIndependentPair f := by
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, fun l k heq => ?_⟩
    apply hij l k
    rw [zpow_conj, zpow_conj, heq]
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, fun l k heq => ?_⟩
    apply hij l k
    have h := heq
    rw [zpow_conj, zpow_conj] at h
    exact mul_left_cancel (mul_right_cancel h)

end Hypotheses

/-! ## 5. Restriction to a coordinate subspace: "we may assume `S = univ`"

Berend's §4 first produces a *minimal* accumulating coordinate set `S`
(`BerendSec4.exists_minimal_acc`) and then argues inside `coord S` as if `S` were
the whole index set.  This section supplies that step: the restriction of the
configuration to `S` is again a configuration of the same kind — closed set,
`0` non-isolated, invariant under the restricted diagonal family, in the model
`S → ℝ`.  It is the "reduce the general hypothesis to the coordinate case" half
of the change-of-coordinates direction; the converse passage (from the
restricted model back to `ι → ℝ`) is plan §C.6 and is *not* done here. -/

section Restriction

open BerendSec4

/-- The inclusion of `S → ℝ` into `ι → ℝ` as the coordinate subspace of `S`. -/
def coordExtend {ι : Type*} [DecidableEq ι] (S : Finset ι) : (S → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun y i := if h : i ∈ S then y ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i ∈ S <;> simp [h]

/-- Restriction of a vector of `ι → ℝ` to the coordinates in `S`. -/
def coordRestrict {ι : Type*} (S : Finset ι) : (ι → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun x i := x i
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem coordExtend_apply {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (y : S → ℝ) (i : ι) : coordExtend S y i = if h : i ∈ S then y ⟨i, h⟩ else 0 := rfl

@[simp] theorem coordRestrict_apply {ι : Type*} (S : Finset ι) (x : ι → ℝ) (i : S) :
    coordRestrict S x i = x i := rfl

theorem coordExtend_mem {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : S → ℝ) :
    (coordExtend S y : ι → ℝ) ∈ BerendSec4.coord (S : Set ι) := by
  intro i hi
  rw [coordExtend_apply]
  exact dif_neg hi

theorem coordRestrict_coordExtend {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : S → ℝ) :
    coordRestrict S (coordExtend S y) = y := by
  funext i
  simp [coordExtend_apply]

theorem coordExtend_coordRestrict {ι : Type*} [DecidableEq ι] {S : Finset ι} {x : ι → ℝ}
    (hx : x ∈ BerendSec4.coord (S : Set ι)) :
    (coordExtend S (coordRestrict S x) : ι → ℝ) = x := by
  funext i
  by_cases h : i ∈ S
  · simp [coordExtend_apply, h]
  · have : x i = 0 := hx i h
    simp [coordExtend_apply, h, this]

theorem coordRestrict_injOn {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Set.InjOn (coordRestrict S) (BerendSec4.coord (S : Set ι) : Set (ι → ℝ)) := by
  intro x hx y hy hxy
  rw [← coordExtend_coordRestrict hx, ← coordExtend_coordRestrict hy, hxy]

theorem continuous_coordExtend {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    Continuous (coordExtend S) :=
  (coordExtend S).continuous_of_finiteDimensional

theorem continuous_coordRestrict {ι : Type*} [Fintype ι] (S : Finset ι) :
    Continuous (coordRestrict S) :=
  (coordRestrict S).continuous_of_finiteDimensional

/-- The diagonal map commutes with restriction to `S`. -/
theorem coordRestrict_diag {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ι → ℝ)
    (x : ι → ℝ) :
    coordRestrict S (BerendSec4.diag lam x) =
      BerendSec4.diag (fun i : S => lam i) (coordRestrict S x) := by
  funext i
  simp [BerendSec4.diag_apply]

/-- **The accumulating hypothesis restricts to the coordinate subspace.**  If `E`
accumulates at `0` inside `coord S`, then the restriction of `E ∩ coord S` to `S`
accumulates at `0` in the full model `S → ℝ`. -/
theorem acc_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Set (ι → ℝ)}
    {S : Finset ι} (hacc : BerendSec4.Acc E S) :
    BerendSec4.Acc (coordRestrict S '' (E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))))
      (Finset.univ : Finset S) := by
  have hcont := continuous_coordRestrict (S := S)
  have h0 : (0 : S → ℝ) ∈ closure (coordRestrict S '' (((E ∩ (BerendSec4.coord (S : Set ι) :
      Set (ι → ℝ))) \ {0}))) := by
    exact image_closure_subset_closure_image hcont
      (s := ((E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))) \ {0}))
      ⟨(0 : ι → ℝ), hacc, by simp⟩
  have hcoord : (BerendSec4.coord ((Finset.univ : Finset S) : Set S) : Set (S → ℝ)) = univ := by
    ext y
    simp [BerendSec4.mem_coord]
  have hset : (((coordRestrict S '' (E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ)))) ∩
      (BerendSec4.coord ((Finset.univ : Finset S) : Set S) : Set (S → ℝ))) \ {0}) =
      coordRestrict S '' (((E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))) \ {0})) := by
    rw [hcoord, Set.inter_univ]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy0⟩
      have hxS : x ∈ BerendSec4.coord (S : Set ι) := hx.2
      have hx0 : x ≠ 0 := by
        intro hx0'
        apply hy0
        rw [hx0']
        simp
      exact ⟨x, ⟨hx, hx0⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      have hxS : x ∈ BerendSec4.coord (S : Set ι) := hx.2
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      intro hy
      exact hx0 ((coordRestrict_injOn S) hxS (Submodule.zero_mem _) hy)
  rw [BerendSec4.Acc, hset]
  exact h0

/-- **The invariance restricts with the configuration.** -/
theorem invariant_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Set (ι → ℝ)} {S : Finset ι}
    {lam : ι → ℝ} (hinv : ∀ x ∈ E, BerendSec4.diag lam x ∈ E) :
    ∀ y ∈ coordRestrict S '' (E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))),
      BerendSec4.diag (fun i : S => lam i) y ∈
        coordRestrict S '' (E ∩ (BerendSec4.coord (S : Set ι) : Set (ι → ℝ))) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨BerendSec4.diag lam x, ⟨hinv x hx.1, BerendSec4.diag_mem_coord lam hx.2⟩, ?_⟩
  rw [coordRestrict_diag]

end Restriction

end BerendTransport

end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendTransport.zeroNonisolatedFull_iff_conj
#print axioms CubicTwoStage.BerendTransport.dichotomy_iff_conj
#print axioms CubicTwoStage.BerendTransport.zeroNonisolatedFull_words_iff
#print axioms CubicTwoStage.BerendTransport.dichotomy_words_iff
#print axioms CubicTwoStage.BerendTransport.zeroNonisolatedFull_torusEnd_iff
#print axioms CubicTwoStage.BerendTransport.dichotomy_torusEnd_iff
#print axioms CubicTwoStage.BerendTransport.rationallyIndependentPair_conj
#print axioms CubicTwoStage.BerendTransport.commute_conjFamily
#print axioms CubicTwoStage.BerendTransport.acc_restrict
#print axioms CubicTwoStage.BerendTransport.invariant_restrict
#print axioms CubicTwoStage.BerendTransport.dense_image_linearEquiv
#print axioms CubicTwoStage.BerendTransport.image_add_submodule_subgroup
