/-
Work package A3 of `BEREND_PROOF_PLAN.md` (§A.3 "common eigenbasis" and §A.4
"power-difference invertibility"), swarm `smw6j8dl8`, member m4.

This module is project-owned, contains no `sorry` and no new axiom, and does not
import or mention `CubicTwoStage.berend_multi_invariance`; `#print axioms` on
every declaration below reports only `propext`, `Classical.choice` and
`Quot.sound`.

## What is proved

* `mapsTo_eigenspace_of_commute`, `map_eigenspace_le_of_commute` — an
  endomorphism commuting with `s` carries every eigenspace of `s` into itself.
* `exists_smul_of_finrank_eigenspace_eq_one` — on a one-dimensional eigenspace a
  commuting endomorphism is a scalar.
* `exists_common_eigenbasis` — **the common eigenbasis of §A.3.**  Over an
  algebraically closed field, if the characteristic polynomial of `s` is a
  product of three linear factors with distinct roots, then there is a basis
  `b : Basis (Fin 3) K V` of eigenvectors of `s`, the three eigenspaces are
  one-dimensional (`finrank = 1`, proved, not assumed), and every endomorphism
  commuting with `s` acts on each `b i` by a scalar.  This is the precise form of
  "invariant subspaces are spans of coordinate subsets" used by stage C.
* `exists_common_eigenbasis_family` — consequently a whole commuting family
  containing `s` is simultaneously diagonal in that basis.
* `eigenspace_eq_span_basis` — each eigenspace is the line spanned by the
  corresponding basis vector.
* `hasEigenvalue_of_charpoly_eq_prod`, `finrank_eq_three_of_charpoly_eq_prod` —
  roots of a completely split characteristic polynomial are eigenvalues, and
  `finrank K V = 3`.
* `not_hasEigenvalue_of_irreducible_charpoly`,
  `not_isOfFinOrder_of_hasEigenvalue` — (B1) forbids eigenvalues outright
  (adapted from the reviewed `m2/BerendAlgebra.lean` of the previous swarm) and
  in particular forbids root-of-unity eigenvalues.
* `exists_roots_of_irreducible_cubic` — a monic irreducible cubic `p` over `ℚ`
  maps over `ℂ` to a product of three linear factors with pairwise distinct
  roots (splitting from `IsAlgClosed.splits`, distinctness from separability in
  characteristic zero), enumerated as a map `Fin 3 → ℂ`.
* `exists_common_eigenbasis_of_irreducible_cubic` — **A3 end to end**: if
  `charpoly s` for `s : End ℂ V` is the image of a monic irreducible cubic over
  `ℚ`, one gets the eigenvalue family, the common eigenbasis, the
  one-dimensionality of the eigenspaces, and the diagonalisation of the whole
  centraliser, in a single application.
* `exists_eq_of_hasEigenvalue_of_charpoly_eq_prod` — every eigenvalue of a map
  with completely split characteristic polynomial is one of the `μ i`.
* `eq_span_basis_of_minimal_invariant` — **an invariant subspace minimal among
  the non-zero `s`-invariant ones is one of the eigenlines** `span {b i}`.  This
  is the "invariant subspaces are spanned by coordinate subsets" input of
  Berend §4 (plan §C.1) in the minimal form in which §4 uses it.
* `pow_apply_eq_smul_pow`, `eq_zero_of_pow_apply_eq_pow_apply`,
  `ker_pow_sub_pow_eq_bot`, `injective_pow_sub_pow`, `pow_ne_pow` — **the
  power-difference lemma of §A.4**: if `0` is not an eigenvalue of `s` and no
  eigenvalue is a root of unity, then for `n ≠ m` the map `s ^ n - s ^ m` is
  injective (hence invertible in finite dimension) and `s ^ n ≠ s ^ m`.

## Deficit (what is *not* proved here, and exactly what is missing)

1. **Base change (owned by A1/A2).**  (B1) in `CubicTwoStage/Berend.lean` is
   stated for the integral endomorphism `lact i` of the ℤ-module
   `AddSubgroup.toIntSubmodule L`.  The lemmas here are stated over a field, so
   the transfer `charpoly (baseChange ℂ f) = (charpoly f).map (algebraMap ℤ ℂ)`
   (with irreducibility preserved by Gauss) is needed to instantiate them; it is
   *not* proved here.
2. **Full coordinate-subset form.**  Only the *minimal* case is proved
   (`eq_span_basis_of_minimal_invariant`); the general statement "an arbitrary
   `s`-invariant `W` is the span of the `b i` it contains" is not formalised.
   Its proof needs the Lagrange projectors
   `π i = c i⁻¹ • ∏ j ≠ i (s - μ j • 1)`, `c i = ∏ j ≠ i (μ i - μ j)`, the
   identity `∑ i π i = 1` (check it on the basis `b`: `π i (b j) = δ i j • b j`),
   `π i (W) ⊆ W`, and `eigenspace (μ i) = span {b i}`.
3. Only nonnegative powers `s ^ n` are treated; the `ℤ`-indexed form
   `(f i) ^ l` used by (B3) needs the linear-equivalence (invertible) version,
   which follows from `s ^ n - s ^ m` being invertible but is not spelled out.
-/
import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace CubicTwoStage

namespace BerendA3



section Basic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **A commuting map preserves every eigenspace.** -/
theorem mapsTo_eigenspace_of_commute {s g : Module.End K V} (h : Commute s g) (μ : K) :
    ∀ x ∈ s.eigenspace μ, g x ∈ s.eigenspace μ := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  calc s (g x) = g (s x) := by
        have h' := h.eq
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h'
        exact congrArg (fun e => e x) h'
    _ = g (μ • x) := by rw [hx]
    _ = μ • g x := map_smul g μ x

/-- **A commuting map preserves every eigenspace** (submodule form). -/
theorem map_eigenspace_le_of_commute {s g : Module.End K V} (h : Commute s g) (μ : K) :
    Submodule.map g (s.eigenspace μ) ≤ s.eigenspace μ :=
  Submodule.map_le_iff_le_comap.mpr fun _ hx => mapsTo_eigenspace_of_commute h μ _ hx

/-- **On a one-dimensional eigenspace every commuting map is a scalar.** -/
theorem exists_smul_of_finrank_eigenspace_eq_one [FiniteDimensional K V]
    {s g : Module.End K V} (h : Commute s g)
    {μ : K} (hμ : finrank K (s.eigenspace μ) = 1) {x : V} (hx : x ∈ s.eigenspace μ) :
    ∃ c : K, g x = c • x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  · have hmem : g x ∈ s.eigenspace μ := mapsTo_eigenspace_of_commute h μ x hx
    have hle : Submodule.span K {x} ≤ s.eigenspace μ :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have heq : Submodule.span K {x} = s.eigenspace μ :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hμ, finrank_span_singleton hx0])
    rw [← heq] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩

end Basic




/-! ## (B1) forbids eigenvalues, roots of unity in particular -/

section NoEigenvalue

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- **An irreducible characteristic polynomial of degree different from one has no
eigenvalue.**  (Adapted from the checked fragment `m2/BerendAlgebra.lean` of the
previous swarm, `not_hasEigenvalue_of_irreducible_charpoly`.) -/
theorem not_hasEigenvalue_of_irreducible_charpoly (f : Module.End K V)
    (hirr : Irreducible (LinearMap.charpoly f)) (hdeg : f.charpoly.natDegree ≠ 1)
    (μ : K) : ¬ f.HasEigenvalue μ := by
  intro hμ
  have hroot : f.charpoly.IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mp hμ
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hchar : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hchar hq
  have hnd : f.charpoly.natDegree = 1 + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C μ).ne_zero hqne,
      Polynomial.natDegree_X_sub_C]
  rcases hirr.isUnit_or_isUnit hq with hunit | hunit
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; norm_num) hunit
  · rw [Polynomial.natDegree_eq_zero_of_isUnit hunit, add_zero] at hnd
    exact hdeg hnd

/-- **A power of an endomorphism has no eigenvalue one**, given that its
characteristic polynomial is irreducible and the dimension is not one. -/
theorem not_hasEigenvalue_one_of_charpoly_pow_irreducible (s : Module.End K V)
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (s ^ n)))
    (hfr : Module.finrank K V ≠ 1) (n : ℕ) (hn : 0 < n) :
    ¬ (s ^ n).HasEigenvalue 1 := by
  refine not_hasEigenvalue_of_irreducible_charpoly (s ^ n) (hB1 n hn) ?_ 1
  rw [LinearMap.charpoly_natDegree]
  exact hfr

end NoEigenvalue



/-! ## The power-difference lemma (plan §A.4) -/

section PowDiff

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Iterating an eigenvector relation: `s ^ k y = μ ^ k • y`. -/
theorem pow_apply_eq_smul_pow {s : Module.End K V} {μ : K} {y : V} (hy : s y = μ • y)
    (k : ℕ) : (s ^ k) y = (μ ^ k) • y := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hy, smul_smul, ← pow_succ]

variable [IsAlgClosed K]

/-- **(B1) forbids root-of-unity eigenvalues** (plan §A.4).  If every power of `s`
has an irreducible characteristic polynomial and `finrank ≠ 1`, then no eigenvalue
of `s` is a root of unity. -/
theorem not_isOfFinOrder_of_hasEigenvalue {s : Module.End K V}
    (hB1 : ∀ n : ℕ, 0 < n → Irreducible (LinearMap.charpoly (s ^ n)))
    (hfr : Module.finrank K V ≠ 1) {μ : K} (hμ : s.HasEigenvalue μ) :
    ¬ IsOfFinOrder μ := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hn1⟩
  have hpow : (s ^ n).HasEigenvalue (μ ^ n) := hμ.pow n
  rw [hn1] at hpow
  exact not_hasEigenvalue_one_of_charpoly_pow_irreducible s hB1 hfr n hn hpow

end PowDiff



section PowDiffMain

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **The power-difference lemma (plan §A.4).**  If no eigenvalue of `s` is zero or
a root of unity, then `s ^ n` and `s ^ m` have no common nonzero fixed point for
`n ≠ m`: equivalently `s ^ n - s ^ m` is injective, hence invertible.

This is the step that makes `s ^ n - s ^ m` invertible on the lattice tensored with
`ℚ` in §3 of the paper. -/
theorem eq_zero_of_pow_apply_eq_pow_apply {s : Module.End K V}
    (h0 : ¬ s.HasEigenvalue 0)
    (hru : ∀ μ : K, s.HasEigenvalue μ → ¬ IsOfFinOrder μ)
    {n m : ℕ} (hnm : n ≠ m) {x : V} (hx : (s ^ n) x = (s ^ m) x) : x = 0 := by
  by_contra hx0
  -- the kernel of `s ^ n - s ^ m` is `s`-invariant
  set W : Submodule K V := LinearMap.ker (s ^ n - s ^ m) with hWdef
  have hxW : x ∈ W := by
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hx
  have hinv : ∀ y ∈ W, s y ∈ W := by
    intro y hy
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy ⊢
    have hcomm : ∀ k : ℕ, (s ^ k) (s y) = s ((s ^ k) y) := by
      intro k
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
    rw [hcomm n, hcomm m, hy]
  -- the restriction has an eigenvalue
  haveI : Nontrivial W :=
    ⟨⟨⟨x, hxW⟩, 0, fun h => hx0 (by simpa using congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, hμeig⟩ := Module.End.exists_eigenvalue (LinearMap.restrict s hinv)
  obtain ⟨y, hyeig⟩ := hμeig.exists_hasEigenvector
  set yv : V := (y : V) with hyv
  have hys : s yv = μ • yv := by
    have h := hyeig.apply_eq_smul
    have h' := congrArg Subtype.val h
    simpa [LinearMap.restrict_apply, hyv] using h'
  have hyne : yv ≠ 0 := by
    intro h
    exact hyeig.2 (Subtype.ext (by simpa [hyv] using h))
  have hyker : (s ^ n) yv = (s ^ m) yv := by
    have h : (s ^ n - s ^ m) yv = 0 := LinearMap.mem_ker.mp y.2
    rwa [LinearMap.sub_apply, sub_eq_zero] at h
  have hpow : μ ^ n = μ ^ m := by
    rw [pow_apply_eq_smul_pow hys n, pow_apply_eq_smul_pow hys m] at hyker
    have hsub : (μ ^ n - μ ^ m) • yv = 0 := by rw [sub_smul, hyker, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hyne
  have hμ : s.HasEigenvalue μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (show s.HasEigenvector μ yv from ⟨Module.End.mem_eigenspace_iff.mpr hys, hyne⟩)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact h0 hμ
  have hfin : IsOfFinOrder μ := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · refine ⟨m - n, Nat.sub_pos_of_lt hlt, ?_⟩
      have h : μ ^ n * μ ^ (m - n) = μ ^ n * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le, ← hpow]
      exact mul_left_cancel₀ (pow_ne_zero n hμ0) h
    · refine ⟨n - m, Nat.sub_pos_of_lt hgt, ?_⟩
      have h : μ ^ m * μ ^ (n - m) = μ ^ m * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hgt.le, hpow]
      exact mul_left_cancel₀ (pow_ne_zero m hμ0) h
  exact hru μ hμ hfin

/-- **`s ^ n - s ^ m` has trivial kernel** for `n ≠ m`. -/
theorem ker_pow_sub_pow_eq_bot {s : Module.End K V}
    (h0 : ¬ s.HasEigenvalue 0)
    (hru : ∀ μ : K, s.HasEigenvalue μ → ¬ IsOfFinOrder μ)
    {n m : ℕ} (hnm : n ≠ m) : LinearMap.ker (s ^ n - s ^ m) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_pow_apply_eq_pow_apply h0 hru hnm ?_
  have h : (s ^ n - s ^ m) x = 0 := hx
  rw [LinearMap.sub_apply, sub_eq_zero] at h
  exact h

/-- **`s ^ n - s ^ m` is injective** for `n ≠ m`. -/
theorem injective_pow_sub_pow {s : Module.End K V}
    (h0 : ¬ s.HasEigenvalue 0)
    (hru : ∀ μ : K, s.HasEigenvalue μ → ¬ IsOfFinOrder μ)
    {n m : ℕ} (hnm : n ≠ m) : Function.Injective (s ^ n - s ^ m) :=
  LinearMap.ker_eq_bot.mp (ker_pow_sub_pow_eq_bot h0 hru hnm)

/-- **`s ^ n ≠ s ^ m`** for `n ≠ m` whenever the space is nontrivial. -/
theorem pow_ne_pow [Nontrivial V] {s : Module.End K V}
    (h0 : ¬ s.HasEigenvalue 0)
    (hru : ∀ μ : K, s.HasEigenvalue μ → ¬ IsOfFinOrder μ)
    {n m : ℕ} (hnm : n ≠ m) : s ^ n ≠ s ^ m := by
  intro h
  have hk := ker_pow_sub_pow_eq_bot h0 hru hnm
  rw [h, sub_self, LinearMap.ker_zero] at hk
  have hzero : ∀ y : V, y = 0 := by
    intro y
    have hy : y ∈ (⊤ : Submodule K V) := Submodule.mem_top
    rw [hk] at hy
    simpa using hy
  obtain ⟨z, hz⟩ := exists_ne (0 : V)
  exact hz (hzero z)

end PowDiffMain



/-! ## The common eigenbasis (plan §A.3) -/

section CommonEigenbasis

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Each root of a completely split characteristic polynomial is an eigenvalue. -/
theorem hasEigenvalue_of_charpoly_eq_prod {s : Module.End K V} {μ : Fin 3 → K}
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) (i : Fin 3) :
    s.HasEigenvalue (μ i) := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly s (μ i)).mpr ?_
  show Polynomial.eval (μ i) (LinearMap.charpoly s) = 0
  rw [hchar, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- A characteristic polynomial which is a product of three linear factors forces
dimension three. -/
theorem finrank_eq_three_of_charpoly_eq_prod {s : Module.End K V} {μ : Fin 3 → K}
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) : Module.finrank K V = 3 := by
  have h : (LinearMap.charpoly s).natDegree = 3 := by
    rw [hchar, Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := fun i => (X - C (μ i))) (fun i _ => Polynomial.monic_X_sub_C (μ i))]
    simp
  rwa [LinearMap.charpoly_natDegree] at h

/-- **The common eigenbasis.**  If the characteristic polynomial of `s` is a product
of three distinct linear factors, then `V` has a basis of eigenvectors of `s`, and
every endomorphism commuting with `s` acts on each of these basis vectors by a
scalar.  This is the "common eigenbasis" of Berend §3: the eigenspaces of `s` are
one-dimensional, so any commuting family is simultaneously diagonal in this basis. -/
theorem exists_common_eigenbasis [Nontrivial V] (s : Module.End K V) (μ : Fin 3 → K)
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) (hμ : Function.Injective μ) :
    ∃ b : Basis (Fin 3) K V,
      (∀ i, s (b i) = μ i • b i) ∧
      (∀ i, Module.finrank K (s.eigenspace (μ i)) = 1) ∧
      ∀ (g : Module.End K V), Commute s g → ∀ i, ∃ c : K, g (b i) = c • b i := by
  classical
  have hfr : Module.finrank K V = 3 := finrank_eq_three_of_charpoly_eq_prod hchar
  have heig : ∀ i, s.HasEigenvalue (μ i) := fun i => hasEigenvalue_of_charpoly_eq_prod hchar i
  choose v hv using fun i => (heig i).exists_hasEigenvector
  have hli : LinearIndependent K v := Module.End.eigenvectors_linearIndependent' s μ hμ v hv
  have hcard : Fintype.card (Fin 3) = Module.finrank K V := by simp [hfr]
  let b : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  have hb : ∀ i, b i = v i := fun i => by
    simp [b]
  -- the eigenspaces of `s` are pairwise disjoint
  have hpair : ∀ i j : Fin 3, i ≠ j → Disjoint (s.eigenspace (μ i)) (s.eigenspace (μ j)) := by
    intro i j hij
    rw [Submodule.disjoint_def]
    intro x hxi hxj
    rw [Module.End.mem_eigenspace_iff] at hxi hxj
    have h : (μ i - μ j) • x = 0 := by rw [sub_smul, ← hxi, ← hxj, sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') (hμ.ne hij)
    · exact h'
  -- they span, because the eigenbasis does
  have hmem : ∀ i, b i ∈ s.eigenspace (μ i) := fun i =>
    Module.End.mem_eigenspace_iff.mpr (by rw [hb i]; exact (hv i).apply_eq_smul)
  have htop : s.eigenspace (μ 0) ⊔ s.eigenspace (μ 1) ⊔ s.eigenspace (μ 2) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← b.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨j, rfl⟩
    fin_cases j
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hmem 0))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (hmem 1))
    · exact Submodule.mem_sup_right (hmem 2)
  -- the second eigenspace meets the sum of the first two trivially
  have hsplit : (s.eigenspace (μ 0) ⊔ s.eigenspace (μ 1)) ⊓ s.eigenspace (μ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, Submodule.mem_sup] at hx
    obtain ⟨⟨a, ha, b', hb', rfl⟩, hx2⟩ := hx
    have ha' : s a = μ 0 • a := Module.End.mem_eigenspace_iff.mp ha
    have hb'' : s b' = μ 1 • b' := Module.End.mem_eigenspace_iff.mp hb'
    have hx2' : s (a + b') = μ 2 • (a + b') := Module.End.mem_eigenspace_iff.mp hx2
    have hlin : (μ 0 - μ 2) • a + (μ 1 - μ 2) • b' = 0 := by
      have hEq : (μ 0) • a + (μ 1) • b' = (μ 2) • a + (μ 2) • b' := by
        calc (μ 0) • a + (μ 1) • b' = s (a + b') := by rw [map_add, ha', hb'']
          _ = (μ 2) • a + (μ 2) • b' := by rw [hx2', smul_add]
      calc (μ 0 - μ 2) • a + (μ 1 - μ 2) • b'
          = ((μ 0) • a + (μ 1) • b') - ((μ 2) • a + (μ 2) • b') := by
            rw [sub_smul, sub_smul]; abel
        _ = 0 := by rw [hEq, sub_self]
    have hne02 : μ 0 - μ 2 ≠ 0 := sub_ne_zero.mpr (hμ.ne (by decide))
    have hne12 : μ 1 - μ 2 ≠ 0 := sub_ne_zero.mpr (hμ.ne (by decide))
    have haP1 : a ∈ s.eigenspace (μ 1) := by
      have hmem : (μ 0 - μ 2) • a ∈ s.eigenspace (μ 1) := by
        have hEq2 : (μ 0 - μ 2) • a = -((μ 1 - μ 2) • b') := by
          rw [eq_neg_iff_add_eq_zero]
          exact hlin
        rw [hEq2]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hb')
      have hone : a = (μ 0 - μ 2)⁻¹ • ((μ 0 - μ 2) • a) := by
        rw [smul_smul, inv_mul_cancel₀ hne02, one_smul]
      rw [hone]
      exact Submodule.smul_mem _ _ hmem
    have ha0 : a = 0 := by
      have hmem : a ∈ s.eigenspace (μ 0) ⊓ s.eigenspace (μ 1) := ⟨ha, haP1⟩
      have hle := disjoint_iff_inf_le.mp (hpair 0 1 (by decide))
      simpa using hle hmem
    have hb0 : b' = 0 := by
      rw [ha0, smul_zero, zero_add] at hlin
      exact (smul_eq_zero.mp hlin).resolve_left hne12
    rw [ha0, hb0, add_zero]
    exact Submodule.zero_mem _
  -- hence the finrank is the sum of the three eigen-dimensions
  have hsum : Module.finrank K V =
      Module.finrank K (s.eigenspace (μ 0)) + Module.finrank K (s.eigenspace (μ 1)) +
        Module.finrank K (s.eigenspace (μ 2)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K := K)
      (s.eigenspace (μ 0)) (s.eigenspace (μ 1))
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (K := K)
      (s.eigenspace (μ 0) ⊔ s.eigenspace (μ 1)) (s.eigenspace (μ 2))
    rw [le_bot_iff.mp (disjoint_iff_inf_le.mp (hpair 0 1 (by decide))), finrank_bot,
      add_zero] at h1
    rw [htop, finrank_top K V, hsplit, finrank_bot, add_zero] at h2
    rw [h2, h1]
  -- each eigen-dimension is positive
  have hpos : ∀ i, 1 ≤ Module.finrank K (s.eigenspace (μ i)) := by
    intro i
    have hne : s.eigenspace (μ i) ≠ ⊥ := by
      intro hbot
      have hzero : v i ∈ (⊥ : Submodule K V) := hbot ▸ Module.End.mem_eigenspace_iff.mpr
        (hv i).apply_eq_smul
      exact (hv i).2 (by simpa using hzero)
    haveI : Nontrivial ↥(s.eigenspace (μ i)) := Submodule.nontrivial_iff_ne_bot.mpr hne
    have hpos' : 0 < Module.finrank K ↥(s.eigenspace (μ i)) :=
      Module.finrank_pos (R := K) (M := ↥(s.eigenspace (μ i)))
    omega
  have hdim : ∀ i, Module.finrank K (s.eigenspace (μ i)) = 1 := by
    set A := Module.finrank K (s.eigenspace (μ 0)) with hA
    set B := Module.finrank K (s.eigenspace (μ 1)) with hB
    set C := Module.finrank K (s.eigenspace (μ 2)) with hC
    have h3 : A + B + C = 3 := by
      rw [hA, hB, hC, ← hsum]
      exact hfr
    have hA1 : 1 ≤ A := by rw [hA]; exact hpos 0
    have hB1 : 1 ≤ B := by rw [hB]; exact hpos 1
    have hC1 : 1 ≤ C := by rw [hC]; exact hpos 2
    have hall : A = 1 ∧ B = 1 ∧ C = 1 := by omega
    have hd0 : Module.finrank K (s.eigenspace (μ 0)) = 1 := by rw [← hA]; exact hall.1
    have hd1 : Module.finrank K (s.eigenspace (μ 1)) = 1 := by rw [← hB]; exact hall.2.1
    have hd2 : Module.finrank K (s.eigenspace (μ 2)) = 1 := by rw [← hC]; exact hall.2.2
    intro i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  refine ⟨b, fun i => by rw [hb i]; exact (hv i).apply_eq_smul, hdim, ?_⟩
  intro g hg i
  exact exists_smul_of_finrank_eigenspace_eq_one hg (hdim i) (hmem i)

/-- **Each eigenspace is the line spanned by the corresponding basis vector.** -/
theorem eigenspace_eq_span_basis {s : Module.End K V} {μ : Fin 3 → K} {b : Basis (Fin 3) K V}
    (hb : ∀ i, s (b i) = μ i • b i)
    (hdim : ∀ i, Module.finrank K (s.eigenspace (μ i)) = 1) (i : Fin 3) :
    s.eigenspace (μ i) = Submodule.span K {b i} := by
  have hle : Submodule.span K {b i} ≤ s.eigenspace (μ i) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (Module.End.mem_eigenspace_iff.mpr (hb i)))
  refine Eq.symm (Submodule.eq_of_le_of_finrank_eq hle ?_)
  rw [finrank_span_singleton (b.ne_zero i), hdim i]

/-- **The family version**: if `s` has a basis of eigenvectors in three distinct
eigenspaces and every member of a commuting family commutes with `s`, then the
whole family is simultaneously diagonal in that basis. -/
theorem exists_common_eigenbasis_family [Nontrivial V] {ι : Type*} (f : ι → Module.End K V)
    (s : Module.End K V) (hs : ∀ i, Commute s (f i)) (μ : Fin 3 → K)
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) (hμ : Function.Injective μ) :
    ∃ b : Basis (Fin 3) K V,
      (∀ i, s (b i) = μ i • b i) ∧
      ∀ (i : ι) (j : Fin 3), ∃ c : K, f i (b j) = c • b j := by
  obtain ⟨b, hb, -, hdiag⟩ := exists_common_eigenbasis s μ hchar hμ
  exact ⟨b, hb, fun i j => hdiag (f i) (hs i) j⟩

end CommonEigenbasis

/-! ## From (B1) over `ℚ` to the common eigenbasis over `ℂ` -/

section IrreducibleCubic

/-- **A cubic splits over `ℂ` into three linear factors with distinct roots.**  If
`p : ℚ[X]` is monic and irreducible of degree three, then its image in `ℂ[X]` is a
product of three linear factors whose roots are pairwise distinct.

This is the exact form in which Berend's (B1) — an irreducible characteristic
polynomial over `ℤ`, hence over `ℚ` — is consumed by `exists_common_eigenbasis`;
it is pure polynomial algebra (splitting over `ℂ` plus separability in
characteristic zero). -/
theorem exists_roots_of_irreducible_cubic {p : ℚ[X]} (hp : p.Monic) (hirr : Irreducible p)
    (hdeg : p.natDegree = 3) :
    ∃ μ : Fin 3 → ℂ, Function.Injective μ ∧ p.map (algebraMap ℚ ℂ) = ∏ i, (X - C (μ i)) := by
  classical
  haveI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  set P : ℂ[X] := p.map (algebraMap ℚ ℂ) with hP
  have hPM : P.Monic := hp.map (algebraMap ℚ ℂ)
  have hPsep : P.Separable := (separable_map (algebraMap ℚ ℂ)).mpr hirr.separable
  have hnod : P.roots.Nodup := Polynomial.nodup_roots hPsep
  have hcard : P.roots.card = 3 := by
    rw [← Splits.natDegree_eq_card_roots (Fact.out : P.Splits), hP, natDegree_map, hdeg]
  obtain ⟨a, b, c, hL⟩ :=
    List.length_eq_three.mp (by simpa using hcard : P.roots.toList.length = 3)
  have hroots : P.roots = ((a :: b :: c :: [] : List ℂ) : Multiset ℂ) := by
    rw [← Multiset.coe_toList (s := P.roots), hL]
  have hnod' : (a :: b :: c :: [] : List ℂ).Nodup := by
    rw [← Multiset.coe_nodup, ← hroots]
    exact hnod
  have h1 := List.nodup_cons.mp hnod'
  have h2 := List.nodup_cons.mp h1.2
  have hab : a ≠ b := fun h => h1.1 (by simp [h])
  have hac : a ≠ c := fun h => h1.1 (by simp [h])
  have hbc : b ≠ c := fun h => h2.1 (by simp [h])
  refine ⟨![a, b, c], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [Splits.eq_prod_roots_of_monic (Fact.out : P.Splits) hPM, hroots]
    simp [List.prod_cons, Fin.prod_univ_three, mul_assoc]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]

/-- **§A.3 end to end.**  If the characteristic polynomial of `s : End ℂ V` is the
image over `ℂ` of a monic irreducible cubic `p` over `ℚ`, then `V` has a common
eigenbasis of `s` and of every endomorphism commuting with `s`, the eigenspaces are
one-dimensional, and the eigenvalues are the three distinct roots of `p`. -/
theorem exists_common_eigenbasis_of_irreducible_cubic (s : Module.End ℂ V) {p : ℚ[X]}
    (hp : p.Monic) (hirr : Irreducible p) (hdeg : p.natDegree = 3)
    (hchar : LinearMap.charpoly s = p.map (algebraMap ℚ ℂ)) :
    ∃ (μ : Fin 3 → ℂ) (b : Basis (Fin 3) ℂ V), Function.Injective μ ∧
      (∀ i, s (b i) = μ i • b i) ∧
      (∀ i, Module.finrank ℂ (s.eigenspace (μ i)) = 1) ∧
      ∀ g : Module.End ℂ V, Commute s g → ∀ i, ∃ c : ℂ, g (b i) = c • b i := by
  obtain ⟨μ, hμ, hprod⟩ := exists_roots_of_irreducible_cubic hp hirr hdeg
  rw [hprod] at hchar
  obtain ⟨b, hb, hdim, hdiag⟩ := exists_common_eigenbasis s μ hchar hμ
  exact ⟨μ, b, hμ, hb, hdim, hdiag⟩

end IrreducibleCubic

/-! ## Minimal invariant subspaces are coordinate lines (plan §C.1 input) -/

section MinimalInvariant

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every eigenvalue of a map whose characteristic polynomial is a product of the
three linear factors `X - μ i` is one of the `μ i`. -/
theorem exists_eq_of_hasEigenvalue_of_charpoly_eq_prod {s : Module.End K V} {μ : Fin 3 → K}
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) {ν : K} (hν : s.HasEigenvalue ν) :
    ∃ i, ν = μ i := by
  have hroot : (LinearMap.charpoly s).IsRoot ν :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly s ν).mp hν
  rw [Polynomial.IsRoot, hchar, Polynomial.eval_prod] at hroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  exact ⟨i, sub_eq_zero.mp (by simpa using hi)⟩

/-- **A minimal non-zero invariant subspace is one of the eigenlines.**  If `b` is a
common eigenbasis of `s` with pairwise distinct eigenvalues and `W` is a non-zero
`s`-invariant subspace minimal with that property, then `W` is the line spanned by
one of the basis vectors.  This is the "invariant subspaces are spanned by
coordinate subsets" input of Berend §4, in the minimal form in which §4 uses it. -/
theorem eq_span_basis_of_minimal_invariant [Nontrivial V] {s : Module.End K V} {μ : Fin 3 → K}
    (hchar : LinearMap.charpoly s = ∏ i, (X - C (μ i))) {b : Basis (Fin 3) K V}
    (hb : ∀ i, s (b i) = μ i • b i)
    (hdim : ∀ i, Module.finrank K (s.eigenspace (μ i)) = 1)
    (W : Submodule K V) (hW : ∀ x ∈ W, s x ∈ W) (hne : W ≠ ⊥)
    (hmin : ∀ W' : Submodule K V, W' ≤ W → W' ≠ ⊥ → (∀ x ∈ W', s x ∈ W') → W' = W) :
    ∃ i, W = Submodule.span K {b i} := by
  classical
  haveI : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue (LinearMap.restrict s hW)
  obtain ⟨z, hz⟩ := hν.exists_hasEigenvector
  set zV : V := (z : V) with hzV
  have hzW : zV ∈ W := z.2
  have hzne : zV ≠ 0 := by
    intro h
    exact hz.2 (Subtype.ext (by simpa [hzV] using h))
  have hzs : s zV = ν • zV := by
    have h := congrArg Subtype.val hz.apply_eq_smul
    simpa [LinearMap.restrict_apply, hzV] using h
  obtain ⟨i, rfl⟩ := exists_eq_of_hasEigenvalue_of_charpoly_eq_prod hchar
    (Module.End.hasEigenvalue_of_hasEigenvector
      (show s.HasEigenvector ν zV from ⟨Module.End.mem_eigenspace_iff.mpr hzs, hzne⟩))
  refine ⟨i, ?_⟩
  have hP : s.eigenspace (μ i) = Submodule.span K {b i} := eigenspace_eq_span_basis hb hdim i
  have hzspan : zV ∈ Submodule.span K {b i} := hP ▸ Module.End.mem_eigenspace_iff.mpr hzs
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzspan
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hzne hc.symm
  have hbi : b i ∈ W := by
    have : b i = c⁻¹ • zV := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hzW
  have hspan_le : Submodule.span K {b i} ≤ W := by
    rw [Submodule.span_le]
    rintro x rfl
    exact hbi
  have hinv : ∀ x ∈ Submodule.span K {b i}, s x ∈ Submodule.span K {b i} := by
    intro x hx
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hd, map_smul, hb i, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  exact (hmin (Submodule.span K {b i}) hspan_le (by simpa using b.ne_zero i) hinv).symm

end MinimalInvariant

end BerendA3

end CubicTwoStage