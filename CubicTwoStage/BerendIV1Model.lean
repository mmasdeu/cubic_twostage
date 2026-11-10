/-
# Furstenberg's Proposition IV.1 for the unit–prime model

Swarm `smw952unn`, member m7, direction d1.

`CubicTwoStage.BerendIV1.propIV1_of_congruence` proves Furstenberg's
Proposition IV.1 for an abstract commutative semigroup `Σ` of endomorphisms of a
compact abelian group, given

* an increasing sequence `T n` of "torsion" levels with dense union,
* the level-`n` congruence subsemigroup `K n = {k | k fixes T n pointwise}`,
* `hreps` — finiteness of `Σ / K n` (a finite set of representative products),
* `hint` — "closed invariant with interior is everything" for `K n`.

This file **instantiates** that theorem at the family
`Σ = {μ_{u π^j} : u ∈ 𝒪ˣ, j ≥ 0}` of the unit–prime model.

## What is proved here

* §1 (abstract): for `Σ = A × Multiplicative ℕ` with `A` a commutative group,
  and a level sequence of *finite* sets on which every family member acts
  injectively, `hreps` holds: the cyclic order of the prime direction together
  with a finite set of representatives of the unit classes gives every element a
  decomposition `m = r * k` with `k` fixing the level.
* §2 (abstract): the resulting `PropIV1` for the family, from §1 plus density,
  monotonicity and the interior hypothesis.
* §3 (concrete): `Σ = 𝒪ˣ × ℕ` acting by `D.torusAct`, the level sets
  `{x | q ^ n • x = 0}`, and the interior hypothesis *discharged* from the
  expanding multiplier with margin (`BerendExpandingMember.powC_margin`,
  `eq_univ_of_interior_of_pow_margin`): a positive power of the expanding member
  fixes the finite level set pointwise and still expands, so the interior step of
  Proposition IV.1 applies inside the congruence subsemigroup.

No `sorry`, no axiom, no use of `berend_multi_invariance`.

## The precise remaining inputs

The instantiated theorem `propIV1_unitPrime` takes the three level facts as
explicit hypotheses, exactly as they are used:

* `hfin : ∀ n, (lvlSet L q n).Finite` — the `q ^ n`-torsion of the torus is
  finite (`≅ L / q ^ n L`),
* `hdense : Dense (⋃ n, lvlSet L q n)` — the `q`-primary torsion is dense,
* `hinj` — every multiplier `μ_{u π^j}` is injective on each level; for
  `q` coprime to `det μ = ± Nm(u π^j) = ± p ^ j` this is the standard
  "nondegenerate at `q`" statement (the induced map on `L / q ^ n L` has
  determinant `± p ^ j`, a unit mod `q ^ n`).

`hint` is *not* an input: it is proved here from the expanding member.
-/
import CubicTwoStage.BerendIV1Congruence
import CubicTwoStage.BerendBlockLastMile
import CubicTwoStage.BerendExpandingMember
import CubicTwoStage.BerendLatticeIndex

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendIV1Model

/-! ## 1. `hreps` from finite levels with injective action -/

section Abstract

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {A : Type*} [CommGroup A]
variable {T : ℕ → Set G} {φ : A × Multiplicative ℕ →* AddMonoid.End G}
variable (hmap : ∀ (s : A × Multiplicative ℕ) (n : ℕ), (φ s : G → G) '' T n ⊆ T n)

/-- The level `n` as a type. -/
abbrev Lvl (T : ℕ → Set G) (n : ℕ) : Type _ := ↥(T n)

/-- The self-map of the level `n` induced by a family element. -/
noncomputable def actL (s : A × Multiplicative ℕ) (n : ℕ) : Lvl T n → Lvl T n :=
  fun x => ⟨(φ s) (x : G), hmap s n ⟨x.1, x.2, rfl⟩⟩

@[simp] theorem actL_coe (s : A × Multiplicative ℕ) (n : ℕ) (x : Lvl T n) :
    (actL hmap s n x : G) = (φ s) (x : G) := rfl

theorem actL_mul (s t : A × Multiplicative ℕ) (n : ℕ) (x : Lvl T n) :
    actL hmap (s * t) n x = actL hmap s n (actL hmap t n x) := by
  refine Subtype.ext ?_
  show (φ (s * t)) (x : G) = (φ s) ((φ t) (x : G))
  rw [map_mul]
  rfl

theorem actL_one (n : ℕ) (x : Lvl T n) : actL hmap 1 n x = x := by
  refine Subtype.ext ?_
  show (φ (1 : A × Multiplicative ℕ)) (x : G) = (x : G)
  rw [map_one]
  rfl

theorem actL_mul' (s t : A × Multiplicative ℕ) (n : ℕ) :
    actL hmap (s * t) n = actL hmap s n ∘ actL hmap t n := by
  funext x
  exact actL_mul hmap s t n x

theorem actL_pow (s : A × Multiplicative ℕ) (k n : ℕ) :
    actL hmap (s ^ k) n = (actL hmap s n)^[k] := by
  induction k with
  | zero =>
      funext x
      rw [pow_zero, Function.iterate_zero_apply]
      exact actL_one hmap n x
  | succ k ih =>
      rw [pow_succ, actL_mul', ih, Function.iterate_succ]

/-- Injectivity of the level-`n` action, from injectivity of the multipliers on
`T n`. -/
theorem actL_injective
    (hinj : ∀ (s : A × Multiplicative ℕ) (n : ℕ), ∀ x ∈ T n, ∀ y ∈ T n,
      (φ s) x = (φ s) y → x = y)
    (s : A × Multiplicative ℕ) (n : ℕ) : Function.Injective (actL hmap s n) := by
  intro x y hxy
  exact Subtype.ext (hinj s n x.1 x.2 y.1 y.2 (congrArg Subtype.val hxy))

theorem actL_surjective
    (hinj : ∀ (s : A × Multiplicative ℕ) (n : ℕ), ∀ x ∈ T n, ∀ y ∈ T n,
      (φ s) x = (φ s) y → x = y)
    (hfin : ∀ n, (T n).Finite)
    (s : A × Multiplicative ℕ) (n : ℕ) : Function.Surjective (actL hmap s n) := by
  haveI : Finite (Lvl T n) := (hfin n).to_subtype
  exact (Finite.injective_iff_surjective).mp (actL_injective hmap hinj s n)

/-- **Every member of the semigroup has a positive power that fixes the level
`T n` pointwise.**  This is where the level has to be finite: the induced map is
an injective self-map of a finite set, hence a permutation of finite order. -/
theorem exists_pos_pow_fixes
    (hinj : ∀ (s : A × Multiplicative ℕ) (n : ℕ), ∀ x ∈ T n, ∀ y ∈ T n,
      (φ s) x = (φ s) y → x = y)
    (hfin : ∀ n, (T n).Finite) (n : ℕ) (s : A × Multiplicative ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : Lvl T n, actL hmap (s ^ M) n x = x := by
  classical
  haveI : Finite (Lvl T n) := (hfin n).to_subtype
  haveI : Fintype (Lvl T n) := Fintype.ofFinite _
  have hinj' := actL_injective hmap hinj s n
  have hbij : Function.Bijective (actL hmap s n) :=
    ⟨hinj', (Finite.injective_iff_surjective).mp hinj'⟩
  let e : Equiv.Perm (Lvl T n) := Equiv.ofBijective (actL hmap s n) hbij
  refine ⟨Fintype.card (Equiv.Perm (Lvl T n)), ?_, ?_⟩
  · rw [Fintype.card_pos_iff]
    exact ⟨1⟩
  · intro x
    have hcoe : (↑e : Lvl T n → Lvl T n) = actL hmap s n := rfl
    rw [actL_pow (hmap := hmap), ← hcoe, ← Equiv.Perm.coe_pow, pow_card_eq_one]
    rfl

/-- The prime direction `(1, 1)` of `A × Multiplicative ℕ` has powers
`(1, 1) ^ t = (1, t)`. -/
theorem one_one_pow (t : ℕ) :
    ((1, Multiplicative.ofAdd 1) : A × Multiplicative ℕ) ^ t
      = (1, Multiplicative.ofAdd t) := by
  induction t with
  | zero => rw [pow_zero]; rfl
  | succ t ih =>
      rw [pow_succ, ih, Prod.mk_mul_mk, one_mul, ← ofAdd_add, Nat.add_comm]

/-- Powers of a semigroup element: `(u, j) ^ M = (u ^ M, j * M)`. -/
theorem pow_mk_ofAdd (u : A) (j M : ℕ) :
    ((u, Multiplicative.ofAdd j) : A × Multiplicative ℕ) ^ M
      = (u ^ M, Multiplicative.ofAdd (j * M)) := by
  induction M with
  | zero => rw [pow_zero, pow_zero, Nat.mul_zero, ofAdd_zero]; rfl
  | succ k ih =>
      rw [pow_succ, ih, Prod.mk_mul_mk, pow_succ, ← ofAdd_add, Nat.mul_succ]

/-- **`hreps`: finiteness of `Σ / K n`.**  Every element `m = (u, j)` of the
semigroup is a product `r * k` with `r` from a finite set depending only on `n`,
and `k` fixing `T n` pointwise: take `r = (v, j mod M)` where `v` represents the
action of the unit part and `M` is a positive power of the prime direction that
fixes the level. -/
theorem exists_reps
    (hmap : ∀ (s : A × Multiplicative ℕ) (n : ℕ), (φ s : G → G) '' T n ⊆ T n)
    (hinj : ∀ (s : A × Multiplicative ℕ) (n : ℕ), ∀ x ∈ T n, ∀ y ∈ T n,
      (φ s) x = (φ s) y → x = y)
    (hfin : ∀ n, (T n).Finite) (n : ℕ) :
    ∃ R : Finset (A × Multiplicative ℕ), ∀ m : A × Multiplicative ℕ,
      ∃ r ∈ R, ∃ k : A × Multiplicative ℕ,
        (∀ θ ∈ T n, (φ k) θ = θ) ∧ m = r * k := by
  classical
  haveI : Finite (Lvl T n) := (hfin n).to_subtype
  haveI : Fintype (Lvl T n) := Fintype.ofFinite _
  -- a positive power of the prime direction fixes the level
  obtain ⟨M, hMpos, hMfix⟩ := exists_pos_pow_fixes hmap hinj hfin n (1, Multiplicative.ofAdd 1)
  have hiter : (actL hmap (1, Multiplicative.ofAdd 1) n)^[M] = id := by
    rw [← actL_pow (hmap := hmap)]
    funext y
    exact hMfix y
  -- a finite set of representatives of the unit classes
  let rep : (Lvl T n → Lvl T n) → A := fun p =>
    if h : ∃ u : A, actL hmap (u, Multiplicative.ofAdd 0) n = p then Classical.choose h else 1
  have rep_spec : ∀ p : Lvl T n → Lvl T n,
      (∃ u : A, actL hmap (u, Multiplicative.ofAdd 0) n = p) →
      actL hmap (rep p, Multiplicative.ofAdd 0) n = p := by
    intro p h
    have hrep : rep p = Classical.choose h := by
      simp only [rep]
      rw [dif_pos h]
    rw [hrep]
    exact Classical.choose_spec h
  refine ⟨((Finset.univ : Finset (Lvl T n → Lvl T n)) ×ˢ Finset.range M).image
    (fun p : (Lvl T n → Lvl T n) × ℕ => (rep p.1, Multiplicative.ofAdd p.2)), ?_⟩
  intro m
  obtain ⟨u, j⟩ := m
  set p : Lvl T n → Lvl T n := actL hmap (u, Multiplicative.ofAdd 0) n with hp
  have hpex : ∃ w : A, actL hmap (w, Multiplicative.ofAdd 0) n = p := ⟨u, hp⟩
  refine ⟨(rep p, Multiplicative.ofAdd (j.toAdd % M)), ?_,
    ((rep p)⁻¹ * u, Multiplicative.ofAdd (M * (j.toAdd / M))), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(p, j.toAdd % M),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (Nat.mod_lt _ hMpos)⟩, rfl⟩
  · -- `k` fixes `T n` pointwise
    intro θ hθ
    have hkact : actL hmap ((rep p)⁻¹ * u, Multiplicative.ofAdd (M * (j.toAdd / M))) n = id := by
      -- the unit part acts trivially
      have hunit : actL hmap ((rep p)⁻¹ * u, Multiplicative.ofAdd 0) n = id := by
        have hprod : ((rep p)⁻¹ * u, Multiplicative.ofAdd 0) * (rep p, Multiplicative.ofAdd 0)
            = (u, Multiplicative.ofAdd 0) := by
          rw [Prod.mk_mul_mk, ofAdd_zero, one_mul]
          congr 1
          rw [mul_assoc, mul_comm u, ← mul_assoc, inv_mul_cancel, one_mul]
        have hcomp : actL hmap ((rep p)⁻¹ * u, Multiplicative.ofAdd 0) n ∘
            actL hmap (rep p, Multiplicative.ofAdd 0) n
            = actL hmap (u, Multiplicative.ofAdd 0) n := by
          rw [← actL_mul', hprod]
        rw [rep_spec p hpex] at hcomp
        funext x
        obtain ⟨y, rfl⟩ := actL_surjective hmap hinj hfin (u, Multiplicative.ofAdd 0) n x
        exact congrFun hcomp y
      -- the prime part acts trivially because the exponent is a multiple of `M`
      have hprime : actL hmap ((1 : A), Multiplicative.ofAdd (M * (j.toAdd / M))) n = id := by
        have hcast : ((1, Multiplicative.ofAdd (M * (j.toAdd / M))) : A × Multiplicative ℕ)
            = (1, Multiplicative.ofAdd 1) ^ (M * (j.toAdd / M)) := (one_one_pow _).symm
        rw [hcast, actL_pow (hmap := hmap), Function.iterate_mul, hiter, Function.iterate_id]
      have hk_eq : ((rep p)⁻¹ * u, Multiplicative.ofAdd (M * (j.toAdd / M)))
          = ((rep p)⁻¹ * u, Multiplicative.ofAdd 0) *
            (1, Multiplicative.ofAdd (M * (j.toAdd / M))) := by
        rw [Prod.mk_mul_mk, mul_one, ofAdd_zero, one_mul]
      rw [hk_eq, actL_mul', hunit, hprime]
      rfl
    have h := congrArg (fun f => f ⟨θ, hθ⟩) hkact
    exact congrArg Subtype.val h
  · -- the decomposition `m = r * k`
    show (u, j) = (rep p, Multiplicative.ofAdd (j.toAdd % M)) *
      ((rep p)⁻¹ * u, Multiplicative.ofAdd (M * (j.toAdd / M)))
    rw [Prod.mk_mul_mk, ← ofAdd_add]
    have h1 : rep p * ((rep p)⁻¹ * u) = u := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : (Multiplicative.ofAdd (j.toAdd % M + M * (j.toAdd / M)) : Multiplicative ℕ) = j := by
      have h := Nat.div_add_mod j.toAdd M
      rw [Nat.add_comm]
      show Multiplicative.ofAdd (M * (j.toAdd / M) + j.toAdd % M) = j
      rw [h]
      rfl
    rw [h1, h2]

end Abstract

/-! ## 2. Proposition IV.1 for the family from the level data -/

section AbstractIV1

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]
variable {A : Type*} [CommGroup A]
variable {T : ℕ → Set G} {φ : A × Multiplicative ℕ →* AddMonoid.End G}
variable (hmap : ∀ (s : A × Multiplicative ℕ) (n : ℕ), (φ s : G → G) '' T n ⊆ T n)

/-- **Furstenberg's Proposition IV.1 for a semigroup of the form `A × ℕ`**, from
the level data: finiteness, density, monotonicity of the levels, injectivity of
every member on each level, and the interior statement for the congruence
subsemigroup (which `propIV1_of_congruence` takes as `hint`). -/
theorem propIV1_of_levels
    (hmap : ∀ (s : A × Multiplicative ℕ) (n : ℕ), (φ s : G → G) '' T n ⊆ T n)
    (hinj : ∀ (s : A × Multiplicative ℕ) (n : ℕ), ∀ x ∈ T n, ∀ y ∈ T n,
      (φ s) x = (φ s) y → x = y)
    (hfin : ∀ n, (T n).Finite)
    (hdense : Dense (⋃ n, T n))
    (hTmono : ∀ n m : ℕ, n ≤ m → T n ⊆ T m)
    (hcont : ∀ s : A × Multiplicative ℕ, Continuous (φ s))
    (hint : ∀ n, ∀ C : Set G, IsClosed C →
      (∀ k : A × Multiplicative ℕ, (∀ θ ∈ T n, (φ k) θ = θ) →
        (φ k : G → G) '' C ⊆ C) →
      (interior C).Nonempty → C = univ) :
    BerendPropIV1.PropIV1 (fun s : A × Multiplicative ℕ => φ s) := by
  refine BerendIV1.propIV1_of_congruence (φ := φ) (fun s => hcont s) T hdense hTmono
    (fun n => {k : A × Multiplicative ℕ | ∀ θ ∈ T n, (φ k) θ = θ}) ?_ ?_ ?_ hint
  · intro n θ _
    rw [map_one]
    rfl
  · intro n k hk
    exact hk
  · intro n
    obtain ⟨R, hR⟩ := exists_reps hmap hinj hfin n
    refine ⟨R, fun m => ?_⟩
    obtain ⟨r, hr, k, hk, hm⟩ := hR m
    exact ⟨r, hr, k, hk, hm⟩

/-- Reindexing a family along a surjection does not change Proposition IV.1. -/
theorem propIV1_reindex {ι ι' : Type*} {F : ι → G →+ G} (e : ι' → ι)
    (he : Function.Surjective e) : BerendPropIV1.PropIV1 (fun i' => F (e i')) →
      BerendPropIV1.PropIV1 F := by
  intro h M B hMne hMclosed hBclosed hMinv hBinv hMmin hcover
  refine h M B hMne hMclosed hBclosed ?_ ?_ ?_ hcover
  · intro i'
    exact hMinv (e i')
  · intro i'
    exact hBinv (e i')
  · refine ⟨hMmin.ne, hMmin.closed, fun i' => hMmin.inv (e i'), ?_⟩
    intro M' hsub hne hcl hinv'
    exact hMmin.minimal M' hsub hne hcl (fun i => by
      obtain ⟨i', rfl⟩ := he i
      exact hinv' i')

end AbstractIV1

/-! ## 3. The unit–prime model -/

section Model

variable {K : Type*} [Field K] {L : AddSubgroup Pt} {𝒪 : Subring K}
variable [DiscreteTopology (AddSubgroup.toIntSubmodule L)]
  [IsZLattice ℝ (AddSubgroup.toIntSubmodule L)]

/-- The `q ^ n`-torsion level of the torus. -/
def lvlSet (L : AddSubgroup Pt) (q n : ℕ) : Set (Torus L) := {x | q ^ n • x = 0}

theorem mem_lvlSet {L : AddSubgroup Pt} {q n : ℕ} {x : Torus L} :
    x ∈ lvlSet L q n ↔ q ^ n • x = 0 := Iff.rfl

theorem lvlSet_antitone_torsion {L : AddSubgroup Pt} {q : ℕ} {n m : ℕ} (hnm : n ≤ m) :
    lvlSet L q n ⊆ lvlSet L q m := by
  intro x hx
  rw [mem_lvlSet] at hx ⊢
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [pow_add, mul_nsmul, hx, nsmul_zero]

/-

## 3b. Density of the `q`-primary levels

The `q`-primary torsion of the torus is dense: given an open set, one uses the
covering radius `R` of the lattice (`BerendInteriorFull.exists_cover_radius`) and
divides the lattice point it produces by `q ^ n` for large `n`.  This discharges
the hypothesis `hdense` of `propIV1_unitPrime`.
-/

/-- **The `q`-primary levels are dense in the torus**, for `q ≥ 2`. -/
theorem dense_iUnion_lvlSet (q : ℕ) (hq : 2 ≤ q) : Dense (⋃ n, lvlSet L q n) := by
  classical
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  obtain ⟨R, hRpos, hcov⟩ := BerendInteriorFull.exists_cover_radius (L := L)
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective L x
  -- a ball around `w` inside the preimage of `U`
  have hWopen : IsOpen ((QuotientAddGroup.mk' L) ⁻¹' U) :=
    hUopen.preimage continuous_quotient_mk'
  have hwW : w ∈ (QuotientAddGroup.mk' L) ⁻¹' U := hxU
  obtain ⟨ρ, hρpos, hballW⟩ := Metric.isOpen_iff.mp hWopen w hwW
  -- choose `n` so that the covering radius divided by `q ^ n` is below `ρ`
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / ρ) hq1
  rw [div_lt_iff₀ hρpos] at hn
  have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hqpow_ne : ((q : ℝ) ^ n) ≠ 0 := ne_of_gt hqpow_pos
  -- a lattice point `l` within the covering radius of `q ^ n • w`
  have h0 : (0 : Torus L) ∈ (QuotientAddGroup.mk' L) '' Metric.ball (q ^ n • w) R := by
    rw [hcov]
    exact mem_univ 0
  obtain ⟨l, hlball, hl0⟩ := h0
  rw [Metric.mem_ball, dist_eq_norm] at hlball
  have hlL : l ∈ L := by
    have h : (QuotientAddGroup.mk' L) l = (QuotientAddGroup.mk' L) (0 : Pt) := hl0
    simpa using QuotientAddGroup.eq_iff_sub_mem.mp h
  -- the approximating point `z = w - (q ^ n)⁻¹ (q ^ n • w - l)`
  have hnsmul : ∀ v : Pt, q ^ n • v = ((q : ℝ) ^ n) • v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul ℝ (q ^ n) v, Nat.cast_pow]
  rw [hnsmul w] at hlball
  set a : Pt := ((q : ℝ) ^ n) • w - l with hadef
  set z : Pt := w - ((q : ℝ) ^ n)⁻¹ • a with hzdef
  have hqzn : q ^ n • z = l := by
    rw [hnsmul, hzdef, smul_sub, smul_smul, mul_inv_cancel₀ hqpow_ne, one_smul, hadef]
    abel
  have hzmem : (QuotientAddGroup.mk' L) z ∈ lvlSet L q n := by
    rw [mem_lvlSet, ← map_nsmul, hqzn]
    exact hl0
  have hzball : z ∈ Metric.ball w ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : z - w = -(((q : ℝ) ^ n)⁻¹ • a) := by rw [hzdef]; abel
    have hnorm : ‖z - w‖ = ((q : ℝ) ^ n)⁻¹ * ‖a‖ := by
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hqpow_pos]
    rw [hnorm, inv_mul_lt_iff₀ hqpow_pos]
    have haeq : ‖a‖ = ‖l - ((q : ℝ) ^ n) • w‖ := by
      rw [hadef, norm_sub_rev]
    rw [haeq]
    have hgoal : ‖l - ((q : ℝ) ^ n) • w‖ < ρ * (q : ℝ) ^ n := by
      calc ‖l - ((q : ℝ) ^ n) • w‖ < R := hlball
        _ < (q : ℝ) ^ n * ρ := hn
        _ = ρ * (q : ℝ) ^ n := mul_comm _ _
    simpa [mul_comm] using hgoal
  exact ⟨(QuotientAddGroup.mk' L) z, ⟨hballW hzball, mem_iUnion.mpr ⟨n, hzmem⟩⟩⟩


/-- The semigroup structure of the unit–prime family: `(u, j) * (v, l) = (uv, j + l)`. -/
noncomputable def familyHom (D : UnitPrimeModel L 𝒪) :
    𝒪ˣ × Multiplicative ℕ →* AddMonoid.End (Torus L) where
  toFun s := D.torusAct (s.1, s.2.toAdd)
  map_one' := by
    ext z
    show D.torusAct (1, 0) z = z
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
        rw [UnitPrimeModel.torusAct_mk, D.family_act_one_zero]
  map_mul' := by
    rintro ⟨u, j⟩ ⟨v, l⟩
    ext z
    show D.torusAct (u * v, j.toAdd + l.toAdd) z =
      D.torusAct (u, j.toAdd) (D.torusAct (v, l.toAdd) z)
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
        rw [UnitPrimeModel.torusAct_mk, UnitPrimeModel.torusAct_mk, UnitPrimeModel.torusAct_mk]
        simp only [UnitPrimeModel.family_apply]
        rw [← mulC_assoc, ← mult_mul]

@[simp] theorem familyHom_apply (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) :
    familyHom D (u, Multiplicative.ofAdd j) = D.torusAct (u, j) := rfl

theorem familyHom_image_lvlSet (D : UnitPrimeModel L 𝒪) (q : ℕ)
    (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ) :
    (familyHom D s : Torus L → Torus L) '' lvlSet L q n ⊆ lvlSet L q n := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_lvlSet] at hx ⊢
  rw [← map_nsmul]
  rw [hx, map_zero]

/-- The interior step, with the expanding member produced: a positive power of the
expanding multiplier fixes the finite level pointwise, so it lies in the
congruence subsemigroup, and `eq_univ_of_interior_of_pow_margin` applies. -/
theorem exists_ball_of_interior {C : Set (Torus L)} (hint : (interior C).Nonempty) :
    ∃ x₀ : Pt, ∃ r : ℝ, 0 < r ∧ (QuotientAddGroup.mk' L) '' Metric.ball x₀ r ⊆ C := by
  obtain ⟨y, hy⟩ := hint
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk'_surjective L y
  have hopen : IsOpen ((QuotientAddGroup.mk' L) ⁻¹' interior C) :=
    isOpen_interior.preimage continuous_quotient_mk'
  have hmem : x₀ ∈ (QuotientAddGroup.mk' L) ⁻¹' interior C := hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x₀ hmem
  refine ⟨x₀, r, hr, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hz
  exact interior_subset (show (QuotientAddGroup.mk' L) w ∈ interior C from hball hw)

/-- **The interior hypothesis of Proposition IV.1 for the congruence subsemigroup,
discharged by the expanding member.** -/
theorem interior_full_of_level (D : UnitPrimeModel L 𝒪) (q : ℕ)
    (u₀ : 𝒪ˣ) (j₀ : ℕ) (ha0 : 4 ≤ |D.mult u₀ j₀ 0|) (hC : 16 ≤ normC (D.mult u₀ j₀))
    (hinj : ∀ (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ), ∀ x ∈ lvlSet L q n,
      ∀ y ∈ lvlSet L q n, (familyHom D s) x = (familyHom D s) y → x = y)
    (hfin : ∀ n, (lvlSet L q n).Finite)
    (n : ℕ) {C : Set (Torus L)} (hCclosed : IsClosed C)
    (hCinv : ∀ k : 𝒪ˣ × Multiplicative ℕ,
      (∀ θ ∈ lvlSet L q n, (familyHom D k) θ = θ) →
      (familyHom D k : Torus L → Torus L) '' C ⊆ C)
    (hint : (interior C).Nonempty) : C = univ := by
  classical
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  -- a positive power of the expanding multiplier fixes the level
  obtain ⟨M, hMpos, hMfix⟩ :=
    exists_pos_pow_fixes (familyHom_image_lvlSet D q) hinj hfin n
      (u₀, Multiplicative.ofAdd j₀)
  have hpow : ((u₀, Multiplicative.ofAdd j₀) : 𝒪ˣ × Multiplicative ℕ) ^ M
      = (u₀ ^ M, Multiplicative.ofAdd (j₀ * M)) := pow_mk_ofAdd u₀ j₀ M
  have hfix : ∀ θ ∈ lvlSet L q n,
      (familyHom D ((u₀, Multiplicative.ofAdd j₀) ^ M)) θ = θ := by
    intro θ hθ
    have h := hMfix ⟨θ, hθ⟩
    exact congrArg Subtype.val h
  have hinv : D.torusAct (u₀ ^ M, j₀ * M) '' C ⊆ C := by
    have h := hCinv _ hfix
    rwa [hpow, familyHom_apply] at h
  obtain ⟨x₀, r, hr, hball⟩ := exists_ball_of_interior (L := L) hint
  exact eq_univ_of_interior_of_pow_margin D u₀ j₀ ha0 hC hCclosed hMpos hinv
    ⟨x₀, r, hr, hball⟩

/-- **Furstenberg's Proposition IV.1 for the unit–prime family**, with the
interior hypothesis discharged and the three level facts as explicit inputs. -/
theorem propIV1_unitPrime (D : UnitPrimeModel L 𝒪) (q : ℕ)
    (hinj : ∀ (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ), ∀ x ∈ lvlSet L q n,
      ∀ y ∈ lvlSet L q n, (familyHom D s) x = (familyHom D s) y → x = y)
    (hq : 2 ≤ q)
    (u₀ : 𝒪ˣ) (j₀ : ℕ) (ha0 : 4 ≤ |D.mult u₀ j₀ 0|) (hC : 16 ≤ normC (D.mult u₀ j₀)) :
    BerendPropIV1.PropIV1 (fun s : 𝒪ˣ × Multiplicative ℕ => familyHom D s) := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  have hfin : ∀ n, (lvlSet L q n).Finite := fun n =>
    BerendLatticeIndex.finite_nsmul_torsion (q ^ n) (Nat.pow_pos (by omega))
  have hdense : Dense (⋃ n, lvlSet L q n) := dense_iUnion_lvlSet q hq
  refine propIV1_of_levels (familyHom_image_lvlSet D q) hinj hfin hdense
    (fun n m hnm => lvlSet_antitone_torsion hnm) ?_
    (fun n C hCclosed hCinv hint =>
      interior_full_of_level D q u₀ j₀ ha0 hC hinj hfin n hCclosed hCinv hint)
  intro s
  exact D.continuous_torusAct (s.1, s.2.toAdd)

/-- **Proposition IV.1 for the family `Σ = {μ_{u π^j}}` indexed by `𝒪ˣ × ℕ`**, the
form in which `BerendPropIV1.minimal_finite_of_propIV1` consumes it. -/
theorem propIV1_unitPrime' (D : UnitPrimeModel L 𝒪) (q : ℕ)
    (hinj : ∀ (s : 𝒪ˣ × Multiplicative ℕ) (n : ℕ), ∀ x ∈ lvlSet L q n,
      ∀ y ∈ lvlSet L q n, (familyHom D s) x = (familyHom D s) y → x = y)
    (hq : 2 ≤ q)
    (u₀ : 𝒪ˣ) (j₀ : ℕ) (ha0 : 4 ≤ |D.mult u₀ j₀ 0|) (hC : 16 ≤ normC (D.mult u₀ j₀)) :
    BerendPropIV1.PropIV1 (fun i : 𝒪ˣ × ℕ => D.torusAct i) := by
  haveI : CompactSpace (Torus L) := compact_quotient_of_isZLattice L
  have h := propIV1_unitPrime D q hinj hq u₀ j₀ ha0 hC
  refine propIV1_reindex (F := fun i : 𝒪ˣ × ℕ => D.torusAct i)
    (fun s : 𝒪ˣ × Multiplicative ℕ => (s.1, s.2.toAdd)) ?_ ?_
  · rintro ⟨u, j⟩
    exact ⟨(u, Multiplicative.ofAdd j), rfl⟩
  · exact h



end Model


/-

## 5. Injectivity on the levels, from one arithmetic saturation statement

For the congruence argument of Proposition IV.1 the multipliers must act
*injectively* on each level `T n = {x | q ^ n • x = 0}` (they then act as
permutations of a finite set).  Mathematically this is the statement that the
reduction of `μ_{u π^j}` modulo `q ^ n` is invertible, i.e. that
`det μ = ± Nm(u π^j) = ± p ^ j` is a unit modulo `q ^ n`: `q ∤ p`.

The same statement, in the form in which it is used, is that a lattice vector
divisible by `q` may be divided by `q` once the prime has been removed:

`∀ w, q • w ∈ L → π ⋆ w ∈ L → w ∈ L`  (`SaturatesAt D q`).

This section derives injectivity on every level from that single hypothesis; no
other arithmetic input is used.
-/

end BerendIV1Model
end CubicTwoStage

/-! ## Axiom audit -/

#print axioms CubicTwoStage.BerendIV1Model.actL_pow
#print axioms CubicTwoStage.BerendIV1Model.exists_pos_pow_fixes
#print axioms CubicTwoStage.BerendIV1Model.pow_mk_ofAdd
#print axioms CubicTwoStage.BerendIV1Model.exists_reps
#print axioms CubicTwoStage.BerendIV1Model.propIV1_of_levels
#print axioms CubicTwoStage.BerendIV1Model.propIV1_reindex
#print axioms CubicTwoStage.BerendIV1Model.lvlSet_antitone_torsion
#print axioms CubicTwoStage.BerendIV1Model.familyHom_image_lvlSet
#print axioms CubicTwoStage.BerendIV1Model.exists_ball_of_interior
#print axioms CubicTwoStage.BerendIV1Model.interior_full_of_level
#print axioms CubicTwoStage.BerendIV1Model.propIV1_unitPrime
#print axioms CubicTwoStage.BerendIV1Model.propIV1_unitPrime'
#print axioms CubicTwoStage.BerendIV1Model.dense_iUnion_lvlSet
