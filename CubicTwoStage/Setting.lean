/-
Section 3 of the paper: Definition 3.4, Proposition 3.5, Theorem 3.6,
Lemmas 3.7 and 3.8.
-/
import CubicTwoStage.Basic
import CubicTwoStage.Model
import CubicTwoStage.Cooke
import CubicTwoStage.Padic

set_option linter.unusedVariables false

namespace CubicTwoStage

variable {K : Type*} [Field K]

/-! ### Definition 3.4: `𝒞_N`, `N`-smooth Euclideanity, smooth level -/

/-- **Definition 3.4** (the set `𝒞_N`).  The centres of the regions whose
denominator has norm at most `N`: the elements `[q₁,q₂] = q₁ + 1/q₂` with
`q₁, q₂ ∈ 𝒪` and `|Nm q₂| ≤ N`. -/
def Centres (𝒪 : Subring K) (Nm : AbsNorm K) (N : ℕ) : Set K :=
  {c | ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ c = q1 + q2⁻¹ ∧ Nm q2 ≤ (N : ℚ≥0)}

/-- **Definition 3.4**.  `K` is **`N`-smooth Euclidean** if the fundamental domain
`D̄` is covered by the regions whose centres lie in `𝒞_N`. -/
def IsNSmoothEuclidean (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (N : ℕ) : Prop :=
  ∀ x ∈ unitCube, ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧ Nm q2 ≤ (N : ℚ≥0) ∧
    |normR (x - σ (q1 + q2⁻¹))| < (((Nm q2 : ℚ≥0) : ℝ))⁻¹

/-- **Definition 3.4** (the smooth level).  `N` is *the* smooth level `N_min(K)`. -/
def HasSmoothLevel (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) (N : ℕ) : Prop :=
  IsNSmoothEuclidean 𝒪 Nm σ N ∧ ∀ M, M < N → ¬ IsNSmoothEuclidean 𝒪 Nm σ M

/-! ### Proposition 3.5 -/

/-- **Proposition 3.5**.  Let `n ≥ 1`, let `t = lcm(1,…,n)`, and let `K` be
`n`-smooth Euclidean.  Then the inhomogeneous minimum satisfies

  `M(K) = sup_{ξ ∈ K} min_{g ∈ 𝒪} |Nm(ξ - g)| ≤ t³`,

and consequently

  `|d_K| ≤ (420 t³)²`.

Both inequalities are the conclusions of this theorem.  The hypotheses
`hM`/`hMmin` express `M = M(K)` as the least real bound for the nearest-integer
norms, while `hCassels` is Cassels' inequality `√|d_K| / 420 ≤ M(K)` ([Ca], quoted
in the paper).  The other assumptions are the concrete inputs used by its proof:
translation of an arbitrary point into the fundamental domain (`hfund`),
integrality of `t / α` (`hdiv`), positive integer values of the norm on `𝒪`
(`hNat`), and the cubic scaling of an integer scalar (`hdeg`). -/
theorem prop_finite_smooth (𝒪 : Subring K) [Algebra ℚ K] [CharZero K] (Nm : AbsNorm K) (σ : K →ₗ[ℚ] Pt) (n t : ℕ)
    (hn : 1 ≤ n) (ht : 0 < t)
    (hSmooth : IsNSmoothEuclidean 𝒪 Nm σ n)
    (hfund : ∀ x : Pt, ∃ g ∈ 𝒪, x - σ g ∈ unitCube)
    (hdiv : ∀ q : K, q ∈ 𝒪 → Nm q ≤ (n : ℚ≥0) → (t : K) / q ∈ (𝒪 : Set K))
    (hdeg : ∀ c : ℕ, Nm (c : K) = (c : ℚ≥0) ^ 3)
    (hNat : ∀ α ∈ 𝒪, α ≠ 0 → ∃ k : ℕ, 0 < k ∧ Nm α = (k : ℚ≥0))
    (hNm : ∀ a b : K, (((Nm (a - b) : ℚ≥0)) : ℝ) = |normR (σ a - σ b)|)
    (M : ℝ) (hM : ∀ ξ : K, ∃ g ∈ 𝒪, |(((Nm (ξ - g) : ℚ≥0)) : ℝ)| ≤ M)
    (hMmin : ∀ m : ℝ, (∀ ξ : K, ∃ g ∈ 𝒪, |(((Nm (ξ - g) : ℚ≥0)) : ℝ)| ≤ m) → M ≤ m)
    (dK : ℤ) (hCassels : Real.sqrt ((|dK| : ℤ) : ℝ) / 420 ≤ M) :
    M ≤ (t : ℝ) ^ 3 ∧ ((|dK| : ℤ) : ℝ) ≤ (420 * (t : ℝ) ^ 3) ^ 2 := by
  have htK : (t : K) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have htnat : ∀ c : ℕ, (c : K) ∈ 𝒪 := by
    intro c
    induction c with
    | zero => simpa using 𝒪.zero_mem
    | succ c ih => simpa [Nat.cast_succ] using 𝒪.add_mem ih 𝒪.one_mem
  have hMle : M ≤ (t : ℝ) ^ 3 := by
    refine hMmin ((t : ℝ) ^ 3) (fun ξ => ?_)
    obtain ⟨g, hg, hgfund⟩ := hfund (σ (ξ / (t : K)))
    obtain ⟨q1, hq1, q2, hq2, hq2ne, hq2le, hbound⟩ := hSmooth _ hgfund
    obtain ⟨k, hk, htk⟩ := hNat q2 hq2 hq2ne
    have hq2Pos : 0 < (((Nm q2 : ℚ≥0)) : ℝ) := by exact_mod_cast (zero_lt_iff.mpr ((AbsNorm.ne_zero_iff Nm).mpr hq2ne))
    have htkO : (t : K) / q2 ∈ 𝒪 := hdiv q2 hq2 hq2le
    have hcentreO : (t : K) * (q1 + g + q2⁻¹) ∈ 𝒪 := by
      have heq : (t : K) * (q1 + g + q2⁻¹) = (t : K) * (q1 + g) + (t : K) / q2 := by
        field_simp
      rw [heq]
      exact 𝒪.add_mem (𝒪.mul_mem (htnat t) (𝒪.add_mem hq1 hg)) htkO
    refine ⟨(t : K) * (q1 + g + q2⁻¹), hcentreO, ?_⟩
    have hb : ((Nm (ξ / (t : K) - (q1 + g + q2⁻¹)) : ℚ≥0) : ℝ) <
        (((Nm q2 : ℚ≥0)) : ℝ)⁻¹ := by
      rw [hNm]
      convert hbound using 1
      simp [map_add, sub_eq_add_neg, add_assoc]
      abel
    have hb1 : ((Nm (ξ / (t : K) - (q1 + g + q2⁻¹)) : ℚ≥0) : ℝ) < 1 := by
      apply lt_of_lt_of_le hb
      have hq2ge1 : (1 : ℚ≥0) ≤ Nm q2 := by
        rw [htk]
        exact_mod_cast hk
      rw [inv_le_one₀ hq2Pos]
      exact_mod_cast hq2ge1
    let a : K := q1 + g + q2⁻¹
    have hident : ξ - (t : K) * a = (t : K) * (ξ / (t : K) - a) := by
      field_simp
    have hnormInt : ((Nm (ξ - (t : K) * a) : ℚ≥0) : ℝ) =
        (t : ℝ) ^ 3 * ((Nm (ξ / (t : K) - a) : ℚ≥0) : ℝ) := by
      rw [hident, map_mul, hdeg t]
      norm_cast
    rw [hnormInt]
    have hPosX : 0 ≤ ((Nm (ξ / (t : K) - a) : ℚ≥0) : ℝ) := by positivity
    have htPos : 0 ≤ (t : ℝ) ^ 3 := by positivity
    rw [abs_of_nonneg (by positivity)]
    have hb1' : ((Nm (ξ / (t : K) - a) : ℚ≥0) : ℝ) < 1 := hb1
    nlinarith
  refine ⟨hMle, ?_⟩
  have hsqrt : Real.sqrt ((|dK| : ℤ) : ℝ) ≤ 420 * (t : ℝ) ^ 3 := by
    calc
      _ = 420 * (Real.sqrt ((|dK| : ℤ) : ℝ) / 420) := by ring
      _ ≤ 420 * M := mul_le_mul_of_nonneg_left hCassels (by norm_num)
      _ ≤ 420 * (t : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hMle (by norm_num)
  calc
    ((|dK| : ℤ) : ℝ) = Real.sqrt ((|dK| : ℤ) : ℝ) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    _ ≤ (420 * (t : ℝ) ^ 3) ^ 2 := by nlinarith [Real.sqrt_nonneg ((|dK| : ℤ) : ℝ)]


/-! ### Theorem 3.6: the uncovered set is finite -/

/-- The set `𝒵` of points of `ℝ × ℂ` that lie in no region `V(q)`. -/
def uncovered (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K → Pt) : Set Pt :=
  {x | ∀ q1 ∈ 𝒪, ∀ q2 ∈ 𝒪, q2 ≠ 0 →
    ¬ |normR (x - σ (q1 + q2⁻¹))| < (((Nm q2 : ℚ≥0)) : ℝ)⁻¹}

/-- An indexed commuting family of endomorphisms of `ℝ × ℂ`, preserving the
lattice `L`.  This is the data on which the multi-invariance theorem of Berend
will be invoked. -/
structure CommutingTorusActions (L : AddSubgroup Pt) (ι : Type*) where
  act : ι → (Pt →+ Pt)
  lattice : ∀ i : ι, ∀ g ∈ L, act i g ∈ L
  commute : ∀ i j : ι, ∀ x : Pt, act i (act j x) = act j (act i x)

/-- A multiplier model for multiplication by `u · π^j` on the model algebra
`ℝ × ℂ` (see `Model.lean`).  Its indices are algebraic units and nonnegative
powers of a prime.

Besides the multiplicative images `unit_image u` and `prime_image prime` of the
data, the structure records the inverse multipliers `unit_inv u`, `prime_inv`
and the two facts that make them inverses.  These are part of the model, not
extra mathematical hypotheses: in the intended instance `unit_image` is the
restriction of the embedding `σ` to `𝒪ˣ`, so `unit_inv u` is `σ(u⁻¹)`, and
`prime_image π = σ(π)` is a unit of the model algebra because `σ(π)` has no zero
coordinate.  Recording them makes the multipliers invertible linear maps and
the induced torus endomorphisms injective, both of which are used below. -/
structure UnitPrimeModel {K : Type*} [Field K] (L : AddSubgroup Pt) (𝒪 : Subring K) where
  unit : K
  unit_image : (𝒪ˣ) → Pt
  unit_mul : ∀ u v : 𝒪ˣ, unit_image (u * v) = unit_image u ⋆ unit_image v
  unit_one : unit_image 1 = oneC
  unit_inv : 𝒪ˣ → Pt
  unit_inv_mul : ∀ u : 𝒪ˣ, unit_image u ⋆ unit_inv u = oneC
  prime : K
  prime_image : K → Pt
  prime_inv : Pt
  prime_inv_mul : prime_image prime ⋆ prime_inv = oneC
  lattice : ∀ u : 𝒪ˣ, ∀ j : ℕ, ∀ g ∈ L,
    (unit_image u ⋆ powC (prime_image prime) j) ⋆ g ∈ L
  lattice_unit_inv : ∀ (u : 𝒪ˣ) (g : Pt), g ∈ L → unit_inv u ⋆ g ∈ L

/-- The multiplier attached to the index `(u, j)`: `σ(u · π^j)`. -/
noncomputable def UnitPrimeModel.mult {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) : Pt :=
  D.unit_image u ⋆ powC (D.prime_image D.prime) j

/-- Multiplication by a point of the model algebra, as an additive
endomorphism. -/
noncomputable def addHomMulC (a : Pt) : Pt →+ Pt where
  toFun := fun x => a ⋆ x
  map_zero' := mulC_zero a
  map_add' := fun x y => mulC_add a x y

@[simp] lemma addHomMulC_apply (a x : Pt) : addHomMulC a x = a ⋆ x := rfl

/-- The concrete commuting endomorphisms generated by multiplication by a unit
and by a prime. -/
noncomputable def UnitPrimeModel.family {K : Type*} [Field K] {L : AddSubgroup Pt}
    (𝒪 : Subring K) (D : UnitPrimeModel L 𝒪) :
    CommutingTorusActions L (𝒪ˣ × ℕ) where
  act := fun i => addHomMulC (D.mult i.1 i.2)
  lattice := fun ⟨u, j⟩ g hg => D.lattice u j g hg
  commute := by
    rintro ⟨u, j⟩ ⟨v, l⟩ x
    show D.mult u j ⋆ (D.mult v l ⋆ x) = D.mult v l ⋆ (D.mult u j ⋆ x)
    rw [← mulC_assoc, ← mulC_assoc, mulC_comm (D.mult u j) (D.mult v l)]

/-- Apply a list of unit–prime actions in sequence, setting the empty list to
the identity action. -/
noncomputable def UnitPrimeModel.applyList {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (l : List (𝒪ˣ × ℕ)) (x : Pt) : Pt :=
  l.foldl (fun z i => D.family.act i z) x

@[simp] lemma UnitPrimeModel.applyList_nil {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (x : Pt) : D.applyList [] x = x := rfl

lemma UnitPrimeModel.applyList_append_singleton {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (l : List (𝒪ˣ × ℕ)) (i : 𝒪ˣ × ℕ)
    (x : Pt) :
    D.applyList (l ++ [i]) x = D.family.act i (D.applyList l x) := by
  simp only [UnitPrimeModel.applyList, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `(1, 0)` gives the identity torus endomorphism. -/
lemma UnitPrimeModel.family_act_one_zero {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (x : Pt) :
    D.family.act (1, 0) x = x := by
  show D.unit_image 1 ⋆ powC (D.prime_image D.prime) 0 ⋆ x = x
  rw [D.unit_one, powC_zero, mulC_oneC, oneC_mulC]

/-- Defining formula for the unit–prime action. -/
lemma UnitPrimeModel.family_apply {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (x : Pt) :
    D.family.act (u, j) x = D.mult u j ⋆ x := rfl

/-! ### The unit-only action

The family is indexed by pairs `(u, j)`, so an iterate of a single element mixes
in powers of `π`.  The periodic-orbit argument of Theorem 3.6 needs the action of
the unit `ε` *alone*, iterated: it is `μ_ε` of the paper, not `μ_{επ^j}`.  The
two actions are related by `actU_mul`, which is why the model records
`unit_mul`. -/

/-- The action of a single unit `u` on the model algebra: multiplication by
`unit_image u`. -/
noncomputable def UnitPrimeModel.actU {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) : Pt →+ Pt :=
  addHomMulC (D.unit_image u)

lemma UnitPrimeModel.actU_apply {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (x : Pt) :
    D.actU u x = D.unit_image u ⋆ x := rfl

/-- A product of units acts by the composite of the two actions. -/
lemma UnitPrimeModel.actU_mul {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u v : 𝒪ˣ) (x : Pt) :
    D.actU (u * v) x = D.actU u (D.actU v x) := by
  show D.unit_image (u * v) ⋆ x = D.unit_image u ⋆ (D.unit_image v ⋆ x)
  rw [D.unit_mul, mulC_assoc]

/-- On the index `(u, 0)` the family action is the unit action. -/
lemma UnitPrimeModel.family_act_zero {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (x : Pt) :
    D.family.act (u, 0) x = D.actU u x := by
  show D.unit_image u ⋆ powC (D.prime_image D.prime) 0 ⋆ x = D.unit_image u ⋆ x
  rw [powC_zero, mulC_oneC]

/-- The `n`-th iterate of the action of `ε` is the action of `ε ^ n`. -/
lemma UnitPrimeModel.actU_pow {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (ε : 𝒪ˣ) (n : ℕ) :
    ∀ x : Pt, D.actU (ε ^ n) x = (D.actU ε)^[n] x := by
  induction n with
  | zero =>
      intro x
      rw [pow_zero, Function.iterate_zero_apply]
      show D.unit_image 1 ⋆ x = x
      rw [D.unit_one, oneC_mulC]
  | succ n ih =>
      intro x
      rw [pow_succ, D.actU_mul, ih, Function.iterate_succ_apply]

/-- The unit multiplier is inverted by `unit_inv`. -/
lemma UnitPrimeModel.unit_inv_mul' {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) :
    D.unit_inv u ⋆ D.unit_image u = oneC := by
  rw [mulC_comm]; exact D.unit_inv_mul u

/-- The action of a unit is injective: `unit_inv u` inverts it. -/
lemma UnitPrimeModel.actU_injective {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) :
    Function.Injective (D.actU u) := by
  intro x y h
  have h' : D.unit_image u ⋆ x = D.unit_image u ⋆ y := h
  calc x = D.unit_inv u ⋆ (D.unit_image u ⋆ x) := by
        rw [← mulC_assoc, D.unit_inv_mul', oneC_mulC]
    _ = D.unit_inv u ⋆ (D.unit_image u ⋆ y) := by rw [h']
    _ = y := by rw [← mulC_assoc, D.unit_inv_mul', oneC_mulC]

/-- The action of a unit is continuous. -/
lemma UnitPrimeModel.continuous_actU {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) : Continuous (D.actU u) := by
  have h : (D.actU u : Pt → Pt) = fun x => D.unit_image u ⋆ x := rfl
  rw [h]
  exact continuous_mulC _

/-- The family action of `(u, j)` is continuous. -/
lemma UnitPrimeModel.continuous_family {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) :
    Continuous (D.family.act i) := by
  rcases i with ⟨u, j⟩
  have h : (D.family.act (u, j) : Pt → Pt) = fun x => D.mult u j ⋆ x := rfl
  rw [h]
  exact continuous_mulC _

/-- The multiplier of `(u, 0)` is the unit image. -/
lemma UnitPrimeModel.mult_zero {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) : D.mult u 0 = D.unit_image u := by
  show D.unit_image u ⋆ powC (D.prime_image D.prime) 0 = D.unit_image u
  rw [powC_zero, mulC_oneC]

/-- The prime image is inverted by `prime_inv`. -/
lemma UnitPrimeModel.prime_inv_mul' {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) :
    D.prime_inv ⋆ D.prime_image D.prime = oneC := by
  rw [mulC_comm]; exact D.prime_inv_mul

/-- The multiplier is a unit of the model algebra; its inverse is the recorded
`unit_inv u ⋆ prime_inv ^ j`. -/
lemma UnitPrimeModel.mult_inv {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) :
    D.unit_inv u ⋆ powC D.prime_inv j ⋆ (D.unit_image u ⋆ powC (D.prime_image D.prime) j) = oneC := by
  have h1 : D.unit_inv u ⋆ D.unit_image u = oneC := D.unit_inv_mul' u
  have h2 : powC D.prime_inv j ⋆ powC (D.prime_image D.prime) j = oneC := by
    rw [powC_mul_powC, D.prime_inv_mul', powC_oneC]
  rw [mulC_mul_mul_comm, h1, h2, mulC_oneC]

/-- The same identity in the other order. -/
lemma UnitPrimeModel.mult_mul_inv {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) :
    (D.unit_image u ⋆ powC (D.prime_image D.prime) j) ⋆ (D.unit_inv u ⋆ powC D.prime_inv j) = oneC := by
  rw [mulC_comm, D.mult_inv]

/-- The inverse multiplier undoes the multiplier. -/
lemma UnitPrimeModel.inv_mult_apply {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (x : Pt) :
    D.unit_inv u ⋆ powC D.prime_inv j ⋆
      ((D.unit_image u ⋆ powC (D.prime_image D.prime) j) ⋆ x) = x := by
  rw [← mulC_assoc, D.mult_inv, oneC_mulC]

/-- The multiplier undoes the inverse multiplier. -/
lemma UnitPrimeModel.mult_apply_inv {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (u : 𝒪ˣ) (j : ℕ) (x : Pt) :
    (D.unit_image u ⋆ powC (D.prime_image D.prime) j) ⋆
      (D.unit_inv u ⋆ powC D.prime_inv j ⋆ x) = x := by
  rw [← mulC_assoc, D.mult_mul_inv, oneC_mulC]

/-- The multiplier `σ(u π^j)`, as an invertible real-linear map of the model
space.  These are the linear maps whose characteristic polynomials are the ones
Berend's hypothesis (B1) refers to, and whose eigenvalues are the ones (B2)
refers to. -/
noncomputable def UnitPrimeModel.linFam {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) : Pt ≃ₗ[ℝ] Pt where
  toFun := fun x => D.mult i.1 i.2 ⋆ x
  invFun := fun x => D.unit_inv i.1 ⋆ powC D.prime_inv i.2 ⋆ x
  map_add' := fun x y => mulC_add _ x y
  map_smul' := fun c x => smul_mulC c _ x
  left_inv := fun x => D.inv_mult_apply i.1 i.2 x
  right_inv := fun x => D.mult_apply_inv i.1 i.2 x

/-- The linear map underlying `linFam` is the family action. -/
lemma UnitPrimeModel.linFam_coe {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) (x : Pt) :
    ((D.linFam i : Pt →ₗ[ℝ] Pt) : Pt → Pt) x = D.family.act i x := rfl

/-- Distinct indices give commuting endomorphisms: everything is a multiplier. -/
lemma UnitPrimeModel.linFam_comm {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (i i' : 𝒪ˣ × ℕ) (x : Pt) :
    D.linFam i (D.linFam i' x) = D.linFam i' (D.linFam i x) := by
  show D.mult i.1 i.2 ⋆ (D.mult i'.1 i'.2 ⋆ x) = D.mult i'.1 i'.2 ⋆ (D.mult i.1 i.2 ⋆ x)
  rw [← mulC_assoc, ← mulC_assoc, mulC_comm (D.mult i.1 i.2) (D.mult i'.1 i'.2)]

/-- The multipliers preserve the lattice. -/
lemma UnitPrimeModel.lattice_linFam {K : Type*} [Field K] {L : AddSubgroup Pt}
    {𝒪 : Subring K} (D : UnitPrimeModel L 𝒪) (i : 𝒪ˣ × ℕ) {g : Pt} (hg : g ∈ L) :
    D.linFam i g ∈ L := by
  show ((D.linFam i : Pt →ₗ[ℝ] Pt) : Pt → Pt) g ∈ L
  rw [D.linFam_coe]
  exact D.lattice i.1 i.2 g hg

/-! ### Lemma 3.7 and Lemma 3.8 -/

/-- **Lemma 3.8** (tower).  Let `π` and `m` be as in Lemma 3.7.  If
`|Nm(π^j y - (g + π^{-m}))| < |Nm π|^{-m}`, then `y` lies in a region with a centre
whose denominator has norm `|Nm π|^{m+j}`.

With `a = 1 + π^m g`, `s = m + j` and `x = a/π^s` one has
`|Nm(y - x)| < |Nm π|^{-s}`, and the `p`-adic hypothesis writes
`a = ε^k + π^s h`, so that `x = [h, π^s ε^{-k}]`.

Here `σ` is taken to be the `ℚ`-linear embedding in lattice coordinates, and `hy`
is stated in `K` rather than by multiplying coordinate vectors pointwise.  The
additional hypothesis `ε⁻¹ ∈ 𝒪` records that `ε` is a unit of `𝒪`. -/
theorem lem_tower (𝒪 : Subring K) [Algebra ℚ K] (Nm : AbsNorm K) (σ : K →ₗ[ℚ] Pt) (π ε : K) (m j : ℕ)
    (hπO : π ∈ 𝒪) (hπ0 : π ≠ 0) (hεO : ε ∈ 𝒪) (hεinv : ε⁻¹ ∈ 𝒪) (hεn : Nm ε = 1)
    (hN : ∀ a : K, ((Nm a : ℚ≥0) : ℝ) = |normR (σ a)|)
    (hpadic : ∀ a ∈ 𝒪, ∃ k : ℕ, ∃ h ∈ 𝒪, a - ε ^ k = π ^ (m + j) * h)
    {y : K} {g : K} (hg : g ∈ 𝒪)
    (hy : ((Nm (π ^ j * y - (g + (π ^ m)⁻¹)) : ℚ≥0) : ℝ) < (((Nm π : ℚ≥0)) : ℝ) ^ (-(m : ℤ))) :
    ∃ q1 ∈ 𝒪, ∃ q2 ∈ 𝒪, q2 ≠ 0 ∧
      |normR (σ y - σ (q1 + q2⁻¹))| < (((Nm q2 : ℚ≥0)) : ℝ)⁻¹ := by
  have hπpow : ∀ k : ℕ, π ^ k ∈ 𝒪 := fun k => pow_mem hπO k
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, map_zero] at hεn
    exact zero_ne_one hεn
  have hεinv0 : ε⁻¹ ≠ 0 := inv_ne_zero hε0
  have hp : 0 < (((Nm π : ℚ≥0)) : ℝ) := by
    have hn : Nm π ≠ 0 := (AbsNorm.ne_zero_iff Nm).mpr hπ0
    exact_mod_cast (zero_lt_iff.mpr hn)
  have hpj : 0 < (((Nm π : ℚ≥0)) : ℝ) ^ j := by positivity
  have ha : 1 + π ^ m * g ∈ 𝒪 := 𝒪.add_mem 𝒪.one_mem (𝒪.mul_mem (hπpow m) hg)
  obtain ⟨k, h, hh, hA⟩ := hpadic (1 + π ^ m * g) ha
  refine ⟨h, hh, π ^ (m + j) * (ε⁻¹) ^ k,
    𝒪.mul_mem (hπpow (m + j)) (pow_mem hεinv k), ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hεinv0)
  have hNq2 : Nm (π ^ (m + j) * (ε⁻¹) ^ k) = Nm π ^ (m + j) := by
    simp [map_mul, map_pow, hεn]
  have hcentre : h + (π ^ (m + j) * (ε⁻¹) ^ k)⁻¹ =
      (1 + π ^ m * g) / π ^ (m + j) := by
    have haEq : 1 + π ^ m * g = π ^ (m + j) * h + ε ^ k := sub_eq_iff_eq_add.mp hA
    rw [haEq, mul_inv, inv_pow, inv_inv]
    field_simp
  have hrad : (((Nm (π ^ (m + j) * (ε⁻¹) ^ k) : ℚ≥0)) : ℝ)⁻¹
      = ((Nm π : ℚ≥0) : ℝ) ^ (-(m : ℤ) - (j : ℤ)) := by
    rw [hNq2]
    norm_cast
    have hExp : (-((m+j:ℕ) : ℤ)) = (-(m:ℤ) - (j:ℤ)) := by
      push_cast
      ring
    rw [← hExp, zpow_neg, zpow_natCast]
  rw [← map_sub, hcentre, ← hN, hrad]
  have hMult : π ^ j * (y - (1 + π ^ m * g) / π ^ (m + j)) =
      π ^ j * y - (g + (π ^ m)⁻¹) := by
    field_simp
    ring
  have hMass : (((Nm π : ℚ≥0)) : ℝ) ^ j *
      ((Nm (y - (1 + π ^ m * g) / π ^ (m + j)) : ℚ≥0) : ℝ) <
        (((Nm π : ℚ≥0)) : ℝ) ^ (-(m : ℤ)) := by
    have hEq : ((Nm (π ^ j * (y - (1 + π ^ m * g) / π ^ (m + j))) : ℚ≥0) : ℝ) =
        (((Nm π : ℚ≥0)) : ℝ) ^ j *
          ((Nm (y - (1 + π ^ m * g) / π ^ (m + j)) : ℚ≥0) : ℝ) := by
      rw [map_mul, map_pow]
      norm_cast
    rw [← hEq, hMult]
    exact hy
  have hsplit := zpow_sub₀ hp.ne' (-(m : ℤ)) (j : ℤ)
  rw [hsplit]
  refine (lt_div_iff₀ hpj).mpr ?_
  rw [mul_comm]
  exact hMass


end CubicTwoStage
