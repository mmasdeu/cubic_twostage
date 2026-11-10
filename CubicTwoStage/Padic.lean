import CubicTwoStage.Basic

/-!
## Unit powers modulo an odd prime power

The group-theoretic content of Lemma 3.7: congruence classes congruent to `1`
modulo `p^m` are powers of a given generator whose first non-unit coefficient
is not divisible by `p`.  The proof uses cardinalities of kernels of units maps
and `ZMod.orderOf_one_add_mul_prime_pow`.
-/

namespace CubicTwoStage


theorem zmod_exists_pow_of_modEq_one (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (m n : ℕ) (hm : 0 < m) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u)
    (v : (ZMod (p ^ (n + m)))ˣ) (hvval : (v : ZMod (p ^ (n + m))) = 1 + p ^ m * u)
    (A : (ZMod (p ^ (n + m)))ˣ)
    (hker : (ZMod.unitsMap (pow_dvd_pow p (by omega : m ≤ n + m))) A = 1) :
    ∃ k : ℕ, A = v ^ k := by
  classical
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (n + m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f : (ZMod (p ^ (n + m)))ˣ →* (ZMod (p ^ m))ˣ :=
    ZMod.unitsMap (pow_dvd_pow p (by omega : m ≤ n + m))
  let H := f.ker
  have hvH : v ∈ H := by
    change f v = 1
    apply Units.ext
    change (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ n + m)) (ZMod (p ^ m))) (v : ZMod (p ^ (n + m))) = 1
    rw [hvval, ZMod.castHom_apply, ZMod.cast_add, ZMod.cast_mul, ZMod.cast_one,
      ZMod.cast_pow, ZMod.cast_natCast (pow_dvd_pow p (by omega : m ≤ n + m)), ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
    all_goals exact pow_dvd_pow _ (by omega)
  haveI : NeZero (p ^ (n + m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hRange : f.range = ⊤ := by
    haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact MonoidHom.range_eq_top.mpr
      (ZMod.unitsMap_surjective (pow_dvd_pow p (by omega : m ≤ n + m)))
  have hIndex : H.index = (p ^ m).totient := by
    rw [Subgroup.index_ker, hRange, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hmul : Nat.card H * (p ^ m).totient = (p ^ (n + m)).totient := by
    have hcard := H.card_mul_index
    rw [hIndex] at hcard
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using hcard
  have hcard : Nat.card H = p ^ n := by
    have hpPow : p ^ (n + m - 1) = p ^ n * p ^ (m - 1) := by
      rw [← pow_add, Nat.add_sub_assoc hm]
    rw [Nat.totient_prime_pow hp (n := n + m) (by omega),
      Nat.totient_prime_pow hp (n := m) hm, hpPow] at hmul
    have hm0 : 0 < p ^ (m - 1) * (p - 1) := Nat.mul_pos (pow_pos hp.pos _) (Nat.sub_pos_of_lt hp.two_le)
    apply Nat.mul_right_cancel hm0
    simpa [mul_assoc] using hmul
  have horder : orderOf (⟨v, hvH⟩ : H) = p ^ n := by
    rw [Subgroup.orderOf_mk]
    rw [← orderOf_injective (Units.coeHom (ZMod (p ^ (n + m)))) Units.coeHom_injective v]
    rw [Units.coeHom_apply, hvval]
    have hpge2 := hp.two_le
    exact ZMod.orderOf_one_add_mul_prime_pow hp m (by omega) (by
      have hp2 : p ≠ 2 := hpodd
      have hp3 : 3 ≤ p := by omega
      nlinarith) u hu n
  have hpows : (Subgroup.zpowers (⟨v, hvH⟩ : H)) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    rw [Nat.card_zpowers, horder, hcard]
  have hmem : A ∈ H := hker
  have hpA : (⟨A, hker⟩ : H) ∈ Subgroup.zpowers (⟨v, hvH⟩ : H) := by
    rw [hpows]
    trivial
  rw [mem_zpowers_iff_mem_range_orderOf] at hpA
  obtain ⟨i, hi, hval⟩ := Finset.mem_image.mp hpA
  exact ⟨i, congrArg Subtype.val hval.symm⟩


/-- In `ZMod (p^s)`, `1 + p^m v` is a unit as soon as `m ≥ 1`: `p^m v` is
nilpotent. -/
lemma zmod_unit_one_add_pow (p s m : ℕ) (hm : 1 ≤ m) (_hms : m ≤ s) (v : ℤ) :
    IsUnit ((1 + (p : ZMod (p ^ s)) ^ m * (v : ZMod (p ^ s))) : ZMod (p ^ s)) := by
  have hnil : IsNilpotent ((p : ZMod (p ^ s)) ^ m * (v : ZMod (p ^ s))) := by
    refine ⟨s, ?_⟩
    rw [mul_pow]
    have hp : ((p : ZMod (p ^ s)) ^ m) ^ s = 0 := by
      rw [← pow_mul, ← Nat.cast_pow]
      obtain ⟨k, hk⟩ := pow_dvd_pow (p) (m := s) (n := m * s) (by nlinarith)
      rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [hp, zero_mul]
  simpa using hnil.isUnit_one_add

variable {K : Type*} [Field K]

/-- **Lemma 3.7** (`p`-adic approximation by powers of a unit), in its local
residue-isomorphism formulation.

Let `p` be odd, let `e` be the degree-one residue isomorphism modulo `π^(n+m)`,
and suppose the residue of `ε^(p-1)` has the proper primitive form
`1 + p^m * u` with `p ∤ u`.  If `a` has residue `1 + p^m * v` alongside being a
unit modulo `π^(n+m)`, then `a` is congruent to a nonnegative power of `ε` modulo
`π^(n+m)`.  The exponent is `(p-1)k`, where `k` comes from the cyclic subgroup
of appropriate prime-power order.

This version makes explicit the residue isomorphism and generator condition
used by the number-theoretic proof.  The earlier formulation of the minimal-
divisibility condition was incorrect, since it would have forced `m = 0`. -/
theorem lem_padic (𝒪 : Subring K) (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (n m : ℕ)
    (hm : 0 < m) (π : 𝒪) (ε : 𝒪ˣ) (a : 𝒪)
    (e : (𝒪 ⧸ Ideal.span {π ^ (n + m)}) ≃+* ZMod (p ^ (n + m)))
    (he : ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ e (Ideal.Quotient.mk _ ((ε : 𝒪) ^ (p - 1))) =
      (1 + (p : ZMod (p ^ (n + m))) ^ m * u))
    (ha : ∃ v : ℤ, e (Ideal.Quotient.mk _ a) =
      (1 + (p : ZMod (p ^ (n + m))) ^ m * v))
    (haU : IsUnit (e (Ideal.Quotient.mk _ a))) :
    ∃ k : ℕ, ∃ h : 𝒪, a - ε ^ k = π ^ (n + m) * h := by
  classical
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let v0 : (ZMod (p ^ (n + m)))ˣ :=
    Units.mapEquiv e.toMulEquiv (Units.map (Ideal.Quotient.mk _).toMonoidHom (ε ^ (p - 1)))
  obtain ⟨u, hu, heU⟩ := he
  obtain ⟨v, hv⟩ := ha
  have hvval : (v0 : ZMod (p ^ (n + m))) = 1 + (p : ZMod (p ^ (n + m))) ^ m * u := by
    dsimp [v0]
    simpa only [map_pow] using heU
  let A : (ZMod (p ^ (n + m)))ˣ := haU.unit
  obtain ⟨k, hk⟩ := zmod_exists_pow_of_modEq_one p hp hpodd m n hm u hu v0 hvval A
    (by
      apply Units.ext
      change (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ n + m)) (ZMod (p ^ m))) (e (Ideal.Quotient.mk _ a)) = 1
      rw [hv, ZMod.castHom_apply, ZMod.cast_add, ZMod.cast_mul, ZMod.cast_one,
        ZMod.cast_pow, ZMod.cast_natCast (pow_dvd_pow p (by omega : m ≤ n + m)),
        ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
      all_goals exact pow_dvd_pow _ (by omega))
  refine ⟨(p - 1) * k, ?_⟩
  apply (Ideal.mem_span_singleton (y := π ^ (n + m))).mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  apply e.injective
  calc
    _ = (A : ZMod (p ^ (n + m))) := IsUnit.unit_spec haU
    _ = (v0 ^ k : (ZMod (p ^ (n + m)))ˣ) := congrArg Units.val hk
    _ = (v0 : ZMod (p ^ (n + m))) ^ k := rfl
    _ = e (Ideal.Quotient.mk _ ((ε : 𝒪) ^ ((p - 1) * k))) := by
      dsimp [v0]
      simp only [map_pow, pow_mul]

