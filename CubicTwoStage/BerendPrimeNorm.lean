/-
# Prime norm and coprime saturation in the ring of integers

If an algebraic integer `x` has prime absolute norm, it is prime in the ring of
integers (`prime_of_absNorm_eq_prime`).  For a different ordinary prime `q`,
the ideals `(x)` and `(q)` are comaximal.  Consequently, a field element `w`
is an algebraic integer as soon as `q*w` and `x*w` are both algebraic integers.
The proof is the elementary identity `w = a*(x*w) + b*(q*w)` coming from
`1 = a*x + b*q` in the ring of integers.
-/
import CubicTwoStage.Main
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Operations

open NumberField

set_option maxHeartbeats 1000000

namespace CubicTwoStage
namespace BerendPrimeNorm

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal norm of an algebraic integer agrees with its selected absolute
norm on the number field. -/
theorem absNorm_span_of_absNorm_eq {x : 𝓞 K} {p : ℕ}
    (hx : numberFieldAbsNorm K (x : K) = (p : ℚ≥0)) :
    Ideal.absNorm (Ideal.span ({x} : Set (𝓞 K))) = p := by
  rw [Ideal.absNorm_span_singleton]
  have hq : |Algebra.norm ℚ (x : K)| = (p : ℚ) := by
    have h := congrArg (fun r : ℚ≥0 => (r : ℚ)) hx
    change |Algebra.norm ℚ (x : K)| = (p : ℚ) at h
    exact h
  have hcast : ((Algebra.norm ℤ x).natAbs : ℚ) = (p : ℚ) := by
    calc
      ((Algebra.norm ℤ x).natAbs : ℚ) = |((Algebra.norm ℤ x : ℤ) : ℚ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |Algebra.norm ℚ (x : K)| := by rw [Algebra.coe_norm_int]
      _ = (p : ℚ) := hq
  exact_mod_cast hcast

/-- Prime absolute norm implies primality in the ring of integers. -/
theorem prime_of_absNorm_eq_prime {x : 𝓞 K} {p : ℕ} (hp : p.Prime)
    (hx : numberFieldAbsNorm K (x : K) = (p : ℚ≥0)) (hx0 : x ≠ 0) : Prime x := by
  apply Ideal.prime_of_irreducible_absNorm_span hx0
  rw [absNorm_span_of_absNorm_eq hx]
  exact hp

/-- For a different rational prime `q`, the ideals `(x)` and `(q)` are
comaximal whenever the absolute norm of `x` is `p`. -/
theorem coprime_ideals_of_absNorm_eq_prime {x : 𝓞 K} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : numberFieldAbsNorm K (x : K) = (p : ℚ≥0)) (hx0 : x ≠ 0) :
    Ideal.span ({x} : Set (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} = ⊤ := by
  have hprime : Prime x := prime_of_absNorm_eq_prime hp hx hx0
  have hprimeIdeal : (Ideal.span ({x} : Set (𝓞 K))).IsPrime :=
    (Ideal.span_singleton_prime hx0).mpr hprime
  have hmax : (Ideal.span ({x} : Set (𝓞 K))).IsMaximal :=
    hprimeIdeal.isMaximal (by simpa using hx0)
  by_contra hnot
  have heq : Ideal.span ({x} : Set (𝓞 K)) =
      Ideal.span ({x} : Set (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} :=
    hmax.eq_of_le hnot le_sup_left
  have hle : Ideal.span {(q : 𝓞 K)} ≤ Ideal.span ({x} : Set (𝓞 K)) := by
    rw [heq]
    exact le_sup_right
  have hmem : (q : 𝓞 K) ∈ Ideal.span ({x} : Set (𝓞 K)) :=
    hle (Ideal.mem_span_singleton_self (q : 𝓞 K))
  have hdvd := Ideal.absNorm_dvd_norm_of_mem hmem
  rw [absNorm_span_of_absNorm_eq hx, Algebra.norm_natCast] at hdvd
  have hdvd' : p ∣ q ^ Module.finrank ℤ (𝓞 K) := by
    exact_mod_cast hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd'))

/-- If `q` and `x` have distinct prime norm data, a field element already lies
in the ring of integers as soon as both `q*w` and `x*w` lie there. -/
theorem mem_numberFieldO_of_coprime {x : 𝓞 K} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : numberFieldAbsNorm K (x : K) = (p : ℚ≥0)) (hx0 : x ≠ 0)
    {w : K} (hqw : IsIntegral ℤ ((q : K) * w))
    (hxw : IsIntegral ℤ ((x : K) * w)) : IsIntegral ℤ w := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp
    (Ideal.isCoprime_iff_sup_eq.mpr (coprime_ideals_of_absNorm_eq_prime hp hq hpq hx hx0))
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton.mp ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.mp hb
  let aa : 𝓞 K := ⟨(q : K) * w, hqw⟩
  let bb : 𝓞 K := ⟨(x : K) * w, hxw⟩
  let z : 𝓞 K := a' * bb + b' * aa
  have habK := congrArg (fun z : 𝓞 K => (z : K)) hab
  push_cast at habK
  have hz : w = (z : K) := by
    dsimp [z, aa, bb]
    change w = (a' : K) * ((x : K) * w) + (b' : K) * ((q : K) * w)
    calc
      w = 1 * w := (one_mul w).symm
      _ = ((x : K) * (a' : K) + (q : K) * (b' : K)) * w := by rw [habK]
      _ = (a' : K) * ((x : K) * w) + (b' : K) * ((q : K) * w) := by ring
  exact hz ▸ z.2

end BerendPrimeNorm
end CubicTwoStage

#print axioms CubicTwoStage.BerendPrimeNorm.absNorm_span_of_absNorm_eq
#print axioms CubicTwoStage.BerendPrimeNorm.prime_of_absNorm_eq_prime
#print axioms CubicTwoStage.BerendPrimeNorm.coprime_ideals_of_absNorm_eq_prime
#print axioms CubicTwoStage.BerendPrimeNorm.mem_numberFieldO_of_coprime
