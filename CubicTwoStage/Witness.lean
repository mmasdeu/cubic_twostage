/-
Section 6 of the paper: exact obstructions — Proposition 6.2 (witnesses) and
Proposition 6.3 (lower bounds for the smooth level).
-/
import CubicTwoStage.Basic
import CubicTwoStage.Setting
import CubicTwoStage.Normalize

set_option linter.unusedVariables false

namespace CubicTwoStage

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `f(x) = min_{g ∈ 𝒪} |Nm(x - g)|`, the quantity of §6.  The values are shown
in `ℝ`, with bounded lattice indexed by `𝒪`.  The minimum exists in the intended
setting because the values lie in `m^{-n}ℤ` when `mx ∈ 𝒪`. -/
noncomputable def fmin (𝒪 : Subring K) (Nm : AbsNorm K) (x : K) : ℝ :=
  ⨅ g : 𝒪, ((Nm (x - (g : K)) : ℚ≥0) : ℝ)

/-- A **witness**: a point `x ∈ K` with `f(x) ≥ 1`, i.e. lying in no region with
unit denominator. -/
def IsWitness (𝒪 : Subring K) (Nm : AbsNorm K) (x : K) : Prop := 1 ≤ fmin 𝒪 Nm x

/-- **Proposition 6.2** (witness criterion).

Let `x = a/m`.  The finite set `orb` contains representatives modulo `m` of the
orbit of `a` under multiplication by `±ε`; `orbCube` says they are precisely the
residue representatives in `[0,m)³`.  For a finite list of candidate lattice
translations `lattice d`, the statement uses the **orbit** value `b`, not `a`.

`hDmem` describes the candidates coming from a normalization box `B`, and the
threshold is `m³`, exactly as in the paper.  The normalization supplied by
Lemma 6.1 is the hypothesis `hB`, surjectivity of the integral coordinates is
`hlatticeSurj`, and `hdeg` is the cubic scaling `Nm(m : K) = m³`. -/
theorem prop_witness (𝒪 : Subring K) [CharZero K] (Nm : AbsNorm K) (σ : K →ₗ[ℚ] Pt)
    (m : ℕ) (hm : 0 < m) (a ε : K) (ha : a ∈ 𝒪) (hε : ε ∈ 𝒪)
    (hεinv : ε⁻¹ ∈ 𝒪) (hεnorm : Nm ε = 1)
    (D : Finset (Fin 3 → ℤ)) (orb : Finset K) (lattice : (Fin 3 → ℤ) → K)
    (hlattice : ∀ d, lattice d ∈ 𝒪)
    (hlatticeSurj : ∀ t ∈ 𝒪, ∃ d : Fin 3 → ℤ, lattice d = t)
    (hdeg : ∀ c : ℕ, Nm (c : K) = (c : ℚ≥0) ^ 3) (B : Set Pt)
    (hDmem : ∀ d : Fin 3 → ℤ, d ∈ D ↔
      ∃ y ∈ B, |normR y| < 1 ∧ ∃ b ∈ orb, y = σ (b / (m : K) - lattice d))
    (horb : ∀ b : K, b ∈ orb ↔
      (∃ k : ℤ, ∃ h ∈ 𝒪, b = ε ^ k * a + (m : K) * h) ∨
      (∃ k : ℤ, ∃ h ∈ 𝒪, b = -(ε ^ k * a) + (m : K) * h))
    (horbCube : ∀ b ∈ orb, σ (b / (m : K)) ∈ unitCube)
    (hB : ∀ g ∈ 𝒪, ((Nm (a / (m : K) - g) : ℚ≥0) : ℝ) < 1 →
      ∃ k : ℤ, σ (ε ^ k * (a / (m : K) - g)) ∈ B)
    (hN : ∀ z : K, ((Nm z : ℚ≥0) : ℝ) = |normR (σ z)|) :
    1 ≤ fmin 𝒪 Nm (a / (m : K)) ↔
      ∀ d ∈ D, ∀ b ∈ orb, (m : ℝ) ^ 3 ≤
        ((Nm (b - (m : K) * lattice d) : ℚ≥0) : ℝ) := by
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, map_zero] at hεnorm
    exact zero_ne_one hεnorm
  have hEpZ : ∀ k : ℤ, (ε ^ k : K) ∈ 𝒪 := by
    intro k
    cases k with
    | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem hε n
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow]
      exact pow_mem hεinv (n + 1)
  have hEpOne : ∀ k : ℤ, ε ^ k * ε ^ (-k) = 1 := by
    intro k
    rw [← zpow_add₀ hε0, add_neg_cancel, zpow_zero]
  have hEpNorm : ∀ k : ℤ, Nm (ε ^ k : K) = 1 := by
    intro k
    rw [map_zpow₀, hεnorm, one_zpow]
  have hbdd : BddBelow (Set.range (fun g : 𝒪 =>
      ((Nm (a / (m : K) - (g : K)) : ℚ≥0) : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, rfl⟩
    positivity
  have hmR : 0 < (m : ℝ) ^ 3 := by positivity
  constructor
  · intro hlow d hd b hb
    obtain (⟨k, h, ih, hrel⟩ | ⟨k, h, ih, hrel⟩) := (horb b).mp hb
    · let g : K := -(ε ^ (-k) * (h - lattice d))
      have hgm : g ∈ 𝒪 := 𝒪.neg_mem (𝒪.mul_mem (hEpZ (-k)) (𝒪.sub_mem ih (hlattice d)))
      have hcalc : b / (m : K) - lattice d = ε ^ k * (a / (m : K) - g) := by
        dsimp [g]
        rw [hrel, zpow_neg]
        field_simp
        ring
      have hnorm : ((Nm (b / (m : K) - lattice d) : ℚ≥0) : ℝ) =
          ((Nm (a / (m : K) - g) : ℚ≥0) : ℝ) := by
        rw [hcalc, map_mul, map_zpow₀, hεnorm, one_zpow, one_mul]
      have hnorm' : ((Nm (b - (m : K) * lattice d) : ℚ≥0) : ℝ) =
          (m : ℝ) ^ 3 * ((Nm (b / (m : K) - lattice d) : ℚ≥0) : ℝ) := by
        have hi : b - (m : K) * lattice d = (m : K) * (b / (m : K) - lattice d) := by
          field_simp
        rw [hi, map_mul, hdeg m]
        norm_cast
      by_contra hnot
      have hsmall := lt_of_not_ge hnot
      rw [hnorm'] at hsmall
      have hgt := (le_ciInf_iff hbdd).mp hlow ⟨g, hgm⟩
      rw [← hnorm] at hgt
      nlinarith
    · let g : K := ε ^ (-k) * (h - lattice d)
      have hgm : g ∈ 𝒪 := 𝒪.mul_mem (hEpZ (-k)) (𝒪.sub_mem ih (hlattice d))
      have hcalc : b / (m : K) - lattice d = -ε ^ k * (a / (m : K) - g) := by
        dsimp [g]
        rw [hrel, zpow_neg]
        field_simp
        ring
      have hnorm : ((Nm (b / (m : K) - lattice d) : ℚ≥0) : ℝ) =
          ((Nm (a / (m : K) - g) : ℚ≥0) : ℝ) := by
        rw [hcalc, map_mul, AbsNorm.abs_neg, map_zpow₀, hεnorm, one_zpow, one_mul]
      have hnorm' : ((Nm (b - (m : K) * lattice d) : ℚ≥0) : ℝ) =
          (m : ℝ) ^ 3 * ((Nm (b / (m : K) - lattice d) : ℚ≥0) : ℝ) := by
        have hi : b - (m : K) * lattice d = (m : K) * (b / (m : K) - lattice d) := by
          field_simp
        rw [hi, map_mul, hdeg m]
        norm_cast
      by_contra hnot
      have hsmall := lt_of_not_ge hnot
      rw [hnorm'] at hsmall
      have hgt := (le_ciInf_iff hbdd).mp hlow ⟨g, hgm⟩
      rw [← hnorm] at hgt
      nlinarith
  · intro htest
    refine (le_ciInf_iff hbdd).mpr (fun g => ?_)
    by_contra hnot
    have hlow : ((Nm (a / (m : K) - g) : ℚ≥0) : ℝ) < 1 := lt_of_not_ge hnot
    obtain ⟨k, hBmem⟩ := hB (g : K) g.2 hlow
    obtain ⟨d, hd_eq⟩ := hlatticeSurj (ε ^ k * g) (𝒪.mul_mem (hEpZ k) g.2)
    let b : K := ε ^ k * a
    have hb : b ∈ orb := (horb b).mpr (Or.inl ⟨k, 0, 𝒪.zero_mem, by simp [b]⟩)
    have hcalc : b / (m : K) - lattice d = ε ^ k * (a / (m : K) - g) := by
      dsimp [b]
      rw [hd_eq]
      field_simp
    have hyN : |normR (σ (ε ^ k * (a / (m : K) - g)))| < 1 := by
      rw [← hN, map_mul, map_zpow₀, hεnorm, one_zpow, one_mul]
      exact hlow
    have hd : d ∈ D := by
      refine (hDmem d).mpr ⟨σ (ε ^ k * (a / (m : K) - g)), hBmem, hyN, b, hb, ?_⟩
      rw [hcalc]
    have hsmall := htest d hd b hb
    have hnorm' : ((Nm (b - (m : K) * lattice d) : ℚ≥0) : ℝ) =
        (m : ℝ) ^ 3 * ((Nm (b / (m : K) - lattice d) : ℚ≥0) : ℝ) := by
      have hi : b - (m : K) * lattice d = (m : K) * (b / (m : K) - lattice d) := by
        field_simp
      rw [hi, map_mul, hdeg m]
      norm_cast
    rw [hnorm', hcalc, map_mul, map_zpow₀, hεnorm, one_zpow, one_mul] at hsmall
    have hmPos : 0 < (m : ℝ) ^ 3 := by positivity
    nlinarith


/-- The single-centre equivalence behind Proposition 6.3: if `x - c = b/(m n)`,
then `f(b/(m n)) ≥ 1/n` is exactly the assertion that no translate of `c` covers
`x`. -/
theorem level_core (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K →ₗ[ℚ] Pt)
    (hN : ∀ z : K, ((Nm z : ℚ≥0) : ℝ) = |normR (σ z)|)
    (m n : ℕ) (x c b : K) (hxc : x - c = b / ((m * n : ℕ) : K)) :
    (1 / ((n : ℝ))) ≤ fmin 𝒪 Nm (b / ((m * n : ℕ) : K)) ↔
      ∀ g ∈ 𝒪, ¬ |normR (σ x - σ (c + g))| < ((n : ℝ))⁻¹ := by
  have hbdd : BddBelow (Set.range (fun g : 𝒪 =>
      ((Nm (b / ((m * n : ℕ) : K) - (g : K)) : ℚ≥0) : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, rfl⟩
    positivity
  have heq : ∀ g : K, ((Nm (b / ((m * n : ℕ) : K) - g) : ℚ≥0) : ℝ) =
      |normR (σ x - σ (c + g))| := by
    intro g
    calc
      ((Nm (b / ((m * n : ℕ) : K) - g) : ℚ≥0) : ℝ) = |normR (σ (x - c - g))| := by
        rw [← hxc, hN]
      _ = |normR (σ x - σ (c + g))| := by
        congr 1
        simp only [map_sub, map_add]
        abel
  constructor
  · intro hf g hg
    rw [← heq g, not_lt]
    simpa [one_div] using (le_ciInf_iff hbdd).mp hf ⟨g, hg⟩
  · intro hh
    refine (le_ciInf_iff hbdd).mpr (fun g => ?_)
    rw [heq g]
    simpa [one_div] using (not_lt.mp (hh g g.2))

/-- **Proposition 6.3** (lower bound for the smooth level).

For every centre `q₁ + 1/q₂` with `|Nm q₂| ≤ L`, `hL` supplies the integral
norm `n` and the point `b` of the paper for which `x - c = b/(m n)`, together with
the obstruction `f(b/(m n)) ≥ 1/n`.  Hence no such centre covers `x`.  Since `x`
is represented in `unitCube` (`hxCube`), it follows that no level `M ≤ L` is
smooth.  Equivalently, the smooth level is strictly greater than `L`. -/
theorem prop_level (𝒪 : Subring K) (Nm : AbsNorm K) (σ : K →ₗ[ℚ] Pt)
    (m L : ℕ) (a : K)
    (hN : ∀ z : K, ((Nm z : ℚ≥0) : ℝ) = |normR (σ z)|)
    (hxCube : σ (a / (m : K)) ∈ unitCube)
    (hL : ∀ q1 ∈ 𝒪, ∀ q2 ∈ 𝒪, q2 ≠ 0 → Nm q2 ≤ (L : ℚ≥0) →
      ∃ n : ℕ, ∃ b : K, 0 < n ∧
        a / (m : K) - (q1 + q2⁻¹) = b / ((m * n : ℕ) : K) ∧
        Nm q2 = (n : ℚ≥0) ∧ (1 / (n : ℝ)) ≤ fmin 𝒪 Nm (b / ((m * n : ℕ) : K))) :
    ∀ M : ℕ, IsNSmoothEuclidean 𝒪 Nm σ M → L < M := by
  intro M hSmooth
  by_contra hn
  have hML : M ≤ L := by omega
  obtain ⟨q1, hq1, q2, hq2, hq2ne, hq2le, hbound⟩ := hSmooth _ hxCube
  obtain ⟨n, b, hn, hxc, hnorm, hlevel⟩ := hL q1 hq1 q2 hq2 hq2ne
    (le_trans hq2le (by exact_mod_cast hML))
  have hno := (level_core 𝒪 Nm σ hN m n (a / (m : K)) (q1 + q2⁻¹) b hxc).mp
    (by simpa [hnorm] using hlevel)
  exact hno 0 𝒪.zero_mem (by simpa [hnorm] using hbound)

end CubicTwoStage
