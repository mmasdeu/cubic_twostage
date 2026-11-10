/-
# Integral functionals on closed subgroups of a real vector space

The Stage-I modules of the Berend development take, as their only unproduced
hypothesis, the *density* of a coordinate subspace modulo the lattice,

  `Dense ((coord S : Set (ι → ℝ)) + (L : Set (ι → ℝ)))`,

and record in their docstrings that this is equivalent to the statement that no
nonzero *character* of the torus annihilates the coordinate subspace
(`BerendStageILine`, "the remaining input, precisely"), and that the general
codimension `≥ 2` criterion "needs the structure theory of closed subgroups of
`ℝ ^ d` ... and is not proved here" (`BerendTorusLastMile`).

This file supplies that structure theory in the minimal form needed:
every closed proper subgroup `H` of a finite-dimensional real normed space
carries a nonzero linear functional that is `ℤ`-valued on `H`.  The proof
reduces to the discrete case, where a greedy minimal-norm argument produces
the functional, and the discrete case is the content of
`exists_integral_functional_of_discrete`.

Axiom free: imports only `Mathlib`.
-/
/-
# Integral functionals on closed subgroups of a real vector space

The Stage-I modules of the Berend development take, as their only unproduced
hypothesis, the *density* of a coordinate subspace modulo the lattice,

  `Dense ((coord S : Set (ι → ℝ)) + (L : Set (ι → ℝ)))`,

and their docstrings record that this is equivalent to the statement that no
nonzero *character* of the torus annihilates the coordinate subspace
(`BerendStageILine`, "the remaining input, precisely"), and that the general
codimension `≥ 2` criterion "needs the structure theory of closed subgroups of
`ℝ ^ d` ... and is not proved here" (`BerendTorusLastMile`).

This file supplies the two halves of that structure theory which are needed and
which do not depend on the arithmetic of the field:

* **the discrete case** (`exists_integral_functional_of_discrete`,
  `exists_integral_functional_of_discrete'`): a closed discrete subgroup
  spanning a finite-dimensional real normed space carries a nonzero linear
  functional with integer values on it.  The proof is a minimal-norm induction:
  a shortest nonzero element `d₀` gives a hyperplane `ker ψ` with `ψ d₀ = 1`,
  and rounding the `ψ`-coordinate against `d₀` shows that the image of the
  subgroup in that hyperplane again has an isolated zero and lower dimension.

* **the existence of a line** (`exists_line_of_not_isolatedZero`): a closed
  subgroup with no isolated zero contains a whole line `ℝ • u`.  The proof is
  the classical floor argument: accumulate `h n → 0`, pass to a subsequence of
  `‖h n‖⁻¹ • h n` on the unit sphere, and recover `t • u` as the limit of
  `⌊t / ‖h n‖⌋ • h n`.

Together these reduce the separation theorem for an *arbitrary* closed proper
subgroup (needed for the character criterion above) to one quotient step, which
is stated at the end of the file as the remaining deficit.  Everything else of
the reduction is proved, and every declaration depends only on `propext`,
`Classical.choice` and `Quot.sound` (see the audit at the end).
-/ 
import Mathlib

noncomputable section
open Set Filter Topology Module
open Set Filter Topology Module

namespace BerendCoordDense

variable {E : Type*}

/-! ## 1. Isolated zero and closedness -/

section Isolated

variable [NormedAddCommGroup E]

/-- `0` is an isolated point of the additive subgroup `D`.  For a subgroup of a
normed group this is the same as `DiscreteTopology D`, but it is the form in
which the arguments below consume discreteness. -/
def IsolatedZero (D : AddSubgroup E) : Prop :=
  ∃ ε > 0, ∀ d ∈ D, ‖d‖ < ε → d = 0

/-- A subgroup with an isolated zero is discrete. -/
theorem isolatedZero_of_discreteTopology (D : AddSubgroup E) [DiscreteTopology D] :
    IsolatedZero D := by
  have hopen : IsOpen ({0} : Set D) := isOpen_discrete {0}
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hsub⟩ := hopen 0 (mem_singleton 0)
  refine ⟨ε, hε, fun d hd hlt => ?_⟩
  have hmem : (⟨d, hd⟩ : D) ∈ Metric.ball (0 : D) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hlt
  have := hsub hmem
  simpa using this

/-- A subgroup with an isolated zero is closed: a sequence in it that converges
is eventually constant. -/
theorem isClosed_of_isolatedZero {D : AddSubgroup E} (h : IsolatedZero D) :
    IsClosed (D : Set E) := by
  obtain ⟨ε, hε, hiso⟩ := h
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff] at hx
  have hseq : ∀ n : ℕ, ∃ d ∈ D, ‖x - d‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hyb, hyD⟩ := hx (Metric.ball x (1 / ((n : ℝ) + 1)))
      Metric.isOpen_ball (Metric.mem_ball_self hpos)
    refine ⟨y, hyD, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hyb
    exact hyb
  choose d hd hdist using hseq
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hconst : ∀ m n : ℕ, N ≤ m → N ≤ n → d m = d n := by
    intro m n hm hn
    have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hn' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : ‖x - d m‖ < 1 / ((N : ℝ) + 1) :=
      lt_of_lt_of_le (hdist m) (by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith)
    have h2 : ‖x - d n‖ < 1 / ((N : ℝ) + 1) :=
      lt_of_lt_of_le (hdist n) (by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
    have hsmall : ‖d m - d n‖ < ε := by
      have h3 : ‖d m - d n‖ ≤ ‖x - d m‖ + ‖x - d n‖ := by
        have := dist_triangle (d m) x (d n)
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (d m) x] at this
        exact this
      have h4 : 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) < ε := by
        have h2e : 2 / ε < (N : ℝ) := hN
        rw [div_lt_iff₀ hε] at h2e
        have hsum : 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) = 2 / ((N : ℝ) + 1) := by
          field_simp
          norm_num
        rw [hsum, div_lt_iff₀ (by positivity : (0:ℝ) < (N:ℝ) + 1)]
        nlinarith
      linarith
    exact sub_eq_zero.mp (hiso (d m - d n) (D.sub_mem (hd m) (hd n)) hsmall)
  have hxdN : ‖x - d N‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
    have hstep : ‖x - d N‖ < 1 / ((N : ℝ) + (k : ℝ) + 1) := by
      have heq : d (N + k) = d N := hconst (N + k) N (Nat.le_add_right N k) le_rfl
      rw [← heq]
      have hcast : ((N + k : ℕ) : ℝ) + 1 = (N : ℝ) + (k : ℝ) + 1 := by
        push_cast
        ring
      calc ‖x - d (N + k)‖ < 1 / (((N + k : ℕ) : ℝ) + 1) := hdist (N + k)
        _ = 1 / ((N : ℝ) + (k : ℝ) + 1) := by rw [hcast]
    have hk' : 1 / δ < (k : ℝ) + 1 := by linarith
    have hsmall : 1 / ((N : ℝ) + (k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
      have hle : (k : ℝ) + 1 ≤ (N : ℝ) + (k : ℝ) + 1 := by
        have hNk : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      exact one_div_le_one_div_of_le hk1 hle
    have hfin : 1 / ((k : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (k:ℝ) + 1)]
      have : 1 < δ * ((k : ℝ) + 1) := by
        rw [div_lt_iff₀ hδ] at hk'
        linarith
      linarith
    linarith
  have hxD : x - d N = 0 := norm_eq_zero.mp hxdN
  have : x = d N := sub_eq_zero.mp hxD
  rw [this]
  exact hd N

/-- **Minimal-norm element** of a closed subgroup with an isolated zero. -/
theorem exists_min_norm [NormedSpace ℝ E] [FiniteDimensional ℝ E] {D : AddSubgroup E}
    (hcl : IsClosed (D : Set E)) (hiso : IsolatedZero D) (hne : D ≠ ⊥) :
    ∃ d ∈ D, d ≠ 0 ∧ ∀ d' ∈ D, d' ≠ 0 → ‖d‖ ≤ ‖d'‖ := by
  obtain ⟨ε, hε, hiso'⟩ := hiso
  have hne' : ∃ d ∈ D, d ≠ 0 := by
    by_contra h
    push_neg at h
    refine hne ?_
    rw [eq_bot_iff]
    intro x hx
    simpa using h x hx
  obtain ⟨d₁, hd₁, hd₁ne⟩ := hne'
  have hM : ε ≤ ‖d₁‖ := by
    by_contra hlt
    push_neg at hlt
    exact hd₁ne (hiso' d₁ hd₁ hlt)
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  have hcomp : IsCompact (Metric.closedBall (0 : E) ‖d₁‖ ∩ {x : E | ε / 2 ≤ ‖x‖}) :=
    (isCompact_closedBall (0 : E) ‖d₁‖).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hKcomp : IsCompact ((D : Set E) ∩ (Metric.closedBall (0 : E) ‖d₁‖ ∩ {x : E | ε / 2 ≤ ‖x‖})) :=
    hcomp.inter_left hcl
  have hKne : ((D : Set E) ∩ (Metric.closedBall (0 : E) ‖d₁‖ ∩ {x : E | ε / 2 ≤ ‖x‖})).Nonempty := by
    refine ⟨d₁, hd₁, ?_, ?_⟩
    · simp [Metric.mem_closedBall]
    · simp only [mem_ofPred_eq]; linarith
  obtain ⟨x, hx, hmin⟩ := hKcomp.exists_isMinOn hKne continuous_norm.continuousOn
  refine ⟨x, hx.1, ?_, ?_⟩
  · rintro rfl
    have hle := hx.2.2
    simp only [mem_ofPred_eq, norm_zero] at hle
    linarith
  · intro d' hd' hd'ne
    have hx1 : ‖x‖ ≤ ‖d₁‖ := by simpa [Metric.mem_closedBall] using hx.2.1
    rcases le_total ‖d'‖ ‖d₁‖ with h | h
    · refine hmin ⟨hd', by simpa [Metric.mem_closedBall] using h, ?_⟩
      simp only [mem_ofPred_eq]
      have hge : ε ≤ ‖d'‖ := by
        by_contra hlt
        push_neg at hlt
        exact hd'ne (hiso' d' hd' hlt)
      linarith
    · exact le_trans hx1 h

end Isolated


/-! ## 2. The discrete case: a `ℤ`-valued functional on a discrete full lattice -/

section Discrete

universe u

/-- A rounding step: every real `c` is within `1/2` of an integer. -/
theorem exists_int_close (c : ℝ) : ∃ k : ℤ, |c - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊c + 1 / 2⌋, ?_⟩
  have h1 : ((⌊c + 1 / 2⌋ : ℤ) : ℝ) ≤ c + 1 / 2 := Int.floor_le _
  have h2 : c + 1 / 2 < ((⌊c + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- **The discrete case, by induction on the dimension.**  A closed discrete
subgroup whose `ℝ`-span is a finite-dimensional real normed space carries a
nonzero linear functional with integer values on it. -/
theorem exists_integral_functional_of_discrete_aux :
    ∀ (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ (D : AddSubgroup E), IsolatedZero D →
        Submodule.span ℝ (D : Set E) = ⊤ → D ≠ ⊥ →
        ∃ μ : E →ₗ[ℝ] ℝ, μ ≠ 0 ∧ ∀ d ∈ D, ∃ m : ℤ, μ d = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hn D hiso hspan hne
    classical
    obtain ⟨d₀, hd₀D, hd₀ne, hmin⟩ :=
      exists_min_norm (isClosed_of_isolatedZero hiso) hiso hne
    set i : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E d₀ with hi_def
    have hi_inj : Function.Injective i := by
      intro a b hab
      simp only [hi_def, LinearMap.toSpanSingleton_apply] at hab
      have h : (a - b) • d₀ = 0 := by rw [sub_smul, hab, sub_self]
      rcases smul_eq_zero.mp h with h' | h'
      · linarith
      · exact absurd h' hd₀ne
    obtain ⟨N, hN⟩ := Submodule.exists_isCompl (LinearMap.range i)
    set ψ : E →ₗ[ℝ] ℝ := LinearMap.linearProjOfIsCompl (q := N) i hi_inj hN with hψdef
    have hψ : ψ d₀ = 1 := by
      have h1 : i 1 = d₀ := by simp [hi_def]
      rw [← h1]
      exact LinearMap.linearProjOfIsCompl_apply_left (q := N) i hi_inj hN 1
    have hd₀pos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
    set π : E →ₗ[ℝ] E := LinearMap.id - (LinearMap.toSpanSingleton ℝ E d₀).comp ψ with hπ
    have hπ_apply : ∀ x : E, π x = x - ψ x • d₀ := by
      intro x; simp [hπ]
    have hπd₀ : π d₀ = 0 := by
      rw [hπ_apply, hψ, one_smul, sub_self]
    have hπψ : ∀ x : E, ψ (π x) = 0 := by
      intro x; rw [hπ_apply, map_sub, map_smul, hψ, smul_eq_mul, mul_one, sub_self]
    have hπfix : ∀ y : E, ψ y = 0 → π y = y := by
      intro y hy; rw [hπ_apply, hy, zero_smul, sub_zero]
    set K : Submodule ℝ E := LinearMap.ker ψ with hKdef
    have hd₀K : d₀ ∉ K := by simp [hKdef, hψ]
    have hKtop : K ≠ ⊤ := fun h => hd₀K (h ▸ Submodule.mem_top)
    set πK : E →ₗ[ℝ] K := π.codRestrict K (fun x => hπψ x) with hπK
    have hπK_surj : Function.Surjective πK := by
      intro y
      exact ⟨(y : E), Subtype.ext (hπfix (y : E) y.2)⟩
    set D' : AddSubgroup K := D.map πK.toAddMonoidHom with hD'def
    -- every image is either zero or at distance at least `‖d₀‖/2`
    have key : ∀ d ∈ D, π d = 0 ∨ ‖d₀‖ / 2 ≤ ‖π d‖ := by
      intro d hd
      rcases eq_or_ne (π d) 0 with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ?_
        by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk⟩ := exists_int_close (ψ d)
        have hmem : d - (k : ℝ) • d₀ ∈ D := by
          have hkD : (k : ℝ) • d₀ ∈ D := by
            have hz : (k : ℤ) • d₀ ∈ D := D.zsmul_mem hd₀D k
            rwa [Int.cast_smul_eq_zsmul ℝ k d₀]
          exact D.sub_mem hd hkD
        have hdecomp : d - (k : ℝ) • d₀ = π d + (ψ d - (k : ℝ)) • d₀ := by
          rw [hπ_apply d]; module
        have hnorm : ‖d - (k : ℝ) • d₀‖ < ‖d₀‖ := by
          rw [hdecomp]
          calc ‖π d + (ψ d - (k : ℝ)) • d₀‖
              ≤ ‖π d‖ + ‖(ψ d - (k : ℝ)) • d₀‖ := norm_add_le _ _
            _ = ‖π d‖ + |ψ d - (k : ℝ)| * ‖d₀‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ‖π d‖ + (1 / 2) * ‖d₀‖ := by nlinarith [hk, abs_nonneg (ψ d - (k:ℝ))]
            _ < ‖d₀‖ / 2 + (1 / 2) * ‖d₀‖ := by linarith
            _ = ‖d₀‖ := by ring
        have hne' : d - (k : ℝ) • d₀ ≠ 0 := by
          intro hzero
          apply h0
          have h1 : π (d - (k : ℝ) • d₀) = π d := by
            rw [map_sub, map_smul, hπd₀, smul_zero, sub_zero]
          rw [← h1, hzero, map_zero]
        exact absurd (hmin _ hmem hne') (not_le.mpr hnorm)
    have hiso' : IsolatedZero D' := by
      refine ⟨‖d₀‖ / 2, by positivity, ?_⟩
      intro x hx hlt
      obtain ⟨d, hd, rfl⟩ := AddSubgroup.mem_map.mp hx
      have hnorm : ‖π d‖ < ‖d₀‖ / 2 := hlt
      rcases key d hd with h | h
      · exact Subtype.ext h
      · linarith
    have hspan' : Submodule.span ℝ (D' : Set K) = ⊤ := by
      have himg : (D' : Set K) = πK '' (D : Set E) := by
        rw [hD'def]; rfl
      rw [himg, ← Submodule.map_span, hspan, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr hπK_surj
    by_cases hD'bot : D' = ⊥
    · -- `D` lies on the line spanned by `d₀`, and `ψ` is the functional
      refine ⟨ψ, ?_, ?_⟩
      · intro h0
        have := hψ
        rw [h0] at this
        simpa using this
      · intro d hd
        have hpizero : π d = 0 := by
          have hmem : πK d ∈ D' := AddSubgroup.mem_map.mpr ⟨d, hd, rfl⟩
          rw [hD'bot] at hmem
          exact congrArg Subtype.val (by simpa using hmem)
        have hd_eq : d = ψ d • d₀ := by
          have h' : d - ψ d • d₀ = 0 := by rw [← hπ_apply d]; exact hpizero
          exact sub_eq_zero.mp h'
        obtain ⟨k, hk⟩ := exists_int_close (ψ d)
        have hmem : d - (k : ℝ) • d₀ ∈ D := by
          have hkD : (k : ℝ) • d₀ ∈ D := by
            have hz : (k : ℤ) • d₀ ∈ D := D.zsmul_mem hd₀D k
            rwa [Int.cast_smul_eq_zsmul ℝ k d₀]
          exact D.sub_mem hd hkD
        have hsmall : ‖d - (k : ℝ) • d₀‖ < ‖d₀‖ := by
          rw [hd_eq, ← sub_smul, norm_smul, Real.norm_eq_abs]
          by_cases hc : (ψ d - (k : ℝ)) = 0
          · simp [hc, hd₀pos]
          · have hpos : 0 < |ψ d - (k : ℝ)| := abs_pos.mpr hc
            nlinarith [abs_nonneg (ψ d - (k:ℝ))]
        by_cases hzero : d - (k : ℝ) • d₀ = 0
        · refine ⟨k, ?_⟩
          have hdk : d = (k : ℝ) • d₀ := sub_eq_zero.mp hzero
          rw [hdk, map_smul, hψ, smul_eq_mul, mul_one]
        · exact absurd (hmin _ hmem hzero) (not_le.mpr hsmall)
    · -- recurse on the hyperplane `K`
      have hfr : finrank ℝ K < n := by
        rw [← hn]
        exact Submodule.finrank_lt hKtop
      obtain ⟨μ', hμ'ne, hμ'int⟩ :=
        ih (finrank ℝ K) hfr K rfl D' hiso' hspan' hD'bot
      refine ⟨μ'.comp πK, ?_, ?_⟩
      · intro hcomp
        apply hμ'ne
        ext y
        have hy : (πK y : K) = y := Subtype.ext (hπfix (y : E) y.2)
        have h0 := LinearMap.ext_iff.mp hcomp y
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h0
        rw [hy] at h0
        exact h0
      · intro d hd
        exact hμ'int (πK d) (AddSubgroup.mem_map.mpr ⟨d, hd, rfl⟩)

/-- **The discrete case.** -/
theorem exists_integral_functional_of_discrete (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (D : AddSubgroup E) (hiso : IsolatedZero D)
    (hspan : Submodule.span ℝ (D : Set E) = ⊤) (hne : D ≠ ⊥) :
    ∃ μ : E →ₗ[ℝ] ℝ, μ ≠ 0 ∧ ∀ d ∈ D, ∃ m : ℤ, μ d = m :=
  exists_integral_functional_of_discrete_aux (finrank ℝ E) E rfl D hiso hspan hne

end Discrete

/-! ## 3. A closed subgroup with no line is discrete -/

section NoLine

variable [NormedAddCommGroup E]

/-- **A closed subgroup that is not discrete contains a whole line.**  The
contrapositive is what the structure theorem uses: a closed subgroup containing
no nonzero one-parameter subgroup has an isolated zero. -/
theorem exists_line_of_not_isolatedZero [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D : AddSubgroup E} (hcl : IsClosed (D : Set E)) (h : ¬ IsolatedZero D) :
    ∃ u : E, u ≠ 0 ∧ ∀ t : ℝ, t • u ∈ D := by
  classical
  have hstep : ∀ ε : ℝ, 0 < ε → ∃ d ∈ D, d ≠ 0 ∧ ‖d‖ < ε := by
    intro ε hε
    by_contra hc
    have hc' : ∀ d ∈ D, d ≠ 0 → ε ≤ ‖d‖ := by
      intro d hd hne
      by_contra hlt
      push Not at hlt
      exact hc ⟨d, hd, hne, hlt⟩
    exact h ⟨ε, hε, fun d hd hlt => by
      by_contra hne
      exact absurd hlt (not_lt.mpr (hc' d hd hne))⟩
  choose hh hhmem hhne hhnorm using fun n : ℕ => hstep (1 / ((n : ℝ) + 1)) (by positivity)
  have hhpos : ∀ n, 0 < ‖hh n‖ := fun n => norm_pos_iff.mpr (hhne n)
  set y : ℕ → E := fun n => ‖hh n‖⁻¹ • hh n with hy
  have hyh : ∀ n, hh n = ‖hh n‖ • y n := by
    intro n
    rw [hy, smul_smul, mul_inv_cancel₀ (ne_of_gt (hhpos n)), one_smul]
  have hynorm : ∀ n, ‖y n‖ = 1 := by
    intro n
    have h := congrArg norm (hyh n)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hhpos n)] at h
    have h1 : ‖hh n‖ * 1 = ‖hh n‖ * ‖y n‖ := by rw [mul_one, ← h]
    exact (mul_left_cancel₀ (ne_of_gt (hhpos n)) h1).symm
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  have hcomp : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  obtain ⟨u, hu, φ, hφ, hytend⟩ := hcomp.tendsto_subseq (fun n => by
    rw [Metric.mem_sphere, dist_zero_right]; exact hynorm n)
  have hu1 : ‖u‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hu; exact hu
  have hunorm : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu1; norm_num at hu1
  have hytend' : Tendsto (fun n : ℕ => y (φ n)) atTop (𝓝 u) := hytend
  have hclose : Tendsto (fun n : ℕ => ‖y (φ n) - u‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => y (φ n) - u) atTop (𝓝 (u - u)) :=
      hytend'.sub tendsto_const_nhds
    rw [sub_self] at h0
    simpa using h0.norm
  have hhsmall : Tendsto (fun n : ℕ => ‖hh (φ n)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hhnorm (φ n))) hsub
  -- the nonnegative half-line
  have hprev : ∀ s : ℝ, 0 ≤ s → s • u ∈ D := by
    intro s hs
    have hbound : ∀ n : ℕ,
        ‖((⌊s / ‖hh (φ n)‖⌋ : ℤ) : ℝ) • hh (φ n) - s • u‖
          ≤ ‖hh (φ n)‖ + s * ‖y (φ n) - u‖ := by
      intro n
      set c : ℝ := s / ‖hh (φ n)‖ with hc
      set k : ℤ := ⌊c⌋ with hk
      have hkh : ((k : ℝ) • hh (φ n)) = ((k : ℝ) * ‖hh (φ n)‖) • y (φ n) := by
        conv_lhs => rw [hyh (φ n)]
        rw [smul_smul]
      have hsplit : ((k : ℝ) • hh (φ n) - s • u)
          = ((k : ℝ) * ‖hh (φ n)‖ - s) • y (φ n) + s • (y (φ n) - u) := by
        rw [hkh, smul_sub]
        module
      have hk_bound : |c - (k : ℝ)| ≤ 1 := by
        have h1 : (k : ℝ) ≤ c := Int.floor_le _
        have h2 : c < (k : ℝ) + 1 := Int.lt_floor_add_one _
        rw [abs_le]; constructor <;> linarith
      have hfirst : ‖((k : ℝ) * ‖hh (φ n)‖ - s) • y (φ n)‖ ≤ ‖hh (φ n)‖ := by
        rw [norm_smul, hynorm (φ n), mul_one, Real.norm_eq_abs]
        have hsc : s = ‖hh (φ n)‖ * c := by
          rw [hc, mul_div_cancel₀ s (ne_of_gt (hhpos (φ n)))]
        have hfac : (k : ℝ) * ‖hh (φ n)‖ - s = -(‖hh (φ n)‖ * (c - (k : ℝ))) := by
          rw [hsc]; ring
        rw [hfac, abs_neg, abs_mul, abs_of_pos (hhpos (φ n))]
        calc ‖hh (φ n)‖ * |c - (k : ℝ)| ≤ ‖hh (φ n)‖ * 1 :=
              mul_le_mul_of_nonneg_left hk_bound (le_of_lt (hhpos (φ n)))
          _ = ‖hh (φ n)‖ := mul_one _
      calc ‖((⌊s / ‖hh (φ n)‖⌋ : ℤ) : ℝ) • hh (φ n) - s • u‖
          = ‖((k : ℝ) * ‖hh (φ n)‖ - s) • y (φ n) + s • (y (φ n) - u)‖ := by rw [hsplit]
        _ ≤ ‖((k : ℝ) * ‖hh (φ n)‖ - s) • y (φ n)‖ + ‖s • (y (φ n) - u)‖ := norm_add_le _ _
        _ ≤ ‖hh (φ n)‖ + s * ‖y (φ n) - u‖ := by
            have h2 : ‖s • (y (φ n) - u)‖ = s * ‖y (φ n) - u‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
            rw [h2]; linarith [hfirst]
    have hzero : Tendsto (fun n : ℕ =>
        ‖((⌊s / ‖hh (φ n)‖⌋ : ℤ) : ℝ) • hh (φ n) - s • u‖) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => s * ‖y (φ n) - u‖) atTop (𝓝 0) := by
        simpa using hclose.const_mul s
      have hsum : Tendsto (fun n : ℕ => ‖hh (φ n)‖ + s * ‖y (φ n) - u‖) atTop (𝓝 0) := by
        simpa using hhsmall.add h2
      exact squeeze_zero (fun n => norm_nonneg _) hbound hsum
    have hmain : Tendsto (fun n : ℕ => ((⌊s / ‖hh (φ n)‖⌋ : ℤ) : ℝ) • hh (φ n))
        atTop (𝓝 (s • u)) := by
      rw [Metric.tendsto_atTop] at hzero ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hzero ε hε
      exact ⟨N, fun n hn => by
        have h := hN n hn
        rw [dist_eq_norm, sub_zero, norm_norm] at h
        rw [dist_eq_norm]
        exact h⟩
    refine hcl.mem_of_tendsto hmain (Eventually.of_forall fun n => ?_)
    have hz : (⌊s / ‖hh (φ n)‖⌋ : ℤ) • hh (φ n) ∈ D := D.zsmul_mem (hhmem (φ n)) _
    rwa [Int.cast_smul_eq_zsmul ℝ (⌊s / ‖hh (φ n)‖⌋) (hh (φ n))]
  refine ⟨u, hunorm, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact hprev t ht
  · have hpos : 0 < -t := by linarith
    have hneg := hprev (-t) (le_of_lt hpos)
    have heq : t • u = -((-t) • u) := by rw [neg_smul, neg_neg]
    rw [heq]
    exact D.neg_mem hneg

end NoLine

/-! ## 4. A functional with a prescribed nonzero value -/

section Prescribed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For `x ≠ 0` there is a linear functional taking the value `1` at `x`. -/
theorem exists_functional_eq_one {x : E} (hx : x ≠ 0) : ∃ k : E →ₗ[ℝ] ℝ, k x = 1 := by
  set i : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E x with hi_def
  have hi_inj : Function.Injective i := by
    intro a b hab
    simp only [hi_def, LinearMap.toSpanSingleton_apply] at hab
    have h : (a - b) • x = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · linarith
    · exact absurd h' hx
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (LinearMap.range i)
  refine ⟨LinearMap.linearProjOfIsCompl (q := N) i hi_inj hN, ?_⟩
  have h1 : i 1 = x := by simp [hi_def]
  rw [← h1]
  exact LinearMap.linearProjOfIsCompl_apply_left (q := N) i hi_inj hN 1

/-- **The largest subspace contained in a subgroup.** -/
def lineal (H : AddSubgroup E) : Submodule ℝ E where
  carrier := {x : E | ∀ t : ℝ, t • x ∈ H}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro x y hx hy t
    rw [smul_add]
    exact H.add_mem (hx t) (hy t)
  smul_mem' := by
    intro c x hx t
    simpa [smul_smul] using hx (t * c)

theorem mem_lineal {H : AddSubgroup E} {x : E} :
    x ∈ lineal H ↔ ∀ t : ℝ, t • x ∈ H := Iff.rfl

theorem lineal_le {H : AddSubgroup E} : (lineal H : Set E) ⊆ H := by
  intro x hx
  simpa using hx 1

/-- **Spanning-free form of the discrete case.** -/
theorem exists_integral_functional_of_discrete' {D : AddSubgroup E} (hiso : IsolatedZero D)
    (hne : D ≠ ⊥) :
    ∃ μ : E →ₗ[ℝ] ℝ, μ ≠ 0 ∧ ∀ d ∈ D, ∃ m : ℤ, μ d = m := by
  classical
  set U : Submodule ℝ E := Submodule.span ℝ (D : Set E) with hU
  set DU : AddSubgroup U := D.comap U.subtype.toAddMonoidHom with hDU
  have hisoU : IsolatedZero DU := by
    obtain ⟨ε, hε, hε'⟩ := hiso
    refine ⟨ε, hε, fun x hx hlt => ?_⟩
    have hxE : (x : E) ∈ D := hx
    have h0 : (x : E) = 0 := hε' (x : E) hxE (by simpa using hlt)
    exact Subtype.ext h0
  have hneU : DU ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro d hd
    have hmem : (⟨d, Submodule.subset_span hd⟩ : U) ∈ DU := hd
    rw [h] at hmem
    simpa using hmem
  have hspanU : Submodule.span ℝ (DU : Set U) = ⊤ := by
    have h1 : Submodule.map U.subtype (Submodule.span ℝ (DU : Set U)) = U := by
      rw [Submodule.map_span]
      have himg : (U.subtype '' (DU : Set U)) = (D : Set E) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
      rw [himg, ← hU]
    rw [eq_top_iff]
    intro y _
    have hy : (y : E) ∈ Submodule.map U.subtype (Submodule.span ℝ (DU : Set U)) := by
      rw [h1]; exact y.2
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  obtain ⟨μU, hμUne, hμUint⟩ :=
    exists_integral_functional_of_discrete U DU hisoU hspanU hneU
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl U
  have hN' : IsCompl (LinearMap.range U.subtype) N := by
    rwa [Submodule.range_subtype]
  refine ⟨μU.comp (LinearMap.linearProjOfIsCompl (q := N) U.subtype U.subtype_injective hN'),
    ?_, ?_⟩
  · intro h0
    apply hμUne
    ext y
    have h1 := LinearMap.ext_iff.mp h0 y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1
    have hfix : (LinearMap.linearProjOfIsCompl (q := N) U.subtype U.subtype_injective hN')
        (y : E) = y :=
      LinearMap.linearProjOfIsCompl_apply_left (q := N) U.subtype U.subtype_injective hN' y
    rw [hfix] at h1
    exact h1
  · intro d hd
    obtain ⟨m, hm⟩ := hμUint ⟨d, Submodule.subset_span hd⟩ (by exact hd)
    refine ⟨m, ?_⟩
    have hfix : (LinearMap.linearProjOfIsCompl (q := N) U.subtype U.subtype_injective hN')
        ((⟨d, Submodule.subset_span hd⟩ : U) : E) = ⟨d, Submodule.subset_span hd⟩ :=
      LinearMap.linearProjOfIsCompl_apply_left (q := N) U.subtype U.subtype_injective hN'
        (⟨d, Submodule.subset_span hd⟩ : U)
    simp only [LinearMap.comp_apply]
    rw [hfix]
    exact hm

/-! ## 5. What remains, precisely

The separation theorem for an arbitrary closed proper subgroup `H ≤ E` is
reduced by the two theorems above to a single step.  The argument is:

* if `H` has an isolated zero, `exists_integral_functional_of_discrete'` gives
  a nonzero `ℤ`-valued functional on `H` outright;
* otherwise `exists_line_of_not_isolatedZero` produces a line `ℝ ∙ u ⊆ H`; since
  `H` is closed and contains that line, `H` is saturated for the quotient map
  `E → E ⧸ ℝ ∙ u`, so the image `H ⧸ ℝ ∙ u` is closed, is not the whole
  quotient (density of it would give `H = ⊤`), and has strictly smaller
  dimension.  Induction on `dim E` then yields a functional on the quotient,
  which pulls back to `H`.

Only the quotient-cleanliness step (`Dense (mk '' H) → H = ⊤` for a closed
`H ⊇ ℝ ∙ u`) is not formalized here; everything else in the reduction is
proved.
-/

end Prescribed


/-! ## 6. Axiom audit -/

#print axioms BerendCoordDense.isolatedZero_of_discreteTopology
#print axioms BerendCoordDense.isClosed_of_isolatedZero
#print axioms BerendCoordDense.exists_min_norm
#print axioms BerendCoordDense.exists_integral_functional_of_discrete
#print axioms BerendCoordDense.exists_integral_functional_of_discrete'
#print axioms BerendCoordDense.exists_line_of_not_isolatedZero
#print axioms BerendCoordDense.exists_functional_eq_one

section Separation

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Separation for closed proper subgroups.**  Every closed subgroup `H ≠ ⊤` of a
finite-dimensional real normed space carries a nonzero linear functional that is
`ℤ`-valued on `H`.

The proof is an induction on the dimension.  If `H` has an isolated zero, the
discrete case applies.  Otherwise `H` contains a line `ℝ • u`; choosing
`ψ u = 1` and projecting onto the hyperplane `ker ψ` *along that line* maps `H`
into `H ∩ ker ψ`, so the induction applies there and the functional pulls back. -/
theorem exists_integral_functional_of_isClosed_aux :
    ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ (H : AddSubgroup E), IsClosed (H : Set E) → H ≠ ⊤ →
        ∃ k : E →ₗ[ℝ] ℝ, k ≠ 0 ∧ ∀ h ∈ H, ∃ m : ℤ, k h = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hn H hcl hne
    classical
    rcases eq_or_ne H ⊥ with hbot | hbot
    · haveI hnt : Nontrivial E := by
        rcases subsingleton_or_nontrivial E with h | h
        · exact absurd (Subsingleton.elim H ⊤) hne
        · exact h
      obtain ⟨x, hx⟩ := exists_ne (0 : E)
      obtain ⟨k, hk⟩ := exists_functional_eq_one hx
      refine ⟨k, ?_, ?_⟩
      · intro h0; rw [h0] at hk; simpa using hk
      · intro h hh
        rw [hbot] at hh
        have hz : h = 0 := by simpa using hh
        exact ⟨0, by rw [hz]; simp⟩
    · by_cases hdis : IsolatedZero H
      · obtain ⟨k, hkne, hkint⟩ := exists_integral_functional_of_discrete' hdis hbot
        exact ⟨k, hkne, hkint⟩
      · obtain ⟨u, hu0, hul⟩ := exists_line_of_not_isolatedZero hcl hdis
        obtain ⟨ψ, hψ⟩ := exists_functional_eq_one hu0
        set P : Submodule ℝ E := LinearMap.ker ψ with hP
        set L : Submodule ℝ E := Submodule.span ℝ {u} with hL
        have hmemL : ∀ c : ℝ, c • u ∈ L := by
          intro c
          rw [hL, Submodule.mem_span_singleton]
          exact ⟨c, rfl⟩
        have hLH : (L : Set E) ⊆ H := by
          intro x hx
          have hx' : x ∈ Submodule.span ℝ ({u} : Set E) := by simpa [hL] using hx
          rw [Submodule.mem_span_singleton] at hx'
          obtain ⟨c, rfl⟩ := hx'
          simpa using hul c
        have hψP : ∀ x ∈ P, ψ x = 0 := fun x hx => hx
        have huP : u ∉ P := by
          intro h
          have h1 : ψ u = 0 := h
          rw [hψ] at h1; exact one_ne_zero h1
        have hcompl : IsCompl P L := by
          constructor
          · rw [disjoint_iff, eq_bot_iff]
            intro x hx
            obtain ⟨hxP, hxL⟩ := hx
            have hxL' : x ∈ Submodule.span ℝ ({u} : Set E) := by simpa [hL] using hxL
            rw [Submodule.mem_span_singleton] at hxL'
            obtain ⟨c, rfl⟩ := hxL'
            have h1 : ψ (c • u) = 0 := hxP
            rw [map_smul, hψ, smul_eq_mul, mul_one] at h1
            rw [h1, zero_smul]
            exact Submodule.zero_mem _
          · rw [codisjoint_iff, eq_top_iff]
            intro x _
            have hx : x = (x - ψ x • u) + ψ x • u := by abel
            rw [hx]
            refine Submodule.add_mem_sup ?_ (hmemL (ψ x))
            simp only [hP, LinearMap.mem_ker]
            rw [map_sub, map_smul, hψ, smul_eq_mul, mul_one, sub_self]
        have hPL : IsCompl (LinearMap.range P.subtype) L := by
          rwa [Submodule.range_subtype]
        set proj : E →ₗ[ℝ] P :=
          LinearMap.linearProjOfIsCompl (q := L) P.subtype P.subtype_injective hPL with hproj
        have hprojfix : ∀ y : P, proj (y : E) = y := fun y =>
          LinearMap.linearProjOfIsCompl_apply_left (q := L) P.subtype P.subtype_injective hPL y
        have hprojker : ∀ x : E, proj x = 0 → x ∈ L := by
          intro x hx
          have : x ∈ LinearMap.ker proj := hx
          rwa [LinearMap.ker_linearProjOfIsCompl] at this
        -- the piece of `H` inside the hyperplane
        set H1 : AddSubgroup P := (H ⊓ P.toAddSubgroup).comap P.subtype.toAddMonoidHom with hH1
        have hH1mem : ∀ y : P, y ∈ H1 ↔ (y : E) ∈ H := by
          intro y
          constructor
          · intro hy; exact hy.1
          · intro hy; exact ⟨hy, y.2⟩
        have hH1cl : IsClosed (H1 : Set P) := by
          have hPcl : IsClosed (P : Set E) := Submodule.closed_of_finiteDimensional P
          have hcl' : IsClosed ((H ⊓ P.toAddSubgroup : AddSubgroup E) : Set E) := hcl.inter hPcl
          exact hcl'.preimage continuous_subtype_val
        have hH1ne : H1 ≠ ⊤ := by
          intro htop
          apply hne
          rw [eq_top_iff]
          intro x _
          have hPsub : P.toAddSubgroup ≤ H := by
            intro y hy
            have : (⟨y, hy⟩ : P) ∈ H1 := by
              rw [htop]
              exact AddSubgroup.mem_top _
            exact (hH1mem ⟨y, hy⟩).1 this
          have hsup : P ⊔ L = ⊤ := by
            rw [eq_top_iff]
            intro x _
            have hx : x = (x - ψ x • u) + ψ x • u := by abel
            rw [hx]
            refine Submodule.add_mem_sup ?_ (hmemL (ψ x))
            simp only [hP, LinearMap.mem_ker]
            rw [map_sub, map_smul, hψ, smul_eq_mul, mul_one, sub_self]
          have hmem : x ∈ P ⊔ L := by rw [hsup]; exact Submodule.mem_top
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
          rw [← hab]
          exact H.add_mem (hPsub ha) (hLH hb)
        have hfr : finrank ℝ P < n := by
          rw [← hn]
          exact Submodule.finrank_lt (by
            intro h
            have hmem : u ∈ P := by rw [h]; exact Submodule.mem_top
            exact huP hmem)
        obtain ⟨k', hk'ne, hk'int⟩ := ih (finrank ℝ P) hfr P rfl H1 hH1cl hH1ne
        refine ⟨k'.comp proj, ?_, ?_⟩
        · intro h0
          apply hk'ne
          ext y
          have h1 := LinearMap.ext_iff.mp h0 y
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1
          rw [hprojfix y] at h1
          exact h1
        · intro h hh
          -- `proj h ∈ H ∩ P`
          have hker : h - (proj h : E) ∈ L := by
            apply hprojker
            rw [map_sub]
            have hfix := hprojfix (proj h)
            rw [hfix, sub_self]
          have hmemH : (proj h : E) ∈ H := by
            have h2 : h - (h - (proj h : E)) ∈ H := H.sub_mem hh (hLH hker)
            have heq : h - (h - (proj h : E)) = (proj h : E) := by abel
            rwa [heq] at h2
          obtain ⟨m, hm⟩ := hk'int (proj h) ((hH1mem (proj h)).2 hmemH)
          refine ⟨m, ?_⟩
          simpa [LinearMap.comp_apply] using hm

/-- **Separation for closed proper subgroups.** -/
theorem exists_integral_functional_of_isClosed (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : AddSubgroup E} (hcl : IsClosed (H : Set E)) (hne : H ≠ ⊤) :
    ∃ k : E →ₗ[ℝ] ℝ, k ≠ 0 ∧ ∀ h ∈ H, ∃ m : ℤ, k h = m :=
  exists_integral_functional_of_isClosed_aux (finrank ℝ E) E rfl H hcl hne

end Separation

end BerendCoordDense

