/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.PureGround

/-! # The gap of the parent Hamiltonian (G5, Package A)

For a pure covariance `Γ` the quadratic Hamiltonian `H_{-Γ}` has ground energy `-n/2`,
attained only by the Gaussian state `ρ₀` with covariance `Γ` (Package B of G4). Here we show
that the spectrum has a gap of exactly one above the ground energy: every density operator
orthogonal to `ρ₀` (`Tr(ρ ρ₀) = 0`) has energy at least `-n/2 + 1`, and for `n ≥ 1` this bound
is attained. In the rotated frame `H_{-Γ} = Uᴴ H_{D(ε)} U` with `|ε_j| = 1`, the diagonal
entries of `H_{D(ε)}` are `-n/2 + (number of modes differing from s^ε)`, and orthogonality to
`ρ₀ = Uᴴ |s^ε⟩⟨s^ε| U` kills the weight of the rotated `ρ` at `s^ε`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The diagonal entry of `U ρ U*` at `s₀` is `Tr(ρ · U* |s₀⟩⟨s₀| U)`. -/
lemma diag_conj_eq_trace_mul (U ρ : Matrix (FockIndex n) (FockIndex n) ℂ) (s₀ : FockIndex n) :
    (U * ρ * U.conjTranspose) s₀ s₀ =
      (ρ * (U.conjTranspose * occupation s₀ * U)).trace := by
  calc (U * ρ * U.conjTranspose) s₀ s₀
      = (occupation s₀ * (U * ρ * U.conjTranspose)).trace := (trace_occupation_mul _ _).symm
    _ = ((occupation s₀ * U * ρ) * U.conjTranspose).trace := by simp only [Matrix.mul_assoc]
    _ = (U.conjTranspose * (occupation s₀ * U * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = ((U.conjTranspose * occupation s₀ * U) * ρ).trace := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

/-- The energy of a configuration differing from `s^ε` is at least one above the ground energy
when every `|ε_j| = 1`. -/
lemma groundEnergy_add_one_le_blockEnergy {ε : Fin n → ℝ} (hε : ∀ j, |ε j| = 1)
    {s : FockIndex n} (hs : s ≠ groundConfig ε) :
    groundEnergy ε + 1 ≤ blockEnergy ε s := by
  have hsub := blockEnergy_sub_groundConfig ε s
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ groundConfig ε j := Function.ne_iff.mp hs
  have h1 : (if s j = groundConfig ε j then 0 else |ε j|) ≤
      ∑ k, if s k = groundConfig ε k then 0 else |ε k| :=
    Finset.single_le_sum (f := fun k => if s k = groundConfig ε k then 0 else |ε k|)
      (fun k _ => by split_ifs <;> simp) (Finset.mem_univ j)
  rw [ite_eq_right hj, hε j] at h1
  linarith

/-- The energy of a configuration differing from `s^ε` exactly in the mode `j₀` is exactly one
above the ground energy when `|ε_{j₀}| = 1`. -/
lemma blockEnergy_update_groundConfig {ε : Fin n → ℝ} (j₀ : Fin n) (hε : |ε j₀| = 1)
    (b : Fin 2) (hb : b ≠ groundConfig ε j₀) :
    blockEnergy ε (Function.update (groundConfig ε) j₀ b) = groundEnergy ε + 1 := by
  have hsub := blockEnergy_sub_groundConfig ε (Function.update (groundConfig ε) j₀ b)
  rw [Finset.sum_eq_single j₀] at hsub
  · rw [Function.update_self, ite_eq_right hb, hε] at hsub
    linarith
  · intro k _ hk
    rw [Function.update_of_ne hk, ite_eq_left rfl]
  · simp

/-- Proposed Theorem (gap), bound: for pure `Γ`, a Gaussian `ρ₀` with covariance `Γ` (the
ground state of `H_{-Γ}`), and a density operator `ρ` with `Tr(ρ ρ₀) = 0`,
`E_{-Γ}(ρ) ≥ -n/2 + 1`. -/
theorem energy_neg_ge_of_trace_mul_eq_zero {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsPure Γ) {ρ₀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ₀ : IsGaussian ρ₀)
    (hcov : covariance ρ₀ = Γ) (hρ : IsDensity ρ) (horth : (ρ * ρ₀).trace = 0) :
    -(n / 2 : ℝ) + 1 ≤ energy (-Γ) ρ := by
  have hneg : IsPure (-Γ) := by
    refine ⟨by rw [Matrix.transpose_neg, hΓ.1, neg_neg], ?_⟩
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hΓ.2]
  obtain ⟨O, ε, hO, hdet, hOε⟩ := exists_normalForm_special (-Γ) hneg.1
  have hε : ∀ j, |ε j| = 1 := abs_eq_one_of_isPure_normalForm hO hOε hneg
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  -- `ρ₀` is the ground state `Uᴴ |s^ε⟩⟨s^ε| U`
  have hcovΓ : covariance (groundState U ε) = Γ := by
    rw [covariance_groundState hU hU' hUO, blockForm_neg_sgn_of_abs_eq_one hε, Matrix.mul_neg,
      Matrix.neg_mul, ← hOε, neg_neg]
  have hρ₀eq : ρ₀ = groundState U ε :=
    hρ₀.eq_of_covariance_eq (isGaussian_pure hU hU' hUO _) (by rw [hcov, hcovΓ])
  -- pass to the rotated frame
  rw [hOε, energy_conj hU' hUO hO]
  unfold energy
  rw [quadHam_blockForm, re_trace_mul_diagonal]
  have hρ' : IsDensity (U * ρ * U.conjTranspose) := (covariance_conj hU hU' hUO hρ).1
  have h0 : ((U * ρ * U.conjTranspose) (groundConfig ε) (groundConfig ε)).re = 0 := by
    rw [diag_conj_eq_trace_mul, ← groundState, ← hρ₀eq, horth, Complex.zero_re]
  have hE := groundEnergy_of_abs_eq_one hε
  have hterm : ∀ s, ((U * ρ * U.conjTranspose) s s).re * (-(n / 2 : ℝ) + 1) ≤
      ((U * ρ * U.conjTranspose) s s).re * blockEnergy ε s := fun s => by
    by_cases hs : s = groundConfig ε
    · rw [hs, h0, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hρ'.diag_re_nonneg s)
      rw [← hE]
      exact groundEnergy_add_one_le_blockEnergy hε hs
  calc -(n / 2 : ℝ) + 1 = ∑ s, ((U * ρ * U.conjTranspose) s s).re * (-(n / 2 : ℝ) + 1) := by
        rw [← Finset.sum_mul, hρ'.sum_diag_re, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun s _ => hterm s

/-- Proposed Theorem (gap), attainment: for `n ≥ 1` there is a density operator `ρ'` with
`Tr(ρ' ρ₀) = 0` and `E_{-Γ}(ρ') = -n/2 + 1`. -/
theorem exists_trace_mul_eq_zero_and_energy_neg_eq
    {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsPure Γ) {ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ₀ : IsGaussian ρ₀)
    (hcov : covariance ρ₀ = Γ) (hn : 0 < n) :
    ∃ ρ' : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsDensity ρ' ∧ (ρ' * ρ₀).trace = 0 ∧ energy (-Γ) ρ' = -(n / 2 : ℝ) + 1 := by
  have hneg : IsPure (-Γ) := by
    refine ⟨by rw [Matrix.transpose_neg, hΓ.1, neg_neg], ?_⟩
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hΓ.2]
  obtain ⟨O, ε, hO, hdet, hOε⟩ := exists_normalForm_special (-Γ) hneg.1
  have hε : ∀ j, |ε j| = 1 := abs_eq_one_of_isPure_normalForm hO hOε hneg
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  have hcovΓ : covariance (groundState U ε) = Γ := by
    rw [covariance_groundState hU hU' hUO, blockForm_neg_sgn_of_abs_eq_one hε, Matrix.mul_neg,
      Matrix.neg_mul, ← hOε, neg_neg]
  have hρ₀eq : ρ₀ = groundState U ε :=
    hρ₀.eq_of_covariance_eq (isGaussian_pure hU hU' hUO _) (by rw [hcov, hcovΓ])
  -- flip the mode `0` of the ground configuration
  set j₀ : Fin n := ⟨0, hn⟩
  set s' : FockIndex n := Function.update (groundConfig ε) j₀ (1 - groundConfig ε j₀) with hs'def
  have hb : (1 : Fin 2) - groundConfig ε j₀ ≠ groundConfig ε j₀ := by
    generalize groundConfig ε j₀ = b
    fin_cases b <;> decide
  have hs' : s' ≠ groundConfig ε := fun h => hb (by
    have := congrFun h j₀
    rwa [hs'def, Function.update_self] at this)
  refine ⟨U.conjTranspose * occupation s' * U,
    (covariance_conj' hU hU' hUO (isDensity_occupation s')).1, ?_, ?_⟩
  · -- orthogonality: `|s'⟩⟨s'| · |s^ε⟩⟨s^ε| = 0`
    rw [hρ₀eq, groundState]
    have hprod : U.conjTranspose * occupation s' * U *
        (U.conjTranspose * occupation (groundConfig ε) * U) =
        U.conjTranspose * (occupation s' * occupation (groundConfig ε)) * U := by
      calc U.conjTranspose * occupation s' * U *
            (U.conjTranspose * occupation (groundConfig ε) * U)
          = U.conjTranspose * occupation s' * (U * U.conjTranspose) *
              occupation (groundConfig ε) * U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hprod, occupation, occupation, Matrix.single_mul_single_of_ne (h := hs'), Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero]
  · -- energy: exactly one mode differs from `s^ε`
    rw [hOε, energy_conj hU' hUO hO]
    have hback : U * (U.conjTranspose * occupation s' * U) * U.conjTranspose = occupation s' := by
      calc U * (U.conjTranspose * occupation s' * U) * U.conjTranspose
          = (U * U.conjTranspose) * occupation s' * (U * U.conjTranspose) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
    rw [hback]
    unfold energy
    rw [quadHam_blockForm, re_trace_mul_diagonal, Finset.sum_eq_single s']
    · simp only [occupation, Matrix.single_apply_same, Complex.one_re, one_mul]
      rw [hs'def, blockEnergy_update_groundConfig j₀ (hε j₀) _ hb, groundEnergy_of_abs_eq_one hε]
    · intro s _ hs; simp [occupation, Ne.symm hs]
    · simp

end Fermionic
