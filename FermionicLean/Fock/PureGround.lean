/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Pure
import FermionicLean.Fock.Thermal

/-! # Pure covariances are ground covariances (G4, Package B)

For a pure covariance `Γ`, the quadratic Hamiltonian `H_{-Γ}` has ground energy `-n/2`, every
density operator of that energy is the Gaussian state with covariance `Γ`, and the
covariance-level energy form is bounded below by `-n/2` with equality only at `Γ`
(`groundState_of_isPure`). The sign: `-Γ` has a normal form `O D(ε) Oᵀ` with `|ε_j| = 1`, and
the ground covariance `O D(-sgn ε) Oᵀ = -O D(ε) Oᵀ = Γ`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

lemma sgn'_eq_self_of_abs_eq_one {t : ℝ} (h : |t| = 1) : sgn' t = t := by
  unfold sgn'
  rcases abs_eq (zero_le_one' ℝ) |>.mp h with h1 | h1
  · rw [h1]; simp
  · rw [h1]; simp

/-- The ground energy of a block form with all `|ε_j| = 1` is `-n/2`. -/
lemma groundEnergy_of_abs_eq_one {ε : Fin n → ℝ} (h : ∀ j, |ε j| = 1) :
    groundEnergy ε = -(n / 2 : ℝ) := by
  unfold groundEnergy
  simp [h]
  ring

/-- `D(-sgn ε) = -D(ε)` when every `|ε_j| = 1`. -/
lemma blockForm_neg_sgn_of_abs_eq_one {ε : Fin n → ℝ} (h : ∀ j, |ε j| = 1) :
    blockForm (fun j => -sgn' (ε j)) = -blockForm ε := by
  rw [← blockForm_neg]
  congr 1
  funext j
  simp [sgn'_eq_self_of_abs_eq_one (h j)]

/-- Theorem 7: for pure `Γ`, `H_{-Γ}` has ground energy `-n/2`; its ground state is the Gaussian
state with covariance `Γ`, unique among all density operators of that energy; and the
covariance-level energy form is `≥ -n/2` on admissible matrices, with equality iff `Γ' = Γ`. -/
theorem groundState_of_isPure {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsPure Γ) :
    ∃ ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsGaussian ρ₀ ∧ covariance ρ₀ = Γ ∧ energy (-Γ) ρ₀ = -(n / 2 : ℝ) ∧
      (∀ ρ, IsDensity ρ → -(n / 2 : ℝ) ≤ energy (-Γ) ρ) ∧
      (∀ ρ, IsDensity ρ → energy (-Γ) ρ = -(n / 2 : ℝ) → ρ = ρ₀) ∧
      (∀ Γ', IsAdmissible Γ' → -(n / 2 : ℝ) ≤ energyForm (-Γ) Γ') ∧
      (∀ Γ', IsAdmissible Γ' → (energyForm (-Γ) Γ' = -(n / 2 : ℝ) ↔ Γ' = Γ)) := by
  have hneg : IsPure (-Γ) := by
    refine ⟨by rw [Matrix.transpose_neg, hΓ.1, neg_neg], ?_⟩
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hΓ.2]
  obtain ⟨O, ε, hO, hdet, hOε⟩ := exists_normalForm_special (-Γ) hneg.1
  have hε : ∀ j, |ε j| = 1 := abs_eq_one_of_isPure_normalForm hO hOε hneg
  have hε0 : ∀ j, ε j ≠ 0 := fun j h0 => by simpa [h0] using hε j
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  obtain ⟨hge, hdens, henergy, hcov, -⟩ := groundState_of_normalForm hO hOε hU hU' hUO
  obtain ⟨huniq, hform, hformiff⟩ := groundState_unique_of_normalForm hO hOε hU hU' hUO hε0
  have hcovΓ : covariance (groundState U ε) = Γ := by
    rw [hcov, blockForm_neg_sgn_of_abs_eq_one hε, Matrix.mul_neg, Matrix.neg_mul, ← hOε, neg_neg]
  have hE := groundEnergy_of_abs_eq_one hε
  refine ⟨groundState U ε, isGaussian_pure hU hU' hUO _, hcovΓ, by rw [henergy, hE],
    fun ρ hρ => hE ▸ hge ρ hρ, fun ρ hρ heq => huniq ρ hρ (by rw [heq, hE]),
    fun Γ' hΓ' => hE ▸ hform Γ' hΓ', fun Γ' hΓ' => ?_⟩
  rw [← hE, hformiff Γ' hΓ', hcovΓ]

/-- Theorem 7, uniqueness form: a Gaussian state with pure covariance `Γ` is the ground state of
`H_{-Γ}`: its energy is `-n/2` and every density operator of that energy equals it. -/
theorem eq_of_energy_neg_eq_of_isPure {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ρ₀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ₀ : IsGaussian ρ₀)
    (hcov : covariance ρ₀ = Γ) (hΓ : IsPure Γ) (hρ : IsDensity ρ)
    (heq : energy (-Γ) ρ = -(n / 2 : ℝ)) : ρ = ρ₀ := by
  obtain ⟨ρ₁, hρ₁, hcov₁, -, -, huniq, -, -⟩ := groundState_of_isPure hΓ
  rw [huniq ρ hρ heq]
  exact (hρ₀.eq_of_covariance_eq hρ₁ (by rw [hcov, hcov₁])).symm

theorem energy_neg_eq_of_isPure {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ₀ : IsGaussian ρ₀)
    (hcov : covariance ρ₀ = Γ) (hΓ : IsPure Γ) : energy (-Γ) ρ₀ = -(n / 2 : ℝ) := by
  obtain ⟨ρ₁, hρ₁, hcov₁, hE, -, -, -, -⟩ := groundState_of_isPure hΓ
  rw [hρ₀.eq_of_covariance_eq hρ₁ (by rw [hcov, hcov₁]), hE]

end Fermionic
