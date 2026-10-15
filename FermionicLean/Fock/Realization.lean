/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.NormalForm
import FermionicLean.Fock.Spin
import FermionicLean.Fock.GroundState
import FermionicLean.Fock.Mixture

/-! # Realization of covariances and ground states of quadratic Hamiltonians

Every admissible covariance is the covariance of a density operator, and every pure covariance
that of a pure state (Theorem 17): write `Γ = O D(ε) Oᵀ` with `det O = 1`, implement `O` by a
unitary `U`, and take `Uᴴ ρ_ε U` with `ρ_ε` the product mixture. The ground state of every
quadratic Hamiltonian is a pure Gaussian state with the covariance `O D(-sgn ε) Oᵀ` and energy
`-(1/2) ∑ |ε_j|` (Theorem 18), and a pure covariance determines its state (Corollary 19).
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### Theorem 17 -/

/-- The realizing state of an admissible covariance, given its normal form and an implementing
unitary: `Uᴴ ρ_ε U`. -/
noncomputable def realization (U : Matrix (FockIndex n) (FockIndex n) ℂ) (ε : Fin n → ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  U.conjTranspose * productMixture ε * U

/-- Theorem 17, explicit form: for `Γ = O D(ε) Oᵀ` admissible and `U` implementing `O`,
`Uᴴ ρ_ε U` is a density operator with covariance `Γ`. -/
theorem isDensity_realization_and_covariance {U : Matrix (FockIndex n) (FockIndex n) ℂ}
    {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {ε : Fin n → ℝ}
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1) (hUO : ConjugatesMajorana U O)
    (hO : O * O.transpose = 1) (hΓ : Γ = O * blockForm ε * O.transpose) (hadm : IsAdmissible Γ) :
    IsDensity (realization U ε) ∧ covariance (realization U ε) = Γ := by
  have hε := abs_le_one_of_isAdmissible_normalForm hO hΓ hadm
  have h := covariance_conj' hU hU' hUO (isDensity_productMixture hε)
  refine ⟨h.1, ?_⟩
  unfold realization
  rw [h.2, covariance_productMixture, hΓ]

/-- Theorem 17: every admissible matrix is the covariance of a density operator. -/
theorem exists_isDensity_covariance_eq (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsAdmissible Γ) : ∃ ρ : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsDensity ρ ∧ covariance ρ = Γ := by
  obtain ⟨O, ε, hO, hdet, h⟩ := exists_normalForm_special Γ hΓ.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  exact ⟨realization U ε, isDensity_realization_and_covariance hU hU' hUO hO h hΓ⟩

/-- Theorem 17: a pure covariance is the covariance of a pure state `Uᴴ |s⟩⟨s| U`. -/
theorem exists_pure_state_of_isPure (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsPure Γ) : ∃ (U : Matrix (FockIndex n) (FockIndex n) ℂ) (s : FockIndex n),
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧
      IsDensity (U.conjTranspose * occupation s * U) ∧
      covariance (U.conjTranspose * occupation s * U) = Γ := by
  obtain ⟨O, ε, hO, hdet, h⟩ := exists_normalForm_special Γ hΓ.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  have hε := abs_eq_one_of_isPure_normalForm hO h hΓ
  have hmix := productMixture_of_abs_eq_one hε
  have hres := isDensity_realization_and_covariance hU hU' hUO hO h hΓ.isAdmissible
  refine ⟨U, fun j => if ε j = 1 then 1 else 0, hU, hU', ?_, ?_⟩
  · have := hres.1; unfold realization at this; rwa [hmix] at this
  · have := hres.2; unfold realization at this; rwa [hmix] at this

/-! ### Theorem 18 -/

/-- Theorem 18: every real antisymmetric `h` has a special-orthogonal normal form
`h = O D(ε) Oᵀ` and an implementing unitary `U`. -/
theorem exists_normalForm_unitary (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) :
    ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ)
      (U : Matrix (FockIndex n) (FockIndex n) ℂ),
      O * O.transpose = 1 ∧ O.det = 1 ∧ h = O * blockForm ε * O.transpose ∧
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ConjugatesMajorana U O := by
  obtain ⟨O, ε, hO, hdet, hOε⟩ := exists_normalForm_special h hh
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  exact ⟨O, ε, U, hO, hdet, hOε, hU, hU', hUO⟩

/-- Theorem 18(a): for every such choice, `Tr(ρ H_h) ≥ E_0(ε)` for every density operator, the
pure state `ρ₀ = Uᴴ |s^ε⟩⟨s^ε| U` attains it, and its covariance `O D(-sgn ε) Oᵀ` is pure. -/
theorem groundState_of_normalForm {h O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} {U : Matrix (FockIndex n) (FockIndex n) ℂ} (hO : O * O.transpose = 1)
    (hOε : h = O * blockForm ε * O.transpose) (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hUO : ConjugatesMajorana U O) :
    (∀ ρ, IsDensity ρ → groundEnergy ε ≤ energy h ρ) ∧
    IsDensity (groundState U ε) ∧ energy h (groundState U ε) = groundEnergy ε ∧
    covariance (groundState U ε) = O * blockForm (fun j => -sgn' (ε j)) * O.transpose ∧
    IsPure (covariance (groundState U ε)) := by
  subst hOε
  refine ⟨fun ρ hρ => groundEnergy_le_energy hU hU' hUO hO hρ, isDensity_groundState hU hU' hUO,
    energy_groundState hU hU' hUO hO, covariance_groundState hU hU' hUO, ?_⟩
  rw [covariance_groundState hU hU' hUO]
  apply isPure_orthogonalCongruence hO
  rw [isPure_blockForm_iff]
  intro j
  unfold sgn'
  split_ifs <;> simp

/-- Theorem 18(b): with no zero `ε_j`, the minimizing density operator is unique, and the
minimizing admissible covariance is unique and equals `Γ(ρ₀)`. -/
theorem groundState_unique_of_normalForm {h O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} {U : Matrix (FockIndex n) (FockIndex n) ℂ} (hO : O * O.transpose = 1)
    (hOε : h = O * blockForm ε * O.transpose) (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hUO : ConjugatesMajorana U O) (hε : ∀ j, ε j ≠ 0) :
    (∀ ρ, IsDensity ρ → energy h ρ = groundEnergy ε → ρ = groundState U ε) ∧
    (∀ Γ, IsAdmissible Γ → groundEnergy ε ≤ energyForm h Γ) ∧
    (∀ Γ, IsAdmissible Γ →
      (energyForm h Γ = groundEnergy ε ↔ Γ = covariance (groundState U ε))) := by
  subst hOε
  refine ⟨fun ρ hρ heq => eq_groundState_of_energy_eq hU hU' hUO hO hε hρ heq,
    fun Γ hΓ => groundEnergy_le_energyForm hO hΓ, fun Γ hΓ => ?_⟩
  rw [energyForm_eq_groundEnergy_iff hO hΓ hε, covariance_groundState hU hU' hUO]

/-- Theorem 18, existence form: every quadratic Hamiltonian has a pure Gaussian ground state. -/
theorem exists_groundState (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) :
    ∃ ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ, IsDensity ρ₀ ∧ IsPure (covariance ρ₀) ∧
      ∀ ρ, IsDensity ρ → energy h ρ₀ ≤ energy h ρ := by
  obtain ⟨O, ε, U, hO, -, hOε, hU, hU', hUO⟩ := exists_normalForm_unitary h hh
  obtain ⟨hge, hdens, henergy, -, hpure⟩ := groundState_of_normalForm hO hOε hU hU' hUO
  exact ⟨groundState U ε, hdens, hpure, fun ρ hρ => henergy ▸ hge ρ hρ⟩

/-! ### Corollary 19 -/

/-- Corollary 19: a density operator with a pure covariance `O D(η) Oᵀ` (`U` implementing `O`)
is the pure state `Uᴴ |s⟩⟨s| U` with `s_j = 1` iff `η_j = 1`. -/
theorem eq_of_covariance_eq_pure_normalForm {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {η : Fin n → ℝ}
    {U : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsDensity ρ) (hO : O * O.transpose = 1)
    (hη : ∀ j, |η j| = 1) (hcov : covariance ρ = O * blockForm η * O.transpose)
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hUO : ConjugatesMajorana U O) :
    ρ = U.conjTranspose * occupation (fun j => if η j = 1 then 1 else 0) * U := by
  -- the Hamiltonian `h = O D(-η) Oᵀ` has ground energy `-n/2`, attained by `ρ`
  have hε : ∀ j, -η j ≠ 0 := fun j h => by
    have := hη j; rw [neg_eq_zero.mp h] at this; simp at this
  have hconfig : groundConfig (fun j => -η j) = fun j => if η j = 1 then 1 else 0 := by
    funext j
    unfold groundConfig
    have := hη j
    rcases abs_eq (zero_le_one' ℝ) |>.mp this with h1 | h1 <;> norm_num [h1]
  have hsgn : (fun j => -sgn' (-η j)) = η := by
    funext j
    unfold sgn'
    have := hη j
    rcases abs_eq (zero_le_one' ℝ) |>.mp this with h1 | h1 <;> norm_num [h1]
  have henergy : energy (O * blockForm (fun j => -η j) * O.transpose) ρ =
      groundEnergy fun j => -η j := by
    rw [energy_eq_energyForm (orthogonalCongruence_transpose (blockForm_transpose _)) hρ.1.1,
      hcov, (energyForm_eq_groundEnergy_iff hO
        (isAdmissible_orthogonalCongruence hO ((isAdmissible_blockForm_iff η).mpr
          fun j => (hη j).le)) hε).mpr]
    rw [hsgn]
  have := eq_groundState_of_energy_eq hU hU' hUO hO hε hρ henergy
  rw [this]
  unfold groundState
  rw [hconfig]

/-- Corollary 19: two density operators with the same pure covariance are equal. -/
theorem eq_of_covariance_eq_of_isPure {ρ σ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hpure : IsPure (covariance ρ))
    (heq : covariance ρ = covariance σ) : ρ = σ := by
  obtain ⟨O, η, hO, hdet, hcov⟩ := exists_normalForm_special (covariance ρ) hpure.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  have hη := abs_eq_one_of_isPure_normalForm hO hcov hpure
  rw [eq_of_covariance_eq_pure_normalForm hρ hO hη hcov hU hU' hUO,
    eq_of_covariance_eq_pure_normalForm hσ hO hη (heq ▸ hcov) hU hU' hUO]

end Fermionic
