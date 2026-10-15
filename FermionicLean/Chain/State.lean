/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.GaussianMap
import FermionicLean.Chain.Product

/-! # The chain state

The periodic chain of F3b is a covariance `Γ_N = Γ_in ⋆ β_N` on the labels of `N * P` physical
modes, obtained by contracting the periodic input `Γ_in` (on the physical and virtual labels)
with the bond `β_N` (on the virtual labels). On Fock space, the input state is the Gaussian
state with covariance `Γ_in` and the bond state the Gaussian state with covariance `β_N`
(unique by G2); their contraction is a Gaussian state with covariance `Γ_N` (G3, Theorem 15).
The physical modes are the first `N * P` modes and the virtual modes the last `2 N M`.
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

/-! ### The Gaussian state with a given admissible covariance -/

/-- Every admissible covariance is the covariance of a Gaussian state (F6, Theorem 17 with
G2, Corollary 10). -/
theorem exists_isGaussian_covariance_eq {n : ℕ}
    (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (hΓ : IsAdmissible Γ) :
    ∃ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, IsGaussian ρ ∧ covariance ρ = Γ := by
  obtain ⟨O, ε, hO, hdet, h⟩ := exists_normalForm_special Γ hΓ.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hO hdet
  have hε := abs_le_one_of_isAdmissible_normalForm hO h hΓ
  exact ⟨realization U ε, isGaussian_realization hU hU' hUO hε,
    (isDensity_realization_and_covariance hU hU' hUO hO h hΓ).2⟩

/-- The Gaussian state with covariance `Γ`. -/
noncomputable def gaussianOf {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsAdmissible Γ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  Classical.choose (exists_isGaussian_covariance_eq Γ hΓ)

theorem isGaussian_gaussianOf {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsAdmissible Γ) : IsGaussian (gaussianOf Γ hΓ) :=
  (Classical.choose_spec (exists_isGaussian_covariance_eq Γ hΓ)).1

theorem covariance_gaussianOf {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsAdmissible Γ) : covariance (gaussianOf Γ hΓ) = Γ :=
  (Classical.choose_spec (exists_isGaussian_covariance_eq Γ hΓ)).2

/-! ### Relabelling the chain -/

variable (N M P : ℕ)

/-- The virtual modes `L ⊕ L`, `L = Fin N × Fin M`, as `N M + N M` modes. -/
def virtualModeEquiv : (Fin N × Fin M) ⊕ (Fin N × Fin M) ≃ Fin (N * M + N * M) :=
  (Equiv.sumCongr (siteModeEquiv N M) (siteModeEquiv N M)).trans finSumFinEquiv

/-- The eliminated labels of the chain as Majorana labels of `N M + N M` modes. -/
def eliminatedModeEquiv : Eliminated N M ≃ MajoranaIndex (N * M + N * M) :=
  Equiv.sumCongr (virtualModeEquiv N M) (virtualModeEquiv N M)

/-- All labels of the chain as Majorana labels of `N P + (N M + N M)` modes, physical first. -/
def chainLabelEquiv :
    Retained N P ⊕ Eliminated N M ≃ MajoranaIndex (N * P + (N * M + N * M)) :=
  (Equiv.sumCongr (retainedModeEquiv N P) (eliminatedModeEquiv N M)).trans
    (labelSplit (N * P) (N * M + N * M)).symm

/-- The periodic input covariance on the Majorana labels of the chain. -/
def inputCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Matrix (MajoranaIndex (N * P + (N * M + N * M)))
      (MajoranaIndex (N * P + (N * M + N * M))) ℝ :=
  (periodicInput Γ).submatrix (chainLabelEquiv N M P).symm (chainLabelEquiv N M P).symm

/-- The bond covariance on the Majorana labels of the virtual modes. -/
def bondCov : Matrix (MajoranaIndex (N * M + N * M)) (MajoranaIndex (N * M + N * M)) ℝ :=
  (periodicBond N M).submatrix (eliminatedModeEquiv N M).symm (eliminatedModeEquiv N M).symm

variable {N M P}

lemma isAdmissible_inputCov {Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ}
    (hΓ : ∀ i, Admissible (Γ i)) : IsAdmissible (inputCov N M P Γ) := by
  rw [isAdmissible_iff_admissible, inputCov, admissible_submatrix_equiv_iff,
    admissible_periodicInput_iff]
  exact hΓ

lemma isAdmissible_bondCov : IsAdmissible (bondCov N M) := by
  rw [isAdmissible_iff_admissible, bondCov, admissible_submatrix_equiv_iff]
  exact pure_bond.admissible

lemma chainLabelEquiv_symm_embedR (a : MajoranaIndex (N * P)) :
    (chainLabelEquiv N M P).symm (embedR a) = Sum.inl ((retainedModeEquiv N P).symm a) := by
  simp [chainLabelEquiv, embedR]

lemma chainLabelEquiv_symm_embedE (e : MajoranaIndex (N * M + N * M)) :
    (chainLabelEquiv N M P).symm (embedE e) = Sum.inr ((eliminatedModeEquiv N M).symm e) := by
  simp [chainLabelEquiv, embedE]

/-- The blocks of the relabelled input are the relabelled blocks. -/
lemma blockR_inputCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    blockR (inputCov N M P Γ) =
      (periodicInput Γ).toBlocks₁₁.submatrix (retainedModeEquiv N P).symm
        (retainedModeEquiv N P).symm := by
  ext a b
  simp [blockR, inputCov, Matrix.toBlocks₁₁, chainLabelEquiv_symm_embedR]

lemma blockRE_inputCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    blockRE (inputCov N M P Γ) =
      (periodicInput Γ).toBlocks₁₂.submatrix (retainedModeEquiv N P).symm
        (eliminatedModeEquiv N M).symm := by
  ext a b
  simp [blockRE, inputCov, Matrix.toBlocks₁₂, chainLabelEquiv_symm_embedR,
    chainLabelEquiv_symm_embedE]

lemma blockER_inputCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    blockER (inputCov N M P Γ) =
      (periodicInput Γ).toBlocks₂₁.submatrix (eliminatedModeEquiv N M).symm
        (retainedModeEquiv N P).symm := by
  ext a b
  simp [blockER, inputCov, Matrix.toBlocks₂₁, chainLabelEquiv_symm_embedR,
    chainLabelEquiv_symm_embedE]

lemma blockE_inputCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    blockE (inputCov N M P Γ) =
      (periodicInput Γ).toBlocks₂₂.submatrix (eliminatedModeEquiv N M).symm
        (eliminatedModeEquiv N M).symm := by
  ext a b
  simp [blockE, inputCov, Matrix.toBlocks₂₂, chainLabelEquiv_symm_embedE]

lemma one_sub_blockE_mul_bondCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    1 - blockE (inputCov N M P Γ) * bondCov N M =
      (1 - (periodicInput Γ).toBlocks₂₂ * periodicBond N M).submatrix
        (eliminatedModeEquiv N M).symm (eliminatedModeEquiv N M).symm := by
  rw [blockE_inputCov, bondCov, Matrix.submatrix_mul_equiv]
  ext a b
  simp [Matrix.one_apply, (eliminatedModeEquiv N M).symm.injective.eq_iff]

/-- The contraction commutes with the relabelling. -/
lemma contractCov_inputCov_bondCov (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    contractCov (inputCov N M P Γ) (bondCov N M) =
      (periodicCovariance Γ).submatrix (retainedModeEquiv N P).symm
        (retainedModeEquiv N P).symm := by
  rw [contractCov, one_sub_blockE_mul_bondCov, blockR_inputCov, blockRE_inputCov,
    blockER_inputCov, bondCov, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  ext a b
  simp [periodicCovariance, contract]

lemma isUnit_det_inputCov_bondCov_iff (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    IsUnit (1 - blockE (inputCov N M P Γ) * bondCov N M).det ↔
      ContractInvertible (periodicInput Γ) (periodicBond N M) := by
  rw [one_sub_blockE_mul_bondCov, Matrix.det_submatrix_equiv_self]
  rfl

/-! ### The chain state -/

/-- The input state: the Gaussian state with covariance `Γ_in`. -/
noncomputable def inputState (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hΓ : ∀ i, Admissible (Γ i)) :=
  gaussianOf (inputCov N M P Γ) (isAdmissible_inputCov hΓ)

/-- The bond state of the chain: the Gaussian state with covariance `β_N`. -/
noncomputable def bondStateN (N M : ℕ) :=
  gaussianOf (bondCov N M) (isAdmissible_bondCov (N := N) (M := M))

/-- The chain state `Z⁻¹ Tr_E (ρ_in (1 ⊗ σ_N))` on the physical modes. -/
noncomputable def chainState (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hΓ : ∀ i, Admissible (Γ i)) : Matrix (FockIndex (N * P)) (FockIndex (N * P)) ℂ :=
  contractState (inputState Γ hΓ) (bondStateN N M)

variable (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
  (hΓ : ∀ i, Admissible (Γ i))

lemma isGaussian_inputState : IsGaussian (inputState Γ hΓ) := isGaussian_gaussianOf _ _

lemma covariance_inputState : covariance (inputState Γ hΓ) = inputCov N M P Γ :=
  covariance_gaussianOf _ _

lemma isGaussian_bondStateN : IsGaussian (bondStateN N M) := isGaussian_gaussianOf _ _

lemma covariance_bondStateN : covariance (bondStateN N M) = bondCov N M :=
  covariance_gaussianOf _ _

lemma isUnit_det_chain (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    IsUnit (1 - blockE (covariance (inputState Γ hΓ)) * covariance (bondStateN N M)).det := by
  rw [covariance_inputState, covariance_bondStateN, isUnit_det_inputCov_bondCov_iff]
  exact hinv

/-- Theorem 15: the normalization of the chain is positive. -/
theorem normalization_chain_pos (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    0 < normalization (inputState Γ hΓ) (bondStateN N M) :=
  normalization_pos (isGaussian_inputState Γ hΓ) isGaussian_bondStateN
    (isUnit_det_chain Γ hΓ hinv)

/-- Theorem 15: the chain state is Gaussian. -/
theorem isGaussian_chainState (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    IsGaussian (chainState Γ hΓ) :=
  isGaussian_contractState (isGaussian_inputState Γ hΓ) isGaussian_bondStateN
    (isUnit_det_chain Γ hΓ hinv) (normalization_chain_pos Γ hΓ hinv).ne'

/-- Theorem 15: the covariance of the chain state is the periodic covariance `Γ_N`. -/
theorem covariance_chainState (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    covariance (chainState Γ hΓ) =
      (periodicCovariance Γ).submatrix (retainedModeEquiv N P).symm
        (retainedModeEquiv N P).symm := by
  rw [chainState, covariance_contractState (isGaussian_inputState Γ hΓ) isGaussian_bondStateN
    (isUnit_det_chain Γ hΓ hinv) (normalization_chain_pos Γ hΓ hinv).ne', covariance_inputState,
    covariance_bondStateN, contractCov_inputCov_bondCov]

end Fermionic
