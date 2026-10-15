/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Pure

/-! # Purity of the chain state (G4, Corollary 5)

For pure on-site covariances the periodic input is pure, the bond is pure, so the chain
state is a projection and its covariance, the periodic covariance of F3b, is pure. This is
the statement deferred in F3b and F4. (`pure_blockDiagonal_iff` is F5's, in `Chain/Product`.)
-/

open Matrix

namespace Fermionic

variable {N M P : ℕ}

/-- The periodic input of pure on-site covariances is pure. -/
theorem pure_periodicInput_iff (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Pure (periodicInput Γ) ↔ ∀ i, Pure (Γ i) := by
  unfold periodicInput
  rw [pure_submatrix_equiv_iff, pure_submatrix_equiv_iff, pure_blockDiagonal_iff]

theorem isPure_inputCov {Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ}
    (hΓ : ∀ i, Pure (Γ i)) : IsPure (inputCov N M P Γ) := by
  rw [isPure_iff_pure, inputCov, pure_submatrix_equiv_iff]
  exact (pure_periodicInput_iff Γ).mpr hΓ

theorem isPure_bondCov : IsPure (bondCov N M) := by
  rw [isPure_iff_pure, bondCov, pure_submatrix_equiv_iff]
  exact pure_bond

variable (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) (hΓ : ∀ i, Admissible (Γ i))

/-- Corollary 5: the chain state of pure on-site covariances is a projection. -/
theorem chainState_mul_self_of_forall_pure (hpure : ∀ i, Pure (Γ i))
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    chainState Γ hΓ * chainState Γ hΓ = chainState Γ hΓ :=
  contractState_mul_self_of_isPure (isGaussian_inputState Γ hΓ) isGaussian_bondStateN
    (by rw [covariance_inputState]; exact isPure_inputCov hpure)
    (by rw [covariance_bondStateN]; exact isPure_bondCov) (isUnit_det_chain Γ hΓ hinv)

/-- Corollary 5: the periodic covariance of pure on-site covariances is pure (the statement
deferred in F3b and F4). -/
theorem pure_periodicCovariance_of_forall_pure (hpure : ∀ i, Pure (Γ i))
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    Pure (periodicCovariance Γ) := by
  have hadm : ∀ i, Admissible (Γ i) := fun i => (hpure i).admissible
  have h := (isGaussian_chainState Γ hadm hinv).isPure_covariance_of_mul_self
    (chainState_mul_self_of_forall_pure Γ hadm hpure hinv)
  rw [covariance_chainState Γ hadm hinv, isPure_iff_pure, pure_submatrix_equiv_iff] at h
  exact h

end Fermionic
