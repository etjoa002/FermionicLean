/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.PureGround
import FermionicLean.Chain.Pure
import FermionicLean.Chain.Kitaev

/-! # The Kitaev chain state (G4, Package B)

The chain state of F3b with the Kitaev on-site covariance at every site is a Gaussian state
on `N` physical modes whose covariance is the Kitaev chain covariance `K_N` of G3, relabelled
to Majorana labels. Since `K_N` is pure, the state is a projection, and by Package A it is the
unique ground state of the quadratic Hamiltonian `H_{-K_N}`, which is the Kitaev chain
Hamiltonian at its solvable point, `(i/2) ∑_i c_{x_{i+1}} c_{y_i}` (Definition 9, Lemma 10,
Theorem 12).
-/

open Matrix

namespace Fermionic

variable {N : ℕ}

/-! ### The Kitaev covariance and Hamiltonian on Majorana labels -/

/-- The Kitaev chain covariance `K_N` on the Majorana labels of `N * 1` modes. -/
def kitaevCov (N : ℕ) : Matrix (MajoranaIndex (N * 1)) (MajoranaIndex (N * 1)) ℝ :=
  (kitaevChain N).submatrix (retainedModeEquiv N 1).symm (retainedModeEquiv N 1).symm

theorem isPure_kitaevCov : IsPure (kitaevCov N) := by
  rw [isPure_iff_pure, kitaevCov, pure_submatrix_equiv_iff]
  exact pure_kitaevChain

/-- Definition 9: the Kitaev chain Hamiltonian `H_{-K_N}`. -/
noncomputable def kitaevHam (N : ℕ) : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ :=
  quadHam (-(kitaevCov N))

/-- The Majorana label `x_i` of site `i`. -/
def kitaevX (i : Fin N) : MajoranaIndex (N * 1) := Sum.inl (siteModeEquiv N 1 (i, 0))

/-- The Majorana label `y_i` of site `i`. -/
def kitaevY (i : Fin N) : MajoranaIndex (N * 1) := Sum.inr (siteModeEquiv N 1 (i, 0))

lemma kitaevX_ne_kitaevY (i j : Fin N) : kitaevX i ≠ kitaevY j := Sum.inl_ne_inr

lemma retainedModeEquiv_inl (i : Fin N) (c : Fin 1) :
    retainedModeEquiv N 1 (Sum.inl (i, c)) = kitaevX i := by
  rw [Fin.eq_zero c]; rfl

lemma retainedModeEquiv_inr (i : Fin N) (c : Fin 1) :
    retainedModeEquiv N 1 (Sum.inr (i, c)) = kitaevY i := by
  rw [Fin.eq_zero c]; rfl

/-! #### The coefficients of `H_{-K_N}` -/

lemma hamCoeff_kitaev_apply (r r' : Retained N 1) :
    hamCoeff (-(kitaevCov N)) (retainedModeEquiv N 1 r) (retainedModeEquiv N 1 r') =
      -(Complex.I / 4) * (kitaevChain N r r' : ℂ) := by
  simp only [hamCoeff, kitaevCov, Matrix.neg_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Complex.ofReal_neg]
  ring

lemma hamCoeff_kitaev_x_x (i j : Fin N) :
    hamCoeff (-(kitaevCov N)) (kitaevX i) (kitaevX j) = 0 := by
  rw [← retainedModeEquiv_inl i 0, ← retainedModeEquiv_inl j 0, hamCoeff_kitaev_apply]
  simp [kitaevChain]

lemma hamCoeff_kitaev_y_y (i j : Fin N) :
    hamCoeff (-(kitaevCov N)) (kitaevY i) (kitaevY j) = 0 := by
  rw [← retainedModeEquiv_inr i 0, ← retainedModeEquiv_inr j 0, hamCoeff_kitaev_apply]
  simp [kitaevChain]

lemma hamCoeff_kitaev_x_y (j i : Fin N) :
    hamCoeff (-(kitaevCov N)) (kitaevX j) (kitaevY i) =
      if j = finRotate N i then Complex.I / 4 else 0 := by
  rw [← retainedModeEquiv_inl j 0, ← retainedModeEquiv_inr i 0, hamCoeff_kitaev_apply]
  simp only [kitaevChain, Matrix.of_apply]
  split_ifs <;> simp

lemma hamCoeff_kitaev_y_x (i j : Fin N) :
    hamCoeff (-(kitaevCov N)) (kitaevY i) (kitaevX j) =
      if j = finRotate N i then -(Complex.I / 4) else 0 := by
  rw [← retainedModeEquiv_inr i 0, ← retainedModeEquiv_inl j 0, hamCoeff_kitaev_apply]
  simp only [kitaevChain, Matrix.of_apply]
  split_ifs <;> simp

/-- Lemma 10: `H_{-K_N} = (i/2) ∑_i c_{x_{i+1}} c_{y_i}`. -/
theorem kitaevHam_eq :
    kitaevHam N = ∑ i : Fin N,
      (Complex.I / 2) • (majorana (kitaevX (finRotate N i)) * majorana (kitaevY i)) := by
  unfold kitaevHam quadHam
  rw [← Equiv.sum_comp (retainedModeEquiv N 1)]
  simp_rw [← Equiv.sum_comp (retainedModeEquiv N 1)
    (fun b => hamCoeff (-(kitaevCov N)) _ b • (majorana _ * majorana b))]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one,
    retainedModeEquiv_inl, retainedModeEquiv_inr]
  simp only [hamCoeff_kitaev_x_x, hamCoeff_kitaev_y_y, hamCoeff_kitaev_x_y,
    hamCoeff_kitaev_y_x, zero_smul, Finset.sum_const_zero, zero_add, add_zero, ite_smul,
    Fintype.sum_ite_eq']
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : majorana (kitaevX (finRotate N i)) * majorana (kitaevY i) +
      majorana (kitaevY i) * majorana (kitaevX (finRotate N i)) = 0 := by
    simpa [kitaevX_ne_kitaevY] using majorana_anticommute (kitaevX (finRotate N i)) (kitaevY i)
  rw [eq_neg_of_add_eq_zero_right h, smul_neg, neg_smul, neg_neg, ← add_smul]
  congr 1
  ring

/-! ### The Kitaev chain state -/

/-- The chain state with the Kitaev on-site covariance at every site. -/
noncomputable def kitaevState (N : ℕ) : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ :=
  chainState (fun _ : Fin N => kitaevLocal) (fun _ => admissible_kitaevLocal)

/-- Theorem 12: `-N/2` is the ground energy of `H_{-K_N}`. -/
theorem energy_kitaevHam_ge {ρ : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ}
    (hρ : IsDensity ρ) : -(((N * 1 : ℕ) : ℝ) / 2) ≤ energy (-(kitaevCov N)) ρ := by
  obtain ⟨-, -, -, -, hge, -, -, -⟩ := groundState_of_isPure (isPure_kitaevCov (N := N))
  exact hge ρ hρ

variable [NeZero N]

/-- Theorem 12: the covariance of the Kitaev chain state is `K_N`. -/
theorem covariance_kitaevState : covariance (kitaevState N) = kitaevCov N := by
  rw [kitaevState, covariance_chainState _ _ kitaev_contractInvertible,
    periodicCovariance_kitaev, kitaevCov]

theorem isGaussian_kitaevState : IsGaussian (kitaevState N) :=
  isGaussian_chainState _ _ kitaev_contractInvertible

/-- Theorem 12: the Kitaev chain state is a projection. -/
theorem kitaevState_mul_self : kitaevState N * kitaevState N = kitaevState N :=
  isGaussian_kitaevState.mul_self_of_isPure
    (by rw [covariance_kitaevState]; exact isPure_kitaevCov)

/-- Theorem 12: the Kitaev chain state has energy `-N/2` for `H_{-K_N}`. -/
theorem energy_kitaevState :
    energy (-(kitaevCov N)) (kitaevState N) = -(((N * 1 : ℕ) : ℝ) / 2) :=
  energy_neg_eq_of_isPure isGaussian_kitaevState covariance_kitaevState isPure_kitaevCov

theorem energy_kitaevState' : energy (-(kitaevCov N)) (kitaevState N) = -((N : ℝ) / 2) := by
  rw [energy_kitaevState]; simp

/-- Theorem 12: the Kitaev chain state is the unique ground state of `H_{-K_N}`. -/
theorem eq_kitaevState_of_energy_eq {ρ : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ}
    (hρ : IsDensity ρ) (h : energy (-(kitaevCov N)) ρ = -(((N * 1 : ℕ) : ℝ) / 2)) :
    ρ = kitaevState N :=
  eq_of_energy_neg_eq_of_isPure isGaussian_kitaevState covariance_kitaevState isPure_kitaevCov
    hρ h

end Fermionic
