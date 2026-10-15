/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Basic

/-! # Contraction against a pure pair covariance

For a pure `Γp` (`Γpᵀ = -Γp`, `Γp² = -1`) and `1 - D Γp` invertible, `Γp + D` is
invertible and `Γp (1 - D Γp)⁻¹ = -(Γp + D)⁻¹`, because `(D + Γp)(-Γp) = 1 - D Γp`.
-/

open Matrix

namespace Fermionic

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a pure pair covariance with `1 - D Γp` invertible, `Γp + D` is invertible. -/
theorem isUnit_det_add_of_pure {D Γp : Matrix κ κ ℝ} (hp : Pure Γp)
    (hinv : IsUnit (1 - D * Γp).det) : IsUnit (Γp + D).det := by
  rw [← add_mul_neg_of_pure hp, Matrix.det_mul, IsUnit.mul_iff] at hinv
  rw [add_comm]
  exact hinv.1

/-- For a pure pair covariance, `Γp (1 - D Γp)⁻¹ = -(Γp + D)⁻¹`. -/
theorem mul_inv_one_sub_mul_eq_neg_inv_add_of_pure {D Γp : Matrix κ κ ℝ} (hp : Pure Γp)
    (hinv : IsUnit (1 - D * Γp).det) : Γp * (1 - D * Γp)⁻¹ = -(Γp + D)⁻¹ := by
  rw [eq_neg_iff_add_eq_zero, ← neg_eq_iff_add_eq_zero]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.neg_mul, add_comm, ← Matrix.mul_assoc, add_mul_neg_of_pure hp,
    Matrix.mul_nonsing_inv _ hinv]

end Fermionic
