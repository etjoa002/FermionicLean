/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Admissible

/-! # Orthogonal congruence

A real orthogonal change of Majorana basis preserves admissibility and purity.
-/

open Matrix

namespace Fermionic

variable {n : ℕ} {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

lemma transpose_mul_self_of_mul_transpose (hO : O * O.transpose = 1) :
    O.transpose * O = 1 :=
  mul_eq_one_comm.mp hO

lemma orthogonalCongruence_transpose (hΓ : Γ.transpose = -Γ) :
    (O * Γ * O.transpose).transpose = -(O * Γ * O.transpose) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hΓ,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-- Theorem 4 (orthogonal congruence), admissibility. -/
theorem isAdmissible_orthogonalCongruence (hO : O * O.transpose = 1)
    (hΓ : IsAdmissible Γ) : IsAdmissible (O * Γ * O.transpose) := by
  refine ⟨orthogonalCongruence_transpose hΓ.1, ?_⟩
  have hOtO := transpose_mul_self_of_mul_transpose hO
  have hcong : 1 - (O * Γ * O.transpose).transpose * (O * Γ * O.transpose) =
      O * (1 - Γ.transpose * Γ) * O.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hO]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul]
  rw [hcong]
  have := hΓ.2.mul_mul_conjTranspose_same O
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- Theorem 4 (orthogonal congruence), purity. -/
theorem isPure_orthogonalCongruence (hO : O * O.transpose = 1)
    (hΓ : IsPure Γ) : IsPure (O * Γ * O.transpose) := by
  refine ⟨orthogonalCongruence_transpose hΓ.1, ?_⟩
  have hOtO := transpose_mul_self_of_mul_transpose hO
  have : O * Γ * O.transpose * (O * Γ * O.transpose) = O * (Γ * Γ) * O.transpose := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul]
  rw [this, hΓ.2, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hO]

end Fermionic
