/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Defs

/-! # Block elimination inside a determinant

For a matrix `D` on `ι ⊕ κ` and a block-diagonal bond `β = β₁ ⊕ β₂`, eliminating the `κ` block
gives `det (1 - Dβ) = det (1 - D₂₂ β₂) · det (1 - (D ⋆ β₂) β₁)`, where `D ⋆ β₂` is the
contraction of `D` with `β₂` (G3, Lemma 12 in its general form). It is the block determinant
formula around the invertible lower-right block `1 - D₂₂ β₂`.
-/

open Matrix

namespace Fermionic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Lemma 12 (general form): the determinant of `1 - D (β₁ ⊕ β₂)` factors through the
contraction of the `κ` block. -/
theorem det_one_sub_mul_fromBlocks
    (D : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (β₁ : Matrix ι ι ℝ) (β₂ : Matrix κ κ ℝ)
    (h : IsUnit (1 - D.toBlocks₂₂ * β₂).det) :
    (1 - D * Matrix.fromBlocks β₁ 0 0 β₂).det =
      (1 - D.toBlocks₂₂ * β₂).det * (1 - contract D β₂ * β₁).det := by
  have hD : D = Matrix.fromBlocks D.toBlocks₁₁ D.toBlocks₁₂ D.toBlocks₂₁ D.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks D).symm
  have hblock : 1 - D * Matrix.fromBlocks β₁ 0 0 β₂ =
      Matrix.fromBlocks (1 - D.toBlocks₁₁ * β₁) (-(D.toBlocks₁₂ * β₂))
        (-(D.toBlocks₂₁ * β₁)) (1 - D.toBlocks₂₂ * β₂) := by
    conv_lhs => rw [hD]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp only [Matrix.mul_zero, add_zero, zero_add, sub_eq_add_neg]
  let _ := Matrix.invertibleOfIsUnitDet _ h
  rw [hblock, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  unfold contract
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul, Matrix.mul_assoc, sub_sub]

end Fermionic
