/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Admissible
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Contraction of a covariance with a bond

For `Γ = fromBlocks A B C D` on retained ⊕ eliminated labels and a bond `Γp` on the
eliminated labels, the contraction is `A + B Γp (1 - D Γp)⁻¹ C`. It is meaningful
when `1 - D Γp` is invertible; the inverse is Mathlib's, which is `0` otherwise.
-/

open Matrix

namespace Fermionic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Definition 1: the star-product contraction. -/
noncomputable def contract (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Γp : Matrix κ κ ℝ) :
    Matrix ι ι ℝ :=
  Γ.toBlocks₁₁ + Γ.toBlocks₁₂ * Γp * (1 - Γ.toBlocks₂₂ * Γp)⁻¹ * Γ.toBlocks₂₁

/-- The eliminated-block condition of the contraction. -/
def ContractInvertible (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Γp : Matrix κ κ ℝ) : Prop :=
  IsUnit (1 - Γ.toBlocks₂₂ * Γp).det

end Fermionic
