/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Defs

/-! # The row-vector system of the contraction theorem

The proof of the contraction theorem (G3, Theorem 9) reduces to three identities between
linear functionals on the eliminated labels, written as row vectors `αE`, `bE` of length `2m`:
(I) `αE (1 + iD) + bE (1 - iD) = 2i y B`, (II) `αE (1 - iβ) = bE (1 + iβ)`, and the quantity
`i (αE - bE) C` entering (III). This file solves (I)–(II) when `1 - Dβ` is invertible:
`i (αE - bE) C = -2i y Bβ (1 - Dβ)⁻¹ C`. The matrices are complex here; the application maps
the real blocks of a covariance.
-/

open Matrix

namespace Fermionic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Push-through: `(1 - βD)⁻¹ β = β (1 - Dβ)⁻¹` when `1 - Dβ` is invertible. -/
lemma inv_one_sub_mul_mul_eq {R : Type*} [CommRing R] (D β : Matrix κ κ R)
    (h : IsUnit (1 - D * β).det) : (1 - β * D)⁻¹ * β = β * (1 - D * β)⁻¹ := by
  have h' : IsUnit (1 - β * D).det := by rwa [Matrix.det_one_sub_mul_comm]
  have key : β * (1 - D * β) = (1 - β * D) * β := by noncomm_ring
  calc (1 - β * D)⁻¹ * β = (1 - β * D)⁻¹ * (β * (1 - D * β)) * (1 - D * β)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc β, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    _ = β * (1 - D * β)⁻¹ := by
        rw [key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h', Matrix.one_mul]

/-- The solution of the system (I)–(II). -/
theorem row_system_solution (D β : Matrix κ κ ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (hinv : IsUnit (1 - D * β).det) (αE bE : κ → ℂ) (y : ι → ℂ)
    (hI : αE ᵥ* (1 + Complex.I • D) + bE ᵥ* (1 - Complex.I • D) =
      (2 * Complex.I) • (y ᵥ* B))
    (hII : αE ᵥ* (1 - Complex.I • β) = bE ᵥ* (1 + Complex.I • β)) :
    Complex.I • ((αE - bE) ᵥ* C) =
      (-(2 * Complex.I)) • (y ᵥ* (B * β * (1 - D * β)⁻¹ * C)) := by
  have hinv' : IsUnit (1 - β * D).det := by rwa [Matrix.det_one_sub_mul_comm]
  set s : κ → ℂ := αE + bE with hs
  -- (II): αE - bE = i (s β)
  have hd : αE - bE = Complex.I • (s ᵥ* β) := by
    funext k
    have h := congrFun hII k
    simp only [Matrix.vecMul_sub, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, Matrix.add_vecMul] at h ⊢
    linear_combination h
  -- (I): s (1 - β D) = 2i y B
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hD : αE ᵥ* D - bE ᵥ* D = Complex.I • ((s ᵥ* β) ᵥ* D) := by
    rw [← Matrix.sub_vecMul, hd, Matrix.smul_vecMul]
  have hsI : s ᵥ* (1 - β * D) = (2 * Complex.I) • (y ᵥ* B) := by
    rw [← hI, Matrix.vecMul_sub, Matrix.vecMul_one, ← Matrix.vecMul_vecMul, Matrix.vecMul_add,
      Matrix.vecMul_one, Matrix.vecMul_smul, Matrix.vecMul_sub, Matrix.vecMul_one,
      Matrix.vecMul_smul]
    funext k
    have h1 := congrFun hD k
    have hsk : s k = αE k + bE k := by rw [hs]; rfl
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    linear_combination hsk + (-Complex.I) * h1 - (((s ᵥ* β) ᵥ* D) k) * hI2
  -- solve: s = 2i y B (1 - βD)⁻¹
  have hsol : s = (2 * Complex.I) • (y ᵥ* (B * (1 - β * D)⁻¹)) := by
    have h := congrArg (fun r => r ᵥ* (1 - β * D)⁻¹) hsI
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hinv', Matrix.vecMul_one,
      Matrix.smul_vecMul] at h
    exact h
  have hmat : B * (1 - β * D)⁻¹ * β * C = B * β * (1 - D * β)⁻¹ * C := by
    rw [Matrix.mul_assoc B, inv_one_sub_mul_mul_eq D β hinv, ← Matrix.mul_assoc]
  rw [hd, Matrix.smul_vecMul, smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.vecMul_vecMul,
    hsol, Matrix.smul_vecMul, Matrix.vecMul_vecMul, neg_smul,
    ← Matrix.mul_assoc (B * (1 - β * D)⁻¹), hmat]

end Fermionic
