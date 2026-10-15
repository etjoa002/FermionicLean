/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Defs

/-! # Antisymmetry and admissibility of the contraction

The contraction of admissible covariances is admissible: the energy argument writes
`Γ (x, w) = (u, v)` with `w = Γp v`, so `‖u‖² + ‖v‖² ≤ ‖x‖² + ‖w‖² ≤ ‖x‖² + ‖v‖²`.
For a pure bond the contraction is the Schur form `A + B (D + Γp)⁻¹ Bᵀ`.
-/

open Matrix

namespace Fermionic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-! ### Push-through -/

/-- Lemma 2: `det (1 - X Y) = det (1 - Y X)`, so both are units together. -/
lemma isUnit_det_one_sub_mul_comm (X Y : Matrix κ κ ℝ) :
    IsUnit (1 - X * Y).det ↔ IsUnit (1 - Y * X).det := by
  rw [Matrix.det_one_sub_mul_comm]

/-- Lemma 2: `Y (1 - X Y)⁻¹ = (1 - Y X)⁻¹ Y`. -/
lemma mul_inv_one_sub_mul_comm {X Y : Matrix κ κ ℝ} (h : IsUnit (1 - X * Y).det) :
    Y * (1 - X * Y)⁻¹ = (1 - Y * X)⁻¹ * Y := by
  have h' : IsUnit (1 - Y * X).det := (isUnit_det_one_sub_mul_comm X Y).mp h
  have key : Y * (1 - X * Y) = (1 - Y * X) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  calc Y * (1 - X * Y)⁻¹
      = (1 - Y * X)⁻¹ * ((1 - Y * X) * Y) * (1 - X * Y)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h', Matrix.one_mul]
    _ = (1 - Y * X)⁻¹ * (Y * (1 - X * Y)) * (1 - X * Y)⁻¹ := by rw [key]
    _ = (1 - Y * X)⁻¹ * Y := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]

/-! ### Blocks of an antisymmetric matrix -/

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma toBlocks_of_transpose_eq_neg {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hΓ : Γ.transpose = -Γ) :
    Γ.toBlocks₁₁.transpose = -Γ.toBlocks₁₁ ∧ Γ.toBlocks₂₁.transpose = -Γ.toBlocks₁₂ ∧
    Γ.toBlocks₁₂.transpose = -Γ.toBlocks₂₁ ∧ Γ.toBlocks₂₂.transpose = -Γ.toBlocks₂₂ := by
  have h := hΓ
  rw [← Matrix.fromBlocks_toBlocks Γ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_inj] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

omit [Fintype ι] in
/-- Theorem 3: the contraction of antisymmetric matrices is antisymmetric. -/
theorem contract_transpose {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {Γp : Matrix κ κ ℝ}
    (hΓ : Γ.transpose = -Γ) (hp : Γp.transpose = -Γp) (hinv : ContractInvertible Γ Γp) :
    (contract Γ Γp).transpose = -contract Γ Γp := by
  obtain ⟨hA, hC, hB, hD⟩ := toBlocks_of_transpose_eq_neg hΓ
  set A := Γ.toBlocks₁₁; set B := Γ.toBlocks₁₂; set C := Γ.toBlocks₂₁; set D := Γ.toBlocks₂₂
  have hT : (1 - D * Γp).transpose = 1 - Γp * D := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hp, hD,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hpush : (1 - Γp * D)⁻¹ * Γp = Γp * (1 - D * Γp)⁻¹ :=
    (mul_inv_one_sub_mul_comm hinv).symm
  unfold contract
  rw [Matrix.transpose_add, hA, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hT, hp, hC, hB, neg_add]
  congr 1
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [← Matrix.mul_assoc (1 - Γp * D)⁻¹, hpush]
  simp only [Matrix.mul_assoc, B, C, D]

/-! ### The energy argument -/

/-- The loop variables of the energy argument: `Γ (x, w) = (contract Γ Γp x, v)`. -/
lemma contract_mulVec (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Γp : Matrix κ κ ℝ)
    (hinv : ContractInvertible Γ Γp) (x : ι → ℝ) :
    let v := (1 - Γ.toBlocks₂₂ * Γp)⁻¹ *ᵥ (Γ.toBlocks₂₁ *ᵥ x)
    Γ *ᵥ Sum.elim x (Γp *ᵥ v) = Sum.elim (contract Γ Γp *ᵥ x) v := by
  intro v
  have hv : v = Γ.toBlocks₂₁ *ᵥ x + Γ.toBlocks₂₂ *ᵥ (Γp *ᵥ v) := by
    have h1 : (1 - Γ.toBlocks₂₂ * Γp) *ᵥ v = Γ.toBlocks₂₁ *ᵥ x := by
      simp only [v, Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mul]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h1
    rw [← h1]; abel
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks Γ]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  congr 1
  · simp only [contract, Matrix.add_mulVec, v, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · exact hv.symm

/-- Theorem 4 (norm form): the contraction is norm-contractive. -/
lemma contract_dotProduct_le {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {Γp : Matrix κ κ ℝ}
    (hΓ : ∀ z : ι ⊕ κ → ℝ, (Γ *ᵥ z) ⬝ᵥ (Γ *ᵥ z) ≤ z ⬝ᵥ z)
    (hp : ∀ y : κ → ℝ, (Γp *ᵥ y) ⬝ᵥ (Γp *ᵥ y) ≤ y ⬝ᵥ y)
    (hinv : ContractInvertible Γ Γp) (x : ι → ℝ) :
    (contract Γ Γp *ᵥ x) ⬝ᵥ (contract Γ Γp *ᵥ x) ≤ x ⬝ᵥ x := by
  have h := contract_mulVec Γ Γp hinv x
  simp only at h
  set v := (1 - Γ.toBlocks₂₂ * Γp)⁻¹ *ᵥ (Γ.toBlocks₂₁ *ᵥ x) with hv
  have h1 := hΓ (Sum.elim x (Γp *ᵥ v))
  rw [h, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim] at h1
  have h2 := hp v
  linarith

/-- Theorem 4: the contraction of admissible covariances is admissible. -/
theorem contract_admissible [DecidableEq ι] {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {Γp : Matrix κ κ ℝ}
    (hΓ : Admissible Γ) (hp : Admissible Γp) (hinv : ContractInvertible Γ Γp) :
    Admissible (contract Γ Γp) := by
  rw [admissible_iff_norm (contract_transpose hΓ.1 hp.1 hinv)]
  exact contract_dotProduct_le ((admissible_iff_norm hΓ.1).mp hΓ)
    ((admissible_iff_norm hp.1).mp hp) hinv

/-! ### Pure bonds -/

/-- For a pure bond, `(D + Γp)(-Γp) = 1 - D Γp`. -/
lemma add_mul_neg_of_pure {D Γp : Matrix κ κ ℝ} (hp : Pure Γp) :
    (D + Γp) * (-Γp) = 1 - D * Γp := by
  rw [Matrix.mul_neg, Matrix.add_mul, hp.2]
  abel

lemma neg_inv_of_pure {Γp : Matrix κ κ ℝ} (hp : Pure Γp) : (-Γp)⁻¹ = Γp :=
  Matrix.inv_eq_left_inv (by rw [Matrix.mul_neg, hp.2, neg_neg])

lemma isUnit_det_neg_of_pure {Γp : Matrix κ κ ℝ} (hp : Pure Γp) : IsUnit (-Γp).det :=
  Matrix.isUnit_det_of_left_inverse (by rw [Matrix.mul_neg, hp.2, neg_neg] : Γp * (-Γp) = 1)

omit [Fintype ι] in
/-- Theorem 5: for a pure bond the invertibility conditions coincide. -/
theorem contractInvertible_iff_of_pure (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) {Γp : Matrix κ κ ℝ}
    (hp : Pure Γp) : ContractInvertible Γ Γp ↔ IsUnit (Γ.toBlocks₂₂ + Γp).det := by
  unfold ContractInvertible
  rw [← add_mul_neg_of_pure hp, Matrix.det_mul, IsUnit.mul_iff]
  exact and_iff_left (isUnit_det_neg_of_pure hp)

omit [Fintype ι] in
/-- Theorem 5: the Schur form of the contraction with a pure bond. -/
theorem contract_eq_schur_of_pure {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {Γp : Matrix κ κ ℝ}
    (hΓ : Γ.transpose = -Γ) (hp : Pure Γp) (hinv : ContractInvertible Γ Γp) :
    contract Γ Γp =
      Γ.toBlocks₁₁ + Γ.toBlocks₁₂ * (Γ.toBlocks₂₂ + Γp)⁻¹ * Γ.toBlocks₁₂.transpose := by
  obtain ⟨-, -, hB, -⟩ := toBlocks_of_transpose_eq_neg hΓ
  have hunit : IsUnit (Γ.toBlocks₂₂ + Γp).det :=
    (contractInvertible_iff_of_pure Γ hp).mp hinv
  have hinvEq : (1 - Γ.toBlocks₂₂ * Γp)⁻¹ = Γp * (Γ.toBlocks₂₂ + Γp)⁻¹ := by
    rw [← add_mul_neg_of_pure hp, Matrix.mul_inv_rev, neg_inv_of_pure hp]
  have hkey : Γp * (1 - Γ.toBlocks₂₂ * Γp)⁻¹ = -(Γ.toBlocks₂₂ + Γp)⁻¹ := by
    rw [hinvEq, ← Matrix.mul_assoc, hp.2, Matrix.neg_mul, Matrix.one_mul]
  unfold contract
  rw [Matrix.mul_assoc Γ.toBlocks₁₂, hkey, hB]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Fermionic
