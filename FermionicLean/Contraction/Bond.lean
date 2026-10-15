/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Basic

/-! # The bond covariance and teleportation

Two matched sets of modes `L`, `L'` carry the Majorana labels `(x_L, x_L', y_L, y_L')`,
the index type `(L ⊕ L) ⊕ (L ⊕ L)`. The bond covariance is `fromBlocks ω 0 0 (-ω)`
with `ω = fromBlocks 0 1 (-1) 0`. Contracting two bonds through a bond reproduces the
bond, which fixes the sign convention of the construction.
-/

open Matrix

namespace Fermionic

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The pairing matrix `ω = fromBlocks 0 1 (-1) 0` on `L ⊕ L`. -/
def pairing (L : Type*) [Fintype L] [DecidableEq L] : Matrix (L ⊕ L) (L ⊕ L) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- Majorana labels of two matched mode sets: `x`-labels of `L ⊕ L'`, then `y`-labels. -/
abbrev PairIndex (L : Type*) := (L ⊕ L) ⊕ (L ⊕ L)

/-- Definition 6: the bond covariance. -/
def bond (L : Type*) [Fintype L] [DecidableEq L] : Matrix (PairIndex L) (PairIndex L) ℝ :=
  Matrix.fromBlocks (pairing L) 0 0 (-(pairing L))

lemma pairing_transpose : (pairing L).transpose = -(pairing L) := by
  simp [pairing, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma pairing_mul_self : pairing L * pairing L = -1 := by
  simp [pairing, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]

/-- Theorem 7: the bond covariance is pure. -/
theorem pure_bond : Pure (bond L) := by
  refine ⟨?_, ?_⟩
  · simp [bond, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, pairing_transpose]
  · rw [bond, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, pairing_mul_self]
    have h1 : (-1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) = Matrix.fromBlocks (-1) 0 0 (-1) := by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]; simp
    have h2 : (-1 : Matrix (PairIndex L) (PairIndex L) ℝ) =
        Matrix.fromBlocks (-1) 0 0 (-1) := by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]; simp
    rw [h2, neg_zero]

/-! ### Teleportation -/

/-- The cross block of two bonds `(A₁,B₁)`, `(A₂,B₂)` between the retained labels
`(A₁,B₂)` and the eliminated labels `(B₁,A₂)`: `+1` on `A₁–B₁`, `-1` on `B₂–A₂` in the
`x` sector and the opposite signs in the `y` sector. -/
def teleportCross (L : Type*) [Fintype L] [DecidableEq L] :
    Matrix (PairIndex L) (PairIndex L) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 (-1)) 0 0 (Matrix.fromBlocks (-1) 0 0 1)

/-- The two-bond input in split form: retained `(A₁,B₂)`, eliminated `(B₁,A₂)`. -/
def teleportInput (L : Type*) [Fintype L] [DecidableEq L] :
    Matrix (PairIndex L ⊕ PairIndex L) (PairIndex L ⊕ PairIndex L) ℝ :=
  Matrix.fromBlocks 0 (teleportCross L) (-(teleportCross L).transpose) 0

lemma teleportCross_transpose : (teleportCross L).transpose = teleportCross L := by
  simp [teleportCross, Matrix.fromBlocks_transpose]

lemma teleportInput_transpose : (teleportInput L).transpose = -(teleportInput L) := by
  simp [teleportInput, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg,
    teleportCross_transpose]

lemma teleportInput_contractInvertible : ContractInvertible (teleportInput L) (bond L) := by
  unfold ContractInvertible teleportInput
  simp [Matrix.toBlocks_fromBlocks₂₂]

lemma teleportCross_mul_bond_mul_teleportCross :
    teleportCross L * bond L * teleportCross L = -(bond L) := by
  simp [teleportCross, bond, pairing, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/-- Relabelling from the split form `(A₁,B₂ | B₁,A₂)` to the systems `(A₁,B₁) ⊕ (A₂,B₂)`. -/
def teleportRelabel : PairIndex L ⊕ PairIndex L → PairIndex L ⊕ PairIndex L
  | Sum.inl (Sum.inl (Sum.inl a)) => Sum.inl (Sum.inl (Sum.inl a))
  | Sum.inl (Sum.inl (Sum.inr b)) => Sum.inr (Sum.inl (Sum.inr b))
  | Sum.inl (Sum.inr (Sum.inl a)) => Sum.inl (Sum.inr (Sum.inl a))
  | Sum.inl (Sum.inr (Sum.inr b)) => Sum.inr (Sum.inr (Sum.inr b))
  | Sum.inr (Sum.inl (Sum.inl b)) => Sum.inl (Sum.inl (Sum.inr b))
  | Sum.inr (Sum.inl (Sum.inr a)) => Sum.inr (Sum.inl (Sum.inl a))
  | Sum.inr (Sum.inr (Sum.inl b)) => Sum.inl (Sum.inr (Sum.inr b))
  | Sum.inr (Sum.inr (Sum.inr a)) => Sum.inr (Sum.inr (Sum.inl a))

/-- The split-form input is the independent sum of two bonds, relabelled. -/
lemma teleportInput_eq_submatrix :
    (Matrix.fromBlocks (bond L) 0 0 (bond L)).submatrix teleportRelabel teleportRelabel =
      teleportInput L := by
  ext i j
  rcases i with ((a | a) | (a | a)) | ((a | a) | (a | a)) <;>
    rcases j with ((b | b) | (b | b)) | ((b | b) | (b | b)) <;>
    simp [teleportRelabel, bond, pairing, teleportInput, teleportCross, Matrix.fromBlocks,
      Matrix.one_apply, eq_comm]

/-- Theorem 8: contracting two bonds through a bond reproduces the bond. -/
theorem contract_teleportInput : contract (teleportInput L) (bond L) = bond L := by
  unfold contract teleportInput
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, sub_zero,
    inv_one, Matrix.mul_one, zero_add, teleportCross_transpose, Matrix.mul_neg]
  rw [teleportCross_mul_bond_mul_teleportCross, neg_neg]

end Fermionic
