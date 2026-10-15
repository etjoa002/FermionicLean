/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.BlockForm
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # The exponential of a block form

`blockRotation θ` is the rotation by the angle `θ_j` in each plane `(x_j, y_j)`, with the
$(x, y)$ block form `fromBlocks (diag cos θ) (-(diag sin θ)) (diag sin θ) (diag cos θ)`. It is
orthogonal, `blockRotation θ ᵀ = blockRotation (-θ)`, and `exp (blockForm θ) = blockRotation (-θ)`
(Lemma 9 of G1): the even powers of `D(θ)` are `(-1)^m diag (θ^{2m}, θ^{2m})` and the odd powers
`(-1)^m D(θ^{2m+1})`, so the exponential series splits into the cosine and sine series entrywise.
-/

open Matrix NormedSpace
open scoped Nat

namespace Fermionic

variable {n : ℕ}

/-- Definition 7: the block rotation `R(θ)`, rows `x_j : (cos θ_j, -sin θ_j)`,
`y_j : (sin θ_j, cos θ_j)` on the columns `(x_j, y_j)`. -/
noncomputable def blockRotation (θ : Fin n → ℝ) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ j))
    (-(Matrix.diagonal fun j => Real.sin (θ j)))
    (Matrix.diagonal fun j => Real.sin (θ j)) (Matrix.diagonal fun j => Real.cos (θ j))

/-- Lemma 9: `R(θ)ᵀ = R(-θ)`. -/
theorem blockRotation_transpose (θ : Fin n → ℝ) :
    (blockRotation θ).transpose = blockRotation (-θ) := by
  simp [blockRotation, Matrix.fromBlocks_transpose, Matrix.diagonal_transpose, Real.cos_neg,
    Real.sin_neg, Matrix.diagonal_neg]

/-- Lemma 9: `R(θ) R(θ)ᵀ = 1`. -/
theorem blockRotation_mul_transpose (θ : Fin n → ℝ) :
    blockRotation θ * (blockRotation θ).transpose = 1 := by
  rw [blockRotation_transpose, ← Matrix.fromBlocks_one]
  simp only [blockRotation, Pi.neg_apply, Real.cos_neg, Real.sin_neg, Matrix.fromBlocks_multiply,
    neg_neg, Matrix.diagonal_mul_diagonal, Matrix.diagonal_neg,
    Matrix.diagonal_add, ← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_inj,
    Matrix.diagonal_eq_diagonal_iff]
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · linear_combination Real.cos_sq_add_sin_sq (θ i)
  · ring
  · ring
  · linear_combination Real.cos_sq_add_sin_sq (θ i)

/-- `diag (a, a) * diag (b, b) = diag (a b, a b)`. -/
private lemma diagPair_mul_diagPair (a b : Fin n → ℝ) :
    Matrix.fromBlocks (Matrix.diagonal a) 0 0 (Matrix.diagonal a) *
        Matrix.fromBlocks (Matrix.diagonal b) 0 0 (Matrix.diagonal b) =
      Matrix.fromBlocks (Matrix.diagonal (a * b)) 0 0 (Matrix.diagonal (a * b)) := by
  simp only [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Pi.mul_def]

/-- `diag (a, a) * D(b) = D(a b)`. -/
private lemma diagPair_mul_blockForm (a b : Fin n → ℝ) :
    Matrix.fromBlocks (Matrix.diagonal a) 0 0 (Matrix.diagonal a) * blockForm b =
      blockForm (a * b) := by
  simp only [blockForm, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_neg, add_zero, zero_add, neg_zero, Pi.mul_def]

/-- The even powers: `D(θ)^(2m) = (-1)^m diag (θ^{2m}, θ^{2m})`. -/
theorem blockForm_pow_even (θ : Fin n → ℝ) (m : ℕ) :
    blockForm θ ^ (2 * m) =
      (-1 : ℝ) ^ m • Matrix.fromBlocks (Matrix.diagonal fun j => θ j ^ (2 * m)) 0 0
        (Matrix.diagonal fun j => θ j ^ (2 * m)) := by
  induction m with
  | zero => simp [Matrix.fromBlocks_one]
  | succ m ih =>
    have key : (fun j => θ j ^ (2 * m)) * (θ * θ) = fun j => θ j ^ (2 * m + 2) := by
      funext j; simp only [Pi.mul_apply]; ring
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add (blockForm θ), ih, sq (blockForm θ),
      blockForm_mul_blockForm, Matrix.mul_neg, Matrix.smul_mul, diagPair_mul_diagPair, key,
      pow_succ, mul_neg_one, neg_smul]

/-- The odd powers: `D(θ)^(2m+1) = (-1)^m D(θ^{2m+1})`. -/
theorem blockForm_pow_odd (θ : Fin n → ℝ) (m : ℕ) :
    blockForm θ ^ (2 * m + 1) = (-1 : ℝ) ^ m • blockForm fun j => θ j ^ (2 * m + 1) := by
  have key : (fun j => θ j ^ (2 * m)) * θ = fun j => θ j ^ (2 * m + 1) := by
    funext j; simp only [Pi.mul_apply]; ring
  rw [pow_succ (blockForm θ), blockForm_pow_even, Matrix.smul_mul, diagPair_mul_blockForm, key]

/-- `c • diag (v, v) = diag (c v, c v)`. -/
private lemma smul_diagPair (c : ℝ) (v : Fin n → ℝ) :
    c • Matrix.fromBlocks (Matrix.diagonal v) 0 0 (Matrix.diagonal v) =
      Matrix.fromBlocks (Matrix.diagonal (c • v)) 0 0 (Matrix.diagonal (c • v)) := by
  simp only [Matrix.fromBlocks_smul, Matrix.diagonal_smul, smul_zero]

/-- `c • D(v) = D(c v)`. -/
private lemma smul_blockForm (c : ℝ) (v : Fin n → ℝ) : c • blockForm v = blockForm (c • v) := by
  simp only [blockForm, Matrix.fromBlocks_smul, Matrix.diagonal_smul, smul_zero, smul_neg]

/-- The even term of the exponential series of `D(θ)`: the cosine term entrywise. -/
private lemma expTerm_even (θ : Fin n → ℝ) (m : ℕ) :
    (((2 * m)! : ℝ)⁻¹) • blockForm θ ^ (2 * m) =
      Matrix.fromBlocks (Matrix.diagonal fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m) / (2 * m)!) 0 0
        (Matrix.diagonal fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m) / (2 * m)!) := by
  have key : (((2 * m)! : ℝ)⁻¹ * (-1) ^ m) • (fun j => θ j ^ (2 * m)) =
      fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m) / (2 * m)! := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [blockForm_pow_even, smul_smul, smul_diagPair, key]

/-- The odd term of the exponential series of `D(θ)`: the sine term entrywise. -/
private lemma expTerm_odd (θ : Fin n → ℝ) (m : ℕ) :
    (((2 * m + 1)! : ℝ)⁻¹) • blockForm θ ^ (2 * m + 1) =
      blockForm fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m + 1) / (2 * m + 1)! := by
  have key : (((2 * m + 1)! : ℝ)⁻¹ * (-1) ^ m) • (fun j => θ j ^ (2 * m + 1)) =
      fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m + 1) / (2 * m + 1)! := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [blockForm_pow_odd, smul_smul, smul_blockForm, key]

/-- `v ↦ diag (v, v)` as an additive map. -/
private def diagPairHom : (Fin n → ℝ) →+ Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ where
  toFun v := Matrix.fromBlocks (Matrix.diagonal v) 0 0 (Matrix.diagonal v)
  map_zero' := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  map_add' a b := by
    simp only [Matrix.fromBlocks_add, Matrix.diagonal_add, add_zero, Pi.add_def]

/-- `v ↦ D(v)` as an additive map. -/
private def blockFormHom : (Fin n → ℝ) →+ Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ where
  toFun := blockForm
  map_zero' := by
    ext (i | i) (j | j) <;> simp [blockForm, Matrix.fromBlocks]
  map_add' a b := by
    simp only [blockForm, Matrix.fromBlocks_add, Matrix.diagonal_add, add_zero, Pi.add_def, neg_add,
      Matrix.diagonal_neg]

private lemma continuous_diagPairHom : Continuous (diagPairHom (n := n)) := by
  change Continuous fun v : Fin n → ℝ =>
    Matrix.fromBlocks (Matrix.diagonal v) 0 0 (Matrix.diagonal v)
  exact continuous_id.matrix_diagonal.matrix_fromBlocks continuous_const continuous_const
    continuous_id.matrix_diagonal

private lemma continuous_blockFormHom : Continuous (blockFormHom (n := n)) := by
  change Continuous fun v : Fin n → ℝ =>
    Matrix.fromBlocks 0 (Matrix.diagonal v) (-(Matrix.diagonal v)) 0
  exact continuous_const.matrix_fromBlocks continuous_id.matrix_diagonal
    continuous_id.matrix_diagonal.neg continuous_const

/-- Entrywise convergence transported to `diag (v, v)`. -/
private lemma hasSum_diagPair {f : ℕ → Fin n → ℝ} {v : Fin n → ℝ} (h : HasSum f v) :
    HasSum (fun m => Matrix.fromBlocks (Matrix.diagonal (f m)) 0 0 (Matrix.diagonal (f m)))
      (Matrix.fromBlocks (Matrix.diagonal v) 0 0 (Matrix.diagonal v)) :=
  h.map diagPairHom continuous_diagPairHom

/-- Entrywise convergence transported to `D(v)`. -/
private lemma hasSum_blockForm {f : ℕ → Fin n → ℝ} {v : Fin n → ℝ} (h : HasSum f v) :
    HasSum (fun m => blockForm (f m)) (blockForm v) :=
  h.map blockFormHom continuous_blockFormHom

/-- `R(-θ) = diag (cos θ, cos θ) + D(sin θ)`. -/
private lemma blockRotation_neg_eq (θ : Fin n → ℝ) :
    blockRotation (-θ) =
      Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ j)) 0 0
          (Matrix.diagonal fun j => Real.cos (θ j)) +
        blockForm fun j => Real.sin (θ j) := by
  ext (i | i) (j | j) <;>
    simp [blockRotation, blockForm, Matrix.fromBlocks, Matrix.diagonal_apply]

/-- Lemma 9: `exp (D(θ)) = R(-θ)`. -/
theorem exp_blockForm (θ : Fin n → ℝ) : exp (blockForm θ) = blockRotation (-θ) := by
  rw [blockRotation_neg_eq, exp_eq_tsum ℝ]
  refine HasSum.tsum_eq (HasSum.even_add_odd ?_ ?_)
  · have hc : HasSum (fun m => fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m) / (2 * m)!)
        (fun j => Real.cos (θ j)) := Pi.hasSum.mpr fun j => Real.hasSum_cos (θ j)
    simpa only [expTerm_even] using hasSum_diagPair hc
  · have hs : HasSum (fun m => fun j => (-1 : ℝ) ^ m * θ j ^ (2 * m + 1) / (2 * m + 1)!)
        (fun j => Real.sin (θ j)) := Pi.hasSum.mpr fun j => Real.hasSum_sin (θ j)
    simpa only [expTerm_odd] using hasSum_blockForm hs

/-- Lemma 9: `exp (-(t • D(ε))) = R(t • ε)`. -/
theorem exp_neg_smul_blockForm (t : ℝ) (ε : Fin n → ℝ) :
    exp (-(t • blockForm ε)) = blockRotation (t • ε) := by
  have : -(t • blockForm ε) = blockForm (-(t • ε)) := by
    ext (a | a) (b | b) <;>
      simp [blockForm, Matrix.fromBlocks, Matrix.diagonal_apply] <;> split_ifs <;> simp
  rw [this, exp_blockForm, neg_neg]

end Fermionic
