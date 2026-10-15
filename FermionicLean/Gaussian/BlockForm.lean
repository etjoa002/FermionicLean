/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Examples
import FermionicLean.Fock.Occupation
import Mathlib.Algebra.Order.Star.Real

/-! # The block form `D(ε)`

`blockForm ε = fromBlocks 0 (diagonal ε) (-(diagonal ε)) 0` pairs `x_j` with `y_j` with
weight `ε_j`. It is admissible exactly when every `|ε_j| ≤ 1` and pure exactly when every
`|ε_j| = 1`; `Ω_n = blockForm 1`, and the occupation covariance of `s` is
`blockForm (occupationSignEntry ∘ s)`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-- Definition 1: the block form `D(ε)`. -/
def blockForm (ε : Fin n → ℝ) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0

lemma blockForm_transpose (ε : Fin n → ℝ) : (blockForm ε).transpose = -blockForm ε := by
  simp [blockForm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.diagonal_transpose]

lemma blockForm_mul_blockForm (ε δ : Fin n → ℝ) :
    blockForm ε * blockForm δ = -Matrix.fromBlocks (Matrix.diagonal (ε * δ)) 0 0
      (Matrix.diagonal (ε * δ)) := by
  simp [blockForm, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal, mul_comm]

lemma transpose_mul_blockForm (ε : Fin n → ℝ) :
    (blockForm ε).transpose * blockForm ε =
      Matrix.fromBlocks (Matrix.diagonal (ε * ε)) 0 0 (Matrix.diagonal (ε * ε)) := by
  rw [blockForm_transpose, Matrix.neg_mul, blockForm_mul_blockForm, neg_neg]

/-- The entries of `1 - D(ε)ᵀ D(ε)`: `1 - ε_j²` on both labels of mode `j`. -/
def blockGap (ε : Fin n → ℝ) : MajoranaIndex n → ℝ :=
  Sum.elim (fun j => 1 - ε j * ε j) (fun j => 1 - ε j * ε j)

lemma one_sub_transpose_mul_blockForm (ε : Fin n → ℝ) :
    1 - (blockForm ε).transpose * blockForm ε = Matrix.diagonal (blockGap ε) := by
  rw [transpose_mul_blockForm]
  ext (a | a) (b | b) <;>
    simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, blockGap]
    <;> split_ifs <;> simp_all

lemma abs_le_one_iff_sq_le (t : ℝ) : |t| ≤ 1 ↔ t * t ≤ 1 := by
  rw [← abs_mul_abs_self t]
  constructor
  · intro h; nlinarith [abs_nonneg t]
  · intro h; nlinarith [abs_nonneg t]

lemma abs_eq_one_iff_sq_eq (t : ℝ) : |t| = 1 ↔ t * t = 1 := by
  rw [← abs_mul_abs_self t]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have h0 := abs_nonneg t
    nlinarith

/-- Definition 1: `D(ε)` is admissible iff every `|ε_j| ≤ 1`. -/
theorem isAdmissible_blockForm_iff (ε : Fin n → ℝ) :
    IsAdmissible (blockForm ε) ↔ ∀ j, |ε j| ≤ 1 := by
  unfold IsAdmissible
  rw [one_sub_transpose_mul_blockForm, Matrix.posSemidef_diagonal_iff]
  constructor
  · rintro ⟨-, h⟩ j
    have := h (Sum.inl j)
    simp only [blockGap, Sum.elim_inl] at this
    rw [abs_le_one_iff_sq_le]; linarith
  · intro h
    refine ⟨blockForm_transpose ε, fun a => ?_⟩
    have key : ∀ j, 0 ≤ 1 - ε j * ε j := fun j => by
      have := (abs_le_one_iff_sq_le (ε j)).mp (h j); linarith
    rcases a with j | j <;> simp [blockGap, key]

/-- Definition 1: `D(ε)` is pure iff every `|ε_j| = 1`. -/
theorem isPure_blockForm_iff (ε : Fin n → ℝ) :
    IsPure (blockForm ε) ↔ ∀ j, |ε j| = 1 := by
  unfold IsPure
  rw [blockForm_mul_blockForm, neg_eq_iff_eq_neg, neg_neg, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨-, h, -, -, -⟩ j
    have := congrFun (congrFun h j) j
    simp only [Matrix.diagonal_apply_eq, Pi.mul_apply, Matrix.one_apply_eq] at this
    exact (abs_eq_one_iff_sq_eq (ε j)).mpr this
  · intro h
    refine ⟨blockForm_transpose ε, ?_, rfl, rfl, ?_⟩ <;>
    · ext i j
      simp only [Matrix.diagonal_apply, Matrix.one_apply, Pi.mul_apply]
      split_ifs with hij
      · subst hij; exact (abs_eq_one_iff_sq_eq (ε i)).mp (h i)
      · rfl

/-- `Ω_n = D(1)`. -/
theorem standardCovariance_eq_blockForm : standardCovariance n = blockForm 1 := by
  simp [standardCovariance, blockForm]

/-- The occupation covariance is `D(σ(s))`, `σ_j = -1` empty, `+1` occupied. -/
theorem covariance_occupation_eq_blockForm (s : FockIndex n) :
    covariance (occupation s) = blockForm (fun j => occupationSignEntry (s j)) := by
  rw [covariance_occupation]; rfl

end Fermionic
