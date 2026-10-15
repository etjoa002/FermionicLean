/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Admissible

/-! # Examples

The standard pure covariance `fromBlocks 0 1 (-1) 0`, and the one-mode family `λ • ω`.
-/

open Matrix

namespace Fermionic

/-- The block matrix `(0, 1; -1, 0)` on `n` modes; it is a pure covariance. -/
def standardCovariance (n : ℕ) : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

lemma standardCovariance_transpose (n : ℕ) :
    (standardCovariance n).transpose = -standardCovariance n := by
  simp [standardCovariance, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma standardCovariance_mul_self (n : ℕ) :
    standardCovariance n * standardCovariance n = -1 := by
  simp [standardCovariance, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_neg]

/-- The standard covariance is pure (boundary check of the F1 proposal). -/
theorem isPure_standardCovariance (n : ℕ) : IsPure (standardCovariance n) :=
  ⟨standardCovariance_transpose n, standardCovariance_mul_self n⟩

/-- The one-mode generator `ω = (0, 1; -1, 0)`. -/
abbrev oneModeOmega : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ := standardCovariance 1

/-- Proposition 7: every antisymmetric one-mode matrix is a multiple of `ω`. -/
theorem oneMode_eq_smul {Γ : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ}
    (hΓ : Γ.transpose = -Γ) : ∃ lam : ℝ, Γ = lam • oneModeOmega := by
  refine ⟨Γ (Sum.inl 0) (Sum.inr 0), ?_⟩
  have h := fun i j => congrFun (congrFun hΓ i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [standardCovariance, Matrix.fromBlocks] <;>
    linarith [h (Sum.inl 0) (Sum.inl 0), h (Sum.inr 0) (Sum.inr 0), h (Sum.inl 0) (Sum.inr 0)]

lemma smul_oneModeOmega_transpose (lam : ℝ) :
    (lam • oneModeOmega).transpose = -(lam • oneModeOmega) := by
  rw [Matrix.transpose_smul, standardCovariance_transpose, smul_neg]

lemma smul_oneModeOmega_mul_self (lam : ℝ) :
    (lam • oneModeOmega) * (lam • oneModeOmega) = -((lam * lam) • (1 : Matrix _ _ ℝ)) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, standardCovariance_mul_self, smul_smul, smul_neg]

/-- Proposition 7: `λ • ω` is admissible iff `|λ| ≤ 1`. -/
theorem isAdmissible_oneMode_iff (lam : ℝ) : IsAdmissible (lam • oneModeOmega) ↔ |lam| ≤ 1 := by
  rw [isAdmissible_iff_norm (smul_oneModeOmega_transpose lam), abs_le_one_iff_mul_self_le_one]
  have hsq : ∀ v : MajoranaIndex 1 → ℝ,
      ((lam • oneModeOmega) *ᵥ v) ⬝ᵥ ((lam • oneModeOmega) *ᵥ v) = (lam * lam) * (v ⬝ᵥ v) := by
    intro v
    have := dotProduct_one_sub_transpose_mul_mulVec (lam • oneModeOmega) v
    rw [smul_oneModeOmega_transpose, Matrix.neg_mul, smul_oneModeOmega_mul_self, neg_neg,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
    linarith
  simp only [hsq]
  constructor
  · intro h
    have := h (Pi.single (Sum.inl 0) 1)
    simpa using this
  · intro h v
    have hv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    nlinarith

/-- Proposition 7: `λ • ω` is pure iff `|λ| = 1`. -/
theorem isPure_oneMode_iff (lam : ℝ) : IsPure (lam • oneModeOmega) ↔ |lam| = 1 := by
  unfold IsPure
  rw [smul_oneModeOmega_mul_self, neg_inj]
  constructor
  · rintro ⟨-, h⟩
    have h0 : lam * lam = 1 := by
      simpa using congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    rcases mul_self_eq_one_iff.mp h0 with h1 | h1 <;> simp [h1]
  · intro h
    refine ⟨smul_oneModeOmega_transpose lam, ?_⟩
    rcases abs_eq (zero_le_one' ℝ) |>.mp h with h1 | h1 <;> simp [h1]

end Fermionic
