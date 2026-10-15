/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Admissible

/-! # Admissibility over an arbitrary finite index set

The conditions `Γᵀ = -Γ` and `1 - Γᵀ Γ ⪰ 0` do not refer to the Majorana labelling.
`Admissible` and `Pure` are the same conditions on a matrix indexed by any finite type;
on `MajoranaIndex n` they coincide with `IsAdmissible` and `IsPure` definitionally.
-/

open Matrix

namespace Fermionic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Admissibility for a matrix on an arbitrary finite index set. -/
def Admissible (Γ : Matrix ι ι ℝ) : Prop :=
  Γ.transpose = -Γ ∧ (1 - Γ.transpose * Γ).PosSemidef

/-- Purity for a matrix on an arbitrary finite index set. -/
def Pure (Γ : Matrix ι ι ℝ) : Prop :=
  Γ.transpose = -Γ ∧ Γ * Γ = -1

lemma isAdmissible_iff_admissible {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    IsAdmissible Γ ↔ Admissible Γ := Iff.rfl

lemma isPure_iff_pure {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    IsPure Γ ↔ Pure Γ := Iff.rfl

lemma dotProduct_one_sub_transpose_mul_mulVec' (Γ : Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ ((1 - Γ.transpose * Γ) *ᵥ v) = v ⬝ᵥ v - (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Norm form of admissibility on an arbitrary index set. -/
theorem admissible_iff_norm {Γ : Matrix ι ι ℝ} (hΓ : Γ.transpose = -Γ) :
    Admissible Γ ↔ ∀ v : ι → ℝ, (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) ≤ v ⬝ᵥ v := by
  unfold Admissible
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.isHermitian_iff_isSymm]
  constructor
  · rintro ⟨-, -, h⟩ v
    have := h v
    rw [star_trivial, dotProduct_one_sub_transpose_mul_mulVec'] at this
    linarith
  · intro h
    refine ⟨hΓ, ?_, fun v => ?_⟩
    · change (1 - Γ.transpose * Γ).transpose = 1 - Γ.transpose * Γ
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    · rw [star_trivial, dotProduct_one_sub_transpose_mul_mulVec']
      linarith [h v]

/-- A pure covariance is admissible (norm form). -/
theorem Pure.admissible {Γ : Matrix ι ι ℝ} (h : Pure Γ) : Admissible Γ := by
  rw [admissible_iff_norm h.1]
  intro v
  have := dotProduct_one_sub_transpose_mul_mulVec' Γ v
  have hTT : Γ.transpose * Γ = 1 := by rw [h.1, Matrix.neg_mul, h.2, neg_neg]
  rw [hTT, sub_self, Matrix.zero_mulVec, dotProduct_zero] at this
  linarith

end Fermionic
