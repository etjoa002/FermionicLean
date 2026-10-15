/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Admissible

/-! # Covariance restriction to selected modes

Selecting both Majorana coordinates of distinct modes preserves admissibility.
The proof extends a vector on the selected coordinates by zero and uses the norm form.
-/

open Matrix

namespace Fermionic

variable {m n : ℕ}

/-- Zero-extension matrix of an injective coordinate selection `E`: `Q j α = 1` iff `E α = j`. -/
def selectionMatrix {ι κ : Type*} [DecidableEq ι] (E : κ → ι) : Matrix ι κ ℝ :=
  fun j α => if E α = j then 1 else 0

lemma submatrix_eq_selection {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Matrix ι ι ℝ) (E : κ → ι) :
    Γ.submatrix E E = (selectionMatrix E).transpose * Γ * selectionMatrix E := by
  ext α β
  simp [selectionMatrix, Matrix.mul_apply, Matrix.submatrix]

lemma selection_transpose_mul_self {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] {E : κ → ι} (hE : Function.Injective E) :
    (selectionMatrix E).transpose * selectionMatrix E = 1 := by
  ext α β
  simp [selectionMatrix, Matrix.mul_apply, Matrix.one_apply, hE.eq_iff]

lemma selection_mulVec_dotProduct_self {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {E : κ → ι} (hE : Function.Injective E) (v : κ → ℝ) :
    (selectionMatrix E *ᵥ v) ⬝ᵥ (selectionMatrix E *ᵥ v) = v ⬝ᵥ v := by
  classical
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, selection_transpose_mul_self hE,
    Matrix.vecMul_one]

lemma selection_transpose_mulVec_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (E : κ → ι) (w : ι → ℝ) (α : κ) :
    ((selectionMatrix E).transpose *ᵥ w) α = w (E α) := by
  simp [selectionMatrix, Matrix.mulVec, dotProduct]

lemma selection_transpose_mulVec_dotProduct_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {E : κ → ι} (hE : Function.Injective E) (w : ι → ℝ) :
    ((selectionMatrix E).transpose *ᵥ w) ⬝ᵥ ((selectionMatrix E).transpose *ᵥ w) ≤
      w ⬝ᵥ w := by
  simp only [dotProduct, selection_transpose_mulVec_apply]
  rw [← Finset.sum_image (f := fun j => w j * w j) (s := Finset.univ)
    (fun x _ y _ h => hE h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => mul_self_nonneg (w j))

/-- Theorem 5 (mode selection). -/
theorem isAdmissible_subsystem {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {e : Fin m → Fin n} (hΓ : IsAdmissible Γ) (he : Function.Injective e) :
    IsAdmissible (Γ.submatrix (Sum.map e e) (Sum.map e e)) := by
  have hE : Function.Injective (Sum.map e e) := he.sumMap he
  have hanti : (Γ.submatrix (Sum.map e e) (Sum.map e e)).transpose =
      -(Γ.submatrix (Sum.map e e) (Sum.map e e)) := by
    ext i j
    have := congrFun (congrFun hΓ.1 (Sum.map e e i)) (Sum.map e e j)
    simpa [Matrix.submatrix, Matrix.transpose] using this
  rw [isAdmissible_iff_norm hanti]
  intro v
  rw [submatrix_eq_selection, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set Q := selectionMatrix (Sum.map e e) with hQ
  calc (Q.transpose *ᵥ (Γ *ᵥ (Q *ᵥ v))) ⬝ᵥ (Q.transpose *ᵥ (Γ *ᵥ (Q *ᵥ v)))
      ≤ (Γ *ᵥ (Q *ᵥ v)) ⬝ᵥ (Γ *ᵥ (Q *ᵥ v)) := selection_transpose_mulVec_dotProduct_le hE _
    _ ≤ (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) := (isAdmissible_iff_norm hΓ.1).mp hΓ _
    _ = v ⬝ᵥ v := selection_mulVec_dotProduct_self hE v

end Fermionic
