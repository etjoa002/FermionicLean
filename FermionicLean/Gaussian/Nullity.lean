/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Real.Basic

/-! # The nullity lemma

For an invertible block matrix `M = fromBlocks P Y Z Q` the off-diagonal block `N₁₂` of
`N = M⁻¹` has the rank of `Y`. The map `v ↦ Q v` sends `ker Y` injectively into
`ker N₁₂` (because `N₂₂ Q v = v` there), and symmetrically with `M` and `N` exchanged;
both blocks have the same shape, so equal nullities give equal ranks. No invertibility
of the diagonal blocks is used.
-/

open Matrix Module

namespace Fermionic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `M (0, v) = (M₁₂ v, M₂₂ v)`. -/
lemma mulVec_sumElim_zero (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (v : κ → ℝ) :
    M *ᵥ Sum.elim 0 v = Sum.elim (M.toBlocks₁₂ *ᵥ v) (M.toBlocks₂₂ *ᵥ v) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- For `v ∈ ker M₁₂`: `(M⁻¹)₁₂ (M₂₂ v) = 0` and `(M⁻¹)₂₂ (M₂₂ v) = v`. -/
lemma inv_toBlocks_mulVec_of_toBlocks12_mulVec_eq_zero (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : IsUnit M.det) {v : κ → ℝ} (hv : M.toBlocks₁₂ *ᵥ v = 0) :
    (M⁻¹).toBlocks₁₂ *ᵥ (M.toBlocks₂₂ *ᵥ v) = 0 ∧
      (M⁻¹).toBlocks₂₂ *ᵥ (M.toBlocks₂₂ *ᵥ v) = v := by
  have h1 : M⁻¹ *ᵥ (M *ᵥ Sum.elim (0 : ι → ℝ) v) = Sum.elim (0 : ι → ℝ) v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  rw [mulVec_sumElim_zero M v, hv, mulVec_sumElim_zero M⁻¹ (M.toBlocks₂₂ *ᵥ v)] at h1
  exact ⟨funext fun i => by simpa using congrFun h1 (Sum.inl i),
    funext fun j => by simpa using congrFun h1 (Sum.inr j)⟩

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Membership in `ker (mulVecLin A)` unfolded. -/
lemma mulVec_eq_zero_of_mem_ker {A : Matrix ι κ ℝ} (v : LinearMap.ker A.mulVecLin) :
    A *ᵥ (v : κ → ℝ) = 0 :=
  LinearMap.mem_ker.mp v.2

/-- One direction of the nullity lemma: `dim ker M₁₂ ≤ dim ker (M⁻¹)₁₂`. -/
lemma finrank_ker_toBlocks12_le_inv (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : IsUnit M.det) :
    finrank ℝ (LinearMap.ker M.toBlocks₁₂.mulVecLin) ≤
      finrank ℝ (LinearMap.ker (M⁻¹).toBlocks₁₂.mulVecLin) := by
  let f : LinearMap.ker M.toBlocks₁₂.mulVecLin →ₗ[ℝ] LinearMap.ker (M⁻¹).toBlocks₁₂.mulVecLin :=
    LinearMap.codRestrict _ (M.toBlocks₂₂.mulVecLin.domRestrict _) fun v => by
      simpa using (inv_toBlocks_mulVec_of_toBlocks12_mulVec_eq_zero M hM
        (mulVec_eq_zero_of_mem_ker v)).1
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun v w hvw => ?_
  have h := congrArg (fun x : LinearMap.ker (M⁻¹).toBlocks₁₂.mulVecLin =>
    (M⁻¹).toBlocks₂₂ *ᵥ x.1) hvw
  simp only [f, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply,
    Matrix.mulVecLin_apply] at h
  rw [(inv_toBlocks_mulVec_of_toBlocks12_mulVec_eq_zero M hM (mulVec_eq_zero_of_mem_ker v)).2,
    (inv_toBlocks_mulVec_of_toBlocks12_mulVec_eq_zero M hM (mulVec_eq_zero_of_mem_ker w)).2] at h
  exact Subtype.ext h

/-- The nullity lemma: for an invertible block matrix, the off-diagonal block of the inverse
has the rank of the off-diagonal block. No invertibility of the diagonal blocks is assumed. -/
theorem rank_toBlocks12_inv (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : IsUnit M.det) :
    (M⁻¹).toBlocks₁₂.rank = M.toBlocks₁₂.rank := by
  have h1 := finrank_ker_toBlocks12_le_inv M hM
  have h2 := finrank_ker_toBlocks12_le_inv M⁻¹ (Matrix.isUnit_nonsing_inv_det M hM)
  rw [Matrix.nonsing_inv_nonsing_inv M hM] at h2
  have e1 := LinearMap.finrank_range_add_finrank_ker M.toBlocks₁₂.mulVecLin
  have e2 := LinearMap.finrank_range_add_finrank_ker (M⁻¹).toBlocks₁₂.mulVecLin
  unfold Matrix.rank
  omega

end Fermionic
