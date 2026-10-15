/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.DirectSumDefs
import FermionicLean.Gaussian.Admissible

/-! # Admissibility and purity of independent sums

After grouping each subsystem's coordinates, the independent sum is block diagonal;
antisymmetry, `Γᵀ Γ` and `Γ²` are computed blockwise. The coordinate grouping is a
ring isomorphism of matrix algebras, so these identities are its images.
-/

open Matrix

namespace Fermionic

/-- The coordinate grouping of `splitModes` as an equivalence. -/
def modeSplitEquiv (n m : ℕ) : MajoranaIndex (n + m) ≃ MajoranaIndex n ⊕ MajoranaIndex m :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin n) (Fin m) (Fin n) (Fin m))

lemma modeSplitEquiv_coe (n m : ℕ) :
    (modeSplitEquiv n m : MajoranaIndex (n + m) → MajoranaIndex n ⊕ MajoranaIndex m) =
      splitModes := by
  funext i
  rcases i with i | i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i <;>
    cases j <;> simp [modeSplitEquiv, splitModes, Equiv.sumSumSumComm]

/-- The grouping as an isomorphism of matrix algebras. -/
def groupingEquiv (n m : ℕ) :
    Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ ≃ₐ[ℝ]
      Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (modeSplitEquiv n m).symm

lemma groupingEquiv_apply {n m : ℕ}
    (M : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ) :
    groupingEquiv n m M = M.submatrix (modeSplitEquiv n m) (modeSplitEquiv n m) := by
  simp [groupingEquiv, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

lemma directSumCov_eq {n m : ℕ}
    (A : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (B : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ) :
    directSumCov A B = groupingEquiv n m (Matrix.fromBlocks A 0 0 B) := by
  rw [directSumCov, groupingEquiv_apply, modeSplitEquiv_coe]

lemma groupingEquiv_transpose {n m : ℕ}
    (M : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ) :
    (groupingEquiv n m M).transpose = groupingEquiv n m M.transpose := by
  rw [groupingEquiv_apply, groupingEquiv_apply, Matrix.transpose_submatrix]

lemma groupingEquiv_posSemidef_iff {n m : ℕ}
    (M : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ) :
    (groupingEquiv n m M).PosSemidef ↔ M.PosSemidef := by
  rw [groupingEquiv_apply, Matrix.posSemidef_submatrix_equiv]

/-- A real block diagonal matrix is positive semidefinite iff both blocks are. -/
lemma posSemidef_fromBlocks_zero_iff {u v : Type*} [Finite u] [Finite v]
    (A : Matrix u u ℝ) (B : Matrix v v ℝ) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  cases nonempty_fintype u
  cases nonempty_fintype v
  constructor
  · intro h
    constructor
    · convert h.submatrix Sum.inl using 1
      all_goals
        ext i j
        rfl
    · convert h.submatrix Sum.inr using 1
      all_goals
        ext i j
        rfl
  · rintro ⟨hA, hB⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hA.isHermitian.fromBlocks (by simp) hB.isHermitian
    · intro x
      have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      simp only [star_trivial] at ha hb ⊢
      simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
        dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      exact add_nonneg ha hb

variable {n m : ℕ} (A : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
  (B : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ)

lemma directSumCov_transpose_iff :
    (directSumCov A B).transpose = -directSumCov A B ↔
      A.transpose = -A ∧ B.transpose = -B := by
  rw [directSumCov_eq, groupingEquiv_transpose, ← map_neg, (groupingEquiv n m).injective.eq_iff,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp [Matrix.fromBlocks_inj]

lemma one_sub_directSumCov_transpose_mul :
    1 - (directSumCov A B).transpose * directSumCov A B =
      groupingEquiv n m (Matrix.fromBlocks (1 - A.transpose * A) 0 0 (1 - B.transpose * B)) := by
  rw [directSumCov_eq, groupingEquiv_transpose, ← map_mul, ← map_one (groupingEquiv n m),
    ← map_sub, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    show (1 : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ)
      = Matrix.fromBlocks 1 0 0 1 from Matrix.fromBlocks_one.symm]
  congr 1
  simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, neg_zero]

lemma directSumCov_mul_self :
    directSumCov A B * directSumCov A B =
      groupingEquiv n m (Matrix.fromBlocks (A * A) 0 0 (B * B)) := by
  rw [directSumCov_eq, ← map_mul, Matrix.fromBlocks_multiply]
  simp

/-- Theorem 6 (independent composition), admissibility. -/
theorem isAdmissible_directSum_iff :
    IsAdmissible (directSumCov A B) ↔ IsAdmissible A ∧ IsAdmissible B := by
  unfold IsAdmissible
  rw [directSumCov_transpose_iff, one_sub_directSumCov_transpose_mul,
    groupingEquiv_posSemidef_iff, posSemidef_fromBlocks_zero_iff]
  tauto

/-- Theorem 6 (independent composition), purity. -/
theorem isPure_directSum_iff :
    IsPure (directSumCov A B) ↔ IsPure A ∧ IsPure B := by
  unfold IsPure
  rw [directSumCov_transpose_iff, directSumCov_mul_self, ← map_one (groupingEquiv n m),
    ← map_neg, (groupingEquiv n m).injective.eq_iff, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_neg]
  simp only [neg_zero, Matrix.fromBlocks_inj, true_and]
  tauto

end Fermionic
