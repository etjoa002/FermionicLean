/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.ThreeSite

/-! # The determinant of the three-site contraction

For the three-site chain of `FermionicLean.Chain.ThreeSite`, `det(1 - D β_3) = (304/125)^2`.
Over `ℤ`, `5·1 - D_Z β_Z` is block diagonal along `Eliminated 3 1 = (X ⊕ X) ⊕ (X ⊕ X)`,
`X = Fin 3 × Fin 1`; its four `3 × 3` diagonal blocks are circulant with determinants
`152, 152, 250, 250`, so the integer determinant is `38000^2`, and
`det(1 - D β_3) = 38000^2 / 5^12 = (304/125)^2`.
-/

open Matrix

namespace Fermionic

/-- Block-triangular determinant from a vanishing lower-left block. -/
lemma det_of_toBlocks₂₁_eq_zero {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [CommRing R] (A : Matrix (m ⊕ n) (m ⊕ n) R) (h : A.toBlocks₂₁ = 0) :
    A.det = A.toBlocks₁₁.det * A.toBlocks₂₂.det := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h]
  exact Matrix.det_fromBlocks_zero₂₁ _ _ _

/-- Reindex `Fin 3 × Fin 1` to `Fin 3`. -/
lemma det_three_of_equiv (A : Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℤ) :
    A.det = (Matrix.reindex (finProdFinEquiv.trans (finCongr (by norm_num)))
      (finProdFinEquiv.trans (finCongr (by norm_num))) A : Matrix (Fin 3) (Fin 3) ℤ).det :=
  (Matrix.det_reindex_self _ A).symm

lemma threeSite_detZ_blocks₂₁ :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₂₁ = 0 := by
  decide

lemma threeSite_detZ_blocks₁₁₂₁ :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₁₁.toBlocks₂₁
      = 0 := by
  decide

lemma threeSite_detZ_blocks₂₂₂₁ :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₂₂.toBlocks₂₁
      = 0 := by
  decide

lemma threeSite_detZ_b11 :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₁₁.toBlocks₁₁.det
      = 152 := by
  rw [det_three_of_equiv, Matrix.det_fin_three]
  decide

lemma threeSite_detZ_b12 :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₁₁.toBlocks₂₂.det
      = 152 := by
  rw [det_three_of_equiv, Matrix.det_fin_three]
  decide

lemma threeSite_detZ_b21 :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₂₂.toBlocks₁₁.det
      = 250 := by
  rw [det_three_of_equiv, Matrix.det_fin_three]
  decide

lemma threeSite_detZ_b22 :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).toBlocks₂₂.toBlocks₂₂.det
      = 250 := by
  rw [det_three_of_equiv, Matrix.det_fin_three]
  decide

/-- The integer determinant: `det(5·1 - D_Z β_Z) = 38000^2`. -/
theorem threeSite_detZ :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)).det = 38000 ^ 2 := by
  rw [det_of_toBlocks₂₁_eq_zero _ threeSite_detZ_blocks₂₁,
    det_of_toBlocks₂₁_eq_zero _ threeSite_detZ_blocks₁₁₂₁,
    det_of_toBlocks₂₁_eq_zero _ threeSite_detZ_blocks₂₂₂₁,
    threeSite_detZ_b11, threeSite_detZ_b12, threeSite_detZ_b21, threeSite_detZ_b22]
  norm_num

/-- The determinant of the matrix in `threeSite_contractInvertible`:
`det(1 - D β_3) = (304/125)^2`. -/
theorem threeSite_det :
    (1 - (periodicInput (fun _ : Fin 3 => threeSiteLocal)).toBlocks₂₂ * periodicBond 3 1).det =
      (304 / 125 : ℝ) ^ 2 := by
  rw [periodicInput_threeSite, toBlocks₂₂_smul_map, periodicBond, bond_eq_map_bondZ]
  set MZ := (5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1) with hMZ
  have hmap : MZ.map (Int.cast : ℤ → ℝ) =
      (5 : ℝ) • 1 - threeSiteInputZ.toBlocks₂₂.map (Int.cast : ℤ → ℝ) *
        (bondZ (Fin 3 × Fin 1)).map (Int.cast : ℤ → ℝ) := by
    rw [hMZ, mapZ_sub, mapZ_zsmul, mapZ_one, mapZ_mul]
    norm_num
  have h : (1 - (5 : ℝ)⁻¹ • threeSiteInputZ.toBlocks₂₂.map (Int.cast : ℤ → ℝ) *
        (bondZ (Fin 3 × Fin 1)).map (Int.cast : ℤ → ℝ)) =
      (5 : ℝ)⁻¹ • MZ.map (Int.cast : ℤ → ℝ) := by
    rw [hmap, smul_sub, smul_smul, Matrix.smul_mul]; norm_num
  have hdet : (MZ.map (Int.cast : ℤ → ℝ)).det = ((MZ.det : ℤ) : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) MZ).symm
  have hcard : Fintype.card (Eliminated 3 1) = 12 := by simp
  rw [h, Matrix.det_smul, hdet, hMZ, threeSite_detZ, hcard]
  norm_num

end Fermionic
