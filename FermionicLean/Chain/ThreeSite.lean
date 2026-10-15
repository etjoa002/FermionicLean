/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.Periodic

/-! # A three-site periodic chain, evaluated exactly

`N = 3`, `M = P = 1`, the same pure local matrix at every site. All matrices are scaled
to integer entries, the identities are decided over `ℤ`, and the result is cast to `ℝ`.
-/

open Matrix

namespace Fermionic

/-! ### Integer forms of the chain constructions -/

section IntegerForms

variable {N M P : ℕ}

/-- The periodic input over `ℤ` (same formula as `periodicInput`). -/
def periodicInputZ (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℤ) :
    Matrix (Retained N P ⊕ Eliminated N M) (Retained N P ⊕ Eliminated N M) ℤ :=
  ((Matrix.blockDiagonal Γ).submatrix (siteMajorEquiv N M P) (siteMajorEquiv N M P)).submatrix
    (chainEquiv N M P) (chainEquiv N M P)

/-- The bond covariance over `ℤ`. -/
def bondZ (L : Type*) [Fintype L] [DecidableEq L] : Matrix (PairIndex L) (PairIndex L) ℤ :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 1 (-1) 0) 0 0 (-(Matrix.fromBlocks 0 1 (-1) 0))

lemma bond_eq_map_bondZ (L : Type*) [Fintype L] [DecidableEq L] :
    bond L = (bondZ L).map (Int.cast : ℤ → ℝ) := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [bond, bondZ, pairing, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

section CastLemmas

variable {ι κ μ : Type*} [Fintype κ]

lemma mapZ_mul (A : Matrix ι κ ℤ) (B : Matrix κ μ ℤ) :
    (A * B).map (Int.cast : ℤ → ℝ) = A.map Int.cast * B.map Int.cast := by
  ext i j; simp [Matrix.mul_apply]

omit [Fintype κ] in
lemma mapZ_add (A B : Matrix ι μ ℤ) :
    (A + B).map (Int.cast : ℤ → ℝ) = A.map Int.cast + B.map Int.cast := by
  ext i j; simp

omit [Fintype κ] in
lemma mapZ_sub (A B : Matrix ι μ ℤ) :
    (A - B).map (Int.cast : ℤ → ℝ) = A.map Int.cast - B.map Int.cast := by
  ext i j; simp

omit [Fintype κ] in
lemma mapZ_zsmul (n : ℤ) (A : Matrix ι μ ℤ) :
    (n • A).map (Int.cast : ℤ → ℝ) = (n : ℝ) • A.map Int.cast := by
  ext i j; simp

omit [Fintype κ] in
lemma mapZ_one [DecidableEq ι] : (1 : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ) = 1 := by
  ext i j; simp [Matrix.one_apply]

omit [Fintype κ] in
lemma mapZ_neg (A : Matrix ι μ ℤ) : (-A).map (Int.cast : ℤ → ℝ) = -A.map Int.cast := by
  ext i j; simp

omit [Fintype κ] in
lemma mapZ_transpose (A : Matrix ι μ ℤ) :
    A.transpose.map (Int.cast : ℤ → ℝ) = (A.map Int.cast).transpose := by
  ext i j; simp

end CastLemmas

lemma periodicInput_smul_map (c : ℝ) (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℤ) :
    periodicInput (fun i => c • (Γ i).map (Int.cast : ℤ → ℝ)) =
      c • (periodicInputZ Γ).map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [periodicInput, periodicInputZ, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.blockDiagonal_apply]
  split_ifs <;> simp

end IntegerForms

/-! ### The example -/

/-- Labels `(x_A, x_B, x_C, y_A, y_B, y_C)` as `Fin 6`. -/
def siteLabelIdx : SiteLabel 1 1 → Fin 6
  | Sum.inl (Sum.inl (Sum.inl _)) => 0
  | Sum.inl (Sum.inl (Sum.inr _)) => 1
  | Sum.inl (Sum.inr _) => 2
  | Sum.inr (Sum.inl (Sum.inl _)) => 3
  | Sum.inr (Sum.inl (Sum.inr _)) => 4
  | Sum.inr (Sum.inr _) => 5

/-- `5 Γ_loc` on `(x_A, x_B, x_C, y_A, y_B, y_C)`. -/
def threeSiteLocalZ : Matrix (SiteLabel 1 1) (SiteLabel 1 1) ℤ :=
  (!![0, 3, -4, 0, 0, 0;
      -3, 0, 0, 0, 0, -4;
      4, 0, 0, 0, 0, -3;
      0, 0, 0, 0, -5, 0;
      0, 0, 0, 5, 0, 0;
      0, 4, 3, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).submatrix siteLabelIdx siteLabelIdx

/-- The local matrix `Γ_loc` of the three-site example. -/
noncomputable def threeSiteLocal : Matrix (SiteLabel 1 1) (SiteLabel 1 1) ℝ :=
  (5 : ℝ)⁻¹ • threeSiteLocalZ.map (Int.cast : ℤ → ℝ)

/-- Physical labels `(x_{C_0}, x_{C_1}, x_{C_2}, y_{C_0}, y_{C_1}, y_{C_2})` as `Fin 6`. -/
def retainedIdx : Retained 3 1 → Fin 6
  | Sum.inl (i, _) => ⟨i.val, by omega⟩
  | Sum.inr (i, _) => ⟨i.val + 3, by omega⟩

/-- `19 Γ_3`: the circulant output. -/
def threeSiteOutputZ : Matrix (Retained 3 1) (Retained 3 1) ℤ :=
  (!![0, 0, 0, -15, 6, -10;
      0, 0, 0, -10, -15, 6;
      0, 0, 0, 6, -10, -15;
      15, 10, -6, 0, 0, 0;
      -6, 15, 10, 0, 0, 0;
      10, -6, 15, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).submatrix retainedIdx retainedIdx

/-- The periodic covariance of the three-site example. -/
noncomputable def threeSiteOutput : Matrix (Retained 3 1) (Retained 3 1) ℝ :=
  (19 : ℝ)⁻¹ • threeSiteOutputZ.map (Int.cast : ℤ → ℝ)

/-- Eliminated labels `(x_L, x_L', y_L, y_L')`, each `Fin 3 × Fin 1`, as `Fin 12`. -/
def eliminatedIdx : Eliminated 3 1 → Fin 12
  | Sum.inl (Sum.inl (i, _)) => ⟨i.val, by omega⟩
  | Sum.inl (Sum.inr (i, _)) => ⟨i.val + 3, by omega⟩
  | Sum.inr (Sum.inl (i, _)) => ⟨i.val + 6, by omega⟩
  | Sum.inr (Sum.inr (i, _)) => ⟨i.val + 9, by omega⟩

/-- `152 (1 - D β_3)⁻¹`. -/
def threeSiteInvZ : Matrix (Eliminated 3 1) (Eliminated 3 1) ℤ :=
  (!![125, -75, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      45, 125, -75, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      -75, 45, 125, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 125, 45, -75, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -75, 125, 45, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 45, -75, 125, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 76, -76, 76, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 76, 76, -76, 0, 0, 0;
      0, 0, 0, 0, 0, 0, -76, 76, 76, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 76, -76;
      0, 0, 0, 0, 0, 0, 0, 0, 0, -76, 76, 76;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 76, -76, 76] : Matrix (Fin 12) (Fin 12) ℤ).submatrix
    eliminatedIdx eliminatedIdx

/-- The chain data of the example over `ℤ`. -/
def threeSiteInputZ : Matrix (Retained 3 1 ⊕ Eliminated 3 1) (Retained 3 1 ⊕ Eliminated 3 1) ℤ :=
  periodicInputZ (fun _ : Fin 3 => threeSiteLocalZ)

/-! ### Integer identities, decided by evaluation -/

lemma threeSiteLocalZ_transpose : threeSiteLocalZ.transpose = -threeSiteLocalZ := by decide

lemma threeSiteLocalZ_mul_self : threeSiteLocalZ * threeSiteLocalZ = -(25 : ℤ) • 1 := by decide

/-- `(5·1 - D_Z β_Z) Y_Z = 760·1`, where `D = D_Z/5`, `Y = Y_Z/152`. -/
lemma threeSite_inv_identity :
    ((5 : ℤ) • 1 - threeSiteInputZ.toBlocks₂₂ * bondZ (Fin 3 × Fin 1)) * threeSiteInvZ =
      (760 : ℤ) • 1 := by decide

/-- With `A = A_Z/5`, `B = B_Z/5`, `C = C_Z/5`, `Y = Y_Z/152`, `Γ_3 = O_Z/19`, the identity
`Γ_3 = A + B β Y C` times `5·5·152·19 = 72200` reads `14440 A_Z + 19 B_Z β_Z Y_Z C_Z = 3800 O_Z`. -/
lemma threeSite_output_identity :
    (14440 : ℤ) • threeSiteInputZ.toBlocks₁₁ +
      (19 : ℤ) • (threeSiteInputZ.toBlocks₁₂ * bondZ (Fin 3 × Fin 1) * threeSiteInvZ *
        threeSiteInputZ.toBlocks₂₁) =
      (3800 : ℤ) • threeSiteOutputZ := by decide

/-! ### Real statements -/

theorem pure_threeSiteLocal : Pure threeSiteLocal := by
  refine ⟨?_, ?_⟩
  · rw [threeSiteLocal, Matrix.transpose_smul, ← mapZ_transpose, threeSiteLocalZ_transpose,
      mapZ_neg, smul_neg]
  · rw [threeSiteLocal, smul_mul_smul_comm, ← mapZ_mul, threeSiteLocalZ_mul_self, mapZ_zsmul,
      mapZ_one, smul_smul]
    norm_num

lemma periodicInput_threeSite :
    periodicInput (fun _ : Fin 3 => threeSiteLocal) =
      (5 : ℝ)⁻¹ • threeSiteInputZ.map (Int.cast : ℤ → ℝ) := by
  unfold threeSiteLocal threeSiteInputZ
  exact periodicInput_smul_map _ _

section Blocks

variable {ι κ : Type*}

lemma toBlocks₁₁_smul_map (c : ℝ) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ) :
    (c • A.map (Int.cast : ℤ → ℝ)).toBlocks₁₁ = c • A.toBlocks₁₁.map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [Matrix.toBlocks₁₁]

lemma toBlocks₁₂_smul_map (c : ℝ) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ) :
    (c • A.map (Int.cast : ℤ → ℝ)).toBlocks₁₂ = c • A.toBlocks₁₂.map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [Matrix.toBlocks₁₂]

lemma toBlocks₂₁_smul_map (c : ℝ) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ) :
    (c • A.map (Int.cast : ℤ → ℝ)).toBlocks₂₁ = c • A.toBlocks₂₁.map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [Matrix.toBlocks₂₁]

lemma toBlocks₂₂_smul_map (c : ℝ) (A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℤ) :
    (c • A.map (Int.cast : ℤ → ℝ)).toBlocks₂₂ = c • A.toBlocks₂₂.map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [Matrix.toBlocks₂₂]

end Blocks

/-- The real right inverse: `(1 - D β_3) (Y_Z/152) = 1`. -/
lemma threeSite_right_inverse :
    (1 - (periodicInput (fun _ : Fin 3 => threeSiteLocal)).toBlocks₂₂ * periodicBond 3 1) *
      ((152 : ℝ)⁻¹ • threeSiteInvZ.map (Int.cast : ℤ → ℝ)) = 1 := by
  rw [periodicInput_threeSite, toBlocks₂₂_smul_map, periodicBond, bond_eq_map_bondZ]
  have key := congrArg (fun X : Matrix (Eliminated 3 1) (Eliminated 3 1) ℤ =>
    X.map (Int.cast : ℤ → ℝ)) threeSite_inv_identity
  simp only [mapZ_mul, mapZ_sub, mapZ_zsmul, mapZ_one, Int.cast_ofNat] at key
  set DZ := threeSiteInputZ.toBlocks₂₂.map (Int.cast : ℤ → ℝ)
  set BZ := (bondZ (Fin 3 × Fin 1)).map (Int.cast : ℤ → ℝ)
  set YZ := threeSiteInvZ.map (Int.cast : ℤ → ℝ)
  have h : (1 - (5 : ℝ)⁻¹ • DZ * BZ) = (5 : ℝ)⁻¹ • ((5 : ℝ) • 1 - DZ * BZ) := by
    rw [smul_sub, smul_smul, Matrix.smul_mul]; norm_num
  rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  norm_num

/-- The real inverse `(1 - D β_3)⁻¹ = Y_Z / 152`. -/
lemma threeSite_inv_eq :
    (1 - (periodicInput (fun _ : Fin 3 => threeSiteLocal)).toBlocks₂₂ * periodicBond 3 1)⁻¹ =
      (152 : ℝ)⁻¹ • threeSiteInvZ.map (Int.cast : ℤ → ℝ) :=
  Matrix.inv_eq_right_inv threeSite_right_inverse

/-- Proposition 6: the three-site chain is contractible. -/
theorem threeSite_contractInvertible :
    ContractInvertible (periodicInput (fun _ : Fin 3 => threeSiteLocal)) (periodicBond 3 1) :=
  Matrix.isUnit_det_of_right_inverse threeSite_right_inverse

/-- Proposition 6: the periodic covariance of the three-site example. -/
theorem periodicCovariance_threeSite :
    periodicCovariance (fun _ : Fin 3 => threeSiteLocal) = threeSiteOutput := by
  unfold periodicCovariance contract
  rw [threeSite_inv_eq, periodicInput_threeSite, toBlocks₁₁_smul_map, toBlocks₁₂_smul_map,
    toBlocks₂₁_smul_map, periodicBond, bond_eq_map_bondZ, threeSiteOutput]
  have key := congrArg (fun X : Matrix (Retained 3 1) (Retained 3 1) ℤ =>
    X.map (Int.cast : ℤ → ℝ)) threeSite_output_identity
  simp only [mapZ_mul, mapZ_add, mapZ_zsmul, Int.cast_ofNat] at key
  set AZ := threeSiteInputZ.toBlocks₁₁.map (Int.cast : ℤ → ℝ)
  set BZ := threeSiteInputZ.toBlocks₁₂.map (Int.cast : ℤ → ℝ)
  set CZ := threeSiteInputZ.toBlocks₂₁.map (Int.cast : ℤ → ℝ)
  set βZ := (bondZ (Fin 3 × Fin 1)).map (Int.cast : ℤ → ℝ)
  set YZ := threeSiteInvZ.map (Int.cast : ℤ → ℝ)
  set OZ := threeSiteOutputZ.map (Int.cast : ℤ → ℝ)
  apply smul_right_injective (Matrix (Retained 3 1) (Retained 3 1) ℝ)
    (show (72200 : ℝ) ≠ 0 by norm_num)
  simp only [smul_add, smul_smul, Matrix.smul_mul, Matrix.mul_smul]
  norm_num
  exact key

end Fermionic
