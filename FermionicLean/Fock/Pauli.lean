/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Defs

/-! # Commutation rules of the Pauli matrices and the string

`X_j` moves a diagonal matrix through the flip; `X_j` anticommutes with `Z_j` and
with the strings `S_k` for `j < k`, and commutes with all other `Z_k`, `S_k`.
All three families are Hermitian involutions.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

lemma bitSign_add_one (b : Fin 2) : bitSign (b + 1) = -bitSign b := by
  fin_cases b <;> simp [bitSign]

lemma bitSign_mul_self (b : Fin 2) : bitSign b * bitSign b = 1 := by
  fin_cases b <;> simp [bitSign]

lemma star_bitSign (b : Fin 2) : star (bitSign b) = bitSign b := by
  fin_cases b <;> simp [bitSign]

lemma flipPerm_symm (j : Fin n) : (flipPerm j).symm = flipPerm j := rfl

lemma flipPerm_apply (j : Fin n) (s : FockIndex n) : flipPerm j s = flip j s := rfl

/-- Lemma 2(c): moving a diagonal matrix through the flip composes its entries with the flip. -/
lemma pauliX_mul_diagonal (j : Fin n) (d : FockIndex n → ℂ) :
    pauliX j * Matrix.diagonal d = Matrix.diagonal (fun s => d (flip j s)) * pauliX j := by
  rw [pauliX, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext s t
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, id, flipPerm_symm]
  change (if flip j s = t then d (flip j s) else 0) = if s = flip j t then d (flip j s) else 0
  by_cases h : flip j s = t
  · subst h
    simp [flip_flip]
  · have h' : s ≠ flip j t := fun e => h (by rw [e, flip_flip])
    simp only [h, h', ↓reduceIte]

/-- Lemma 2(a): `X_j² = 1`. -/
lemma pauliX_mul_self (j : Fin n) : pauliX j * pauliX j = 1 := by
  rw [pauliX, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  have : (flipPerm j).trans (flipPerm j) = Equiv.refl _ := by
    ext s k
    simp only [Equiv.trans_apply, Equiv.refl_apply]
    have : (flipPerm j) ((flipPerm j) s) = s := flip_flip j s
    rw [this]
  rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- Lemma 2(a): `Z_j² = 1`. -/
lemma pauliZ_mul_self (j : Fin n) : pauliZ j * pauliZ j = 1 := by
  simp [pauliZ, Matrix.diagonal_mul_diagonal, bitSign_mul_self]

lemma jwString_entry_mul_self (j : Fin n) (s : FockIndex n) :
    (∏ k : Fin n, if k < j then bitSign (s k) else 1) *
      (∏ k : Fin n, if k < j then bitSign (s k) else 1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  split_ifs <;> simp [bitSign_mul_self]

/-- Lemma 2(a): `S_j² = 1`. -/
lemma jwString_mul_self (j : Fin n) : jwString j * jwString j = 1 := by
  simp [jwString, Matrix.diagonal_mul_diagonal, jwString_entry_mul_self]

/-- The flip permutation matrix is symmetric. -/
lemma pauliX_transpose (j : Fin n) : (pauliX j).transpose = pauliX j := by
  rw [pauliX, ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, flipPerm_symm]

/-- Lemma 2(a): `X_j` is Hermitian. -/
lemma pauliX_conjTranspose (j : Fin n) : (pauliX j).conjTranspose = pauliX j := by
  rw [Matrix.conjTranspose, pauliX_transpose]
  ext s t
  simp only [Matrix.map_apply, pauliX, PEquiv.toMatrix_apply]
  split_ifs <;> simp

lemma diagonal_conjTranspose_of_star (d : FockIndex n → ℂ) (hd : ∀ s, star (d s) = d s) :
    (Matrix.diagonal d).conjTranspose = Matrix.diagonal d := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext s
  exact hd s

/-- Lemma 2(a): `Z_j` is Hermitian. -/
lemma pauliZ_conjTranspose (j : Fin n) : (pauliZ j).conjTranspose = pauliZ j :=
  diagonal_conjTranspose_of_star _ fun s => star_bitSign (s j)

/-- Lemma 2(a): `S_j` is Hermitian. -/
lemma jwString_conjTranspose (j : Fin n) : (jwString j).conjTranspose = jwString j := by
  refine diagonal_conjTranspose_of_star _ fun s => ?_
  rw [star_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp [star_bitSign]

/-- Lemma 2(b): flips of different modes commute. -/
lemma pauliX_mul_pauliX_comm (j k : Fin n) : pauliX j * pauliX k = pauliX k * pauliX j := by
  simp only [pauliX]
  rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, ← PEquiv.toMatrix_trans,
    ← Equiv.toPEquiv_trans]
  congr 2
  ext s i
  simp only [Equiv.trans_apply, flipPerm_apply]
  by_cases hij : i = j <;> by_cases hik : i = k
  · subst hij; subst hik; rfl
  · subst hij
    simp only [flip_apply_self, flip_apply_ne hik]
  · subst hik
    simp only [flip_apply_self, flip_apply_ne hij]
  · simp only [flip_apply_ne hij, flip_apply_ne hik]

/-- Lemma 2(d): `X_j Z_j = -Z_j X_j`. -/
lemma pauliX_mul_pauliZ (j : Fin n) : pauliX j * pauliZ j = -(pauliZ j * pauliX j) := by
  rw [pauliZ, pauliX_mul_diagonal, ← Matrix.neg_mul]
  congr 1
  ext s t
  simp only [Matrix.diagonal_apply, Matrix.neg_apply, flip_apply_self, bitSign_add_one]
  split_ifs <;> simp

/-- Lemma 2(d): `X_j Z_k = Z_k X_j` for `k ≠ j`. -/
lemma pauliX_mul_pauliZ_of_ne {j k : Fin n} (h : k ≠ j) :
    pauliX j * pauliZ k = pauliZ k * pauliX j := by
  rw [pauliZ, pauliX_mul_diagonal]
  congr 1
  ext s t
  simp [Matrix.diagonal_apply, flip_apply_ne h]

lemma jwString_entry_flip (j k : Fin n) (s : FockIndex n) :
    (∏ i : Fin n, if i < k then bitSign (flip j s i) else 1) =
      (if j < k then -1 else 1) * ∏ i : Fin n, if i < k then bitSign (s i) else 1 := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => if i < k then bitSign (s i) else 1)
      (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, (if i < k then bitSign (flip j s i) else 1) =
      ∏ i ∈ Finset.univ.erase j, (if i < k then bitSign (s i) else 1) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [flip_apply_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, flip_apply_self]
  by_cases hjk : j < k
  · simp [hjk, bitSign_add_one]
  · simp [hjk]

/-- Lemma 2(e): `X_j S_k = ± S_k X_j`, with the sign `-1` exactly when `j < k`. -/
lemma pauliX_mul_jwString (j k : Fin n) :
    pauliX j * jwString k = (if j < k then -1 else 1) • (jwString k * pauliX j) := by
  rw [jwString, pauliX_mul_diagonal, ← Matrix.smul_mul]
  congr 1
  ext s t
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, jwString_entry_flip]
  split_ifs <;> simp

lemma pauliX_mul_jwString_of_lt {j k : Fin n} (h : j < k) :
    pauliX j * jwString k = -(jwString k * pauliX j) := by
  rw [pauliX_mul_jwString]; simp [h]

lemma pauliX_mul_jwString_of_le {j k : Fin n} (h : k ≤ j) :
    pauliX j * jwString k = jwString k * pauliX j := by
  rw [pauliX_mul_jwString]; simp [not_lt.mpr h]

/-- Lemma 2(b): the diagonal families commute. -/
lemma pauliZ_mul_jwString_comm (j k : Fin n) :
    pauliZ j * jwString k = jwString k * pauliZ j := by
  simp [pauliZ, jwString, Matrix.diagonal_mul_diagonal, mul_comm]

lemma jwString_mul_jwString_comm (j k : Fin n) :
    jwString j * jwString k = jwString k * jwString j := by
  simp [jwString, Matrix.diagonal_mul_diagonal, mul_comm]

lemma pauliZ_mul_pauliZ_comm (j k : Fin n) : pauliZ j * pauliZ k = pauliZ k * pauliZ j := by
  simp [pauliZ, Matrix.diagonal_mul_diagonal, mul_comm]

end Fermionic
