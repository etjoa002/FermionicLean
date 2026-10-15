/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Wick
import FermionicLean.Fock.Parity
import FermionicLean.Fock.Hamiltonian
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # The partial trace

Fock space of `n + m` modes splits as `𝓕_n ⊗ 𝓕_m`: a configuration `s` is the pair of its
first `n` and last `m` bits (`fockSplit`), and `tensor X Y` is the Kronecker product reindexed
along this split. The Majorana operators of the retained modes `j < n` are `c_j ⊗ 1`, those of
the eliminated modes `n + j` are `P_n ⊗ c_j` (Lemma 2). The partial traces `ptraceE` (over the
last `m` modes) and `ptraceR` (over the first `n`) satisfy the usual calculus (Lemma 3), and the
marginals of a Gaussian state are Gaussian with the diagonal blocks of its covariance
(Theorem 4).
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

/-! ### Definition 1: the split, the tensor product and the partial traces -/

/-- The split `{0,1}^(n+m) ≃ {0,1}^n × {0,1}^m` into the first `n` and the last `m` bits. -/
def fockSplit (n m : ℕ) : FockIndex (n + m) ≃ FockIndex n × FockIndex m :=
  (finSumFinEquiv.arrowCongr (Equiv.refl (Fin 2))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) (Fin 2))

/-- The split of the Majorana labels: retained labels (modes `j < n`) first. -/
def labelSplit (n m : ℕ) : MajoranaIndex (n + m) ≃ MajoranaIndex n ⊕ MajoranaIndex m :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin n) (Fin m) (Fin n) (Fin m))

variable {n m : ℕ}

@[simp]
lemma fockSplit_apply_fst (s : FockIndex (n + m)) (j : Fin n) :
    (fockSplit n m s).1 j = s (Fin.castAdd m j) := by
  simp [fockSplit]

@[simp]
lemma fockSplit_apply_snd (s : FockIndex (n + m)) (j : Fin m) :
    (fockSplit n m s).2 j = s (Fin.natAdd n j) := by
  simp [fockSplit]

@[simp]
lemma fockSplit_symm_apply_castAdd (p : FockIndex n × FockIndex m) (j : Fin n) :
    (fockSplit n m).symm p (Fin.castAdd m j) = p.1 j := by
  obtain ⟨a, b⟩ := p
  simp [fockSplit]

@[simp]
lemma fockSplit_symm_apply_natAdd (p : FockIndex n × FockIndex m) (j : Fin m) :
    (fockSplit n m).symm p (Fin.natAdd n j) = p.2 j := by
  obtain ⟨a, b⟩ := p
  simp [fockSplit]

@[simp]
lemma labelSplit_inl_castAdd (j : Fin n) :
    labelSplit n m (Sum.inl (Fin.castAdd m j)) = Sum.inl (Sum.inl j) := by
  simp [labelSplit, Equiv.sumSumSumComm]

@[simp]
lemma labelSplit_inr_castAdd (j : Fin n) :
    labelSplit n m (Sum.inr (Fin.castAdd m j)) = Sum.inl (Sum.inr j) := by
  simp [labelSplit, Equiv.sumSumSumComm]

@[simp]
lemma labelSplit_inl_natAdd (j : Fin m) :
    labelSplit n m (Sum.inl (Fin.natAdd n j)) = Sum.inr (Sum.inl j) := by
  simp [labelSplit, Equiv.sumSumSumComm]

@[simp]
lemma labelSplit_inr_natAdd (j : Fin m) :
    labelSplit n m (Sum.inr (Fin.natAdd n j)) = Sum.inr (Sum.inr j) := by
  simp [labelSplit, Equiv.sumSumSumComm]

/-- The retained labels, embedded in the labels of `n + m` modes. -/
def embedR (a : MajoranaIndex n) : MajoranaIndex (n + m) := (labelSplit n m).symm (Sum.inl a)

/-- The eliminated labels, embedded in the labels of `n + m` modes. -/
def embedE (a : MajoranaIndex m) : MajoranaIndex (n + m) := (labelSplit n m).symm (Sum.inr a)

@[simp]
lemma embedR_inl (j : Fin n) : embedR (m := m) (Sum.inl j) = Sum.inl (Fin.castAdd m j) := by
  rw [embedR, Equiv.symm_apply_eq, labelSplit_inl_castAdd]

@[simp]
lemma embedR_inr (j : Fin n) : embedR (m := m) (Sum.inr j) = Sum.inr (Fin.castAdd m j) := by
  rw [embedR, Equiv.symm_apply_eq, labelSplit_inr_castAdd]

@[simp]
lemma embedE_inl (j : Fin m) : embedE (n := n) (Sum.inl j) = Sum.inl (Fin.natAdd n j) := by
  rw [embedE, Equiv.symm_apply_eq, labelSplit_inl_natAdd]

@[simp]
lemma embedE_inr (j : Fin m) : embedE (n := n) (Sum.inr j) = Sum.inr (Fin.natAdd n j) := by
  rw [embedE, Equiv.symm_apply_eq, labelSplit_inr_natAdd]

@[simp]
lemma labelSplit_embedR (a : MajoranaIndex n) : labelSplit n m (embedR a) = Sum.inl a := by
  simp [embedR]

@[simp]
lemma labelSplit_embedE (a : MajoranaIndex m) : labelSplit n m (embedE a) = Sum.inr a := by
  simp [embedE]

lemma embedR_injective : Function.Injective (embedR (n := n) (m := m)) :=
  (labelSplit n m).symm.injective.comp Sum.inl_injective

lemma embedE_injective : Function.Injective (embedE (n := n) (m := m)) :=
  (labelSplit n m).symm.injective.comp Sum.inr_injective

/-- The tensor product `X ⊗ Y` of matrices on `𝓕_n` and `𝓕_m`, as a matrix on `𝓕_(n+m)`. -/
def tensor (X : Matrix (FockIndex n) (FockIndex n) ℂ) (Y : Matrix (FockIndex m) (FockIndex m) ℂ) :
    Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ :=
  (Matrix.kroneckerMap (· * ·) X Y).submatrix (fockSplit n m) (fockSplit n m)

/-- The partial trace over the eliminated (last `m`) modes. -/
def ptraceE (M : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  fun s t => ∑ u, M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t, u))

/-- The partial trace over the retained (first `n`) modes. -/
def ptraceR (M : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    Matrix (FockIndex m) (FockIndex m) ℂ :=
  fun s t => ∑ u, M ((fockSplit n m).symm (u, s)) ((fockSplit n m).symm (u, t))

lemma tensor_apply (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) (s t : FockIndex (n + m)) :
    tensor X Y s t =
      X (fockSplit n m s).1 (fockSplit n m t).1 * Y (fockSplit n m s).2 (fockSplit n m t).2 :=
  rfl

lemma tensor_apply_symm (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) (p q : FockIndex n × FockIndex m) :
    tensor X Y ((fockSplit n m).symm p) ((fockSplit n m).symm q) = X p.1 q.1 * Y p.2 q.2 := by
  simp [tensor_apply]

lemma ptraceE_apply (M : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) (s t : FockIndex n) :
    ptraceE M s t = ∑ u, M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t, u)) :=
  rfl

lemma ptraceR_apply (M : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) (s t : FockIndex m) :
    ptraceR M s t = ∑ u, M ((fockSplit n m).symm (u, s)) ((fockSplit n m).symm (u, t)) :=
  rfl

/-- A sum over configurations of `n + m` modes, split. -/
lemma sum_fockSplit (F : FockIndex (n + m) → ℂ) :
    ∑ z, F z = ∑ s, ∑ u, F ((fockSplit n m).symm (s, u)) := by
  rw [← Equiv.sum_comp (fockSplit n m).symm, Fintype.sum_prod_type]

/-! ### The tensor product calculus -/

lemma tensor_mul_tensor (X X' : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y Y' : Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor X Y * tensor X' Y' = tensor (X * X') (Y * Y') := by
  rw [tensor, tensor, tensor, Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

lemma tensor_diagonal_diagonal (d : FockIndex n → ℂ) (d' : FockIndex m → ℂ) :
    tensor (Matrix.diagonal d) (Matrix.diagonal d') =
      Matrix.diagonal fun s => d (fockSplit n m s).1 * d' (fockSplit n m s).2 := by
  rw [tensor, Matrix.diagonal_kronecker_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

lemma tensor_one_one : tensor (1 : Matrix (FockIndex n) (FockIndex n) ℂ)
    (1 : Matrix (FockIndex m) (FockIndex m) ℂ) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

lemma tensor_smul_left (c : ℂ) (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) : tensor (c • X) Y = c • tensor X Y := by
  ext s t
  simp only [tensor_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

lemma tensor_smul_right (c : ℂ) (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) : tensor X (c • Y) = c • tensor X Y := by
  ext s t
  simp only [tensor_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma tensor_add_left (X X' : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) : tensor (X + X') Y = tensor X Y + tensor X' Y := by
  ext s t
  simp only [tensor_apply, Matrix.add_apply, add_mul]

lemma tensor_add_right (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y Y' : Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor X (Y + Y') = tensor X Y + tensor X Y' := by
  ext s t
  simp only [tensor_apply, Matrix.add_apply, mul_add]

lemma tensor_sub_left (X X' : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) : tensor (X - X') Y = tensor X Y - tensor X' Y := by
  ext s t
  simp only [tensor_apply, Matrix.sub_apply, sub_mul]

lemma tensor_sub_right (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y Y' : Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor X (Y - Y') = tensor X Y - tensor X Y' := by
  ext s t
  simp only [tensor_apply, Matrix.sub_apply, mul_sub]

lemma tensor_sum_left {ι : Type*} (S : Finset ι) (X : ι → Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor (∑ i ∈ S, X i) Y = ∑ i ∈ S, tensor (X i) Y := by
  ext s t
  simp only [tensor_apply, Matrix.sum_apply, Finset.sum_mul]

lemma tensor_sum_right {ι : Type*} (S : Finset ι) (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : ι → Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor X (∑ i ∈ S, Y i) = ∑ i ∈ S, tensor X (Y i) := by
  ext s t
  simp only [tensor_apply, Matrix.sum_apply, Finset.mul_sum]

lemma tensor_conjTranspose (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) :
    (tensor X Y).conjTranspose = tensor X.conjTranspose Y.conjTranspose := by
  ext s t
  simp only [tensor_apply, Matrix.conjTranspose_apply, star_mul']

/-- `X ⊗ 1` commutes with `1 ⊗ Y`. -/
lemma tensor_one_mul_tensor_one_comm (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) :
    tensor X 1 * tensor 1 Y = tensor 1 Y * tensor X 1 := by
  rw [tensor_mul_tensor, tensor_mul_tensor, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul]

lemma tensor_eq_mul (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Y : Matrix (FockIndex m) (FockIndex m) ℂ) : tensor X Y = tensor X 1 * tensor 1 Y := by
  rw [tensor_mul_tensor, Matrix.mul_one, Matrix.one_mul]

lemma tensor_list_prod_one (L : List (Matrix (FockIndex n) (FockIndex n) ℂ)) :
    tensor L.prod (1 : Matrix (FockIndex m) (FockIndex m) ℂ) =
      (L.map fun X => tensor X 1).prod := by
  induction L with
  | nil => exact tensor_one_one
  | cons X L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, tensor_mul_tensor,
      Matrix.mul_one]

/-! ### Lemma 2: the Majorana operators of a split -/

lemma pauliX_apply (j : Fin n) (s t : FockIndex n) :
    pauliX j s t = if flip j s = t then 1 else 0 := by
  simp only [pauliX, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, flipPerm_apply]

lemma fockSplit_flip_castAdd (j : Fin n) (s : FockIndex (n + m)) :
    fockSplit n m (flip (Fin.castAdd m j) s) =
      (flip j (fockSplit n m s).1, (fockSplit n m s).2) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · by_cases hk : k = j
    · subst hk
      simp [flip_apply_self]
    · have hk' : Fin.castAdd m k ≠ Fin.castAdd m j := fun h => hk (by simpa using h)
      simp [flip_apply_ne hk, flip_apply_ne hk']
  · have hk' : Fin.natAdd n k ≠ Fin.castAdd m j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    simp [flip_apply_ne hk']

lemma fockSplit_flip_natAdd (j : Fin m) (s : FockIndex (n + m)) :
    fockSplit n m (flip (Fin.natAdd n j) s) =
      ((fockSplit n m s).1, flip j (fockSplit n m s).2) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · have hk' : Fin.castAdd m k ≠ Fin.natAdd n j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    simp [flip_apply_ne hk']
  · by_cases hk : k = j
    · subst hk
      simp [flip_apply_self]
    · have hk' : Fin.natAdd n k ≠ Fin.natAdd n j := fun h => hk ((Fin.natAdd_inj n).mp h)
      simp [flip_apply_ne hk, flip_apply_ne hk']

lemma pauliX_castAdd (j : Fin n) :
    pauliX (Fin.castAdd m j) = tensor (pauliX j) (1 : Matrix (FockIndex m) (FockIndex m) ℂ) := by
  ext s t
  have key : flip (Fin.castAdd m j) s = t ↔ flip j (fockSplit n m s).1 = (fockSplit n m t).1 ∧
      (fockSplit n m s).2 = (fockSplit n m t).2 := by
    rw [← (fockSplit n m).apply_eq_iff_eq, fockSplit_flip_castAdd, Prod.ext_iff]
  rw [pauliX_apply, tensor_apply, pauliX_apply, Matrix.one_apply]
  simp only [key]
  split_ifs <;> simp_all

lemma pauliX_natAdd (j : Fin m) :
    pauliX (Fin.natAdd n j) = tensor (1 : Matrix (FockIndex n) (FockIndex n) ℂ) (pauliX j) := by
  ext s t
  have key : flip (Fin.natAdd n j) s = t ↔ (fockSplit n m s).1 = (fockSplit n m t).1 ∧
      flip j (fockSplit n m s).2 = (fockSplit n m t).2 := by
    rw [← (fockSplit n m).apply_eq_iff_eq, fockSplit_flip_natAdd, Prod.ext_iff]
  rw [pauliX_apply, tensor_apply, pauliX_apply, Matrix.one_apply]
  simp only [key]
  split_ifs <;> simp_all

lemma pauliZ_castAdd (j : Fin n) :
    pauliZ (Fin.castAdd m j) = tensor (pauliZ j) (1 : Matrix (FockIndex m) (FockIndex m) ℂ) := by
  rw [pauliZ, pauliZ, ← Matrix.diagonal_one, tensor_diagonal_diagonal]
  congr 1
  funext s
  simp

lemma pauliZ_natAdd (j : Fin m) :
    pauliZ (Fin.natAdd n j) = tensor (1 : Matrix (FockIndex n) (FockIndex n) ℂ) (pauliZ j) := by
  rw [pauliZ, pauliZ, ← Matrix.diagonal_one, tensor_diagonal_diagonal]
  congr 1
  funext s
  simp

lemma jwString_castAdd (j : Fin n) :
    jwString (Fin.castAdd m j) =
      tensor (jwString j) (1 : Matrix (FockIndex m) (FockIndex m) ℂ) := by
  rw [jwString, jwString, ← Matrix.diagonal_one, tensor_diagonal_diagonal]
  congr 1
  funext s
  have hB : ∏ i : Fin m, (if Fin.natAdd n i < Fin.castAdd m j then bitSign (s (Fin.natAdd n i))
      else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hj := j.isLt
    have : ¬ Fin.natAdd n i < Fin.castAdd m j := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      omega
    simp [this]
  rw [Fin.prod_univ_add, hB]
  simp only [mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.lt_def, Fin.val_castAdd, fockSplit_apply_fst]

lemma jwString_natAdd (j : Fin m) :
    jwString (Fin.natAdd n j) = tensor parity (jwString j) := by
  rw [jwString, jwString, parity, tensor_diagonal_diagonal]
  congr 1
  funext s
  rw [Fin.prod_univ_add, paritySign]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.isLt
    have : Fin.castAdd m i < Fin.natAdd n j := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      omega
    simp [this]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.lt_def, Fin.val_natAdd, fockSplit_apply_snd, Nat.add_lt_add_iff_left]

/-- `P_(n+m) = P_n ⊗ P_m`. -/
lemma parity_split :
    (parity : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) = tensor parity parity := by
  rw [parity, parity, parity, tensor_diagonal_diagonal]
  congr 1
  funext s
  simp [paritySign, Fin.prod_univ_add]

/-- Lemma 2: a retained Majorana operator is `c_a ⊗ 1`. -/
lemma majorana_retained_x (j : Fin n) :
    majorana (n := n + m) (Sum.inl (Fin.castAdd m j)) = tensor (majorana (Sum.inl j)) 1 := by
  simp only [majorana]
  rw [jwString_castAdd, pauliX_castAdd, tensor_mul_tensor, Matrix.mul_one]

lemma majorana_retained_y (j : Fin n) :
    majorana (n := n + m) (Sum.inr (Fin.castAdd m j)) = tensor (majorana (Sum.inr j)) 1 := by
  simp only [majorana]
  rw [jwString_castAdd, pauliX_castAdd, pauliZ_castAdd, tensor_mul_tensor, tensor_mul_tensor,
    Matrix.mul_one, Matrix.mul_one, tensor_smul_left]

/-- Lemma 2: an eliminated Majorana operator is `P_n ⊗ c_a`. -/
lemma majorana_eliminated_x (j : Fin m) :
    majorana (n := n + m) (Sum.inl (Fin.natAdd n j)) = tensor parity (majorana (Sum.inl j)) := by
  simp only [majorana]
  rw [jwString_natAdd, pauliX_natAdd, tensor_mul_tensor, Matrix.mul_one]

lemma majorana_eliminated_y (j : Fin m) :
    majorana (n := n + m) (Sum.inr (Fin.natAdd n j)) = tensor parity (majorana (Sum.inr j)) := by
  simp only [majorana]
  rw [jwString_natAdd, pauliX_natAdd, pauliZ_natAdd, tensor_mul_tensor, tensor_mul_tensor,
    Matrix.mul_one, Matrix.mul_one, tensor_smul_right]

lemma majorana_embedR (a : MajoranaIndex n) :
    majorana (embedR (m := m) a) = tensor (majorana a) 1 := by
  rcases a with j | j
  · rw [embedR_inl, majorana_retained_x]
  · rw [embedR_inr, majorana_retained_y]

lemma majorana_embedE (a : MajoranaIndex m) :
    majorana (embedE (n := n) a) = tensor parity (majorana a) := by
  rcases a with j | j
  · rw [embedE_inl, majorana_eliminated_x]
  · rw [embedE_inr, majorana_eliminated_y]

/-- A vector on the retained labels, extended by zero. -/
def extendR (v : MajoranaIndex n → ℂ) : MajoranaIndex (n + m) → ℂ :=
  Sum.elim v 0 ∘ labelSplit n m

/-- A vector on the eliminated labels, extended by zero. -/
def extendE (v : MajoranaIndex m → ℂ) : MajoranaIndex (n + m) → ℂ :=
  Sum.elim 0 v ∘ labelSplit n m

@[simp]
lemma extendR_embedR (v : MajoranaIndex n → ℂ) (a : MajoranaIndex n) :
    extendR (m := m) v (embedR a) = v a := by
  simp [extendR]

@[simp]
lemma extendR_embedE (v : MajoranaIndex n → ℂ) (a : MajoranaIndex m) :
    extendR v (embedE a) = 0 := by
  simp [extendR]

@[simp]
lemma extendE_embedR (v : MajoranaIndex m → ℂ) (a : MajoranaIndex n) :
    extendE v (embedR a) = 0 := by
  simp [extendE]

@[simp]
lemma extendE_embedE (v : MajoranaIndex m → ℂ) (a : MajoranaIndex m) :
    extendE (n := n) v (embedE a) = v a := by
  simp [extendE]

/-- A sum over the labels of `n + m` modes, split into retained and eliminated labels. -/
lemma sum_labelSplit {M : Type*} [AddCommMonoid M] (F : MajoranaIndex (n + m) → M) :
    ∑ a, F a = ∑ a, F (embedR a) + ∑ a, F (embedE a) := by
  rw [← Equiv.sum_comp (labelSplit n m).symm, Fintype.sum_sum_type]
  rfl

/-- Lemma 2: `(v̄·c) = (v·c) ⊗ 1` for `v` supported on the retained labels. -/
lemma lincomb_extendR (v : MajoranaIndex n → ℂ) :
    lincomb (extendR (m := m) v) = tensor (lincomb v) 1 := by
  rw [lincomb, lincomb, tensor_sum_left, sum_labelSplit]
  simp [majorana_embedR, tensor_smul_left]

/-- Lemma 2: `(ū·c) = P_n ⊗ (u·c)` for `u` supported on the eliminated labels. -/
lemma lincomb_extendE (v : MajoranaIndex m → ℂ) :
    lincomb (extendE (n := n) v) = tensor parity (lincomb v) := by
  rw [lincomb, lincomb, tensor_sum_right, sum_labelSplit]
  simp [majorana_embedE, tensor_smul_right]

lemma prod_lincomb_extendR (l : List (MajoranaIndex n → ℂ)) :
    ((l.map (extendR (m := m))).map lincomb).prod = tensor (l.map lincomb).prod 1 := by
  induction l with
  | nil => simp [tensor_one_one]
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, lincomb_extendR, tensor_mul_tensor, Matrix.mul_one]

lemma prod_lincomb_extendE (l : List (MajoranaIndex m → ℂ)) :
    ((l.map (extendE (n := n))).map lincomb).prod =
      tensor (parity ^ l.length) (l.map lincomb).prod := by
  induction l with
  | nil => simp [tensor_one_one]
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [ih, lincomb_extendE, tensor_mul_tensor, pow_succ']

lemma parity_pow_even {k : ℕ} (hk : Even k) :
    (parity : Matrix (FockIndex n) (FockIndex n) ℂ) ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, pow_two, parity_mul_self, one_pow]

lemma parity_pow_odd {k : ℕ} (hk : Odd k) :
    (parity : Matrix (FockIndex n) (FockIndex n) ℂ) ^ k = parity := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, pow_two, parity_mul_self, one_pow, one_mul]

/-- Lemma 2: a product of an even number of eliminated factors is `1 ⊗ ∏ (u_i·c)`. -/
lemma prod_lincomb_extendE_even (l : List (MajoranaIndex m → ℂ)) (hl : Even l.length) :
    ((l.map (extendE (n := n))).map lincomb).prod = tensor 1 (l.map lincomb).prod := by
  rw [prod_lincomb_extendE, parity_pow_even hl]

lemma prod_lincomb_extendE_odd (l : List (MajoranaIndex m → ℂ)) (hl : Odd l.length) :
    ((l.map (extendE (n := n))).map lincomb).prod = tensor parity (l.map lincomb).prod := by
  rw [prod_lincomb_extendE, parity_pow_odd hl]

lemma lincomb_single_smul (a : MajoranaIndex n) (c : ℂ) :
    lincomb (Pi.single a c) = c • majorana a := by
  simp only [lincomb, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- `Z_j = (-i c_{x_j}) c_{y_j}`, a product of two Majorana factors. -/
lemma pauliZ_eq_lincomb_mul_lincomb (j : Fin n) :
    pauliZ j =
      lincomb (Pi.single (Sum.inl j) (-Complex.I)) * lincomb (Pi.single (Sum.inr j) 1) := by
  rw [lincomb_single_smul, lincomb_single_smul, one_smul, Matrix.smul_mul, neg_smul,
    I_smul_majorana_x_mul_y, neg_neg]

/-- `P_n ⊗ 1` is a product of `2n` retained Majorana factors. -/
lemma exists_prod_lincomb_eq_tensor_parity_one :
    ∃ L : List (MajoranaIndex (n + m) → ℂ), Even L.length ∧
      (L.map lincomb).prod = tensor parity (1 : Matrix (FockIndex m) (FockIndex m) ℂ) := by
  suffices h : ∀ S : Finset (Fin n), ∃ L : List (MajoranaIndex (n + m) → ℂ), Even L.length ∧
      (L.map lincomb).prod =
        tensor (Matrix.diagonal fun s : FockIndex n => ∏ j ∈ S, bitSign (s j)) 1 by
    obtain ⟨L, hL, hprod⟩ := h Finset.univ
    exact ⟨L, hL, hprod⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨[], ⟨0, rfl⟩, by simp [tensor_one_one]⟩
  | insert j S hj ih =>
    obtain ⟨L, hL, hprod⟩ := ih
    refine ⟨Pi.single (Sum.inl (Fin.castAdd m j)) (-Complex.I) ::
      Pi.single (Sum.inr (Fin.castAdd m j)) 1 :: L, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hL
      exact ⟨k + 1, by simp only [List.length_cons]; omega⟩
    · rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
        ← pauliZ_eq_lincomb_mul_lincomb, hprod, pauliZ_castAdd, tensor_mul_tensor, Matrix.mul_one,
        pauliZ, Matrix.diagonal_mul_diagonal]
      congr 2
      funext s
      rw [Finset.prod_insert hj]

/-! ### Lemma 3: the partial-trace calculus -/

/-- A sum over configurations of `n + m` modes, split with the eliminated bits outside. -/
lemma sum_fockSplit' (F : FockIndex (n + m) → ℂ) :
    ∑ z, F z = ∑ u, ∑ s, F ((fockSplit n m).symm (s, u)) := by
  rw [← Equiv.sum_comp (fockSplit n m).symm, Fintype.sum_prod_type_right]

section ptraceE

variable (M M' : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
  (X : Matrix (FockIndex n) (FockIndex n) ℂ) (Y : Matrix (FockIndex m) (FockIndex m) ℂ)

lemma ptraceE_add : ptraceE (M + M') = ptraceE M + ptraceE M' := by
  ext s t
  simp only [ptraceE_apply, Matrix.add_apply, Finset.sum_add_distrib]

lemma ptraceE_smul (c : ℂ) : ptraceE (c • M) = c • ptraceE M := by
  ext s t
  simp only [ptraceE_apply, Matrix.smul_apply, Finset.smul_sum]

lemma ptraceE_sum {ι : Type*} (S : Finset ι)
    (F : ι → Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    ptraceE (∑ i ∈ S, F i) = ∑ i ∈ S, ptraceE (F i) := by
  ext s t
  simp only [ptraceE_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Lemma 3(a): the partial trace preserves the trace. -/
lemma trace_ptraceE : (ptraceE M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptraceE_apply]
  rw [sum_fockSplit fun z => M z z]

/-- Lemma 3(a): `Tr_E (X ⊗ Y) = (Tr Y) X`. -/
lemma ptraceE_tensor : ptraceE (tensor X Y) = Y.trace • X := by
  ext s t
  simp only [ptraceE_apply, tensor_apply_symm, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => mul_comm _ _

/-- Lemma 3(a): `Tr_E ((X ⊗ 1) M) = X Tr_E M`. -/
lemma ptraceE_tensor_one_mul : ptraceE (tensor X 1 * M) = X * ptraceE M := by
  ext s t
  simp only [ptraceE_apply, Matrix.mul_apply]
  calc ∑ u, ∑ z, tensor X 1 ((fockSplit n m).symm (s, u)) z * M z ((fockSplit n m).symm (t, u))
      = ∑ u, ∑ s', ∑ u', X s s' * (1 : Matrix (FockIndex m) (FockIndex m) ℂ) u u' *
          M ((fockSplit n m).symm (s', u')) ((fockSplit n m).symm (t, u)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit]
        simp only [tensor_apply_symm]
    _ = ∑ s', X s s' * ∑ u, M ((fockSplit n m).symm (s', u)) ((fockSplit n m).symm (t, u)) := by
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
        exact Finset.sum_comm

/-- Lemma 3(a): `Tr_E (M (X ⊗ 1)) = (Tr_E M) X`. -/
lemma ptraceE_mul_tensor_one : ptraceE (M * tensor X 1) = ptraceE M * X := by
  ext s t
  simp only [ptraceE_apply, Matrix.mul_apply]
  calc ∑ u, ∑ z, M ((fockSplit n m).symm (s, u)) z * tensor X 1 z ((fockSplit n m).symm (t, u))
      = ∑ u, ∑ t', ∑ u', M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t', u')) *
          (X t' t * (1 : Matrix (FockIndex m) (FockIndex m) ℂ) u' u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit]
        simp only [tensor_apply_symm]
    _ = ∑ t', (∑ u, M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t', u))) * X t' t := by
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, Finset.sum_mul]
        exact Finset.sum_comm

/-- Lemma 3(a): `Tr_E (M (1 ⊗ V)) = Tr_E ((1 ⊗ V) M)`. -/
lemma ptraceE_mul_one_tensor_comm (V : Matrix (FockIndex m) (FockIndex m) ℂ) :
    ptraceE (M * tensor 1 V) = ptraceE (tensor 1 V * M) := by
  ext s t
  simp only [ptraceE_apply, Matrix.mul_apply]
  calc ∑ u, ∑ z, M ((fockSplit n m).symm (s, u)) z * tensor 1 V z ((fockSplit n m).symm (t, u))
      = ∑ u, ∑ u', ∑ t', M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t', u')) *
          ((1 : Matrix (FockIndex n) (FockIndex n) ℂ) t' t * V u' u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit']
        simp only [tensor_apply_symm]
    _ = ∑ u, ∑ u', M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t, u')) * V u' u := by
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ u, ∑ u', ∑ s', (1 : Matrix (FockIndex n) (FockIndex n) ℂ) s s' * V u u' *
          M ((fockSplit n m).symm (s', u')) ((fockSplit n m).symm (t, u)) := by
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => mul_comm _ _
    _ = ∑ u, ∑ z,
          tensor 1 V ((fockSplit n m).symm (s, u)) z * M z ((fockSplit n m).symm (t, u)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit']
        simp only [tensor_apply_symm]

/-- Lemma 3(a): `Tr ((Tr_E M) X) = Tr (M (X ⊗ 1))`. -/
lemma trace_ptraceE_mul : (ptraceE M * X).trace = (M * tensor X 1).trace := by
  rw [← trace_ptraceE (M * tensor X 1), ptraceE_mul_tensor_one]

/-- Lemma 3(b): the partial trace commutes with the adjoint. -/
lemma ptraceE_conjTranspose : (ptraceE M).conjTranspose = ptraceE M.conjTranspose := by
  ext s t
  simp only [Matrix.conjTranspose_apply, ptraceE_apply, star_sum]

/-- The vector `x ⊗ e_u` on `n + m` modes. -/
def extVecE (x : FockIndex n → ℂ) (u : FockIndex m) : FockIndex (n + m) → ℂ :=
  fun z => if (fockSplit n m z).2 = u then x (fockSplit n m z).1 else 0

lemma extVecE_apply_symm (x : FockIndex n → ℂ) (u u' : FockIndex m) (s : FockIndex n) :
    extVecE x u ((fockSplit n m).symm (s, u')) = if u' = u then x s else 0 := by
  simp [extVecE]

lemma star_extVecE_apply_symm (x : FockIndex n → ℂ) (u u' : FockIndex m) (s : FockIndex n) :
    star (extVecE x u ((fockSplit n m).symm (s, u'))) = if u' = u then star (x s) else 0 := by
  rw [extVecE_apply_symm]
  split_ifs <;> simp

/-- `x* (Tr_E M) x = ∑_u (x ⊗ e_u)* M (x ⊗ e_u)`. -/
lemma dotProduct_ptraceE_mulVec (x : FockIndex n → ℂ) :
    star x ⬝ᵥ ptraceE M *ᵥ x = ∑ u, star (extVecE x u) ⬝ᵥ M *ᵥ extVecE x u := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  calc ∑ s, star (x s) * ∑ t, ptraceE M s t * x t
      = ∑ u, ∑ s, star (x s) * ∑ t,
          M ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t, u)) * x t := by
        simp only [ptraceE_apply, Finset.sum_mul, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun s _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ u, ∑ z, star (extVecE x u z) * ∑ w, M z w * extVecE x u w := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit fun z => star (extVecE x u z) * ∑ w, M z w * extVecE x u w]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [star_extVecE_apply_symm, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        congr 1
        rw [sum_fockSplit fun w => M ((fockSplit n m).symm (s, u)) w * extVecE x u w]
        simp only [extVecE_apply_symm, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]

/-- Lemma 3(b): the partial trace of a positive semidefinite matrix is positive semidefinite. -/
lemma ptraceE_posSemidef (hM : M.PosSemidef) : (ptraceE M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, ptraceE_conjTranspose, hM.1.eq]
  · rw [dotProduct_ptraceE_mulVec]
    exact Finset.sum_nonneg fun u _ => hM.dotProduct_mulVec_nonneg _

/-- Lemma 3(b): the partial trace of a density operator is a density operator. -/
lemma isDensity_ptraceE (hM : IsDensity M) : IsDensity (ptraceE M) :=
  ⟨ptraceE_posSemidef M hM.1, by rw [trace_ptraceE, hM.2]⟩

end ptraceE

section ptraceR

variable (M M' : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
  (X : Matrix (FockIndex n) (FockIndex n) ℂ) (Y : Matrix (FockIndex m) (FockIndex m) ℂ)

lemma ptraceR_add : ptraceR (M + M') = ptraceR M + ptraceR M' := by
  ext s t
  simp only [ptraceR_apply, Matrix.add_apply, Finset.sum_add_distrib]

lemma ptraceR_smul (c : ℂ) : ptraceR (c • M) = c • ptraceR M := by
  ext s t
  simp only [ptraceR_apply, Matrix.smul_apply, Finset.smul_sum]

/-- Lemma 3(c): the partial trace preserves the trace. -/
lemma trace_ptraceR : (ptraceR M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptraceR_apply]
  rw [sum_fockSplit' fun z => M z z]

/-- Lemma 3(c): `Tr_R (X ⊗ Y) = (Tr X) Y`. -/
lemma ptraceR_tensor : ptraceR (tensor X Y) = X.trace • Y := by
  ext s t
  simp only [ptraceR_apply, tensor_apply_symm, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Finset.sum_mul]

/-- Lemma 3(c): `Tr_R ((1 ⊗ Y) M) = Y Tr_R M`. -/
lemma ptraceR_one_tensor_mul : ptraceR (tensor 1 Y * M) = Y * ptraceR M := by
  ext s t
  simp only [ptraceR_apply, Matrix.mul_apply]
  calc ∑ u, ∑ z, tensor 1 Y ((fockSplit n m).symm (u, s)) z * M z ((fockSplit n m).symm (u, t))
      = ∑ u, ∑ s', ∑ u', (1 : Matrix (FockIndex n) (FockIndex n) ℂ) u u' * Y s s' *
          M ((fockSplit n m).symm (u', s')) ((fockSplit n m).symm (u, t)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit']
        simp only [tensor_apply_symm]
    _ = ∑ s', Y s s' * ∑ u, M ((fockSplit n m).symm (u, s')) ((fockSplit n m).symm (u, t)) := by
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, Finset.mul_sum]
        exact Finset.sum_comm

/-- Lemma 3(c): `Tr_R (M (1 ⊗ Y)) = (Tr_R M) Y`. -/
lemma ptraceR_mul_one_tensor : ptraceR (M * tensor 1 Y) = ptraceR M * Y := by
  ext s t
  simp only [ptraceR_apply, Matrix.mul_apply]
  calc ∑ u, ∑ z, M ((fockSplit n m).symm (u, s)) z * tensor 1 Y z ((fockSplit n m).symm (u, t))
      = ∑ u, ∑ t', ∑ u', M ((fockSplit n m).symm (u, s)) ((fockSplit n m).symm (u', t')) *
          ((1 : Matrix (FockIndex n) (FockIndex n) ℂ) u' u * Y t' t) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit']
        simp only [tensor_apply_symm]
    _ = ∑ t', (∑ u, M ((fockSplit n m).symm (u, s)) ((fockSplit n m).symm (u, t'))) * Y t' t := by
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
        exact Finset.sum_comm

/-- Lemma 3(c): `Tr ((Tr_R M) Y) = Tr (M (1 ⊗ Y))`. -/
lemma trace_ptraceR_mul : (ptraceR M * Y).trace = (M * tensor 1 Y).trace := by
  rw [← trace_ptraceR (M * tensor 1 Y), ptraceR_mul_one_tensor]

/-- Lemma 3(c): the partial trace commutes with the adjoint. -/
lemma ptraceR_conjTranspose : (ptraceR M).conjTranspose = ptraceR M.conjTranspose := by
  ext s t
  simp only [Matrix.conjTranspose_apply, ptraceR_apply, star_sum]

/-- The vector `e_u ⊗ y` on `n + m` modes. -/
def extVecR (y : FockIndex m → ℂ) (u : FockIndex n) : FockIndex (n + m) → ℂ :=
  fun z => if (fockSplit n m z).1 = u then y (fockSplit n m z).2 else 0

lemma extVecR_apply_symm (y : FockIndex m → ℂ) (u u' : FockIndex n) (s : FockIndex m) :
    extVecR y u ((fockSplit n m).symm (u', s)) = if u' = u then y s else 0 := by
  simp [extVecR]

lemma star_extVecR_apply_symm (y : FockIndex m → ℂ) (u u' : FockIndex n) (s : FockIndex m) :
    star (extVecR y u ((fockSplit n m).symm (u', s))) = if u' = u then star (y s) else 0 := by
  rw [extVecR_apply_symm]
  split_ifs <;> simp

/-- `y* (Tr_R M) y = ∑_u (e_u ⊗ y)* M (e_u ⊗ y)`. -/
lemma dotProduct_ptraceR_mulVec (y : FockIndex m → ℂ) :
    star y ⬝ᵥ ptraceR M *ᵥ y = ∑ u, star (extVecR y u) ⬝ᵥ M *ᵥ extVecR y u := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  calc ∑ s, star (y s) * ∑ t, ptraceR M s t * y t
      = ∑ u, ∑ s, star (y s) * ∑ t,
          M ((fockSplit n m).symm (u, s)) ((fockSplit n m).symm (u, t)) * y t := by
        simp only [ptraceR_apply, Finset.sum_mul, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun s _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ u, ∑ z, star (extVecR y u z) * ∑ w, M z w * extVecR y u w := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sum_fockSplit' fun z => star (extVecR y u z) * ∑ w, M z w * extVecR y u w]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [star_extVecR_apply_symm, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        congr 1
        rw [sum_fockSplit' fun w => M ((fockSplit n m).symm (u, s)) w * extVecR y u w]
        simp only [extVecR_apply_symm, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]

/-- Lemma 3(c): the partial trace of a positive semidefinite matrix is positive semidefinite. -/
lemma ptraceR_posSemidef (hM : M.PosSemidef) : (ptraceR M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
  · rw [Matrix.IsHermitian, ptraceR_conjTranspose, hM.1.eq]
  · rw [dotProduct_ptraceR_mulVec]
    exact Finset.sum_nonneg fun u _ => hM.dotProduct_mulVec_nonneg _

/-- Lemma 3(c): the partial trace of a density operator is a density operator. -/
lemma isDensity_ptraceR (hM : IsDensity M) : IsDensity (ptraceR M) :=
  ⟨ptraceR_posSemidef M hM.1, by rw [trace_ptraceR, hM.2]⟩

end ptraceR

/-! ### Theorem 4: marginals of a Gaussian state -/

/-- `W_G (f v₁, …, f vₘ) = W_{G'} (v₁, …, vₘ)` when `f` carries the form of `G` to that of `G'`;
the Wick expansion depends on `G` only through `v ⬝ᵥ G *ᵥ w`. -/
theorem wick_map_of_dotProduct {N : ℕ} {G : Matrix (MajoranaIndex N) (MajoranaIndex N) ℂ}
    {G' : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ}
    (f : (MajoranaIndex n → ℂ) → (MajoranaIndex N → ℂ))
    (hf : ∀ v w, f v ⬝ᵥ G *ᵥ f w = v ⬝ᵥ G' *ᵥ w) (l : List (MajoranaIndex n → ℂ)) :
    wick G (l.map f) = wick G' l := by
  suffices h : ∀ k, ∀ l : List (MajoranaIndex n → ℂ), l.length ≤ k →
      wick G (l.map f) = wick G' l from h l.length l le_rfl
  intro k
  induction k with
  | zero =>
    intro l hl
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    simp
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | v :: l =>
      rw [List.map_cons, wick_cons' _ _ (List.length_map ..), wick_cons]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.getElem_map, List.eraseIdx_map, ih (l.eraseIdx j)
        ((List.length_eraseIdx_le l j).trans (by simpa using hl)), hf]

lemma extendR_dotProduct_mulVec (G : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℂ)
    (v w : MajoranaIndex n → ℂ) :
    extendR v ⬝ᵥ G *ᵥ extendR w = v ⬝ᵥ G.submatrix embedR embedR *ᵥ w := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [sum_labelSplit fun a => extendR v a * ∑ b, G a b * extendR w b]
  simp only [extendR_embedR, extendR_embedE, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [sum_labelSplit fun b => G (embedR a) b * extendR w b]
  simp only [extendR_embedR, extendR_embedE, mul_zero, Finset.sum_const_zero, add_zero]

lemma extendE_dotProduct_mulVec (G : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℂ)
    (v w : MajoranaIndex m → ℂ) :
    extendE v ⬝ᵥ G *ᵥ extendE w = v ⬝ᵥ G.submatrix embedE embedE *ᵥ w := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [sum_labelSplit fun a => extendE v a * ∑ b, G a b * extendE w b]
  simp only [extendE_embedR, extendE_embedE, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [sum_labelSplit fun b => G (embedE a) b * extendE w b]
  simp only [extendE_embedR, extendE_embedE, mul_zero, Finset.sum_const_zero, zero_add]

lemma commutator_embedR (a b : MajoranaIndex n) :
    commutator (embedR (m := m) a) (embedR b) = tensor (commutator a b) 1 := by
  rw [commutator, commutator, majorana_embedR, majorana_embedR, tensor_mul_tensor,
    tensor_mul_tensor, Matrix.mul_one, tensor_sub_left]

lemma commutator_embedE (a b : MajoranaIndex m) :
    commutator (embedE (n := n) a) (embedE b) = tensor 1 (commutator a b) := by
  rw [commutator, commutator, majorana_embedE, majorana_embedE, tensor_mul_tensor,
    tensor_mul_tensor, parity_mul_self, tensor_sub_right]

/-- Theorem 4: the covariance of `Tr_E ρ` is the retained block `A` of the covariance of `ρ`. -/
theorem covariance_ptraceE (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    covariance (ptraceE ρ) = (covariance ρ).submatrix embedR embedR := by
  ext a b
  simp only [covariance, Matrix.submatrix_apply, commutator_embedR, ← trace_ptraceE_mul]

/-- Theorem 4: the covariance of `Tr_R ρ` is the eliminated block `D` of the covariance of `ρ`. -/
theorem covariance_ptraceR (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    covariance (ptraceR ρ) = (covariance ρ).submatrix embedE embedE := by
  ext a b
  simp only [covariance, Matrix.submatrix_apply, commutator_embedE, ← trace_ptraceR_mul]

lemma twoPoint_ptraceE (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    twoPoint (ptraceE ρ) = (twoPoint ρ).submatrix embedR embedR := by
  ext a b
  simp only [twoPoint_apply, Matrix.submatrix_apply, covariance_ptraceE, embedR_injective.eq_iff]

lemma twoPoint_ptraceR (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    twoPoint (ptraceR ρ) = (twoPoint ρ).submatrix embedE embedE := by
  ext a b
  simp only [twoPoint_apply, Matrix.submatrix_apply, covariance_ptraceR, embedE_injective.eq_iff]

/-- Theorem 4: the marginal `Tr_E ρ` of a Gaussian state is Gaussian. -/
theorem isGaussian_ptraceE {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    (hρ : IsGaussian ρ) : IsGaussian (ptraceE ρ) := by
  refine ⟨isDensity_ptraceE ρ hρ.1, fun l => ?_⟩
  rw [twoPoint_ptraceE, ← wick_map_of_dotProduct extendR (extendR_dotProduct_mulVec _), ← hρ.2,
    momentList, momentList, trace_ptraceE_mul, prod_lincomb_extendR]

/-- Theorem 4: the marginal `Tr_R ρ` of a Gaussian state is Gaussian. -/
theorem isGaussian_ptraceR {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    (hρ : IsGaussian ρ) : IsGaussian (ptraceR ρ) := by
  refine ⟨isDensity_ptraceR ρ hρ.1, fun l => ?_⟩
  rw [twoPoint_ptraceR, ← wick_map_of_dotProduct extendE (extendE_dotProduct_mulVec _),
    momentList, trace_ptraceR_mul]
  rcases Nat.even_or_odd l.length with he | ho
  · rw [← prod_lincomb_extendE_even l he, ← momentList, hρ.2]
  · obtain ⟨L, hL, hprod⟩ := exists_prod_lincomb_eq_tensor_parity_one (n := n) (m := m)
    have h1 : tensor (1 : Matrix (FockIndex n) (FockIndex n) ℂ) (l.map lincomb).prod =
        tensor parity 1 * ((l.map (extendE (n := n))).map lincomb).prod := by
      rw [prod_lincomb_extendE_odd l ho, tensor_mul_tensor, parity_mul_self, Matrix.one_mul]
    have h2 : Odd (L ++ l.map extendE).length := by
      rw [List.length_append, List.length_map]
      exact hL.add_odd ho
    rw [h1, ← hprod, ← List.prod_append, ← List.map_append, ← momentList, hρ.2, wick_odd _ h2,
      wick_odd _ (by simpa using ho)]

end Fermionic
