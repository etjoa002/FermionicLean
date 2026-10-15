/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Pauli
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Canonical anticommutation relations

Every Majorana operator is a signed flip `diagonal f_a * X_{mode a}`. The
anticommutator of two of them is `diagonal g * X_j X_k` with an explicit scalar
`g`, and the CAR reduce to the identity `g = 2 δ_ab` on the sign functions.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The mode of a Majorana label. -/
def mode : MajoranaIndex n → Fin n := Sum.elim id id

/-- Entry of the Jordan–Wigner string. -/
def stringSign (j : Fin n) (s : FockIndex n) : ℂ :=
  ∏ k : Fin n, if k < j then bitSign (s k) else 1

/-- The sign function of a Majorana operator as a signed flip. -/
def majoranaSign : MajoranaIndex n → FockIndex n → ℂ
  | Sum.inl j, s => stringSign j s
  | Sum.inr j, s => -Complex.I * stringSign j s * bitSign (s j)

lemma jwString_eq_diagonal (j : Fin n) : jwString j = Matrix.diagonal (stringSign j) := rfl

lemma stringSign_flip (j k : Fin n) (s : FockIndex n) :
    stringSign k (flip j s) = (if j < k then -1 else 1) * stringSign k s :=
  jwString_entry_flip j k s

lemma stringSign_mul_self (j : Fin n) (s : FockIndex n) :
    stringSign j s * stringSign j s = 1 :=
  jwString_entry_mul_self j s

lemma star_stringSign (j : Fin n) (s : FockIndex n) : star (stringSign j s) = stringSign j s := by
  unfold stringSign
  rw [star_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp [star_bitSign]

/-- Every Majorana operator is a signed flip. -/
lemma majorana_eq_diagonal_mul (a : MajoranaIndex n) :
    majorana a = Matrix.diagonal (majoranaSign a) * pauliX (mode a) := by
  rcases a with j | j
  · rfl
  · simp only [majorana, mode, Sum.elim_inr, id]
    rw [Matrix.mul_assoc, pauliZ, pauliX_mul_diagonal, ← Matrix.mul_assoc,
      jwString_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.smul_mul]
    congr 1
    ext s t
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, majoranaSign, flip_apply_self,
      bitSign_add_one, smul_eq_mul]
    split_ifs <;> ring

/-- Product of two signed flips. -/
lemma diagonal_mul_pauliX_mul_diagonal_mul_pauliX (f g : FockIndex n → ℂ) (j k : Fin n) :
    Matrix.diagonal f * pauliX j * (Matrix.diagonal g * pauliX k) =
      Matrix.diagonal (fun s => f s * g (flip j s)) * (pauliX j * pauliX k) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pauliX j), pauliX_mul_diagonal,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]

lemma bitSign_flip_self (j : Fin n) (s : FockIndex n) : bitSign (flip j s j) = -bitSign (s j) := by
  rw [flip_apply_self, bitSign_add_one]

lemma bitSign_flip_ne {j k : Fin n} (h : k ≠ j) (s : FockIndex n) :
    bitSign (flip j s k) = bitSign (s k) := by
  rw [flip_apply_ne h]

lemma ite_lt_add_ite_lt {j k : Fin n} (h : j ≠ k) :
    ((if j < k then (-1 : ℂ) else 1) + (if k < j then -1 else 1)) = 0 := by
  rcases lt_or_gt_of_ne h with hjk | hkj
  · simp [hjk, not_lt.mpr hjk.le]
  · simp [hkj, not_lt.mpr hkj.le]

/-- The scalar identity behind the CAR. -/
lemma majoranaSign_anticomm (a b : MajoranaIndex n) (s : FockIndex n) :
    majoranaSign a s * majoranaSign b (flip (mode a) s) +
      majoranaSign b s * majoranaSign a (flip (mode b) s) =
      if a = b then 2 else 0 := by
  rcases a with j | j <;> rcases b with k | k
  · by_cases hjk : j = k
    · subst hjk
      simp only [majoranaSign, mode, Sum.elim_inl, id, stringSign_flip, lt_self_iff_false,
        ↓reduceIte, one_mul]
      linear_combination 2 * stringSign_mul_self j s
    · simp only [majoranaSign, mode, Sum.elim_inl, id, stringSign_flip, hjk, ↓reduceIte,
        Sum.inl.injEq]
      linear_combination (stringSign j s * stringSign k s) * ite_lt_add_ite_lt hjk
  · by_cases hjk : j = k
    · subst hjk
      simp only [majoranaSign, mode, Sum.elim_inl, Sum.elim_inr, id, stringSign_flip,
        bitSign_flip_self, lt_self_iff_false, ↓reduceIte, one_mul, reduceCtorEq]
      ring
    · simp only [majoranaSign, mode, Sum.elim_inl, Sum.elim_inr, id, stringSign_flip,
        bitSign_flip_ne (Ne.symm hjk), ↓reduceIte, reduceCtorEq]
      linear_combination (-Complex.I * stringSign j s * stringSign k s * bitSign (s k)) *
        ite_lt_add_ite_lt hjk
  · by_cases hjk : j = k
    · subst hjk
      simp only [majoranaSign, mode, Sum.elim_inl, Sum.elim_inr, id, stringSign_flip,
        bitSign_flip_self, lt_self_iff_false, ↓reduceIte, one_mul, reduceCtorEq]
      ring
    · simp only [majoranaSign, mode, Sum.elim_inl, Sum.elim_inr, id, stringSign_flip,
        bitSign_flip_ne hjk, ↓reduceIte, reduceCtorEq]
      linear_combination (-Complex.I * stringSign j s * stringSign k s * bitSign (s j)) *
        ite_lt_add_ite_lt hjk
  · by_cases hjk : j = k
    · subst hjk
      simp only [majoranaSign, mode, Sum.elim_inr, id, stringSign_flip, bitSign_flip_self,
        lt_self_iff_false, ↓reduceIte, one_mul]
      have h1 := stringSign_mul_self j s
      have h2 := bitSign_mul_self (s j)
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (-2 * Complex.I * Complex.I * (bitSign (s j) * bitSign (s j))) * h1 +
        (-2 * Complex.I * Complex.I) * h2 + (-2) * hI
    · simp only [majoranaSign, mode, Sum.elim_inr, id, stringSign_flip,
        bitSign_flip_ne (Ne.symm hjk), bitSign_flip_ne hjk, hjk, ↓reduceIte, Sum.inr.injEq]
      linear_combination (Complex.I * Complex.I * stringSign j s * stringSign k s *
        bitSign (s j) * bitSign (s k)) * ite_lt_add_ite_lt hjk

/-- Theorem 3: canonical anticommutation relations. -/
theorem majorana_anticommute (a b : MajoranaIndex n) :
    majorana a * majorana b + majorana b * majorana a =
      (if a = b then (2 : ℂ) else 0) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) := by
  rw [majorana_eq_diagonal_mul a, majorana_eq_diagonal_mul b,
    diagonal_mul_pauliX_mul_diagonal_mul_pauliX, diagonal_mul_pauliX_mul_diagonal_mul_pauliX,
    pauliX_mul_pauliX_comm (mode b) (mode a), ← Matrix.add_mul, Matrix.diagonal_add]
  simp only [majoranaSign_anticomm]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    rw [pauliX_mul_self, Matrix.mul_one, Matrix.smul_one_eq_diagonal]
  · simp [hab]

/-- Theorem 3: Majorana operators are Hermitian. -/
theorem majorana_conjTranspose (a : MajoranaIndex n) :
    (majorana a).conjTranspose = majorana a := by
  rw [majorana_eq_diagonal_mul, Matrix.conjTranspose_mul, pauliX_conjTranspose,
    Matrix.diagonal_conjTranspose, pauliX_mul_diagonal]
  congr 2
  funext s
  rcases a with j | j
  · simp only [mode, Sum.elim_inl, id, majoranaSign, Pi.star_apply, star_stringSign,
      stringSign_flip, lt_self_iff_false, ↓reduceIte, one_mul]
  · simp only [mode, Sum.elim_inr, id, majoranaSign, Pi.star_apply, star_mul', star_neg,
      Complex.star_def, Complex.conj_I, star_stringSign, star_bitSign, stringSign_flip,
      bitSign_flip_self, lt_self_iff_false, ↓reduceIte, one_mul]
    ring

end Fermionic
