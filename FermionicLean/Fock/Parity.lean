/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Majorana

/-! # The parity operator

`P = Z_1 ⋯ Z_n` is the diagonal sign matrix `s ↦ ∏_j (-1)^{s_j}`. It squares to one and
anticommutes with every Majorana operator: `P c_a P = -c_a` (G2, Lemma 6). Consequently
the trace of a product of an odd number of Majorana operators against any matrix
commuting with `P` vanishes.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The parity sign of a configuration, `∏_j (-1)^{s_j}`. -/
def paritySign (s : FockIndex n) : ℂ := ∏ j, bitSign (s j)

/-- The parity operator `P = Z_1 ⋯ Z_n`. -/
def parity : Matrix (FockIndex n) (FockIndex n) ℂ := Matrix.diagonal paritySign

lemma paritySign_mul_self (s : FockIndex n) : paritySign s * paritySign s = 1 := by
  rw [paritySign, ← Finset.prod_mul_distrib]
  simp [bitSign_mul_self]

lemma paritySign_flip (j : Fin n) (s : FockIndex n) : paritySign (flip j s) = -paritySign s := by
  rw [paritySign, paritySign, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => bitSign (s k)) (Finset.mem_univ j),
    bitSign_flip_self, neg_mul]
  congr 2
  exact Finset.prod_congr rfl fun k hk => bitSign_flip_ne (Finset.ne_of_mem_erase hk) s

lemma parity_mul_self : (parity : Matrix (FockIndex n) (FockIndex n) ℂ) * parity = 1 := by
  simp [parity, Matrix.diagonal_mul_diagonal, paritySign_mul_self]

lemma parity_conjTranspose :
    (parity : Matrix (FockIndex n) (FockIndex n) ℂ).conjTranspose = parity := by
  rw [parity, Matrix.diagonal_conjTranspose]
  congr 1
  funext s
  simp [paritySign, star_bitSign]

/-- Lemma 6: `P c_a P = -c_a`. -/
theorem parity_mul_majorana_mul_parity (a : MajoranaIndex n) :
    parity * majorana a * parity = -majorana a := by
  rw [majorana_eq_diagonal_mul, parity]
  simp only [Matrix.mul_assoc]
  rw [pauliX_mul_diagonal]
  simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.neg_mul]
  congr 1
  ext s t
  simp only [Matrix.diagonal_apply, Matrix.neg_apply, paritySign_flip]
  split_ifs
  · linear_combination (-(majoranaSign a s)) * paritySign_mul_self s
  · simp

/-- `P c_a = -c_a P`. -/
theorem parity_mul_majorana (a : MajoranaIndex n) :
    parity * majorana a = -(majorana a * parity) := by
  have h := parity_mul_majorana_mul_parity a
  calc parity * majorana a = parity * majorana a * (parity * parity) := by
        rw [parity_mul_self, Matrix.mul_one]
    _ = -(majorana a * parity) := by rw [← Matrix.mul_assoc, h, Matrix.neg_mul]

/-- `P X_1 ⋯ X_k P = (-1)^k X_1 ⋯ X_k` when every factor satisfies `P X P = -X`. -/
theorem parity_mul_list_prod_mul_parity (l : List (Matrix (FockIndex n) (FockIndex n) ℂ))
    (hl : ∀ X ∈ l, parity * X * parity = -X) :
    parity * l.prod * parity = (-1) ^ l.length • l.prod := by
  induction l with
  | nil => simp [parity_mul_self]
  | cons X l ih =>
    have hX := hl X (List.mem_cons_self ..)
    have ih' := ih fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    calc parity * (X :: l).prod * parity
        = (parity * X * parity) * (parity * l.prod * parity) := by
          simp only [List.prod_cons, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc parity parity, parity_mul_self, Matrix.one_mul]
      _ = (-1) ^ (X :: l).length • (X :: l).prod := by
          rw [hX, ih', List.length_cons, List.prod_cons, pow_succ, Matrix.neg_mul,
            Matrix.mul_smul, ← Matrix.smul_mul, mul_comm, mul_smul, neg_one_smul, Matrix.smul_mul]

/-- Odd products of Majorana operators are traceless against any matrix commuting with `P`. -/
theorem trace_mul_list_prod_eq_zero_of_odd (ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (hρ : parity * ρ = ρ * parity) (l : List (Matrix (FockIndex n) (FockIndex n) ℂ))
    (hl : ∀ X ∈ l, parity * X * parity = -X) (hodd : Odd l.length) :
    (ρ * l.prod).trace = 0 := by
  have h2 : ρ * (parity * l.prod * parity) = parity * (ρ * l.prod) * parity := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hρ]
    simp only [Matrix.mul_assoc]
  have h1 : (ρ * l.prod).trace = (ρ * (parity * l.prod * parity)).trace := by
    rw [h2, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, parity_mul_self, Matrix.one_mul]
  rw [parity_mul_list_prod_mul_parity l hl, hodd.neg_one_pow, neg_one_smul, Matrix.mul_neg,
    Matrix.trace_neg] at h1
  linear_combination h1 / 2

end Fermionic
