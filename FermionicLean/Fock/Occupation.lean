/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Covariance
import FermionicLean.Gaussian.Examples

/-! # Occupation-number states

The state `|s⟩⟨s|` of a configuration `s` is a density operator whose covariance is
`fromBlocks 0 D (-D) 0` with `D = diag (-(-1)^{s_j})`. The vacuum has covariance
`-standardCovariance n`, and every occupation covariance is pure.
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The occupation-number state `|s⟩⟨s|`. -/
def occupation (s : FockIndex n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  Matrix.single s s 1

/-- The real sign `-(-1)^b`: `-1` for an empty mode, `+1` for an occupied one. -/
def occupationSignEntry (b : Fin 2) : ℝ := if b = 0 then -1 else 1

/-- The diagonal block of the occupation covariance. -/
def occupationSign (s : FockIndex n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun j => occupationSignEntry (s j)

lemma occupation_conjTranspose (s : FockIndex n) :
    (occupation s).conjTranspose = occupation s := by
  ext i j
  simp [occupation, Matrix.single, Matrix.conjTranspose_apply, and_comm]

lemma occupation_dotProduct (s : FockIndex n) (x : FockIndex n → ℂ) :
    star x ⬝ᵥ (occupation s *ᵥ x) = star (x s) * x s := by
  rw [occupation, Matrix.single_mulVec, dotProduct]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [Function.update_of_ne ht]
  · simp

/-- Theorem 6: `|s⟩⟨s|` is a density operator. -/
theorem isDensity_occupation (s : FockIndex n) : IsDensity (occupation s) := by
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (occupation_conjTranspose s)
    fun x => ?_, ?_⟩
  · rw [occupation_dotProduct, Complex.nonneg_iff]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    constructor
    · nlinarith [mul_self_nonneg (x s).re, mul_self_nonneg (x s).im]
    · ring
  · simp [occupation, Matrix.trace_single_eq_same]

lemma trace_occupation_mul (s : FockIndex n) (M : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (occupation s * M).trace = M s s := by
  rw [occupation, Matrix.trace_single_mul, one_smul]

/-- The diagonal entry of `X_j X_k`: `1` if `j = k`, else `0`. -/
lemma pauliX_mul_pauliX_apply_self (j k : Fin n) (s : FockIndex n) :
    (pauliX j * pauliX k) s s = if j = k then 1 else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp [pauliX_mul_self]
  · simp only [pauliX, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.trans_apply, flipPerm_apply,
      hjk, ↓reduceIte]
    split_ifs with h
    · exfalso
      have := congrFun h j
      rw [flip_apply_ne hjk, flip_apply_self] at this
      revert this
      generalize s j = b
      fin_cases b <;> decide
    · rfl

/-- The product `c_a c_b` has diagonal entry `f_a(s) f_b(flip s) [mode a = mode b]`. -/
lemma majorana_mul_apply_self (a b : MajoranaIndex n) (s : FockIndex n) :
    (majorana a * majorana b) s s =
      majoranaSign a s * majoranaSign b (flip (mode a) s) *
        (if mode a = mode b then 1 else 0) := by
  rw [majorana_eq_diagonal_mul a, majorana_eq_diagonal_mul b,
    diagonal_mul_pauliX_mul_diagonal_mul_pauliX, Matrix.diagonal_mul, pauliX_mul_pauliX_apply_self]

lemma occupationSignEntry_eq (b : Fin 2) :
    ((occupationSignEntry b : ℝ) : ℂ) = -bitSign b := by
  fin_cases b <;> simp [occupationSignEntry, bitSign]

/-- Theorem 6: the covariance of an occupation state. -/
theorem covariance_occupation (s : FockIndex n) :
    covariance (occupation s) =
      Matrix.fromBlocks 0 (occupationSign s) (-(occupationSign s)) 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [covariance_diag]
    rcases a with j | j <;> simp [Matrix.fromBlocks]
  · rw [covariance_of_ne _ hab, trace_occupation_mul, majorana_mul_apply_self]
    rcases a with j | j <;> rcases b with k | k <;>
      simp only [mode, Sum.elim_inl, Sum.elim_inr, id, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Matrix.neg_apply, occupationSign, Matrix.diagonal_apply]
    · have hjk : j ≠ k := fun h => hab (by rw [h])
      simp [hjk]
    · by_cases hjk : j = k
      · subst hjk
        simp only [majoranaSign, stringSign_flip, bitSign_flip_self, lt_self_iff_false,
          ↓reduceIte, one_mul, mul_one]
        have h1 := stringSign_mul_self j s
        have hb : ((occupationSignEntry (s j) : ℝ) : ℂ) = -bitSign (s j) := occupationSignEntry_eq _
        have : Complex.I * (stringSign j s * (-Complex.I * stringSign j s * -bitSign (s j))) =
            ((occupationSignEntry (s j) : ℝ) : ℂ) := by
          rw [hb]
          linear_combination (Complex.I * Complex.I * bitSign (s j)) * h1 +
            bitSign (s j) * Complex.I_sq
        rw [this, Complex.ofReal_re]
      · simp [hjk]
    · by_cases hjk : j = k
      · subst hjk
        simp only [majoranaSign, stringSign_flip, lt_self_iff_false, ↓reduceIte, one_mul,
          mul_one]
        have h1 := stringSign_mul_self j s
        have hb : ((occupationSignEntry (s j) : ℝ) : ℂ) = -bitSign (s j) := occupationSignEntry_eq _
        have : Complex.I * (-Complex.I * stringSign j s * bitSign (s j) * stringSign j s) =
            -((occupationSignEntry (s j) : ℝ) : ℂ) := by
          rw [hb, neg_neg]
          linear_combination (-(Complex.I * Complex.I * bitSign (s j))) * h1 +
            (-(bitSign (s j))) * Complex.I_sq
        rw [this]
        simp
      · simp [hjk]
    · have hjk : j ≠ k := fun h => hab (by rw [h])
      simp [hjk]

/-- Corollary 7: the vacuum covariance is `-Ω_n`. -/
theorem covariance_vacuum :
    covariance (occupation (fun _ : Fin n => 0)) = -(standardCovariance n) := by
  rw [covariance_occupation, standardCovariance, Matrix.fromBlocks_neg]
  have hD : occupationSign (fun _ : Fin n => (0 : Fin 2)) = -1 := by
    ext i j
    simp [occupationSign, occupationSignEntry, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hD]
  simp

/-- Corollary 7: every occupation covariance is pure. -/
theorem isPure_covariance_occupation (s : FockIndex n) :
    IsPure (covariance (occupation s)) := by
  rw [covariance_occupation]
  have hDsq : occupationSign s * occupationSign s = 1 := by
    ext i j
    simp only [occupationSign, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
      Matrix.one_apply]
    split_ifs with h
    · subst h
      unfold occupationSignEntry
      split_ifs <;> norm_num
    · rfl
  have hDt : (occupationSign s).transpose = occupationSign s := by
    simp [occupationSign, Matrix.diagonal_transpose]
  refine ⟨?_, ?_⟩
  · rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.transpose_neg, hDt]
    simp
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, hDsq, zero_add,
      add_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp

end Fermionic
