/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.BlockForm
import FermionicLean.Fock.Gate

/-! # Quadratic Hamiltonians

`quadHam h = (i/4) ∑ h_ab c_a c_b` for a real antisymmetric `h`. It is Hermitian, its
energy on a Hermitian `ρ` is `(1/4) ∑ h_ab Γ(ρ)_ab`, a unitary implementing `O` conjugates
it to `quadHam (Oᵀ h O)`, and in the block form it is the diagonal operator
`∑ ε_j (n_j - 1/2)`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The complex coefficient of `c_a c_b` in `H_h`. -/
noncomputable def hamCoeff (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (a b : MajoranaIndex n) : ℂ :=
  (Complex.I / 4) * (h a b : ℂ)

/-- Definition 2: the quadratic Hamiltonian `H_h = (i/4) ∑_{a,b} h_ab c_a c_b`. -/
noncomputable def quadHam (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  ∑ a, ∑ b, hamCoeff h a b • (majorana a * majorana b)

variable {h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

lemma h_apply_swap (hh : h.transpose = -h) (a b : MajoranaIndex n) : h b a = -h a b := by
  have := congrFun (congrFun hh a) b
  simpa [Matrix.transpose_apply] using this

lemma h_apply_self (hh : h.transpose = -h) (a : MajoranaIndex n) : h a a = 0 := by
  have := h_apply_swap hh a a; linarith

lemma star_hamCoeff (hh : h.transpose = -h) (a b : MajoranaIndex n) :
    star (hamCoeff h a b) = hamCoeff h b a := by
  simp only [hamCoeff, Complex.star_def, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, h_apply_swap hh a b]
  push_cast
  ring

/-- Lemma 3(a): `H_h` is Hermitian. -/
theorem quadHam_conjTranspose (hh : h.transpose = -h) :
    (quadHam h).conjTranspose = quadHam h := by
  unfold quadHam
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    majorana_conjTranspose, star_hamCoeff hh]
  exact Finset.sum_comm

theorem quadHam_isHermitian (hh : h.transpose = -h) : (quadHam h).IsHermitian :=
  quadHam_conjTranspose hh

/-- Lemma 3(b): the energy is `(1/4) ∑ h_ab Γ(ρ)_ab`, as a complex identity. -/
theorem trace_mul_quadHam (hh : h.transpose = -h) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) :
    (ρ * quadHam h).trace = ((1 / 4 * ∑ a, ∑ b, h a b * covariance ρ a b : ℝ) : ℂ) := by
  unfold quadHam
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [majorana_mul_eq, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    coe_covariance hρ a b]
  by_cases hab : a = b
  · subst hab
    simp [hamCoeff, h_apply_self hh]
  · simp only [hab, ite_false, zero_mul, zero_add, hamCoeff]
    ring

/-- Lemma 3(b): the energy is real. -/
theorem trace_mul_quadHam_re (hh : h.transpose = -h) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) :
    (ρ * quadHam h).trace = (((ρ * quadHam h).trace.re : ℝ) : ℂ) := by
  rw [trace_mul_quadHam hh hρ]; simp

/-- The energy as a real number. -/
noncomputable def energy (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) : ℝ :=
  (ρ * quadHam h).trace.re

theorem energy_eq (hh : h.transpose = -h) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) :
    energy h ρ = 1 / 4 * ∑ a, ∑ b, h a b * covariance ρ a b := by
  unfold energy
  rw [trace_mul_quadHam hh hρ, Complex.ofReal_re]

/-! ### Conjugation by a Gaussian unitary -/

/-- Bilinear reindexing of a double sum of double sums. -/
lemma sum_sum_smul_sum_sum {ι : Type*} [Fintype ι]
    (f : ι → ι → ℂ) (g : ι → ι → ι → ι → ℂ) (X : ι → ι → Matrix (FockIndex n) (FockIndex n) ℂ) :
    ∑ a, ∑ b, f a b • ∑ c, ∑ d, g a b c d • X c d =
      ∑ c, ∑ d, (∑ a, ∑ b, f a b * g a b c d) • X c d := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  -- left: ∑ a ∑ b ∑ c ∑ d ; right: ∑ c ∑ d ∑ a ∑ b
  calc ∑ a, ∑ b, ∑ c, ∑ d, (f a b * g a b c d) • X c d
      = ∑ a, ∑ c, ∑ b, ∑ d, (f a b * g a b c d) • X c d := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, (f a b * g a b c d) • X c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, (f a b * g a b c d) • X c d := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, (f a b * g a b c d) • X c d := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Lemma 3(c): a unitary implementing `O` conjugates `H_h` to `H_{Oᵀ h O}`. -/
theorem conj_quadHam {U : Matrix (FockIndex n) (FockIndex n) ℂ}
    {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) :
    U * quadHam h * U.conjTranspose = quadHam (O.transpose * h * O) := by
  have hconj : ∀ a b, U * (majorana a * majorana b) * U.conjTranspose =
      ∑ c, ∑ d, (((O a c : ℝ) : ℂ) * ((O b d : ℝ) : ℂ)) • (majorana c * majorana d) := by
    intro a b
    rw [← conj_mul_conj hU', hO a, hO b, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  unfold quadHam
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hconj]
  rw [sum_sum_smul_sum_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 1
  simp only [hamCoeff, Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ### The block form is diagonal -/

/-- `i c_{x_j} c_{y_j} = -Z_j`. -/
lemma I_smul_majorana_x_mul_y (j : Fin n) :
    Complex.I • (majorana (Sum.inl j) * majorana (Sum.inr j)) = -pauliZ j := by
  simp only [majorana, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  congr 1
  calc jwString j * pauliX j * (jwString j * pauliX j * pauliZ j)
      = jwString j * (pauliX j * jwString j) * pauliX j * pauliZ j := by
        simp only [Matrix.mul_assoc]
    _ = pauliZ j := by
        rw [pauliX_mul_jwString_of_le (le_refl j), ← Matrix.mul_assoc, jwString_mul_self,
          Matrix.one_mul, pauliX_mul_self, Matrix.one_mul]

/-- The diagonal entry `∑_j ε_j (s_j - 1/2)`. -/
noncomputable def blockEnergy (ε : Fin n → ℝ) (s : FockIndex n) : ℝ :=
  ∑ j, ε j * ((s j : ℕ) - 1 / 2)

lemma bitSign_eq (b : Fin 2) : bitSign b = 1 - 2 * ((b : ℕ) : ℂ) := by
  fin_cases b <;> norm_num [bitSign]

/-- Lemma 4: `H_{D(ε)} = diag (s ↦ ∑_j ε_j (s_j - 1/2))`. -/
theorem quadHam_blockForm (ε : Fin n → ℝ) :
    quadHam (blockForm ε) = Matrix.diagonal fun s => ((blockEnergy ε s : ℝ) : ℂ) := by
  unfold quadHam
  -- only the pairs (x_j, y_j) and (y_j, x_j) contribute
  have hcoeff : ∀ a b, hamCoeff (blockForm ε) a b • (majorana a * majorana b) =
      match a, b with
      | Sum.inl j, Sum.inr k => if j = k then
          ((Complex.I / 4) * (ε j : ℂ)) • (majorana (Sum.inl j) * majorana (Sum.inr j)) else 0
      | Sum.inr j, Sum.inl k => if j = k then
          ((Complex.I / 4) * (ε j : ℂ)) • (majorana (Sum.inl j) * majorana (Sum.inr j)) else 0
      | _, _ => 0 := by
    rintro (j | j) (k | k)
    · simp [hamCoeff, blockForm, Matrix.fromBlocks]
    · by_cases hjk : j = k
      · subst hjk; simp [hamCoeff, blockForm, Matrix.fromBlocks]
      · simp [hamCoeff, blockForm, Matrix.fromBlocks, hjk]
    · by_cases hjk : j = k
      · subst hjk
        simp only [hamCoeff, blockForm, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
          Matrix.diagonal_apply_eq, ite_true]
        rw [majorana_mul_comm_of_ne Sum.inr_ne_inl]
        push_cast
        simp only [smul_neg, ← neg_smul]
        congr 1; ring
      · simp [hamCoeff, blockForm, Matrix.fromBlocks, hjk]
    · simp [hamCoeff, blockForm, Matrix.fromBlocks]
  simp only [hcoeff, Fintype.sum_sum_type, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const_zero, add_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ j, ((Complex.I / 4) * (ε j : ℂ)) • (majorana (Sum.inl j) * majorana (Sum.inr j)) +
      ((Complex.I / 4) * (ε j : ℂ)) • (majorana (Sum.inl j) * majorana (Sum.inr j)) =
      Matrix.diagonal fun s => ((ε j * ((s j : ℕ) - 1 / 2) : ℝ) : ℂ) := by
    intro j
    rw [← two_smul ℂ, smul_smul, show (2 : ℂ) * ((Complex.I / 4) * (ε j : ℂ)) =
      ((ε j : ℂ) / 2) * Complex.I by ring, ← smul_smul, I_smul_majorana_x_mul_y, pauliZ]
    ext s t
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [bitSign_eq]; push_cast; ring
    · simp
  simp only [hterm]
  ext s t
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, blockEnergy]
  split_ifs <;> push_cast <;> simp

end Fermionic
