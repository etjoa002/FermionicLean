/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Majorana
import FermionicLean.Gaussian.Admissible
import Mathlib.Basic.Complex.BigOperators

/-! # Covariance of a density operator

`covariance ρ a b = Re ((i/2) Tr (ρ [c_a, c_b]))`. For Hermitian `ρ` it is real and
antisymmetric; for a density operator it is admissible, because
`Tr (ρ A* A) = z* (1 + iΓ) z ≥ 0` for `A = ∑ conj (z_a) c_a`.
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

variable {n : ℕ}

/-- Definition 3: a density operator is positive semidefinite with unit trace. -/
def IsDensity (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The commutator `[c_a, c_b]`. -/
def commutator (a b : MajoranaIndex n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  majorana a * majorana b - majorana b * majorana a

/-- Definition 3: the Majorana covariance of `ρ`. -/
noncomputable def covariance (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  fun a b => ((Complex.I / 2) * (ρ * commutator a b).trace).re

lemma commutator_swap (a b : MajoranaIndex n) : commutator b a = -commutator a b := by
  simp [commutator]

lemma commutator_self (a : MajoranaIndex n) : commutator a a = 0 := by
  simp [commutator]

lemma commutator_conjTranspose (a b : MajoranaIndex n) :
    (commutator a b).conjTranspose = -commutator a b := by
  simp [commutator, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, majorana_conjTranspose]

/-- For `a ≠ b` the commutator is twice the product. -/
lemma commutator_of_ne {a b : MajoranaIndex n} (h : a ≠ b) :
    commutator a b = (2 : ℂ) • (majorana a * majorana b) := by
  have hac := majorana_anticommute a b
  simp only [h, ↓reduceIte, zero_smul] at hac
  have : majorana b * majorana a = -(majorana a * majorana b) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hac
  rw [commutator, this, sub_neg_eq_add, two_smul]

/-- Theorem 4: the trace `Tr (ρ [c_a, c_b])` is purely imaginary for Hermitian `ρ`. -/
lemma star_trace_mul_commutator {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) (a b : MajoranaIndex n) :
    star (ρ * commutator a b).trace = -(ρ * commutator a b).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, commutator_conjTranspose,
    hρ.eq, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]

/-- Theorem 4: the imaginary part of `(i/2) Tr (ρ [c_a, c_b])` vanishes. -/
theorem covariance_im_eq_zero {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) (a b : MajoranaIndex n) :
    ((Complex.I / 2) * (ρ * commutator a b).trace).im = 0 := by
  have h := star_trace_mul_commutator hρ a b
  rw [Complex.star_def, Complex.ext_iff] at h
  simp only [Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im] at h
  have hre : (ρ * commutator a b).trace.re = 0 := by linarith [h.1]
  simp [Complex.mul_im, hre]

/-- The covariance entry as a complex number. -/
lemma coe_covariance {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : ρ.IsHermitian) (a b : MajoranaIndex n) :
    ((covariance ρ a b : ℝ) : ℂ) = (Complex.I / 2) * (ρ * commutator a b).trace := by
  apply Complex.ext
  · simp [covariance]
  · simp [covariance_im_eq_zero hρ a b]

/-- Theorem 4: the covariance is antisymmetric. -/
theorem covariance_transpose (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (covariance ρ).transpose = -covariance ρ := by
  ext a b
  simp [covariance, commutator_swap a b, Matrix.trace_neg]

/-- Theorem 4: the diagonal entries vanish. -/
theorem covariance_diag (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) (a : MajoranaIndex n) :
    covariance ρ a a = 0 := by
  simp [covariance, commutator_self]

/-- Theorem 4: off-diagonal entries are `Re (i Tr (ρ c_a c_b))`. -/
theorem covariance_of_ne (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) {a b : MajoranaIndex n}
    (h : a ≠ b) :
    covariance ρ a b = (Complex.I * (ρ * (majorana a * majorana b)).trace).re := by
  simp only [covariance, commutator_of_ne h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  ring

/-! ### Admissibility -/

/-- The operator `A = ∑ conj (z_a) c_a`. -/
def annihilator (z : MajoranaIndex n → ℂ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  ∑ a, star (z a) • majorana a

lemma annihilator_conjTranspose (z : MajoranaIndex n → ℂ) :
    (annihilator z).conjTranspose = ∑ a, z a • majorana a := by
  simp [annihilator, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, majorana_conjTranspose]

/-- `c_a c_b = δ_ab 1 + (1/2)[c_a, c_b]`. -/
lemma majorana_mul_eq (a b : MajoranaIndex n) :
    majorana a * majorana b =
      (if a = b then (1 : ℂ) else 0) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) +
        (1 / 2 : ℂ) • commutator a b := by
  have h := majorana_anticommute a b
  have h2 : (2 : ℂ) • (majorana a * majorana b) =
      (majorana a * majorana b + majorana b * majorana a) + commutator a b := by
    rw [commutator, two_smul]; abel
  have : majorana a * majorana b = (1 / 2 : ℂ) • ((2 : ℂ) • (majorana a * majorana b)) := by
    rw [smul_smul]; norm_num
  rw [this, h2, h, smul_add, smul_smul]
  congr 2
  split_ifs <;> norm_num

lemma conjTranspose_mul_annihilator (z : MajoranaIndex n → ℂ) :
    (annihilator z).conjTranspose * annihilator z =
      (star z ⬝ᵥ z) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) +
        ∑ a, ∑ b, (z a * star (z b) * (1 / 2)) • commutator a b := by
  rw [annihilator_conjTranspose, annihilator, Finset.sum_mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, majorana_mul_eq, smul_add,
    Finset.sum_add_distrib]
  congr 1
  · rw [dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring

/-- `Tr (ρ A* A) = z* (1 + iΓ) z` for a density operator. -/
lemma trace_mul_conjTranspose_mul_annihilator {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) (z : MajoranaIndex n → ℂ) :
    (ρ * ((annihilator z).conjTranspose * annihilator z)).trace =
      star z ⬝ᵥ ((1 + Complex.I • (covariance ρ).map Complex.ofReal) *ᵥ z) := by
  have hH : ρ.IsHermitian := hρ.1.isHermitian
  rw [conjTranspose_mul_annihilator, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, hρ.2, smul_eq_mul, mul_one, Matrix.mul_sum,
    Matrix.trace_sum]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hΓ : ∀ a b, z a * star (z b) * (1 / 2) * (ρ * commutator a b).trace =
      -Complex.I * (z a * star (z b)) * ((covariance ρ a b : ℝ) : ℂ) := by
    intro a b
    rw [coe_covariance hH]
    linear_combination (z a * star (z b) * (ρ * commutator a b).trace / 2) * Complex.I_sq
  simp only [hΓ]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  congr 1
  have hanti : ∀ a b, ((covariance ρ a b : ℝ) : ℂ) = -((covariance ρ b a : ℝ) : ℂ) := by
    intro a b
    have := congrFun (congrFun (covariance_transpose ρ) b) a
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    rw [this]; push_cast; ring
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hanti a b]
  ring

/-- Theorem 5: the covariance of a density operator is admissible. -/
theorem IsDensity.isAdmissible_covariance {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) : IsAdmissible (covariance ρ) := by
  have hanti := covariance_transpose ρ
  rw [isAdmissible_iff_hermitian hanti]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · have hmap : ((covariance ρ).map Complex.ofReal).conjTranspose =
        (covariance ρ).transpose.map Complex.ofReal := by
      ext i j; simp
    have hneg : (-(covariance ρ)).map Complex.ofReal = -((covariance ρ).map Complex.ofReal) := by
      ext i j; simp
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hmap,
      hanti, Complex.star_def, Complex.conj_I, hneg, smul_neg, neg_smul, neg_neg]
  · rw [← trace_mul_conjTranspose_mul_annihilator hρ z, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle]
    have hP := hρ.1.mul_mul_conjTranspose_same (annihilator z)
    have hd : ∀ s, 0 ≤ (annihilator z * ρ * (annihilator z).conjTranspose) s s :=
      fun s => hP.diag_nonneg
    rw [Complex.nonneg_iff, Matrix.trace, Complex.re_sum, Complex.im_sum]
    exact ⟨Finset.sum_nonneg fun s _ => (Complex.nonneg_iff.mp (hd s)).1,
      (Finset.sum_eq_zero fun s _ => (Complex.nonneg_iff.mp (hd s)).2.symm).symm⟩

end Fermionic
