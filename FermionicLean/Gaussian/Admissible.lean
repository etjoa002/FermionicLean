/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Defs
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-! # Equivalent forms of Majorana admissibility

The real condition `1 - Γᵀ Γ ⪰ 0` is equivalent to the norm bound `‖Γ v‖ ≤ ‖v‖`
and to positive semidefiniteness of the complex Hermitian matrix `1 + i Γ`.
Pure covariances are admissible isometries.
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

variable {n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- Quadratic form of `1 - Γᵀ Γ` as a difference of squared norms. -/
lemma dotProduct_one_sub_transpose_mul_mulVec
    (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (v : MajoranaIndex n → ℝ) :
    v ⬝ᵥ ((1 - Γ.transpose * Γ) *ᵥ v) = v ⬝ᵥ v - (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma transpose_one_sub_transpose_mul (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    (1 - Γ.transpose * Γ).transpose = 1 - Γ.transpose * Γ := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- Theorem 1 (norm form). -/
theorem isAdmissible_iff_norm (hΓ : Γ.transpose = -Γ) :
    IsAdmissible Γ ↔ ∀ v : MajoranaIndex n → ℝ, (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) ≤ v ⬝ᵥ v := by
  unfold IsAdmissible
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.isHermitian_iff_isSymm]
  constructor
  · rintro ⟨-, -, h⟩ v
    have := h v
    rw [star_trivial, dotProduct_one_sub_transpose_mul_mulVec] at this
    linarith
  · intro h
    refine ⟨hΓ, transpose_one_sub_transpose_mul Γ, fun v => ?_⟩
    rw [star_trivial, dotProduct_one_sub_transpose_mul_mulVec]
    linarith [h v]

/-- Theorem 3 (purity): a pure covariance satisfies `Γᵀ Γ = 1`. -/
theorem IsPure.transpose_mul_self (h : IsPure Γ) : Γ.transpose * Γ = 1 := by
  rw [h.1, Matrix.neg_mul, h.2, neg_neg]

/-- Theorem 3 (purity): a pure covariance is an isometry. -/
theorem IsPure.dotProduct_mulVec (h : IsPure Γ) (v : MajoranaIndex n → ℝ) :
    (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) = v ⬝ᵥ v := by
  have := dotProduct_one_sub_transpose_mul_mulVec Γ v
  rw [h.transpose_mul_self, sub_self, Matrix.zero_mulVec, dotProduct_zero] at this
  linarith

/-- Theorem 3 (purity): every pure covariance is admissible. -/
theorem IsPure.isAdmissible (h : IsPure Γ) : IsAdmissible Γ :=
  (isAdmissible_iff_norm h.1).mpr fun v => (h.dotProduct_mulVec v).le

/-! ### Complexification bridge -/

/-- Entrywise inclusion of a real vector into `ℂ`. -/
def ofRealVec {ι : Type*} (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

lemma star_ofRealVec {ι : Type*} (x : ι → ℝ) : star (ofRealVec x) = ofRealVec x := by
  funext i; simp [ofRealVec]

lemma ofRealVec_dotProduct {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    ofRealVec x ⬝ᵥ ofRealVec y = ((x ⬝ᵥ y : ℝ) : ℂ) := by
  exact (RingHom.map_dotProduct Complex.ofRealHom x y).symm

lemma map_ofReal_mulVec_ofRealVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    A.map Complex.ofReal *ᵥ ofRealVec x = ofRealVec (A *ᵥ x) := by
  funext i
  change (A.map (⇑Complex.ofRealHom) *ᵥ (Complex.ofRealHom ∘ x)) i = _
  exact (RingHom.map_mulVec Complex.ofRealHom A x i).symm

lemma eq_ofRealVec_re_add_smul_im {ι : Type*} (z : ι → ℂ) :
    z = ofRealVec (fun i => (z i).re) + Complex.I • ofRealVec (fun i => (z i).im) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, ofRealVec, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (z i)).symm

/-- Quadratic form of a real antisymmetric matrix vanishes on real vectors. -/
lemma dotProduct_mulVec_self_eq_zero (hΓ : Γ.transpose = -Γ) (a : MajoranaIndex n → ℝ) :
    a ⬝ᵥ (Γ *ᵥ a) = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec Γ a a
  rw [hΓ, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- Antisymmetry exchanges the two arguments of the bilinear form up to sign. -/
lemma dotProduct_mulVec_comm_neg (hΓ : Γ.transpose = -Γ) (a b : MajoranaIndex n → ℝ) :
    a ⬝ᵥ (Γ *ᵥ b) = -(b ⬝ᵥ (Γ *ᵥ a)) := by
  have h := Matrix.dotProduct_transpose_mulVec Γ b a
  rw [hΓ, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- The Hermitian form of `1 + iΓ` at `z = a + i b`, in terms of real data. -/
lemma hermitianForm_eq (hΓ : Γ.transpose = -Γ) (a b : MajoranaIndex n → ℝ) :
    star (ofRealVec a + Complex.I • ofRealVec b) ⬝ᵥ
        ((1 + Complex.I • Γ.map Complex.ofReal) *ᵥ
          (ofRealVec a + Complex.I • ofRealVec b)) =
      ((a ⬝ᵥ a + b ⬝ᵥ b + 2 * (b ⬝ᵥ (Γ *ᵥ a)) : ℝ) : ℂ) := by
  simp only [star_add, star_smul, star_ofRealVec, Complex.star_def, Complex.conj_I,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, map_ofReal_mulVec_ofRealVec, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, ofRealVec_dotProduct, smul_eq_mul,
    dotProduct_mulVec_self_eq_zero hΓ, dotProduct_mulVec_comm_neg hΓ a b]
  rw [dotProduct_comm b a]
  push_cast
  apply Complex.ext
  · simp; ring
  · simp

/-- Theorem 2 (Hermitian form). -/
theorem isAdmissible_iff_hermitian (hΓ : Γ.transpose = -Γ) :
    IsAdmissible Γ ↔ (1 + Complex.I • Γ.map Complex.ofReal).PosSemidef := by
  rw [isAdmissible_iff_norm hΓ, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨?_, fun z => ?_⟩
    · have hmap : (Γ.map Complex.ofReal).conjTranspose = Γ.transpose.map Complex.ofReal := by
        ext i j; simp
      have hneg : (-Γ).map Complex.ofReal = -(Γ.map Complex.ofReal) := by
        ext i j; simp
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
        hmap, hΓ, Complex.star_def, Complex.conj_I, hneg, smul_neg, neg_smul, neg_neg]
    · rw [eq_ofRealVec_re_add_smul_im z, hermitianForm_eq hΓ]
      set a : MajoranaIndex n → ℝ := fun i => (z i).re
      set b : MajoranaIndex n → ℝ := fun i => (z i).im
      have h1 : 0 ≤ (b + Γ *ᵥ a) ⬝ᵥ (b + Γ *ᵥ a) :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg ((b + Γ *ᵥ a) i)
      have h2 := h a
      have h3 : (b + Γ *ᵥ a) ⬝ᵥ (b + Γ *ᵥ a) =
          b ⬝ᵥ b + 2 * (b ⬝ᵥ (Γ *ᵥ a)) + (Γ *ᵥ a) ⬝ᵥ (Γ *ᵥ a) := by
        simp only [dotProduct_add, add_dotProduct, dotProduct_comm (Γ *ᵥ a) b]
        ring
      rw [Complex.nonneg_iff]
      simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
      linarith
  · rintro ⟨-, h⟩ a
    have := h (ofRealVec a + Complex.I • ofRealVec (-(Γ *ᵥ a)))
    rw [hermitianForm_eq hΓ, Complex.nonneg_iff] at this
    simp only [Complex.ofReal_re, neg_dotProduct, dotProduct_neg] at this
    linarith [this.1]

end Fermionic
