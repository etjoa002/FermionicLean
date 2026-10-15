/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Rotation
import FermionicLean.Fock.Gate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Every rotation is implemented by a Gaussian unitary

The factor `cos φ + sin φ c_a c_b` implements the plane rotation `R_ab(cos 2φ, sin 2φ)`
(Lemma 15); implementation is compatible with products, `U ~ O`, `V ~ O'` giving `U V ~ O' O`;
so every rotation product, hence every special orthogonal matrix on the Majorana labels
(Theorem 14), is implemented by a unitary product of such factors (Theorem 16).
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### One factor, one plane rotation -/

/-- Lemma 15: the factor `cos φ + sin φ c_a c_b` implements `R_ab(cos 2φ, sin 2φ)`. -/
theorem conjugatesMajorana_rotFactor {a b : MajoranaIndex n} (hab : a ≠ b) (φ : ℝ) :
    ConjugatesMajorana (rotFactor φ a b)
      (planeRot (Real.cos (2 * φ)) (Real.sin (2 * φ)) a b) := by
  intro d
  by_cases hda : d = a
  · subst hda
    rw [rotFactor_conj_left hab, Finset.sum_eq_add d b hab
      (fun x _ hx => by simp [planeRot, hx.1, hx.2])
      (fun h => absurd (Finset.mem_univ d) h) (fun h => absurd (Finset.mem_univ b) h)]
    simp only [planeRot, ite_true, hab, ite_false, Ne.symm hab]
    push_cast
    module
  · by_cases hdb : d = b
    · subst hdb
      rw [rotFactor_conj_right hab, Finset.sum_eq_add a d hab
        (fun x _ hx => by simp [planeRot, hx.1, hx.2])
        (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ d) h)]
      simp only [planeRot, ite_true, hab, ite_false, Ne.symm hab]
    · rw [rotFactor_conj_of_ne hab hda hdb, Finset.sum_eq_single d]
      · rw [planeRot_apply_of_ne hda hdb]; simp
      · intro x _ hx; rw [planeRot_apply_of_ne hda hdb]; simp [hx]
      · simp

/-- Lemma 15: every point of the unit circle is `(cos 2φ, sin 2φ)` for some `φ`. -/
lemma exists_angle_of_sq_add_sq {c s : ℝ} (hcs : c * c + s * s = 1) :
    ∃ φ : ℝ, Real.cos (2 * φ) = c ∧ Real.sin (2 * φ) = s := by
  have hc1 : -1 ≤ c := by nlinarith [mul_self_nonneg s, mul_self_nonneg (c + 1)]
  have hc2 : c ≤ 1 := by nlinarith [mul_self_nonneg s, mul_self_nonneg (c - 1)]
  have hs : Real.sqrt (1 - c ^ 2) = |s| := by
    rw [show 1 - c ^ 2 = s ^ 2 by nlinarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 s with hs0 | hs0
  · refine ⟨Real.arccos c / 2, ?_, ?_⟩
    · rw [show 2 * (Real.arccos c / 2) = Real.arccos c by ring, Real.cos_arccos hc1 hc2]
    · rw [show 2 * (Real.arccos c / 2) = Real.arccos c by ring, Real.sin_arccos, hs,
        abs_of_nonneg hs0]
  · refine ⟨-Real.arccos c / 2, ?_, ?_⟩
    · rw [show 2 * (-Real.arccos c / 2) = -Real.arccos c by ring, Real.cos_neg,
        Real.cos_arccos hc1 hc2]
    · rw [show 2 * (-Real.arccos c / 2) = -Real.arccos c by ring, Real.sin_neg,
        Real.sin_arccos, hs, abs_of_neg hs0, neg_neg]

/-- Lemma 15: the identity implements `1`. -/
theorem conjugatesMajorana_one :
    ConjugatesMajorana (1 : Matrix (FockIndex n) (FockIndex n) ℂ) 1 := by
  intro a
  simp [Matrix.one_apply]

/-- Lemma 15: the product rule, `U ~ O` and `V ~ O'` give `U V ~ O' O`. -/
theorem conjugatesMajorana_mul {U V : Matrix (FockIndex n) (FockIndex n) ℂ}
    {O O' : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} (hU : ConjugatesMajorana U O)
    (hV : ConjugatesMajorana V O') : ConjugatesMajorana (U * V) (O' * O) := by
  intro a
  rw [Matrix.conjTranspose_mul]
  calc U * V * majorana a * (V.conjTranspose * U.conjTranspose)
      = U * (V * majorana a * V.conjTranspose) * U.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = ∑ b, ((O' a b : ℝ) : ℂ) • (U * majorana b * U.conjTranspose) := by
        rw [hV a, Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = ∑ b, ((O' a b : ℝ) : ℂ) • ∑ d, ((O b d : ℝ) : ℂ) • majorana d := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hU b]
    _ = ∑ d, (((O' * O) a d : ℝ) : ℂ) • majorana d := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
        push_cast
        rfl

/-! ### Theorem 16 -/

/-- Every rotation product on the Majorana labels is implemented by a unitary. -/
theorem exists_unitary_of_isRotProduct {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hO : IsRotProduct O) :
    ∃ U : Matrix (FockIndex n) (FockIndex n) ℂ,
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ConjugatesMajorana U O := by
  induction hO with
  | one => exact ⟨1, by simp, by simp, conjugatesMajorana_one⟩
  | @mul_planeRot R c s a b hR hab hcs ih =>
    obtain ⟨U, hU, hU', hUO⟩ := ih
    obtain ⟨φ, hc, hs⟩ := exists_angle_of_sq_add_sq hcs
    have hV := conjugatesMajorana_rotFactor hab φ
    rw [hc, hs] at hV
    refine ⟨rotFactor φ a b * U, ?_, ?_, conjugatesMajorana_mul hV hUO⟩
    · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul,
        rotFactor_mul_conjTranspose hab]
    · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (rotFactor φ a b).conjTranspose, conjTranspose_mul_rotFactor hab,
        Matrix.one_mul, hU']

/-- Theorem 16: every special orthogonal matrix on the Majorana labels is implemented by a
unitary. -/
theorem exists_unitary_conjugatesMajorana (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hO : O * O.transpose = 1) (hdet : O.det = 1) :
    ∃ U : Matrix (FockIndex n) (FockIndex n) ℂ,
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ConjugatesMajorana U O :=
  exists_unitary_of_isRotProduct (isRotProduct_of_special_orthogonal O hO hdet)

end Fermionic
