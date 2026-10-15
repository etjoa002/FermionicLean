/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Congruence
import FermionicLean.Gaussian.BlockForm
import Mathlib.Analysis.Matrix.Spectrum

/-! # The real antisymmetric normal form

Every real antisymmetric matrix on the Majorana labels is `O D(ε) Oᵀ` with `O` orthogonal
and `ε ≥ 0` (Theorem 12). The route is spectral: `M = iΓ` is Hermitian, its orthonormal
eigenvectors `v_k` with eigenvalue `μ_k > 0` give the real vectors `e_k = √2 Re v_k`,
`f_k = -√2 Im v_k` with `Γ f_k = μ_k e_k`, `Γ e_k = -μ_k f_k`; they are orthonormal, are
completed to an orthonormal basis indexed by the labels, and every completing vector lies in
the kernel of `Γ`. The columns of that basis form `O`. Part (a) fixes `det O = 1` by the
reflection of `y_0`; part (b) reads the bounds `|ε_j| ≤ 1` (`= 1`) off `D(ε) = Oᵀ Γ O`.
-/

open Matrix

namespace Fermionic

/-! ### Spectral data of `iΓ` on a general finite label set -/

section General

variable {ι : Type*}

/-- Real part of a complex vector. -/
def reVec (v : ι → ℂ) : ι → ℝ := fun i => (v i).re

/-- Imaginary part of a complex vector. -/
def imVec (v : ι → ℂ) : ι → ℝ := fun i => (v i).im

lemma ofRealVec_reVec_add_smul_imVec (v : ι → ℂ) :
    ofRealVec (reVec v) + Complex.I • ofRealVec (imVec v) = v :=
  (eq_ofRealVec_re_add_smul_im v).symm

lemma reVec_ofRealVec (x : ι → ℝ) : reVec (ofRealVec x) = x := by
  funext i; simp [reVec, ofRealVec]

lemma imVec_ofRealVec (x : ι → ℝ) : imVec (ofRealVec x) = 0 := by
  funext i; simp [imVec, ofRealVec]

variable [Fintype ι]

lemma dotProduct_star_re (v w : ι → ℂ) :
    (v ⬝ᵥ star w).re = reVec v ⬝ᵥ reVec w + imVec v ⬝ᵥ imVec w := by
  simp only [dotProduct, Complex.re_sum, reVec, imVec, Complex.mul_re, Pi.star_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotProduct_star_im (v w : ι → ℂ) :
    (v ⬝ᵥ star w).im = imVec v ⬝ᵥ reVec w - reVec v ⬝ᵥ imVec w := by
  simp only [dotProduct, Complex.im_sum, reVec, imVec, Complex.mul_im, Pi.star_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotProduct_re (v w : ι → ℂ) :
    (v ⬝ᵥ w).re = reVec v ⬝ᵥ reVec w - imVec v ⬝ᵥ imVec w := by
  simp only [dotProduct, Complex.re_sum, reVec, imVec, Complex.mul_re]
  rw [← Finset.sum_sub_distrib]

lemma dotProduct_im (v w : ι → ℂ) :
    (v ⬝ᵥ w).im = reVec v ⬝ᵥ imVec w + imVec v ⬝ᵥ reVec w := by
  simp only [dotProduct, Complex.im_sum, reVec, imVec, Complex.mul_im]
  rw [← Finset.sum_add_distrib]

/-- The Hermitian matrix `iΓ`. -/
def cplx (Γ : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.I • Γ.map Complex.ofReal

omit [Fintype ι] in
lemma map_ofReal_neg (Γ : Matrix ι ι ℝ) : (-Γ).map Complex.ofReal = -(Γ.map Complex.ofReal) := by
  ext i j; simp

omit [Fintype ι] in
lemma cplx_isHermitian {Γ : Matrix ι ι ℝ} (hΓ : Γ.transpose = -Γ) : (cplx Γ).IsHermitian := by
  have hmap : (Γ.map Complex.ofReal).conjTranspose = Γ.transpose.map Complex.ofReal := by
    ext i j; simp
  unfold Matrix.IsHermitian cplx
  rw [Matrix.conjTranspose_smul, hmap, hΓ, Complex.star_def, Complex.conj_I, map_ofReal_neg,
    smul_neg, neg_smul, neg_neg]

omit [Fintype ι] in
lemma cplx_transpose {Γ : Matrix ι ι ℝ} (hΓ : Γ.transpose = -Γ) :
    (cplx Γ).transpose = -(cplx Γ) := by
  unfold cplx
  rw [Matrix.transpose_smul, ← Matrix.transpose_map, hΓ, map_ofReal_neg, smul_neg]

lemma cplx_mulVec_ofRealVec (Γ : Matrix ι ι ℝ) (x : ι → ℝ) :
    cplx Γ *ᵥ ofRealVec x = Complex.I • ofRealVec (Γ *ᵥ x) := by
  unfold cplx
  rw [Matrix.smul_mulVec, map_ofReal_mulVec_ofRealVec]

omit [Fintype ι] in
lemma real_smul_vec (x : ℝ) (v : ι → ℂ) : x • v = (x : ℂ) • v := by
  funext i; simp [Complex.real_smul]

/-- Real and imaginary parts of an eigenvector of `iΓ`. -/
lemma mulVec_reVec_imVec_of_cplx_mulVec_eq {Γ : Matrix ι ι ℝ} {v : ι → ℂ} {μ : ℝ}
    (hv : cplx Γ *ᵥ v = (μ : ℂ) • v) :
    Γ *ᵥ imVec v = -μ • reVec v ∧ Γ *ᵥ reVec v = μ • imVec v := by
  rw [← ofRealVec_reVec_add_smul_imVec v, Matrix.mulVec_add, Matrix.mulVec_smul,
    cplx_mulVec_ofRealVec, cplx_mulVec_ofRealVec] at hv
  constructor <;> funext i <;> have hi := congrFun hv i <;>
    simp only [Pi.add_apply, Pi.smul_apply, ofRealVec, smul_eq_mul, Complex.ext_iff, Complex.add_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im] at hi ⊢ <;> linarith [hi.1, hi.2]

section Eigen

variable [DecidableEq ι]

variable {Γ : Matrix ι ι ℝ} (hΓ : Γ.transpose = -Γ)

/-- Eigenvalues of `iΓ`. -/
noncomputable def eigVal (k : ι) : ℝ := (cplx_isHermitian hΓ).eigenvalues k

/-- Orthonormal eigenvectors of `iΓ`, as plain complex vectors. -/
noncomputable def eigVec (k : ι) : ι → ℂ :=
  WithLp.ofLp ((cplx_isHermitian hΓ).eigenvectorBasis k)

lemma cplx_mulVec_eigVec (k : ι) : cplx Γ *ᵥ eigVec hΓ k = (eigVal hΓ k : ℂ) • eigVec hΓ k := by
  rw [← real_smul_vec]
  exact (cplx_isHermitian hΓ).mulVec_eigenvectorBasis k

lemma eigVec_dotProduct_star (j k : ι) :
    eigVec hΓ k ⬝ᵥ star (eigVec hΓ j) = if j = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (cplx_isHermitian hΓ).eigenvectorBasis.orthonormal j k
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  exact h

/-- Eigenvectors for eigenvalues that do not sum to zero are bilinearly orthogonal. -/
lemma eigVec_dotProduct_eq_zero {j k : ι} (h : eigVal hΓ j + eigVal hΓ k ≠ 0) :
    eigVec hΓ j ⬝ᵥ eigVec hΓ k = 0 := by
  have h1 : eigVec hΓ j ⬝ᵥ (cplx Γ *ᵥ eigVec hΓ k) =
      (eigVal hΓ k : ℂ) * (eigVec hΓ j ⬝ᵥ eigVec hΓ k) := by
    rw [cplx_mulVec_eigVec, dotProduct_smul, smul_eq_mul]
  have h2 : eigVec hΓ j ⬝ᵥ (cplx Γ *ᵥ eigVec hΓ k) =
      -((eigVal hΓ j : ℂ) * (eigVec hΓ j ⬝ᵥ eigVec hΓ k)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, cplx_transpose hΓ, Matrix.neg_mulVec,
      cplx_mulVec_eigVec, neg_dotProduct, smul_dotProduct, smul_eq_mul]
  have h3 : ((eigVal hΓ j + eigVal hΓ k : ℝ) : ℂ) * (eigVec hΓ j ⬝ᵥ eigVec hΓ k) = 0 := by
    push_cast; linear_combination h2 - h1
  exact (mul_eq_zero.mp h3).resolve_left (Complex.ofReal_ne_zero.mpr h)

/-- The real vector `√2 Re v_k`. -/
noncomputable def eVec (k : ι) : ι → ℝ := Real.sqrt 2 • reVec (eigVec hΓ k)

/-- The real vector `-√2 Im v_k`. -/
noncomputable def fVec (k : ι) : ι → ℝ := -(Real.sqrt 2) • imVec (eigVec hΓ k)

lemma mulVec_eVec (k : ι) : Γ *ᵥ eVec hΓ k = -(eigVal hΓ k) • fVec hΓ k := by
  obtain ⟨-, h⟩ := mulVec_reVec_imVec_of_cplx_mulVec_eq (cplx_mulVec_eigVec hΓ k)
  rw [eVec, fVec, Matrix.mulVec_smul, h, smul_smul, smul_smul]
  congr 1; ring

lemma mulVec_fVec (k : ι) : Γ *ᵥ fVec hΓ k = eigVal hΓ k • eVec hΓ k := by
  obtain ⟨h, -⟩ := mulVec_reVec_imVec_of_cplx_mulVec_eq (cplx_mulVec_eigVec hΓ k)
  rw [eVec, fVec, Matrix.mulVec_smul, h, smul_smul, smul_smul]
  congr 1; ring

lemma sqrt_two_mul_sqrt_two : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- The real dot products of eigenvector real/imaginary parts, for `μ_j, μ_k > 0`. -/
lemma reIm_dotProducts {j k : ι} (hj : 0 < eigVal hΓ j) (hk : 0 < eigVal hΓ k) :
    (reVec (eigVec hΓ j) ⬝ᵥ reVec (eigVec hΓ k) = if j = k then 1 / 2 else 0) ∧
    (imVec (eigVec hΓ j) ⬝ᵥ imVec (eigVec hΓ k) = if j = k then 1 / 2 else 0) ∧
    reVec (eigVec hΓ j) ⬝ᵥ imVec (eigVec hΓ k) = 0 := by
  have h1 := eigVec_dotProduct_star hΓ j k
  have h2 := eigVec_dotProduct_eq_zero hΓ (j := j) (k := k) (by linarith)
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2re := congrArg Complex.re h2
  have h2im := congrArg Complex.im h2
  rw [dotProduct_star_re] at h1re
  rw [dotProduct_star_im] at h1im
  rw [dotProduct_re] at h2re
  rw [dotProduct_im] at h2im
  simp only [Complex.zero_re, Complex.zero_im] at h2re h2im
  have h1im0 : (if j = k then (1 : ℂ) else 0).im = 0 := by split_ifs <;> simp
  rw [h1im0, dotProduct_comm (imVec (eigVec hΓ k)) (reVec (eigVec hΓ j))] at h1im
  rw [dotProduct_comm (imVec (eigVec hΓ j)) (reVec (eigVec hΓ k))] at h2im
  rw [dotProduct_comm (reVec (eigVec hΓ k)), dotProduct_comm (imVec (eigVec hΓ k))] at h1re
  refine ⟨?_, ?_, ?_⟩
  · split_ifs at h1re ⊢ with hjk <;> simp at h1re <;> linarith
  · split_ifs at h1re ⊢ with hjk <;> simp at h1re <;> linarith
  · linarith

lemma eVec_dotProduct_eVec {j k : ι} (hj : 0 < eigVal hΓ j) (hk : 0 < eigVal hΓ k) :
    eVec hΓ j ⬝ᵥ eVec hΓ k = if j = k then 1 else 0 := by
  obtain ⟨h, -, -⟩ := reIm_dotProducts hΓ hj hk
  rw [eVec, eVec, smul_dotProduct, dotProduct_smul, h, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    sqrt_two_mul_sqrt_two]
  split_ifs <;> norm_num

lemma fVec_dotProduct_fVec {j k : ι} (hj : 0 < eigVal hΓ j) (hk : 0 < eigVal hΓ k) :
    fVec hΓ j ⬝ᵥ fVec hΓ k = if j = k then 1 else 0 := by
  obtain ⟨-, h, -⟩ := reIm_dotProducts hΓ hj hk
  rw [fVec, fVec, smul_dotProduct, dotProduct_smul, h, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    neg_mul_neg, sqrt_two_mul_sqrt_two]
  split_ifs <;> norm_num

lemma eVec_dotProduct_fVec {j k : ι} (hj : 0 < eigVal hΓ j) (hk : 0 < eigVal hΓ k) :
    eVec hΓ j ⬝ᵥ fVec hΓ k = 0 := by
  obtain ⟨-, -, h⟩ := reIm_dotProducts hΓ hj hk
  rw [eVec, fVec, smul_dotProduct, dotProduct_smul, h, smul_zero, smul_zero]

/-- Step (iv): a real vector orthogonal to every `e_k, f_k` with `μ_k > 0` is in the kernel. -/
lemma mulVec_eq_zero_of_orthogonal (x : ι → ℝ)
    (hx : ∀ k, 0 < eigVal hΓ k → eVec hΓ k ⬝ᵥ x = 0 ∧ fVec hΓ k ⬝ᵥ x = 0) : Γ *ᵥ x = 0 := by
  set b := (cplx_isHermitian hΓ).eigenvectorBasis with hb
  -- coefficients of `x` in the eigenbasis
  set c : ι → ℂ := fun k => ofRealVec x ⬝ᵥ star (eigVec hΓ k) with hc
  have hexp : ofRealVec x = ∑ k, c k • eigVec hΓ k := by
    have h := b.sum_repr' (WithLp.toLp 2 (ofRealVec x))
    have h2 := congrArg WithLp.ofLp h
    rw [WithLp.ofLp_sum] at h2
    simp only [WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at h2
    exact h2.symm
  have hpos : ∀ k, 0 < eigVal hΓ k → c k = 0 := by
    intro k hk
    obtain ⟨he, hf⟩ := hx k hk
    rw [eVec, smul_dotProduct, smul_eq_mul, mul_eq_zero] at he
    rw [fVec, smul_dotProduct, smul_eq_mul, mul_eq_zero] at hf
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have he2 : reVec (eigVec hΓ k) ⬝ᵥ x = 0 := he.resolve_left hs
    have hf2 : imVec (eigVec hΓ k) ⬝ᵥ x = 0 := hf.resolve_left (neg_ne_zero.mpr hs)
    apply Complex.ext
    · rw [hc, Complex.zero_re]
      simp only
      rw [dotProduct_star_re, reVec_ofRealVec, imVec_ofRealVec, zero_dotProduct, add_zero,
        dotProduct_comm, he2]
    · rw [hc, Complex.zero_im]
      simp only
      rw [dotProduct_star_im, reVec_ofRealVec, imVec_ofRealVec, zero_dotProduct, zero_sub,
        dotProduct_comm, hf2, neg_zero]
  have hstar : ∀ k, star (c k) = eigVec hΓ k ⬝ᵥ ofRealVec x := by
    intro k
    rw [hc]
    simp only
    rw [← star_dotProduct_star, star_star, star_ofRealVec]
  have hneg : ∀ k, eigVal hΓ k < 0 → c k = 0 := by
    intro k hk
    rw [← star_eq_zero, hstar, hexp, dotProduct_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    by_cases hjk : eigVal hΓ k + eigVal hΓ j = 0
    · have hj : 0 < eigVal hΓ j := by linarith
      rw [hpos j hj, zero_mul]
    · rw [eigVec_dotProduct_eq_zero hΓ hjk, mul_zero]
  have hM : cplx Γ *ᵥ ofRealVec x = 0 := by
    rw [hexp, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.mulVec_smul, cplx_mulVec_eigVec, smul_smul]
    rcases lt_trichotomy (eigVal hΓ k) 0 with hk | hk | hk
    · rw [hneg k hk, zero_mul, zero_smul]
    · rw [hk, Complex.ofReal_zero, mul_zero, zero_smul]
    · rw [hpos k hk, zero_mul, zero_smul]
  rw [cplx_mulVec_ofRealVec] at hM
  funext i
  have hi := congrFun hM i
  simp only [Pi.smul_apply, ofRealVec, smul_eq_mul, Pi.zero_apply, mul_eq_zero,
    Complex.I_ne_zero, false_or, Complex.ofReal_eq_zero] at hi
  exact hi

end Eigen

end General

/-! ### Theorem 12 (b) and the reduction of (a) -/

variable {n : ℕ}

lemma blockForm_eq_of_normalForm {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} (hO : O * O.transpose = 1) (h : Γ = O * blockForm ε * O.transpose) :
    blockForm ε = O.transpose * Γ * O.transpose.transpose := by
  have hOtO := transpose_mul_self_of_mul_transpose hO
  rw [Matrix.transpose_transpose, h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul, Matrix.mul_one]

/-- Theorem 12(b): in any such decomposition of an admissible matrix, `|ε_j| ≤ 1`. -/
theorem abs_le_one_of_isAdmissible_normalForm {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} (hO : O * O.transpose = 1) (h : Γ = O * blockForm ε * O.transpose)
    (hΓ : IsAdmissible Γ) : ∀ j, |ε j| ≤ 1 := by
  rw [← isAdmissible_blockForm_iff, blockForm_eq_of_normalForm hO h]
  exact isAdmissible_orthogonalCongruence (transpose_mul_self_of_mul_transpose hO) hΓ

/-- Theorem 12(b): for a pure matrix, `|ε_j| = 1`. -/
theorem abs_eq_one_of_isPure_normalForm {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} (hO : O * O.transpose = 1) (h : Γ = O * blockForm ε * O.transpose)
    (hΓ : IsPure Γ) : ∀ j, |ε j| = 1 := by
  rw [← isPure_blockForm_iff, blockForm_eq_of_normalForm hO h]
  exact isPure_orthogonalCongruence (transpose_mul_self_of_mul_transpose hO) hΓ

/-! ### The reflection of the label `y_0` -/

/-- The sign vector `-1` at `y_0`, `+1` elsewhere. -/
def reflectSign (n : ℕ) (hn : 0 < n) : MajoranaIndex n → ℝ :=
  Sum.elim (fun _ => 1) (fun j => if j = ⟨0, hn⟩ then -1 else 1)

lemma reflectSign_mul_self (hn : 0 < n) (i : MajoranaIndex n) :
    reflectSign n hn i * reflectSign n hn i = 1 := by
  rcases i with j | j
  · simp [reflectSign]
  · simp only [reflectSign, Sum.elim_inr]; split_ifs <;> norm_num

lemma diagonal_reflectSign_mul_transpose (hn : 0 < n) :
    Matrix.diagonal (reflectSign n hn) * (Matrix.diagonal (reflectSign n hn)).transpose = 1 := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, reflectSign_mul_self]

lemma det_diagonal_reflectSign (hn : 0 < n) :
    (Matrix.diagonal (reflectSign n hn)).det = -1 := by
  rw [Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [reflectSign]

lemma diagonal_reflectSign_mul_blockForm (hn : 0 < n) (ε : Fin n → ℝ) :
    Matrix.diagonal (reflectSign n hn) * blockForm ε * Matrix.diagonal (reflectSign n hn) =
      blockForm (fun j => if j = ⟨0, hn⟩ then -ε j else ε j) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockForm, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.fromBlocks, reflectSign,
      ] <;> split_ifs <;> simp_all

lemma det_eq_one_or_neg_one_of_orthogonal {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hO : O * O.transpose = 1) : O.det = 1 ∨ O.det = -1 := by
  have h := congrArg Matrix.det hO
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.mp h

/-- Theorem 12(a) from the existence of some normal form: reflect `y_0` if `det O = -1`. -/
theorem exists_normalForm_special_of_exists
    (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (h : ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * O.transpose = 1 ∧ Γ = O * blockForm ε * O.transpose) :
    ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * O.transpose = 1 ∧ O.det = 1 ∧ Γ = O * blockForm ε * O.transpose := by
  obtain ⟨O, ε, hO, hΓ⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨O, ε, hO, Matrix.det_isEmpty, hΓ⟩
  rcases det_eq_one_or_neg_one_of_orthogonal hO with hdet | hdet
  · exact ⟨O, ε, hO, hdet, hΓ⟩
  have hΘΘ := diagonal_reflectSign_mul_transpose hn
  have hΘ2 : Matrix.diagonal (reflectSign n hn) * Matrix.diagonal (reflectSign n hn) = 1 := by
    rwa [Matrix.diagonal_transpose] at hΘΘ
  refine ⟨O * Matrix.diagonal (reflectSign n hn), fun j => if j = ⟨0, hn⟩ then -ε j else ε j,
    ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), hΘΘ,
      Matrix.one_mul, hO]
  · rw [Matrix.det_mul, hdet, det_diagonal_reflectSign]; norm_num
  · rw [← diagonal_reflectSign_mul_blockForm hn, Matrix.transpose_mul, Matrix.diagonal_transpose,
      hΓ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hΘ2, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hΘ2, Matrix.one_mul]


/-! ### Theorem 12: existence of the normal form -/

/-- Theorem 12: every real antisymmetric matrix on the Majorana labels is `O D(ε) Oᵀ` with `O`
orthogonal and `ε ≥ 0`. -/
theorem exists_normalForm (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : Γ.transpose = -Γ) :
    ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * O.transpose = 1 ∧ (∀ j, 0 ≤ ε j) ∧ Γ = O * blockForm ε * O.transpose := by
  classical
  -- the eigenvector indices with positive eigenvalue
  let P := {k : MajoranaIndex n // 0 < eigVal hΓ k}
  -- step (ii): the orthonormal family `e_k, f_k`
  let g : P ⊕ P → EuclideanSpace ℝ (MajoranaIndex n) :=
    Sum.elim (fun k => WithLp.toLp 2 (eVec hΓ k.1)) (fun k => WithLp.toLp 2 (fVec hΓ k.1))
  have hg : Orthonormal ℝ g := by
    rw [orthonormal_iff_ite]
    rintro (j | j) (k | k) <;>
      simp only [g, Sum.elim_inl, Sum.elim_inr, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false]
    · rw [eVec_dotProduct_eVec hΓ k.2 j.2]
      by_cases h : j = k
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (Subtype.ext h'.symm))]
    · rw [dotProduct_comm, eVec_dotProduct_fVec hΓ j.2 k.2]
    · rw [eVec_dotProduct_fVec hΓ k.2 j.2]
    · rw [fVec_dotProduct_fVec hΓ k.2 j.2]
      by_cases h : j = k
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (Subtype.ext h'.symm))]
  -- step (iii): `2 |P| ≤ 2n`, an injection `φ : P ↪ Fin n`, and the placement `ψ`
  have hcard : Fintype.card P ≤ Fintype.card (Fin n) := by
    have h := hg.linearIndependent.fintype_card_le_finrank
    rw [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin] at h
    rw [Fintype.card_fin]
    omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ψ : P ⊕ P → MajoranaIndex n := Sum.map φ φ
  have hψ : Function.Injective ψ := φ.injective.sumMap φ.injective
  let v : MajoranaIndex n → EuclideanSpace ℝ (MajoranaIndex n) := fun ℓ =>
    if h : ℓ ∈ Set.range ψ then g ((Equiv.ofInjective ψ hψ).symm ⟨ℓ, h⟩) else 0
  have hv : Orthonormal ℝ ((Set.range ψ).domRestrict v) := by
    have : (Set.range ψ).domRestrict v = g ∘ (Equiv.ofInjective ψ hψ).symm := by
      funext x
      simp only [Set.domRestrict, Function.comp, v, dite_eq_left x.2]
    rw [this]
    exact hg.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  have hplace : ∀ a : P ⊕ P, WithLp.ofLp (b (ψ a)) = WithLp.ofLp (g a) := by
    intro a
    rw [hb (ψ a) (Set.mem_range_self a)]
    simp only [v, dite_eq_left (Set.mem_range_self a), Equiv.ofInjective_symm_apply]
  have hbe : ∀ k : P, WithLp.ofLp (b (Sum.inl (φ k))) = eVec hΓ k.1 := fun k => hplace (Sum.inl k)
  have hbf : ∀ k : P, WithLp.ofLp (b (Sum.inr (φ k))) = fVec hΓ k.1 := fun k => hplace (Sum.inr k)
  have hborth : ∀ ℓ ℓ', WithLp.ofLp (b ℓ) ⬝ᵥ WithLp.ofLp (b ℓ') = if ℓ = ℓ' then 1 else 0 := by
    intro ℓ ℓ'
    have h := orthonormal_iff_ite.mp b.orthonormal ℓ ℓ'
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at h
    exact h
  -- step (iv): the completing vectors lie in the kernel
  have hker : ∀ ℓ, ℓ ∉ Set.range ψ → Γ *ᵥ WithLp.ofLp (b ℓ) = 0 := by
    intro ℓ hℓ
    apply mulVec_eq_zero_of_orthogonal hΓ
    intro k hk
    have h1 : Sum.inl (φ ⟨k, hk⟩) ≠ ℓ := fun h => hℓ ⟨Sum.inl ⟨k, hk⟩, h⟩
    have h2 : Sum.inr (φ ⟨k, hk⟩) ≠ ℓ := fun h => hℓ ⟨Sum.inr ⟨k, hk⟩, h⟩
    constructor
    · have := hborth (Sum.inl (φ ⟨k, hk⟩)) ℓ
      rwa [hbe, ite_eq_right h1] at this
    · have := hborth (Sum.inr (φ ⟨k, hk⟩)) ℓ
      rwa [hbf, ite_eq_right h2] at this
  have hkerl : ∀ j, j ∉ Set.range φ → Sum.inl j ∉ Set.range ψ := by
    rintro j hj ⟨a | a, ha⟩
    · exact hj ⟨a, Sum.inl.inj ha⟩
    · simp [ψ] at ha
  have hkerr : ∀ j, j ∉ Set.range φ → Sum.inr j ∉ Set.range ψ := by
    rintro j hj ⟨a | a, ha⟩
    · simp [ψ] at ha
    · exact hj ⟨a, Sum.inr.inj ha⟩
  -- step (v): the matrix `O` with columns `b ℓ`, and the weights `ε`
  let O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ := Matrix.of fun i ℓ => WithLp.ofLp (b ℓ) i
  have hOtO : O.transpose * O = 1 := by
    ext ℓ ℓ'
    rw [Matrix.one_apply, ← hborth ℓ ℓ']
    rfl
  have hO : O * O.transpose = 1 := mul_eq_one_comm.mp hOtO
  let ε : Fin n → ℝ := fun j =>
    if h : j ∈ Set.range φ then eigVal hΓ ((Equiv.ofInjective φ φ.injective).symm ⟨j, h⟩).1 else 0
  have hε : ∀ k : P, ε (φ k) = eigVal hΓ k.1 := by
    intro k
    simp only [ε, dite_eq_left (Set.mem_range_self k), Equiv.ofInjective_symm_apply]
  have hε0 : ∀ j, j ∉ Set.range φ → ε j = 0 := by
    intro j hj
    simp only [ε, dite_eq_right hj]
  have hεnn : ∀ j, 0 ≤ ε j := by
    intro j
    by_cases hj : j ∈ Set.range φ
    · obtain ⟨k, rfl⟩ := hj
      rw [hε]
      exact k.2.le
    · rw [hε0 j hj]
  have hentry : ∀ ℓ ℓ', (O.transpose * Γ * O) ℓ ℓ' =
      WithLp.ofLp (b ℓ) ⬝ᵥ (Γ *ᵥ WithLp.ofLp (b ℓ')) := by
    intro ℓ ℓ'
    rw [Matrix.mul_assoc]
    rfl
  have hD : O.transpose * Γ * O = blockForm ε := by
    ext ℓ ℓ'
    rw [hentry]
    rcases ℓ' with j' | j'
    · by_cases hj' : j' ∈ Set.range φ
      · obtain ⟨k, rfl⟩ := hj'
        rw [hbe, mulVec_eVec, dotProduct_smul, ← hbf, hborth]
        rcases ℓ with j | j
        · simp [blockForm, Matrix.fromBlocks]
        · by_cases h : j = φ k
          · subst h
            simp [blockForm, Matrix.fromBlocks, hε]
          · simp [blockForm, Matrix.fromBlocks, h]
      · rw [hker _ (hkerl j' hj'), dotProduct_zero]
        rcases ℓ with j | j
        · simp [blockForm, Matrix.fromBlocks]
        · by_cases h : j = j'
          · subst h
            simp [blockForm, Matrix.fromBlocks, hε0 j hj']
          · simp [blockForm, Matrix.fromBlocks, Matrix.diagonal_apply_ne _ h]
    · by_cases hj' : j' ∈ Set.range φ
      · obtain ⟨k, rfl⟩ := hj'
        rw [hbf, mulVec_fVec, dotProduct_smul, ← hbe, hborth]
        rcases ℓ with j | j
        · by_cases h : j = φ k
          · subst h
            simp [blockForm, Matrix.fromBlocks, hε]
          · simp [blockForm, Matrix.fromBlocks, h]
        · simp [blockForm, Matrix.fromBlocks]
      · rw [hker _ (hkerr j' hj'), dotProduct_zero]
        rcases ℓ with j | j
        · by_cases h : j = j'
          · subst h
            simp [blockForm, Matrix.fromBlocks, hε0 j hj']
          · simp [blockForm, Matrix.fromBlocks, Matrix.diagonal_apply_ne _ h]
        · simp [blockForm, Matrix.fromBlocks]
  refine ⟨O, ε, hO, hεnn, ?_⟩
  rw [← hD]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc O O.transpose, hO, Matrix.one_mul, Matrix.mul_one]

/-- Theorem 12(a): the normal form with `det O = 1` (one sign of `ε` may flip). -/
theorem exists_normalForm_special (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : Γ.transpose = -Γ) :
    ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * O.transpose = 1 ∧ O.det = 1 ∧ Γ = O * blockForm ε * O.transpose := by
  obtain ⟨O, ε, hO, -, h⟩ := exists_normalForm Γ hΓ
  exact exists_normalForm_special_of_exists Γ ⟨O, ε, hO, h⟩

end Fermionic
