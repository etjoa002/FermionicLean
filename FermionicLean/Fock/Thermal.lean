/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Realization
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! # The exponential family and thermal states

`gaussianState h = exp (-H_h) / Tr exp (-H_h)` for a real antisymmetric `h`. In the block form it
is the product mixture with parameter `-tanh (ε/2)` (Lemma 2), so for `h = O D(ε) Oᵀ` it is
`Uᴴ ρ_{-tanh(ε/2)} U`: a density operator with covariance `O D(-tanh(ε/2)) Oᵀ` (Theorem 3). The
thermal state of `H_h` at inverse temperature `β` is `gaussianState (β • h)` (Corollary 4).
The covariance of an exponential state is strictly admissible (Proposition 5), and every
strictly admissible covariance is realized by the exponential family, with the parameter
unique in a frame (Theorem 6).
-/

open Matrix NormedSpace

namespace Fermionic

variable {n : ℕ}

/-! ### Definition 1 -/

/-- Definition 1: the partition function `Z(h) = Tr exp (-H_h)`. -/
noncomputable def partitionFunction (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : ℂ :=
  (exp (-(quadHam h))).trace

/-- Definition 1: the exponential state `ρ_h = exp (-H_h) / Z(h)`. -/
noncomputable def gaussianState (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  (partitionFunction h)⁻¹ • exp (-(quadHam h))

/-- Definition 1: the thermal state of `H_h` at inverse temperature `β`, `exp (-β H_h) / Z`. -/
noncomputable def thermalState (β : ℝ) (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  gaussianState (β • h)

/-- `H_{-h} = -H_h`. -/
lemma quadHam_neg (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    quadHam (-h) = -quadHam h := by
  unfold quadHam
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← neg_smul]
  congr 1
  simp only [hamCoeff, Matrix.neg_apply, Complex.ofReal_neg]
  ring

lemma blockForm_neg (ε : Fin n → ℝ) : blockForm (-ε) = -blockForm ε := by
  ext (a | a) (b | b) <;>
    simp [blockForm, Matrix.fromBlocks, Matrix.diagonal_apply] <;> split_ifs <;> simp

lemma blockEnergy_neg (ε : Fin n → ℝ) (s : FockIndex n) :
    blockEnergy (-ε) s = -blockEnergy ε s := by
  simp [blockEnergy, Finset.sum_neg_distrib]

/-- `-H_{D(ε)} = H_{D(-ε)}`. -/
lemma neg_quadHam_blockForm (ε : Fin n → ℝ) :
    -(quadHam (blockForm ε)) = quadHam (blockForm (-ε)) := by
  rw [blockForm_neg, quadHam_neg]

lemma prod_two_mul_cosh_neg (ε : Fin n → ℝ) :
    ∏ j, 2 * Real.cosh ((-ε) j / 2) = ∏ j, 2 * Real.cosh (ε j / 2) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Pi.neg_apply, neg_div, Real.cosh_neg]

/-! ### Lemma 2: the block form -/

/-- `exp (H_{D(ε)})` is the diagonal of the entrywise exponentials. -/
theorem exp_quadHam_blockForm (ε : Fin n → ℝ) :
    exp (quadHam (blockForm ε)) =
      Matrix.diagonal fun s => ((Real.exp (blockEnergy ε s) : ℝ) : ℂ) := by
  rw [quadHam_blockForm, Matrix.exp_diagonal]
  congr 1
  funext s
  rw [Pi.coe_exp, Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]

/-- Lemma 2(a): `exp (-H_{D(ε)})` is the diagonal of `exp (-d_ε(s))`. -/
theorem exp_neg_quadHam_blockForm (ε : Fin n → ℝ) :
    exp (-(quadHam (blockForm ε))) =
      Matrix.diagonal fun s => ((Real.exp (-blockEnergy ε s) : ℝ) : ℂ) := by
  rw [neg_quadHam_blockForm, exp_quadHam_blockForm]
  simp only [blockEnergy_neg]

/-- The entrywise weight `exp (∑_j ε_j (s_j - 1/2)) = ∏_j exp (ε_j (s_j - 1/2))`. -/
lemma exp_blockEnergy (ε : Fin n → ℝ) (s : FockIndex n) :
    Real.exp (blockEnergy ε s) = ∏ j, Real.exp (ε j * ((s j : ℕ) - 1 / 2)) := by
  unfold blockEnergy
  rw [Real.exp_sum]

/-- The one-mode weight: `exp (ε (b - 1/2)) = 2 cosh (ε/2) · p_b` with `p` the Bernoulli weight
of parameter `tanh (ε/2)`. -/
lemma exp_mul_sub_half_eq (ε : ℝ) (b : Fin 2) :
    Real.exp (ε * ((b : ℕ) - 1 / 2)) = 2 * Real.cosh (ε / 2) * bernoulli (Real.tanh (ε / 2)) b := by
  have hc := (Real.cosh_pos (ε / 2)).ne'
  have h0 : 2 * Real.cosh (ε / 2) * ((1 - Real.tanh (ε / 2)) / 2) = Real.exp (-(ε / 2)) := by
    rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_sub_sinh]
    field_simp
  have h1 : 2 * Real.cosh (ε / 2) * ((1 + Real.tanh (ε / 2)) / 2) = Real.exp (ε / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_add_sinh]
    field_simp
  fin_cases b
  · simp only [bernoulli, Fin.zero_eta, Fin.isValue, ↓reduceIte, Nat.cast_zero, zero_sub]
    rw [h0]; congr 1; ring
  · simp only [bernoulli, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Nat.cast_one]
    rw [h1]; congr 1; ring

/-- The weight of a configuration as a multiple of the product weight. -/
lemma exp_blockEnergy_eq_productWeight (ε : Fin n → ℝ) (s : FockIndex n) :
    Real.exp (blockEnergy ε s) =
      (∏ j, 2 * Real.cosh (ε j / 2)) * productWeight (fun j => Real.tanh (ε j / 2)) s := by
  rw [exp_blockEnergy, productWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => exp_mul_sub_half_eq (ε j) (s j)

/-- `Tr exp (H_{D(ε)}) = ∏_j 2 cosh (ε_j / 2)`. -/
theorem trace_exp_quadHam_blockForm (ε : Fin n → ℝ) :
    (exp (quadHam (blockForm ε))).trace = ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ) := by
  rw [exp_quadHam_blockForm, Matrix.trace_diagonal]
  simp only [exp_blockEnergy_eq_productWeight]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, sum_productWeight, mul_one]

/-- Lemma 2(b): `Z(D(ε)) = ∏_j 2 cosh (ε_j / 2)`. -/
theorem partitionFunction_blockForm (ε : Fin n → ℝ) :
    partitionFunction (blockForm ε) = ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ) := by
  unfold partitionFunction
  rw [neg_quadHam_blockForm, trace_exp_quadHam_blockForm, prod_two_mul_cosh_neg]

lemma prod_two_mul_cosh_pos (ε : Fin n → ℝ) : 0 < ∏ j, 2 * Real.cosh (ε j / 2) :=
  Finset.prod_pos fun j _ => by positivity

/-- The product mixture is the diagonal matrix of the product weights. -/
lemma productMixture_eq_diagonal (lam : Fin n → ℝ) :
    productMixture lam = Matrix.diagonal fun s => ((productWeight lam s : ℝ) : ℂ) := by
  ext s t
  simp only [productMixture, Matrix.sum_apply, Matrix.smul_apply, occupation, smul_eq_mul,
    Matrix.diagonal_apply]
  simp only [Matrix.single_apply]
  rw [Finset.sum_eq_single s]
  · by_cases hst : s = t <;> simp [hst]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- `Z(D(ε))⁻¹ exp (H_{D(ε)})` is the product mixture with parameter `tanh (ε/2)`. -/
theorem inv_smul_exp_quadHam_blockForm (ε : Fin n → ℝ) :
    ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ)⁻¹ • exp (quadHam (blockForm ε)) =
      productMixture fun j => Real.tanh (ε j / 2) := by
  rw [exp_quadHam_blockForm, productMixture_eq_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext s
  rw [Pi.smul_apply, smul_eq_mul, exp_blockEnergy_eq_productWeight]
  have h0 : ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (prod_two_mul_cosh_pos ε).ne'
  rw [Complex.ofReal_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-- Lemma 2(c): `ρ_{D(ε)}` is the product mixture with parameter `-tanh (ε/2)`. -/
theorem gaussianState_blockForm (ε : Fin n → ℝ) :
    gaussianState (blockForm ε) = productMixture fun j => -Real.tanh (ε j / 2) := by
  unfold gaussianState
  rw [partitionFunction_blockForm, neg_quadHam_blockForm, ← prod_two_mul_cosh_neg,
    inv_smul_exp_quadHam_blockForm]
  congr 1
  funext j
  rw [Pi.neg_apply, neg_div, Real.tanh_neg]

lemma abs_tanh_half_lt_one (ε : Fin n → ℝ) (j : Fin n) : |-Real.tanh (ε j / 2)| < 1 := by
  rw [abs_neg]; exact Real.abs_tanh_lt_one _

lemma abs_tanh_half_le_one (ε : Fin n → ℝ) (j : Fin n) : |-Real.tanh (ε j / 2)| ≤ 1 :=
  (abs_tanh_half_lt_one ε j).le

/-- Lemma 2(c): `ρ_{D(ε)}` is a density operator with covariance `D(-tanh (ε/2))`. -/
theorem isDensity_gaussianState_blockForm (ε : Fin n → ℝ) :
    IsDensity (gaussianState (blockForm ε)) := by
  rw [gaussianState_blockForm]
  exact isDensity_productMixture (abs_tanh_half_le_one ε)

theorem covariance_gaussianState_blockForm (ε : Fin n → ℝ) :
    covariance (gaussianState (blockForm ε)) = blockForm fun j => -Real.tanh (ε j / 2) := by
  rw [gaussianState_blockForm, covariance_productMixture]

/-- The energy form of `O D(ε) Oᵀ` on `O D(λ) Oᵀ` is `(1/2) ∑_j ε_j λ_j`. -/
lemma energyForm_conj_blockForm {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hOO : O * O.transpose = 1) (ε lam : Fin n → ℝ) :
    energyForm (O * blockForm ε * O.transpose) (O * blockForm lam * O.transpose) =
      1 / 2 * ∑ j, ε j * lam j := by
  rw [energyForm_rotated O _ ε (orthogonalCongruence_transpose (blockForm_transpose _))]
  have hOtO := transpose_mul_self_of_mul_transpose hOO
  have : O.transpose * (O * blockForm lam * O.transpose) * O = blockForm lam := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul, Matrix.mul_one]
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [blockForm, Matrix.fromBlocks_apply₁₂]

/-! ### Theorem 3: the exponential family -/

section Rotated

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {ε : Fin n → ℝ}

lemma isUnit_of_conjTranspose_mul (hU' : U.conjTranspose * U = 1) : IsUnit U :=
  (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_left_inverse hU')

lemma inv_eq_conjTranspose (hU' : U.conjTranspose * U = 1) : U⁻¹ = U.conjTranspose :=
  Matrix.inv_eq_left_inv hU'

/-- `exp (Uᴴ A U) = Uᴴ exp A U` for a unitary `U`. -/
lemma exp_conjTranspose_mul_mul (hU' : U.conjTranspose * U = 1)
    (A : Matrix (FockIndex n) (FockIndex n) ℂ) :
    exp (U.conjTranspose * A * U) = U.conjTranspose * exp A * U := by
  rw [← inv_eq_conjTranspose hU']
  exact Matrix.exp_conj' U A (isUnit_of_conjTranspose_mul hU')

/-- `exp (-H_h) = Uᴴ exp (-H_{D(ε)}) U` for `h = O D(ε) Oᵀ` and `U` implementing `O`. -/
lemma exp_neg_quadHam_conj (hU' : U.conjTranspose * U = 1) (hO : ConjugatesMajorana U O)
    (hOO : O * O.transpose = 1) :
    exp (-(quadHam (O * blockForm ε * O.transpose))) =
      U.conjTranspose * exp (-(quadHam (blockForm ε))) * U := by
  rw [← conjTranspose_mul_quadHam_blockForm_mul hU' hO hOO, ← Matrix.neg_mul, ← Matrix.mul_neg,
    exp_conjTranspose_mul_mul hU']

lemma trace_conjTranspose_mul_mul (hU : U * U.conjTranspose = 1)
    (A : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (U.conjTranspose * A * U).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- Theorem 3(a): `Z(O D(ε) Oᵀ) = ∏_j 2 cosh (ε_j / 2)`. -/
theorem partitionFunction_conj (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    partitionFunction (O * blockForm ε * O.transpose) =
      ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ) := by
  unfold partitionFunction
  rw [exp_neg_quadHam_conj hU' hO hOO, trace_conjTranspose_mul_mul hU]
  exact partitionFunction_blockForm ε

/-- Theorem 3(a): `ρ_{O D(ε) Oᵀ} = Uᴴ ρ_{D(ε)} U = Uᴴ ρ_{-tanh(ε/2)} U`, the realization of F6. -/
theorem gaussianState_conj (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    gaussianState (O * blockForm ε * O.transpose) =
      realization U fun j => -Real.tanh (ε j / 2) := by
  unfold realization
  rw [← gaussianState_blockForm]
  unfold gaussianState
  rw [partitionFunction_conj hU hU' hO hOO, partitionFunction_blockForm,
    exp_neg_quadHam_conj hU' hO hOO, Matrix.mul_smul, Matrix.smul_mul]

/-- Theorem 3(a): `ρ_{O D(ε) Oᵀ}` is a density operator. -/
theorem isDensity_gaussianState_conj (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    IsDensity (gaussianState (O * blockForm ε * O.transpose)) := by
  rw [gaussianState_conj hU hU' hO hOO]
  exact (covariance_conj' hU hU' hO (isDensity_productMixture (abs_tanh_half_le_one ε))).1

/-- Theorem 3(a): `Γ(ρ_{O D(ε) Oᵀ}) = O D(-tanh (ε/2)) Oᵀ`. -/
theorem covariance_gaussianState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    covariance (gaussianState (O * blockForm ε * O.transpose)) =
      O * blockForm (fun j => -Real.tanh (ε j / 2)) * O.transpose := by
  rw [gaussianState_conj hU hU' hO hOO]
  unfold realization
  rw [(covariance_conj' hU hU' hO (isDensity_productMixture (abs_tanh_half_le_one ε))).2,
    covariance_productMixture]

/-- Theorem 3(a): the energy `Tr(ρ_h H_h) = -(1/2) ∑_j ε_j tanh (ε_j / 2)`. -/
theorem energy_gaussianState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    energy (O * blockForm ε * O.transpose) (gaussianState (O * blockForm ε * O.transpose)) =
      -(1 / 2 * ∑ j, ε j * Real.tanh (ε j / 2)) := by
  have hh : (O * blockForm ε * O.transpose).transpose = -(O * blockForm ε * O.transpose) :=
    orthogonalCongruence_transpose (blockForm_transpose _)
  have hd := isDensity_gaussianState_conj (ε := ε) hU hU' hO hOO
  rw [energy_eq_energyForm hh hd.1.1, covariance_gaussianState hU hU' hO hOO,
    energyForm_conj_blockForm hOO]
  simp only [mul_neg, Finset.sum_neg_distrib]

end Rotated

/-- Theorem 3(b): `Z(h)` is a positive real number for every antisymmetric `h`. -/
theorem exists_partitionFunction_eq (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) :
    ∃ z : ℝ, 0 < z ∧ partitionFunction h = (z : ℂ) := by
  obtain ⟨O, ε, U, hOO, -, hOε, hU, hU', hUO⟩ := exists_normalForm_unitary h hh
  refine ⟨∏ j, 2 * Real.cosh (ε j / 2), prod_two_mul_cosh_pos ε, ?_⟩
  rw [hOε, partitionFunction_conj hU hU' hUO hOO]

/-- Theorem 3(b): `ρ_h` is a density operator for every antisymmetric `h`. -/
theorem isDensity_gaussianState (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) : IsDensity (gaussianState h) := by
  obtain ⟨O, ε, U, hOO, -, hOε, hU, hU', hUO⟩ := exists_normalForm_unitary h hh
  rw [hOε]
  exact isDensity_gaussianState_conj hU hU' hUO hOO

/-- Theorem 3(b): for every antisymmetric `h` there is a special-orthogonal normal form
`h = O D(ε) Oᵀ` with `Γ(ρ_h) = O D(tanh (ε/2)) Oᵀ`. -/
theorem exists_covariance_gaussianState (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) :
    ∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * O.transpose = 1 ∧ O.det = 1 ∧ h = O * blockForm ε * O.transpose ∧
      covariance (gaussianState h) =
        O * blockForm (fun j => -Real.tanh (ε j / 2)) * O.transpose := by
  obtain ⟨O, ε, U, hOO, hdet, hOε, hU, hU', hUO⟩ := exists_normalForm_unitary h hh
  refine ⟨O, ε, hOO, hdet, hOε, ?_⟩
  rw [hOε]
  exact covariance_gaussianState hU hU' hUO hOO

/-! ### Corollary 4: thermal states -/

lemma blockForm_neg_smul (β : ℝ) (ε : Fin n → ℝ) :
    blockForm (-(β • ε)) = -(β • blockForm ε) := by
  ext (a | a) (b | b) <;>
    simp [blockForm, Matrix.fromBlocks, Matrix.diagonal_apply] <;> split_ifs <;> simp

lemma blockForm_zero : blockForm (0 : Fin n → ℝ) = 0 := by
  ext (a | a) (b | b) <;> simp [blockForm, Matrix.fromBlocks]

/-- `β h = O D(β ε) Oᵀ` for `h = O D(ε) Oᵀ`. -/
lemma smul_conj_blockForm (β : ℝ) (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (ε : Fin n → ℝ) :
    β • (O * blockForm ε * O.transpose) = O * blockForm (β • ε) * O.transpose := by
  have : blockForm (β • ε) = β • blockForm ε := by
    have := blockForm_neg_smul β ε
    rw [blockForm_neg] at this
    exact neg_injective this
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

section Thermal

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {ε : Fin n → ℝ}

/-- Corollary 4: the thermal state is a density operator. -/
theorem isDensity_thermalState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) (β : ℝ) :
    IsDensity (thermalState β (O * blockForm ε * O.transpose)) := by
  unfold thermalState
  rw [smul_conj_blockForm]
  exact isDensity_gaussianState_conj hU hU' hO hOO

/-- Corollary 4: `Γ(ρ_{β h}) = O D(-tanh (β ε / 2)) Oᵀ`. -/
theorem covariance_thermalState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) (β : ℝ) :
    covariance (thermalState β (O * blockForm ε * O.transpose)) =
      O * blockForm (fun j => -Real.tanh (β * ε j / 2)) * O.transpose := by
  unfold thermalState
  rw [smul_conj_blockForm, covariance_gaussianState hU hU' hO hOO]
  rfl

/-- Corollary 4: the thermal energy `Tr(ρ_{β h} H_h) = -(1/2) ∑_j ε_j tanh (β ε_j / 2)`. -/
theorem energy_thermalState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) (β : ℝ) :
    energy (O * blockForm ε * O.transpose) (thermalState β (O * blockForm ε * O.transpose)) =
      -(1 / 2 * ∑ j, ε j * Real.tanh (β * ε j / 2)) := by
  have hh : (O * blockForm ε * O.transpose).transpose = -(O * blockForm ε * O.transpose) :=
    orthogonalCongruence_transpose (blockForm_transpose _)
  rw [energy_eq_energyForm hh (isDensity_thermalState hU hU' hO hOO β).1.1,
    covariance_thermalState hU hU' hO hOO, energyForm_conj_blockForm hOO]
  simp only [mul_neg, Finset.sum_neg_distrib]

end Thermal

/-- `H_0 = 0`. -/
lemma quadHam_zero : quadHam (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) = 0 := by
  simp [quadHam, hamCoeff]

/-- Corollary 4: `Z(0) = 2^n`. -/
theorem partitionFunction_zero :
    partitionFunction (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) = (2 ^ n : ℂ) := by
  unfold partitionFunction
  rw [quadHam_zero, neg_zero, NormedSpace.exp_zero, Matrix.trace_one, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

/-- Corollary 4: `ρ_0 = 2^{-n} 1`, the maximally mixed state. -/
theorem gaussianState_zero :
    gaussianState (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) = ((2 ^ n : ℂ))⁻¹ • 1 := by
  unfold gaussianState
  rw [partitionFunction_zero, quadHam_zero, neg_zero, NormedSpace.exp_zero]

/-- Corollary 4: `Γ(ρ_0) = 0`. -/
theorem covariance_gaussianState_zero :
    covariance (gaussianState (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)) = 0 := by
  have h := covariance_gaussianState (n := n) (U := 1) (O := 1) (ε := 0) (by simp) (by simp)
    conjugatesMajorana_one (by simp)
  rw [blockForm_zero, Matrix.mul_zero, Matrix.zero_mul] at h
  rw [h]
  have : (fun j : Fin n => -Real.tanh ((0 : Fin n → ℝ) j / 2)) = 0 := by
    funext j; simp
  rw [this, blockForm_zero, Matrix.mul_zero, Matrix.zero_mul]

/-! ### Proposition 5: strict admissibility -/

/-- Proposition 5: `Γ` is strictly admissible when `Γᵀ = -Γ` and `1 - Γᵀ Γ` is positive
definite. -/
def IsStrictlyAdmissible (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : Prop :=
  Γ.transpose = -Γ ∧ (1 - Γ.transpose * Γ).PosDef

theorem IsStrictlyAdmissible.isAdmissible {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (h : IsStrictlyAdmissible Γ) : IsAdmissible Γ :=
  ⟨h.1, h.2.posSemidef⟩

lemma abs_lt_one_iff_sq_lt (t : ℝ) : |t| < 1 ↔ t * t < 1 := by
  rw [← abs_mul_abs_self t]
  constructor
  · intro h; nlinarith [abs_nonneg t]
  · intro h; nlinarith [abs_nonneg t]

/-- Proposition 5(c): `D(λ)` is strictly admissible iff every `|λ_j| < 1`. -/
theorem isStrictlyAdmissible_blockForm_iff (lam : Fin n → ℝ) :
    IsStrictlyAdmissible (blockForm lam) ↔ ∀ j, |lam j| < 1 := by
  unfold IsStrictlyAdmissible
  rw [one_sub_transpose_mul_blockForm, Matrix.posDef_diagonal_iff]
  constructor
  · rintro ⟨-, h⟩ j
    have := h (Sum.inl j)
    simp only [blockGap, Sum.elim_inl] at this
    rw [abs_lt_one_iff_sq_lt]; linarith
  · intro h
    refine ⟨blockForm_transpose lam, fun a => ?_⟩
    have key : ∀ j, 0 < 1 - lam j * lam j := fun j => by
      have := (abs_lt_one_iff_sq_lt (lam j)).mp (h j); linarith
    rcases a with j | j <;> simp [blockGap, key]

/-- Proposition 5(c): strict admissibility is preserved by orthogonal congruence. -/
theorem isStrictlyAdmissible_orthogonalCongruence
    {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} (hO : O * O.transpose = 1)
    (hΓ : IsStrictlyAdmissible Γ) : IsStrictlyAdmissible (O * Γ * O.transpose) := by
  refine ⟨orthogonalCongruence_transpose hΓ.1, ?_⟩
  have hOtO := transpose_mul_self_of_mul_transpose hO
  have hcong : 1 - (O * Γ * O.transpose).transpose * (O * Γ * O.transpose) =
      O * (1 - Γ.transpose * Γ) * O.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hO]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul]
  rw [hcong]
  have hinj : Function.Injective O.vecMul := by
    intro x y hxy
    change x ᵥ* O = y ᵥ* O at hxy
    have key : ∀ z : MajoranaIndex n → ℝ, (z ᵥ* O) ᵥ* O.transpose = z := fun z => by
      rw [Matrix.vecMul_vecMul, hO, Matrix.vecMul_one]
    calc x = (x ᵥ* O) ᵥ* O.transpose := (key x).symm
      _ = (y ᵥ* O) ᵥ* O.transpose := by rw [hxy]
      _ = y := key y
  have := hΓ.2.mul_mul_conjTranspose_same hinj
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- Proposition 5(a): the covariance of an exponential state is strictly admissible. -/
theorem isStrictlyAdmissible_covariance_gaussianState
    (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (hh : h.transpose = -h) :
    IsStrictlyAdmissible (covariance (gaussianState h)) := by
  obtain ⟨O, ε, hOO, -, -, hcov⟩ := exists_covariance_gaussianState h hh
  rw [hcov]
  exact isStrictlyAdmissible_orthogonalCongruence hOO
    ((isStrictlyAdmissible_blockForm_iff _).mpr (abs_tanh_half_lt_one ε))

/-- Proposition 5(b): for `n ≥ 1` the covariance of an exponential state is not pure. -/
theorem not_isPure_covariance_gaussianState (hn : 0 < n)
    (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (hh : h.transpose = -h) :
    ¬ IsPure (covariance (gaussianState h)) := by
  intro hpure
  obtain ⟨O, ε, hOO, -, -, hcov⟩ := exists_covariance_gaussianState h hh
  have := abs_eq_one_of_isPure_normalForm hOO hcov hpure ⟨0, hn⟩
  exact absurd this (abs_tanh_half_lt_one ε ⟨0, hn⟩).ne

/-! ### Theorem 6: realization by the exponential family -/

section Realization

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- Theorem 6(a): for `|η_j| < 1`, `h = O D(-2 artanh η) Oᵀ` has `Γ(ρ_h) = O D(η) Oᵀ`. -/
theorem covariance_gaussianState_artanh (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1)
    {η : Fin n → ℝ} (hη : ∀ j, |η j| < 1) :
    covariance (gaussianState (O * blockForm (fun j => -(2 * Real.artanh (η j))) * O.transpose)) =
      O * blockForm η * O.transpose := by
  rw [covariance_gaussianState hU hU' hO hOO]
  congr 3
  funext j
  rw [show -(2 * Real.artanh (η j)) / 2 = -Real.artanh (η j) by ring, Real.tanh_neg, neg_neg]
  exact Real.tanh_artanh (Set.mem_Ioo.mpr (abs_lt.mp (hη j)))

/-- Theorem 6(c): the parameter is unique in a frame. -/
theorem eq_of_covariance_gaussianState_eq (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1)
    {ε ε' : Fin n → ℝ}
    (heq : covariance (gaussianState (O * blockForm ε * O.transpose)) =
      covariance (gaussianState (O * blockForm ε' * O.transpose))) :
    ε = ε' := by
  rw [covariance_gaussianState hU hU' hO hOO, covariance_gaussianState hU hU' hO hOO] at heq
  have hOtO := transpose_mul_self_of_mul_transpose hOO
  have key : ∀ lam : Fin n → ℝ,
      O.transpose * (O * blockForm lam * O.transpose) * O = blockForm lam := fun lam => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O.transpose O, hOtO, Matrix.one_mul, Matrix.mul_one]
  have hb : blockForm (fun j => -Real.tanh (ε j / 2)) =
      blockForm (fun j => -Real.tanh (ε' j / 2)) := by
    rw [← key (fun j => -Real.tanh (ε j / 2)), heq, key]
  funext j
  have hj := congrFun (congrFun hb (Sum.inl j)) (Sum.inr j)
  simp only [blockForm, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq] at hj
  have := Real.tanh_injective (neg_injective hj)
  linarith

end Realization

/-- Theorem 6(b): every strictly admissible matrix is the covariance of an exponential state. -/
theorem exists_gaussianState_covariance_eq (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : IsStrictlyAdmissible Γ) :
    ∃ h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ,
      h.transpose = -h ∧ covariance (gaussianState h) = Γ := by
  obtain ⟨O, η, hOO, hdet, hΓη⟩ := exists_normalForm_special Γ hΓ.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hOO hdet
  have hη : ∀ j, |η j| < 1 := by
    rw [← isStrictlyAdmissible_blockForm_iff, blockForm_eq_of_normalForm hOO hΓη]
    exact isStrictlyAdmissible_orthogonalCongruence (transpose_mul_self_of_mul_transpose hOO) hΓ
  refine ⟨O * blockForm (fun j => -(2 * Real.artanh (η j))) * O.transpose,
    orthogonalCongruence_transpose (blockForm_transpose _), ?_⟩
  rw [covariance_gaussianState_artanh hU hU' hUO hOO hη, hΓη]

end Fermionic
