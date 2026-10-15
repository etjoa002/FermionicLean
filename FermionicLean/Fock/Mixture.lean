/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.BlockForm

/-! # Mixed product states

For `λ ∈ [-1, 1]^n` the mixed product state `ρ_λ = ∑_s (∏_j p_j(s_j)) |s⟩⟨s|` with
`p_j(0) = (1 - λ_j)/2`, `p_j(1) = (1 + λ_j)/2` is a density operator whose covariance is
the block form `D(λ)`; when every `|λ_j| = 1` it is the occupation state with `s_j = 1`
iff `λ_j = 1`.
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

variable {n : ℕ}

/-- The Bernoulli weight of bit `b` for parameter `λ`: `(1 - λ)/2` for `b = 0`,
`(1 + λ)/2` for `b = 1`. -/
noncomputable def bernoulli (lam : ℝ) (b : Fin 2) : ℝ :=
  if b = 0 then (1 - lam) / 2 else (1 + lam) / 2

/-- The product weight of a configuration. -/
noncomputable def productWeight (lam : Fin n → ℝ) (s : FockIndex n) : ℝ :=
  ∏ j, bernoulli (lam j) (s j)

/-- Definition 10: the mixed product state `ρ_λ = ∑_s (∏_j p_j(s_j)) |s⟩⟨s|`. -/
noncomputable def productMixture (lam : Fin n → ℝ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  ∑ s, ((productWeight lam s : ℝ) : ℂ) • occupation s

lemma bernoulli_nonneg {lam : ℝ} (h : |lam| ≤ 1) (b : Fin 2) : 0 ≤ bernoulli lam b := by
  rw [abs_le] at h
  unfold bernoulli
  split_ifs <;> linarith [h.1, h.2]

lemma sum_bernoulli (lam : ℝ) : bernoulli lam 0 + bernoulli lam 1 = 1 := by
  simp [bernoulli]; ring

lemma sum_bernoulli_mul_occupationSignEntry (lam : ℝ) :
    bernoulli lam 0 * occupationSignEntry 0 + bernoulli lam 1 * occupationSignEntry 1 = lam := by
  simp [bernoulli, occupationSignEntry]; ring

lemma productWeight_nonneg {lam : Fin n → ℝ} (h : ∀ j, |lam j| ≤ 1) (s : FockIndex n) :
    0 ≤ productWeight lam s :=
  Finset.prod_nonneg fun j _ => bernoulli_nonneg (h j) (s j)

/-- The weights sum to one: `∑_s ∏_j p_j(s_j) = ∏_j (p_j(0) + p_j(1)) = 1`. -/
lemma sum_productWeight (lam : Fin n → ℝ) : ∑ s, productWeight lam s = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum fun j b => bernoulli (lam j) b]
  simp [Fin.sum_univ_two, sum_bernoulli]

/-- The `j`-th moment `∑_s p(s) σ_j(s) = λ_j`. -/
lemma sum_productWeight_mul_occupationSignEntry (lam : Fin n → ℝ) (j : Fin n) :
    ∑ s, productWeight lam s * occupationSignEntry (s j) = lam j := by
  have key : ∀ s : FockIndex n, productWeight lam s * occupationSignEntry (s j) =
      ∏ j', bernoulli (lam j') (s j') * (if j' = j then occupationSignEntry (s j') else 1) := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp [productWeight]
  simp only [key]
  rw [← Fintype.prod_sum
    fun j' b => bernoulli (lam j') b * (if j' = j then occupationSignEntry b else 1)]
  rw [Finset.prod_eq_single j]
  · simp [Fin.sum_univ_two, sum_bernoulli_mul_occupationSignEntry]
  · intro j' _ hj'
    simp [Fin.sum_univ_two, hj', sum_bernoulli]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma trace_occupation (s : FockIndex n) : (occupation s).trace = 1 := by
  simp [occupation, Matrix.trace_single_eq_same]

/-- The covariance is additive and real-homogeneous (finite sums). -/
theorem covariance_sum {ι : Type*} (t : Finset ι) (ρ : ι → Matrix (FockIndex n) (FockIndex n) ℂ)
    (c : ι → ℝ) :
    covariance (∑ i ∈ t, ((c i : ℝ) : ℂ) • ρ i) = ∑ i ∈ t, c i • covariance (ρ i) := by
  ext a b
  simp only [covariance, Matrix.sum_apply, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, Finset.mul_sum, Complex.re_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- The block form is linear in its parameter (finite sums). -/
lemma blockForm_sum {ι : Type*} (t : Finset ι) (c : ι → ℝ) (ε : ι → Fin n → ℝ) :
    ∑ i ∈ t, c i • blockForm (ε i) = blockForm (fun j => ∑ i ∈ t, c i * ε i j) := by
  ext (a | a) (b | b) <;>
    simp only [blockForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.diagonal_apply] <;>
    by_cases hab : a = b <;> simp [hab]

/-- Theorem 11: `ρ_λ` is a density operator when every `|λ_j| ≤ 1`. -/
theorem isDensity_productMixture {lam : Fin n → ℝ} (h : ∀ j, |lam j| ≤ 1) :
    IsDensity (productMixture lam) := by
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_, ?_⟩
  · simp [productMixture, Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      occupation_conjTranspose]
  · simp only [productMixture, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
      dotProduct_smul, smul_eq_mul]
    have hterm : ∀ s : FockIndex n,
        0 ≤ (productWeight lam s : ℝ) * (star x ⬝ᵥ (occupation s *ᵥ x)).re ∧
          (productWeight lam s : ℝ) * (star x ⬝ᵥ (occupation s *ᵥ x)).im = 0 := by
      intro s
      have hq := Complex.nonneg_iff.mp ((isDensity_occupation s).1.dotProduct_mulVec_nonneg x)
      exact ⟨mul_nonneg (productWeight_nonneg h s) hq.1, by rw [← hq.2, mul_zero]⟩
    rw [Complex.nonneg_iff, Complex.re_sum, Complex.im_sum]
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    exact ⟨Finset.sum_nonneg fun s _ => (hterm s).1,
      (Finset.sum_eq_zero fun s _ => (hterm s).2).symm⟩
  · simp only [productMixture, Matrix.trace_sum, Matrix.trace_smul, trace_occupation, smul_eq_mul,
      mul_one]
    rw [← Complex.ofReal_sum, sum_productWeight, Complex.ofReal_one]

/-- Theorem 11: `Γ(ρ_λ) = D(λ)`. -/
theorem covariance_productMixture (lam : Fin n → ℝ) :
    covariance (productMixture lam) = blockForm lam := by
  unfold productMixture
  rw [covariance_sum]
  simp only [covariance_occupation_eq_blockForm]
  rw [blockForm_sum]
  congr 1
  funext j
  exact sum_productWeight_mul_occupationSignEntry lam j

/-- When `|λ_j| = 1` the weight is concentrated on the bit `s_j = 1` iff `λ_j = 1`. -/
lemma bernoulli_of_abs_eq_one {lam : ℝ} (h : |lam| = 1) (b : Fin 2) :
    bernoulli lam b = if b = (if lam = 1 then 1 else 0) then 1 else 0 := by
  rcases (abs_eq zero_le_one).mp h with h1 | h1
  · subst h1
    fin_cases b <;> simp [bernoulli]
  · subst h1
    fin_cases b <;> norm_num [bernoulli]

/-- Theorem 11: when every `|λ_j| = 1`, `ρ_λ` is the occupation state with `s_j = 1`
iff `λ_j = 1`. -/
theorem productMixture_of_abs_eq_one {lam : Fin n → ℝ} (h : ∀ j, |lam j| = 1) :
    productMixture lam = occupation (fun j => if lam j = 1 then 1 else 0) := by
  set s₀ : FockIndex n := fun j => if lam j = 1 then 1 else 0 with hs₀
  have hw : ∀ s : FockIndex n, productWeight lam s = if s = s₀ then 1 else 0 := by
    intro s
    unfold productWeight
    simp only [fun j => bernoulli_of_abs_eq_one (h j) (s j)]
    rw [Finset.prod_boole]
    congr 1
    simp only [Finset.mem_univ, true_implies, funext_iff]
    rfl
  have hterm : ∀ s : FockIndex n,
      ((productWeight lam s : ℝ) : ℂ) • occupation s = if s = s₀ then occupation s else 0 := by
    intro s
    rw [hw]
    split_ifs <;> simp
  unfold productMixture
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  simp

end Fermionic
