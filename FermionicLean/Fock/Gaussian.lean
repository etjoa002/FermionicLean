/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Wick
import FermionicLean.Fock.Parity
import FermionicLean.Fock.Evolution
import FermionicLean.Fock.Monomial

/-! # The Gaussian families

The mixed product states `ρ_λ`, `λ ∈ [-1,1]^n`, are Gaussian (G2, Theorem 9), hence so are
their conjugates by implementing unitaries: the realization states of F6, the exponential
states of G1 and the pure states `Uᴴ |s⟩⟨s| U` (Corollary 10). Since the Majorana monomials
form a basis (`Fock/Monomial.lean`), the moments determine the state: two Gaussian states with
the same covariance are equal (Theorem 14), so every Gaussian state is the realization state
of its covariance, a Gaussian state with pure covariance is pure, and the exponential state
with a given covariance is unique (Corollary 15).

The proof feeds the recursion criterion `isGaussian_of_recursion` with two facts about
`ρ_λ`: its odd moments vanish (parity), and for each mode `j` the single identity
`(c_x - iλ_j c_y) ρ_λ = ρ_λ (c_x + iλ_j c_y)` (and its `y` counterpart), valid for every
`λ_j ∈ [-1,1]`. The identity comes from the weight relation
`p_j(s_j) w(flip_j s) = p_j(1 - s_j) w(s)`; at `λ_j = -1` it reads `a_j ρ = ρ a_j^*` (both zero),
at `|λ_j| < 1` it is the KMS row of the proposal, so no case split is needed.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### Lemma 6: parity and the odd moments -/

lemma parity_mul_lincomb_mul_parity (v : MajoranaIndex n → ℂ) :
    parity * lincomb v * parity = -lincomb v := by
  simp only [lincomb, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    parity_mul_majorana_mul_parity, smul_neg, Finset.sum_neg_distrib]

lemma parity_mul_productMixture (lam : Fin n → ℝ) :
    parity * productMixture lam = productMixture lam * parity := by
  rw [productMixture_eq_diagonal, parity, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext s
  ring

/-- Lemma 6: the odd moments of a product mixture vanish. -/
theorem momentList_productMixture_eq_zero_of_odd (lam : Fin n → ℝ)
    (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    momentList (productMixture lam) l = 0 := by
  unfold momentList
  refine trace_mul_list_prod_eq_zero_of_odd _ (parity_mul_productMixture lam) _ ?_
    (by simpa using hl)
  intro X hX
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hX
  exact parity_mul_lincomb_mul_parity v

/-! ### The mode relation -/

lemma bernoulli_eq_bitSign (lam : ℝ) (b : Fin 2) :
    ((bernoulli lam b : ℝ) : ℂ) = (1 - (lam : ℂ) * bitSign b) / 2 := by
  fin_cases b <;> simp [bernoulli, bitSign]

/-- The weight relation `p_j(s_j) w(flip_j s) = p_j(1 - s_j) w(s)`. -/
lemma productWeight_flip (lam : Fin n → ℝ) (j : Fin n) (s : FockIndex n) :
    bernoulli (lam j) (s j) * productWeight lam (flip j s) =
      bernoulli (lam j) (flip j s j) * productWeight lam s := by
  unfold productWeight
  rw [← Finset.mul_prod_erase Finset.univ (fun k => bernoulli (lam k) (flip j s k))
      (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => bernoulli (lam k) (s k)) (Finset.mem_univ j)]
  have h : ∏ k ∈ Finset.univ.erase j, bernoulli (lam k) (flip j s k) =
      ∏ k ∈ Finset.univ.erase j, bernoulli (lam k) (s k) :=
    Finset.prod_congr rfl fun k hk => by rw [flip_apply_ne (Finset.ne_of_mem_erase hk)]
  rw [h]
  ring

/-- `Z_j c_{x_j} = i c_{y_j}`. -/
lemma pauliZ_mul_majorana_x (j : Fin n) :
    pauliZ j * majorana (Sum.inl j) = Complex.I • majorana (Sum.inr j) := by
  have hZX : pauliZ j * pauliX j = -(pauliX j * pauliZ j) := by rw [pauliX_mul_pauliZ, neg_neg]
  have h : pauliZ j * majorana (Sum.inl j) = -(majorana (Sum.inl j) * pauliZ j) := by
    change pauliZ j * (jwString j * pauliX j) = -(jwString j * pauliX j * pauliZ j)
    rw [← Matrix.mul_assoc, pauliZ_mul_jwString_comm, Matrix.mul_assoc, hZX, Matrix.mul_neg,
      Matrix.mul_assoc]
  rw [h, majorana_x_mul_pauliZ, neg_smul, neg_neg]

/-- `Z_j c_{y_j} = -i c_{x_j}`. -/
lemma pauliZ_mul_majorana_y (j : Fin n) :
    pauliZ j * majorana (Sum.inr j) = (-Complex.I) • majorana (Sum.inl j) := by
  have hZX : pauliZ j * pauliX j = -(pauliX j * pauliZ j) := by rw [pauliX_mul_pauliZ, neg_neg]
  have h : pauliZ j * majorana (Sum.inr j) = -(majorana (Sum.inr j) * pauliZ j) := by
    change pauliZ j * (Complex.I • (jwString j * pauliX j * pauliZ j)) =
      -(Complex.I • (jwString j * pauliX j * pauliZ j) * pauliZ j)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pauliZ_mul_jwString_comm,
      Matrix.mul_assoc (jwString j), hZX, Matrix.mul_neg, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
  rw [h, majorana_y_mul_pauliZ, neg_smul]

lemma one_add_smul_pauliZ (j : Fin n) (c : ℂ) :
    (1 : Matrix (FockIndex n) (FockIndex n) ℂ) + c • pauliZ j =
      Matrix.diagonal fun s => 1 + c * bitSign (s j) := by
  ext s t
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, pauliZ, Matrix.diagonal_apply,
    smul_eq_mul]
  split_ifs <;> simp

/-- The mode relation for `c_{x_j}`: `(c_x - iλ_j c_y) ρ_λ = ρ_λ (c_x + iλ_j c_y)`. -/
theorem majorana_x_relation_productMixture (lam : Fin n → ℝ) (j : Fin n) :
    (majorana (Sum.inl j) - (Complex.I * lam j) • majorana (Sum.inr j)) * productMixture lam =
      productMixture lam *
        (majorana (Sum.inl j) + (Complex.I * lam j) • majorana (Sum.inr j)) := by
  have h1 : majorana (Sum.inl j) - (Complex.I * lam j) • majorana (Sum.inr j) =
      (1 + (-(lam j : ℂ)) • pauliZ j) * majorana (Sum.inl j) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, pauliZ_mul_majorana_x, smul_smul,
      sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have h2 : majorana (Sum.inl j) + (Complex.I * lam j) • majorana (Sum.inr j) =
      (1 + (lam j : ℂ) • pauliZ j) * majorana (Sum.inl j) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, pauliZ_mul_majorana_x, smul_smul,
      mul_comm]
  rw [h1, h2, one_add_smul_pauliZ, one_add_smul_pauliZ, productMixture_eq_diagonal,
    majorana_eq_diagonal_mul]
  simp only [Matrix.mul_assoc]
  rw [pauliX_mul_diagonal]
  simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext s
  simp only [mode, Sum.elim_inl, id]
  have hw : ((bernoulli (lam j) (s j) : ℝ) : ℂ) *
        ((productWeight lam (Fermionic.flip j s) : ℝ) : ℂ) =
      ((bernoulli (lam j) (Fermionic.flip j s j) : ℝ) : ℂ) *
        ((productWeight lam s : ℝ) : ℂ) := by
    exact_mod_cast productWeight_flip lam j s
  rw [bernoulli_eq_bitSign, bernoulli_eq_bitSign, bitSign_flip_self] at hw
  linear_combination ((2 : ℂ) * majoranaSign (Sum.inl j) s) * hw

/-- The mode relation for `c_{y_j}`: `(c_y + iλ_j c_x) ρ_λ = ρ_λ (c_y - iλ_j c_x)`. -/
theorem majorana_y_relation_productMixture (lam : Fin n → ℝ) (j : Fin n) :
    (majorana (Sum.inr j) - (-(Complex.I * lam j)) • majorana (Sum.inl j)) * productMixture lam =
      productMixture lam *
        (majorana (Sum.inr j) + (-(Complex.I * lam j)) • majorana (Sum.inl j)) := by
  have h1 : majorana (Sum.inr j) - (-(Complex.I * lam j)) • majorana (Sum.inl j) =
      (1 + (-(lam j : ℂ)) • pauliZ j) * majorana (Sum.inr j) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, pauliZ_mul_majorana_y, smul_smul,
      sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have h2 : majorana (Sum.inr j) + (-(Complex.I * lam j)) • majorana (Sum.inl j) =
      (1 + (lam j : ℂ) • pauliZ j) * majorana (Sum.inr j) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, pauliZ_mul_majorana_y, smul_smul]
    congr 2
    ring
  rw [h1, h2, one_add_smul_pauliZ, one_add_smul_pauliZ, productMixture_eq_diagonal,
    majorana_eq_diagonal_mul]
  simp only [Matrix.mul_assoc]
  rw [pauliX_mul_diagonal]
  simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext s
  simp only [mode, Sum.elim_inr, id]
  have hw : ((bernoulli (lam j) (s j) : ℝ) : ℂ) *
        ((productWeight lam (Fermionic.flip j s) : ℝ) : ℂ) =
      ((bernoulli (lam j) (Fermionic.flip j s j) : ℝ) : ℂ) *
        ((productWeight lam s : ℝ) : ℂ) := by
    exact_mod_cast productWeight_flip lam j s
  rw [bernoulli_eq_bitSign, bernoulli_eq_bitSign, bitSign_flip_self] at hw
  linear_combination ((2 : ℂ) * majoranaSign (Sum.inr j) s) * hw

/-! ### The two-point matrix of a product mixture -/

lemma twoPoint_productMixture_mulVec_x (lam : Fin n → ℝ) (w : MajoranaIndex n → ℂ)
    (j : Fin n) :
    (twoPoint (productMixture lam) *ᵥ w) (Sum.inl j) =
      w (Sum.inl j) - Complex.I * lam j * w (Sum.inr j) := by
  simp [twoPoint, covariance_productMixture, blockForm, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
    apply_ite Complex.ofReal, ite_mul, mul_ite]
  ring

lemma twoPoint_productMixture_mulVec_y (lam : Fin n → ℝ) (w : MajoranaIndex n → ℂ)
    (j : Fin n) :
    (twoPoint (productMixture lam) *ᵥ w) (Sum.inr j) =
      w (Sum.inr j) - (-(Complex.I * lam j)) * w (Sum.inl j) := by
  simp [twoPoint, covariance_productMixture, blockForm, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
    apply_ite Complex.ofReal, ite_mul, mul_ite]
  ring

/-! ### Theorem 9 -/

lemma lincomb_single (a : MajoranaIndex n) : lincomb (Pi.single a 1) = majorana a := by
  simp [lincomb, Pi.single_apply, Finset.sum_ite_eq']

/-- The trace form of Lemma 4's second identity for a single Majorana factor and an odd list:
`Tr (ρ X c_a) = ∑ᵢ (-1)^i 2 (wᵢ)_a Tr (ρ X_î) - Tr (ρ c_a X)`. -/
lemma trace_mul_prod_mul_majorana_of_odd (ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (a : MajoranaIndex n) (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    (ρ * ((l.map lincomb).prod * majorana a)).trace =
      ∑ i : Fin l.length, (-1) ^ (i : ℕ) * (2 * l[(i : ℕ)] a) * momentList ρ (l.eraseIdx i) -
        (ρ * (majorana a * (l.map lincomb).prod)).trace := by
  have h := congrArg (fun M => (ρ * M).trace) (prod_mul_lincomb (Pi.single a 1) l)
  simp only [lincomb_single, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, single_dotProduct, one_mul,
    hl.neg_one_pow, neg_one_mul] at h
  rw [h, sub_eq_add_neg]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_one_pow_sub_one_sub i.isLt, hl.neg_one_pow, momentList]
  ring

/-- The recursion (ii) of Lemma 5 for a label `a` from a mode relation
`(c_a - μ c_b) ρ = ρ (c_a + μ c_b)` and the matching row `(G w)_a = w_a - μ w_b`. -/
theorem recursion_of_relation {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    {a b : MajoranaIndex n} {μ : ℂ}
    (hrel : (majorana a - μ • majorana b) * ρ = ρ * (majorana a + μ • majorana b))
    (hG : ∀ w : MajoranaIndex n → ℂ, (twoPoint ρ *ᵥ w) a = w a - μ * w b)
    (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    (ρ * (majorana a * (l.map lincomb).prod)).trace =
      ∑ i : Fin l.length,
        (-1) ^ (i : ℕ) * (twoPoint ρ *ᵥ l[(i : ℕ)]) a * momentList ρ (l.eraseIdx i) := by
  set X := (l.map lincomb).prod with hX
  have key := congrArg (fun M => (M * X).trace) hrel
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc] at key
  rw [Matrix.trace_mul_comm (majorana a), Matrix.trace_mul_comm (majorana b),
    Matrix.mul_assoc, Matrix.mul_assoc] at key
  have hBa := trace_mul_prod_mul_majorana_of_odd ρ a l hl
  have hBb := trace_mul_prod_mul_majorana_of_odd ρ b l hl
  rw [← hX] at hBa hBb
  rw [hBa, hBb] at key
  simp only [hG]
  have hs : ∑ i : Fin l.length,
      (-1) ^ (i : ℕ) * (l[(i : ℕ)] a - μ * l[(i : ℕ)] b) * momentList ρ (l.eraseIdx i) =
      (∑ i : Fin l.length,
          (-1) ^ (i : ℕ) * (2 * l[(i : ℕ)] a) * momentList ρ (l.eraseIdx i) -
        μ * ∑ i : Fin l.length, (-1) ^ (i : ℕ) * (2 * l[(i : ℕ)] b) *
          momentList ρ (l.eraseIdx i)) / 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hs]
  linear_combination (-1 / 2 : ℂ) * key

/-- Theorem 9: every mixed product state `ρ_λ`, `λ ∈ [-1,1]^n`, is Gaussian. -/
theorem isGaussian_productMixture {lam : Fin n → ℝ} (h : ∀ j, |lam j| ≤ 1) :
    IsGaussian (productMixture lam) := by
  refine isGaussian_of_recursion (isDensity_productMixture h)
    (momentList_productMixture_eq_zero_of_odd lam) fun a l hl => ?_
  rcases a with j | j
  · exact recursion_of_relation (majorana_x_relation_productMixture lam j)
      (fun w => twoPoint_productMixture_mulVec_x lam w j) l hl
  · exact recursion_of_relation (majorana_y_relation_productMixture lam j)
      (fun w => twoPoint_productMixture_mulVec_y lam w j) l hl

/-! ### Corollary 10: the Gaussian families -/

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
variable {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- Corollary 10(a): the realization states of F6 are Gaussian. -/
theorem isGaussian_realization (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hUO : ConjugatesMajorana U O) {ε : Fin n → ℝ} (hε : ∀ j, |ε j| ≤ 1) :
    IsGaussian (realization U ε) :=
  isGaussian_conj hU hU' hUO (isGaussian_productMixture hε)

/-- Corollary 10(b): every exponential state is Gaussian. -/
theorem isGaussian_gaussianState (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) : IsGaussian (gaussianState h) := by
  obtain ⟨O, ε, U, hOO, -, hOε, hU, hU', hUO⟩ := exists_normalForm_unitary h hh
  rw [hOε, gaussianState_conj hU hU' hUO hOO]
  exact isGaussian_realization hU hU' hUO (abs_tanh_half_le_one ε)

/-- Every thermal state is Gaussian. -/
theorem isGaussian_thermalState (β : ℝ) (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : h.transpose = -h) : IsGaussian (thermalState β h) :=
  isGaussian_gaussianState _ (by rw [Matrix.transpose_smul, hh, smul_neg])

/-- An occupation state is the product mixture with `λ_j = ±1`. -/
lemma occupation_eq_productMixture (s : FockIndex n) :
    occupation s = productMixture fun j => if s j = 1 then 1 else -1 := by
  rw [productMixture_of_abs_eq_one (fun j => by split_ifs <;> simp)]
  congr 1
  funext j
  generalize s j = b
  fin_cases b <;> norm_num

/-- Corollary 10(c): every occupation state is Gaussian. -/
theorem isGaussian_occupation (s : FockIndex n) : IsGaussian (occupation s) := by
  rw [occupation_eq_productMixture]
  exact isGaussian_productMixture fun j => by split_ifs <;> simp

/-- Corollary 10(c): every pure state `Uᴴ |s⟩⟨s| U` with `U` implementing an orthogonal `O`
is Gaussian. -/
theorem isGaussian_pure (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hUO : ConjugatesMajorana U O) (s : FockIndex n) :
    IsGaussian (U.conjTranspose * occupation s * U) :=
  isGaussian_conj hU hU' hUO (isGaussian_occupation s)

/-! ### Theorem 14: a Gaussian state is determined by its covariance -/

/-- A monomial is the product of the linear combinations of the unit vectors of its labels. -/
lemma monomial_eq_prod_lincomb (S : Finset (MajoranaIndex n)) :
    monomial S =
      (((labels S).map fun a => (Pi.single a 1 : MajoranaIndex n → ℂ)).map lincomb).prod := by
  unfold monomial
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun a _ => (lincomb_single a).symm

/-- Theorem 14: two Gaussian states with the same covariance are equal. -/
theorem IsGaussian.eq_of_covariance_eq {ρ σ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) (hσ : IsGaussian σ) (h : covariance ρ = covariance σ) : ρ = σ := by
  refine eq_of_trace_mul_monomial_eq fun S => ?_
  rw [monomial_eq_prod_lincomb]
  change momentList ρ _ = momentList σ _
  rw [hρ.2, hσ.2, twoPoint, twoPoint, h]

/-! ### Corollary 15: the converse -/

/-- Corollary 15(a): every Gaussian state is the realization state of its covariance. -/
theorem IsGaussian.exists_realization_eq {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) :
    ∃ (U : Matrix (FockIndex n) (FockIndex n) ℂ)
      (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧
      ConjugatesMajorana U O ∧ O * O.transpose = 1 ∧ (∀ j, |ε j| ≤ 1) ∧
      covariance ρ = O * blockForm ε * O.transpose ∧ ρ = realization U ε := by
  have hadm := hρ.1.isAdmissible_covariance
  obtain ⟨O, ε, hOO, hdet, hΓ⟩ := exists_normalForm_special (covariance ρ) hadm.1
  obtain ⟨U, hU, hU', hUO⟩ := exists_unitary_conjugatesMajorana O hOO hdet
  have hε := abs_le_one_of_isAdmissible_normalForm hOO hΓ hadm
  have hres := isDensity_realization_and_covariance hU hU' hUO hOO hΓ hadm
  exact ⟨U, O, ε, hU, hU', hUO, hOO, hε, hΓ,
    hρ.eq_of_covariance_eq (isGaussian_realization hU hU' hUO hε) hres.2.symm⟩

/-- Corollary 15(b): a Gaussian state with pure covariance is a pure state `Uᴴ |s⟩⟨s| U`. -/
theorem IsGaussian.exists_pure_eq_of_isPure {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) (hpure : IsPure (covariance ρ)) :
    ∃ (U : Matrix (FockIndex n) (FockIndex n) ℂ) (s : FockIndex n),
      U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧
      ρ = U.conjTranspose * occupation s * U := by
  obtain ⟨U, O, ε, hU, hU', hUO, hOO, -, hΓ, hreal⟩ := hρ.exists_realization_eq
  have hε := abs_eq_one_of_isPure_normalForm hOO hΓ hpure
  refine ⟨U, fun j => if ε j = 1 then 1 else 0, hU, hU', ?_⟩
  rw [hreal, realization, productMixture_of_abs_eq_one hε]

/-- Corollary 15(b): a Gaussian state with pure covariance is idempotent. -/
theorem IsGaussian.mul_self_of_isPure {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) (hpure : IsPure (covariance ρ)) : ρ * ρ = ρ := by
  obtain ⟨U, s, hU, hU', rfl⟩ := hρ.exists_pure_eq_of_isPure hpure
  have hocc : occupation s * occupation s = occupation s := by
    simp [occupation, Matrix.single_mul_single_same]
  calc U.conjTranspose * occupation s * U * (U.conjTranspose * occupation s * U)
      = U.conjTranspose * (occupation s * (U * U.conjTranspose) * occupation s) * U := by
        simp only [Matrix.mul_assoc]
    _ = U.conjTranspose * occupation s * U := by
        rw [hU, Matrix.mul_one, hocc, Matrix.mul_assoc]

/-- Corollary 15(c): a Gaussian state with strictly admissible covariance is an exponential
state. -/
theorem IsGaussian.exists_gaussianState_eq_of_isStrictlyAdmissible
    {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsGaussian ρ)
    (hΓ : IsStrictlyAdmissible (covariance ρ)) :
    ∃ h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ,
      h.transpose = -h ∧ ρ = gaussianState h := by
  obtain ⟨h, hh, hcov⟩ := exists_gaussianState_covariance_eq (covariance ρ) hΓ
  exact ⟨h, hh, hρ.eq_of_covariance_eq (isGaussian_gaussianState h hh) hcov.symm⟩

/-- Corollary 15(c): the exponential state with a given covariance is unique (the deferral of
G1, Theorem 6). -/
theorem gaussianState_eq_of_covariance_eq {h h' : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hh : h.transpose = -h) (hh' : h'.transpose = -h')
    (hcov : covariance (gaussianState h) = covariance (gaussianState h')) :
    gaussianState h = gaussianState h' :=
  (isGaussian_gaussianState h hh).eq_of_covariance_eq (isGaussian_gaussianState h' hh') hcov

end Fermionic
