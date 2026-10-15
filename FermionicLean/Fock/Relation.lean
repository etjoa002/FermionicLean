/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Gaussian

/-! # The relation of a Gaussian state

A Gaussian state `ρ` with two-point matrix `G = 1 - iΓ(ρ)` satisfies
`(Gᵀ v · c) ρ = ρ (G v · c)` for every vector `v` (G3, Theorem 5): for a product mixture this
is the mode relation of G2, and the general case follows by transport. Conversely, a matrix `τ`
whose odd moments vanish and which satisfies the relation for a matrix `G` with `G + Gᵀ = 2`
has moments `Tr τ · W_G` (G3, Theorem 6); a density operator satisfying the relation with its own
two-point matrix is Gaussian. Gaussian states are even: `P ρ P = ρ`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### Linearity of `lincomb` -/

lemma lincomb_add (v w : MajoranaIndex n → ℂ) : lincomb (v + w) = lincomb v + lincomb w := by
  simp [lincomb, add_smul, Finset.sum_add_distrib]

lemma lincomb_smul (c : ℂ) (v : MajoranaIndex n → ℂ) :
    lincomb (c • v) = c • lincomb v := by
  simp [lincomb, smul_smul, Finset.smul_sum]

lemma lincomb_sum {ι : Type*} (s : Finset ι) (v : ι → MajoranaIndex n → ℂ) :
    lincomb (∑ i ∈ s, v i) = ∑ i ∈ s, lincomb (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lincomb]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, lincomb_add, ih]

/-! ### Theorem 6: the relation criterion -/

/-- G2's `isGaussian_of_recursion` for an arbitrary matrix: the recursion (ii) with a matrix `G`
and vanishing odd moments give `momentList τ l = Tr τ · W_G l`. -/
theorem momentList_eq_trace_mul_wick_of_recursion (τ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ)
    (hodd : ∀ l : List (MajoranaIndex n → ℂ), Odd l.length → momentList τ l = 0)
    (hrec : ∀ (a : MajoranaIndex n) (l : List (MajoranaIndex n → ℂ)), Odd l.length →
      (τ * (majorana a * (l.map lincomb).prod)).trace =
        ∑ i : Fin l.length,
          (-1) ^ (i : ℕ) * (G *ᵥ l[(i : ℕ)]) a * momentList τ (l.eraseIdx i))
    (l : List (MajoranaIndex n → ℂ)) : momentList τ l = τ.trace * wick G l := by
  suffices h : ∀ k, ∀ l : List (MajoranaIndex n → ℂ), l.length ≤ k →
      momentList τ l = τ.trace * wick G l from h l.length l le_rfl
  intro k
  induction k with
  | zero =>
    intro l hl
    have h0 : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst h0
    simp [momentList]
  | succ k ih =>
    intro l hl
    rcases Nat.even_or_odd l.length with he | ho
    · match l with
      | [] => simp [momentList]
      | v :: l =>
        have hlo : Odd l.length := by
          rw [List.length_cons, Nat.even_add_one] at he
          exact Nat.not_even_iff_odd.mp he
        rw [wick_cons_eq_sum, momentList_cons_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hrec a l hlo]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ih (l.eraseIdx i)
          ((List.length_eraseIdx_le l i).trans (by simpa using hl))]
        ring
    · rw [hodd l ho, wick_odd l ho, mul_zero]

/-- The trace form of the moving lemma for a linear combination and an odd list:
`Tr (τ X (u·c)) = ∑ᵢ (-1)^i 2 (uᵀ wᵢ) Tr (τ X_î) - Tr (τ (u·c) X)`. -/
lemma trace_mul_prod_mul_lincomb_of_odd (τ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (u : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    (τ * ((l.map lincomb).prod * lincomb u)).trace =
      ∑ i : Fin l.length,
        (-1) ^ (i : ℕ) * (2 * (u ⬝ᵥ l[(i : ℕ)])) * momentList τ (l.eraseIdx i) -
        (τ * (lincomb u * (l.map lincomb).prod)).trace := by
  have h := congrArg (fun M => (τ * M).trace) (prod_mul_lincomb u l)
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, hl.neg_one_pow, neg_one_mul] at h
  rw [h, sub_eq_add_neg]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_one_pow_sub_one_sub i.isLt, hl.neg_one_pow, momentList]
  ring

/-- The relation for every vector, from the relation for the unit vectors. -/
lemma relation_of_forall_single {τ : Matrix (FockIndex n) (FockIndex n) ℂ}
    {G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ}
    (h : ∀ a : MajoranaIndex n, lincomb (G.transpose *ᵥ Pi.single a 1) * τ =
      τ * lincomb (G *ᵥ Pi.single a 1)) (v : MajoranaIndex n → ℂ) :
    lincomb (G.transpose *ᵥ v) * τ = τ * lincomb (G *ᵥ v) := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : MajoranaIndex n → ℂ) := by
    ext b; simp [Pi.single_apply]
  rw [hv, Matrix.mulVec_sum, Matrix.mulVec_sum, lincomb_sum, lincomb_sum, Matrix.sum_mul,
    Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, lincomb_smul, lincomb_smul, Matrix.smul_mul,
    Matrix.mul_smul, h a]

/-- Theorem 6, the recursion: the relation `(Gᵀ v·c) τ = τ (G v·c)` for all `v`, with
`G + Gᵀ = 2`, gives the recursion (ii) of G2's Lemma 5 for every label. -/
theorem recursion_of_relation' {τ : Matrix (FockIndex n) (FockIndex n) ℂ}
    {G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ} (hG : G + G.transpose = (2 : ℂ) • 1)
    (hrel : ∀ v : MajoranaIndex n → ℂ,
      lincomb (G.transpose *ᵥ v) * τ = τ * lincomb (G *ᵥ v))
    (a : MajoranaIndex n) (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    (τ * (majorana a * (l.map lincomb).prod)).trace =
      ∑ i : Fin l.length,
        (-1) ^ (i : ℕ) * (G *ᵥ l[(i : ℕ)]) a * momentList τ (l.eraseIdx i) := by
  set X := (l.map lincomb).prod with hX
  set e : MajoranaIndex n → ℂ := Pi.single a 1 with he
  -- the relation traced against X
  have key : (τ * (lincomb (G *ᵥ e) * X)).trace =
      (τ * (X * lincomb (G.transpose *ᵥ e))).trace := by
    rw [← Matrix.mul_assoc, ← hrel e, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [trace_mul_prod_mul_lincomb_of_odd τ _ l hl, ← hX] at key
  -- linearity: lincomb (G e) + lincomb (Gᵀ e) = 2 • majorana a
  have hsum : lincomb (G *ᵥ e) + lincomb (G.transpose *ᵥ e) = (2 : ℂ) • majorana a := by
    rw [← lincomb_add, ← Matrix.add_mulVec, hG, he, ← lincomb_single a, ← lincomb_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdot : ∀ w : MajoranaIndex n → ℂ, (G.transpose *ᵥ e) ⬝ᵥ w = (G *ᵥ w) a := by
    intro w
    rw [he, Matrix.mulVec_single_one]
    rfl
  have h2 : (τ * ((lincomb (G *ᵥ e) + lincomb (G.transpose *ᵥ e)) * X)).trace =
      2 * (τ * (majorana a * X)).trace := by
    rw [hsum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, key] at h2
  simp only [hdot] at h2
  have h3 : ∑ i : Fin l.length, (-1) ^ (i : ℕ) * (2 * (G *ᵥ l[(i : ℕ)]) a) *
      momentList τ (l.eraseIdx i) =
      2 * ∑ i : Fin l.length,
        (-1) ^ (i : ℕ) * (G *ᵥ l[(i : ℕ)]) a * momentList τ (l.eraseIdx i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h3] at h2
  linear_combination (-1 / 2 : ℂ) * h2

/-- Theorem 6: a matrix with vanishing odd moments satisfying the relation with a matrix `G`,
`G + Gᵀ = 2`, has moments `Tr τ · W_G`. -/
theorem momentList_eq_trace_mul_wick_of_relation {τ : Matrix (FockIndex n) (FockIndex n) ℂ}
    {G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ} (hG : G + G.transpose = (2 : ℂ) • 1)
    (hodd : ∀ l : List (MajoranaIndex n → ℂ), Odd l.length → momentList τ l = 0)
    (hrel : ∀ v : MajoranaIndex n → ℂ,
      lincomb (G.transpose *ᵥ v) * τ = τ * lincomb (G *ᵥ v))
    (l : List (MajoranaIndex n → ℂ)) : momentList τ l = τ.trace * wick G l :=
  momentList_eq_trace_mul_wick_of_recursion τ G hodd
    (fun a l hl => recursion_of_relation' hG hrel a l hl) l

lemma twoPoint_add_transpose (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    twoPoint ρ + (twoPoint ρ).transpose = (2 : ℂ) • 1 := by
  ext a b
  have h := congrFun (congrFun (covariance_transpose ρ) a) b
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp only [Matrix.add_apply, Matrix.transpose_apply, twoPoint_apply, h, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  push_cast
  by_cases hab : a = b
  · subst hab; simp; norm_num
  · simp [hab, Ne.symm hab]

/-- Theorem 6, the criterion: a density operator with vanishing odd moments satisfying the
relation with its own two-point matrix is Gaussian. -/
theorem isGaussian_of_relation {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsDensity ρ)
    (hodd : ∀ l : List (MajoranaIndex n → ℂ), Odd l.length → momentList ρ l = 0)
    (hrel : ∀ v : MajoranaIndex n → ℂ,
      lincomb ((twoPoint ρ).transpose *ᵥ v) * ρ = ρ * lincomb (twoPoint ρ *ᵥ v)) :
    IsGaussian ρ :=
  ⟨hρ, fun l => by
    rw [momentList_eq_trace_mul_wick_of_relation (twoPoint_add_transpose ρ) hodd hrel l, hρ.2,
      one_mul]⟩

/-! ### Theorem 5: every Gaussian state satisfies the relation -/

/-- The relation for a product mixture, from the mode relations of G2. -/
theorem relation_productMixture (lam : Fin n → ℝ) (v : MajoranaIndex n → ℂ) :
    lincomb ((twoPoint (productMixture lam)).transpose *ᵥ v) * productMixture lam =
      productMixture lam * lincomb (twoPoint (productMixture lam) *ᵥ v) := by
  refine relation_of_forall_single (fun a => ?_) v
  have hcol : ∀ b c : MajoranaIndex n, twoPoint (productMixture lam) b c =
      (if b = c then 1 else 0) - Complex.I * (blockForm lam b c : ℂ) := by
    intro b c
    rw [twoPoint_apply, covariance_productMixture]
  have hlin : ∀ (w : MajoranaIndex n → ℂ), lincomb w = ∑ b, w b • majorana b :=
    fun w => rfl
  rcases a with j | j
  · have h1 : lincomb (twoPoint (productMixture lam) *ᵥ Pi.single (Sum.inl j) 1) =
        majorana (Sum.inl j) + (Complex.I * lam j) • majorana (Sum.inr j) := by
      rw [hlin, Matrix.mulVec_single_one, Fintype.sum_sum_type]
      simp [Matrix.col, hcol, blockForm, Matrix.fromBlocks, Matrix.diagonal_apply,
        apply_ite Complex.ofReal, mul_ite, ite_smul, Finset.sum_ite_eq', Finset.sum_neg_distrib,
        neg_smul]
    have h2 : lincomb ((twoPoint (productMixture lam)).transpose *ᵥ Pi.single (Sum.inl j) 1) =
        majorana (Sum.inl j) - (Complex.I * lam j) • majorana (Sum.inr j) := by
      rw [hlin, Matrix.mulVec_single_one, Fintype.sum_sum_type]
      simp [Matrix.col, Matrix.transpose_apply, hcol, blockForm, Matrix.fromBlocks,
        Matrix.diagonal_apply, apply_ite Complex.ofReal, mul_ite, ite_smul, Finset.sum_ite_eq,
        Finset.sum_neg_distrib, neg_smul, sub_eq_add_neg]
    rw [h1, h2]
    exact majorana_x_relation_productMixture lam j
  · have h1 : lincomb (twoPoint (productMixture lam) *ᵥ Pi.single (Sum.inr j) 1) =
        majorana (Sum.inr j) + (-(Complex.I * lam j)) • majorana (Sum.inl j) := by
      rw [hlin, Matrix.mulVec_single_one, Fintype.sum_sum_type]
      simp [Matrix.col, hcol, blockForm, Matrix.fromBlocks, Matrix.diagonal_apply,
        apply_ite Complex.ofReal, mul_ite, ite_smul, Finset.sum_ite_eq', Finset.sum_neg_distrib,
        neg_smul, sub_eq_add_neg]
      abel
    have h2 : lincomb ((twoPoint (productMixture lam)).transpose *ᵥ Pi.single (Sum.inr j) 1) =
        majorana (Sum.inr j) - (-(Complex.I * lam j)) • majorana (Sum.inl j) := by
      rw [hlin, Matrix.mulVec_single_one, Fintype.sum_sum_type]
      simp [Matrix.col, Matrix.transpose_apply, hcol, blockForm, Matrix.fromBlocks,
        Matrix.diagonal_apply, apply_ite Complex.ofReal, mul_ite, ite_smul, Finset.sum_ite_eq,
        Finset.sum_neg_distrib, neg_smul, sub_eq_add_neg]
      abel
    rw [h1, h2]
    exact majorana_y_relation_productMixture lam j

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
variable {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- `Uᴴ (w·c) U = (O w)·c` for `U` implementing `O`. -/
lemma conjTranspose_mul_lincomb_mul (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (w : MajoranaIndex n → ℂ) :
    U.conjTranspose * lincomb w * U = lincomb (O.map Complex.ofReal *ᵥ w) := by
  have hOO : O * O.transpose = 1 := orthogonal_of_conjugatesMajorana hU' hO
  have hOc : (O.map Complex.ofReal).transpose * O.map Complex.ofReal = 1 := by
    have h := mul_eq_one_comm.mp hOO
    have this : (O.transpose * O).map Complex.ofRealHom =
        (1 : Matrix _ _ ℝ).map Complex.ofRealHom := by
      rw [h]
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (by simp) (by simp)] at this
    exact this
  have h := conj_lincomb (U := U) (O := O) hO (O.map Complex.ofReal *ᵥ w)
  rw [Matrix.mulVec_mulVec, hOc, Matrix.one_mulVec] at h
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul, Matrix.mul_assoc, hU',
    Matrix.mul_one]

/-- Theorem 5: every Gaussian state satisfies `(Gᵀ v·c) ρ = ρ (G v·c)`, `G = 1 - iΓ(ρ)`. -/
theorem IsGaussian.relation {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsGaussian ρ)
    (v : MajoranaIndex n → ℂ) :
    lincomb ((twoPoint ρ).transpose *ᵥ v) * ρ = ρ * lincomb (twoPoint ρ *ᵥ v) := by
  obtain ⟨U, O, ε, hU, hU', hUO, hOO, hε, -, hreal⟩ := hρ.exists_realization_eq
  set Oc := O.map Complex.ofReal with hOcdef
  have hOc : Oc * Oc.transpose = 1 := by
    have this : (O * O.transpose).map Complex.ofRealHom =
        (1 : Matrix _ _ ℝ).map Complex.ofRealHom := by
      rw [hOO]
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (by simp) (by simp)] at this
    exact this
  have hOc' : Oc.transpose * Oc = 1 := mul_eq_one_comm.mp hOc
  have hG : twoPoint ρ = Oc * twoPoint (productMixture ε) * Oc.transpose := by
    rw [hreal, realization, twoPoint_conj hU hU' hUO (isDensity_productMixture hε)]
  have hGT : (twoPoint ρ).transpose =
      Oc * (twoPoint (productMixture ε)).transpose * Oc.transpose := by
    rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  -- move to the product mixture
  have hL : lincomb ((twoPoint ρ).transpose *ᵥ v) =
      U.conjTranspose *
        lincomb ((twoPoint (productMixture ε)).transpose *ᵥ (Oc.transpose *ᵥ v)) * U := by
    rw [conjTranspose_mul_lincomb_mul hU' hUO, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hGT]
  have hR : lincomb (twoPoint ρ *ᵥ v) =
      U.conjTranspose * lincomb (twoPoint (productMixture ε) *ᵥ (Oc.transpose *ᵥ v)) * U := by
    rw [conjTranspose_mul_lincomb_mul hU' hUO, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG]
  rw [hL, hR, hreal, realization]
  have hrel := relation_productMixture ε (Oc.transpose *ᵥ v)
  set Gε := twoPoint (productMixture ε) with hGε
  calc U.conjTranspose * lincomb (Gε.transpose *ᵥ (Oc.transpose *ᵥ v)) *
        U * (U.conjTranspose * productMixture ε * U)
      = U.conjTranspose * (lincomb (Gε.transpose *ᵥ (Oc.transpose *ᵥ v)) *
          productMixture ε) * U := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U U.conjTranspose, hU, Matrix.one_mul]
    _ = U.conjTranspose * (productMixture ε *
          lincomb (Gε *ᵥ (Oc.transpose *ᵥ v))) * U := by rw [hrel]
    _ = U.conjTranspose * productMixture ε * U *
          (U.conjTranspose * lincomb (Gε *ᵥ (Oc.transpose *ᵥ v)) * U) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U U.conjTranspose, hU, Matrix.one_mul]

/-- Gaussian states are even: `P ρ P = ρ`. -/
theorem IsGaussian.parity_conj {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsGaussian ρ) :
    parity * ρ * parity = ρ := by
  refine eq_of_trace_mul_monomial_eq fun S => ?_
  have hP : parity * monomial S * parity = ((-1 : ℤ) ^ S.card) • monomial S := by
    have hl : ∀ X ∈ (labels S).map majorana, parity * X * parity = -X := by
      intro X hX
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hX
      exact parity_mul_majorana_mul_parity a
    unfold monomial
    rw [parity_mul_list_prod_mul_parity _ hl, List.length_map, length_labels]
  have h1 : (parity * ρ * parity * monomial S).trace =
      (ρ * (parity * monomial S * parity)).trace := by
    rw [Matrix.mul_assoc (parity * ρ) parity, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [h1, hP, Matrix.mul_smul, Matrix.trace_smul]
  rcases Nat.even_or_odd S.card with he | ho
  · rw [he.neg_one_pow, one_smul]
  · have h0 : (ρ * monomial S).trace = 0 := by
      rw [monomial_eq_prod_lincomb]
      change momentList ρ _ = 0
      rw [hρ.2, wick_odd]
      simpa [length_labels] using ho
    rw [h0, smul_zero]

end Fermionic
