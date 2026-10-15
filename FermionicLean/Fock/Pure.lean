/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.State

/-! # Purity of the contraction (G4, Package A)

The contraction of two rank-one states is rank one: for `ψ` on `n + m` modes and `φ` on the
last `m` modes, `|ψ⟩⟨ψ| ⋆ |φ⟩⟨φ| = |χ⟩⟨χ|` with `χ_s = ∑_u conj(φ_u) ψ_(s,u)` and
`Z = ‖χ‖²` (`contractRaw_vecMulVec`, `normalization_vecMulVec`). A Gaussian state with
`ρ * ρ = ρ` has a pure covariance (`IsGaussian.isPure_covariance_of_mul_self`): the weights
of an idempotent product mixture are `0` or `1`, which forces every `|λ_j| = 1`. Hence the
contracted state of two Gaussian states with pure covariances is a projection
(`contractState_mul_self_of_isPure`) and `Γ ⋆ β` is pure (`isPure_contractCov_of_isPure`).
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

variable {n m : ℕ}

/-! ### The rank-one contraction -/

/-- The partial inner product `χ_s = ∑_u conj(φ_u) ψ_(s,u)`. -/
noncomputable def partialInner (ψ : FockIndex (n + m) → ℂ) (φ : FockIndex m → ℂ) :
    FockIndex n → ℂ :=
  fun s => ∑ u, star (φ u) * ψ ((fockSplit n m).symm (s, u))

/-- Lemma 1: `|ψ⟩⟨ψ| ⋆ |φ⟩⟨φ| = |χ⟩⟨χ|`. -/
theorem contractRaw_vecMulVec (ψ : FockIndex (n + m) → ℂ) (φ : FockIndex m → ℂ) :
    contractRaw (vecMulVec ψ (star ψ)) (vecMulVec φ (star φ)) =
      vecMulVec (partialInner ψ φ) (star (partialInner ψ φ)) := by
  ext s t
  rw [contractRaw, ptraceE_apply]
  have h1 : ∀ u, (vecMulVec ψ (star ψ) *
      tensor (1 : Matrix (FockIndex n) (FockIndex n) ℂ) (vecMulVec φ (star φ)))
      ((fockSplit n m).symm (s, u)) ((fockSplit n m).symm (t, u)) =
      ψ ((fockSplit n m).symm (s, u)) * star (φ u) * star (partialInner ψ φ t) := by
    intro u
    rw [Matrix.mul_apply, ← Equiv.sum_comp (fockSplit n m).symm, Fintype.sum_prod_type]
    simp only [tensor_apply_symm, vecMulVec_apply, Pi.star_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single t]
    · simp only [ite_true, one_mul, partialInner, star_sum, star_mul', star_star, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u' _ => ?_
      ring
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ t) h
  simp only [h1, vecMulVec_apply, Pi.star_apply, ← Finset.sum_mul]
  congr 1
  simp only [partialInner]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- Lemma 1: `Z = ‖χ‖²`, as `∑_s conj(χ_s) χ_s`. -/
theorem normalization_vecMulVec (ψ : FockIndex (n + m) → ℂ) (φ : FockIndex m → ℂ) :
    normalization (vecMulVec ψ (star ψ)) (vecMulVec φ (star φ)) =
      star (partialInner ψ φ) ⬝ᵥ partialInner ψ φ := by
  rw [← trace_contractRaw, contractRaw_vecMulVec]
  simp [Matrix.trace, vecMulVec_apply, dotProduct, mul_comm]

/-- A conjugated occupation state is rank one: `Uᴴ |s⟩⟨s| U = |ψ⟩⟨ψ|` with `ψ = Uᴴ e_s`. -/
theorem conjTranspose_mul_occupation_mul_eq_vecMulVec (U : Matrix (FockIndex n) (FockIndex n) ℂ)
    (s : FockIndex n) :
    U.conjTranspose * occupation s * U =
      vecMulVec (fun i => star (U s i)) (star fun i => star (U s i)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [occupation, Matrix.mul_single_apply_same]
    simp [vecMulVec_apply, Matrix.conjTranspose_apply]
  · intro b _ hb
    rw [occupation, Matrix.mul_single_apply_of_ne (i := s) (j := s) (a := i) (b := b) (hbj := hb)]
    simp
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- A Gaussian state with pure covariance is `|ψ⟩⟨ψ|` for a vector `ψ`. -/
theorem IsGaussian.exists_vecMulVec_eq_of_isPure {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) (hpure : IsPure (covariance ρ)) :
    ∃ ψ : FockIndex n → ℂ, ρ = vecMulVec ψ (star ψ) := by
  obtain ⟨U, s, -, -, rfl⟩ := hρ.exists_pure_eq_of_isPure hpure
  exact ⟨_, conjTranspose_mul_occupation_mul_eq_vecMulVec U s⟩

/-! ### An idempotent Gaussian state has a pure covariance -/

lemma bernoulli_add (lam : ℝ) : bernoulli lam 0 + bernoulli lam 1 = 1 := by
  simp [bernoulli]; ring

lemma bernoulli_le_one {lam : ℝ} (h : |lam| ≤ 1) (b : Fin 2) : bernoulli lam b ≤ 1 := by
  rw [abs_le] at h
  unfold bernoulli
  split_ifs <;> linarith [h.1, h.2]

lemma bernoulli_lt_one {lam : ℝ} (h : |lam| < 1) (b : Fin 2) : bernoulli lam b < 1 := by
  rw [abs_lt] at h
  unfold bernoulli
  split_ifs <;> linarith [h.1, h.2]

lemma bernoulli_pos {lam : ℝ} (h : |lam| < 1) (b : Fin 2) : 0 < bernoulli lam b := by
  rw [abs_lt] at h
  unfold bernoulli
  split_ifs <;> linarith [h.1, h.2]

/-- The diagonal entry of a product mixture is its weight. -/
lemma productMixture_apply_diag (lam : Fin n → ℝ) (s : FockIndex n) :
    productMixture lam s s = (productWeight lam s : ℂ) := by
  simp [productMixture, occupation, Matrix.sum_apply, Matrix.single_apply]

/-- The diagonal entry of the square of a product mixture is the squared weight. -/
lemma productMixture_mul_self_apply_diag (lam : Fin n → ℝ) (s : FockIndex n) :
    (productMixture lam * productMixture lam) s s = ((productWeight lam s) ^ 2 : ℝ) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [productMixture_apply_diag]; push_cast; ring
  · intro t _ hts
    simp only [productMixture, occupation, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul, mul_ite, mul_zero]
    refine mul_eq_zero.mpr (Or.inl (Finset.sum_eq_zero fun c _ => ?_))
    split_ifs with h
    · exact absurd (h.2.symm.trans h.1) hts
    · rfl
  · intro h; exact absurd (Finset.mem_univ s) h

/-- If an idempotent product mixture has a parameter with `|λ_j| < 1`, some weight lies
strictly between `0` and `1`: contradiction. -/
theorem abs_eq_one_of_productMixture_mul_self {lam : Fin n → ℝ} (hlam : ∀ j, |lam j| ≤ 1)
    (h : productMixture lam * productMixture lam = productMixture lam) (j : Fin n) :
    |lam j| = 1 := by
  by_contra hne
  have hlt : |lam j| < 1 := lt_of_le_of_ne (hlam j) hne
  -- the configuration: a positive-weight bit at every other mode, anything at `j`
  classical
  let s : FockIndex n := fun k => if 0 < bernoulli (lam k) 0 then 0 else 1
  have hpos : ∀ k, 0 < bernoulli (lam k) (s k) := by
    intro k
    change 0 < bernoulli (lam k) (if 0 < bernoulli (lam k) 0 then 0 else 1)
    split_ifs with h0
    · exact h0
    · have := bernoulli_add (lam k)
      have h0' := bernoulli_nonneg (hlam k) (0 : Fin 2)
      have : bernoulli (lam k) 0 = 0 := le_antisymm (not_lt.mp h0) h0'
      linarith
  have hw : (productWeight lam s) ^ 2 = productWeight lam s := by
    have := congrFun (congrFun h s) s
    rw [productMixture_mul_self_apply_diag, productMixture_apply_diag] at this
    exact_mod_cast this
  have hwpos : 0 < productWeight lam s := Finset.prod_pos fun k _ => hpos k
  have hwlt : productWeight lam s < 1 := by
    unfold productWeight
    calc ∏ k, bernoulli (lam k) (s k)
        = bernoulli (lam j) (s j) * ∏ k ∈ Finset.univ.erase j, bernoulli (lam k) (s k) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      _ ≤ bernoulli (lam j) (s j) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (hpos j).le
          exact Finset.prod_le_one₀ (fun k _ => (hpos k).le) fun k _ => bernoulli_le_one (hlam k) _
      _ < 1 := by rw [mul_one]; exact bernoulli_lt_one hlt _
  have : productWeight lam s * (productWeight lam s - 1) = 0 := by nlinarith [hw]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact absurd h0 hwpos.ne'
  · exact absurd (sub_eq_zero.mp h1) hwlt.ne

/-- Theorem 2: an idempotent Gaussian state has a pure covariance. -/
theorem IsGaussian.isPure_covariance_of_mul_self {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) (h : ρ * ρ = ρ) : IsPure (covariance ρ) := by
  obtain ⟨U, O, ε, hU, hU', hUO, hOO, hε, hΓ, hreal⟩ := hρ.exists_realization_eq
  have hmix : productMixture ε * productMixture ε = productMixture ε := by
    have h' : U * ρ * U.conjTranspose = productMixture ε := by
      rw [hreal, realization]
      calc U * (U.conjTranspose * productMixture ε * U) * U.conjTranspose
          = (U * U.conjTranspose) * productMixture ε * (U * U.conjTranspose) := by
            simp only [Matrix.mul_assoc]
        _ = productMixture ε := by rw [hU]; simp
    calc productMixture ε * productMixture ε
        = U * ρ * (U.conjTranspose * U) * ρ * U.conjTranspose := by
          rw [← h']; simp only [Matrix.mul_assoc]
      _ = U * (ρ * ρ) * U.conjTranspose := by rw [hU']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = productMixture ε := by rw [h, h']
  have habs : ∀ j, |ε j| = 1 := abs_eq_one_of_productMixture_mul_self hε hmix
  rw [hΓ]
  exact isPure_orthogonalCongruence hOO ((isPure_blockForm_iff ε).mpr habs)

/-- Theorem 2, both directions: a Gaussian state is idempotent iff its covariance is pure. -/
theorem IsGaussian.mul_self_iff_isPure {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) : ρ * ρ = ρ ↔ IsPure (covariance ρ) :=
  ⟨hρ.isPure_covariance_of_mul_self, hρ.mul_self_of_isPure⟩

/-! ### The contraction of pure Gaussian states -/

variable {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
  {σ : Matrix (FockIndex m) (FockIndex m) ℂ}

/-- Theorem 3: the contracted state of two Gaussian states with pure covariances is a
projection. -/
theorem contractState_mul_self_of_isPure (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hρp : IsPure (covariance ρ)) (hσp : IsPure (covariance σ))
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det) :
    contractState ρ σ * contractState ρ σ = contractState ρ σ := by
  have hZ : normalization ρ σ ≠ 0 := (normalization_pos hρ hσ hinv).ne'
  obtain ⟨ψ, hψ⟩ := hρ.exists_vecMulVec_eq_of_isPure hρp
  obtain ⟨φ, hφ⟩ := hσ.exists_vecMulVec_eq_of_isPure hσp
  have hraw := contractRaw_vecMulVec ψ φ
  have hnorm := normalization_vecMulVec ψ φ
  rw [← hψ, ← hφ] at hraw hnorm
  simp only [contractState, hraw, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    ← hnorm, smul_smul, vecMulVec_smul]
  rw [inv_mul_cancel₀ hZ, mul_one]

/-- Corollary 4: the contraction of pure covariances is pure. -/
theorem isPure_contractCov_of_isPure {Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ}
    {β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ} (hΓ : IsPure Γ) (hβ : IsPure β)
    (hinv : IsUnit (1 - blockE Γ * β).det) : IsPure (contractCov Γ β) := by
  obtain ⟨ρ, hρ, hρΓ⟩ := exists_isGaussian_covariance_eq Γ hΓ.isAdmissible
  obtain ⟨σ, hσ, hσβ⟩ := exists_isGaussian_covariance_eq β hβ.isAdmissible
  subst hρΓ; subst hσβ
  have h := isGaussian_contractState' hρ hσ hinv
  rw [← h.2]
  exact h.1.isPure_covariance_of_mul_self (contractState_mul_self_of_isPure hρ hσ hΓ hβ hinv)

end Fermionic
