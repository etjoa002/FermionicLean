/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.PartialTrace
import FermionicLean.Fock.Relation
import FermionicLean.Contraction.RowSolve
import FermionicLean.Contraction.BlockDet
import Mathlib.Analysis.Matrix.Order

/-! # The contraction of Gaussian states

For a state `ρ` on `n + m` modes and a state `σ` on the last `m` modes, the contraction
`ρ ⋆ σ = Tr_E (ρ (1 ⊗ σ))` is a matrix on the first `n` modes with normalization
`Z = Tr (ρ (1 ⊗ σ))`. When `ρ` and `σ` are Gaussian with covariances `Γ` and `β` and
`1 - Dβ` is invertible (`D` the eliminated block of `Γ`), the moments of `ρ ⋆ σ` are `Z`
times the Wick expansion of `1 - i (Γ ⋆ β)`, with `Γ ⋆ β = A + Bβ(1 - Dβ)⁻¹C` the
star-product contraction of F3 (G3, Theorem 9); if `Z ≠ 0`, the contracted state
`Z⁻¹ ρ ⋆ σ` is Gaussian with covariance `Γ ⋆ β` (Corollary 10). The proof reduces,
through the relations of `ρ` and `σ` (`Fock/Relation.lean`) and the moving lemma of G2, to the
row-vector system solved in `Contraction/RowSolve.lean`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Fermionic

variable {n m : ℕ}

/-! ### Definitions -/

/-- The unnormalized contraction `Tr_E (ρ (1 ⊗ σ))`. -/
noncomputable def contractRaw (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (σ : Matrix (FockIndex m) (FockIndex m) ℂ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  ptraceE (ρ * tensor 1 σ)

/-- The normalization `Z(ρ, σ) = Tr (ρ (1 ⊗ σ))`. -/
noncomputable def normalization (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (σ : Matrix (FockIndex m) (FockIndex m) ℂ) : ℂ :=
  (ρ * tensor 1 σ).trace

/-- The contracted state `Z⁻¹ ρ ⋆ σ`. -/
noncomputable def contractState (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (σ : Matrix (FockIndex m) (FockIndex m) ℂ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  (normalization ρ σ)⁻¹ • contractRaw ρ σ

lemma trace_contractRaw (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (σ : Matrix (FockIndex m) (FockIndex m) ℂ) :
    (contractRaw ρ σ).trace = normalization ρ σ :=
  trace_ptraceE _

/-- The blocks of a matrix on the labels of `n + m` modes: retained `A`, mixed `B`, `C`,
eliminated `D`. -/
def blockR (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ := Γ.submatrix embedR embedR

def blockRE (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ) :
    Matrix (MajoranaIndex n) (MajoranaIndex m) ℝ := Γ.submatrix embedR embedE

def blockER (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ) :
    Matrix (MajoranaIndex m) (MajoranaIndex n) ℝ := Γ.submatrix embedE embedR

def blockE (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ) :
    Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ := Γ.submatrix embedE embedE

/-- The star-product contraction `Γ ⋆ β = A + Bβ(1 - Dβ)⁻¹C` in the blocks of `Γ`. -/
noncomputable def contractCov (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ)
    (β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  blockR Γ + blockRE Γ * β * (1 - blockE Γ * β)⁻¹ * blockER Γ

/-- `contractCov` is F3's `contract` of the matrix reindexed by the label split. -/
lemma contractCov_eq_contract (Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ)
    (β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ) :
    contractCov Γ β =
      contract (Γ.submatrix (labelSplit n m).symm (labelSplit n m).symm) β := rfl

lemma blockRE_transpose {Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ}
    (hΓ : Γ.transpose = -Γ) : (blockRE Γ).transpose = -blockER Γ := by
  ext a b
  have h := congrFun (congrFun hΓ (embedE a)) (embedR b)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [blockRE, blockER, h]

lemma blockE_transpose {Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ}
    (hΓ : Γ.transpose = -Γ) : (blockE Γ).transpose = -blockE Γ := by
  ext a b
  have h := congrFun (congrFun hΓ (embedE a)) (embedE b)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [blockE, h]

lemma blockR_transpose {Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ}
    (hΓ : Γ.transpose = -Γ) : (blockR Γ).transpose = -blockR Γ := by
  ext a b
  have h := congrFun (congrFun hΓ (embedR a)) (embedR b)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [blockR, h]

/-- The contraction of antisymmetric matrices is antisymmetric. -/
lemma contractCov_transpose {Γ : Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ}
    {β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ} (hΓ : Γ.transpose = -Γ)
    (hβ : β.transpose = -β) (hinv : IsUnit (1 - blockE Γ * β).det) :
    (contractCov Γ β).transpose = -contractCov Γ β := by
  have hinv' : IsUnit (1 - β * blockE Γ).det := by rwa [Matrix.det_one_sub_mul_comm]
  have hT : (1 - blockE Γ * β).transpose = 1 - β * blockE Γ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hβ, blockE_transpose hΓ,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hCT : (blockER Γ).transpose = -blockRE Γ := by
    rw [show blockER Γ = -(blockRE Γ).transpose from
      (neg_eq_iff_eq_neg.mpr (blockRE_transpose hΓ)).symm, Matrix.transpose_neg,
      Matrix.transpose_transpose]
  unfold contractCov
  rw [Matrix.transpose_add, blockR_transpose hΓ, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hT, hβ, hCT, blockRE_transpose hΓ]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [← Matrix.mul_assoc (1 - β * blockE Γ)⁻¹, inv_one_sub_mul_mul_eq _ _ hinv, neg_add]
  simp only [Matrix.mul_assoc]

/-! ### Moments of the contraction as moments on the full space -/

section moments

variable (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
  (σ : Matrix (FockIndex m) (FockIndex m) ℂ)

lemma momentList_contractRaw_eq (l : List (MajoranaIndex n → ℂ)) :
    momentList (contractRaw ρ σ) l = momentList (ρ * tensor 1 σ) (l.map extendR) := by
  rw [momentList, momentList, contractRaw, trace_ptraceE_mul, prod_lincomb_extendR]

lemma trace_contractRaw_mul_majorana_mul (a : MajoranaIndex n)
    (l : List (MajoranaIndex n → ℂ)) :
    (contractRaw ρ σ * (majorana a * (l.map lincomb).prod)).trace =
      (ρ * tensor 1 σ * (majorana (embedR a) * ((l.map extendR).map lincomb).prod)).trace := by
  rw [contractRaw, trace_ptraceE_mul, prod_lincomb_extendR, majorana_embedR, tensor_mul_tensor,
    Matrix.mul_one]

end moments

/-! ### Positivity and evenness -/

/-- Lemma 8: the contraction of positive semidefinite matrices is positive semidefinite. -/
theorem contractRaw_posSemidef {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (contractRaw ρ σ).PosSemidef := by
  classical
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    (A := Matrix (FockIndex m) (FockIndex m) ℂ) hσ.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hσ.nonneg)
  have hXH : X.conjTranspose = X := hX.star_eq
  have h1 : contractRaw ρ σ = ptraceE ((tensor 1 X).conjTranspose * ρ * tensor 1 X) := by
    rw [contractRaw, ← hXX, ← Matrix.mul_one (1 : Matrix (FockIndex n) (FockIndex n) ℂ),
      ← tensor_mul_tensor, Matrix.mul_one, ← Matrix.mul_assoc, ptraceE_mul_one_tensor_comm,
      tensor_conjTranspose, Matrix.conjTranspose_one, hXH, Matrix.mul_assoc]
  rw [h1]
  exact ptraceE_posSemidef _ (hρ.conjTranspose_mul_mul_same _)

/-- The normalization of two density operators is real and nonnegative. -/
theorem normalization_nonneg {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    0 ≤ normalization ρ σ := by
  rw [← trace_contractRaw]
  exact (contractRaw_posSemidef hρ hσ).trace_nonneg

/-- The contracted state is a density operator when `Z ≠ 0`. -/
theorem isDensity_contractState {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hZ : normalization ρ σ ≠ 0) : IsDensity (contractState ρ σ) := by
  have hpos : (contractRaw ρ σ).PosSemidef := contractRaw_posSemidef hρ hσ
  have hZr : 0 ≤ normalization ρ σ := normalization_nonneg hρ hσ
  refine ⟨?_, ?_⟩
  · rw [contractState]
    exact hpos.smul (inv_nonneg.mpr hZr)
  · rw [contractState, Matrix.trace_smul, trace_contractRaw, smul_eq_mul, inv_mul_cancel₀ hZ]

/-- Parity commutes with `ρ (1 ⊗ σ)` for even `ρ` and `σ`. -/
lemma parity_mul_mul_tensor_one {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : parity * ρ * parity = ρ)
    (hσ : parity * σ * parity = σ) :
    parity * (ρ * tensor 1 σ) = ρ * tensor 1 σ * parity := by
  have hσ' : parity * tensor (n := n) 1 σ * parity = tensor 1 σ := by
    rw [parity_split, tensor_mul_tensor, tensor_mul_tensor, Matrix.mul_one,
      parity_mul_self, hσ]
  have key : parity * (ρ * tensor 1 σ) * parity = ρ * tensor 1 σ := by
    calc parity * (ρ * tensor 1 σ) * parity
        = (parity * ρ * parity) * (parity * tensor 1 σ * parity) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc parity parity, parity_mul_self, Matrix.one_mul]
      _ = ρ * tensor 1 σ := by rw [hρ, hσ']
  calc parity * (ρ * tensor 1 σ) = parity * (ρ * tensor 1 σ) * (parity * parity) := by
        rw [parity_mul_self, Matrix.mul_one]
    _ = ρ * tensor 1 σ * parity := by rw [← Matrix.mul_assoc, key]

/-- Lemma 8: the odd moments of the contraction vanish. -/
theorem momentList_contractRaw_eq_zero_of_odd
    {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : parity * ρ * parity = ρ)
    (hσ : parity * σ * parity = σ) (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) :
    momentList (contractRaw ρ σ) l = 0 := by
  rw [momentList_contractRaw_eq, momentList]
  refine trace_mul_list_prod_eq_zero_of_odd _ (parity_mul_mul_tensor_one hρ hσ) _ ?_ ?_
  · intro X hX
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hX
    exact parity_mul_lincomb_mul_parity v
  · simpa using hl

/-! ### Theorem 9: the recursion for the contraction -/

section recursion

variable {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
  {σ : Matrix (FockIndex m) (FockIndex m) ℂ}

lemma extendR_single (a : MajoranaIndex n) :
    extendR (m := m) (Pi.single a 1) = Pi.single (embedR a) 1 := by
  funext c
  obtain ⟨x, rfl⟩ := (labelSplit n m).symm.surjective c
  rcases x with b | b
  · change (Sum.elim (Pi.single a 1) (0 : MajoranaIndex m → ℂ) ∘ labelSplit n m) (embedR b) =
      (Pi.single (embedR a) 1 : MajoranaIndex (n + m) → ℂ) (embedR b)
    simp [labelSplit_embedR, Pi.single_apply, embedR_injective.eq_iff]
  · change (Sum.elim (Pi.single a 1) (0 : MajoranaIndex m → ℂ) ∘ labelSplit n m) (embedE b) =
      (Pi.single (embedR a) 1 : MajoranaIndex (n + m) → ℂ) (embedE b)
    have : embedE (n := n) b ≠ embedR a := by
      intro h
      have := congrArg (labelSplit n m) h
      simp at this
    simp [labelSplit_embedE, this]

lemma extendE_single (e : MajoranaIndex m) :
    extendE (n := n) (Pi.single e 1) = Pi.single (embedE e) 1 := by
  funext c
  obtain ⟨x, rfl⟩ := (labelSplit n m).symm.surjective c
  rcases x with b | b
  · change (Sum.elim (0 : MajoranaIndex n → ℂ) (Pi.single e 1) ∘ labelSplit n m) (embedR b) =
      (Pi.single (embedE e) 1 : MajoranaIndex (n + m) → ℂ) (embedR b)
    have : embedR (m := m) b ≠ embedE e := by
      intro h
      have := congrArg (labelSplit n m) h
      simp at this
    simp [labelSplit_embedR, this]
  · change (Sum.elim (0 : MajoranaIndex n → ℂ) (Pi.single e 1) ∘ labelSplit n m) (embedE b) =
      (Pi.single (embedE e) 1 : MajoranaIndex (n + m) → ℂ) (embedE b)
    simp [labelSplit_embedE, Pi.single_apply, embedE_injective.eq_iff]

/-- The blocks of the two-point matrix in terms of the blocks of the covariance. -/
lemma twoPoint_submatrix_RR (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    (twoPoint ρ).submatrix (embedR (m := m)) embedR =
      1 - Complex.I • (blockR (covariance ρ)).map Complex.ofReal := by
  ext a b
  simp [twoPoint_apply, blockR, embedR_injective.eq_iff, Matrix.one_apply]

lemma twoPoint_submatrix_EE (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    (twoPoint ρ).submatrix (embedE (n := n)) embedE =
      1 - Complex.I • (blockE (covariance ρ)).map Complex.ofReal := by
  ext a b
  simp [twoPoint_apply, blockE, embedE_injective.eq_iff, Matrix.one_apply]

lemma embedR_ne_embedE (a : MajoranaIndex n) (e : MajoranaIndex m) : embedR a ≠ embedE e := by
  intro h
  have := congrArg (labelSplit n m) h
  simp at this

lemma twoPoint_submatrix_RE (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    (twoPoint ρ).submatrix (embedR (m := m)) embedE =
      (-Complex.I) • (blockRE (covariance ρ)).map Complex.ofReal := by
  ext a b
  simp [twoPoint_apply, blockRE, embedR_ne_embedE]

lemma twoPoint_submatrix_ER (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    (twoPoint ρ).submatrix (embedE (n := n)) embedR =
      (-Complex.I) • (blockER (covariance ρ)).map Complex.ofReal := by
  ext a b
  simp [twoPoint_apply, blockER, (embedR_ne_embedE b a).symm]

lemma dotProduct_extendR (w : MajoranaIndex (n + m) → ℂ) (u : MajoranaIndex n → ℂ) :
    w ⬝ᵥ extendR u = (w ∘ embedR) ⬝ᵥ u := by
  simp only [dotProduct]
  rw [sum_labelSplit fun c => w c * extendR u c]
  simp [extendR_embedR, extendR_embedE, Function.comp]

/-- The complexification of the inverse `(1 - Dβ)⁻¹`. -/
lemma map_inv_one_sub_mul (D β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ)
    (h : IsUnit (1 - D * β).det) :
    ((1 - D * β)⁻¹).map Complex.ofReal =
      (1 - D.map Complex.ofReal * β.map Complex.ofReal)⁻¹ := by
  have h1 : (1 - D * β) * (1 - D * β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : ((1 - D * β) * (1 - D * β)⁻¹).map Complex.ofRealHom =
      (1 : Matrix _ _ ℝ).map Complex.ofRealHom := by rw [h1]
  rw [Matrix.map_mul, Matrix.map_one _ (by simp) (by simp), Matrix.map_sub _ (by simp),
    Matrix.map_one _ (by simp) (by simp), Matrix.map_mul] at h2
  exact (Matrix.inv_eq_right_inv h2).symm

/-- A linear functional of the form `v ↦ Tr (M (v·c) X)` decomposes along the split. -/
lemma trace_mul_lincomb_mul_split (M X : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (v : MajoranaIndex (n + m) → ℂ) :
    (M * (lincomb v * X)).trace =
      (fun a => (M * (majorana (embedR a) * X)).trace) ⬝ᵥ (v ∘ embedR) +
      (fun e => (M * (majorana (embedE e) * X)).trace) ⬝ᵥ (v ∘ embedE) := by
  simp only [lincomb, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, dotProduct, Function.comp]
  rw [sum_labelSplit fun c => v c * (M * (majorana c * X)).trace]
  simp only [mul_comm]

/-- Theorem 9, the recursion (ii) for the contraction with the matrix
`G̃ = 1 - i (Γ ⋆ β)`. -/
theorem recursion_contractRaw (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det)
    (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) (a : MajoranaIndex n) :
    (contractRaw ρ σ * (majorana a * (l.map lincomb).prod)).trace =
      ∑ i : Fin l.length,
        (-1) ^ (i : ℕ) *
          ((1 - Complex.I • (contractCov (covariance ρ) (covariance σ)).map Complex.ofReal) *ᵥ
            l[(i : ℕ)]) a *
          momentList (contractRaw ρ σ) (l.eraseIdx i) := by
  classical
  -- notation
  set ω := ρ * tensor 1 σ with hω
  set L := l.map (extendR (m := m)) with hL
  set X := (L.map lincomb).prod with hX
  have hLlen : L.length = l.length := by simp [hL]
  have hLodd : Odd L.length := by rwa [hLlen]
  set G := twoPoint ρ with hG
  set Gs := twoPoint σ with hGs
  -- the real blocks and their complexifications
  set Γ := covariance ρ with hΓ
  set β := covariance σ with hβ
  set Bc := (blockRE Γ).map Complex.ofReal with hBc
  set Cc := (blockER Γ).map Complex.ofReal with hCc
  set Dc := (blockE Γ).map Complex.ofReal with hDc
  set βc := β.map Complex.ofReal with hβc
  set Ac := (blockR Γ).map Complex.ofReal with hAc
  have hΓT : Γ.transpose = -Γ := covariance_transpose ρ
  have hβT : β.transpose = -β := covariance_transpose σ
  -- the three functionals as row vectors
  set αR : MajoranaIndex n → ℂ := fun a => (ω * (majorana (embedR a) * X)).trace with hαR
  set αE : MajoranaIndex m → ℂ := fun e => (ω * (majorana (embedE e) * X)).trace with hαE
  set bE : MajoranaIndex m → ℂ :=
    fun e => (ρ * (majorana (embedE e) * (tensor 1 σ * X))).trace with hbE
  set p : Fin L.length → ℂ := fun i => momentList ω (L.eraseIdx i) with hp
  set y : MajoranaIndex n → ℂ :=
    fun a => ∑ i : Fin l.length,
      (-1) ^ (i : ℕ) * momentList (contractRaw ρ σ) (l.eraseIdx i) * l[(i : ℕ)] a with hy
  -- p i = the moments of the contraction
  have hpi : ∀ i : Fin l.length, momentList (contractRaw ρ σ) (l.eraseIdx i) =
      p ⟨i, by rw [hLlen]; exact i.isLt⟩ := by
    intro i
    change momentList (contractRaw ρ σ) (l.eraseIdx i) =
      momentList ω ((List.map extendR l).eraseIdx i)
    rw [List.eraseIdx_map, momentList_contractRaw_eq]
  -- the functional α and b on full vectors
  have hαfun : ∀ v : MajoranaIndex (n + m) → ℂ, (ω * (lincomb v * X)).trace =
      αR ⬝ᵥ (v ∘ embedR) + αE ⬝ᵥ (v ∘ embedE) :=
    fun v => trace_mul_lincomb_mul_split ω X v
  have hbfun : ∀ v : MajoranaIndex (n + m) → ℂ, (ρ * (lincomb v * (tensor 1 σ * X))).trace =
      αR ⬝ᵥ (v ∘ embedR) + bE ⬝ᵥ (v ∘ embedE) := by
    intro v
    rw [trace_mul_lincomb_mul_split ρ (tensor 1 σ * X) v]
    congr 1
    -- (E1): a retained Majorana commutes with 1 ⊗ σ
    refine congrArg (fun f => f ⬝ᵥ (v ∘ embedR)) (funext fun a => ?_)
    change (ρ * (majorana (embedR a) * (tensor 1 σ * X))).trace =
      (ρ * tensor 1 σ * (majorana (embedR a) * X)).trace
    rw [majorana_embedR, ← Matrix.mul_assoc (tensor _ 1), tensor_one_mul_tensor_one_comm]
    simp only [Matrix.mul_assoc]
  -- (E2): the relation of σ, lifted
  have hE2 : ∀ u : MajoranaIndex m → ℂ,
      (ρ * (lincomb (extendE (Gs.transpose *ᵥ u)) * (tensor 1 σ * X))).trace =
        (ω * (lincomb (extendE (Gs *ᵥ u)) * X)).trace := by
    intro u
    rw [hω, lincomb_extendE, lincomb_extendE]
    have h1 : tensor (parity (n := n)) (lincomb (Gs.transpose *ᵥ u)) * tensor 1 σ =
        tensor 1 σ * tensor parity (lincomb (Gs *ᵥ u)) := by
      rw [tensor_mul_tensor, tensor_mul_tensor, Matrix.mul_one, Matrix.one_mul, hσ.relation]
    rw [← Matrix.mul_assoc (tensor parity _), h1]
    simp only [Matrix.mul_assoc]
  -- (E3): the relation of ρ and the moving lemma
  have hE3 : ∀ v : MajoranaIndex (n + m) → ℂ,
      (ρ * (lincomb (G *ᵥ v) * (tensor 1 σ * X))).trace =
        ∑ i : Fin L.length,
          (-1) ^ (i : ℕ) * (2 * ((G.transpose *ᵥ v) ⬝ᵥ L[(i : ℕ)])) * p i -
          (ω * (lincomb (G.transpose *ᵥ v) * X)).trace := by
    intro v
    have hcomm : (ρ * (lincomb (G *ᵥ v) * (tensor 1 σ * X))).trace =
        (ω * (X * lincomb (G.transpose *ᵥ v))).trace := by
      rw [← Matrix.mul_assoc, ← hρ.relation v, Matrix.mul_assoc, Matrix.trace_mul_comm, hω]
      simp only [Matrix.mul_assoc]
      rw [← hG]
    rw [hcomm, hX, trace_mul_prod_mul_lincomb_of_odd ω _ L hLodd]
  -- conversion of the sums over `L` to sums over `l`
  have hRconv : ∀ w : MajoranaIndex (n + m) → ℂ,
      ∑ i : Fin L.length, (-1) ^ (i : ℕ) * (2 * (w ⬝ᵥ L[(i : ℕ)])) * p i =
        2 * ((w ∘ embedR) ⬝ᵥ y) := by
    intro w
    rw [Fintype.sum_equiv (finCongr hLlen) _ (fun i : Fin l.length =>
      (-1) ^ (i : ℕ) * (2 * ((w ∘ embedR) ⬝ᵥ l[(i : ℕ)])) *
        momentList (contractRaw ρ σ) (l.eraseIdx i)) (fun i => ?_)]
    · simp only [hy, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    · have hLi : L[(i : ℕ)] = extendR l[((finCongr hLlen) i : ℕ)] := by
        simp [hL, List.getElem_map]
      rw [hLi, dotProduct_extendR, hp]
      simp only [finCongr_apply, Fin.val_cast]
      rw [show momentList ω (L.eraseIdx (i : ℕ)) =
          momentList (contractRaw ρ σ) (l.eraseIdx (i : ℕ)) by
        change momentList ω ((List.map extendR l).eraseIdx (i : ℕ)) = _
        rw [List.eraseIdx_map, momentList_contractRaw_eq]]
  have hcol : ∀ (c : MajoranaIndex (n + m)) (M : Matrix (MajoranaIndex (n + m))
      (MajoranaIndex (n + m)) ℂ), M *ᵥ Pi.single c 1 = fun r => M r c := fun c M => by
    rw [Matrix.mulVec_single_one]; rfl
  -- the complex blocks
  have hGRR : G.submatrix embedR embedR = 1 - Complex.I • Ac := twoPoint_submatrix_RR ρ
  have hGEE : G.submatrix embedE embedE = 1 - Complex.I • Dc := twoPoint_submatrix_EE ρ
  have hGRE : G.submatrix embedR embedE = (-Complex.I) • Bc := twoPoint_submatrix_RE ρ
  have hGER : G.submatrix embedE embedR = (-Complex.I) • Cc := twoPoint_submatrix_ER ρ
  have hAcT : Ac.transpose = -Ac := by
    rw [hAc, ← Matrix.transpose_map, blockR_transpose hΓT, Matrix.map_neg _ (by simp)]
  have hDcT : Dc.transpose = -Dc := by
    rw [hDc, ← Matrix.transpose_map, blockE_transpose hΓT, Matrix.map_neg _ (by simp)]
  have hBcT : Bc.transpose = -Cc := by
    rw [hBc, hCc, ← Matrix.transpose_map, blockRE_transpose hΓT, Matrix.map_neg _ (by simp)]
  have hCcT : Cc.transpose = -Bc := by
    have h := congrArg Matrix.transpose hBcT
    rw [Matrix.transpose_transpose, Matrix.transpose_neg] at h
    exact (neg_eq_iff_eq_neg.mpr h).symm
  -- (E3) at a retained unit vector, as the row equation (III)
  have hIII : ∀ a' : MajoranaIndex n,
      (αR ᵥ* (1 - Complex.I • Ac)) a' + (bE ᵥ* ((-Complex.I) • Cc)) a' =
        2 * ((1 - Complex.I • Ac) *ᵥ y) a' -
          ((αR ᵥ* (1 - Complex.I • Ac).transpose) a' +
            (αE ᵥ* ((-Complex.I) • Bc).transpose) a') := by
    intro a'
    have h := hE3 (extendR (Pi.single a' 1))
    rw [hbfun, hαfun, hRconv, extendR_single, hcol, hcol] at h
    have e1 : (fun r => G r (embedR a')) ∘ embedR = fun r => (1 - Complex.I • Ac) r a' := by
      rw [← hGRR]; rfl
    have e2 : (fun r => G r (embedR a')) ∘ embedE = fun r => ((-Complex.I) • Cc) r a' := by
      rw [← hGER]; rfl
    have e3 : (fun r => G.transpose r (embedR a')) ∘ embedR =
        fun r => (1 - Complex.I • Ac) a' r := by
      rw [← hGRR]; rfl
    have e4 : (fun r => G.transpose r (embedR a')) ∘ embedE =
        fun r => ((-Complex.I) • Bc) a' r := by
      rw [← hGRE]; rfl
    rw [e1, e2, e3, e4] at h
    simpa only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h
  -- (E3) at an eliminated unit vector, as the row equation (I)
  have hI' : ∀ e' : MajoranaIndex m,
      (αR ᵥ* ((-Complex.I) • Bc)) e' + (bE ᵥ* (1 - Complex.I • Dc)) e' =
        2 * (((-Complex.I) • Cc) *ᵥ y) e' -
          ((αR ᵥ* ((-Complex.I) • Cc).transpose) e' +
            (αE ᵥ* (1 - Complex.I • Dc).transpose) e') := by
    intro e'
    have h := hE3 (extendE (Pi.single e' 1))
    rw [hbfun, hαfun, hRconv, extendE_single, hcol, hcol] at h
    have e1 : (fun r => G r (embedE e')) ∘ embedR = fun r => ((-Complex.I) • Bc) r e' := by
      rw [← hGRE]; rfl
    have e2 : (fun r => G r (embedE e')) ∘ embedE = fun r => (1 - Complex.I • Dc) r e' := by
      rw [← hGEE]; rfl
    have e3 : (fun r => G.transpose r (embedE e')) ∘ embedR =
        fun r => ((-Complex.I) • Cc) e' r := by
      rw [← hGER]; rfl
    have e4 : (fun r => G.transpose r (embedE e')) ∘ embedE =
        fun r => (1 - Complex.I • Dc) e' r := by
      rw [← hGEE]; rfl
    rw [e1, e2, e3, e4] at h
    simpa only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h
  -- transposes of the complex blocks
  have hT1 : (1 - Complex.I • Ac).transpose = 1 + Complex.I • Ac := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hAcT, smul_neg,
      sub_neg_eq_add]
  have hT2 : (1 - Complex.I • Dc).transpose = 1 + Complex.I • Dc := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hDcT, smul_neg,
      sub_neg_eq_add]
  have hT3 : ((-Complex.I) • Bc).transpose = Complex.I • Cc := by
    rw [Matrix.transpose_smul, hBcT, smul_neg, neg_smul, neg_neg]
  have hT4 : ((-Complex.I) • Cc).transpose = Complex.I • Bc := by
    rw [Matrix.transpose_smul, hCcT, smul_neg, neg_smul, neg_neg]
  -- (I) in the form of the row system: the αR terms cancel since G_RE + G_ERᵀ = 0
  have hI : αE ᵥ* (1 + Complex.I • Dc) + bE ᵥ* (1 - Complex.I • Dc) =
      (2 * Complex.I) • (y ᵥ* Bc) := by
    funext e'
    have h := hI' e'
    rw [hT4, hT2] at h
    have hmv : (((-Complex.I) • Cc) *ᵥ y) e' =
        (y ᵥ* (((-Complex.I) • Cc).transpose)) e' := by
      rw [Matrix.vecMul_transpose]
    rw [hmv, hT4] at h
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.vecMul_smul, smul_eq_mul] at h ⊢
    linear_combination h
  -- (II) from the relation of σ
  have hII : αE ᵥ* (1 - Complex.I • βc) = bE ᵥ* (1 + Complex.I • βc) := by
    have hGs : Gs = 1 - Complex.I • βc := rfl
    have hGsT : Gs.transpose = 1 + Complex.I • βc := by
      rw [hGs, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hβc,
        ← Matrix.transpose_map, hβT, Matrix.map_neg _ (by simp), smul_neg, sub_neg_eq_add]
    funext e'
    have h := hE2 (Pi.single e' 1)
    rw [hbfun, hαfun] at h
    have hcR : ∀ u : MajoranaIndex m → ℂ, extendE (n := n) u ∘ embedR = 0 := fun u => by
      funext r; simp [extendE_embedR]
    have hcE : ∀ u : MajoranaIndex m → ℂ, extendE (n := n) u ∘ embedE = u := fun u => by
      funext r; simp [extendE_embedE]
    rw [hcR, hcR, hcE, hcE, dotProduct_zero, zero_add, zero_add, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at h
    rw [← hGs, ← hGsT]
    exact h.symm
  -- the solution of the row system
  have hinvc : IsUnit (1 - Dc * βc).det := by
    have hmap : (1 - Dc * βc) = (1 - blockE Γ * β).map Complex.ofRealHom := by
      rw [Matrix.map_sub _ (by simp), Matrix.map_one _ (by simp) (by simp), Matrix.map_mul]; rfl
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hinv.map Complex.ofRealHom
  have hsol := row_system_solution Dc βc Bc Cc hinvc αE bE y hI hII
  -- (III) solved for αR
  have hαR : αR = y ᵥ* (1 + Complex.I • (Ac + Bc * βc * (1 - Dc * βc)⁻¹ * Cc)) := by
    funext a'
    have h := hIII a'
    rw [hT1, hT3] at h
    have hmv : ((1 - Complex.I • Ac) *ᵥ y) a' =
        (y ᵥ* (1 - Complex.I • Ac).transpose) a' := by
      rw [Matrix.vecMul_transpose]
    rw [hmv, hT1] at h
    have hs := congrFun hsol a'
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Matrix.vecMul_smul, smul_eq_mul,
      Matrix.sub_vecMul, Matrix.vecMul_one, Matrix.vecMul_add, Matrix.vecMul_sub] at h hs ⊢
    linear_combination (1 / 2 : ℂ) * h - (1 / 2 : ℂ) * hs
  -- the complexified contraction
  have hCm : (contractCov Γ β).map Complex.ofReal = Ac + Bc * βc * (1 - Dc * βc)⁻¹ * Cc := by
    change (contractCov Γ β).map Complex.ofRealHom = _
    rw [contractCov, Matrix.map_add _ (by simp), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    change Ac + Bc * βc * ((1 - blockE Γ * β)⁻¹).map Complex.ofReal * Cc = _
    rw [map_inv_one_sub_mul _ _ hinv]
  -- conclusion
  rw [trace_contractRaw_mul_majorana_mul, ← hω, ← hL, ← hX]
  change αR a = _
  rw [hαR, ← hCm]
  have hGt : (1 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ) +
      Complex.I • (contractCov Γ β).map Complex.ofReal =
      (1 - Complex.I • (contractCov Γ β).map Complex.ofReal).transpose := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, ← Matrix.transpose_map,
      contractCov_transpose hΓT hβT hinv, Matrix.map_neg _ (by simp), smul_neg, sub_neg_eq_add]
  rw [hGt, Matrix.vecMul_transpose]
  simp only [hy, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  ring
/-- Theorem 9: the moments of the contraction are `Z` times the Wick expansion of
`1 - i (Γ ⋆ β)`. -/
theorem momentList_contractRaw_eq_wick (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det)
    (l : List (MajoranaIndex n → ℂ)) :
    momentList (contractRaw ρ σ) l = normalization ρ σ *
      wick (1 - Complex.I •
        (contractCov (covariance ρ) (covariance σ)).map Complex.ofReal) l := by
  rw [← trace_contractRaw]
  exact momentList_eq_trace_mul_wick_of_recursion _ _
    (momentList_contractRaw_eq_zero_of_odd hρ.parity_conj hσ.parity_conj)
    (fun a l hl => recursion_contractRaw hρ hσ hinv l hl a) l

end recursion

/-! ### Corollary 10: the contracted state -/

lemma momentList_smul (c : ℂ) (τ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (l : List (MajoranaIndex n → ℂ)) : momentList (c • τ) l = c * momentList τ l := by
  simp [momentList, Matrix.trace_smul]

/-- A matrix whose two-point moments are `1 - iΓ'` for a real antisymmetric `Γ'` has
covariance `Γ'`. -/
lemma covariance_eq_of_trace_mul_majorana_mul_majorana (τ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (Γ' : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (hΓ' : Γ'.transpose = -Γ')
    (h : ∀ a b, (τ * (majorana a * majorana b)).trace =
      (1 - Complex.I • Γ'.map Complex.ofReal) a b) : covariance τ = Γ' := by
  ext a b
  have hab := h a b
  have hba := h b a
  have hanti := congrFun (congrFun hΓ' a) b
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hanti
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul] at hab hba
  rw [covariance, commutator, Matrix.mul_sub, Matrix.trace_sub, hab, hba, hanti]
  by_cases hab' : a = b
  · subst hab'
    have h0 : Γ' a a = 0 := by linarith
    simp [h0]
  · simp [hab', Ne.symm hab']
    ring

variable {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
  {σ : Matrix (FockIndex m) (FockIndex m) ℂ}

/-- Corollary 10: the covariance of the contracted state is `Γ ⋆ β`. -/
theorem covariance_contractState (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det)
    (hZ : normalization ρ σ ≠ 0) :
    covariance (contractState ρ σ) = contractCov (covariance ρ) (covariance σ) := by
  refine covariance_eq_of_trace_mul_majorana_mul_majorana _ _
    (contractCov_transpose (covariance_transpose ρ) (covariance_transpose σ) hinv) fun a b => ?_
  have h := momentList_contractRaw_eq_wick hρ hσ hinv [Pi.single a 1, Pi.single b 1]
  rw [wick_pair, single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
  rw [contractState, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : (contractRaw ρ σ * (majorana a * majorana b)).trace =
      momentList (contractRaw ρ σ) [Pi.single a 1, Pi.single b 1] := by
    simp [momentList, lincomb_single]
  rw [h2, h, ← mul_assoc, inv_mul_cancel₀ hZ, one_mul]
  rfl

/-- Corollary 10: the contracted state is Gaussian. -/
theorem isGaussian_contractState (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det)
    (hZ : normalization ρ σ ≠ 0) : IsGaussian (contractState ρ σ) := by
  refine ⟨isDensity_contractState hρ.1.1 hσ.1.1 hZ, fun l => ?_⟩
  rw [twoPoint, covariance_contractState hρ hσ hinv hZ, contractState, momentList_smul,
    momentList_contractRaw_eq_wick hρ hσ hinv, ← mul_assoc, inv_mul_cancel₀ hZ, one_mul]

/-! ### Theorem 13: the normalization is positive -/

section normalization

/-- A linear map on the eliminated vectors vanishing on the ranges of `1 - iD` and `1 + iβ`
vanishes when `1 - βD` is invertible: `F w = F (iDw) = F (βDw)`. -/
lemma linearMap_eq_zero_of_ranges {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : (MajoranaIndex m → ℂ) →ₗ[ℂ] V)
    (D β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℂ)
    (hinv : IsUnit (1 - β * D).det)
    (h1 : ∀ v, F ((1 - Complex.I • D) *ᵥ v) = 0)
    (h2 : ∀ u, F ((1 + Complex.I • β) *ᵥ u) = 0) (w : MajoranaIndex m → ℂ) :
    F w = 0 := by
  have hD : ∀ v, F v = F (Complex.I • (D *ᵥ v)) := by
    intro v
    have h := h1 v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, map_sub, sub_eq_zero] at h
    exact h
  have hβ : ∀ u, F u = -F (Complex.I • (β *ᵥ u)) := by
    intro u
    have h := h2 u
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, map_add,
      add_eq_zero_iff_eq_neg] at h
    exact h
  have hBD : ∀ v, F v = F ((β * D) *ᵥ v) := by
    intro v
    rw [hD v, hβ (Complex.I • (D *ᵥ v)), Matrix.mulVec_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul, map_neg, neg_neg, Matrix.mulVec_mulVec]
  have hker : ∀ v, F ((1 - β * D) *ᵥ v) = 0 := by
    intro v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, ← hBD v, sub_self]
  have := hker ((1 - β * D)⁻¹ *ᵥ w)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec] at this

/-- `lincomb` as a linear map. -/
def lincombₗ : (MajoranaIndex m → ℂ) →ₗ[ℂ] Matrix (FockIndex m) (FockIndex m) ℂ where
  toFun := lincomb
  map_add' := lincomb_add
  map_smul' := lincomb_smul

variable {ρ' σ : Matrix (FockIndex m) (FockIndex m) ℂ}

/-- The step of the induction: if `ρ' X σ = 0` for all shorter products, then
`ρ' (w·c) X σ = 0` for every `w`. -/
lemma mul_lincomb_mul_prod_mul_eq_zero (hρ' : IsGaussian ρ') (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - covariance σ * covariance ρ').det)
    (l : List (MajoranaIndex m → ℂ))
    (ih : ∀ l' : List (MajoranaIndex m → ℂ), l'.length < l.length + 1 →
      ρ' * (l'.map lincomb).prod * σ = 0) (w : MajoranaIndex m → ℂ) :
    ρ' * (lincomb w * (l.map lincomb).prod) * σ = 0 := by
  set X := (l.map lincomb).prod with hX
  let F : (MajoranaIndex m → ℂ) →ₗ[ℂ] Matrix (FockIndex m) (FockIndex m) ℂ :=
    (LinearMap.mulRight ℂ σ).comp ((LinearMap.mulRight ℂ X).comp
      ((LinearMap.mulLeft ℂ ρ').comp lincombₗ))
  have hF : ∀ v, F v = ρ' * (lincomb v * X) * σ := fun v => by
    simp [F, lincombₗ, Matrix.mul_assoc]
  have hGρ : twoPoint ρ' = 1 - Complex.I • (covariance ρ').map Complex.ofReal := rfl
  have hGσ : twoPoint σ = 1 - Complex.I • (covariance σ).map Complex.ofReal := rfl
  have hGσT : (twoPoint σ).transpose = 1 + Complex.I • (covariance σ).map Complex.ofReal := by
    rw [hGσ, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      ← Matrix.transpose_map, covariance_transpose, Matrix.map_neg _ (by simp), smul_neg,
      sub_neg_eq_add]
  have hinv' : IsUnit (1 - (covariance σ).map Complex.ofReal *
      (covariance ρ').map Complex.ofReal).det := by
    have hmap : (1 - (covariance σ).map Complex.ofReal * (covariance ρ').map Complex.ofReal) =
        (1 - covariance σ * covariance ρ').map Complex.ofRealHom := by
      rw [Matrix.map_sub _ (by simp), Matrix.map_one _ (by simp) (by simp), Matrix.map_mul]; rfl
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hinv.map Complex.ofRealHom
  rw [← hF]
  refine linearMap_eq_zero_of_ranges F _ _ hinv' (fun v => ?_) (fun u => ?_) w
  · -- the relation of ρ' moves the factor to the left
    rw [hF, ← hGρ, ← Matrix.mul_assoc, ← hρ'.relation v, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc ρ', hX, ih l (Nat.lt_succ_self _), Matrix.mul_zero]
  · -- the relation of σ after moving the factor through X
    rw [hF, ← hGσT, hX]
    rcases l with _ | ⟨v₀, l'⟩
    · have h0 := ih [] (by simp)
      simp only [List.map_nil, List.prod_nil, Matrix.mul_one] at h0 ⊢
      rw [Matrix.mul_assoc, hσ.relation, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
    · rw [lincomb_mul_prod, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]
      have hlast : ρ' * ((-1 : ℂ) ^ (v₀ :: l').length •
          ((List.map lincomb (v₀ :: l')).prod * lincomb ((twoPoint σ).transpose *ᵥ u))) * σ =
          0 := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hσ.relation,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, ih (v₀ :: l') (Nat.lt_succ_self _),
          Matrix.zero_mul, smul_zero]
      rw [hlast, add_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, ih ((v₀ :: l').eraseIdx i) ?_, smul_zero]
      have := List.length_eraseIdx_le (v₀ :: l') i
      simp only [List.length_cons] at this ⊢
      omega

/-- `ρ' X σ = 0` for every product of Majorana linear combinations, once `ρ' σ = 0`. -/
lemma mul_prod_mul_eq_zero (hρ' : IsGaussian ρ') (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - covariance σ * covariance ρ').det) (h0 : ρ' * σ = 0)
    (l : List (MajoranaIndex m → ℂ)) : ρ' * (l.map lincomb).prod * σ = 0 := by
  suffices h : ∀ k, ∀ l : List (MajoranaIndex m → ℂ), l.length < k →
      ρ' * (l.map lincomb).prod * σ = 0 from h (l.length + 1) l (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro l hl; exact absurd hl (Nat.not_lt_zero _)
  | succ k ih =>
    intro l hl
    rcases l with _ | ⟨w, l⟩
    · simpa using h0
    · rw [List.map_cons, List.prod_cons]
      refine mul_lincomb_mul_prod_mul_eq_zero hρ' hσ hinv l (fun l' hl' => ih l' ?_) w
      simp only [List.length_cons] at hl
      omega

/-- Two positive semidefinite matrices with `Tr (A B) = 0` satisfy `A B = 0`. -/
lemma mul_eq_zero_of_trace_mul_eq_zero {A B : Matrix (FockIndex m) (FockIndex m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (h : (A * B).trace = 0) : A * B = 0 := by
  classical
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    (A := Matrix (FockIndex m) (FockIndex m) ℂ) hB.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hB.nonneg)
  obtain ⟨Y, hY, -, hYY⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    (A := Matrix (FockIndex m) (FockIndex m) ℂ) hA.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
  have hXH : X.conjTranspose = X := hX.star_eq
  have hYH : Y.conjTranspose = Y := hY.star_eq
  -- Tr (A B) = Tr ((Y X)ᴴ (Y X))
  have h1 : ((Y * X).conjTranspose * (Y * X)).trace = 0 := by
    rw [Matrix.conjTranspose_mul, hXH, hYH, Matrix.mul_assoc, Matrix.trace_mul_comm, ← h,
      ← hXX, ← hYY]
    simp only [Matrix.mul_assoc]
  have hYX : Y * X = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h1
  calc A * B = Y * (Y * X) * X := by rw [← hXX, ← hYY]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hYX, Matrix.mul_zero, Matrix.zero_mul]

/-- A matrix `M` with `A M B = 0` for every `M`, where `A` and `B` have trace one, cannot exist:
`A` or `B` would vanish. -/
lemma trace_ne_one_of_forall_mul_mul_eq_zero {A B : Matrix (FockIndex m) (FockIndex m) ℂ}
    (h : ∀ M : Matrix (FockIndex m) (FockIndex m) ℂ, A * M * B = 0) (hA : A.trace = 1) :
    B = 0 := by
  by_contra hB
  obtain ⟨s, t, hst⟩ : ∃ s t, B s t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hB (Matrix.ext hall)
  have hA0 : ∃ i j, A i j ≠ 0 := by
    by_contra hall
    push Not at hall
    have : A = 0 := Matrix.ext hall
    rw [this, Matrix.trace_zero] at hA
    exact zero_ne_one hA
  obtain ⟨i, j, hij⟩ := hA0
  have key : (A * (Matrix.single j s (1 : ℂ) : Matrix (FockIndex m) (FockIndex m) ℂ) * B) i t =
      A i j * B s t := by
    rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · rw [Matrix.mul_single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.mul_single_apply_of_ne (hbj := hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [h (Matrix.single j s 1), Matrix.zero_apply] at key
  rcases mul_eq_zero.mp key.symm with h1 | h1
  · exact hij h1
  · exact hst h1

end normalization

variable {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
  {σ : Matrix (FockIndex m) (FockIndex m) ℂ}

/-- Theorem 13: the normalization is nonzero when `1 - Dβ` is invertible. -/
theorem normalization_ne_zero (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det) :
    normalization ρ σ ≠ 0 := by
  intro hZ
  have hρE : IsGaussian (ptraceR ρ) := isGaussian_ptraceR hρ
  have hcov : covariance (ptraceR ρ) = blockE (covariance ρ) := covariance_ptraceR ρ
  have hZ' : (ptraceR ρ * σ).trace = 0 := by
    rw [trace_ptraceR_mul]; exact hZ
  have h0 : ptraceR ρ * σ = 0 := mul_eq_zero_of_trace_mul_eq_zero hρE.1.1 hσ.1.1 hZ'
  have hinv' : IsUnit (1 - covariance σ * covariance (ptraceR ρ)).det := by
    rw [hcov, Matrix.det_one_sub_mul_comm]; exact hinv
  have hall : ∀ M : Matrix (FockIndex m) (FockIndex m) ℂ, ptraceR ρ * M * σ = 0 := by
    intro M
    rw [eq_sum_trace_mul_conjTranspose_monomial_smul M]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_eq_zero fun S _ => ?_, smul_zero]
    rw [monomial_eq_prod_lincomb, mul_prod_mul_eq_zero hρE hσ hinv' h0, smul_zero]
  have hσ0 := trace_ne_one_of_forall_mul_mul_eq_zero hall hρE.1.2
  have h1 := hσ.1.2
  rw [hσ0, Matrix.trace_zero] at h1
  exact zero_ne_one h1

/-- Theorem 13: the normalization is positive. -/
theorem normalization_pos (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det) :
    0 < normalization ρ σ :=
  lt_of_le_of_ne (normalization_nonneg hρ.1.1 hσ.1.1) (normalization_ne_zero hρ hσ hinv).symm

/-- Corollary 10 with Theorem 13: the contracted state of Gaussian states is Gaussian with
covariance `Γ ⋆ β`, whenever `1 - Dβ` is invertible. -/
theorem isGaussian_contractState' (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hinv : IsUnit (1 - blockE (covariance ρ) * covariance σ).det) :
    IsGaussian (contractState ρ σ) ∧
      covariance (contractState ρ σ) = contractCov (covariance ρ) (covariance σ) :=
  ⟨isGaussian_contractState hρ hσ hinv (normalization_ne_zero hρ hσ hinv),
   covariance_contractState hρ hσ hinv (normalization_ne_zero hρ hσ hinv)⟩

end Fermionic
