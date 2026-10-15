/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Contraction.Bond
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Periodic assembly of a Gaussian fermionic matrix product state

Sites `Fin N`; each site has `M` left virtual modes `A`, `M` right virtual modes `B` and
`P` physical modes `C`. The periodic input is the independent sum of the local
covariances, relabelled into retained (physical) and eliminated (virtual) labels with the
`B` labels shifted by one site, so that the eliminated labels are literally
`PairIndex (Fin N × Fin M)` and the periodic bond is `bond (Fin N × Fin M)`.
-/

open Matrix

namespace Fermionic

/-! ### Relabelling and independent sums preserve admissibility -/

section Relabel

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma submatrix_equiv_injective (e : ι ≃ κ) {A B : Matrix κ κ ℝ}
    (h : A.submatrix e e = B.submatrix e e) : A = B := by
  ext i j
  have := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa using this

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma submatrix_equiv_transpose_eq_neg_iff (e : ι ≃ κ) (Γ : Matrix κ κ ℝ) :
    (Γ.submatrix e e).transpose = -(Γ.submatrix e e) ↔ Γ.transpose = -Γ := by
  rw [Matrix.transpose_submatrix]
  constructor
  · intro h
    exact submatrix_equiv_injective e (by rw [h]; rfl)
  · intro h
    rw [h]; rfl

omit [DecidableEq ι] [DecidableEq κ] in
lemma dotProduct_comp_equiv (e : ι ≃ κ) (w : κ → ℝ) :
    (w ∘ e) ⬝ᵥ (w ∘ e) = w ⬝ᵥ w := by
  simp only [dotProduct, Function.comp]
  exact Equiv.sum_comp e (fun k => w k * w k)

omit [DecidableEq ι] [DecidableEq κ] in
lemma mulVec_submatrix_equiv (e : ι ≃ κ) (Γ : Matrix κ κ ℝ) (v : ι → ℝ) :
    (Γ.submatrix e e) *ᵥ v = (Γ *ᵥ (v ∘ e.symm)) ∘ e := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp]
  rw [← Equiv.sum_comp e (fun k => Γ (e i) k * v (e.symm k))]
  simp

/-- Lemma 3 (relabelling): admissibility is invariant under an index bijection. -/
theorem admissible_submatrix_equiv_iff (e : ι ≃ κ) (Γ : Matrix κ κ ℝ) :
    Admissible (Γ.submatrix e e) ↔ Admissible Γ := by
  constructor
  · intro h
    have hT := (submatrix_equiv_transpose_eq_neg_iff e Γ).mp h.1
    rw [admissible_iff_norm hT]
    intro w
    have := (admissible_iff_norm h.1).mp h (w ∘ e)
    have hc : (w ∘ e) ∘ e.symm = w := by ext k; simp
    rw [mulVec_submatrix_equiv, dotProduct_comp_equiv, hc, dotProduct_comp_equiv] at this
    exact this
  · intro h
    have hT := (submatrix_equiv_transpose_eq_neg_iff e Γ).mpr h.1
    rw [admissible_iff_norm hT]
    intro v
    rw [mulVec_submatrix_equiv, dotProduct_comp_equiv, ← dotProduct_comp_equiv e.symm v]
    exact (admissible_iff_norm h.1).mp h _

/-- Lemma 3 (relabelling): purity is invariant under an index bijection. -/
theorem pure_submatrix_equiv_iff (e : ι ≃ κ) (Γ : Matrix κ κ ℝ) :
    Pure (Γ.submatrix e e) ↔ Pure Γ := by
  have hmul : (Γ * Γ).submatrix e e = Γ.submatrix e e * Γ.submatrix e e :=
    (Matrix.submatrix_mul_equiv Γ Γ e e e).symm
  have hneg : (-1 : Matrix ι ι ℝ) = (-1 : Matrix κ κ ℝ).submatrix e e := by
    ext i j; simp [Matrix.one_apply]
  constructor
  · rintro ⟨hT, hsq⟩
    refine ⟨(submatrix_equiv_transpose_eq_neg_iff e Γ).mp hT, ?_⟩
    rw [← hmul, hneg] at hsq
    exact submatrix_equiv_injective e hsq
  · rintro ⟨hT, hsq⟩
    refine ⟨(submatrix_equiv_transpose_eq_neg_iff e Γ).mpr hT, ?_⟩
    rw [← hmul, hsq, ← hneg]

end Relabel

section BlockDiagonal

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ] [DecidableEq ι]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
lemma blockDiagonal_transpose_eq_neg_iff (Γ : σ → Matrix ι ι ℝ) :
    (Matrix.blockDiagonal Γ).transpose = -(Matrix.blockDiagonal Γ) ↔
      ∀ i, (Γ i).transpose = -(Γ i) := by
  rw [Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_neg,
    Matrix.blockDiagonal_injective.eq_iff, funext_iff]
  simp

omit [DecidableEq ι] in
lemma dotProduct_mulVec_blockDiagonal (Γ : σ → Matrix ι ι ℝ) (v : ι × σ → ℝ) :
    ((Matrix.blockDiagonal Γ) *ᵥ v) ⬝ᵥ ((Matrix.blockDiagonal Γ) *ᵥ v) =
      ∑ i : σ, ((Γ i) *ᵥ (fun k => v (k, i))) ⬝ᵥ ((Γ i) *ᵥ (fun k => v (k, i))) := by
  have hmv : ∀ p : ι × σ, ((Matrix.blockDiagonal Γ) *ᵥ v) p =
      ((Γ p.2) *ᵥ (fun k => v (k, p.2))) p.1 := by
    intro p
    simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm, Finset.sum_eq_single p.2]
    · simp
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro k _
      simp [hj.symm]
    · simp
  simp only [dotProduct, hmv, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [DecidableEq σ] [DecidableEq ι] in
lemma dotProduct_self_prod (v : ι × σ → ℝ) :
    v ⬝ᵥ v = ∑ i : σ, (fun k => v (k, i)) ⬝ᵥ (fun k => v (k, i)) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Lemma 3 (independent sums): a block-diagonal matrix is admissible if and only if
every block is. -/
theorem admissible_blockDiagonal_iff (Γ : σ → Matrix ι ι ℝ) :
    Admissible (Matrix.blockDiagonal Γ) ↔ ∀ i, Admissible (Γ i) := by
  constructor
  · intro h i
    have hT := (blockDiagonal_transpose_eq_neg_iff Γ).mp h.1 i
    rw [admissible_iff_norm hT]
    intro w
    let v : ι × σ → ℝ := fun p => if p.2 = i then w p.1 else 0
    have hv := (admissible_iff_norm h.1).mp h v
    rw [dotProduct_mulVec_blockDiagonal, dotProduct_self_prod] at hv
    have hzero : ∀ j, j ≠ i → (fun k => v (k, j)) = 0 := by
      intro j hj; ext k; simp [v, hj]
    have hi : (fun k => v (k, i)) = w := by ext k; simp [v]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i] at hv
    · simpa [hi] using hv
    all_goals first
      | (intro j _ hj; simp [hzero j hj])
      | simp
  · intro h
    have hT := (blockDiagonal_transpose_eq_neg_iff Γ).mpr fun i => (h i).1
    rw [admissible_iff_norm hT]
    intro v
    rw [dotProduct_mulVec_blockDiagonal, dotProduct_self_prod]
    exact Finset.sum_le_sum fun i _ => (admissible_iff_norm (h i).1).mp (h i) _

end BlockDiagonal

/-! ### The periodic chain -/

/-- Modes of one site: `inl (inl a)` left virtual, `inl (inr b)` right virtual, `inr c`
physical. -/
abbrev Site (M P : ℕ) := (Fin M ⊕ Fin M) ⊕ Fin P

/-- Majorana labels of one site, `x` then `y`. -/
abbrev SiteLabel (M P : ℕ) := Site M P ⊕ Site M P

/-- Global Majorana labels, `x` then `y`, sites inside. -/
abbrev ChainLabel (N M P : ℕ) := (Fin N × Site M P) ⊕ (Fin N × Site M P)

/-- Retained labels: `x` and `y` of the physical modes. -/
abbrev Retained (N P : ℕ) := (Fin N × Fin P) ⊕ (Fin N × Fin P)

/-- Eliminated labels: `(x_L, x_L', y_L, y_L')` with `L = Fin N × Fin M`. -/
abbrev Eliminated (N M : ℕ) := PairIndex (Fin N × Fin M)

variable {N M P : ℕ}

/-- One Majorana sector of the label bijection `e`: `L` labels name `A` at the same site,
`L'` labels name `B` at the previous site. -/
def sectorMap (N M P : ℕ) : (Fin N × Fin P) ⊕ ((Fin N × Fin M) ⊕ (Fin N × Fin M)) →
    Fin N × Site M P
  | Sum.inl (i, c) => (i, Sum.inr c)
  | Sum.inr (Sum.inl (i, a)) => (i, Sum.inl (Sum.inl a))
  | Sum.inr (Sum.inr (i, b)) => ((finRotate N).symm i, Sum.inl (Sum.inr b))

def sectorMapInv (N M P : ℕ) : Fin N × Site M P →
    (Fin N × Fin P) ⊕ ((Fin N × Fin M) ⊕ (Fin N × Fin M))
  | (i, Sum.inr c) => Sum.inl (i, c)
  | (i, Sum.inl (Sum.inl a)) => Sum.inr (Sum.inl (i, a))
  | (i, Sum.inl (Sum.inr b)) => Sum.inr (Sum.inr (finRotate N i, b))

/-- One sector of `e` as an equivalence. -/
def sectorEquiv (N M P : ℕ) :
    (Fin N × Fin P) ⊕ ((Fin N × Fin M) ⊕ (Fin N × Fin M)) ≃ Fin N × Site M P where
  toFun := sectorMap N M P
  invFun := sectorMapInv N M P
  left_inv := by
    rintro (⟨i, c⟩ | ⟨i, a⟩ | ⟨i, b⟩) <;> simp [sectorMap, sectorMapInv, -finRotate_symm_apply,
      -finRotate_apply]
  right_inv := by
    rintro ⟨i, (a | b) | c⟩ <;> simp [sectorMap, sectorMapInv, -finRotate_symm_apply,
      -finRotate_apply]

/-- Regrouping `(x_R, x_E) ⊕ (y_R, y_E)` as `R ⊕ E` with `E = (x_L, x_L') ⊕ (y_L, y_L')`. -/
def splitEquiv (N M P : ℕ) :
    Retained N P ⊕ Eliminated N M ≃
      ((Fin N × Fin P) ⊕ ((Fin N × Fin M) ⊕ (Fin N × Fin M))) ⊕
        ((Fin N × Fin P) ⊕ ((Fin N × Fin M) ⊕ (Fin N × Fin M))) :=
  (Equiv.sumAssoc _ _ _).trans <|
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumAssoc _ _ _).symm).trans <|
      (Equiv.sumCongr (Equiv.refl _)
        (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _))).trans <|
        (Equiv.sumCongr (Equiv.refl _) (Equiv.sumAssoc _ _ _)).trans
          (Equiv.sumAssoc _ _ _).symm

/-- The label bijection `e : R ⊕ E ≃ ChainLabel N M P`. -/
def chainEquiv (N M P : ℕ) : Retained N P ⊕ Eliminated N M ≃ ChainLabel N M P :=
  (splitEquiv N M P).trans (Equiv.sumCongr (sectorEquiv N M P) (sectorEquiv N M P))

/-- Site-major global labels from `(site, site label)` pairs. -/
def siteMajorEquiv (N M P : ℕ) : ChainLabel N M P ≃ SiteLabel M P × Fin N :=
  (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)).trans
    (Equiv.sumProdDistrib _ _ _).symm

/-- Definition 1: the periodic input, the independent sum of the local matrices
relabelled by `e`. -/
def periodicInput (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Matrix (Retained N P ⊕ Eliminated N M) (Retained N P ⊕ Eliminated N M) ℝ :=
  ((Matrix.blockDiagonal Γ).submatrix (siteMajorEquiv N M P) (siteMajorEquiv N M P)).submatrix
    (chainEquiv N M P) (chainEquiv N M P)

/-- Definition 2: the periodic bond is the bond covariance of `L = Fin N × Fin M`. -/
def periodicBond (N M : ℕ) : Matrix (Eliminated N M) (Eliminated N M) ℝ :=
  bond (Fin N × Fin M)

/-- Definition 2: the periodic covariance. -/
noncomputable def periodicCovariance (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Matrix (Retained N P) (Retained N P) ℝ :=
  contract (periodicInput Γ) (periodicBond N M)

/-- Lemma 3 applied: the periodic input is admissible when every local matrix is. -/
theorem admissible_periodicInput_iff (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Admissible (periodicInput Γ) ↔ ∀ i, Admissible (Γ i) := by
  unfold periodicInput
  rw [admissible_submatrix_equiv_iff, admissible_submatrix_equiv_iff,
    admissible_blockDiagonal_iff]

/-- Theorem 4: the periodic covariance of admissible chain data is admissible. -/
theorem periodicCovariance_admissible (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hΓ : ∀ i, Admissible (Γ i))
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    Admissible (periodicCovariance Γ) :=
  contract_admissible ((admissible_periodicInput_iff Γ).mpr hΓ)
    (pure_bond (L := Fin N × Fin M)).admissible hinv

end Fermionic
