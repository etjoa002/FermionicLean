/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.Fourier
import FermionicLean.Fock.Occupation

/-! # Product states as chains without virtual modes

A chain with `M = 0` virtual modes has no bonds: its covariance is the independent sum of
the on-site covariances. The occupation states of Fock space are such chains, one
occupation pattern per site.
-/

open Matrix

namespace Fermionic

variable {N P : ℕ}

/-! ### Chains with `M = 0` -/

/-- The physical labels of a site without virtual modes. -/
def physLabel (P : ℕ) : Fin P ⊕ Fin P ≃ SiteLabel 0 P where
  toFun
    | Sum.inl c => Sum.inl (Sum.inr c)
    | Sum.inr c => Sum.inr (Sum.inr c)
  invFun
    | Sum.inl (Sum.inr c) => Sum.inl c
    | Sum.inr (Sum.inr c) => Sum.inr c
    | Sum.inl (Sum.inl a) => a.elim (fun a => a.elim0) (fun a => a.elim0)
    | Sum.inr (Sum.inl a) => a.elim (fun a => a.elim0) (fun a => a.elim0)
  left_inv := by rintro (c | c) <;> rfl
  right_inv := by rintro (((a | a) | c) | ((a | a) | c)) <;> first | rfl | exact a.elim0

lemma physLabel_eq_siteSplit (a : Fin P ⊕ Fin P) :
    physLabel P a = siteSplit 0 P (Sum.inl a) := by
  rcases a with c | c <;> rfl

/-- The retained labels of a chain without virtual modes, in site-major coordinates. -/
def retainedZeroEquiv (N P : ℕ) : Retained N P ≃ SiteLabel 0 P × Fin N :=
  ((Equiv.sumEmpty (Retained N P) (Eliminated N 0)).symm.trans (chainEquiv N 0 P)).trans
    (siteMajorEquiv N 0 P)

lemma retainedZeroEquiv_retained (i : Fin N) (a : Fin P ⊕ Fin P) :
    retainedZeroEquiv N P (retained i a) = (physLabel P a, i) := by
  rcases a with c | c <;> rfl

/-- The periodic input of a chain without virtual modes has no eliminated block. -/
lemma toBlocks₁₁_periodicInput_zero (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    (periodicInput Γ).toBlocks₁₁ =
      (Matrix.blockDiagonal Γ).submatrix (retainedZeroEquiv N P) (retainedZeroEquiv N P) := by
  ext r r'
  rfl

/-- Proposition 1: without virtual modes, the invertibility condition is void. -/
theorem contractInvertible_zero (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    ContractInvertible (periodicInput Γ) (periodicBond N 0) := by
  unfold ContractInvertible
  rw [Matrix.det_isEmpty]
  exact isUnit_one

/-- Proposition 1: without virtual modes, the chain covariance is the relabelled independent
sum of the on-site covariances. -/
theorem periodicCovariance_zero (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    periodicCovariance Γ =
      (Matrix.blockDiagonal Γ).submatrix (retainedZeroEquiv N P) (retainedZeroEquiv N P) := by
  unfold periodicCovariance contract
  rw [← toBlocks₁₁_periodicInput_zero]
  have h : (periodicInput Γ).toBlocks₁₂ * periodicBond N 0 = 0 := by
    ext r e
    exact (IsEmpty.false e).elim
  rw [h, Matrix.zero_mul, Matrix.zero_mul, add_zero]

/-- Proposition 1, entrywise: the chain covariance couples only labels of the same site. -/
theorem periodicCovariance_zero_apply (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ)
    (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    periodicCovariance Γ (retained i a) (retained j b) =
      if i = j then Γ i (siteSplit 0 P (Sum.inl a)) (siteSplit 0 P (Sum.inl b)) else 0 := by
  rw [periodicCovariance_zero, Matrix.submatrix_apply, retainedZeroEquiv_retained,
    retainedZeroEquiv_retained, Matrix.blockDiagonal_apply, physLabel_eq_siteSplit,
    physLabel_eq_siteSplit]

lemma pure_blockDiagonal_iff {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
    [DecidableEq ι] (Γ : σ → Matrix ι ι ℝ) :
    Pure (Matrix.blockDiagonal Γ) ↔ ∀ i, Pure (Γ i) := by
  have hneg : (-1 : Matrix (ι × σ) (ι × σ) ℝ) = Matrix.blockDiagonal (fun _ => -1) := by
    rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_neg]
    rfl
  unfold Pure
  rw [blockDiagonal_transpose_eq_neg_iff, ← Matrix.blockDiagonal_mul, hneg,
    Matrix.blockDiagonal_injective.eq_iff, funext_iff]
  exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- Proposition 1: admissibility and purity are site by site. -/
theorem admissible_periodicCovariance_zero_iff
    (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    Admissible (periodicCovariance Γ) ↔ ∀ i, Admissible (Γ i) := by
  rw [periodicCovariance_zero, admissible_submatrix_equiv_iff, admissible_blockDiagonal_iff]

theorem pure_periodicCovariance_zero_iff
    (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    Pure (periodicCovariance Γ) ↔ ∀ i, Pure (Γ i) := by
  rw [periodicCovariance_zero, pure_submatrix_equiv_iff, pure_blockDiagonal_iff]

/-! ### Occupation states -/

/-- The on-site covariance of an occupation pattern `t` of `P` modes, on the labels of a
site without virtual modes. -/
def occupationLocal (t : FockIndex P) : Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ :=
  (Matrix.fromBlocks 0 (occupationSign t) (-(occupationSign t)) 0).submatrix
    (physLabel P).symm (physLabel P).symm

/-- Site-major identification of the modes of `N` sites with `P` modes each. -/
def siteModeEquiv (N P : ℕ) : Fin N × Fin P ≃ Fin (N * P) := finProdFinEquiv

/-- Majorana labels of the chain as Majorana labels of `N * P` modes. -/
def retainedModeEquiv (N P : ℕ) : Retained N P ≃ MajoranaIndex (N * P) :=
  Equiv.sumCongr (siteModeEquiv N P) (siteModeEquiv N P)

/-- Theorem 2: the covariance of an occupation state of `N * P` modes is the chain without
virtual modes whose on-site covariances are the occupation covariances of the sites. -/
theorem covariance_occupation_eq_periodic (s : Fin N × Fin P → Fin 2) :
    (covariance (occupation (s ∘ (siteModeEquiv N P).symm))).submatrix
        (retainedModeEquiv N P) (retainedModeEquiv N P) =
      periodicCovariance (fun i => occupationLocal (fun c => s (i, c))) := by
  ext r r'
  obtain ⟨i, a, rfl⟩ : ∃ i a, r = retained i a := by
    rcases r with ⟨i, c⟩ | ⟨i, c⟩
    · exact ⟨i, Sum.inl c, rfl⟩
    · exact ⟨i, Sum.inr c, rfl⟩
  obtain ⟨j, b, rfl⟩ : ∃ j b, r' = retained j b := by
    rcases r' with ⟨j, d⟩ | ⟨j, d⟩
    · exact ⟨j, Sum.inl d, rfl⟩
    · exact ⟨j, Sum.inr d, rfl⟩
  rw [periodicCovariance_zero_apply, covariance_occupation]
  have hsign : ∀ (i j : Fin N) (c d : Fin P),
      occupationSign (s ∘ (siteModeEquiv N P).symm) (siteModeEquiv N P (i, c))
          (siteModeEquiv N P (j, d)) =
        if i = j then occupationSign (fun c => s (i, c)) c d else 0 := by
    intro i j c d
    simp only [occupationSign, Matrix.diagonal_apply, Function.comp, Equiv.symm_apply_apply,
      (siteModeEquiv N P).injective.eq_iff, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rcases a with c | c <;> rcases b with d | d <;>
    simp [retained, retainedModeEquiv, occupationLocal, physLabel, siteSplit,
      Matrix.fromBlocks, hsign, neg_ite]

/-- Theorem 2: the vacuum of `N * P` modes is the chain with `-Ω_P` at every site. -/
theorem covariance_vacuum_eq_periodic :
    (covariance (occupation (fun _ : Fin (N * P) => (0 : Fin 2)))).submatrix
        (retainedModeEquiv N P) (retainedModeEquiv N P) =
      periodicCovariance (fun _ : Fin N => occupationLocal (fun _ : Fin P => (0 : Fin 2))) :=
  covariance_occupation_eq_periodic (fun _ => 0)

lemma occupationLocal_vacuum :
    occupationLocal (fun _ : Fin P => (0 : Fin 2)) =
      (-(standardCovariance P)).submatrix (physLabel P).symm (physLabel P).symm := by
  unfold occupationLocal
  rw [← covariance_occupation, covariance_vacuum]

end Fermionic
