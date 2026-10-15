/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Occupation
import FermionicLean.Contraction.Bond

/-! # The bond state

The two-mode state `ψ = (|00⟩ + i |11⟩)/√2` has density operator `ρ = |ψ⟩⟨ψ|`, i.e.
`ρ s t = ψ s * conj (ψ t)`. Its Majorana covariance is the bond covariance
`bond (Fin 1)` under the relabelling `x_1 ↦ x_L, x_2 ↦ x_L', y_1 ↦ y_L, y_2 ↦ y_L'`:
`Γ_{x_1 x_2} = 1`, `Γ_{y_1 y_2} = -1`, all other entries `0`.

The computation goes through `Tr (ρ M) = ⟨ψ, M ψ⟩` and the signed-flip form
`c_a c_b = diagonal (f_a · f_b ∘ flip) X_{mode a} X_{mode b}`, so every entry is a sum of
two explicit products of amplitudes.
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

/-- The amplitude `1/√2`. -/
noncomputable def bondAmp : ℝ := (Real.sqrt 2)⁻¹

lemma bondAmp_mul_self : bondAmp * bondAmp = 1 / 2 := by
  rw [bondAmp, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The bond state vector `ψ = (|00⟩ + i |11⟩)/√2`. -/
noncomputable def bondVec : FockIndex 2 → ℂ := fun s =>
  if s = fun _ => 0 then (bondAmp : ℂ)
  else if s = fun _ => 1 then Complex.I * bondAmp
  else 0

/-- The bond state `|ψ⟩⟨ψ|`. -/
noncomputable def bondState : Matrix (FockIndex 2) (FockIndex 2) ℂ :=
  Matrix.vecMulVec bondVec (star bondVec)

/-- The relabelling `x_1 ↦ x_L, x_2 ↦ x_L', y_1 ↦ y_L, y_2 ↦ y_L'` of the Majorana labels
of two modes as the labels of one bond. -/
def bondLabel : MajoranaIndex 2 → PairIndex (Fin 1)
  | Sum.inl j => Sum.inl (if j = 0 then Sum.inl 0 else Sum.inr 0)
  | Sum.inr j => Sum.inr (if j = 0 then Sum.inl 0 else Sum.inr 0)

theorem bondLabel_bijective : Function.Bijective bondLabel := by decide

/-! ### The vector -/

lemma fock_zero_ne_one : (fun _ : Fin 2 => (0 : Fin 2)) ≠ fun _ => 1 := by
  intro h
  have := congrFun h 0
  exact absurd this (by decide)

lemma bondVec_zero : bondVec (fun _ => 0) = bondAmp := by
  simp [bondVec]

lemma bondVec_one : bondVec (fun _ => 1) = Complex.I * bondAmp := by
  simp [bondVec, fock_zero_ne_one.symm]

lemma bondVec_of_ne {s : FockIndex 2} (h0 : s ≠ fun _ => 0) (h1 : s ≠ fun _ => 1) :
    bondVec s = 0 := by
  simp [bondVec, h0, h1]

/-- A sum over configurations weighted by `conj ψ` has only the terms `00` and `11`. -/
lemma sum_star_bondVec_mul (F : FockIndex 2 → ℂ) :
    ∑ s, star (bondVec s) * F s =
      star (bondVec fun _ => 0) * F (fun _ => 0) + star (bondVec fun _ => 1) * F (fun _ => 1) := by
  refine Finset.sum_eq_add_of_mem _ _ (Finset.mem_univ _) (Finset.mem_univ _) fock_zero_ne_one
    fun c _ hc => ?_
  rw [bondVec_of_ne hc.1 hc.2]
  simp

/-- `‖ψ‖² = 1`. -/
lemma bondVec_dotProduct_star : bondVec ⬝ᵥ star bondVec = 1 := by
  have hc := bondAmp_mul_self
  rw [dotProduct]
  have h := sum_star_bondVec_mul bondVec
  simp only [mul_comm (star (bondVec _)), Pi.star_apply] at h ⊢
  rw [h, bondVec_zero, bondVec_one]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination 2 * hc
  · simp [Complex.mul_re, Complex.mul_im]

/-- `x* (v wᵀ) x = (x* v) (wᵀ x)`. -/
lemma dotProduct_vecMulVec_mulVec {ι : Type*} [Fintype ι] (v w x : ι → ℂ) :
    star x ⬝ᵥ (Matrix.vecMulVec v w *ᵥ x) = (star x ⬝ᵥ v) * (w ⬝ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bondState_conjTranspose : bondState.conjTranspose = bondState := by
  rw [bondState, Matrix.conjTranspose_vecMulVec, star_star]

/-- Theorem 5 (F3b): the bond state is a density operator. -/
theorem isDensity_bondState : IsDensity bondState := by
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg bondState_conjTranspose fun x => ?_, ?_⟩
  · rw [bondState, dotProduct_vecMulVec_mulVec, star_dotProduct x bondVec, Complex.nonneg_iff]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    constructor
    · nlinarith [mul_self_nonneg (star bondVec ⬝ᵥ x).re, mul_self_nonneg (star bondVec ⬝ᵥ x).im]
    · ring
  · rw [bondState, Matrix.trace_vecMulVec, bondVec_dotProduct_star]

/-! ### The covariance -/

/-- `Tr (v wᵀ M) = ∑ s, w s (M v) s`. -/
lemma trace_vecMulVec_mul {ι : Type*} [Fintype ι] (v w : ι → ℂ) (M : Matrix ι ι ℂ) :
    (Matrix.vecMulVec v w * M).trace = ∑ s, w s * (M *ᵥ v) s := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `X_j` acts on vectors by precomposition with the flip. -/
lemma pauliX_mulVec {n : ℕ} (j : Fin n) (v : FockIndex n → ℂ) :
    pauliX j *ᵥ v = fun s => v (flip j s) := by
  rw [pauliX, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

/-- The action of `c_a c_b` on a vector, entrywise. -/
lemma majorana_mul_mulVec {n : ℕ} (a b : MajoranaIndex n) (v : FockIndex n → ℂ)
    (s : FockIndex n) :
    ((majorana a * majorana b) *ᵥ v) s =
      majoranaSign a s * majoranaSign b (flip (mode a) s) *
        v (flip (mode b) (flip (mode a) s)) := by
  rw [majorana_eq_diagonal_mul a, majorana_eq_diagonal_mul b,
    diagonal_mul_pauliX_mul_diagonal_mul_pauliX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pauliX_mulVec, pauliX_mulVec, Matrix.mulVec_diagonal]

/-- `Tr (ρ M) = ⟨ψ, M ψ⟩` reduced to the two configurations `00` and `11`. -/
lemma trace_bondState_mul (M : Matrix (FockIndex 2) (FockIndex 2) ℂ) :
    (bondState * M).trace =
      star (bondVec fun _ => 0) * (M *ᵥ bondVec) (fun _ => 0) +
        star (bondVec fun _ => 1) * (M *ᵥ bondVec) (fun _ => 1) := by
  rw [bondState, trace_vecMulVec_mul]
  exact sum_star_bondVec_mul _

/-- Theorem 5 (F3b): the covariance of the bond state is the bond covariance. -/
theorem covariance_bondState :
    covariance bondState = (bond (Fin 1)).submatrix bondLabel bondLabel := by
  have hc := bondAmp_mul_self
  have h01 : (0 : Fin 2) < 1 := by decide
  have h10 : ¬ (1 : Fin 2) < 0 := by decide
  have h00 : ¬ (0 : Fin 2) < 0 := lt_irrefl _
  have h11 : ¬ (1 : Fin 2) < 1 := lt_irrefl _
  have hadd : (1 : Fin 2) + 1 = 0 := by decide
  ext a b
  rcases a with j | j <;> rcases b with k | k <;> fin_cases j <;> fin_cases k
  all_goals first
    | (rw [covariance_diag]
       simp [bondLabel, bond, pairing, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂])
    | (rw [covariance_of_ne _ (by decide), trace_bondState_mul, majorana_mul_mulVec,
         majorana_mul_mulVec]
       simp [bondLabel, bond, pairing, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
         Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, majoranaSign, mode, stringSign,
         Fin.prod_univ_two, bitSign, flip_apply_self, flip_apply_ne, h01, hadd, bondVec,
         funext_iff, Fin.forall_fin_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
         Complex.add_im, Complex.star_def]
       <;> first | linear_combination 2 * hc | linear_combination (-2) * hc)

end Fermionic
