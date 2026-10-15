/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Hamiltonian
import FermionicLean.Gaussian.Congruence
import Mathlib.Analysis.Matrix.Order

/-! # Ground states in the block form

For a diagonal operator the energy of a density operator is at least the least diagonal
entry, with equality only at the minimizing configuration when the gaps are strict. For
`H_{D(ε)}` the minimizer is the occupation state `s^ε` (mode `j` filled iff `ε_j < 0`),
with energy `-(1/2) ∑ |ε_j|` and covariance `D(-sgn ε)`; a rotation by an implemented `O`
carries this to `h = O D(ε) Oᵀ`. On admissible covariances the energy form is bounded below
by the same value, with equality only at `O D(-sgn ε) Oᵀ`.
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

variable {n : ℕ}

/-! ### A diagonal operator -/

section Diagonal

variable {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}

lemma trace_mul_diagonal (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) (d : FockIndex n → ℝ) :
    (ρ * Matrix.diagonal fun s => ((d s : ℝ) : ℂ)).trace = ∑ s, ρ s s * (d s : ℂ) := by
  simp [Matrix.trace, Matrix.mul_diagonal]

lemma IsDensity.diag_re_nonneg (hρ : IsDensity ρ) (s : FockIndex n) : 0 ≤ (ρ s s).re :=
  (Complex.nonneg_iff.mp hρ.1.diag_nonneg).1

lemma IsDensity.diag_im (hρ : IsDensity ρ) (s : FockIndex n) : (ρ s s).im = 0 :=
  (Complex.nonneg_iff.mp hρ.1.diag_nonneg).2.symm

lemma IsDensity.sum_diag_re (hρ : IsDensity ρ) : ∑ s, (ρ s s).re = 1 := by
  have := congrArg Complex.re hρ.2
  simpa [Matrix.trace, Complex.re_sum] using this

lemma re_trace_mul_diagonal (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) (d : FockIndex n → ℝ) :
    (ρ * Matrix.diagonal fun s => ((d s : ℝ) : ℂ)).trace.re = ∑ s, (ρ s s).re * d s := by
  rw [trace_mul_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Complex.mul_re]

/-- Lemma 5: `Tr (ρ D) ≥ d(s⋆)` when `s⋆` minimizes `d`. -/
theorem trace_mul_diagonal_ge (hρ : IsDensity ρ) {d : FockIndex n → ℝ} {s₀ : FockIndex n}
    (hmin : ∀ s, d s₀ ≤ d s) :
    d s₀ ≤ (ρ * Matrix.diagonal fun s => ((d s : ℝ) : ℂ)).trace.re := by
  rw [re_trace_mul_diagonal]
  calc d s₀ = ∑ s, (ρ s s).re * d s₀ := by rw [← Finset.sum_mul, hρ.sum_diag_re, one_mul]
    _ ≤ ∑ s, (ρ s s).re * d s :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hmin s) (hρ.diag_re_nonneg s)

/-- A vanishing diagonal entry of a positive semidefinite matrix kills its column and row. -/
lemma posSemidef_apply_eq_zero_of_diag_eq_zero {ι : Type*} [Finite ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {s : ι} (hs : A s s = 0) (t : ι) :
    A t s = 0 ∧ A s t = 0 := by
  classical
  have := Fintype.ofFinite ι
  have hcol : A *ᵥ Pi.single s (1 : ℂ) = 0 := by
    rw [← hA.dotProduct_mulVec_zero_iff, Matrix.mulVec_single_one, dotProduct_comm]
    have e1 : star (Pi.single s (1 : ℂ) : ι → ℂ) = Pi.single s 1 := by
      funext w; by_cases hw : w = s <;> simp [hw]
    rw [e1, dotProduct_single]
    simpa [Matrix.col] using hs
  have h1 : A t s = 0 := by
    have := congrFun hcol t
    simpa [Matrix.mulVec_single_one, Matrix.col] using this
  refine ⟨h1, ?_⟩
  have := congrFun (congrFun hA.1.eq s) t
  rw [Matrix.conjTranspose_apply, h1, star_zero] at this
  exact this.symm

/-- Lemma 5: a density operator with zero diagonal off `s₀` is `|s₀⟩⟨s₀|`. -/
lemma IsDensity.eq_occupation_of_diag (hρ : IsDensity ρ) {s₀ : FockIndex n}
    (hdiag : ∀ s, s ≠ s₀ → ρ s s = 0) : ρ = occupation s₀ := by
  have hoff : ∀ s t, s ≠ s₀ → ρ s t = 0 ∧ ρ t s = 0 := fun s t hs =>
    ⟨(posSemidef_apply_eq_zero_of_diag_eq_zero hρ.1 (hdiag s hs) t).2,
      (posSemidef_apply_eq_zero_of_diag_eq_zero hρ.1 (hdiag s hs) t).1⟩
  have h00 : ρ s₀ s₀ = 1 := by
    have := hρ.2
    rw [Matrix.trace, Finset.sum_eq_single s₀] at this
    · exact this
    · intro s _ hs; exact hdiag s hs
    · simp
  ext s t
  simp only [occupation, Matrix.single_apply]
  by_cases hs : s = s₀
  · subst hs
    by_cases ht : t = s
    · subst ht; simp [h00]
    · have := (hoff t s (fun h => ht h)).2
      simp [Ne.symm ht, this]
  · have := (hoff s t hs).1
    rw [this]
    split_ifs with h
    · exact absurd h.1.symm hs
    · rfl

/-- Lemma 5: under strict gaps, equality forces the minimizing occupation state. -/
theorem eq_occupation_of_trace_mul_diagonal_eq (hρ : IsDensity ρ) {d : FockIndex n → ℝ}
    {s₀ : FockIndex n} (hmin : ∀ s, d s₀ ≤ d s) (hgap : ∀ s, s ≠ s₀ → d s₀ < d s)
    (heq : (ρ * Matrix.diagonal fun s => ((d s : ℝ) : ℂ)).trace.re = d s₀) :
    ρ = occupation s₀ := by
  apply hρ.eq_occupation_of_diag
  intro s hs
  -- ∑ (ρ s s).re (d s - d s₀) = 0 with nonnegative terms
  have hsum : ∑ t, (ρ t t).re * (d t - d s₀) = 0 := by
    have := re_trace_mul_diagonal ρ d
    rw [heq] at this
    have h1 : ∑ t, (ρ t t).re * d s₀ = d s₀ := by
      rw [← Finset.sum_mul, hρ.sum_diag_re, one_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, ← this, h1, sub_self]
  have hterm : ∀ t, 0 ≤ (ρ t t).re * (d t - d s₀) := fun t =>
    mul_nonneg (hρ.diag_re_nonneg t) (sub_nonneg.mpr (hmin t))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => hterm t).mp hsum s (Finset.mem_univ s)
  have hgap' : d s - d s₀ ≠ 0 := ne_of_gt (sub_pos.mpr (hgap s hs))
  have hre : (ρ s s).re = 0 := (mul_eq_zero.mp hzero).resolve_right hgap'
  exact Complex.ext hre (hρ.diag_im s)

end Diagonal

/-! ### The block form -/

/-- Definition 6: the ground configuration `s^ε_j = 1` iff `ε_j < 0`. -/
noncomputable def groundConfig (ε : Fin n → ℝ) : FockIndex n :=
  fun j => if ε j < 0 then 1 else 0

/-- Definition 6: the ground energy `-(1/2) ∑ |ε_j|`. -/
noncomputable def groundEnergy (ε : Fin n → ℝ) : ℝ := -(1 / 2) * ∑ j, |ε j|

/-- Definition 6: `sgn` with `sgn 0 = 1`. -/
noncomputable def sgn' (t : ℝ) : ℝ := if t < 0 then -1 else 1

lemma abs_eq_sgn'_mul (t : ℝ) : |t| = sgn' t * t := by
  unfold sgn'; split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma occupationSignEntry_groundConfig (ε : Fin n → ℝ) (j : Fin n) :
    occupationSignEntry (groundConfig ε j) = -sgn' (ε j) := by
  unfold groundConfig occupationSignEntry sgn'
  split_ifs <;> simp_all

/-- Definition 6: `σ(s^ε) = -sgn ε`. -/
lemma covariance_occupation_groundConfig (ε : Fin n → ℝ) :
    covariance (occupation (groundConfig ε)) = blockForm fun j => -sgn' (ε j) := by
  rw [covariance_occupation_eq_blockForm]
  simp only [occupationSignEntry_groundConfig]

lemma blockEnergy_groundConfig (ε : Fin n → ℝ) :
    blockEnergy ε (groundConfig ε) = groundEnergy ε := by
  unfold blockEnergy groundEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold groundConfig
  split_ifs with h
  · rw [abs_of_neg h]; simp; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; simp; ring

/-- Each mode contributes `|ε_j|` to the gap when its bit differs from `s^ε_j`. -/
lemma blockEnergy_sub_groundConfig (ε : Fin n → ℝ) (s : FockIndex n) :
    blockEnergy ε s - groundEnergy ε =
      ∑ j, if s j = groundConfig ε j then 0 else |ε j| := by
  rw [← blockEnergy_groundConfig, blockEnergy, blockEnergy, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold groundConfig
  generalize hb : s j = b
  by_cases h1 : ε j < 0
  · rw [abs_of_neg h1]
    fin_cases b <;> (simp [h1]; try ring)
  · rw [abs_of_nonneg (not_lt.mp h1)]
    fin_cases b <;> (simp [h1]; try ring)

lemma groundEnergy_le_blockEnergy (ε : Fin n → ℝ) (s : FockIndex n) :
    groundEnergy ε ≤ blockEnergy ε s := by
  have := blockEnergy_sub_groundConfig ε s
  have hnn : 0 ≤ ∑ j, if s j = groundConfig ε j then 0 else |ε j| :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> simp [abs_nonneg]
  linarith

lemma groundEnergy_lt_blockEnergy (ε : Fin n → ℝ) (hε : ∀ j, ε j ≠ 0) (s : FockIndex n)
    (hs : s ≠ groundConfig ε) :
    groundEnergy ε < blockEnergy ε s := by
  have := blockEnergy_sub_groundConfig ε s
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ groundConfig ε j := by
    by_contra hall; push Not at hall; exact hs (funext hall)
  have hpos : 0 < ∑ k, if s k = groundConfig ε k then 0 else |ε k| := by
    apply Finset.sum_pos' (fun k _ => by split_ifs <;> simp [abs_nonneg])
    exact ⟨j, Finset.mem_univ j, by simp [hj, abs_pos.mpr (hε j)]⟩
  linarith

variable {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}

/-- Theorem 7(a): `Tr (ρ H_{D(ε)}) ≥ E_0(ε)`. -/
theorem groundEnergy_le_energy_blockForm (ε : Fin n → ℝ) (hρ : IsDensity ρ) :
    groundEnergy ε ≤ energy (blockForm ε) ρ := by
  unfold energy
  rw [quadHam_blockForm, ← blockEnergy_groundConfig]
  exact trace_mul_diagonal_ge hρ fun s => by
    rw [blockEnergy_groundConfig]; exact groundEnergy_le_blockEnergy ε s

/-- Theorem 7(a): the ground configuration attains `E_0(ε)`. -/
theorem energy_blockForm_groundConfig (ε : Fin n → ℝ) :
    energy (blockForm ε) (occupation (groundConfig ε)) = groundEnergy ε := by
  unfold energy
  rw [quadHam_blockForm, re_trace_mul_diagonal, Finset.sum_eq_single (groundConfig ε)]
  · simp [occupation, blockEnergy_groundConfig]
  · intro s _ hs; simp [occupation, Ne.symm hs]
  · simp

/-- Theorem 7(b): with no zero `ε_j`, equality forces `ρ = |s^ε⟩⟨s^ε|`. -/
theorem eq_occupation_of_energy_blockForm_eq (ε : Fin n → ℝ) (hε : ∀ j, ε j ≠ 0)
    (hρ : IsDensity ρ) (heq : energy (blockForm ε) ρ = groundEnergy ε) :
    ρ = occupation (groundConfig ε) := by
  unfold energy at heq
  rw [quadHam_blockForm] at heq
  refine eq_occupation_of_trace_mul_diagonal_eq hρ (d := blockEnergy ε) (s₀ := groundConfig ε)
    ?_ ?_ ?_
  · intro s; rw [blockEnergy_groundConfig]; exact groundEnergy_le_blockEnergy ε s
  · intro s hs; rw [blockEnergy_groundConfig]; exact groundEnergy_lt_blockEnergy ε hε s hs
  · rw [heq, blockEnergy_groundConfig]

/-! ### Rotated block forms -/

section Rotated

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {ε : Fin n → ℝ}

/-- `Uᴴ H_{D(ε)} U = H_{O D(ε) Oᵀ}` when `U` implements `O`. -/
lemma conjTranspose_mul_quadHam_blockForm_mul (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    U.conjTranspose * quadHam (blockForm ε) * U = quadHam (O * blockForm ε * O.transpose) := by
  have hOtO : O.transpose * O = 1 := mul_eq_one_comm.mp hOO
  have hh : O.transpose * (O * blockForm ε * O.transpose) * O = blockForm ε := by
    calc O.transpose * (O * blockForm ε * O.transpose) * O
        = (O.transpose * O) * blockForm ε * (O.transpose * O) := by simp only [Matrix.mul_assoc]
      _ = blockForm ε := by rw [hOtO, Matrix.one_mul, Matrix.mul_one]
  have hc := conj_quadHam (h := O * blockForm ε * O.transpose) hU' hO
  rw [hh] at hc
  rw [← hc]
  calc U.conjTranspose * (U * quadHam (O * blockForm ε * O.transpose) * U.conjTranspose) * U
      = (U.conjTranspose * U) * quadHam (O * blockForm ε * O.transpose) *
          (U.conjTranspose * U) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU', Matrix.one_mul, Matrix.mul_one]

/-- `Tr(ρ H_{O D(ε) Oᵀ}) = Tr((U ρ Uᴴ) H_{D(ε)})`. -/
lemma energy_conj (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1)
    (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    energy (O * blockForm ε * O.transpose) ρ = energy (blockForm ε) (U * ρ * U.conjTranspose) := by
  unfold energy
  rw [← conjTranspose_mul_quadHam_blockForm_mul hU' hO hOO]
  congr 1
  calc (ρ * (U.conjTranspose * quadHam (blockForm ε) * U)).trace
      = ((ρ * U.conjTranspose * quadHam (blockForm ε)) * U).trace := by
        simp only [Matrix.mul_assoc]
    _ = (U * (ρ * U.conjTranspose * quadHam (blockForm ε))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Theorem 8: the ground state `ρ₀ = Uᴴ |s^ε⟩⟨s^ε| U`. -/
noncomputable def groundState (U : Matrix (FockIndex n) (FockIndex n) ℂ) (ε : Fin n → ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  U.conjTranspose * occupation (groundConfig ε) * U

variable {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}

/-- Theorem 8(a): `Tr(ρ H_h) ≥ E_0(ε)` for `h = O D(ε) Oᵀ`. -/
theorem groundEnergy_le_energy (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) (hρ : IsDensity ρ) :
    groundEnergy ε ≤ energy (O * blockForm ε * O.transpose) ρ := by
  rw [energy_conj hU' hO hOO]
  exact groundEnergy_le_energy_blockForm ε (covariance_conj hU hU' hO hρ).1

/-- `Uᴴ` implements `Oᵀ`. -/
lemma conjugatesMajorana_conjTranspose (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) : ConjugatesMajorana U.conjTranspose O.transpose := by
  intro a
  rw [Matrix.conjTranspose_conjTranspose, conjTranspose_mul_majorana_mul hU' hO]
  simp only [Matrix.transpose_apply]

lemma covariance_conj' (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) {σ : Matrix (FockIndex n) (FockIndex n) ℂ} (hσ : IsDensity σ) :
    IsDensity (U.conjTranspose * σ * U) ∧
      covariance (U.conjTranspose * σ * U) = O * covariance σ * O.transpose := by
  have := covariance_conj (U := U.conjTranspose) (O := O.transpose)
    (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
    (by rw [Matrix.conjTranspose_conjTranspose]; exact hU)
    (conjugatesMajorana_conjTranspose hU' hO) hσ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_transpose] at this
  exact this

/-- Theorem 8(b): `ρ₀` is a density operator. -/
theorem isDensity_groundState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) : IsDensity (groundState U ε) :=
  (covariance_conj' hU hU' hO (isDensity_occupation (groundConfig ε))).1

/-- Theorem 8(b): `ρ₀` attains `E_0(ε)`. -/
theorem energy_groundState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1) :
    energy (O * blockForm ε * O.transpose) (groundState U ε) = groundEnergy ε := by
  rw [energy_conj hU' hO hOO]
  unfold groundState
  have : U * (U.conjTranspose * occupation (groundConfig ε) * U) * U.conjTranspose =
      occupation (groundConfig ε) := by
    calc U * (U.conjTranspose * occupation (groundConfig ε) * U) * U.conjTranspose
        = (U * U.conjTranspose) * occupation (groundConfig ε) * (U * U.conjTranspose) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  rw [this, energy_blockForm_groundConfig]

/-- Theorem 8(b): `Γ(ρ₀) = O D(-sgn ε) Oᵀ`. -/
theorem covariance_groundState (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) :
    covariance (groundState U ε) = O * blockForm (fun j => -sgn' (ε j)) * O.transpose := by
  unfold groundState
  rw [(covariance_conj' hU hU' hO (isDensity_occupation (groundConfig ε))).2,
    covariance_occupation_groundConfig]

/-- Theorem 8(c): with no zero `ε_j`, equality forces `ρ = ρ₀`. -/
theorem eq_groundState_of_energy_eq (hU : U * U.conjTranspose = 1)
    (hU' : U.conjTranspose * U = 1) (hO : ConjugatesMajorana U O) (hOO : O * O.transpose = 1)
    (hε : ∀ j, ε j ≠ 0) (hρ : IsDensity ρ)
    (heq : energy (O * blockForm ε * O.transpose) ρ = groundEnergy ε) :
    ρ = groundState U ε := by
  rw [energy_conj hU' hO hOO] at heq
  have h1 := eq_occupation_of_energy_blockForm_eq ε hε (covariance_conj hU hU' hO hρ).1 heq
  unfold groundState
  rw [← h1]
  calc ρ = (U.conjTranspose * U) * ρ * (U.conjTranspose * U) := by
        rw [hU', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end Rotated

/-! ### The variational bound on covariances -/

section Variational

/-- The energy form on covariances, `(1/4) ∑ h_ab Γ_ab`. -/
noncomputable def energyForm (h Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : ℝ :=
  1 / 4 * ∑ a, ∑ b, h a b * Γ a b

lemma energy_eq_energyForm {h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hh : h.transpose = -h) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : ρ.IsHermitian) :
    energy h ρ = energyForm h (covariance ρ) := by
  rw [energy_eq hh hρ]; rfl

/-- The squared norm of a column of `Γ`. -/
lemma column_sq_le_one {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsAdmissible Γ) (b : MajoranaIndex n) : ∑ i, Γ i b * Γ i b ≤ 1 := by
  have hn := (isAdmissible_iff_norm hΓ.1).mp hΓ (Pi.single b 1)
  rw [Matrix.mulVec_single_one, dotProduct_single_one] at hn
  simpa [Matrix.col, dotProduct] using hn

/-- Every entry of an admissible matrix has modulus at most one. -/
lemma abs_apply_le_one_of_isAdmissible {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsAdmissible Γ) (a b : MajoranaIndex n) : |Γ a b| ≤ 1 := by
  have hsq : Γ a b * Γ a b ≤ ∑ i, Γ i b * Γ i b :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (Γ i b)) (Finset.mem_univ a)
  rw [abs_le_one_iff_sq_le]
  linarith [column_sq_le_one hΓ b]

/-- A column of an admissible matrix with an entry of modulus one vanishes elsewhere. -/
lemma apply_eq_zero_of_abs_eq_one {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsAdmissible Γ) {a b : MajoranaIndex n} (hab : |Γ a b| = 1) (c : MajoranaIndex n)
    (hc : c ≠ a) : Γ c b = 0 := by
  have h1 : Γ a b * Γ a b = 1 := (abs_eq_one_iff_sq_eq _).mp hab
  have hsum : ∑ i, Γ i b * Γ i b = Γ a b * Γ a b + ∑ i ∈ Finset.univ.erase a, Γ i b * Γ i b :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  have hrest : ∑ i ∈ Finset.univ.erase a, Γ i b * Γ i b = 0 := by
    have hnn : 0 ≤ ∑ i ∈ Finset.univ.erase a, Γ i b * Γ i b :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith [column_sq_le_one hΓ b]
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (Γ i b)).mp hrest c
    (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
  exact mul_self_eq_zero.mp this

/-- `∑_{ab} (O D Oᵀ)_ab Γ_ab = ∑_{cd} D_cd (Oᵀ Γ O)_cd`. -/
lemma sum_rotated_mul (O D Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    ∑ a, ∑ b, (O * D * O.transpose) a b * Γ a b =
      ∑ c, ∑ d, D c d * (O.transpose * Γ * O) c d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  -- left: ∑ a ∑ b ∑ d ∑ c (O a c * D c d) * O b d * Γ a b
  -- right: ∑ c ∑ d ∑ b ∑ a  D c d * (O a c * Γ a b * O b d)   (after unfolding)
  calc ∑ a, ∑ b, ∑ d, ∑ c, O a c * D c d * O b d * Γ a b
      = ∑ a, ∑ b, ∑ c, ∑ d, O a c * D c d * O b d * Γ a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ b, ∑ d, O a c * D c d * O b d * Γ a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, O a c * D c d * O b d * Γ a b := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, O a c * D c d * O b d * Γ a b := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, O a c * D c d * O b d * Γ a b := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, D c d * (O a c * Γ a b * O b d) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- The energy form of `O D(ε) Oᵀ` on `Γ` is `(1/2) ∑_j ε_j Γ'_{x_j y_j}` with `Γ' = Oᵀ Γ O`. -/
lemma energyForm_rotated (O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ)
    (hΓ : Γ.transpose = -Γ) :
    energyForm (O * blockForm ε * O.transpose) Γ =
      1 / 2 * ∑ j, ε j * (O.transpose * Γ * O) (Sum.inl j) (Sum.inr j) := by
  unfold energyForm
  rw [sum_rotated_mul]
  set Γ' := O.transpose * Γ * O with hΓ'
  have hanti : Γ'.transpose = -Γ' := by
    rw [hΓ', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hΓ,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hswap : ∀ j, Γ' (Sum.inr j) (Sum.inl j) = -Γ' (Sum.inl j) (Sum.inr j) := fun j => by
    have := congrFun (congrFun hanti (Sum.inl j)) (Sum.inr j)
    simpa [Matrix.transpose_apply] using this
  simp only [blockForm, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
    Matrix.diagonal_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  simp only [ite_mul, zero_mul, neg_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_neg_distrib, hswap, mul_neg, neg_neg]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} {ε : Fin n → ℝ}

/-- Theorem 9: the energy form on admissible covariances is at least `E_0(ε)`. -/
theorem groundEnergy_le_energyForm (hOO : O * O.transpose = 1) (hΓ : IsAdmissible Γ) :
    groundEnergy ε ≤ energyForm (O * blockForm ε * O.transpose) Γ := by
  rw [energyForm_rotated O Γ ε hΓ.1, groundEnergy]
  have hΓ' : IsAdmissible (O.transpose * Γ * O) := by
    have := isAdmissible_orthogonalCongruence (O := O.transpose)
      (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hOO) hΓ
    rwa [Matrix.transpose_transpose] at this
  have hterm : ∀ j, -|ε j| ≤ ε j * (O.transpose * Γ * O) (Sum.inl j) (Sum.inr j) := fun j => by
    have hb := abs_apply_le_one_of_isAdmissible hΓ' (Sum.inl j) (Sum.inr j)
    have := neg_abs_le (ε j * (O.transpose * Γ * O) (Sum.inl j) (Sum.inr j))
    rw [abs_mul] at this
    nlinarith [abs_nonneg (ε j), abs_nonneg ((O.transpose * Γ * O) (Sum.inl j) (Sum.inr j))]
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [Finset.sum_neg_distrib] at this
  linarith

/-- The pinning step of Theorem 9: with `Γ'` admissible and `ε_j ≠ 0`, equality of the `j`-th
term forces `Γ'_{x_j y_j} = -sgn ε_j`. -/
lemma entry_eq_of_term_eq {j : Fin n} (hj : ε j ≠ 0)
    (heq : ε j * Γ (Sum.inl j) (Sum.inr j) = -|ε j|) :
    Γ (Sum.inl j) (Sum.inr j) = -sgn' (ε j) := by
  rw [abs_eq_sgn'_mul] at heq
  have hs : sgn' (ε j) * sgn' (ε j) = 1 := by unfold sgn'; split_ifs <;> norm_num
  have : ε j * (Γ (Sum.inl j) (Sum.inr j) + sgn' (ε j)) = 0 := by linarith
  have h2 := (mul_eq_zero.mp this).resolve_left hj
  linarith

/-- Theorem 9: with no zero `ε_j`, equality holds iff `Γ = O D(-sgn ε) Oᵀ`. -/
theorem energyForm_eq_groundEnergy_iff (hOO : O * O.transpose = 1) (hΓ : IsAdmissible Γ)
    (hε : ∀ j, ε j ≠ 0) :
    energyForm (O * blockForm ε * O.transpose) Γ = groundEnergy ε ↔
      Γ = O * blockForm (fun j => -sgn' (ε j)) * O.transpose := by
  have hOtO : O.transpose * O = 1 := mul_eq_one_comm.mp hOO
  have hΓ' : IsAdmissible (O.transpose * Γ * O) := by
    have := isAdmissible_orthogonalCongruence (O := O.transpose)
      (by rw [Matrix.transpose_transpose]; exact hOtO) hΓ
    rwa [Matrix.transpose_transpose] at this
  set Γ' := O.transpose * Γ * O with hΓ'def
  have hback : Γ = O * Γ' * O.transpose := by
    rw [hΓ'def]
    calc Γ = (O * O.transpose) * Γ * (O * O.transpose) := by rw [hOO]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  constructor
  · intro heq
    rw [energyForm_rotated O Γ ε hΓ.1, groundEnergy] at heq
    -- every term attains its bound
    have hterm : ∀ j, -|ε j| ≤ ε j * Γ' (Sum.inl j) (Sum.inr j) := fun j => by
      have hb := abs_apply_le_one_of_isAdmissible hΓ' (Sum.inl j) (Sum.inr j)
      have := neg_abs_le (ε j * Γ' (Sum.inl j) (Sum.inr j))
      rw [abs_mul] at this
      nlinarith [abs_nonneg (ε j), abs_nonneg (Γ' (Sum.inl j) (Sum.inr j))]
    have hsum : ∑ j, (ε j * Γ' (Sum.inl j) (Sum.inr j) + |ε j|) = 0 := by
      rw [Finset.sum_add_distrib]; linarith
    have hall : ∀ j, ε j * Γ' (Sum.inl j) (Sum.inr j) = -|ε j| := fun j => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by linarith [hterm j]).mp hsum j
        (Finset.mem_univ j)
      linarith
    have hxy : ∀ j, Γ' (Sum.inl j) (Sum.inr j) = -sgn' (ε j) := fun j =>
      entry_eq_of_term_eq (hε j) (hall j)
    have hyx : ∀ j, Γ' (Sum.inr j) (Sum.inl j) = sgn' (ε j) := fun j => by
      have := congrFun (congrFun hΓ'.1 (Sum.inl j)) (Sum.inr j)
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this, hxy, neg_neg]
    have habs : ∀ j, |sgn' (ε j)| = 1 := fun j => by unfold sgn'; split_ifs <;> simp
    -- the columns y_j and x_j are pinned
    have hcol : Γ' = blockForm fun j => -sgn' (ε j) := by
      ext (a | a) (b | b)
      · -- (x_a, x_b): column x_b has the entry sgn' at y_b
        have := apply_eq_zero_of_abs_eq_one hΓ' (a := Sum.inr b) (b := Sum.inl b)
          (by rw [hyx, habs]) (Sum.inl a) Sum.inl_ne_inr
        simp [blockForm, this]
      · by_cases hab : a = b
        · subst hab; simp [blockForm, hxy]
        · have := apply_eq_zero_of_abs_eq_one hΓ' (a := Sum.inl b) (b := Sum.inr b)
            (by rw [hxy, abs_neg, habs]) (Sum.inl a) (fun h => hab (Sum.inl_injective h))
          simp [blockForm, this, hab]
      · by_cases hab : a = b
        · subst hab; simp [blockForm, hyx]
        · have := apply_eq_zero_of_abs_eq_one hΓ' (a := Sum.inr b) (b := Sum.inl b)
            (by rw [hyx, habs]) (Sum.inr a) (fun h => hab (Sum.inr_injective h))
          simp [blockForm, this, hab]
      · have := apply_eq_zero_of_abs_eq_one hΓ' (a := Sum.inl b) (b := Sum.inr b)
          (by rw [hxy, abs_neg, habs]) (Sum.inr a) Sum.inr_ne_inl
        simp [blockForm, this]
    rw [hback, hcol]
  · rintro rfl
    rw [energyForm_rotated _ _ _ (orthogonalCongruence_transpose (blockForm_transpose _)),
      groundEnergy]
    have hmid : O.transpose * (O * blockForm (fun j => -sgn' (ε j)) * O.transpose) * O =
        blockForm fun j => -sgn' (ε j) := by
      calc O.transpose * (O * blockForm (fun j => -sgn' (ε j)) * O.transpose) * O
          = (O.transpose * O) * blockForm (fun j => -sgn' (ε j)) * (O.transpose * O) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hOtO, Matrix.one_mul, Matrix.mul_one]
    rw [hmid]
    simp only [blockForm, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_eq_sgn'_mul]
    ring

end Variational

/-! ### The rotated frame in one statement -/

/-- Lemma 7.9 of the notes as one statement: energy and admissibility in the rotated frame. -/
theorem rotatedFrame (O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ)
    (hOO : O * O.transpose = 1) (hΓ : Γ.transpose = -Γ) :
    (O.transpose * Γ * O).transpose = -(O.transpose * Γ * O) ∧
    (IsAdmissible (O.transpose * Γ * O) ↔ IsAdmissible Γ) ∧
    (IsPure (O.transpose * Γ * O) ↔ IsPure Γ) ∧
    energyForm (O * blockForm ε * O.transpose) Γ =
      1 / 2 * ∑ j, ε j * (O.transpose * Γ * O) (Sum.inl j) (Sum.inr j) ∧
    (∀ lam : Fin n → ℝ, Γ = O * blockForm lam * O.transpose →
      O.transpose * Γ * O = blockForm lam ∧
      energyForm (O * blockForm ε * O.transpose) Γ = 1 / 2 * ∑ j, ε j * lam j) := by
  have hOtO : O.transpose * O.transpose.transpose = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hOO
  have hback : O * (O.transpose * Γ * O) * O.transpose = Γ := by
    calc O * (O.transpose * Γ * O) * O.transpose
        = (O * O.transpose) * Γ * (O * O.transpose) := by simp only [Matrix.mul_assoc]
      _ = Γ := by rw [hOO, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩,
    energyForm_rotated O Γ ε hΓ, fun lam hlam => ?_⟩
  · have := orthogonalCongruence_transpose (O := O.transpose) hΓ
    rwa [Matrix.transpose_transpose] at this
  · have := isAdmissible_orthogonalCongruence hOO h
    rwa [hback] at this
  · have := isAdmissible_orthogonalCongruence hOtO h
    rwa [Matrix.transpose_transpose] at this
  · have := isPure_orthogonalCongruence hOO h
    rwa [hback] at this
  · have := isPure_orthogonalCongruence hOtO h
    rwa [Matrix.transpose_transpose] at this
  · have hblock : O.transpose * Γ * O = blockForm lam := by
      rw [hlam]
      calc O.transpose * (O * blockForm lam * O.transpose) * O
          = (O.transpose * O) * blockForm lam * (O.transpose * O) := by
            simp only [Matrix.mul_assoc]
        _ = blockForm lam := by
            rw [mul_eq_one_comm.mp hOO, Matrix.one_mul, Matrix.mul_one]
    refine ⟨hblock, ?_⟩
    rw [energyForm_rotated O Γ ε hΓ, hblock]
    simp only [blockForm, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq]

end Fermionic
