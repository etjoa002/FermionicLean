/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.Periodic
import Mathlib.Analysis.Fourier.ZMod

/-! # Fourier representation of homogeneous periodic chains

When every site carries the same local matrix `Γ`, the discrete Fourier transform over
sites turns the periodic covariance into `N` independent blocks. The block at momentum
`k` is the contraction, over `ℂ`, of the *twisted* local matrix (the phase `ω_k` on the
`B` labels) against the bond of a single site.
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

variable {N M P : ℕ}

/-! ### Characters and the twisted local matrix -/

/-- Definition 1: the character `χ_k(i) = exp(-2πi k i / N)`. -/
noncomputable def character (k i : Fin N) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) * (i.val : ℂ) / (N : ℂ))

/-- Definition 1: the phase `ω_k = χ_k(1) = exp(-2πi k / N)` of a shift by one site. -/
noncomputable def sitePhase (k : Fin N) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ))

/-- Definition 1: the twist, `ω_k` on the `B` labels (`x` and `y` alike), `1` otherwise. -/
noncomputable def twist (k : Fin N) : SiteLabel M P → ℂ
  | Sum.inl (Sum.inl (Sum.inr _)) => sitePhase k
  | Sum.inr (Sum.inl (Sum.inr _)) => sitePhase k
  | _ => 1

/-- Definition 1: the twisted local matrix `diag(t_k) Γ diag(t_k)^*`. -/
noncomputable def twistedLocal (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) (k : Fin N) :
    Matrix (SiteLabel M P) (SiteLabel M P) ℂ :=
  Matrix.diagonal (twist k) * Γ.map Complex.ofReal * (Matrix.diagonal (twist k)).conjTranspose

/-! ### The single-site split and the momentum-space covariance -/

/-- Labels of one site in the retained–eliminated split: `(x_C, y_C)` then
`(x_L, x_L', y_L, y_L')`. -/
abbrev SiteSplit (M P : ℕ) := (Fin P ⊕ Fin P) ⊕ PairIndex (Fin M)

/-- The split of one site's labels: `x_C, y_C` to the physical labels, and
`(x_L, x_L', y_L, y_L')` to `(x_A, x_B, y_A, y_B)`. -/
def siteSplit (M P : ℕ) : SiteSplit M P ≃ SiteLabel M P where
  toFun
    | Sum.inl (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inr c)
    | Sum.inr (Sum.inl (Sum.inl a)) => Sum.inl (Sum.inl (Sum.inl a))
    | Sum.inr (Sum.inl (Sum.inr a)) => Sum.inl (Sum.inl (Sum.inr a))
    | Sum.inr (Sum.inr (Sum.inl a)) => Sum.inr (Sum.inl (Sum.inl a))
    | Sum.inr (Sum.inr (Sum.inr a)) => Sum.inr (Sum.inl (Sum.inr a))
  invFun
    | Sum.inl (Sum.inr c) => Sum.inl (Sum.inl c)
    | Sum.inr (Sum.inr c) => Sum.inl (Sum.inr c)
    | Sum.inl (Sum.inl (Sum.inl a)) => Sum.inr (Sum.inl (Sum.inl a))
    | Sum.inl (Sum.inl (Sum.inr a)) => Sum.inr (Sum.inl (Sum.inr a))
    | Sum.inr (Sum.inl (Sum.inl a)) => Sum.inr (Sum.inr (Sum.inl a))
    | Sum.inr (Sum.inl (Sum.inr a)) => Sum.inr (Sum.inr (Sum.inr a))
  left_inv := by rintro ((c | c) | (a | a) | (a | a)) <;> rfl
  right_inv := by rintro (((a | a) | c) | ((a | a) | c)) <;> rfl

/-- The twisted local matrix in the split `(x_C, y_C) ⊕ (x_L, x_L', y_L, y_L')`. -/
noncomputable def twistedSplit (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) (k : Fin N) :
    Matrix (SiteSplit M P) (SiteSplit M P) ℂ :=
  (twistedLocal Γ k).submatrix (siteSplit M P) (siteSplit M P)

/-- The bond of a single site's `M` virtual modes, as a complex matrix. -/
noncomputable def bondC (M : ℕ) : Matrix (PairIndex (Fin M)) (PairIndex (Fin M)) ℂ :=
  (bond (Fin M)).map Complex.ofReal

/-- The contraction formula of F3a over `ℂ`. -/
noncomputable def contractC {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (Γp : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  Γ.toBlocks₁₁ + Γ.toBlocks₁₂ * Γp * (1 - Γ.toBlocks₂₂ * Γp)⁻¹ * Γ.toBlocks₂₁

/-- Definition 2: the momentum-space covariance
`Σ(k) = A_k + B_k β_M (1 - D_k β_M)⁻¹ C_k`. -/
noncomputable def momentumCovariance (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (k : Fin N) : Matrix (Fin P ⊕ Fin P) (Fin P ⊕ Fin P) ℂ :=
  contractC (twistedSplit Γ k) (bondC M)

/-! ### Fourier coefficients of the chain -/

/-- The retained label `(i, a)` of the physical label `a` at site `i`. -/
def retained (i : Fin N) : Fin P ⊕ Fin P → Retained N P
  | Sum.inl c => Sum.inl (i, c)
  | Sum.inr c => Sum.inr (i, c)

/-- The periodic covariance of the homogeneous chain data `Γ, …, Γ`. -/
noncomputable def homogeneousCovariance (N : ℕ) (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    Matrix (Retained N P) (Retained N P) ℝ :=
  periodicCovariance (fun _ : Fin N => Γ)

/-- Definition 3: the Fourier coefficient
`Γ̂_N(k,l)_{ab} = N⁻¹ ∑_{i j} χ_k(i) (Γ_N)_{(i,a)(j,b)} conj χ_l(j)`. -/
noncomputable def fourierEntry (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (k l : Fin N) (a b : Fin P ⊕ Fin P) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    character k i * ((homogeneousCovariance N Γ (retained i a) (retained j b) : ℝ) : ℂ) *
      star (character l j)

/-! ### Character identities -/

section Characters

variable [NeZero N]

private def toZMod (i : Fin N) : ZMod N := i.val

private def finZModEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun := toZMod
  invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
  left_inv := by
    intro i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv := by
    intro z
    exact ZMod.natCast_zmod_val z

private lemma character_eq_stdAddChar (k i : Fin N) :
    character k i = ZMod.stdAddChar (-(toZMod i * toZMod k)) := by
  calc
    character k i =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((-((i.val * k.val : ℕ) : ℤ) : ℤ) : ℂ) / (N : ℂ)) := by
      rw [character]
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar (((-((i.val * k.val : ℕ) : ℤ) : ℤ) : ZMod N)) :=
      (ZMod.stdAddChar_coe (N := N) (-((i.val * k.val : ℕ) : ℤ))).symm
    _ = ZMod.stdAddChar (-(toZMod i * toZMod k)) := by
      congr 1
      simp [toZMod]

private lemma sitePhase_eq_stdAddChar (k : Fin N) :
    sitePhase k = ZMod.stdAddChar (-(toZMod k)) := by
  calc
    sitePhase k =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(k.val : ℤ) : ℂ) / (N : ℂ)) := by
      rw [sitePhase]
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar ((-(k.val : ℤ) : ℤ) : ZMod N) :=
      by simpa only [Int.cast_neg, Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := N) (-(k.val : ℤ))).symm
    _ = ZMod.stdAddChar (-(toZMod k)) := by
      congr 1
      simp [toZMod]

omit [NeZero N] in
private lemma toZMod_finRotate (i : Fin N) : toZMod (finRotate N i) = toZMod i + 1 := by
  rw [finRotate_apply]
  simp [toZMod, Fin.val_add, ZMod.natCast_mod]

omit [NeZero N] in
private lemma toZMod_neg (k : Fin N) : toZMod (-k) = -toZMod k := by
  simp only [toZMod]
  rw [Fin.val_neg']
  rcases Nat.eq_zero_or_pos k.val with h | h
  · simp [h]
  · rw [Nat.mod_eq_of_lt (by omega)]
    have hk : k.val ≤ N := k.isLt.le
    rw [Nat.cast_sub hk]
    simp

private lemma star_stdAddChar (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ← starRingEnd_apply, ← Circle.coe_inv_eq_conj]
  congr 1
  exact (ZMod.toCircle).map_neg_eq_inv x |>.symm

/-- Shifting the site by one multiplies the character by the site phase. -/
lemma character_finRotate (k i : Fin N) :
    character k (finRotate N i) = character k i * sitePhase k := by
  rw [character_eq_stdAddChar, character_eq_stdAddChar, sitePhase_eq_stdAddChar,
    toZMod_finRotate, ← AddChar.map_add_eq_mul]
  congr 1
  ring

lemma character_finRotate_symm (k i : Fin N) :
    character k ((finRotate N).symm i) = character k i * star (sitePhase k) := by
  have := character_finRotate k ((finRotate N).symm i)
  rw [Equiv.apply_symm_apply] at this
  rw [this, mul_assoc, sitePhase_eq_stdAddChar, star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

lemma star_character (k i : Fin N) :
    star (character k i) = character (-k) i := by
  rw [character_eq_stdAddChar, character_eq_stdAddChar, star_stdAddChar, toZMod_neg]
  congr 1
  ring

lemma sitePhase_neg (k : Fin N) : sitePhase (-k) = star (sitePhase k) := by
  rw [sitePhase_eq_stdAddChar, sitePhase_eq_stdAddChar, star_stdAddChar, toZMod_neg]

lemma sitePhase_mul_star (k : Fin N) : sitePhase k * star (sitePhase k) = 1 := by
  rw [sitePhase_eq_stdAddChar, star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

/-- Orthogonality of the characters in the site index. -/
lemma sum_character_mul_star (k l : Fin N) :
    (∑ i : Fin N, character k i * star (character l i)) = if k = l then (N : ℂ) else 0 := by
  classical
  calc
    _ = ∑ i : Fin N, ZMod.stdAddChar (toZMod i * (toZMod l - toZMod k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [character_eq_stdAddChar, character_eq_stdAddChar, star_stdAddChar,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ z : ZMod N, ZMod.stdAddChar (z * (toZMod l - toZMod k)) :=
      Fintype.sum_equiv (finZModEquiv N) _ _ (fun _ => rfl)
    _ = if toZMod l - toZMod k = 0 then (N : ℂ) else 0 := by
      simpa [ZMod.card] using
        AddChar.sum_mulShift (toZMod l - toZMod k) (ZMod.isPrimitive_stdAddChar N)
    _ = _ := by
      have heq : toZMod l - toZMod k = 0 ↔ k = l := by
        rw [sub_eq_zero]
        exact (finZModEquiv N).injective.eq_iff.trans eq_comm
      simp only [heq]

omit [NeZero N] in
private lemma character_comm (k i : Fin N) : character k i = character i k := by
  unfold character
  congr 1
  ring

/-- Orthogonality of the characters in the momentum index. -/
lemma sum_star_character_mul (i j : Fin N) :
    (∑ k : Fin N, star (character k i) * character k j) = if i = j then (N : ℂ) else 0 := by
  calc
    _ = ∑ k : Fin N, character j k * star (character i k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [character_comm k i, character_comm k j, mul_comm]
    _ = _ := by rw [sum_character_mul_star]; simp [eq_comm]

end Characters

/-! ### The complex contraction under relabelling, block sums and conjugation -/

section ContractC

variable {ι κ ι' κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

omit [Fintype ι] [DecidableEq ι] in
lemma contractC_fromBlocks (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (D : Matrix κ κ ℂ) (Γp : Matrix κ κ ℂ) :
    contractC (Matrix.fromBlocks A B C D) Γp = A + B * Γp * (1 - D * Γp)⁻¹ * C := by
  simp [contractC]

/-- The inverse of a two-sided conjugate. -/
lemma inv_conj_of_isUnit_det {X : Matrix κ κ ℂ} (hX : IsUnit X.det)
    {Pm : Matrix κ' κ ℂ} {Qm : Matrix κ κ' ℂ} (hPQ : Pm * Qm = 1) (hQP : Qm * Pm = 1) :
    (Pm * X * Qm)⁻¹ = Pm * X⁻¹ * Qm := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_assoc (Pm * X) Qm, ← Matrix.mul_assoc Qm (Pm * X⁻¹) Qm,
    ← Matrix.mul_assoc Qm Pm X⁻¹, hQP, Matrix.one_mul, ← Matrix.mul_assoc (Pm * X) X⁻¹ Qm,
    Matrix.mul_assoc Pm X X⁻¹, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, hPQ]

/-- Step 3: the contraction formula commutes with a two-sided relabelling of the retained
and eliminated labels. -/
lemma contractC_conj (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (C : Matrix κ ι ℂ)
    (D : Matrix κ κ ℂ) (Γp : Matrix κ κ ℂ) (hinv : IsUnit (1 - D * Γp).det)
    {PR : Matrix ι' ι ℂ} {QR : Matrix ι ι' ℂ} {PE : Matrix κ' κ ℂ} {QE : Matrix κ κ' ℂ}
    (_hRR : PR * QR = 1) (_hRR' : QR * PR = 1) (hEE : PE * QE = 1) (hEE' : QE * PE = 1) :
    contractC (Matrix.fromBlocks (PR * A * QR) (PR * B * QE) (PE * C * QR) (PE * D * QE))
        (PE * Γp * QE) =
      PR * contractC (Matrix.fromBlocks A B C D) Γp * QR := by
  rw [contractC_fromBlocks, contractC_fromBlocks]
  have h1 : (1 : Matrix κ' κ' ℂ) - PE * D * QE * (PE * Γp * QE) = PE * (1 - D * Γp) * QE := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hEE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc QE PE, hEE', Matrix.one_mul]
  rw [h1, inv_conj_of_isUnit_det hinv hEE hEE']
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  congr 1
  simp only [← Matrix.mul_assoc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc QE PE, hEE', Matrix.one_mul, ← Matrix.mul_assoc QE PE, hEE',
    Matrix.one_mul, ← Matrix.mul_assoc QE PE, hEE', Matrix.one_mul]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma blockDiagonal_inv (X : σ → Matrix κ κ ℂ) (h : ∀ k, IsUnit (X k).det) :
    (Matrix.blockDiagonal X)⁻¹ = Matrix.blockDiagonal (fun k => (X k)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one]
  congr 1
  ext k : 1
  exact Matrix.mul_nonsing_inv _ (h k)

lemma det_one_sub_blockDiagonal_mul (D Γp : σ → Matrix κ κ ℂ) :
    (1 - Matrix.blockDiagonal D * Matrix.blockDiagonal Γp).det =
      ∏ k, (1 - D k * Γp k).det := by
  rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub,
    Matrix.det_blockDiagonal]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Step 4: the contraction of block sums is the block sum of the contractions. -/
lemma contractC_blockDiagonal (A : σ → Matrix ι ι ℂ) (B : σ → Matrix ι κ ℂ)
    (C : σ → Matrix κ ι ℂ) (D Γp : σ → Matrix κ κ ℂ)
    (h : ∀ k, IsUnit (1 - D k * Γp k).det) :
    contractC (Matrix.fromBlocks (Matrix.blockDiagonal A) (Matrix.blockDiagonal B)
        (Matrix.blockDiagonal C) (Matrix.blockDiagonal D)) (Matrix.blockDiagonal Γp) =
      Matrix.blockDiagonal (fun k =>
        contractC (Matrix.fromBlocks (A k) (B k) (C k) (D k)) (Γp k)) := by
  simp only [contractC_fromBlocks]
  have h1 : (1 : Matrix (κ × σ) (κ × σ) ℂ) - Matrix.blockDiagonal D * Matrix.blockDiagonal Γp =
      Matrix.blockDiagonal (fun k => 1 - D k * Γp k) := by
    rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub]
    rfl
  rw [h1, blockDiagonal_inv _ h, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_add]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Entrywise conjugation commutes with the contraction formula. -/
lemma contractC_map_star (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (Γp : Matrix κ κ ℂ) :
    contractC (Γ.map star) (Γp.map star) = (contractC Γ Γp).map star := by
  have hstar : (star : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext fun _ => (starRingEnd_apply _).symm
  have hinv : ∀ X : Matrix κ κ ℂ, (X.map (starRingEnd ℂ))⁻¹ = X⁻¹.map (starRingEnd ℂ) := by
    intro X
    have hX : ∀ Y : Matrix κ κ ℂ, Y.map (starRingEnd ℂ) = Yᴴᵀ := fun Y => by
      ext i j; rfl
    rw [hX, hX, ← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  rw [hstar]
  have h11 : (Γ.map (starRingEnd ℂ)).toBlocks₁₁ = Γ.toBlocks₁₁.map (starRingEnd ℂ) := rfl
  have h12 : (Γ.map (starRingEnd ℂ)).toBlocks₁₂ = Γ.toBlocks₁₂.map (starRingEnd ℂ) := rfl
  have h21 : (Γ.map (starRingEnd ℂ)).toBlocks₂₁ = Γ.toBlocks₂₁.map (starRingEnd ℂ) := rfl
  have h22 : (Γ.map (starRingEnd ℂ)).toBlocks₂₂ = Γ.toBlocks₂₂.map (starRingEnd ℂ) := rfl
  simp only [contractC, h11, h12, h21, h22]
  rw [Matrix.map_add (f := starRingEnd ℂ) (map_add _), Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, ← hinv, Matrix.map_sub (f := starRingEnd ℂ) (map_sub _), Matrix.map_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

end ContractC

/-! ### The discrete Fourier transform over sites -/

section DFT

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The site-index Fourier matrix on labels `α`: rows `(a, k)`, columns `(i, b)`. -/
noncomputable def dft (α : Type*) [DecidableEq α] (N : ℕ) :
    Matrix (α × Fin N) (Fin N × α) ℂ :=
  fun p q => if p.1 = q.2 then character p.2 q.1 else 0

/-- The inverse Fourier matrix, `N⁻¹` times the conjugate transpose of `dft`. -/
noncomputable def dftInv (α : Type*) [DecidableEq α] (N : ℕ) :
    Matrix (Fin N × α) (α × Fin N) ℂ :=
  fun q p => if p.1 = q.2 then (N : ℂ)⁻¹ * star (character p.2 q.1) else 0

omit [Fintype α] in
lemma dftInv_eq_smul_conjTranspose :
    dftInv α N = (N : ℂ)⁻¹ • (dft α N).conjTranspose := by
  ext ⟨i, a⟩ ⟨b, k⟩
  simp only [dftInv, dft, Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  split_ifs <;> simp

omit [DecidableEq β] [Fintype β] in
lemma dft_mul_apply (G : Matrix (Fin N × α) (Fin N × β) ℂ) (a : α) (k : Fin N) (q : Fin N × β) :
    (dft α N * G) (a, k) q = ∑ i : Fin N, character k i * G (i, a) q := by
  simp only [Matrix.mul_apply, dft, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

omit [DecidableEq α] [Fintype α] in
lemma mul_dftInv_apply (H : Matrix (α × Fin N) (Fin N × β) ℂ) (p : α × Fin N) (b : β)
    (l : Fin N) :
    (H * dftInv β N) p (b, l) = ∑ j : Fin N, H p (j, b) * ((N : ℂ)⁻¹ * star (character l j)) := by
  simp only [Matrix.mul_apply, dftInv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

variable [NeZero N]

lemma dft_mul_dftInv : dft α N * dftInv α N = 1 := by
  ext ⟨a, k⟩ ⟨b, l⟩
  rw [mul_dftInv_apply, Matrix.one_apply]
  simp only [dft, Prod.mk.injEq]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases hab : a = b
  · subst hab
    simp only [ite_true]
    have : ∑ j : Fin N, character k j * ((N : ℂ)⁻¹ * star (character l j)) =
        (N : ℂ)⁻¹ * ∑ j : Fin N, character k j * star (character l j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, sum_character_mul_star]
    by_cases hkl : k = l <;> simp [hkl, hN]
  · simp [hab]

lemma dftInv_mul_dft : dftInv α N * dft α N = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, dftInv, dft, Fintype.sum_prod_type, Matrix.one_apply,
    Prod.mk.injEq]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      have : ∑ k : Fin N, (N : ℂ)⁻¹ * star (character k i) * character k j =
          (N : ℂ)⁻¹ * ∑ k : Fin N, star (character k i) * character k j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      rw [this, sum_star_character_mul]
      by_cases hij : i = j <;> simp [hij, hN]
    · simp [hab]
  · intro c _ hc; simp [hc]
  · simp

/-! #### Site shifts -/

/-- The site named by a label: the previous site when the label is shifted. -/
def shiftSite (s : Bool) (i : Fin N) : Fin N := if s then (finRotate N).symm i else i

def unshiftSite (s : Bool) (i : Fin N) : Fin N := if s then finRotate N i else i

omit [NeZero N] in
lemma shiftSite_unshiftSite (s : Bool) (i : Fin N) : shiftSite s (unshiftSite s i) = i := by
  cases s <;> simp only [shiftSite, unshiftSite, ite_true, ite_false, Bool.false_eq_true,
    Equiv.symm_apply_apply]

omit [NeZero N] in
lemma unshiftSite_shiftSite (s : Bool) (i : Fin N) : unshiftSite s (shiftSite s i) = i := by
  cases s <;> simp only [shiftSite, unshiftSite, ite_true, ite_false, Bool.false_eq_true,
    Equiv.apply_symm_apply]

/-- The phase carried by a shifted label. -/
noncomputable def shiftPhase (s : Bool) (k : Fin N) : ℂ := if s then sitePhase k else 1

lemma character_shiftSite (s : Bool) (k i : Fin N) :
    character k (shiftSite s i) = character k i * star (shiftPhase s k) := by
  cases s
  · simp [shiftSite, shiftPhase]
  · simp only [shiftSite, shiftPhase, ite_true]
    exact character_finRotate_symm k i

lemma character_unshiftSite (s : Bool) (k i : Fin N) :
    character k (unshiftSite s i) = character k i * shiftPhase s k := by
  cases s
  · simp [unshiftSite, shiftPhase]
  · simp only [unshiftSite, shiftPhase, ite_true]
    exact character_finRotate k i

/-- Step 2, generic form: a matrix that couples label `a` at site `i` to label `b` at site `j`
exactly when the (shifted) sites agree is block diagonalized by the Fourier transform, the
blocks being the twisted coupling matrix. -/
lemma dft_mul_shiftDiagonal_mul_dftInv (sα : α → Bool) (sβ : β → Bool) (X : Matrix α β ℂ)
    (G : Matrix (Fin N × α) (Fin N × β) ℂ)
    (hG : ∀ i a j b, G (i, a) (j, b) =
      if shiftSite (sα a) i = shiftSite (sβ b) j then X a b else 0) :
    dft α N * G * dftInv β N = Matrix.blockDiagonal (fun k =>
      Matrix.diagonal (fun a => shiftPhase (sα a) k) * X *
        Matrix.diagonal (fun b => star (shiftPhase (sβ b) k))) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  rw [mul_dftInv_apply, Matrix.blockDiagonal_apply]
  simp only [dft_mul_apply, hG, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- collapse the inner sum over `j`
  have hinner : ∀ i : Fin N,
      (∑ j : Fin N, (if shiftSite (sα a) i = shiftSite (sβ b) j then X a b else 0) *
        ((N : ℂ)⁻¹ * star (character l j))) =
      X a b * ((N : ℂ)⁻¹ * star (character l (unshiftSite (sβ b) (shiftSite (sα a) i)))) := by
    intro i
    rw [Finset.sum_eq_single (unshiftSite (sβ b) (shiftSite (sα a) i))]
    · simp [shiftSite_unshiftSite]
    · intro j _ hj
      have : shiftSite (sα a) i ≠ shiftSite (sβ b) j := by
        intro h
        apply hj
        rw [h, unshiftSite_shiftSite]
      simp [this]
    · simp
  have hinner' : ∀ i : Fin N,
      (∑ j : Fin N, character k i *
        (if shiftSite (sα a) i = shiftSite (sβ b) j then X a b else 0) *
        ((N : ℂ)⁻¹ * star (character l j))) =
      character k i * (X a b *
        ((N : ℂ)⁻¹ * star (character l (unshiftSite (sβ b) (shiftSite (sα a) i))))) := by
    intro i
    rw [← hinner i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin N, character k i * (X a b *
          ((N : ℂ)⁻¹ * star (character l (unshiftSite (sβ b) (shiftSite (sα a) i))))) :=
        Finset.sum_congr rfl (fun i _ => hinner' i)
    _ = (N : ℂ)⁻¹ * X a b * (shiftPhase (sα a) l * star (shiftPhase (sβ b) l)) *
          ∑ i : Fin N, character k i * star (character l i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [character_unshiftSite, character_shiftSite, star_mul', star_mul', star_star]
        ring
    _ = _ := by
        rw [sum_character_mul_star]
        split_ifs with hkl
        · subst hkl
          field_simp
        · simp

end DFT

/-! ### The homogeneous chain in site-label coordinates -/

section ChainCoordinates

/-- Shifted labels of the eliminated set: the `L'` labels name the previous site. -/
def elimShift : PairIndex (Fin M) → Bool
  | Sum.inl (Sum.inr _) => true
  | Sum.inr (Sum.inr _) => true
  | _ => false

/-- Physical labels are never shifted. -/
def physShift (P : ℕ) : Fin P ⊕ Fin P → Bool := fun _ => false

/-- Shifted labels of a site in the split coordinates. -/
def splitShift : SiteSplit M P → Bool
  | Sum.inl a => physShift P a
  | Sum.inr e => elimShift e

/-- `(i, a) ↦ (i, a)`: retained labels as pairs. -/
def retainedEquiv (N P : ℕ) : Fin N × (Fin P ⊕ Fin P) ≃ Retained N P where
  toFun p := retained p.1 p.2
  invFun
    | Sum.inl (i, c) => (i, Sum.inl c)
    | Sum.inr (i, c) => (i, Sum.inr c)
  left_inv := by rintro ⟨i, c | c⟩ <;> rfl
  right_inv := by rintro (⟨i, c⟩ | ⟨i, c⟩) <;> rfl

/-- `(i, e) ↦ e_{(i, a)}`: eliminated labels as pairs. -/
def eliminatedEquiv (N M : ℕ) : Fin N × PairIndex (Fin M) ≃ Eliminated N M where
  toFun
    | (i, Sum.inl (Sum.inl a)) => Sum.inl (Sum.inl (i, a))
    | (i, Sum.inl (Sum.inr a)) => Sum.inl (Sum.inr (i, a))
    | (i, Sum.inr (Sum.inl a)) => Sum.inr (Sum.inl (i, a))
    | (i, Sum.inr (Sum.inr a)) => Sum.inr (Sum.inr (i, a))
  invFun
    | Sum.inl (Sum.inl (i, a)) => (i, Sum.inl (Sum.inl a))
    | Sum.inl (Sum.inr (i, a)) => (i, Sum.inl (Sum.inr a))
    | Sum.inr (Sum.inl (i, a)) => (i, Sum.inr (Sum.inl a))
    | Sum.inr (Sum.inr (i, a)) => (i, Sum.inr (Sum.inr a))
  left_inv := by rintro ⟨i, (a | a) | (a | a)⟩ <;> rfl
  right_inv := by rintro ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩)) <;> rfl

/-- The combined relabelling of `R ⊕ E`. -/
def chainSplitEquiv (N M P : ℕ) :
    (Fin N × (Fin P ⊕ Fin P)) ⊕ (Fin N × PairIndex (Fin M)) ≃ Retained N P ⊕ Eliminated N M :=
  Equiv.sumCongr (retainedEquiv N P) (eliminatedEquiv N M)

/-- Site-split coordinates of a global label. -/
def chainSplit (N M P : ℕ) : Fin N × SiteSplit M P → Retained N P ⊕ Eliminated N M
  | (i, Sum.inl a) => Sum.inl (retainedEquiv N P (i, a))
  | (i, Sum.inr e) => Sum.inr (eliminatedEquiv N M (i, e))

lemma siteMajorEquiv_chainEquiv_chainSplit (i : Fin N) (w : SiteSplit M P) :
    siteMajorEquiv N M P (chainEquiv N M P (chainSplit N M P (i, w))) =
      (siteSplit M P w, shiftSite (splitShift w) i) := by
  rcases w with (c | c) | ((a | a) | (a | a)) <;> rfl

/-- Step 2 for the chain: the periodic input couples label `w` at site `i` to label `w'`
at site `j` exactly when the shifted sites agree. -/
lemma periodicInput_chainSplit (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (i j : Fin N) (w w' : SiteSplit M P) :
    periodicInput (fun _ : Fin N => Γ) (chainSplit N M P (i, w)) (chainSplit N M P (j, w')) =
      if shiftSite (splitShift w) i = shiftSite (splitShift w') j then
        Γ (siteSplit M P w) (siteSplit M P w') else 0 := by
  simp only [periodicInput, Matrix.submatrix_apply, siteMajorEquiv_chainEquiv_chainSplit,
    Matrix.blockDiagonal_apply]

/-- The periodic bond in pair coordinates is site diagonal with the single-site bond. -/
lemma periodicBond_eliminatedEquiv (i j : Fin N) (e e' : PairIndex (Fin M)) :
    periodicBond N M (eliminatedEquiv N M (i, e)) (eliminatedEquiv N M (j, e')) =
      if i = j then bond (Fin M) e e' else 0 := by
  rcases e with (a | a) | (a | a) <;> rcases e' with (b | b) | (b | b) <;>
    simp [periodicBond, bond, pairing, eliminatedEquiv, Matrix.one_apply, Prod.ext_iff] <;>
    split_ifs <;> simp_all

end ChainCoordinates

/-! ### Transport lemmas: complexification, relabelling, determinants, positivity -/

section Transport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma map_ofRealHom_inv_of_isUnit_det {X : Matrix κ κ ℝ} (hX : IsUnit X.det) :
    (X.map Complex.ofRealHom)⁻¹ = X⁻¹.map Complex.ofRealHom := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hX, Matrix.map_one _ (map_zero _) (map_one _)]

omit [Fintype ι] [DecidableEq ι] in
/-- The real contraction, complexified, is the complex contraction formula. -/
lemma contract_map_ofReal (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Γp : Matrix κ κ ℝ)
    (hinv : ContractInvertible Γ Γp) :
    (contract Γ Γp).map Complex.ofReal =
      contractC (Γ.map Complex.ofReal) (Γp.map Complex.ofReal) := by
  have hco : (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom := rfl
  rw [hco]
  have h11 : (Γ.map Complex.ofRealHom).toBlocks₁₁ = Γ.toBlocks₁₁.map Complex.ofRealHom := rfl
  have h12 : (Γ.map Complex.ofRealHom).toBlocks₁₂ = Γ.toBlocks₁₂.map Complex.ofRealHom := rfl
  have h21 : (Γ.map Complex.ofRealHom).toBlocks₂₁ = Γ.toBlocks₂₁.map Complex.ofRealHom := rfl
  have h22 : (Γ.map Complex.ofRealHom).toBlocks₂₂ = Γ.toBlocks₂₂.map Complex.ofRealHom := rfl
  simp only [contract, contractC, h11, h12, h21, h22]
  rw [Matrix.map_add (f := Complex.ofRealHom) (map_add _), Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, ← map_ofRealHom_inv_of_isUnit_det hinv,
    Matrix.map_sub (f := Complex.ofRealHom) (map_sub _), Matrix.map_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

variable {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- The complex contraction commutes with relabelling the retained and eliminated labels. -/
lemma contractC_submatrix_sumCongr (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (Γp : Matrix κ κ ℂ)
    (eR : ι' ≃ ι) (eE : κ' ≃ κ) :
    contractC (Γ.submatrix (Equiv.sumCongr eR eE) (Equiv.sumCongr eR eE)) (Γp.submatrix eE eE) =
      (contractC Γ Γp).submatrix eR eR := by
  have h11 : (Γ.submatrix (Equiv.sumCongr eR eE) (Equiv.sumCongr eR eE)).toBlocks₁₁ =
      Γ.toBlocks₁₁.submatrix eR eR := rfl
  have h12 : (Γ.submatrix (Equiv.sumCongr eR eE) (Equiv.sumCongr eR eE)).toBlocks₁₂ =
      Γ.toBlocks₁₂.submatrix eR eE := rfl
  have h21 : (Γ.submatrix (Equiv.sumCongr eR eE) (Equiv.sumCongr eR eE)).toBlocks₂₁ =
      Γ.toBlocks₂₁.submatrix eE eR := rfl
  have h22 : (Γ.submatrix (Equiv.sumCongr eR eE) (Equiv.sumCongr eR eE)).toBlocks₂₂ =
      Γ.toBlocks₂₂.submatrix eE eE := rfl
  simp only [contractC, h11, h12, h21, h22]
  rw [Matrix.submatrix_mul_equiv Γ.toBlocks₂₂ Γp (eE : κ' → κ) eE (eE : κ' → κ),
    ← Matrix.submatrix_one_equiv eE,
    show (1 : Matrix κ κ ℂ).submatrix eE eE - (Γ.toBlocks₂₂ * Γp).submatrix eE eE =
      (1 - Γ.toBlocks₂₂ * Γp).submatrix eE eE from rfl,
    Matrix.inv_submatrix_equiv]
  simp only [Matrix.submatrix_mul_equiv]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A real positive semidefinite matrix stays positive semidefinite over `ℂ`. -/
lemma posSemidef_map_ofReal [Finite ι] {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    (X.map Complex.ofReal).PosSemidef := by
  cases nonempty_fintype ι
  have hsymm : X.transpose = X := by
    have := hX.1
    unfold Matrix.IsHermitian at this
    simpa using this
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hX ⊢
  refine ⟨?_, fun z => ?_⟩
  · unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Matrix.transpose_apply X, hsymm]
  · rw [eq_ofRealVec_re_add_smul_im z]
    set a := fun i => (z i).re
    set b := fun i => (z i).im
    have hcomm : b ⬝ᵥ (X *ᵥ a) = a ⬝ᵥ (X *ᵥ b) := by
      have h := Matrix.dotProduct_transpose_mulVec X b a
      rw [hsymm] at h
      rw [h, dotProduct_comm]
    have hform : star (ofRealVec a + Complex.I • ofRealVec b) ⬝ᵥ
        (X.map Complex.ofReal *ᵥ (ofRealVec a + Complex.I • ofRealVec b)) =
        ((a ⬝ᵥ (X *ᵥ a) + b ⬝ᵥ (X *ᵥ b) : ℝ) : ℂ) := by
      simp only [star_add, star_smul, star_ofRealVec, Complex.star_def, Complex.conj_I,
        Matrix.mulVec_add, Matrix.mulVec_smul, map_ofReal_mulVec_ofRealVec, dotProduct_add,
        add_dotProduct, dotProduct_smul, smul_dotProduct, ofRealVec_dotProduct, smul_eq_mul,
        hcomm]
      push_cast
      apply Complex.ext
      · simp
      · simp
    rw [hform]
    have ha := hX.2 a
    have hb := hX.2 b
    exact_mod_cast add_nonneg ha hb

/-- Conjugation by the Fourier matrices preserves determinants. -/
lemma det_dft_mul_mul_dftInv [NeZero N] {α : Type*} [Fintype α] [DecidableEq α]
    (X : Matrix (Fin N × α) (Fin N × α) ℂ) :
    (dft α N * X * dftInv α N).det = X.det := by
  let e : Fin N × α ≃ α × Fin N := Equiv.prodComm _ _
  have h1 : dft α N * X * dftInv α N =
      (dft α N).submatrix id e.symm * X.submatrix e.symm e.symm *
        (dftInv α N).submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have h2 : (dft α N).submatrix id e.symm * (dftInv α N).submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, dft_mul_dftInv]
    rfl
  have h3 : ((dft α N).submatrix id e.symm).det * ((dftInv α N).submatrix e.symm id).det = 1 := by
    rw [← Matrix.det_mul, h2, Matrix.det_one]
  rw [h1, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h3, one_mul,
    Matrix.det_submatrix_equiv_self]

end Transport

/-! ### Block diagonalization of the homogeneous chain -/

section Homogeneous

variable (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)

/-- The complexified periodic input of the homogeneous chain in pair coordinates. -/
noncomputable def inputPairs (N : ℕ) :
    Matrix ((Fin N × (Fin P ⊕ Fin P)) ⊕ (Fin N × PairIndex (Fin M)))
      ((Fin N × (Fin P ⊕ Fin P)) ⊕ (Fin N × PairIndex (Fin M))) ℂ :=
  ((periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal).submatrix
    (chainSplitEquiv N M P) (chainSplitEquiv N M P)

/-- The complexified periodic bond in pair coordinates. -/
noncomputable def bondPairs (N M : ℕ) :
    Matrix (Fin N × PairIndex (Fin M)) (Fin N × PairIndex (Fin M)) ℂ :=
  ((periodicBond N M).map Complex.ofReal).submatrix (eliminatedEquiv N M) (eliminatedEquiv N M)

/-- The complexified local matrix in the split coordinates, untwisted. -/
noncomputable def localSplit : Matrix (SiteSplit M P) (SiteSplit M P) ℂ :=
  (Γ.map Complex.ofReal).submatrix (siteSplit M P) (siteSplit M P)

/-- The complexified homogeneous covariance in pair coordinates. -/
noncomputable def covariancePairs (N : ℕ) :
    Matrix (Fin N × (Fin P ⊕ Fin P)) (Fin N × (Fin P ⊕ Fin P)) ℂ :=
  ((homogeneousCovariance N Γ).map Complex.ofReal).submatrix (retainedEquiv N P) (retainedEquiv N P)

/-- Pair coordinates of a site-split label. -/
def pairSplit (N M P : ℕ) : Fin N × SiteSplit M P →
    (Fin N × (Fin P ⊕ Fin P)) ⊕ (Fin N × PairIndex (Fin M))
  | (i, Sum.inl a) => Sum.inl (i, a)
  | (i, Sum.inr e) => Sum.inr (i, e)

lemma chainSplitEquiv_pairSplit (i : Fin N) (w : SiteSplit M P) :
    chainSplitEquiv N M P (pairSplit N M P (i, w)) = chainSplit N M P (i, w) := by
  rcases w with a | e <;> rfl

lemma inputPairs_apply (i j : Fin N) (w w' : SiteSplit M P) :
    inputPairs Γ N (pairSplit N M P (i, w)) (pairSplit N M P (j, w')) =
    if shiftSite (splitShift w) i = shiftSite (splitShift w') j then
      localSplit Γ w w' else 0 := by
  simp only [inputPairs, Matrix.submatrix_apply, chainSplitEquiv_pairSplit,
    Matrix.map_apply, periodicInput_chainSplit, localSplit]
  split_ifs <;> simp

lemma twist_siteSplit (k : Fin N) (w : SiteSplit M P) :
    twist k (siteSplit M P w) = shiftPhase (splitShift w) k := by
  rcases w with (c | c) | ((a | a) | (a | a)) <;> simp [twist, siteSplit, shiftPhase, splitShift,
    elimShift, physShift]

lemma twistedSplit_apply (k : Fin N) (w w' : SiteSplit M P) :
    twistedSplit Γ k w w' =
      shiftPhase (splitShift w) k * localSplit Γ w w' * star (shiftPhase (splitShift w') k) := by
  simp only [twistedSplit, twistedLocal, Matrix.submatrix_apply, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, twist_siteSplit, localSplit, Pi.star_apply]

/-! The four blocks of the periodic input and of the twisted local matrix. -/

lemma inputPairs_toBlocks_11 (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    (inputPairs Γ N).toBlocks₁₁ (i, a) (j, b) =
      if shiftSite (physShift P a) i = shiftSite (physShift P b) j then
        (localSplit Γ).toBlocks₁₁ a b else 0 :=
  inputPairs_apply Γ i j (Sum.inl a) (Sum.inl b)

lemma inputPairs_toBlocks_12 (i j : Fin N) (a : Fin P ⊕ Fin P) (e : PairIndex (Fin M)) :
    (inputPairs Γ N).toBlocks₁₂ (i, a) (j, e) =
      if shiftSite (physShift P a) i = shiftSite (elimShift e) j then
        (localSplit Γ).toBlocks₁₂ a e else 0 :=
  inputPairs_apply Γ i j (Sum.inl a) (Sum.inr e)

lemma inputPairs_toBlocks_21 (i j : Fin N) (e : PairIndex (Fin M)) (b : Fin P ⊕ Fin P) :
    (inputPairs Γ N).toBlocks₂₁ (i, e) (j, b) =
      if shiftSite (elimShift e) i = shiftSite (physShift P b) j then
        (localSplit Γ).toBlocks₂₁ e b else 0 :=
  inputPairs_apply Γ i j (Sum.inr e) (Sum.inl b)

lemma inputPairs_toBlocks_22 (i j : Fin N) (e f : PairIndex (Fin M)) :
    (inputPairs Γ N).toBlocks₂₂ (i, e) (j, f) =
      if shiftSite (elimShift e) i = shiftSite (elimShift f) j then
        (localSplit Γ).toBlocks₂₂ e f else 0 :=
  inputPairs_apply Γ i j (Sum.inr e) (Sum.inr f)

lemma twistedSplit_toBlocks_11 (k : Fin N) :
    (twistedSplit Γ k).toBlocks₁₁ =
      Matrix.diagonal (fun a => shiftPhase (physShift P a) k) *
        (localSplit Γ).toBlocks₁₁ *
        Matrix.diagonal (fun b => star (shiftPhase (physShift P b) k)) := by
  ext a b
  simp [Matrix.toBlocks₁₁, twistedSplit_apply, splitShift, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma twistedSplit_toBlocks_12 (k : Fin N) :
    (twistedSplit Γ k).toBlocks₁₂ =
      Matrix.diagonal (fun a => shiftPhase (physShift P a) k) *
        (localSplit Γ).toBlocks₁₂ *
        Matrix.diagonal (fun e => star (shiftPhase (elimShift e) k)) := by
  ext a e
  simp [Matrix.toBlocks₁₂, twistedSplit_apply, splitShift, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma twistedSplit_toBlocks_21 (k : Fin N) :
    (twistedSplit Γ k).toBlocks₂₁ =
      Matrix.diagonal (fun e => shiftPhase (elimShift e) k) *
        (localSplit Γ).toBlocks₂₁ *
        Matrix.diagonal (fun b => star (shiftPhase (physShift P b) k)) := by
  ext e b
  simp [Matrix.toBlocks₂₁, twistedSplit_apply, splitShift, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma twistedSplit_toBlocks_22 (k : Fin N) :
    (twistedSplit Γ k).toBlocks₂₂ =
      Matrix.diagonal (fun e => shiftPhase (elimShift e) k) *
        (localSplit Γ).toBlocks₂₂ *
        Matrix.diagonal (fun f => star (shiftPhase (elimShift f) k)) := by
  ext e f
  simp [Matrix.toBlocks₂₂, twistedSplit_apply, splitShift, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma bondPairs_apply (i j : Fin N) (e f : PairIndex (Fin M)) :
    bondPairs N M (i, e) (j, f) =
      if shiftSite false i = shiftSite false j then bondC M e f else 0 := by
  simp only [bondPairs, bondC, Matrix.submatrix_apply, Matrix.map_apply,
    periodicBond_eliminatedEquiv, shiftSite, Bool.false_eq_true, ite_false]
  split_ifs <;> simp

variable [NeZero N]

lemma dft_inputPairs_11 :
    dft (Fin P ⊕ Fin P) N * (inputPairs Γ N).toBlocks₁₁ * dftInv (Fin P ⊕ Fin P) N =
      Matrix.blockDiagonal (fun k => (twistedSplit Γ k).toBlocks₁₁) := by
  rw [dft_mul_shiftDiagonal_mul_dftInv (fun a => physShift P a)
    (fun b => physShift P b) _ _ (fun i a j b => inputPairs_toBlocks_11 Γ i j a b)]
  simp only [twistedSplit_toBlocks_11]

lemma dft_inputPairs_12 :
    dft (Fin P ⊕ Fin P) N * (inputPairs Γ N).toBlocks₁₂ * dftInv (PairIndex (Fin M)) N =
      Matrix.blockDiagonal (fun k => (twistedSplit Γ k).toBlocks₁₂) := by
  rw [dft_mul_shiftDiagonal_mul_dftInv (fun a => physShift P a)
    (fun e => elimShift e) _ _ (fun i a j b => inputPairs_toBlocks_12 Γ i j a b)]
  simp only [twistedSplit_toBlocks_12]

lemma dft_inputPairs_21 :
    dft (PairIndex (Fin M)) N * (inputPairs Γ N).toBlocks₂₁ * dftInv (Fin P ⊕ Fin P) N =
      Matrix.blockDiagonal (fun k => (twistedSplit Γ k).toBlocks₂₁) := by
  rw [dft_mul_shiftDiagonal_mul_dftInv (fun e => elimShift e)
    (fun b => physShift P b) _ _ (fun i a j b => inputPairs_toBlocks_21 Γ i j a b)]
  simp only [twistedSplit_toBlocks_21]

lemma dft_inputPairs_22 :
    dft (PairIndex (Fin M)) N * (inputPairs Γ N).toBlocks₂₂ * dftInv (PairIndex (Fin M)) N =
      Matrix.blockDiagonal (fun k => (twistedSplit Γ k).toBlocks₂₂) := by
  rw [dft_mul_shiftDiagonal_mul_dftInv (fun e => elimShift e)
    (fun f => elimShift f) _ _ (fun i a j b => inputPairs_toBlocks_22 Γ i j a b)]
  simp only [twistedSplit_toBlocks_22]

lemma dft_bondPairs :
    dft (PairIndex (Fin M)) N * bondPairs N M * dftInv (PairIndex (Fin M)) N =
      Matrix.blockDiagonal (fun _ : Fin N => bondC M) := by
  rw [dft_mul_shiftDiagonal_mul_dftInv (fun _ => false) (fun _ => false) _ _
    (fun i a j b => bondPairs_apply i j a b)]
  simp [shiftPhase]

/-- Conjugation by the Fourier matrices distributes over `1 - X * Y`. -/
lemma dft_one_sub_mul_dftInv {α : Type*} [Fintype α] [DecidableEq α]
    (X Y : Matrix (Fin N × α) (Fin N × α) ℂ) :
    dft α N * (1 - X * Y) * dftInv α N =
      1 - (dft α N * X * dftInv α N) * (dft α N * Y * dftInv α N) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, dft_mul_dftInv]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dftInv α N) (dft α N), dftInv_mul_dft, Matrix.one_mul]

omit [NeZero N] in
/-- The eliminated block of the periodic input, complexified and relabelled. -/
lemma det_one_sub_inputPairs :
    (1 - (inputPairs Γ N).toBlocks₂₂ * bondPairs N M).det =
      (((1 - (periodicInput (fun _ : Fin N => Γ)).toBlocks₂₂ * periodicBond N M).det : ℝ) : ℂ) := by
  have h : (1 : Matrix (Fin N × PairIndex (Fin M)) (Fin N × PairIndex (Fin M)) ℂ) -
      (inputPairs Γ N).toBlocks₂₂ * bondPairs N M =
      ((1 - (periodicInput (fun _ : Fin N => Γ)).toBlocks₂₂ * periodicBond N M).map
        Complex.ofRealHom).submatrix (eliminatedEquiv N M) (eliminatedEquiv N M) := by
    have h22 : (inputPairs Γ N).toBlocks₂₂ =
        ((periodicInput (fun _ : Fin N => Γ)).toBlocks₂₂.map Complex.ofRealHom).submatrix
          (eliminatedEquiv N M) (eliminatedEquiv N M) := rfl
    rw [h22, bondPairs, Matrix.submatrix_mul_equiv,
      ← Matrix.submatrix_one_equiv (eliminatedEquiv N M),
      show ((periodicBond N M).map Complex.ofReal) = (periodicBond N M).map Complex.ofRealHom
        from rfl,
      ← Matrix.map_mul, Matrix.map_sub (f := Complex.ofRealHom) (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  rw [h, Matrix.det_submatrix_equiv_self]
  exact (RingHom.map_det Complex.ofRealHom _).symm

/-- Theorem 4: the determinant of `1 - D β_N` factorizes over momenta. -/
theorem det_one_sub_periodic_eq_prod :
    (((1 - (periodicInput (fun _ : Fin N => Γ)).toBlocks₂₂ * periodicBond N M).det : ℝ) : ℂ) =
      ∏ k : Fin N, (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M).det := by
  rw [← det_one_sub_inputPairs, ← det_dft_mul_mul_dftInv, dft_one_sub_mul_dftInv,
    dft_inputPairs_22, dft_bondPairs, det_one_sub_blockDiagonal_mul]

/-- Theorem 4: every momentum block is invertible when the chain is. -/
theorem momentum_isUnit_det_of_contractInvertible
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (k : Fin N) : IsUnit (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M).det := by
  rw [isUnit_iff_ne_zero]
  have hprod : (∏ k : Fin N, (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M).det) ≠ 0 := by
    rw [← det_one_sub_periodic_eq_prod]
    exact_mod_cast (isUnit_iff_ne_zero.mp hinv)
  exact (Finset.prod_ne_zero_iff.mp hprod) k (Finset.mem_univ k)

/-- Step 5: the Fourier transform of the homogeneous covariance is the block sum of the
momentum-space covariances. -/
theorem dft_covariancePairs
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M)) :
    dft (Fin P ⊕ Fin P) N * covariancePairs Γ N * dftInv (Fin P ⊕ Fin P) N =
      Matrix.blockDiagonal (fun k => momentumCovariance Γ k) := by
  have hcov : covariancePairs Γ N = contractC (inputPairs Γ N) (bondPairs N M) := by
    unfold covariancePairs homogeneousCovariance periodicCovariance inputPairs bondPairs
      chainSplitEquiv
    rw [contract_map_ofReal _ _ hinv, contractC_submatrix_sumCongr]
  have hdet : IsUnit (1 - (inputPairs Γ N).toBlocks₂₂ * bondPairs N M).det := by
    rw [isUnit_iff_ne_zero, det_one_sub_inputPairs]
    exact_mod_cast (isUnit_iff_ne_zero.mp hinv)
  rw [hcov, ← Matrix.fromBlocks_toBlocks (inputPairs Γ N)]
  rw [← contractC_conj _ _ _ _ _ hdet dft_mul_dftInv dftInv_mul_dft dft_mul_dftInv dftInv_mul_dft,
    dft_inputPairs_11, dft_inputPairs_12, dft_inputPairs_21, dft_inputPairs_22, dft_bondPairs,
    contractC_blockDiagonal _ _ _ _ _ (momentum_isUnit_det_of_contractInvertible Γ hinv)]
  congr 1

end Homogeneous

/-! ### The main theorems -/

section MainTheorems

variable {α γ : Type*} [Fintype α] [DecidableEq α] [Fintype γ]

omit [Fintype γ] in
lemma mul_dft_apply (H : Matrix γ (α × Fin N) ℂ) (p : γ) (j : Fin N) (b : α) :
    (H * dft α N) p (j, b) = ∑ k : Fin N, H p (b, k) * character k j := by
  simp only [Matrix.mul_apply, dft, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · simp

omit [Fintype γ] in
lemma dftInv_mul_apply (G : Matrix (α × Fin N) γ ℂ) (i : Fin N) (a : α) (q : γ) :
    (dftInv α N * G) (i, a) q = ∑ k : Fin N, ((N : ℂ)⁻¹ * star (character k i)) * G (a, k) q := by
  simp only [Matrix.mul_apply, dftInv, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

variable [NeZero N]

omit [Fintype γ] in
lemma conjTranspose_dft_mul_mul_dftInv (X : Matrix (Fin N × α) (Fin N × α) ℂ) :
    (dft α N * X * dftInv α N).conjTranspose = dft α N * X.conjTranspose * dftInv α N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdftH : (dft α N).conjTranspose = (N : ℂ) • dftInv α N := by
    rw [dftInv_eq_smul_conjTranspose, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have hinvH : (dftInv α N).conjTranspose = (N : ℂ)⁻¹ • dft α N := by
    rw [dftInv_eq_smul_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    congr 1
    simp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdftH, hinvH, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hN, one_smul, Matrix.mul_assoc]

omit [Fintype α] [DecidableEq α] in
/-- A block-diagonal positive semidefinite matrix has positive semidefinite blocks. -/
lemma posSemidef_of_blockDiagonal [Finite α] {σ : Type*} [Finite σ] [DecidableEq σ]
    (X : σ → Matrix α α ℂ) (h : (Matrix.blockDiagonal X).PosSemidef) (k : σ) :
    (X k).PosSemidef := by
  cases nonempty_fintype α
  cases nonempty_fintype σ
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h ⊢
  refine ⟨?_, fun y => ?_⟩
  · have := h.1
    unfold Matrix.IsHermitian at this ⊢
    rw [Matrix.blockDiagonal_conjTranspose] at this
    exact congrFun (Matrix.blockDiagonal_injective this) k
  · let v : α × σ → ℂ := fun p => if p.2 = k then y p.1 else 0
    have hv := h.2 v
    have hmv : ∀ p : α × σ, (Matrix.blockDiagonal X *ᵥ v) p =
        if p.2 = k then (X k *ᵥ y) p.1 else 0 := by
      intro p
      simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, v]
      by_cases hp : p.2 = k
      · simp only [hp, ite_true]
        rw [Finset.sum_comm, Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          apply Finset.sum_eq_zero
          intro i _
          simp [hj]
        · simp
      · simp only [hp, ite_false]
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j = k
        · subst hj; simp [hp]
        · simp [hj]
    have heq : star v ⬝ᵥ (Matrix.blockDiagonal X *ᵥ v) = star y ⬝ᵥ (X k *ᵥ y) := by
      simp only [dotProduct, hmv, Fintype.sum_prod_type, Pi.star_apply, v]
      rw [Finset.sum_comm, Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro i _
        simp [hj]
      · simp
    rw [← heq]
    exact hv

variable (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)

omit [NeZero N] in
lemma covariancePairs_apply (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    covariancePairs Γ N (i, a) (j, b) =
      ((homogeneousCovariance N Γ (retained i a) (retained j b) : ℝ) : ℂ) := rfl

/-- Theorem 5 (diagonalization): the Fourier coefficients of the homogeneous chain vanish off
the diagonal and are the momentum-space covariances on it. -/
theorem fourierEntry_eq
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (k l : Fin N) (a b : Fin P ⊕ Fin P) :
    fourierEntry Γ k l a b = if k = l then momentumCovariance Γ k a b else 0 := by
  have h := congrFun (congrFun (dft_covariancePairs Γ hinv) (a, k)) (b, l)
  rw [Matrix.blockDiagonal_apply, mul_dftInv_apply] at h
  simp only [dft_mul_apply, covariancePairs_apply] at h
  rw [← h]
  simp only [fourierEntry, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Theorem 6 (reconstruction): the homogeneous covariance is the inverse Fourier transform of
the momentum-space covariances. -/
theorem homogeneousCovariance_reconstruct
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    ((homogeneousCovariance N Γ (retained i a) (retained j b) : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ k : Fin N,
        star (character k i) * momentumCovariance Γ k a b * character k j := by
  have h2 : covariancePairs Γ N = dftInv (Fin P ⊕ Fin P) N *
      Matrix.blockDiagonal (fun k => momentumCovariance Γ k) * dft (Fin P ⊕ Fin P) N := by
    calc covariancePairs Γ N
        = (dftInv (Fin P ⊕ Fin P) N * dft (Fin P ⊕ Fin P) N) * covariancePairs Γ N *
            (dftInv (Fin P ⊕ Fin P) N * dft (Fin P ⊕ Fin P) N) := by
          rw [dftInv_mul_dft, Matrix.one_mul, Matrix.mul_one]
      _ = dftInv (Fin P ⊕ Fin P) N *
            (dft (Fin P ⊕ Fin P) N * covariancePairs Γ N * dftInv (Fin P ⊕ Fin P) N) *
            dft (Fin P ⊕ Fin P) N := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [dft_covariancePairs Γ hinv]
  rw [← covariancePairs_apply, h2, mul_dft_apply]
  simp only [dftInv_mul_apply, Matrix.blockDiagonal_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
    ring
  · intro k' _ hk'
    simp [hk']
  · simp

/-- Theorem 5 (translation invariance): the homogeneous covariance is invariant under the
simultaneous shift of both sites. -/
theorem homogeneousCovariance_translation
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    homogeneousCovariance N Γ (retained (finRotate N i) a) (retained (finRotate N j) b) =
      homogeneousCovariance N Γ (retained i a) (retained j b) := by
  apply Complex.ofReal_injective
  rw [homogeneousCovariance_reconstruct Γ hinv, homogeneousCovariance_reconstruct Γ hinv]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [character_finRotate, character_finRotate, star_mul']
  have := sitePhase_mul_star k
  linear_combination (star (character k i) * momentumCovariance Γ k a b * character k j) * this

/-- Theorem 7(a): the momentum-space covariances at `k` and `-k` are complex conjugates. -/
theorem momentumCovariance_neg (k : Fin N) :
    momentumCovariance Γ (-k) = (momentumCovariance Γ k).map star := by
  unfold momentumCovariance
  rw [← contractC_map_star]
  congr 1
  · ext w w'
    have hs : ∀ s : Bool, shiftPhase s (-k) = star (shiftPhase s k) := by
      intro s; cases s <;> simp [shiftPhase, sitePhase_neg]
    simp only [twistedSplit_apply, Matrix.map_apply, hs, localSplit, Matrix.submatrix_apply]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  · ext e f
    simp [bondC]

omit [NeZero N] in
lemma homogeneousCovariance_transpose (hΓ : Γ.transpose = -Γ)
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M)) :
    (homogeneousCovariance N Γ).transpose = -homogeneousCovariance N Γ := by
  unfold homogeneousCovariance periodicCovariance
  apply contract_transpose _ (pure_bond (L := Fin N × Fin M)).1 hinv
  unfold periodicInput
  rw [submatrix_equiv_transpose_eq_neg_iff, submatrix_equiv_transpose_eq_neg_iff,
    blockDiagonal_transpose_eq_neg_iff]
  exact fun _ => hΓ

omit [NeZero N] in
lemma covariancePairs_conjTranspose :
    (covariancePairs Γ N).conjTranspose =
      ((homogeneousCovariance N Γ).transpose.map Complex.ofReal).submatrix
        (retainedEquiv N P) (retainedEquiv N P) := by
  ext p q
  simp [covariancePairs]

/-- Theorem 7(b): the momentum-space covariances are skew-Hermitian. -/
theorem momentumCovariance_conjTranspose (hΓ : Γ.transpose = -Γ)
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (k : Fin N) :
    (momentumCovariance Γ k).conjTranspose = -(momentumCovariance Γ k) := by
  have hC : (covariancePairs Γ N).conjTranspose = -(covariancePairs Γ N) := by
    rw [covariancePairs_conjTranspose, homogeneousCovariance_transpose Γ hΓ hinv]
    ext p q
    simp [covariancePairs]
  have h := dft_covariancePairs Γ hinv
  have h' := congrArg Matrix.conjTranspose h
  rw [conjTranspose_dft_mul_mul_dftInv, hC, Matrix.mul_neg, Matrix.neg_mul, h,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_neg] at h'
  exact (congrFun (Matrix.blockDiagonal_injective h') k).symm

/-- Theorem 7(c): the momentum-space covariances of an admissible chain are contractions,
`1 - Σ(k)^* Σ(k) ⪰ 0`. -/
theorem momentumCovariance_posSemidef (hΓ : Admissible Γ)
    (hinv : ContractInvertible (periodicInput (fun _ : Fin N => Γ)) (periodicBond N M))
    (k : Fin N) :
    (1 - (momentumCovariance Γ k).conjTranspose * momentumCovariance Γ k).PosSemidef := by
  have hadm : Admissible (homogeneousCovariance N Γ) :=
    periodicCovariance_admissible (fun _ : Fin N => Γ) (fun _ => hΓ) hinv
  -- the real bound, complexified and relabelled
  have hC : (1 - (covariancePairs Γ N).conjTranspose * covariancePairs Γ N).PosSemidef := by
    have h1 := (posSemidef_map_ofReal hadm.2).submatrix (retainedEquiv N P)
    have heq : ((1 - (homogeneousCovariance N Γ).transpose * homogeneousCovariance N Γ).map
        Complex.ofReal).submatrix (retainedEquiv N P) (retainedEquiv N P) =
        1 - (covariancePairs Γ N).conjTranspose * covariancePairs Γ N := by
      rw [covariancePairs_conjTranspose]
      unfold covariancePairs
      rw [Matrix.submatrix_mul_equiv, ← Matrix.submatrix_one_equiv (retainedEquiv N P)]
      change ((1 - _ : Matrix (Retained N P) (Retained N P) ℝ).map Complex.ofRealHom).submatrix
        _ _ = (1 : Matrix (Retained N P) (Retained N P) ℂ).submatrix _ _ -
          ((_ : Matrix (Retained N P) (Retained N P) ℝ).map Complex.ofRealHom *
            (_ : Matrix (Retained N P) (Retained N P) ℝ).map Complex.ofRealHom).submatrix _ _
      rw [← Matrix.map_mul, Matrix.map_sub (f := Complex.ofRealHom) (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    rw [← heq]
    exact h1
  -- conjugate by the Fourier matrix
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdftH : (dft (Fin P ⊕ Fin P) N).conjTranspose = (N : ℂ) • dftInv (Fin P ⊕ Fin P) N := by
    rw [dftInv_eq_smul_conjTranspose, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have h2 := hC.conjTranspose_mul_mul_same (dft (Fin P ⊕ Fin P) N).conjTranspose
  rw [Matrix.conjTranspose_conjTranspose, hdftH, Matrix.mul_smul, dft_one_sub_mul_dftInv,
    ← conjTranspose_dft_mul_mul_dftInv, dft_covariancePairs Γ hinv,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one,
    ← Matrix.blockDiagonal_sub] at h2
  have h3 : (Matrix.blockDiagonal (fun k : Fin N =>
      1 - (momentumCovariance Γ k).conjTranspose * momentumCovariance Γ k)).PosSemidef := by
    have hsm := h2.smul (a := (N : ℂ)⁻¹) (by
      have : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this]
      exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg N)))
    rw [smul_smul, inv_mul_cancel₀ hN, one_smul] at hsm
    exact hsm
  exact posSemidef_of_blockDiagonal _ h3 k

end MainTheorems

end Fermionic
