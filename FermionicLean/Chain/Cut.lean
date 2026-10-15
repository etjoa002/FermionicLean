/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.Periodic
import FermionicLean.Gaussian.Nullity
import FermionicLean.Contraction.PureInverse
import FermionicLean.Gaussian.BlockForm

/-! # The cross-block rank bound for a cut of the periodic chain

A set `S` of sites has the physical labels `R_S` and the cross block
`C_S = (Γ_N)_{R_S R_{S^c}}` of the periodic covariance. The rank of `C_S` is at most
`2 M b(S)`, where `b(S)` is the number of bonds joining `S` to its complement: the
contraction writes `Γ_N = A - B (β + D)⁻¹ C`, the same-site support of the input
confines the cross block to the `(E_S, E_{S^c})` block of `(β + D)⁻¹`, which by the
nullity lemma has the rank of the `(E_S, E_{S^c})` block of the bond `β`, and that
block has at most `2 M` nonzero rows per cut bond. For a pure periodic covariance the
block covariance `Γ_S` satisfies `1 + Γ_S² = C_S C_Sᵀ`, so `rank (1 + Γ_S²) ≤ 2 M b(S)`.
-/

open Matrix

-- Decidable equality on sums of the subtypes below exceeds the default instance size.
set_option synthInstance.maxSize 512

namespace Fermionic

variable {N M P : ℕ}

/-! ### Sites of labels and cut bonds -/

/-- The site of a retained (physical) label. -/
def siteRetained : Retained N P → Fin N
  | Sum.inl (i, _) => i
  | Sum.inr (i, _) => i

/-- The site of an eliminated (virtual) label: `L` labels at their own site, `L'` labels
at the previous site `(finRotate N).symm i`. -/
def siteElim : Eliminated N M → Fin N
  | Sum.inl (Sum.inl (i, _)) => i
  | Sum.inl (Sum.inr (i, _)) => (finRotate N).symm i
  | Sum.inr (Sum.inl (i, _)) => i
  | Sum.inr (Sum.inr (i, _)) => (finRotate N).symm i

/-- The site a global label belongs to: physical labels and left virtual labels `L` at
their own site, right virtual labels `L'` at the previous site (`(finRotate N).symm i`). -/
def siteOf : Retained N P ⊕ Eliminated N M → Fin N :=
  Sum.elim siteRetained siteElim

/-- Bond `i` joins site `i - 1` to site `i`; it is cut by `S` when exactly one end is in `S`. -/
def cutBonds (S : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter fun i => ¬ (i ∈ S ↔ (finRotate N).symm i ∈ S)

lemma mem_cutBonds {S : Finset (Fin N)} {i : Fin N} :
    i ∈ cutBonds S ↔ ¬ (i ∈ S ↔ (finRotate N).symm i ∈ S) := by
  simp [cutBonds]

/-- The physical labels of the sites in `S`. -/
abbrev RetainedIn (S : Finset (Fin N)) := {a : Retained N P // siteRetained a ∈ S}

/-- The physical labels of the sites outside `S`. -/
abbrev RetainedOut (S : Finset (Fin N)) := {a : Retained N P // siteRetained a ∉ S}

/-- The virtual labels belonging to the sites in `S`. -/
abbrev ElimIn (S : Finset (Fin N)) := {e : Eliminated N M // siteElim e ∈ S}

/-- The virtual labels belonging to the sites outside `S`. -/
abbrev ElimOut (S : Finset (Fin N)) := {e : Eliminated N M // siteElim e ∉ S}

/-- The cross block of a matrix on the retained labels between `S` and its complement. -/
def crossBlock (S : Finset (Fin N)) (X : Matrix (Retained N P) (Retained N P) ℝ) :
    Matrix (RetainedIn (P := P) S) (RetainedOut (P := P) S) ℝ :=
  X.submatrix Subtype.val Subtype.val

/-- The block covariance of `S`. -/
def blockCov (S : Finset (Fin N)) (X : Matrix (Retained N P) (Retained N P) ℝ) :
    Matrix (RetainedIn (P := P) S) (RetainedIn (P := P) S) ℝ :=
  X.submatrix Subtype.val Subtype.val

/-! ### Same-site support of the periodic input -/

/-- The `Fin N` component of the site-major label of `a` is its site. -/
lemma siteMajorEquiv_chainEquiv_snd (a : Retained N P ⊕ Eliminated N M) :
    (siteMajorEquiv N M P (chainEquiv N M P a)).2 = siteOf a := by
  rcases a with (⟨i, c⟩ | ⟨i, c⟩) | ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩)) <;> rfl

/-- An entry of the periodic input with labels at different sites vanishes. -/
theorem periodicInput_apply_of_siteOf_ne (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    {a b : Retained N P ⊕ Eliminated N M} (h : siteOf a ≠ siteOf b) :
    periodicInput Γ a b = 0 := by
  simp only [periodicInput, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    siteMajorEquiv_chainEquiv_snd]
  exact ite_eq_right h

lemma siteOf_inl (a : Retained N P) : siteOf (M := M) (Sum.inl a) = siteRetained a := rfl

lemma siteOf_inr (e : Eliminated N M) : siteOf (P := P) (Sum.inr e) = siteElim e := rfl

/-- The `(R, E)` block of the periodic input vanishes between `S` and its complement. -/
lemma toBlocks₁₂_periodicInput_eq_zero (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    {S : Finset (Fin N)} {a : Retained N P} {e : Eliminated N M} (ha : siteRetained a ∈ S)
    (he : siteElim e ∉ S) : (periodicInput Γ).toBlocks₁₂ a e = 0 :=
  periodicInput_apply_of_siteOf_ne Γ (a := Sum.inl a) (b := Sum.inr e) fun h => by
    rw [siteOf_inl, siteOf_inr] at h
    exact he (h ▸ ha)

/-- The `(E, R)` block of the periodic input vanishes between `S` and its complement. -/
lemma toBlocks₂₁_periodicInput_eq_zero (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    {S : Finset (Fin N)} {e : Eliminated N M} {b : Retained N P} (he : siteElim e ∈ S)
    (hb : siteRetained b ∉ S) : (periodicInput Γ).toBlocks₂₁ e b = 0 :=
  periodicInput_apply_of_siteOf_ne Γ (a := Sum.inr e) (b := Sum.inl b) fun h => by
    rw [siteOf_inl, siteOf_inr] at h
    exact hb (h ▸ he)

/-- The `(E, E)` block of the periodic input vanishes between `S` and its complement. -/
lemma toBlocks₂₂_periodicInput_eq_zero (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    {S : Finset (Fin N)} {e e' : Eliminated N M} (he : siteElim e ∈ S)
    (he' : siteElim e' ∉ S) : (periodicInput Γ).toBlocks₂₂ e e' = 0 :=
  periodicInput_apply_of_siteOf_ne Γ (a := Sum.inr e) (b := Sum.inr e') fun h => by
    rw [siteOf_inr, siteOf_inr] at h
    exact he' (h ▸ he)

/-- The `(R, R)` block of the periodic input has vanishing cross block. -/
lemma crossBlock_toBlocks₁₁_periodicInput (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (S : Finset (Fin N)) : crossBlock S (periodicInput Γ).toBlocks₁₁ = 0 := by
  ext a b
  exact periodicInput_apply_of_siteOf_ne Γ (a := Sum.inl a.1) (b := Sum.inl b.1) fun h => by
    rw [siteOf_inl, siteOf_inl] at h
    exact b.2 (h ▸ a.2)

/-! ### Factoring the cross block through the eliminated labels of `S` -/

/-- The eliminated labels split into those of `S` and those of its complement. -/
def elimEquiv (S : Finset (Fin N)) : ElimIn (M := M) S ⊕ ElimOut (M := M) S ≃ Eliminated N M :=
  Equiv.sumCompl fun e => siteElim e ∈ S

lemma sum_eliminated_split (S : Finset (Fin N)) (f : Eliminated N M → ℝ) :
    ∑ e, f e = ∑ e : ElimIn (M := M) S, f e.1 + ∑ e : ElimOut (M := M) S, f e.1 :=
  (Fintype.sum_subtype_add_sum_subtype _ f).symm

/-- When `B` vanishes from `R_S` to `E_{S^c}` and `C` from `E_S` to `R_{S^c}`, the cross block
of `B X C` factors through the `(E_S, E_{S^c})` block of `X`. -/
lemma crossBlock_mul_mul_eq (S : Finset (Fin N))
    {B : Matrix (Retained N P) (Eliminated N M) ℝ} {X : Matrix (Eliminated N M) (Eliminated N M) ℝ}
    {C : Matrix (Eliminated N M) (Retained N P) ℝ}
    (hB : ∀ a e, siteRetained a ∈ S → siteElim e ∉ S → B a e = 0)
    (hC : ∀ e b, siteElim e ∈ S → siteRetained b ∉ S → C e b = 0) :
    crossBlock S (B * X * C) =
      B.submatrix Subtype.val (Subtype.val : ElimIn (M := M) S → _) *
        (X.submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂ *
        C.submatrix (Subtype.val : ElimOut (M := M) S → _) Subtype.val := by
  ext a b
  simp only [crossBlock, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.toBlocks₁₂,
    Matrix.of_apply, elimEquiv, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  simp_rw [sum_eliminated_split S]
  have h1 : ∀ e' : Eliminated N M, ∑ e : ElimOut (M := M) S, B a.1 e.1 * X e.1 e' = 0 :=
    fun e' => Finset.sum_eq_zero fun e _ => by rw [hB a.1 e.1 a.2 e.2, zero_mul]
  have h2 : ∑ e' : ElimIn (M := M) S,
      (∑ e : ElimIn (M := M) S, B a.1 e.1 * X e.1 e'.1) * C e'.1 b.1 = 0 :=
    Finset.sum_eq_zero fun e' _ => by rw [hC e'.1 b.1 e'.2 b.2, mul_zero]
  simp_rw [h1, add_zero]
  rw [h2, zero_add]

/-! ### The cross block of the bond -/

/-- The bond `(i, a)` carried by a virtual label. -/
def bondOf : Eliminated N M → Fin N × Fin M
  | Sum.inl (Sum.inl l) => l
  | Sum.inl (Sum.inr l) => l
  | Sum.inr (Sum.inl l) => l
  | Sum.inr (Sum.inr l) => l

/-- A nonzero bond entry between `E_S` and `E_{S^c}` sits on a cut bond. -/
lemma mem_cutBonds_of_periodicBond_ne_zero (S : Finset (Fin N)) {e e' : Eliminated N M}
    (h : periodicBond N M e e' ≠ 0) (he : siteElim e ∈ S) (he' : siteElim e' ∉ S) :
    (bondOf e).1 ∈ cutBonds S := by
  rw [mem_cutBonds]
  rcases e with ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩)) <;>
    rcases e' with ((⟨j, b⟩ | ⟨j, b⟩) | (⟨j, b⟩ | ⟨j, b⟩)) <;>
    simp [periodicBond, bond, pairing, Matrix.fromBlocks, Matrix.one_apply, siteElim, bondOf,
      Prod.ext_iff] at h he he' ⊢ <;>
    obtain ⟨rfl, rfl⟩ := h <;> tauto

/-- Distinct virtual labels of `S` on the same cut bond and in the same Majorana sector
coincide. -/
lemma eq_of_bondOf_eq (S : Finset (Fin N)) {e e' : Eliminated N M}
    (he : siteElim e ∈ S) (he' : siteElim e' ∈ S) (hcut : (bondOf e).1 ∈ cutBonds S)
    (hb : bondOf e = bondOf e') (hs : e.isLeft = e'.isLeft) : e = e' := by
  rw [mem_cutBonds] at hcut
  rcases e with ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩)) <;>
    rcases e' with ((⟨j, b⟩ | ⟨j, b⟩) | (⟨j, b⟩ | ⟨j, b⟩)) <;>
    simp [siteElim, bondOf, Prod.ext_iff] at he he' hcut hb hs ⊢ <;>
    obtain ⟨rfl, rfl⟩ := hb <;> tauto

/-- The `(E_S, E_{S^c})` block of the bond has rank at most `2 M b(S)`. -/
lemma rank_toBlocks12_periodicBond_submatrix_le (S : Finset (Fin N)) :
    ((periodicBond N M).submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂.rank ≤
      2 * M * (cutBonds S).card := by
  set A := ((periodicBond N M).submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂ with hA
  have hA' : ∀ (e : ElimIn (M := M) S) (e' : ElimOut (M := M) S),
      A e e' = periodicBond N M e.1 e'.1 := fun e e' => rfl
  let T : Finset (ElimIn (M := M) S) := Finset.univ.filter fun e => (bondOf e.1).1 ∈ cutBonds S
  have hT : ∀ e, e ∈ (T : Set (ElimIn (M := M) S)) ↔ (bondOf e.1).1 ∈ cutBonds S := fun e => by
    simp [T]
  have hsupp : Function.support A.row ⊆ T := by
    rw [Function.support_subset_iff']
    intro e he
    ext e'
    by_contra hne
    apply he
    rw [hT]
    rw [Matrix.row_apply, hA', Pi.zero_apply] at hne
    exact mem_cutBonds_of_periodicBond_ne_zero S hne e.2 e'.2
  refine (Matrix.rank_le_card_of_support_subset A T hsupp).trans ?_
  let f : ElimIn (M := M) S → (Fin N × Fin M) × Bool := fun e => (bondOf e.1, e.1.isLeft)
  have hmaps : Set.MapsTo f T
      (((cutBonds S ×ˢ (Finset.univ : Finset (Fin M))) ×ˢ (Finset.univ : Finset Bool) :
        Finset ((Fin N × Fin M) × Bool)) : Set ((Fin N × Fin M) × Bool)) := by
    intro e he
    rw [hT] at he
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Finset.mem_coe, f, he,
      Set.mem_univ, and_self]
  have hinj : Set.InjOn f T := by
    intro e he e' _ hf
    rw [hT] at he
    simp only [f, Prod.mk.injEq] at hf
    exact Subtype.ext (eq_of_bondOf_eq S e.2 e'.2 he hf.1 hf.2)
  calc T.card ≤ ((cutBonds S ×ˢ (Finset.univ : Finset (Fin M))) ×ˢ
        (Finset.univ : Finset Bool)).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = 2 * M * (cutBonds S).card := by
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_bool]
      ring

/-! ### The cross-block rank bound -/

lemma rank_neg' {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    (-X).rank = X.rank := by
  rw [← neg_one_smul ℝ X]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors X
    (mem_nonZeroDivisors_of_ne_zero (by norm_num))

/-- Proposed Theorem (cross-block rank): `rank C_S ≤ 2 M b(S)`. -/
theorem rank_crossBlock_periodicCovariance_le
    (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) (S : Finset (Fin N)) :
    (crossBlock S (periodicCovariance Γ)).rank ≤ 2 * M * (cutBonds S).card := by
  have hpure : Pure (periodicBond N M) := pure_bond
  have hinv' : IsUnit (1 - (periodicInput Γ).toBlocks₂₂ * periodicBond N M).det := hinv
  set Mtot := periodicBond N M + (periodicInput Γ).toBlocks₂₂ with hMtot
  have hMdet : IsUnit Mtot.det := isUnit_det_add_of_pure hpure hinv'
  have hcov : periodicCovariance Γ = (periodicInput Γ).toBlocks₁₁ +
      (periodicInput Γ).toBlocks₁₂ * (-Mtot⁻¹) * (periodicInput Γ).toBlocks₂₁ := by
    unfold periodicCovariance contract
    rw [Matrix.mul_assoc (periodicInput Γ).toBlocks₁₂,
      mul_inv_one_sub_mul_eq_neg_inv_add_of_pure hpure hinv']
  have hsplit : crossBlock S (periodicCovariance Γ) =
      crossBlock S ((periodicInput Γ).toBlocks₁₂ * (-Mtot⁻¹) * (periodicInput Γ).toBlocks₂₁) := by
    rw [hcov]
    unfold crossBlock
    rw [Matrix.submatrix_add]
    change crossBlock S (periodicInput Γ).toBlocks₁₁ + _ = _
    rw [crossBlock_toBlocks₁₁_periodicInput, zero_add]
  rw [hsplit, crossBlock_mul_mul_eq S (fun a e ha he => toBlocks₁₂_periodicInput_eq_zero Γ ha he)
    (fun e b he hb => toBlocks₂₁_periodicInput_eq_zero Γ he hb)]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  have hneg : ((-Mtot⁻¹).submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂ =
      -((Mtot.submatrix (elimEquiv S) (elimEquiv S))⁻¹).toBlocks₁₂ := by
    rw [Matrix.inv_submatrix_equiv]
    rfl
  have hMdet' : IsUnit (Mtot.submatrix (elimEquiv S) (elimEquiv S)).det := by
    rwa [Matrix.det_submatrix_equiv_self]
  have hblock : (Mtot.submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂ =
      ((periodicBond N M).submatrix (elimEquiv S) (elimEquiv S)).toBlocks₁₂ := by
    ext e e'
    simp only [hMtot, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, Matrix.add_apply,
      elimEquiv, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    rw [toBlocks₂₂_periodicInput_eq_zero Γ e.2 e'.2, add_zero]
  rw [hneg, rank_neg', rank_toBlocks12_inv _ hMdet', hblock]
  exact rank_toBlocks12_periodicBond_submatrix_le S

/-! ### The entanglement rank of a pure periodic covariance -/

/-- The retained labels split into those of `S` and those of its complement. -/
def cutRetainedEquiv (S : Finset (Fin N)) :
    RetainedIn (P := P) S ⊕ RetainedOut (P := P) S ≃ Retained N P :=
  Equiv.sumCompl fun a => siteRetained a ∈ S

/-- Proposed Corollary (entanglement rank), identity: for pure `X`, `1 + Γ_S² = C_S C_Sᵀ`. -/
theorem one_add_blockCov_sq_eq (S : Finset (Fin N)) {X : Matrix (Retained N P) (Retained N P) ℝ}
    (hX : Pure X) :
    1 + blockCov S X * blockCov S X = crossBlock S X * (crossBlock S X).transpose := by
  set X' := X.submatrix (cutRetainedEquiv S) (cutRetainedEquiv S) with hX'
  have hT : X'.transpose = -X' := by
    rw [hX', Matrix.transpose_submatrix, hX.1]; rfl
  have hsq : X' * X' = -1 := by
    rw [hX', Matrix.submatrix_mul_equiv X X _ (cutRetainedEquiv S) _, hX.2]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, (cutRetainedEquiv S).injective.eq_iff]
  obtain ⟨-, -, hC, -⟩ := toBlocks_of_transpose_eq_neg hT
  have hC' : X'.toBlocks₂₁ = -X'.toBlocks₁₂.transpose := by rw [hC, neg_neg]
  have h11 : X'.toBlocks₁₁ = blockCov S X := by
    ext a b; simp [X', Matrix.toBlocks₁₁, blockCov, cutRetainedEquiv]
  have h12 : X'.toBlocks₁₂ = crossBlock S X := by
    ext a b; simp [X', Matrix.toBlocks₁₂, crossBlock, cutRetainedEquiv]
  have hmul := congrArg Matrix.toBlocks₁₁ hsq
  rw [← Matrix.fromBlocks_toBlocks X', Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, Matrix.toBlocks_fromBlocks₁₁] at hmul
  rw [hC', Matrix.mul_neg, h11, h12] at hmul
  -- hmul : blockCov * blockCov + -(cross * crossᵀ) = -1
  calc 1 + blockCov S X * blockCov S X
      = blockCov S X * blockCov S X + -(crossBlock S X * (crossBlock S X).transpose) +
          crossBlock S X * (crossBlock S X).transpose + 1 := by abel
    _ = -1 + crossBlock S X * (crossBlock S X).transpose + 1 := by rw [hmul]
    _ = crossBlock S X * (crossBlock S X).transpose := by abel

/-- Proposed Corollary, bound: `rank (1 + Γ_S²) ≤ 2 M b(S)` for the pure periodic covariance. -/
theorem rank_one_add_blockCov_sq_le (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M))
    (hpure : Pure (periodicCovariance Γ)) (S : Finset (Fin N)) :
    (1 + blockCov S (periodicCovariance Γ) * blockCov S (periodicCovariance Γ)).rank
      ≤ 2 * M * (cutBonds S).card := by
  rw [one_add_blockCov_sq_eq S hpure, Matrix.rank_self_mul_transpose]
  exact rank_crossBlock_periodicCovariance_le Γ hinv S

/-- For `Γ = O D(λ) Oᵀ` with `O Oᵀ = 1`, `rank (1 + Γ²) = 2 · #{j : λ_j² ≠ 1}`. -/
theorem rank_one_add_sq_normalForm {n : ℕ} {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hOO : O * O.transpose = 1) (lam : Fin n → ℝ) :
    (1 + (O * blockForm lam * O.transpose) * (O * blockForm lam * O.transpose)).rank
      = 2 * (Finset.univ.filter fun j => lam j ^ 2 ≠ 1).card := by
  have hOO' : O.transpose * O = 1 := mul_eq_one_comm.mp hOO
  have hdet : IsUnit O.det := Matrix.isUnit_det_of_right_inverse hOO
  have hdetT : IsUnit O.transpose.det := by rw [Matrix.det_transpose]; exact hdet
  set w : Fin n → ℝ := fun j => 1 - lam j ^ 2 with hw
  have hmid : 1 + (O * blockForm lam * O.transpose) * (O * blockForm lam * O.transpose) =
      O * Matrix.diagonal (Sum.elim w w) * O.transpose := by
    have h1 : (O * blockForm lam * O.transpose) * (O * blockForm lam * O.transpose) =
        O * (blockForm lam * blockForm lam) * O.transpose := by
      calc (O * blockForm lam * O.transpose) * (O * blockForm lam * O.transpose)
          = O * blockForm lam * (O.transpose * O) * blockForm lam * O.transpose := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hOO', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h1, blockForm_mul_blockForm]
    have hone : (1 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) = O * 1 * O.transpose := by
      rw [Matrix.mul_one, hOO]
    conv_lhs => rw [hone]
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, hw, sq] <;>
      split_ifs <;> ring
  rw [hmid, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetT,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal]
  have hcard : Fintype.card {i : MajoranaIndex n // Sum.elim w w i ≠ 0} =
      2 * (Finset.univ.filter fun j => lam j ^ 2 ≠ 1).card := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : MajoranaIndex n => Sum.elim w w i ≠ 0) =
        (Finset.univ.filter fun j => lam j ^ 2 ≠ 1).disjSum
          (Finset.univ.filter fun j => lam j ^ 2 ≠ 1) := by
      ext i
      rcases i with j | j <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjSum,
          Sum.inl.injEq, Sum.inr.injEq, exists_eq_right, Sum.elim_inl, Sum.elim_inr, hw, ne_eq,
          sub_eq_zero, reduceCtorEq, and_false, exists_false, or_false, false_or] <;>
        exact not_congr eq_comm
    rw [this, Finset.card_disjSum]; ring
  exact hcard

end Fermionic
