/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Realization
import FermionicLean.Fock.Thermal

/-! # Wick's rule and the Gaussian class

A density operator `ρ` is Gaussian when every moment `Tr (ρ (v₁·c) ⋯ (vₘ·c))` of linear
combinations `v·c = ∑ a, v a • c_a` equals the Wick expansion `W_G (v₁, …, vₘ)` of its two-point
matrix `G = 1 - i Γ(ρ)` (Definition 1). The Wick expansion is defined by the recursion
`W_G (v₁, …, vₘ) = ∑_{j ≥ 2} (-1)^j (v₁ᵀ G vⱼ) W_G (v₂, …, v̂ⱼ, …, vₘ)`; it is multilinear and
vanishes on odd lists (Lemma 2). The Gaussian class is closed under conjugation by an implementing
unitary (Theorem 3); one factor moves through a product with alternating signs (Lemma 4), and a
recursion criterion for the removal of one Majorana factor implies Wick's rule (Lemma 5).
-/

open scoped ComplexOrder
open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### Definition 1 -/

/-- Definition 1: the linear combination `v·c = ∑ a, v a • c_a`. -/
def lincomb (v : MajoranaIndex n → ℂ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  ∑ a, v a • majorana a

/-- Definition 1: the two-point matrix `G(ρ) = 1 - i Γ(ρ)`, a complex matrix on the labels. -/
noncomputable def twoPoint (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ :=
  1 - Complex.I • (covariance ρ).map (fun x : ℝ => (x : ℂ))

lemma twoPoint_apply (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) (a b : MajoranaIndex n) :
    twoPoint ρ a b = (if a = b then 1 else 0) - Complex.I * ((covariance ρ a b : ℝ) : ℂ) := by
  simp [twoPoint, Matrix.one_apply]

/-- Definition 1: the Wick expansion of a list of vectors, `W_G () = 1` and
`W_G (v₁, …, vₘ) = ∑_{j=2}^m (-1)^j (v₁ᵀ G vⱼ) W_G (v₂, …, v̂ⱼ, …, vₘ)`. The tail `l = (v₂, …, vₘ)`
is indexed from `0`, so the plan's position `j` is `j' + 2` and its sign `(-1)^j = (-1)^j'`. -/
noncomputable def wick (G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ) :
    List (MajoranaIndex n → ℂ) → ℂ
  | [] => 1
  | v :: l => ∑ j : Fin l.length,
      (-1) ^ (j : ℕ) * (v ⬝ᵥ G *ᵥ l[(j : ℕ)]) * wick G (l.eraseIdx j)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  have := List.length_eraseIdx_le l j
  omega

/-- Definition 1: the moment `Tr (ρ (v₁·c) ⋯ (vₘ·c))` of the list `(v₁, …, vₘ)`. -/
noncomputable def momentList (ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (l : List (MajoranaIndex n → ℂ)) : ℂ :=
  (ρ * (l.map lincomb).prod).trace

/-- Definition 1: a density operator is Gaussian when every moment is the Wick expansion of its
two-point matrix. -/
def IsGaussian (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) : Prop :=
  IsDensity ρ ∧ ∀ l : List (MajoranaIndex n → ℂ), momentList ρ l = wick (twoPoint ρ) l

variable {G : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ}

@[simp] theorem wick_nil : wick G [] = 1 := by
  rw [wick]

theorem wick_cons (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    wick G (v :: l) =
      ∑ j : Fin l.length, (-1) ^ (j : ℕ) * (v ⬝ᵥ G *ᵥ l[(j : ℕ)]) * wick G (l.eraseIdx j) := by
  rw [wick]

/-- `wick_cons` with the tail length named, for lists whose length is only propositionally known. -/
theorem wick_cons' (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) {m : ℕ}
    (hm : l.length = m) :
    wick G (v :: l) = ∑ j : Fin m,
      (-1) ^ (j : ℕ) * (v ⬝ᵥ G *ᵥ l[(j : ℕ)]'(by omega)) * wick G (l.eraseIdx j) := by
  subst hm
  exact wick_cons v l

/-- Lemma 2: `W_G (v) = 0`. -/
@[simp] theorem wick_singleton (v : MajoranaIndex n → ℂ) : wick G [v] = 0 := by
  simp [wick_cons]

/-- Lemma 2: `W_G (v, w) = vᵀ G w`. -/
@[simp] theorem wick_pair (v w : MajoranaIndex n → ℂ) : wick G [v, w] = v ⬝ᵥ G *ᵥ w := by
  simp [wick_cons]

/-- Lemma 2: the Wick expansion vanishes on lists of odd length. -/
theorem wick_odd (l : List (MajoranaIndex n → ℂ)) (hl : Odd l.length) : wick G l = 0 := by
  obtain ⟨k, hk⟩ := hl
  induction k generalizing l with
  | zero =>
    match l, hk with
    | [v], _ => exact wick_singleton v
  | succ k ih =>
    match l, hk with
    | v :: l, hk =>
      rw [wick_cons]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ih (l.eraseIdx j), mul_zero]
      rw [List.length_eraseIdx_of_lt j.isLt]
      simp only [List.length_cons] at hk
      omega

/-- Lemma 2(a): linearity in the first entry, sums. -/
theorem wick_add_head (v v' : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    wick G ((v + v') :: l) = wick G (v :: l) + wick G (v' :: l) := by
  simp only [wick_cons, add_dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lemma 2(a): linearity in the first entry, scalars. -/
theorem wick_smul_head (c : ℂ) (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    wick G ((c • v) :: l) = c * wick G (v :: l) := by
  simp only [wick_cons, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lemma 2(a): the first entry expanded in the labels, `W_G (v, l) = ∑ a, v a • W_G (e_a, l)`
in the form used by the recursion criterion. -/
theorem wick_cons_eq_sum (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    wick G (v :: l) = ∑ a, v a *
      ∑ j : Fin l.length, (-1) ^ (j : ℕ) * (G *ᵥ l[(j : ℕ)]) a * wick G (l.eraseIdx j) := by
  rw [wick_cons]
  simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### Lemma 2(b), (c): the two-point rule and the anticommutator -/

/-- `Tr (ρ c_a c_b) = G(ρ)_ab` for a density operator. -/
lemma trace_mul_majorana_mul_majorana {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) (a b : MajoranaIndex n) :
    (ρ * (majorana a * majorana b)).trace = twoPoint ρ a b := by
  rw [majorana_mul_eq, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, hρ.2,
    twoPoint_apply, coe_covariance hρ.1.isHermitian]
  linear_combination ((ρ * commutator a b).trace / 2) * Complex.I_sq

/-- Lemma 2(b): `Tr (ρ (v·c) (w·c)) = vᵀ G(ρ) w` for a density operator. -/
theorem trace_mul_lincomb_mul_lincomb {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) (v w : MajoranaIndex n → ℂ) :
    (ρ * (lincomb v * lincomb w)).trace = v ⬝ᵥ twoPoint ρ *ᵥ w := by
  simp only [lincomb, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, trace_mul_majorana_mul_majorana hρ, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Lemma 2(b): Wick's rule at `m = 2` holds for every density operator. -/
theorem momentList_pair {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsDensity ρ)
    (v w : MajoranaIndex n → ℂ) : momentList ρ [v, w] = wick (twoPoint ρ) [v, w] := by
  rw [momentList, wick_pair, ← trace_mul_lincomb_mul_lincomb hρ]
  simp

/-- Lemma 2(b): Wick's rule at `m = 0` holds for every density operator. -/
theorem momentList_nil {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsDensity ρ) :
    momentList ρ [] = wick (twoPoint ρ) [] := by
  simp [momentList, hρ.2]

/-- Lemma 2(c): `(u·c) (w·c) + (w·c) (u·c) = 2 (uᵀ w) 1`. -/
theorem lincomb_anticommute (u w : MajoranaIndex n → ℂ) :
    lincomb u * lincomb w + lincomb w * lincomb u =
      (2 * (u ⬝ᵥ w)) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) := by
  have h : ∀ a b, (w a * u b) • (majorana b * majorana a) +
      (u b * w a) • (majorana a * majorana b) =
      (u b * w a) •
        ((if a = b then (2 : ℂ) else 0) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ)) := by
    intro a b
    rw [mul_comm (w a), ← smul_add, add_comm, majorana_anticommute]
  simp only [lincomb, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (f := fun a b => (u a * w b) • (majorana b * majorana a))]
  simp only [← Finset.sum_add_distrib, h, smul_smul, dotProduct, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  ring

/-! ### Theorem 3: transport by an implementing unitary -/

section Transport

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- `U (v·c) U* = (Oᵀ v)·c` when `U` implements `O`; the vector `Oᵀ v` is
`b ↦ ∑ a, O a b * v a`, written with `O` coerced to a complex matrix. -/
theorem conj_lincomb (hO : ConjugatesMajorana U O) (v : MajoranaIndex n → ℂ) :
    U * lincomb v * U.conjTranspose = lincomb ((O.map Complex.ofReal).transpose *ᵥ v) := by
  unfold ConjugatesMajorana at hO
  simp only [lincomb, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hO,
    Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

/-- Conjugation distributes over a product of matrices. -/
lemma conj_list_prod (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (L : List (Matrix (FockIndex n) (FockIndex n) ℂ)) :
    U * L.prod * U.conjTranspose = (L.map fun X => U * X * U.conjTranspose).prod := by
  induction L with
  | nil => simp [hU]
  | cons X L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih, conj_mul_conj hU']

/-- `W_G (Mᵀ v₁, …, Mᵀ vₘ) = W_{M G Mᵀ} (v₁, …, vₘ)` for every complex matrix `M`. -/
theorem wick_map_transpose (M : Matrix (MajoranaIndex n) (MajoranaIndex n) ℂ)
    (l : List (MajoranaIndex n → ℂ)) :
    wick G (l.map fun v => M.transpose *ᵥ v) = wick (M * G * M.transpose) l := by
  suffices h : ∀ k, ∀ l : List (MajoranaIndex n → ℂ), l.length ≤ k →
      wick G (l.map fun v => M.transpose *ᵥ v) = wick (M * G * M.transpose) l from
    h l.length l le_rfl
  intro k
  induction k with
  | zero =>
    intro l hl
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    simp
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | v :: l =>
      rw [List.map_cons, wick_cons' _ _ (List.length_map ..), wick_cons]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.getElem_map, List.eraseIdx_map, ih (l.eraseIdx j)
        ((List.length_eraseIdx_le l j).trans (by simpa using hl))]
      congr 2
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/-- Theorem 3: the two-point matrix transports by `G ↦ O G Oᵀ`. -/
theorem twoPoint_conj (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) :
    twoPoint (U.conjTranspose * ρ * U) =
      O.map Complex.ofReal * twoPoint ρ * (O.map Complex.ofReal).transpose := by
  have hOO : O * O.transpose = 1 := orthogonal_of_conjugatesMajorana hU' hO
  have hOOc : O.map Complex.ofReal * (O.map Complex.ofReal).transpose = 1 := by
    have h := congrArg Complex.ofRealHom.mapMatrix hOO
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.transpose_map] at h
    exact h
  have hmap : (O * covariance ρ * O.transpose).map Complex.ofReal =
      O.map Complex.ofReal * (covariance ρ).map Complex.ofReal *
        (O.map Complex.ofReal).transpose := by
    change (O * covariance ρ * O.transpose).map Complex.ofRealHom =
      O.map Complex.ofRealHom * (covariance ρ).map Complex.ofRealHom *
        (O.map Complex.ofRealHom).transpose
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [twoPoint, twoPoint, (covariance_conj' hU hU' hO hρ).2, hmap, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, hOOc, Matrix.mul_smul, Matrix.smul_mul]

/-- Theorem 3: the Gaussian class is closed under conjugation by an implementing unitary. -/
theorem isGaussian_conj (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) : IsGaussian (U.conjTranspose * ρ * U) := by
  refine ⟨(covariance_conj' hU hU' hO hρ.1).1, fun l => ?_⟩
  rw [twoPoint_conj hU hU' hO hρ.1, ← wick_map_transpose, ← hρ.2, momentList, momentList,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    conj_list_prod hU hU', List.map_map, List.map_map]
  congr 3
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, conj_lincomb hO]

end Transport

/-! ### Lemma 4: moving one factor through a product -/

/-- Lemma 4, first identity, with the length of the list named (for the induction). -/
theorem lincomb_mul_prod' (u : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) {k : ℕ}
    (hk : l.length = k) :
    lincomb u * (l.map lincomb).prod =
      ∑ i : Fin k, ((-1) ^ (i : ℕ) * (2 * (u ⬝ᵥ l[(i : ℕ)]'(by omega)))) •
        ((l.eraseIdx i).map lincomb).prod +
      ((-1 : ℂ) ^ k) • ((l.map lincomb).prod * lincomb u) := by
  induction l generalizing k with
  | nil =>
    subst hk
    simp
  | cons w l ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hk' : l.length = k := by simpa using hk
      rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc,
        eq_sub_of_add_eq (lincomb_anticommute u w), Matrix.sub_mul, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_assoc, ih hk', Matrix.mul_add, Matrix.mul_sum,
        Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_mul, List.getElem_cons_zero,
        List.getElem_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.map_cons,
        List.prod_cons, Matrix.mul_smul, pow_succ, Matrix.mul_assoc]
      rw [sub_eq_add_neg, neg_add, ← Finset.sum_neg_distrib, add_assoc]
      congr 2
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← neg_smul]
        congr 1
        ring
      · rw [← neg_smul]
        congr 1
        ring

/-- Lemma 4, first identity: `b X = ∑ᵢ (-1)^i 2 (uᵀ wᵢ) X_î + (-1)^k X b` for `b = u·c` and
`X = (w₀·c) ⋯ (w_{k-1}·c)`, the factors indexed from `0` (the plan's `(-1)^(i-1)`, `i ≥ 1`). -/
theorem lincomb_mul_prod (u : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    lincomb u * (l.map lincomb).prod =
      ∑ i : Fin l.length, ((-1) ^ (i : ℕ) * (2 * (u ⬝ᵥ l[(i : ℕ)]))) •
        ((l.eraseIdx i).map lincomb).prod +
      ((-1 : ℂ) ^ l.length) • ((l.map lincomb).prod * lincomb u) :=
  lincomb_mul_prod' u l rfl

/-- The sign `(-1)^(k-1-j) = -(-1)^k (-1)^j` for `j < k`. -/
lemma neg_one_pow_sub_one_sub {k j : ℕ} (hj : j < k) :
    (-1 : ℂ) ^ (k - 1 - j) = -((-1) ^ k * (-1) ^ j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have h2 : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by
    rw [← mul_pow]; simp
  rw [show j + m + 1 - 1 - j = m by omega, pow_add, pow_add, pow_one]
  linear_combination (-(-1 : ℂ) ^ m) * h2

/-- Lemma 4, second identity: `X b = ∑ᵢ (-1)^(k-1-i) 2 (uᵀ wᵢ) X_î + (-1)^k b X` (the plan's
`(-1)^(k-i)` with `i ≥ 1`); it is the first identity solved for `X b`. -/
theorem prod_mul_lincomb (u : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    (l.map lincomb).prod * lincomb u =
      ∑ i : Fin l.length, ((-1) ^ (l.length - 1 - (i : ℕ)) * (2 * (u ⬝ᵥ l[(i : ℕ)]))) •
        ((l.eraseIdx i).map lincomb).prod +
      ((-1 : ℂ) ^ l.length) • (lincomb u * (l.map lincomb).prod) := by
  have hsq : ((-1 : ℂ) ^ l.length) * (-1) ^ l.length = 1 := by
    rw [← mul_pow]; simp
  rw [lincomb_mul_prod, smul_add, smul_smul, hsq, one_smul, ← add_assoc, Finset.smul_sum]
  simp only [smul_smul]
  rw [← Finset.sum_add_distrib]
  simp only [← add_smul]
  rw [Finset.sum_eq_zero fun i _ => ?_, zero_add]
  rw [neg_one_pow_sub_one_sub i.isLt]
  convert zero_smul ℂ _ using 2
  ring

/-! ### Lemma 5: the recursion criterion -/

/-- The moment of `v :: l` expanded in the labels of the first factor. -/
lemma momentList_cons_eq_sum (ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)) :
    momentList ρ (v :: l) = ∑ a, v a * (ρ * (majorana a * (l.map lincomb).prod)).trace := by
  simp only [momentList, List.map_cons, List.prod_cons, lincomb, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- Lemma 5: a density operator whose odd moments vanish (i) and whose moments with a leading
Majorana factor `c_a` obey the recursion (ii),
`Tr (ρ c_a (w₀·c) ⋯ (w_{k-1}·c)) = ∑ᵢ (-1)^i (G wᵢ)_a Tr (ρ X_î)` for every label `a` and every
list of odd length `k`, is Gaussian. -/
theorem isGaussian_of_recursion {ρ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ : IsDensity ρ)
    (hodd : ∀ l : List (MajoranaIndex n → ℂ), Odd l.length → momentList ρ l = 0)
    (hrec : ∀ (a : MajoranaIndex n) (l : List (MajoranaIndex n → ℂ)), Odd l.length →
      (ρ * (majorana a * (l.map lincomb).prod)).trace =
        ∑ i : Fin l.length,
          (-1) ^ (i : ℕ) * (twoPoint ρ *ᵥ l[(i : ℕ)]) a * momentList ρ (l.eraseIdx i)) :
    IsGaussian ρ := by
  refine ⟨hρ, fun l => ?_⟩
  suffices h : ∀ k, ∀ l : List (MajoranaIndex n → ℂ), l.length ≤ k →
      momentList ρ l = wick (twoPoint ρ) l from h l.length l le_rfl
  intro k
  induction k with
  | zero =>
    intro l hl
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact momentList_nil hρ
  | succ k ih =>
    intro l hl
    rcases Nat.even_or_odd l.length with he | ho
    · match l with
      | [] => exact momentList_nil hρ
      | v :: l =>
        have hlo : Odd l.length := by
          rw [List.length_cons, Nat.even_add_one] at he
          exact Nat.not_even_iff_odd.mp he
        rw [wick_cons_eq_sum, momentList_cons_eq_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hrec a l hlo]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ih (l.eraseIdx i)
          ((List.length_eraseIdx_le l i).trans (by simpa using hl))]
    · rw [hodd l ho, wick_odd l ho]

end Fermionic
