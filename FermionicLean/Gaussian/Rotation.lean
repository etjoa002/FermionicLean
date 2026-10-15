/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Option
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Plane rotations generate the special orthogonal group

`planeRot c s a b` is the rotation of the plane `(a, b)` of a finite label type: rows `a`
and `b` are `(c, -s)` and `(s, c)` on the columns `(a, b)`, every other row is that of the
identity; `c² + s² = 1`. A rotation product is a finite product of plane rotations. Every
real matrix `O` with `O Oᵀ = 1` and `det O = 1` is a rotation product (Theorem 14), by the
Givens reduction: rotations in the planes `(a, i)` bring the column `i` of `O` to the unit
vector `e_i`, the remaining block is special orthogonal on the labels other than `i`, and
`Fintype.induction_empty_option` closes the induction.
-/

open Matrix

namespace Fermionic

variable {ι : Type*} [DecidableEq ι]

/-- Definition 13: the plane rotation `R_ab(c, s)`. -/
def planeRot (c s : ℝ) (a b : ι) : Matrix ι ι ℝ :=
  fun u v =>
    if u = a then (if v = a then c else if v = b then -s else 0)
    else if u = b then (if v = a then s else if v = b then c else 0)
    else if v = u then 1 else 0

section PlaneRot

variable {c s : ℝ} {a b : ι}

lemma planeRot_apply_of_ne {u v : ι} (hua : u ≠ a) (hub : u ≠ b) :
    planeRot c s a b u v = if v = u then 1 else 0 := by
  simp [planeRot, hua, hub]

lemma planeRot_a_apply (v : ι) :
    planeRot c s a b a v = if v = a then c else if v = b then -s else 0 := by
  simp [planeRot]

lemma planeRot_b_apply (hab : a ≠ b) (v : ι) :
    planeRot c s a b b v = if v = a then s else if v = b then c else 0 := by
  simp [planeRot, Ne.symm hab]

lemma planeRot_transpose (hab : a ≠ b) :
    (planeRot c s a b).transpose = planeRot c (-s) a b := by
  ext u v
  simp only [Matrix.transpose_apply, planeRot, neg_neg]
  by_cases hua : u = a <;> by_cases hub : u = b <;> by_cases hva : v = a <;>
    by_cases hvb : v = b <;> simp_all [eq_comm]

variable [Fintype ι]

omit [DecidableEq ι] in
/-- A row supported on `{a, b}` times a matrix. -/
lemma mul_apply_two {R M : Matrix ι ι ℝ} (hab : a ≠ b) {u : ι}
    (hR : ∀ w, w ≠ a → w ≠ b → R u w = 0) (v : ι) :
    (R * M) u v = R u a * M a v + R u b * M b v := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_add a b hab (fun w _ hw => by rw [hR w hw.1 hw.2, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ b) h)

/-- The rows outside the plane are those of the identity. -/
lemma planeRot_mul_apply_of_ne (M : Matrix ι ι ℝ) {u : ι} (hua : u ≠ a) (hub : u ≠ b) (v : ι) :
    (planeRot c s a b * M) u v = M u v := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u]
  · rw [planeRot_apply_of_ne hua hub]; simp
  · intro w _ hw; rw [planeRot_apply_of_ne hua hub]; simp [hw]
  · simp

/-- The coordinates outside the plane are unchanged by `R_ab *ᵥ`. -/
lemma planeRot_mul_apply_of_ne_vec (x : ι → ℝ) {u : ι} (hua : u ≠ a)
    (hub : u ≠ b) :
    (planeRot c s a b *ᵥ x) u = x u := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single u]
  · rw [planeRot_apply_of_ne hua hub]; simp
  · intro w _ hw; rw [planeRot_apply_of_ne hua hub]; simp [hw]
  · simp

set_option linter.flexible false in
/-- `R_ab(c, s) R_ab(c, -s) = 1` when `c² + s² = 1`. -/
lemma planeRot_mul_transpose (hab : a ≠ b) (hcs : c * c + s * s = 1) :
    planeRot c s a b * (planeRot c s a b).transpose = 1 := by
  rw [planeRot_transpose hab]
  ext u v
  by_cases hua : u = a
  · subst hua
    rw [mul_apply_two hab (fun w hwa hwb => by simp [planeRot, hwa, hwb]),
      planeRot_a_apply, planeRot_a_apply, planeRot_a_apply, planeRot_b_apply hab]
    by_cases hva : v = u <;> by_cases hvb : v = b <;> simp_all [Ne.symm hab, Matrix.one_apply]
    all_goals first | ring1 | linear_combination hcs | linarith | exact fun h => hva h.symm
  · by_cases hub : u = b
    · subst hub
      rw [mul_apply_two hab (fun w hwa hwb => by simp [planeRot, hwa, hwb, Ne.symm hab]),
        planeRot_b_apply hab, planeRot_b_apply hab, planeRot_a_apply, planeRot_b_apply hab]
      by_cases hva : v = a <;> by_cases hvb : v = u <;>
        simp_all [Ne.symm hab, Matrix.one_apply]
      all_goals first | ring1 | linear_combination hcs | linarith | exact fun h => hvb h.symm
    · rw [planeRot_mul_apply_of_ne _ hua hub, planeRot_apply_of_ne hua hub, Matrix.one_apply]
      by_cases h : u = v
      · subst h; simp
      · simp [h, Ne.symm h]

lemma transpose_mul_planeRot (hab : a ≠ b) (hcs : c * c + s * s = 1) :
    (planeRot c s a b).transpose * planeRot c s a b = 1 :=
  mul_eq_one_comm.mp (planeRot_mul_transpose hab hcs)

/-- `det R_ab(c, s) = c² + s²`. -/
lemma det_planeRot (hab : a ≠ b) : (planeRot c s a b).det = c * c + s * s := by
  -- rows `a` and `b` of the identity updated
  have hR : planeRot c s a b =
      Matrix.updateRow (Matrix.updateRow 1 a (c • Pi.single a 1 + (-s) • Pi.single b 1)) b
        (s • Pi.single a 1 + c • Pi.single b 1) := by
    ext u v
    by_cases hub : u = b
    · subst hub
      simp [planeRot_b_apply hab, Matrix.updateRow_self, Pi.single_apply]
      split_ifs <;> simp_all
    · rw [Matrix.updateRow_ne hub]
      by_cases hua : u = a
      · subst hua
        simp [planeRot_a_apply, Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp_all
      · rw [Matrix.updateRow_ne hua, planeRot_apply_of_ne hua hub, Matrix.one_apply]
        by_cases h : u = v
        · subst h; simp
        · simp [h, Ne.symm h]
  rw [hR, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]
  -- second term: row `b` of `updateRow 1 a r` is `e_b` already
  have h2 : Matrix.updateRow (Matrix.updateRow 1 a (c • Pi.single a 1 + (-s) • Pi.single b 1)) b
      (Pi.single b 1) = Matrix.updateRow 1 a (c • Pi.single a 1 + (-s) • Pi.single b 1) := by
    conv_rhs => rw [← Matrix.updateRow_eq_self (Matrix.updateRow 1 a _) b]
    congr 1
    rw [Matrix.updateRow_ne hab.symm]
    ext v; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h2, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]
  have h1a : Matrix.updateRow (1 : Matrix ι ι ℝ) a (Pi.single a 1) = 1 := by
    conv_rhs => rw [← Matrix.updateRow_eq_self (1 : Matrix ι ι ℝ) a]
    congr 1; ext v; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have h1b : (Matrix.updateRow (1 : Matrix ι ι ℝ) a (Pi.single b 1)).det = 0 := by
    apply Matrix.det_zero_of_row_eq hab
    rw [Matrix.updateRow_self, Matrix.updateRow_ne hab.symm]
    ext v; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  -- first term: row `b` is `e_a`; commute the two updates and expand row `a`
  set N : Matrix ι ι ℝ := Matrix.updateRow 1 b (Pi.single a 1) with hN
  have hcomm : Matrix.updateRow (Matrix.updateRow (1 : Matrix ι ι ℝ) a
      (c • Pi.single a 1 + (-s) • Pi.single b 1)) b (Pi.single a 1) =
      Matrix.updateRow N a (c • Pi.single a 1 + (-s) • Pi.single b 1) :=
    Matrix.updateRow_comm _ hab _ _
  have h3a : (Matrix.updateRow N a (Pi.single a 1)).det = 0 := by
    apply Matrix.det_zero_of_row_eq hab
    rw [Matrix.updateRow_self, Matrix.updateRow_ne hab.symm, hN, Matrix.updateRow_self]
  have h3b : (Matrix.updateRow N a (Pi.single b 1)).det = -1 := by
    -- the transposition of rows `a` and `b` of the identity
    have : Matrix.updateRow N a (Pi.single b 1) =
        (1 : Matrix ι ι ℝ).submatrix (Equiv.swap a b) id := by
      ext u v
      by_cases hua : u = a
      · subst hua
        rw [Matrix.updateRow_self, Matrix.submatrix_apply, Equiv.swap_apply_left]
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      · rw [Matrix.updateRow_ne hua]
        by_cases hub : u = b
        · subst hub
          rw [hN, Matrix.updateRow_self, Matrix.submatrix_apply, Equiv.swap_apply_right]
          simp [Matrix.one_apply, Pi.single_apply, eq_comm]
        · rw [hN, Matrix.updateRow_ne hub, Matrix.submatrix_apply,
            Equiv.swap_apply_of_ne_of_ne hua hub]
          rfl
    rw [this, Matrix.det_permute, Matrix.det_one, Equiv.Perm.sign_swap hab]
    simp
  rw [hcomm, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul, h3a,
    h3b, h1a, Matrix.det_one, h1b]
  ring

end PlaneRot

/-! ### Rotation products -/

variable [Fintype ι]

/-- Definition 13: a finite product of plane rotations. -/
inductive IsRotProduct : Matrix ι ι ℝ → Prop
  | one : IsRotProduct 1
  | mul_planeRot {R : Matrix ι ι ℝ} {c s : ℝ} {a b : ι} (hR : IsRotProduct R) (hab : a ≠ b)
      (hcs : c * c + s * s = 1) : IsRotProduct (R * planeRot c s a b)

namespace IsRotProduct

theorem planeRot {c s : ℝ} {a b : ι} (hab : a ≠ b) (hcs : c * c + s * s = 1) :
    IsRotProduct (planeRot c s a b) := by
  simpa using IsRotProduct.mul_planeRot IsRotProduct.one hab hcs

theorem mul {R S : Matrix ι ι ℝ} (hR : IsRotProduct R) (hS : IsRotProduct S) :
    IsRotProduct (R * S) := by
  induction hS with
  | one => simpa using hR
  | mul_planeRot hS' hab hcs ih => rw [← Matrix.mul_assoc]; exact ih.mul_planeRot hab hcs

theorem mul_transpose_self {R : Matrix ι ι ℝ} (hR : IsRotProduct R) : R * R.transpose = 1 := by
  induction hR with
  | one => simp
  | mul_planeRot hS hab hcs ih =>
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Fermionic.planeRot _ _ _ _),
      planeRot_mul_transpose hab hcs, Matrix.one_mul, ih]

theorem transpose_mul_self {R : Matrix ι ι ℝ} (hR : IsRotProduct R) : R.transpose * R = 1 :=
  mul_eq_one_comm.mp hR.mul_transpose_self

theorem det {R : Matrix ι ι ℝ} (hR : IsRotProduct R) : R.det = 1 := by
  induction hR with
  | one => simp
  | mul_planeRot hS hab hcs ih => rw [Matrix.det_mul, ih, det_planeRot hab, hcs, one_mul]

theorem transpose {R : Matrix ι ι ℝ} (hR : IsRotProduct R) : IsRotProduct R.transpose := by
  induction hR with
  | one => simpa using IsRotProduct.one
  | mul_planeRot hS hab hcs ih =>
    rw [Matrix.transpose_mul, planeRot_transpose hab]
    exact (IsRotProduct.planeRot hab (by rw [neg_mul_neg]; exact hcs)).mul ih

end IsRotProduct

/-! ### The Givens reduction -/

section Givens

/-- The reduction of one coordinate: given a rotation product `G` and a label `a ≠ i`, a further
rotation in the plane `(a, i)` zeroes the coordinate `a` of `G v` and keeps the coordinates that
were already zero, making the coordinate `i` nonnegative. -/
lemma exists_zero_coord (v : ι → ℝ) (S : Finset ι) (i : ι) (hi : i ∉ S) :
    ∃ G : Matrix ι ι ℝ, IsRotProduct G ∧ (∀ a ∈ S, (G *ᵥ v) a = 0) ∧
      (∀ u, u ∉ S → u ≠ i → (G *ᵥ v) u = v u) ∧ (S.Nonempty → 0 ≤ (G *ᵥ v) i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, IsRotProduct.one, by simp, by simp, by simp⟩
  | insert a S haS ih =>
    have hi' : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
    have hai : a ≠ i := fun h => hi (h ▸ Finset.mem_insert_self a S)
    obtain ⟨G, hG, hzero, hkeep, hnn⟩ := ih hi'
    set w := G *ᵥ v with hw
    set r := Real.sqrt (w a * w a + w i * w i) with hr
    by_cases hr0 : r = 0
    · -- both coordinates already vanish
      have hsq : w a * w a + w i * w i = 0 := by
        have := Real.sqrt_eq_zero'.mp hr0
        have h0 : 0 ≤ w a * w a + w i * w i := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
        linarith
      have hwa : w a = 0 := by nlinarith [mul_self_nonneg (w a), mul_self_nonneg (w i)]
      have hwi : w i = 0 := by nlinarith [mul_self_nonneg (w a), mul_self_nonneg (w i)]
      refine ⟨G, hG, fun b hb => ?_, fun u hu hui => hkeep u (fun h => hu (Finset.mem_insert_of_mem h)) hui,
        fun _ => by rw [← hw, hwi]⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hwa
      · exact hzero b hb
    · have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
      have hrsq : r * r = w a * w a + w i * w i :=
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      -- rotate in the plane (a, i): rows a, i are (c, -s), (s, c) with c = w_i / r, s = w_a / r
      set c := w i / r with hc
      set s := w a / r with hs
      have hcs : c * c + s * s = 1 := by
        rw [hc, hs, div_mul_div_comm, div_mul_div_comm, ← add_div, add_comm, ← hrsq,
          div_self (mul_ne_zero hr0 hr0)]
      refine ⟨planeRot c s a i * G, (IsRotProduct.planeRot hai hcs).mul hG, ?_, ?_, ?_⟩
      · intro b hb
        rw [← Matrix.mulVec_mulVec]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · -- coordinate a: c w_a - s w_i = 0
          rw [Matrix.mulVec, dotProduct, Finset.sum_eq_add b i hai
            (fun x _ hx => by rw [planeRot_a_apply]; simp [hx.1, hx.2])
            (fun h => absurd (Finset.mem_univ b) h) (fun h => absurd (Finset.mem_univ i) h)]
          rw [planeRot_a_apply, planeRot_a_apply]
          simp only [ite_true, hai, ite_false, Ne.symm hai]
          rw [hc, hs]; field_simp; ring
        · have hba : b ≠ a := fun h => haS (h ▸ hb)
          have hbi : b ≠ i := fun h => hi' (h ▸ hb)
          rw [planeRot_mul_apply_of_ne_vec _ hba hbi]
          exact hzero b hb
      · intro u hu hui
        have hua : u ≠ a := fun h => hu (h ▸ Finset.mem_insert_self a S)
        have huS : u ∉ S := fun h => hu (Finset.mem_insert_of_mem h)
        rw [← Matrix.mulVec_mulVec, planeRot_mul_apply_of_ne_vec _ hua hui]
        exact hkeep u huS hui
      · intro _
        rw [← Matrix.mulVec_mulVec]
        -- coordinate i: s w_a + c w_i = r
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_add a i hai
          (fun x _ hx => by rw [planeRot_b_apply hai]; simp [hx.1, hx.2])
          (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ i) h)]
        rw [planeRot_b_apply hai, planeRot_b_apply hai]
        simp only [ite_true, hai, ite_false, Ne.symm hai]
        have : s * w a + c * w i = r := by
          rw [hc, hs]; field_simp; linarith [hrsq]
        rw [this]; exact hrpos.le

/-- Lifting a matrix on the labels other than `i` to all labels, acting as the identity on `i`:
here for `Option α` with `i = none`. -/
def liftOption {α : Type*} (M : Matrix α α ℝ) : Matrix (Option α) (Option α) ℝ :=
  Matrix.of fun u v =>
    match u, v with
    | some x, some y => M x y
    | none, none => 1
    | _, _ => 0

lemma liftOption_one {α : Type*} [DecidableEq α] : liftOption (1 : Matrix α α ℝ) = 1 := by
  ext (u | u) (v | v) <;> simp [liftOption, Matrix.one_apply]

lemma liftOption_mul {α : Type*} [Fintype α] (M N : Matrix α α ℝ) :
    liftOption (M * N) = liftOption M * liftOption N := by
  ext (u | u) (v | v) <;>
    simp [liftOption, Matrix.mul_apply, Fintype.sum_option]

lemma liftOption_planeRot {α : Type*} [DecidableEq α] (c s : ℝ) (a b : α) :
    liftOption (planeRot c s a b) = planeRot c s (some a) (some b) := by
  ext (u | u) (v | v) <;> simp [liftOption, planeRot]

/-- A rotation product on `α` lifts to a rotation product on `Option α`. -/
lemma IsRotProduct.liftOption {α : Type*} [Fintype α] [DecidableEq α] {R : Matrix α α ℝ}
    (hR : IsRotProduct R) : IsRotProduct (liftOption R) := by
  induction hR with
  | one => rw [liftOption_one]; exact IsRotProduct.one
  | mul_planeRot hS hab hcs ih =>
    rw [liftOption_mul, liftOption_planeRot]
    exact ih.mul_planeRot (fun h => hab (Option.some_injective _ h)) hcs

/-- An orthogonal matrix fixing `e_none` (as a column) is block diagonal. -/
lemma eq_liftOption_of_mulVec_single {α : Type*} [Fintype α] [DecidableEq α]
    {Q : Matrix (Option α) (Option α) ℝ} (hQ : Q * Q.transpose = 1)
    (hcol : ∀ u, Q u none = if u = none then 1 else 0) :
    Q = liftOption (Q.submatrix some some) := by
  have hQtQ : Q.transpose * Q = 1 := mul_eq_one_comm.mp hQ
  -- row `none` has unit norm and the entry 1 at `none`, so its other entries vanish
  have hrow : ∀ v, Q none v = if v = none then 1 else 0 := by
    intro v
    have h1 := congrFun (congrFun hQ none) none
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at h1
    rw [Fintype.sum_option, hcol none] at h1
    simp only [ite_true, mul_one] at h1
    have hsum : ∑ x : α, Q none (some x) * Q none (some x) = 0 := by linarith
    rcases v with _ | x
    · simp [hcol]
    · have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_self_nonneg (Q none (some x))).mp
        hsum x (Finset.mem_univ x)
      simp [mul_self_eq_zero.mp this]
  ext (u | u) (v | v)
  · simp [liftOption, hcol]
  · simp [liftOption, hrow]
  · simp [liftOption, hcol]
  · simp [liftOption]

lemma liftOption_eq_reindex {α : Type*} [DecidableEq α] (M : Matrix α α ℝ) :
    liftOption M = Matrix.reindex (Equiv.optionEquivSumPUnit.{0} α).symm
      (Equiv.optionEquivSumPUnit.{0} α).symm
      (Matrix.fromBlocks M 0 0 (1 : Matrix PUnit PUnit ℝ)) := by
  ext (u | u) (v | v) <;> simp [liftOption, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.optionEquivSumPUnit, Matrix.fromBlocks]

lemma det_liftOption {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) :
    (liftOption M).det = M.det := by
  rw [liftOption_eq_reindex, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

lemma liftOption_injective {α : Type*} : Function.Injective (liftOption (α := α)) := by
  intro M N h
  ext x y
  have := congrFun (congrFun h (some x)) (some y)
  simpa [liftOption] using this

lemma liftOption_transpose {α : Type*} (M : Matrix α α ℝ) :
    (liftOption M).transpose = liftOption M.transpose := by
  ext (u | u) (v | v) <;> simp [liftOption]

/-- Transport of `IsRotProduct` along an equivalence of label types. -/
lemma IsRotProduct.reindex {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {R : Matrix α α ℝ} (hR : IsRotProduct R) :
    IsRotProduct (Matrix.reindex e e R) := by
  induction hR with
  | one => simpa using IsRotProduct.one
  | @mul_planeRot R c s a b hS hab hcs ih =>
    have hpr : (Fermionic.planeRot c s a b).submatrix e.symm e.symm =
        Fermionic.planeRot c s (e a) (e b) := by
      ext u v
      simp only [Matrix.submatrix_apply, Fermionic.planeRot, Equiv.symm_apply_eq,
        EmbeddingLike.apply_eq_iff_eq]
    rw [Matrix.reindex_apply, ← Matrix.submatrix_mul_equiv R _ _ e.symm _, hpr,
      ← Matrix.reindex_apply]
    exact ih.mul_planeRot (fun h => hab (e.injective h)) hcs

/-- Theorem 14 on `Option α`, given the theorem on `α`. -/
lemma isRotProduct_option {α : Type*} [Fintype α] [DecidableEq α]
    (ih : ∀ O : Matrix α α ℝ, O * O.transpose = 1 → O.det = 1 → IsRotProduct O)
    (O : Matrix (Option α) (Option α) ℝ) (hO : O * O.transpose = 1) (hdet : O.det = 1) :
    IsRotProduct O := by
  obtain ⟨G, hG, hzero, -, hnn⟩ :=
    exists_zero_coord (fun u => O u none) (Finset.univ.image some) none (by simp)
  set Q : Matrix (Option α) (Option α) ℝ := G * O with hQ
  have hQO : Q * Q.transpose = 1 := by
    rw [hQ, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc O, hO, Matrix.one_mul,
      hG.mul_transpose_self]
  have hQtQ : Q.transpose * Q = 1 := mul_eq_one_comm.mp hQO
  have hQdet : Q.det = 1 := by rw [hQ, Matrix.det_mul, hG.det, hdet, one_mul]
  have hQcol : ∀ u, Q u none = (G *ᵥ fun u => O u none) u := fun u => by
    simp [hQ, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hcol0 : ∀ x : α, Q (some x) none = 0 := fun x => by
    rw [hQcol]; exact hzero (some x) (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  -- the column `none` has unit norm
  have hunit : Q none none * Q none none = 1 := by
    have h1 : (Q.transpose * Q) none none = (1 : Matrix (Option α) (Option α) ℝ) none none := by
      rw [hQtQ]
    rw [Matrix.mul_apply, Fintype.sum_option] at h1
    simp only [Matrix.transpose_apply, Matrix.one_apply_eq, hcol0, mul_zero,
      Finset.sum_const_zero, add_zero] at h1
    exact h1
  have hQnn : Q none none = 1 := by
    rcases isEmpty_or_nonempty α with hα | hα
    · rw [← hQdet, Matrix.det_unique]
      rfl
    · have hpos : 0 ≤ Q none none := by
        rw [hQcol]
        exact hnn ⟨some (Classical.choice hα), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      nlinarith
  have hcol : ∀ u, Q u none = if u = none then 1 else 0 := by
    rintro (_ | x)
    · simp [hQnn]
    · simp [hcol0]
  have hblock := eq_liftOption_of_mulVec_single hQO hcol
  set Q' : Matrix α α ℝ := Q.submatrix some some with hQ'
  have hQ'O : Q' * Q'.transpose = 1 := by
    apply liftOption_injective
    rw [liftOption_mul, ← liftOption_transpose, ← hblock, hQO, liftOption_one]
  have hQ'det : Q'.det = 1 := by rw [← det_liftOption, ← hblock, hQdet]
  have hQrot : IsRotProduct Q := by rw [hblock]; exact (ih Q' hQ'O hQ'det).liftOption
  have hOeq : O = G.transpose * Q := by
    rw [hQ, ← Matrix.mul_assoc, hG.transpose_mul_self, Matrix.one_mul]
  rw [hOeq]
  exact hG.transpose.mul hQrot

/-- Transport of the hypotheses of Theorem 14 along an equivalence. -/
lemma special_orthogonal_reindex {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) {O : Matrix α α ℝ} (hO : O * O.transpose = 1) (hdet : O.det = 1) :
    Matrix.reindex e e O * (Matrix.reindex e e O).transpose = 1 ∧
      (Matrix.reindex e e O).det = 1 := by
  refine ⟨?_, by rw [Matrix.det_reindex_self, hdet]⟩
  rw [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hO,
    Matrix.submatrix_one_equiv]

/-- Theorem 14 on `Fin m`, by induction on `m` through `Fin (m + 1) ≃ Option (Fin m)`. -/
lemma isRotProduct_fin : ∀ (m : ℕ) (O : Matrix (Fin m) (Fin m) ℝ),
    O * O.transpose = 1 → O.det = 1 → IsRotProduct O := by
  intro m
  induction m with
  | zero =>
    intro O _ _
    have : O = 1 := Matrix.ext fun i _ => i.elim0
    rw [this]; exact IsRotProduct.one
  | succ m ih =>
    intro O hO hdet
    set e := finSuccEquiv m with he
    obtain ⟨h1, h2⟩ := special_orthogonal_reindex e hO hdet
    have h := (isRotProduct_option ih _ h1 h2).reindex e.symm
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self] using h

/-- Theorem 14: every special orthogonal matrix on a finite label type is a rotation product. -/
theorem isRotProduct_of_special_orthogonal {α : Type*} [Fintype α] [DecidableEq α]
    (O : Matrix α α ℝ) (hO : O * O.transpose = 1) (hdet : O.det = 1) : IsRotProduct O := by
  set e := Fintype.equivFin α with he
  obtain ⟨h1, h2⟩ := special_orthogonal_reindex e hO hdet
  have h := (isRotProduct_fin _ _ h1 h2).reindex e.symm
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self] using h

end Givens

end Fermionic
