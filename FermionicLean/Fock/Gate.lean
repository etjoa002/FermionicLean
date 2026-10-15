/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Occupation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Hopping gates and Gaussian unitaries

The hopping gate between modes `j ≠ k` is the closed formula
`U = (cos φ + sin φ c_{x_j} c_{x_k}) (cos φ + sin φ c_{y_j} c_{y_k})`; it is unitary and
conjugates the Majorana operators by a rotation of angle `2φ` in the planes `(x_j, x_k)` and
`(y_j, y_k)`. Every unitary that maps Majorana operators to real linear combinations of
Majorana operators acts on covariances by orthogonal congruence, `Γ(UρU*) = Oᵀ Γ(ρ) O`.
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

variable {n : ℕ}

/-! ### Products of two Majorana operators -/

lemma majorana_mul_self (a : MajoranaIndex n) : majorana a * majorana a = 1 := by
  have h := majorana_anticommute a a
  simp only [ite_true, ← two_smul ℂ (majorana a * majorana a)] at h
  exact smul_right_injective _ two_ne_zero h

lemma majorana_mul_comm_of_ne {a b : MajoranaIndex n} (h : a ≠ b) :
    majorana b * majorana a = -(majorana a * majorana b) := by
  have hac := majorana_anticommute a b
  simp only [h, ite_false, zero_smul] at hac
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hac

/-- The generator `c_a c_b` of a rotation in the plane `(a, b)`. -/
def pairGen (a b : MajoranaIndex n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  majorana a * majorana b

section PairGen

variable {a b : MajoranaIndex n} (h : a ≠ b)
include h

lemma pairGen_mul_self : pairGen a b * pairGen a b = -1 := by
  unfold pairGen
  calc majorana a * majorana b * (majorana a * majorana b)
      = majorana a * (majorana b * majorana a) * majorana b := by
        simp only [Matrix.mul_assoc]
    _ = -1 := by
        rw [majorana_mul_comm_of_ne h, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc,
          majorana_mul_self, Matrix.one_mul, majorana_mul_self]

lemma pairGen_conjTranspose : (pairGen a b).conjTranspose = -pairGen a b := by
  unfold pairGen
  rw [Matrix.conjTranspose_mul, majorana_conjTranspose, majorana_conjTranspose,
    majorana_mul_comm_of_ne h]

/-- `g c_a = -c_b`. -/
lemma pairGen_mul_left : pairGen a b * majorana a = -majorana b := by
  unfold pairGen
  rw [Matrix.mul_assoc, majorana_mul_comm_of_ne h, Matrix.mul_neg, ← Matrix.mul_assoc,
    majorana_mul_self, Matrix.one_mul]

omit h in
/-- `c_a g = c_b`. -/
lemma majorana_mul_pairGen_left : majorana a * pairGen a b = majorana b := by
  unfold pairGen
  rw [← Matrix.mul_assoc, majorana_mul_self, Matrix.one_mul]

omit h in
/-- `g c_b = c_a`. -/
lemma pairGen_mul_right : pairGen a b * majorana b = majorana a := by
  unfold pairGen
  rw [Matrix.mul_assoc, majorana_mul_self, Matrix.mul_one]

/-- `c_b g = -c_a`. -/
lemma majorana_mul_pairGen_right : majorana b * pairGen a b = -majorana a := by
  unfold pairGen
  rw [← Matrix.mul_assoc, majorana_mul_comm_of_ne h, Matrix.neg_mul, Matrix.mul_assoc,
    majorana_mul_self, Matrix.mul_one]

omit h in
lemma majorana_mul_pairGen_of_ne {d : MajoranaIndex n} (hda : d ≠ a) (hdb : d ≠ b) :
    majorana d * pairGen a b = pairGen a b * majorana d := by
  unfold pairGen
  rw [← Matrix.mul_assoc, majorana_mul_comm_of_ne hda.symm, Matrix.neg_mul, Matrix.mul_assoc,
    majorana_mul_comm_of_ne hdb.symm, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

/-! ### One rotation factor -/

/-- `V = cos φ + sin φ c_a c_b`. -/
noncomputable def rotFactor (φ : ℝ) (a b : MajoranaIndex n) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  (Real.cos φ : ℂ) • 1 + (Real.sin φ : ℂ) • pairGen a b

lemma rotFactor_conjTranspose (φ : ℝ) :
    (rotFactor φ a b).conjTranspose = (Real.cos φ : ℂ) • 1 - (Real.sin φ : ℂ) • pairGen a b := by
  simp only [rotFactor, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, pairGen_conjTranspose h, Complex.star_def, Complex.conj_ofReal,
    smul_neg, sub_eq_add_neg]

lemma rotFactor_mul_conjTranspose (φ : ℝ) :
    rotFactor φ a b * (rotFactor φ a b).conjTranspose = 1 := by
  rw [rotFactor_conjTranspose h, rotFactor]
  have hg := pairGen_mul_self h
  have hcs : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq φ
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hg, smul_neg]
  calc _ = ((Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) := by
        module
    _ = 1 := by rw [hcs, one_smul]

lemma conjTranspose_mul_rotFactor (φ : ℝ) :
    (rotFactor φ a b).conjTranspose * rotFactor φ a b = 1 :=
  mul_eq_one_comm.mp (rotFactor_mul_conjTranspose h φ)

/-- The rotation of `c_a`: `V c_a V* = cos 2φ c_a - sin 2φ c_b`. -/
lemma rotFactor_conj_left (φ : ℝ) :
    rotFactor φ a b * majorana a * (rotFactor φ a b).conjTranspose =
      (Real.cos (2 * φ) : ℂ) • majorana a - (Real.sin (2 * φ) : ℂ) • majorana b := by
  have h2c : ((Real.cos (2 * φ) : ℝ) : ℂ) = (Real.cos φ : ℂ) ^ 2 - (Real.sin φ : ℂ) ^ 2 := by
    have hcs : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq φ
    rw [Real.cos_two_mul]; push_cast at hcs ⊢; linear_combination hcs
  have h2s : ((Real.sin (2 * φ) : ℝ) : ℂ) = 2 * (Real.sin φ : ℂ) * (Real.cos φ : ℂ) := by
    rw [Real.sin_two_mul]; push_cast; ring
  rw [h2c, h2s, rotFactor_conjTranspose h, rotFactor]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, pairGen_mul_left h, majorana_mul_pairGen_left,
    majorana_mul_pairGen_right h, Matrix.neg_mul, smul_neg]
  module

/-- The rotation of `c_b`: `V c_b V* = sin 2φ c_a + cos 2φ c_b`. -/
lemma rotFactor_conj_right (φ : ℝ) :
    rotFactor φ a b * majorana b * (rotFactor φ a b).conjTranspose =
      (Real.sin (2 * φ) : ℂ) • majorana a + (Real.cos (2 * φ) : ℂ) • majorana b := by
  have h2c : ((Real.cos (2 * φ) : ℝ) : ℂ) = (Real.cos φ : ℂ) ^ 2 - (Real.sin φ : ℂ) ^ 2 := by
    have hcs : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq φ
    rw [Real.cos_two_mul]; push_cast at hcs ⊢; linear_combination hcs
  have h2s : ((Real.sin (2 * φ) : ℝ) : ℂ) = 2 * (Real.sin φ : ℂ) * (Real.cos φ : ℂ) := by
    rw [Real.sin_two_mul]; push_cast; ring
  rw [h2c, h2s, rotFactor_conjTranspose h, rotFactor]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, pairGen_mul_right, majorana_mul_pairGen_left,
    majorana_mul_pairGen_right h, smul_neg]
  module

/-- Labels outside the plane are fixed. -/
lemma rotFactor_conj_of_ne {d : MajoranaIndex n} (hda : d ≠ a) (hdb : d ≠ b) (φ : ℝ) :
    rotFactor φ a b * majorana d * (rotFactor φ a b).conjTranspose = majorana d := by
  have hcomm : rotFactor φ a b * majorana d = majorana d * rotFactor φ a b := by
    simp only [rotFactor, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, majorana_mul_pairGen_of_ne hda hdb]
  rw [hcomm, Matrix.mul_assoc, rotFactor_mul_conjTranspose h, Matrix.mul_one]

end PairGen

/-! ### The hopping gate -/

section Gate

/-- Definition 7: the hopping gate
`U_{jk}(φ) = (cos φ + sin φ c_{x_j} c_{x_k}) (cos φ + sin φ c_{y_j} c_{y_k})`. -/
noncomputable def hoppingGate (φ : ℝ) (j k : Fin n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  rotFactor φ (Sum.inl j) (Sum.inl k) * rotFactor φ (Sum.inr j) (Sum.inr k)

/-- A row with two entries `c` at `p` and `d` at `q`. -/
def rowTwo {α : Type*} [DecidableEq α] (p q : α) (c d : ℝ) : α → ℝ :=
  fun v => if v = p then c else if v = q then d else 0

/-- The rotation by `θ` in the plane `(j, k)` of `n` modes, the identity elsewhere. -/
noncomputable def planeRotation (θ : ℝ) (j k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun u =>
    if u = j then rowTwo j k (Real.cos θ) (-Real.sin θ)
    else if u = k then rowTwo j k (Real.sin θ) (Real.cos θ)
    else fun v => if v = u then 1 else 0

/-- Definition 7: the rotation `O_{jk}(φ)`, by angle `2φ` in the planes `(x_j, x_k)` and
`(y_j, y_k)`, the identity elsewhere. -/
noncomputable def hoppingRotation (φ : ℝ) (j k : Fin n) :
    Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ :=
  Matrix.fromBlocks (planeRotation (2 * φ) j k) 0 0 (planeRotation (2 * φ) j k)

variable {φ : ℝ} {j k : Fin n}

lemma sum_rowTwo_smul {α : Type*} [Fintype α] [DecidableEq α] {p q : α} (hpq : p ≠ q) (c d : ℝ)
    (g : α → Matrix (FockIndex n) (FockIndex n) ℂ) :
    ∑ v, ((rowTwo p q c d v : ℝ) : ℂ) • g v = (c : ℂ) • g p + (d : ℂ) • g q := by
  have : ∀ v, ((rowTwo p q c d v : ℝ) : ℂ) • g v =
      (if v = p then (c : ℂ) • g p else 0) + (if v = q then (d : ℂ) • g q else 0) := by
    intro v
    unfold rowTwo
    by_cases hvp : v = p
    · subst hvp; simp [hpq]
    · by_cases hvq : v = q
      · subst hvq; simp [hvp]
      · simp [hvp, hvq]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma sum_rowOne_smul {α : Type*} [Fintype α] [DecidableEq α] (u : α)
    (g : α → Matrix (FockIndex n) (FockIndex n) ℂ) :
    ∑ v, (((if v = u then (1 : ℝ) else 0) : ℝ) : ℂ) • g v = g u := by
  simp [ite_smul]

/-- The sum `∑_b O_{ab} c_b` for the block rotation, sector by sector. -/
lemma sum_hoppingRotation_smul (a : MajoranaIndex n) :
    ∑ b, ((hoppingRotation φ j k a b : ℝ) : ℂ) • majorana b =
      match a with
      | Sum.inl u => ∑ v, ((planeRotation (2 * φ) j k u v : ℝ) : ℂ) • majorana (Sum.inl v)
      | Sum.inr u => ∑ v, ((planeRotation (2 * φ) j k u v : ℝ) : ℂ) • majorana (Sum.inr v) := by
  rcases a with u | u <;> simp [hoppingRotation, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- Theorem 8: the hopping gate is unitary. -/
theorem hoppingGate_mul_conjTranspose (hjk : j ≠ k) :
    hoppingGate φ j k * (hoppingGate φ j k).conjTranspose = 1 := by
  have hx : (Sum.inl j : MajoranaIndex n) ≠ Sum.inl k := fun h => hjk (Sum.inl_injective h)
  have hy : (Sum.inr j : MajoranaIndex n) ≠ Sum.inr k := fun h => hjk (Sum.inr_injective h)
  unfold hoppingGate
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rotFactor φ (Sum.inr j) _),
    rotFactor_mul_conjTranspose hy, Matrix.one_mul, rotFactor_mul_conjTranspose hx]

theorem conjTranspose_mul_hoppingGate (hjk : j ≠ k) :
    (hoppingGate φ j k).conjTranspose * hoppingGate φ j k = 1 :=
  mul_eq_one_comm.mp (hoppingGate_mul_conjTranspose hjk)

/-- One plane: `V c_{a(u)} V* = ∑_v R_{uv} c_{a(v)}` for the labels `a(u)` of one sector. -/
lemma rotFactor_conj_sector (hjk : j ≠ k) (ι : Fin n → MajoranaIndex n)
    (hι : Function.Injective ι) (u : Fin n) :
    rotFactor φ (ι j) (ι k) * majorana (ι u) * (rotFactor φ (ι j) (ι k)).conjTranspose =
      ∑ v, ((planeRotation (2 * φ) j k u v : ℝ) : ℂ) • majorana (ι v) := by
  have hx : ι j ≠ ι k := fun h => hjk (hι h)
  by_cases huj : u = j
  · subst huj
    rw [rotFactor_conj_left hx]
    simp only [planeRotation, ite_true]
    rw [sum_rowTwo_smul hjk]
    push_cast
    module
  · by_cases huk : u = k
    · subst huk
      rw [rotFactor_conj_right hx]
      simp only [planeRotation, Ne.symm hjk, ite_false, ite_true]
      rw [sum_rowTwo_smul hjk]
    · have h1 : ι u ≠ ι j := fun h => huj (hι h)
      have h2 : ι u ≠ ι k := fun h => huk (hι h)
      rw [rotFactor_conj_of_ne hx h1 h2]
      simp only [planeRotation, huj, huk, ite_false]
      rw [sum_rowOne_smul]

/-- Theorem 8: the hopping gate conjugates the Majorana operators by `O_{jk}(φ)`. -/
theorem hoppingGate_conj (hjk : j ≠ k) (a : MajoranaIndex n) :
    hoppingGate φ j k * majorana a * (hoppingGate φ j k).conjTranspose =
      ∑ b, ((hoppingRotation φ j k a b : ℝ) : ℂ) • majorana b := by
  have hx : (Sum.inl j : MajoranaIndex n) ≠ Sum.inl k := fun h => hjk (Sum.inl_injective h)
  have hy : (Sum.inr j : MajoranaIndex n) ≠ Sum.inr k := fun h => hjk (Sum.inr_injective h)
  rw [sum_hoppingRotation_smul]
  unfold hoppingGate
  rw [Matrix.conjTranspose_mul]
  have hassoc : ∀ (V W X Wt Vt : Matrix (FockIndex n) (FockIndex n) ℂ),
      V * W * X * (Wt * Vt) = V * (W * X * Wt) * Vt := by
    intros; simp only [Matrix.mul_assoc]
  rw [hassoc]
  rcases a with u | u
  · rw [rotFactor_conj_of_ne hy Sum.inl_ne_inr Sum.inl_ne_inr]
    exact rotFactor_conj_sector hjk Sum.inl Sum.inl_injective u
  · rw [rotFactor_conj_sector hjk Sum.inr Sum.inr_injective u, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    rw [Matrix.mul_smul, Matrix.smul_mul, rotFactor_conj_of_ne hx Sum.inr_ne_inl Sum.inr_ne_inl]

end Gate

/-! ### Gaussian unitaries act by orthogonal congruence -/

section Congruence

variable {U : Matrix (FockIndex n) (FockIndex n) ℂ}
  {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}

/-- The conjugation hypothesis: `U c_a U* = ∑_b O_{ab} c_b`. -/
def ConjugatesMajorana (U : Matrix (FockIndex n) (FockIndex n) ℂ)
    (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : Prop :=
  ∀ a, U * majorana a * U.conjTranspose = ∑ b, ((O a b : ℝ) : ℂ) • majorana b

lemma conj_mul_conj (hU' : U.conjTranspose * U = 1) (X Y : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (U * X * U.conjTranspose) * (U * Y * U.conjTranspose) = U * (X * Y) * U.conjTranspose := by
  calc (U * X * U.conjTranspose) * (U * Y * U.conjTranspose)
      = U * X * (U.conjTranspose * U) * Y * U.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU', Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma trace_majorana_mul (x y : MajoranaIndex n) :
    (majorana x * majorana y).trace = if x = y then (Fintype.card (FockIndex n) : ℂ) else 0 := by
  have h := congrArg Matrix.trace (majorana_anticommute x y)
  rw [Matrix.trace_add, Matrix.trace_mul_comm (majorana y), ← two_mul, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul] at h
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  split_ifs at h ⊢ with hxy
  · exact mul_left_cancel₀ h2 (h.trans (by ring))
  · exact mul_left_cancel₀ h2 (h.trans (by ring))

/-- The trace of a product of two real combinations of Majorana operators. -/
lemma trace_sum_smul_mul (f g : MajoranaIndex n → ℝ) :
    ((∑ x, ((f x : ℝ) : ℂ) • majorana x) * (∑ y, ((g y : ℝ) : ℂ) • majorana y)).trace =
      (Fintype.card (FockIndex n) : ℂ) * ((∑ x, f x * g x : ℝ) : ℂ) := by
  rw [Finset.sum_mul_sum, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, trace_majorana_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Theorem 9: `O` is orthogonal. -/
theorem orthogonal_of_conjugatesMajorana (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) : O * O.transpose = 1 := by
  unfold ConjugatesMajorana at hO
  have hcard : (Fintype.card (FockIndex n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext a b
  have h1 : ((U * majorana a * U.conjTranspose) * (U * majorana b * U.conjTranspose)).trace =
      if a = b then (Fintype.card (FockIndex n) : ℂ) else 0 := by
    rw [conj_mul_conj hU', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU', Matrix.one_mul,
      trace_majorana_mul]
  have h2 : ((U * majorana a * U.conjTranspose) * (U * majorana b * U.conjTranspose)).trace =
      (Fintype.card (FockIndex n) : ℂ) * ((O * O.transpose) a b : ℝ) := by
    rw [hO a, hO b, trace_sum_smul_mul]
    congr 2
  have h3 : ((O * O.transpose) a b : ℂ) = if a = b then 1 else 0 := by
    have := h2.symm.trans h1
    split_ifs with hab
    · subst hab
      simp only [ite_true] at this
      exact mul_left_cancel₀ hcard (this.trans (mul_one _).symm)
    · simp only [hab, ite_false] at this
      exact (mul_eq_zero.mp this).resolve_left hcard
  rw [Matrix.one_apply]
  apply Complex.ofReal_injective
  rw [h3]
  split_ifs <;> simp

/-- A commutator of two linear combinations. -/
lemma commutator_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℂ) (g : κ → ℂ)
    (X : ι → Matrix (FockIndex n) (FockIndex n) ℂ) (Y : κ → Matrix (FockIndex n) (FockIndex n) ℂ) :
    (∑ i, f i • X i) * (∑ j, g j • Y j) - (∑ j, g j • Y j) * (∑ i, f i • X i) =
      ∑ i, ∑ j, (f i * g j) • (X i * Y j - Y j * X i) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (f := fun (j : κ) (i : ι) => (g j • Y j) * (f i • X i)),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, mul_comm (g j) (f i)]

/-- The inverse conjugation: `U* c_a U = ∑_b O_{ba} c_b`. -/
lemma conjTranspose_mul_majorana_mul (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) (a : MajoranaIndex n) :
    U.conjTranspose * majorana a * U = ∑ b, ((O b a : ℝ) : ℂ) • majorana b := by
  have hOO : O.transpose * O = 1 :=
    mul_eq_one_comm.mp (orthogonal_of_conjugatesMajorana hU' hO)
  unfold ConjugatesMajorana at hO
  have hb : ∀ b, majorana b = ∑ b', ((O b b' : ℝ) : ℂ) • (U.conjTranspose * majorana b' * U) := by
    intro b
    have hOb := hO b
    have : U.conjTranspose * (U * majorana b * U.conjTranspose) * U =
        U.conjTranspose * (∑ b', ((O b b' : ℝ) : ℂ) • majorana b') * U := by rw [hOb]
    rw [Matrix.mul_sum, Matrix.sum_mul] at this
    have hleft : U.conjTranspose * (U * majorana b * U.conjTranspose) * U = majorana b := by
      calc U.conjTranspose * (U * majorana b * U.conjTranspose) * U
          = (U.conjTranspose * U) * majorana b * (U.conjTranspose * U) := by
            simp only [Matrix.mul_assoc]
        _ = majorana b := by rw [hU', Matrix.one_mul, Matrix.mul_one]
    rw [hleft] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro b' _
    rw [Matrix.mul_smul, Matrix.smul_mul]
  calc U.conjTranspose * majorana a * U
      = ∑ b', (((O.transpose * O) a b' : ℝ) : ℂ) • (U.conjTranspose * majorana b' * U) := by
        rw [hOO, Finset.sum_eq_single a]
        · simp
        · intro b' _ hb'
          rw [Matrix.one_apply_ne (Ne.symm hb')]
          simp
        · simp
    _ = ∑ b, ((O b a : ℝ) : ℂ) • majorana b := by
        conv_rhs => rw [show (∑ b, ((O b a : ℝ) : ℂ) • majorana b) =
          ∑ b, ((O b a : ℝ) : ℂ) • ∑ b', ((O b b' : ℝ) : ℂ) •
            (U.conjTranspose * majorana b' * U) from by
              apply Finset.sum_congr rfl; intro b _; rw [← hb b]]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b' _
        rw [← Finset.sum_smul, Matrix.mul_apply]
        push_cast
        simp only [Matrix.transpose_apply]

/-- Theorem 9: a unitary that conjugates the Majorana operators by `O` maps density operators
to density operators and covariances by `Γ ↦ Oᵀ Γ O`. -/
theorem covariance_conj (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (hO : ConjugatesMajorana U O) {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsDensity ρ) :
    IsDensity (U * ρ * U.conjTranspose) ∧
    covariance (U * ρ * U.conjTranspose) = O.transpose * covariance ρ * O := by
  have hdens : IsDensity (U * ρ * U.conjTranspose) := by
    refine ⟨?_, ?_⟩
    · have := hρ.1.conjTranspose_mul_mul_same U.conjTranspose
      rwa [Matrix.conjTranspose_conjTranspose] at this
    · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU', Matrix.one_mul, hρ.2]
  refine ⟨hdens, ?_⟩
  have hherm : ρ.IsHermitian := hρ.1.1
  have hherm' : (U * ρ * U.conjTranspose).IsHermitian := hdens.1.1
  ext a b
  apply Complex.ofReal_injective
  rw [coe_covariance hherm' a b]
  -- move the unitary onto the commutator
  have hcyc : ((U * ρ * U.conjTranspose) * commutator a b).trace =
      (ρ * (U.conjTranspose * commutator a b * U)).trace := by
    calc ((U * ρ * U.conjTranspose) * commutator a b).trace
        = (U * (ρ * U.conjTranspose * commutator a b)).trace := by simp only [Matrix.mul_assoc]
      _ = ((ρ * U.conjTranspose * commutator a b) * U).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hcyc]
  -- the conjugated commutator is bilinear in the rotated operators
  have hmid : ∀ X Y : Matrix (FockIndex n) (FockIndex n) ℂ,
      (U.conjTranspose * X * U) * (U.conjTranspose * Y * U) = U.conjTranspose * (X * Y) * U := by
    intro X Y
    calc (U.conjTranspose * X * U) * (U.conjTranspose * Y * U)
        = U.conjTranspose * X * (U * U.conjTranspose) * Y * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hcomm : U.conjTranspose * commutator a b * U =
      ∑ a', ∑ b', (((O a' a : ℝ) : ℂ) * ((O b' b : ℝ) : ℂ)) • commutator a' b' := by
    have h1 : U.conjTranspose * commutator a b * U =
        (U.conjTranspose * majorana a * U) * (U.conjTranspose * majorana b * U) -
          (U.conjTranspose * majorana b * U) * (U.conjTranspose * majorana a * U) := by
      rw [hmid, hmid]
      unfold commutator
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [h1, conjTranspose_mul_majorana_mul hU' hO, conjTranspose_mul_majorana_mul hU' hO,
      commutator_sum_smul]
    rfl
  rw [hcomm, Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  -- compare with the real matrix product
  have hentry : ((O.transpose * covariance ρ * O) a b : ℝ) =
      ∑ b', ∑ a', O a' a * covariance ρ a' b' * O b' b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  calc _ = ∑ a', ∑ b', ((O a' a : ℝ) : ℂ) * ((covariance ρ a' b' : ℝ) : ℂ) * ((O b' b : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro a' _
        apply Finset.sum_congr rfl
        intro b' _
        rw [coe_covariance hherm a' b']
        ring
    _ = _ := by
        rw [hentry]
        push_cast
        exact Finset.sum_comm

end Congruence

/-! ### One gate on an occupation state -/

section Example

/-- The occupation pattern `|10⟩` of two modes. -/
def occ10 : FockIndex 2 := fun i => if i = 0 then 1 else 0

/-- The covariance of `U_{12}(φ)|10⟩`: `X = [[cos 4φ, -sin 4φ], [-sin 4φ, -cos 4φ]]`. -/
noncomputable def gateExample (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (4 * φ), -Real.sin (4 * φ); -Real.sin (4 * φ), -Real.cos (4 * φ)]

theorem conjugatesMajorana_hoppingGate {φ : ℝ} {j k : Fin n} (hjk : j ≠ k) :
    ConjugatesMajorana (hoppingGate φ j k) (hoppingRotation φ j k) :=
  hoppingGate_conj hjk

/-- Corollary 10: one hopping gate on `|10⟩`. -/
theorem covariance_gate_occ10 (φ : ℝ) :
    covariance (hoppingGate φ (0 : Fin 2) 1 * occupation occ10 *
        (hoppingGate φ (0 : Fin 2) 1).conjTranspose) =
      Matrix.fromBlocks 0 (gateExample φ) (-(gateExample φ).transpose) 0 := by
  have hjk : (0 : Fin 2) ≠ 1 := by decide
  rw [(covariance_conj (hoppingGate_mul_conjTranspose hjk) (conjTranspose_mul_hoppingGate hjk)
    (conjugatesMajorana_hoppingGate hjk) (isDensity_occupation occ10)).2, covariance_occupation]
  have h4c : Real.cos (4 * φ) = Real.cos (2 * φ) ^ 2 - Real.sin (2 * φ) ^ 2 := by
    rw [show 4 * φ = 2 * (2 * φ) by ring, Real.cos_two_mul, Real.cos_sq']; ring
  have h4s : Real.sin (4 * φ) = 2 * Real.sin (2 * φ) * Real.cos (2 * φ) := by
    rw [show 4 * φ = 2 * (2 * φ) by ring, Real.sin_two_mul]
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [hoppingRotation, planeRotation, rowTwo, occupationSign, occupationSignEntry, occ10,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, gateExample,
      h4c, h4s] <;> ring

/-- Corollary 10: the vacuum is fixed by every hopping gate. -/
theorem covariance_gate_vacuum {φ : ℝ} {j k : Fin n} (hjk : j ≠ k) :
    covariance (hoppingGate φ j k * occupation (fun _ : Fin n => (0 : Fin 2)) *
        (hoppingGate φ j k).conjTranspose) = -(standardCovariance n) := by
  rw [(covariance_conj (hoppingGate_mul_conjTranspose hjk) (conjTranspose_mul_hoppingGate hjk)
    (conjugatesMajorana_hoppingGate hjk) (isDensity_occupation _)).2, covariance_vacuum]
  have hOO : (hoppingRotation φ j k).transpose * hoppingRotation φ j k = 1 :=
    mul_eq_one_comm.mp (orthogonal_of_conjugatesMajorana
      (conjTranspose_mul_hoppingGate hjk) (conjugatesMajorana_hoppingGate hjk))
  have hR : (planeRotation (2 * φ) j k).transpose * planeRotation (2 * φ) j k = 1 := by
    have := hOO
    unfold hoppingRotation at this
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at this
    simpa using (Matrix.fromBlocks_inj.mp this).1
  unfold hoppingRotation standardCovariance
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [hR]

end Example

end Fermionic
