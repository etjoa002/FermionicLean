/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Parity
import FermionicLean.Fock.Gate

/-! # Majorana monomials

For a set `S` of labels, the monomial `c_S` is the product of the Majorana operators `c_a`,
`a ∈ S`, taken in the order `x_1 < ⋯ < x_n < y_1 < ⋯ < y_n` (G2, Definition 11); the order is
the one transported from `Fin (n + n)` by `finSumFinEquiv`. The monomials are traceless for
`S ≠ ∅` (Lemma 12(a)); they multiply, up to a sign, to the monomial of the symmetric difference,
are Hermitian up to a sign, and are orthonormal for the trace pairing `Tr (Aᴴ B)` (Lemma 12(b)).
Hence the `4^n` monomials form a basis of the `2^n × 2^n` matrices, every matrix is reconstructed
from its moments, `A = 2^{-n} ∑_S Tr (A c_Sᴴ) c_S`, and a matrix is determined by the moments
`Tr (A c_S)` (Theorem 13).

Signs are never computed: a sign is a scalar `ε` with `IsSign ε`, that is `ε = 1 ∨ ε = -1`.
-/

open Matrix

namespace Fermionic

variable {n : ℕ}

/-! ### Signs -/

/-- A sign `±1`. -/
def IsSign (ε : ℂ) : Prop := ε = 1 ∨ ε = -1

lemma IsSign.one : IsSign 1 := Or.inl rfl

lemma IsSign.neg {ε : ℂ} (h : IsSign ε) : IsSign (-ε) := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg 1)

lemma IsSign.mul {ε δ : ℂ} (hε : IsSign ε) (hδ : IsSign δ) : IsSign (ε * δ) := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num [IsSign]

lemma IsSign.mul_self {ε : ℂ} (h : IsSign ε) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

lemma IsSign.star {ε : ℂ} (h : IsSign ε) : star ε = ε := by
  rcases h with rfl | rfl <;> simp

lemma IsSign.neg_one_pow (k : ℕ) : IsSign ((-1 : ℂ) ^ k) := neg_one_pow_eq_or ℂ k

/-! ### Definition 11 -/

/-- The labels in the order `x_1 < ⋯ < x_n < y_1 < ⋯ < y_n`: the enumeration of `Fin (n + n)`
pulled back along `finSumFinEquiv` (`x_j ↦ j`, `y_j ↦ n + j`). -/
def labelList (n : ℕ) : List (MajoranaIndex n) :=
  (List.finRange (n + n)).map finSumFinEquiv.symm

lemma labelList_nodup : (labelList n).Nodup :=
  (List.nodup_finRange (n + n)).map finSumFinEquiv.symm.injective

lemma mem_labelList (a : MajoranaIndex n) : a ∈ labelList n :=
  List.mem_map.mpr ⟨finSumFinEquiv a, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

/-- The label list is increasing for the order transported from `Fin (n + n)`. -/
lemma labelList_pairwise :
    (labelList n).Pairwise fun a b => finSumFinEquiv a < finSumFinEquiv b := by
  rw [labelList, List.pairwise_map]
  exact (List.pairwise_lt_finRange (n + n)).imp fun {i j} h => by simpa using h

/-- The labels of `S` in increasing order. -/
def labels (S : Finset (MajoranaIndex n)) : List (MajoranaIndex n) :=
  (labelList n).filter fun a => decide (a ∈ S)

lemma mem_labels {S : Finset (MajoranaIndex n)} {a : MajoranaIndex n} :
    a ∈ labels S ↔ a ∈ S := by
  simp [labels, mem_labelList]

lemma labels_nodup (S : Finset (MajoranaIndex n)) : (labels S).Nodup :=
  labelList_nodup.filter _

lemma labels_pairwise (S : Finset (MajoranaIndex n)) :
    (labels S).Pairwise fun a b => finSumFinEquiv a < finSumFinEquiv b :=
  labelList_pairwise.filter _

lemma length_labels (S : Finset (MajoranaIndex n)) : (labels S).length = S.card := by
  rw [← List.toFinset_card_of_nodup (labels_nodup S)]
  congr 1
  ext a
  simp [mem_labels]

lemma labels_empty : labels (∅ : Finset (MajoranaIndex n)) = [] := by
  simp [labels]

/-- Definition 11: the monomial `c_S`, the product of the `c_a`, `a ∈ S`, in increasing order. -/
def monomial (S : Finset (MajoranaIndex n)) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  ((labels S).map majorana).prod

lemma monomial_empty : monomial (∅ : Finset (MajoranaIndex n)) = 1 := by
  simp [monomial, labels_empty]

/-- The order on labels, on the modes: `x_j < x_k ↔ j < k`. -/
lemma lt_inl_inl_iff {j k : Fin n} :
    finSumFinEquiv (Sum.inl j : MajoranaIndex n) < finSumFinEquiv (Sum.inl k) ↔ j < k := by
  simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]

/-- The order on labels: every `x_j` precedes every `y_k`. -/
lemma lt_inl_inr (j k : Fin n) :
    finSumFinEquiv (Sum.inl j : MajoranaIndex n) < finSumFinEquiv (Sum.inr k) := by
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
    Fin.val_natAdd]
  omega

/-- The order on labels, on the modes: `y_j < y_k ↔ j < k`. -/
lemma lt_inr_inr_iff {j k : Fin n} :
    finSumFinEquiv (Sum.inr j : MajoranaIndex n) < finSumFinEquiv (Sum.inr k) ↔ j < k := by
  simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd, add_lt_add_iff_left]

/-- The ordered label list of `S` is the unique increasing enumeration of `S`. -/
lemma labels_eq_of_pairwise {S : Finset (MajoranaIndex n)} {l : List (MajoranaIndex n)}
    (hl : l.Pairwise fun a b => finSumFinEquiv a < finSumFinEquiv b) (hS : l.toFinset = S) :
    labels S = l := by
  have hnd : l.Nodup := hl.imp fun h => ne_of_apply_ne _ (ne_of_lt h)
  have hperm : (labels S).Perm l :=
    List.perm_of_nodup_nodup_toFinset_eq (labels_nodup S) hnd (by ext a; simp [mem_labels, ← hS])
  exact hperm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (labels_pairwise S) hl

/-- `c_{{a}} = c_a`. -/
lemma monomial_singleton (a : MajoranaIndex n) : monomial {a} = majorana a := by
  rw [monomial, labels_eq_of_pairwise (l := [a]) (by simp) (by simp)]
  simp

/-- `c_{{a, b}} = c_a c_b` for `a < b`. -/
lemma monomial_pair {a b : MajoranaIndex n} (h : finSumFinEquiv a < finSumFinEquiv b) :
    monomial {a, b} = majorana a * majorana b := by
  rw [monomial, labels_eq_of_pairwise (l := [a, b]) (by simp [h]) (by simp)]
  simp

/-! ### The insertion rule -/

/-- Moving `c_a` through a product of `k` Majorana operators with labels different from `a`
costs the sign `(-1)^k`. -/
lemma list_prod_mul_majorana (l : List (MajoranaIndex n)) (a : MajoranaIndex n)
    (h : ∀ b ∈ l, b ≠ a) :
    (l.map majorana).prod * majorana a =
      (-1) ^ l.length • (majorana a * (l.map majorana).prod) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : b ≠ a := h b (List.mem_cons_self ..)
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem b hc)
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih', Matrix.mul_smul, ← Matrix.mul_assoc,
      majorana_mul_comm_of_ne hb.symm, Matrix.neg_mul, smul_neg, List.length_cons, pow_succ,
      mul_neg_one, neg_smul, Matrix.mul_assoc]

/-- The insertion rule on a duplicate-free list of labels: `c_a` times the ordered product over
`R` is, up to a sign, the ordered product over `insert a R`. -/
lemma majorana_mul_filter_prod (l : List (MajoranaIndex n)) (hl : l.Nodup) (a : MajoranaIndex n)
    (ha : a ∈ l) (R : Finset (MajoranaIndex n)) (haR : a ∉ R) :
    ∃ ε : ℂ, IsSign ε ∧
      majorana a * ((l.filter fun b => decide (b ∈ R)).map majorana).prod =
        ε • ((l.filter fun b => decide (b ∈ insert a R)).map majorana).prod := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hbl, hl⟩ := hl
    by_cases hba : b = a
    · subst hba
      refine ⟨1, IsSign.one, ?_⟩
      have h1 : (l.filter fun c => decide (c ∈ insert b R)) = l.filter fun c => decide (c ∈ R) :=
        List.filter_congr fun c hc => by
          have hcb : c ≠ b := fun h => hbl (h ▸ hc)
          simp [hcb]
      rw [List.filter_cons_of_neg (by simpa using haR), List.filter_cons_of_pos (by simp), h1,
        List.map_cons, List.prod_cons, one_smul]
    · have ha' : a ∈ l := by simpa [Ne.symm hba] using ha
      obtain ⟨ε, hε, h⟩ := ih hl ha'
      by_cases hbR : b ∈ R
      · refine ⟨-ε, hε.neg, ?_⟩
        have hb' : b ∈ insert a R := Finset.mem_insert_of_mem hbR
        rw [List.filter_cons_of_pos (by simpa using hbR),
          List.filter_cons_of_pos (by simpa using hb'), List.map_cons, List.prod_cons,
          List.map_cons, List.prod_cons, ← Matrix.mul_assoc, majorana_mul_comm_of_ne hba,
          Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_smul, neg_smul]
      · refine ⟨ε, hε, ?_⟩
        have hb' : b ∉ insert a R := by simp [Finset.mem_insert, hba, hbR]
        rw [List.filter_cons_of_neg (by simpa using hbR),
          List.filter_cons_of_neg (by simpa using hb')]
        exact h

/-- Insertion rule, `a ∉ R`: `c_a c_R = ± c_{R ∪ {a}}`. -/
theorem majorana_mul_monomial_of_notMem {a : MajoranaIndex n} {R : Finset (MajoranaIndex n)}
    (h : a ∉ R) : ∃ ε : ℂ, IsSign ε ∧ majorana a * monomial R = ε • monomial (insert a R) :=
  majorana_mul_filter_prod (labelList n) labelList_nodup a (mem_labelList a) R h

/-- `c_{R ∪ {a}} = ± c_a c_R` for `a ∉ R`. -/
theorem monomial_insert {a : MajoranaIndex n} {R : Finset (MajoranaIndex n)} (h : a ∉ R) :
    ∃ ε : ℂ, IsSign ε ∧ monomial (insert a R) = ε • (majorana a * monomial R) := by
  obtain ⟨ε, hε, h1⟩ := majorana_mul_monomial_of_notMem h
  exact ⟨ε, hε, by rw [h1, smul_smul, hε.mul_self, one_smul]⟩

/-- Insertion rule, `a ∈ R`: `c_a c_R = ± c_{R \ {a}}`. -/
theorem majorana_mul_monomial_of_mem {a : MajoranaIndex n} {R : Finset (MajoranaIndex n)}
    (h : a ∈ R) : ∃ ε : ℂ, IsSign ε ∧ majorana a * monomial R = ε • monomial (R.erase a) := by
  obtain ⟨ε, hε, h1⟩ := monomial_insert (Finset.notMem_erase a R)
  rw [Finset.insert_erase h] at h1
  exact ⟨ε, hε, by
    rw [h1, Matrix.mul_smul, ← Matrix.mul_assoc, majorana_mul_self, Matrix.one_mul]⟩

/-- Insertion rule: `c_a c_R = ± c_{{a} △ R}`. -/
theorem majorana_mul_monomial (a : MajoranaIndex n) (R : Finset (MajoranaIndex n)) :
    ∃ ε : ℂ, IsSign ε ∧ majorana a * monomial R = ε • monomial (symmDiff {a} R) := by
  by_cases h : a ∈ R
  · have hR : symmDiff {a} R = R.erase a := by
      ext b
      by_cases hb : b = a <;> simp [Finset.mem_symmDiff, hb, h]
    rw [hR]
    exact majorana_mul_monomial_of_mem h
  · have hR : symmDiff {a} R = insert a R := by
      ext b
      by_cases hb : b = a <;> simp [Finset.mem_symmDiff, hb, h]
    rw [hR]
    exact majorana_mul_monomial_of_notMem h

/-! ### Lemma 12(b): products, adjoints, orthonormality -/

/-- Lemma 12(b): `c_S c_T = ± c_{S △ T}`. -/
theorem monomial_mul_monomial (S T : Finset (MajoranaIndex n)) :
    ∃ ε : ℂ, IsSign ε ∧ monomial S * monomial T = ε • monomial (symmDiff S T) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, IsSign.one, ?_⟩
    have h : symmDiff (∅ : Finset (MajoranaIndex n)) T = T := by
      ext b
      simp [Finset.mem_symmDiff]
    rw [monomial_empty, Matrix.one_mul, h, one_smul]
  | insert a S haS ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := monomial_insert haS
    obtain ⟨ε₂, hε₂, h₂⟩ := ih
    obtain ⟨ε₃, hε₃, h₃⟩ := majorana_mul_monomial a (symmDiff S T)
    refine ⟨ε₁ * ε₂ * ε₃, (hε₁.mul hε₂).mul hε₃, ?_⟩
    have hS : symmDiff (insert a S) T = symmDiff {a} (symmDiff S T) := by
      rw [Finset.insert_eq, ← Finset.sup_eq_union,
        ← (Finset.disjoint_singleton_left.mpr haS).symmDiff_eq_sup, symmDiff_assoc]
    rw [hS, h₁, Matrix.smul_mul, Matrix.mul_assoc, h₂, Matrix.mul_smul, h₃, smul_smul, smul_smul,
      mul_assoc]

/-- Lemma 12(b): `c_Sᴴ c_S = 1`. -/
theorem conjTranspose_monomial_mul_monomial (S : Finset (MajoranaIndex n)) :
    (monomial S).conjTranspose * monomial S = 1 := by
  induction S using Finset.induction_on with
  | empty => rw [monomial_empty, Matrix.conjTranspose_one, Matrix.one_mul]
  | insert a S haS ih =>
    obtain ⟨ε, hε, h⟩ := monomial_insert haS
    rw [h, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, majorana_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε.star, hε.mul_self, one_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc (majorana a), majorana_mul_self, Matrix.one_mul, ih]

/-- `c_S c_S = ± 1`. -/
theorem monomial_mul_self (S : Finset (MajoranaIndex n)) :
    ∃ ε : ℂ, IsSign ε ∧ monomial S * monomial S = ε • 1 := by
  obtain ⟨ε, hε, h⟩ := monomial_mul_monomial S S
  rw [symmDiff_self, Finset.bot_eq_empty, monomial_empty] at h
  exact ⟨ε, hε, h⟩

/-- Lemma 12(b): `c_Sᴴ = ± c_S`. -/
theorem conjTranspose_monomial (S : Finset (MajoranaIndex n)) :
    ∃ ε : ℂ, IsSign ε ∧ (monomial S).conjTranspose = ε • monomial S := by
  obtain ⟨ε, hε, h⟩ := monomial_mul_self S
  refine ⟨ε, hε, ?_⟩
  have h1 : monomial S * (ε • monomial S) = 1 := by
    rw [Matrix.mul_smul, h, smul_smul, hε.mul_self, one_smul]
  calc (monomial S).conjTranspose
      = (monomial S).conjTranspose * (monomial S * (ε • monomial S)) := by
        rw [h1, Matrix.mul_one]
    _ = ε • monomial S := by
        rw [← Matrix.mul_assoc, conjTranspose_monomial_mul_monomial, Matrix.one_mul]

/-! ### Lemma 12(a): monomials are traceless -/

/-- Lemma 12(a): `Tr c_S = 0` for `S ≠ ∅`. Odd `|S|` by the parity operator, even `|S|` by
moving one factor around the trace. -/
theorem trace_monomial_eq_zero {S : Finset (MajoranaIndex n)} (hS : S ≠ ∅) :
    (monomial S).trace = 0 := by
  rcases Nat.even_or_odd S.card with heven | hodd
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨ε, hε, h⟩ := monomial_insert (Finset.notMem_erase a S)
    rw [Finset.insert_erase ha] at h
    have hodd' : Odd (S.erase a).card := by
      rw [Finset.card_erase_of_mem ha]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
      obtain ⟨k, hk⟩ := heven
      exact ⟨k - 1, by omega⟩
    have hcomm : monomial (S.erase a) * majorana a = -(majorana a * monomial (S.erase a)) := by
      have := list_prod_mul_majorana (labels (S.erase a)) a
        fun b hb => Finset.ne_of_mem_erase (mem_labels.mp hb)
      rwa [length_labels, hodd'.neg_one_pow, neg_one_smul] at this
    have key : (majorana a * monomial (S.erase a)).trace = 0 := by
      have := Matrix.trace_mul_comm (majorana a) (monomial (S.erase a))
      rw [hcomm, Matrix.trace_neg] at this
      linear_combination this / 2
    rw [h, Matrix.trace_smul, key, smul_zero]
  · have := trace_mul_list_prod_eq_zero_of_odd 1 (by rw [Matrix.one_mul, Matrix.mul_one])
      ((labels S).map majorana)
      (fun X hX => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
        exact parity_mul_majorana_mul_parity a)
      (by rw [List.length_map, length_labels]; exact hodd)
    rwa [Matrix.one_mul] at this

/-- `Tr 1 = 2^n` on Fock space. -/
lemma trace_one_fock : (1 : Matrix (FockIndex n) (FockIndex n) ℂ).trace = 2 ^ n := by
  rw [Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

/-- Lemma 12(b): `Tr (c_Sᴴ c_T) = 2^n [S = T]`. -/
theorem trace_conjTranspose_monomial_mul_monomial (S T : Finset (MajoranaIndex n)) :
    ((monomial S).conjTranspose * monomial T).trace = if S = T then (2 : ℂ) ^ n else 0 := by
  split_ifs with hST
  · subst hST
    rw [conjTranspose_monomial_mul_monomial, trace_one_fock]
  · obtain ⟨ε, hε, h⟩ := conjTranspose_monomial S
    obtain ⟨δ, hδ, h'⟩ := monomial_mul_monomial S T
    have hne : symmDiff S T ≠ ∅ := fun h0 => hST (symmDiff_eq_bot.mp h0)
    rw [h, Matrix.smul_mul, h', Matrix.trace_smul, Matrix.trace_smul, trace_monomial_eq_zero hne,
      smul_zero, smul_zero]

/-! ### Theorem 13: the monomial basis -/

/-- Theorem 13: the monomials are linearly independent. -/
theorem linearIndependent_monomial :
    LinearIndependent ℂ
      (monomial : Finset (MajoranaIndex n) → Matrix (FockIndex n) (FockIndex n) ℂ) := by
  rw [linearIndependent_iff']
  intro s g hg T hT
  have h := congrArg (fun A => ((monomial T).conjTranspose * A).trace) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    trace_conjTranspose_monomial_mul_monomial, Matrix.trace_zero, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, hT, ite_true, mul_eq_zero] at h
  exact h.resolve_right (pow_ne_zero n two_ne_zero)

/-- There are as many monomials as the dimension of the matrix space, `4^n = (2^n)^2`. -/
lemma card_finset_majoranaIndex :
    Fintype.card (Finset (MajoranaIndex n)) =
      Module.finrank ℂ (Matrix (FockIndex n) (FockIndex n) ℂ) := by
  rw [Fintype.card_finset, Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_add]

/-- Theorem 13: the monomial basis of the `2^n × 2^n` matrices. -/
noncomputable def monomialBasis :
    Module.Basis (Finset (MajoranaIndex n)) ℂ (Matrix (FockIndex n) (FockIndex n) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_monomial card_finset_majoranaIndex

@[simp] lemma monomialBasis_apply (S : Finset (MajoranaIndex n)) :
    monomialBasis S = monomial S := by
  rw [monomialBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The coordinates in the monomial basis are the moments, `2^{-n} Tr (A c_Tᴴ)`. -/
theorem monomialBasis_repr (A : Matrix (FockIndex n) (FockIndex n) ℂ)
    (T : Finset (MajoranaIndex n)) :
    monomialBasis.repr A T = ((2 : ℂ) ^ n)⁻¹ * (A * (monomial T).conjTranspose).trace := by
  have h := monomialBasis.sum_repr A
  simp only [monomialBasis_apply] at h
  conv_rhs => rw [← h]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm _ (monomial T).conjTranspose,
    trace_conjTranspose_monomial_mul_monomial, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [mul_comm (monomialBasis.repr A T), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero),
    one_mul]

/-- Theorem 13: reconstruction, `A = 2^{-n} ∑_S Tr (A c_Sᴴ) c_S`. -/
theorem eq_sum_trace_mul_conjTranspose_monomial_smul (A : Matrix (FockIndex n) (FockIndex n) ℂ) :
    A = ((2 : ℂ) ^ n)⁻¹ • ∑ S, (A * (monomial S).conjTranspose).trace • monomial S := by
  conv_lhs => rw [← monomialBasis.sum_repr A]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialBasis_apply, monomialBasis_repr, smul_smul]

/-- Theorem 13: a matrix is determined by its moments `Tr (A c_S)`. -/
theorem eq_of_trace_mul_monomial_eq {A B : Matrix (FockIndex n) (FockIndex n) ℂ}
    (h : ∀ S, (A * monomial S).trace = (B * monomial S).trace) : A = B := by
  calc A = ((2 : ℂ) ^ n)⁻¹ • ∑ S, (A * (monomial S).conjTranspose).trace • monomial S :=
        eq_sum_trace_mul_conjTranspose_monomial_smul A
    _ = ((2 : ℂ) ^ n)⁻¹ • ∑ S, (B * (monomial S).conjTranspose).trace • monomial S := by
        congr 1
        refine Finset.sum_congr rfl fun S _ => ?_
        obtain ⟨ε, hε, hS⟩ := conjTranspose_monomial S
        simp only [hS, Matrix.mul_smul, Matrix.trace_smul, h S]
    _ = B := (eq_sum_trace_mul_conjTranspose_monomial_smul B).symm

end Fermionic
