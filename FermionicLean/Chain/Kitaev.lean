/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Chain.Fourier
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # The Kitaev chain as a chain with one virtual mode

At its solvable point the Kitaev chain pairs the Majorana operator `y_i` of each site with
`x_{i+1}` of the next. The same covariance is the periodic chain of one physical and one
virtual mode per site whose on-site covariance `kitaevLocal` pairs `x_C` with `x_A` and
`y_C` with `x_B`, leaving `y_A, y_B` uncorrelated. The proof goes through momentum space:
the twisted on-site covariance has no virtual–virtual block, so every momentum block is
`B_k β C_k`, and the reconstruction formula of F4 returns the pairing.
-/

open Matrix
open scoped ComplexOrder

namespace Fermionic

/-! ### The on-site covariance -/

/-- Labels of a site with `M = P = 1`, in the order `x_A, x_B, x_C, y_A, y_B, y_C`. -/
abbrev KLabel := SiteLabel 1 1

/-- Definition 3: the Kitaev on-site covariance, `(x_C, x_A) = 1`, `(y_C, x_B) = 1`. -/
def kitaevLocal : Matrix KLabel KLabel ℝ :=
  Matrix.of fun u v =>
    match u, v with
    | Sum.inl (Sum.inr _), Sum.inl (Sum.inl (Sum.inl _)) => 1
    | Sum.inl (Sum.inl (Sum.inl _)), Sum.inl (Sum.inr _) => -1
    | Sum.inr (Sum.inr _), Sum.inl (Sum.inl (Sum.inr _)) => 1
    | Sum.inl (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr _) => -1
    | _, _ => 0

/-- The projector onto the labels `y_A, y_B`. -/
def virtualYProjector : KLabel → ℝ
  | Sum.inr (Sum.inl _) => 1
  | _ => 0

lemma kitaevLocal_transpose : kitaevLocal.transpose = -kitaevLocal := by
  ext (((a | a) | c) | ((a | a) | c)) (((b | b) | d) | ((b | b) | d)) <;>
    simp [kitaevLocal]

lemma one_sub_kitaevLocal_mul :
    1 - kitaevLocal.transpose * kitaevLocal = Matrix.diagonal virtualYProjector := by
  rw [kitaevLocal_transpose]
  ext (((a | a) | c) | ((a | a) | c)) (((b | b) | d) | ((b | b) | d)) <;>
    simp [kitaevLocal, virtualYProjector, Matrix.mul_apply, Fintype.sum_sum_type, Fin.eq_zero]

/-- Lemma 4: the Kitaev on-site covariance is admissible. -/
theorem admissible_kitaevLocal : Admissible kitaevLocal := by
  refine ⟨kitaevLocal_transpose, ?_⟩
  rw [one_sub_kitaevLocal_mul]
  apply Matrix.PosSemidef.diagonal
  intro u
  rcases u with ((a | a) | c) | ((a | a) | c) <;> simp [virtualYProjector]

/-- Lemma 4: the Kitaev on-site covariance is not pure. -/
theorem not_pure_kitaevLocal : ¬ Pure kitaevLocal := by
  rintro ⟨-, h⟩
  have := congrFun (congrFun h (Sum.inr (Sum.inl (Sum.inl 0)))) (Sum.inr (Sum.inl (Sum.inl 0)))
  simp [kitaevLocal, Matrix.mul_apply] at this

/-! ### The chain covariance -/

/-- The Kitaev chain covariance `K_N`: `(y_i, x_{i+1}) = 1`, `(x_{i+1}, y_i) = -1`. -/
def kitaevChain (N : ℕ) : Matrix (Retained N 1) (Retained N 1) ℝ :=
  Matrix.of fun r r' =>
    match r, r' with
    | Sum.inr (i, _), Sum.inl (j, _) => if j = finRotate N i then 1 else 0
    | Sum.inl (j, _), Sum.inr (i, _) => if j = finRotate N i then -1 else 0
    | _, _ => 0

/-- The momentum-space covariance of the Kitaev chain, `Σ(k)_{x y} = -ω_k`,
`Σ(k)_{y x} = conj ω_k`. -/
noncomputable def kitaevSymbol {N : ℕ} (k : Fin N) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.of fun a b =>
    match a, b with
    | Sum.inl _, Sum.inr _ => -sitePhase k
    | Sum.inr _, Sum.inl _ => star (sitePhase k)
    | _, _ => 0

variable {N : ℕ}

/-- The Kitaev on-site covariance in the split coordinates
`(x_C, y_C) ⊕ (x_L, x_L', y_L, y_L')`. -/
def kitaevSplit : Matrix (SiteSplit 1 1) (SiteSplit 1 1) ℂ :=
  Matrix.of fun w w' =>
    match w, w' with
    | Sum.inl (Sum.inl _), Sum.inr (Sum.inl (Sum.inl _)) => 1
    | Sum.inr (Sum.inl (Sum.inl _)), Sum.inl (Sum.inl _) => -1
    | Sum.inl (Sum.inr _), Sum.inr (Sum.inl (Sum.inr _)) => 1
    | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl (Sum.inr _) => -1
    | _, _ => 0

lemma localSplit_kitaev : localSplit kitaevLocal = kitaevSplit := by
  ext ((c | c) | ((a | a) | (a | a))) ((d | d) | ((b | b) | (b | b))) <;>
    simp [localSplit, kitaevLocal, kitaevSplit, siteSplit]

/-- The twisted on-site covariance has no virtual–virtual block. -/
lemma twistedSplit_kitaev_toBlocks_22 (k : Fin N) :
    (twistedSplit kitaevLocal k).toBlocks₂₂ = 0 := by
  ext ((a | a) | (a | a)) ((b | b) | (b | b)) <;>
    simp [Matrix.toBlocks₂₂, twistedSplit_apply, localSplit_kitaev, kitaevSplit]

lemma twistedSplit_kitaev_toBlocks_11 (k : Fin N) :
    (twistedSplit kitaevLocal k).toBlocks₁₁ = 0 := by
  ext (a | a) (b | b) <;>
    simp [Matrix.toBlocks₁₁, twistedSplit_apply, localSplit_kitaev, kitaevSplit]

/-- Theorem 5: the momentum-space covariance of the Kitaev chain. -/
theorem momentumCovariance_kitaev [NeZero N] (k : Fin N) :
    momentumCovariance kitaevLocal k = kitaevSymbol k := by
  unfold momentumCovariance contractC
  rw [twistedSplit_kitaev_toBlocks_22, twistedSplit_kitaev_toBlocks_11, Matrix.zero_mul,
    sub_zero, inv_one, Matrix.mul_one, zero_add]
  ext (a | a) (b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      twistedSplit_apply, localSplit_kitaev, kitaevSplit, bondC, bond, pairing,
      Matrix.fromBlocks, shiftPhase, splitShift, elimShift, physShift, kitaevSymbol,
      Fin.eq_zero]

/-- Theorem 5: the chain is invertible for every `N`, with `det (1 - D β_N) = 1`. -/
theorem det_one_sub_kitaev [NeZero N] :
    (1 - (periodicInput (fun _ : Fin N => kitaevLocal)).toBlocks₂₂ * periodicBond N 1).det =
      1 := by
  have h := det_one_sub_periodic_eq_prod (N := N) kitaevLocal
  simp only [twistedSplit_kitaev_toBlocks_22, Matrix.zero_mul, sub_zero, Matrix.det_one,
    Finset.prod_const_one] at h
  exact_mod_cast h

theorem kitaev_contractInvertible [NeZero N] :
    ContractInvertible (periodicInput (fun _ : Fin N => kitaevLocal)) (periodicBond N 1) := by
  unfold ContractInvertible
  rw [det_one_sub_kitaev]
  exact isUnit_one

/-- Theorem 5: the chain with the Kitaev on-site covariance at every site is `K_N`. -/
theorem periodicCovariance_kitaev [NeZero N] :
    periodicCovariance (fun _ : Fin N => kitaevLocal) = kitaevChain N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  ext r r'
  obtain ⟨i, a, rfl⟩ : ∃ i a, r = retained i a := by
    rcases r with ⟨i, c⟩ | ⟨i, c⟩
    · exact ⟨i, Sum.inl c, rfl⟩
    · exact ⟨i, Sum.inr c, rfl⟩
  obtain ⟨j, b, rfl⟩ : ∃ j b, r' = retained j b := by
    rcases r' with ⟨j, d⟩ | ⟨j, d⟩
    · exact ⟨j, Sum.inl d, rfl⟩
    · exact ⟨j, Sum.inr d, rfl⟩
  apply Complex.ofReal_injective
  have h := homogeneousCovariance_reconstruct kitaevLocal kitaev_contractInvertible i j a b
  simp only [homogeneousCovariance] at h
  rw [h]
  simp only [momentumCovariance_kitaev]
  rcases a with a | a <;> rcases b with b | b
  · simp [kitaevSymbol, kitaevChain, retained]
  · -- (x_i, y_j) = -[i = j + 1]
    have : ∀ k : Fin N, star (character k i) * kitaevSymbol k (Sum.inl a) (Sum.inr b) *
        character k j = -(star (character k i) * character k (finRotate N j)) := by
      intro k
      simp only [kitaevSymbol, Matrix.of_apply, character_finRotate]
      ring
    simp only [this, Finset.sum_neg_distrib, sum_star_character_mul]
    simp [kitaevChain, retained, hN]
    split_ifs <;> simp
  · -- (y_i, x_j) = [j = i + 1]
    have : ∀ k : Fin N, star (character k i) * kitaevSymbol k (Sum.inr a) (Sum.inl b) *
        character k j = star (character k (finRotate N i)) * character k j := by
      intro k
      simp only [kitaevSymbol, Matrix.of_apply, character_finRotate, star_mul']
    simp only [this, sum_star_character_mul]
    simp [kitaevChain, retained, hN, eq_comm]
    split_ifs <;> simp
  · simp [kitaevSymbol, kitaevChain, retained]

lemma kitaevChain_transpose : (kitaevChain N).transpose = -(kitaevChain N) := by
  ext (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩) <;> simp [kitaevChain] <;> split_ifs <;> simp

/-- Theorem 5: `K_N` is pure. -/
theorem pure_kitaevChain : Pure (kitaevChain N) := by
  refine ⟨kitaevChain_transpose, ?_⟩
  ext (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩)
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one,
      kitaevChain, Matrix.of_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.neg_apply,
      Matrix.one_apply, Sum.inl.injEq, Prod.mk.injEq, Fin.eq_zero, and_true]
    rw [Finset.sum_eq_single ((finRotate N).symm i)]
    · rw [Equiv.apply_symm_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    · intro m _ hm
      have : i ≠ finRotate N m := fun h => hm (by rw [h, Equiv.symm_apply_apply])
      simp only [this, ite_false, zero_mul]
    · simp
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, kitaevChain]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, kitaevChain]
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one,
      kitaevChain, Matrix.of_apply, mul_zero, Finset.sum_const_zero, add_zero, Matrix.neg_apply,
      Matrix.one_apply, Sum.inr.injEq, Prod.mk.injEq, Fin.eq_zero, and_true]
    rw [Finset.sum_eq_single (finRotate N i)]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro m _ hm
      simp only [hm, ite_false, zero_mul]
    · simp

/-- Theorem 5: `K_N` is translation invariant. -/
theorem kitaevChain_translation (i j : Fin N) (a b : Fin 1 ⊕ Fin 1) :
    kitaevChain N (retained (finRotate N i) a) (retained (finRotate N j) b) =
      kitaevChain N (retained i a) (retained j b) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [kitaevChain, retained]

/-! ### A pure on-site choice closes a virtual loop -/

section Loop

/-- The pure completion of the Kitaev on-site covariance: additionally `(y_A, y_B) = -1`. -/
def kitaevPure : Matrix KLabel KLabel ℝ :=
  Matrix.of fun u v =>
    match u, v with
    | Sum.inl (Sum.inr _), Sum.inl (Sum.inl (Sum.inl _)) => 1
    | Sum.inl (Sum.inl (Sum.inl _)), Sum.inl (Sum.inr _) => -1
    | Sum.inr (Sum.inr _), Sum.inl (Sum.inl (Sum.inr _)) => 1
    | Sum.inl (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr _) => -1
    | Sum.inr (Sum.inl (Sum.inl _)), Sum.inr (Sum.inl (Sum.inr _)) => -1
    | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inl (Sum.inl _)) => 1
    | _, _ => 0

/-- Proposition 6: the completion is pure. -/
theorem pure_kitaevPure : Pure kitaevPure := by
  refine ⟨?_, ?_⟩ <;>
    ext (((a | a) | c) | ((a | a) | c)) (((b | b) | d) | ((b | b) | d)) <;>
    simp [kitaevPure, Matrix.mul_apply, Fintype.sum_sum_type, Fin.eq_zero]

/-- The completion in the split coordinates. -/
def kitaevPureSplit : Matrix (SiteSplit 1 1) (SiteSplit 1 1) ℂ :=
  Matrix.of fun w w' =>
    match w, w' with
    | Sum.inl (Sum.inl _), Sum.inr (Sum.inl (Sum.inl _)) => 1
    | Sum.inr (Sum.inl (Sum.inl _)), Sum.inl (Sum.inl _) => -1
    | Sum.inl (Sum.inr _), Sum.inr (Sum.inl (Sum.inr _)) => 1
    | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl (Sum.inr _) => -1
    | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr (Sum.inr _)) => -1
    | Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inr (Sum.inl _)) => 1
    | _, _ => 0

lemma localSplit_kitaevPure : localSplit kitaevPure = kitaevPureSplit := by
  ext ((c | c) | ((a | a) | (a | a))) ((d | d) | ((b | b) | (b | b))) <;>
    simp [localSplit, kitaevPure, kitaevPureSplit, siteSplit]

/-- The loop factors of the eliminated block at momentum `k`: `1, 1, 1 + conj ω_k, 1 + ω_k`
on `(x_L, x_L', y_L, y_L')`. -/
noncomputable def loopFactor (k : Fin N) : PairIndex (Fin 1) → ℂ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1 + star (sitePhase k)
  | Sum.inr (Sum.inr _) => 1 + sitePhase k

lemma one_sub_kitaevPure_block (k : Fin N) :
    1 - (twistedSplit kitaevPure k).toBlocks₂₂ * bondC 1 = Matrix.diagonal (loopFactor k) := by
  ext ((a | a) | (a | a)) ((b | b) | (b | b)) <;>
    simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, twistedSplit_apply,
      localSplit_kitaevPure, kitaevPureSplit, bondC, bond, pairing, Matrix.fromBlocks, shiftPhase,
      splitShift, elimShift, loopFactor, Fin.eq_zero]

lemma det_one_sub_kitaevPure_block (k : Fin N) :
    (1 - (twistedSplit kitaevPure k).toBlocks₂₂ * bondC 1).det =
      (1 + star (sitePhase k)) * (1 + sitePhase k) := by
  rw [one_sub_kitaevPure_block, Matrix.det_diagonal]
  simp [Fintype.prod_sum_type, loopFactor]

/-! #### The product of `1 + ω_k` over the momenta -/

variable [NeZero N]

lemma sitePhase_pow (k : Fin N) : sitePhase k ^ N = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [sitePhase, ← Complex.exp_nat_mul]
  have : (N : ℂ) * (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ)) =
      ((-(k.val : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma sitePhase_injective : Function.Injective (sitePhase (N := N)) := by
  intro k l h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold sitePhase at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  -- divide by `2πi/N`: `-k = -l + n N`
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : ((k.val : ℤ) : ℂ) = ((l.val : ℤ) : ℂ) - (n : ℂ) * (N : ℂ) := by
    have := hn
    field_simp at this
    push_cast
    linear_combination -this
  have keyZ : (k.val : ℤ) = (l.val : ℤ) - n * (N : ℤ) := by exact_mod_cast key
  have hk := k.isLt
  have hl := l.isLt
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h0 | h0 | h0
    · have h1 : (N : ℤ) ≤ (-n) * N := by nlinarith
      have h2 : (k.val : ℤ) = l.val + (-n) * N := by rw [keyZ]; ring
      omega
    · exact h0
    · have h1 : (N : ℤ) ≤ n * N := by nlinarith
      have h2 : (l.val : ℤ) = k.val + n * N := by rw [keyZ]; ring
      omega
  subst hn0
  simp only [Int.cast_zero, zero_mul, sub_zero] at keyZ
  exact Fin.ext (by exact_mod_cast keyZ)

lemma image_sitePhase_eq_nthRootsFinset :
    Finset.univ.image (sitePhase (N := N)) = Polynomial.nthRootsFinset N (1 : ℂ) := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact (Polynomial.mem_nthRootsFinset hpos _).mpr (sitePhase_pow k)
  · rw [IsPrimitiveRoot.card_nthRootsFinset (Complex.isPrimitiveRoot_exp N (NeZero.ne N)),
      Finset.card_image_of_injective _ sitePhase_injective]
    simp

/-- `∏_k (1 + ω_k) = 1 - (-1)^N`: the factorization of `z^N - 1` over the roots of unity
at `z = -1`. -/
theorem prod_one_add_sitePhase :
    ∏ k : Fin N, (1 + sitePhase k) = 1 - (-1 : ℂ) ^ N := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := congrArg (Polynomial.eval (-1 : ℂ))
    (Polynomial.X_pow_sub_one_eq_prod hpos (Complex.isPrimitiveRoot_exp N (NeZero.ne N)))
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, ← image_sitePhase_eq_nthRootsFinset,
    Finset.prod_image (fun k _ l _ hkl => sitePhase_injective hkl)] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  have h' : (-1 : ℂ) ^ N - 1 = (-1) ^ N * ∏ k : Fin N, (1 + sitePhase k) := by
    rw [h]
    have hx : ∀ x : Fin N, (-1 - sitePhase x) = (-1) * (1 + sitePhase x) := fun x => by ring
    simp_rw [hx]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsq : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by
    rw [← mul_pow]; simp
  calc ∏ k : Fin N, (1 + sitePhase k)
      = (-1) ^ N * ((-1) ^ N * ∏ k : Fin N, (1 + sitePhase k)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1) ^ N * ((-1 : ℂ) ^ N - 1) := by rw [h']
    _ = 1 - (-1) ^ N := by rw [mul_sub, hsq]; ring

/-- Proposition 6: the determinant of the pure completion's chain,
`det(1 - D β_N) = (1 - (-1)^N)^2`. -/
theorem det_one_sub_kitaevPure :
    (1 - (periodicInput (fun _ : Fin N => kitaevPure)).toBlocks₂₂ * periodicBond N 1).det =
      (1 - (-1 : ℝ) ^ N) ^ 2 := by
  have h := det_one_sub_periodic_eq_prod (N := N) kitaevPure
  simp only [det_one_sub_kitaevPure_block] at h
  rw [Finset.prod_mul_distrib] at h
  have hstar : ∏ k : Fin N, (1 + star (sitePhase k)) = star (∏ k : Fin N, (1 + sitePhase k)) := by
    rw [star_prod]
    simp
  rw [hstar, prod_one_add_sitePhase] at h
  have hreal : star (1 - (-1 : ℂ) ^ N) = 1 - (-1) ^ N := by simp
  rw [hreal] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem det_one_sub_kitaevPure_eq :
    (1 - (periodicInput (fun _ : Fin N => kitaevPure)).toBlocks₂₂ * periodicBond N 1).det =
      2 * (1 - (-1 : ℝ) ^ N) := by
  rw [det_one_sub_kitaevPure]
  rcases neg_one_pow_eq_or ℝ N with h | h <;> rw [h] <;> norm_num

/-- Proposition 6: for odd `N` the pure completion's chain is defined and equals `K_N`. -/
theorem periodicCovariance_kitaevPure_of_odd (hN : Odd N) :
    ContractInvertible (periodicInput (fun _ : Fin N => kitaevPure)) (periodicBond N 1) ∧
    periodicCovariance (fun _ : Fin N => kitaevPure) = kitaevChain N := by
  have hdet : (1 - (periodicInput (fun _ : Fin N => kitaevPure)).toBlocks₂₂ *
      periodicBond N 1).det = 4 := by
    rw [det_one_sub_kitaevPure, hN.neg_one_pow]; norm_num
  have hinv : ContractInvertible (periodicInput (fun _ : Fin N => kitaevPure))
      (periodicBond N 1) := by
    unfold ContractInvertible; rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  refine ⟨hinv, ?_⟩
  -- momentum blocks: the `y`-loop is invertible and does not touch the physical labels
  have hsym : ∀ k : Fin N, momentumCovariance kitaevPure k = kitaevSymbol k := by
    intro k
    have hk := momentum_isUnit_det_of_contractInvertible kitaevPure hinv k
    have hk' : (1 + star (sitePhase k)) * (1 + sitePhase k) ≠ 0 := by
      rw [← det_one_sub_kitaevPure_block]; exact isUnit_iff_ne_zero.mp hk
    have hne1 : 1 + star (sitePhase k) ≠ 0 := left_ne_zero_of_mul hk'
    have hne2 : 1 + sitePhase k ≠ 0 := right_ne_zero_of_mul hk'
    have hinvd : (1 - (twistedSplit kitaevPure k).toBlocks₂₂ * bondC 1)⁻¹ =
        Matrix.diagonal (fun e => (loopFactor k e)⁻¹) := by
      rw [one_sub_kitaevPure_block]
      apply Matrix.inv_eq_right_inv
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      have hne1' : 1 + (starRingEnd ℂ) (sitePhase k) ≠ 0 := hne1
      ext ((a | a) | (a | a)) <;> simp [loopFactor, hne1', hne2]
    unfold momentumCovariance contractC
    rw [hinvd]
    have h11 : (twistedSplit kitaevPure k).toBlocks₁₁ = 0 := by
      ext (a | a) (b | b) <;>
        simp [Matrix.toBlocks₁₁, twistedSplit_apply, localSplit_kitaevPure, kitaevPureSplit]
    rw [h11, zero_add]
    ext (a | a) (b | b) <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        twistedSplit_apply, localSplit_kitaevPure, kitaevPureSplit, bondC, bond, pairing,
        Matrix.fromBlocks, shiftPhase, splitShift, elimShift, physShift, kitaevSymbol,
        Matrix.diagonal_apply, loopFactor, Fin.eq_zero]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  ext r r'
  obtain ⟨i, a, rfl⟩ : ∃ i a, r = retained i a := by
    rcases r with ⟨i, c⟩ | ⟨i, c⟩
    · exact ⟨i, Sum.inl c, rfl⟩
    · exact ⟨i, Sum.inr c, rfl⟩
  obtain ⟨j, b, rfl⟩ : ∃ j b, r' = retained j b := by
    rcases r' with ⟨j, d⟩ | ⟨j, d⟩
    · exact ⟨j, Sum.inl d, rfl⟩
    · exact ⟨j, Sum.inr d, rfl⟩
  apply Complex.ofReal_injective
  have h := homogeneousCovariance_reconstruct kitaevPure hinv i j a b
  simp only [homogeneousCovariance] at h
  rw [h]
  simp only [hsym]
  rcases a with a | a <;> rcases b with b | b
  · simp [kitaevSymbol, kitaevChain, retained]
  · have : ∀ k : Fin N, star (character k i) * kitaevSymbol k (Sum.inl a) (Sum.inr b) *
        character k j = -(star (character k i) * character k (finRotate N j)) := by
      intro k
      simp only [kitaevSymbol, Matrix.of_apply, character_finRotate]
      ring
    simp only [this, Finset.sum_neg_distrib, sum_star_character_mul]
    simp [kitaevChain, retained, hNc]
    split_ifs <;> simp
  · have : ∀ k : Fin N, star (character k i) * kitaevSymbol k (Sum.inr a) (Sum.inl b) *
        character k j = star (character k (finRotate N i)) * character k j := by
      intro k
      simp only [kitaevSymbol, Matrix.of_apply, character_finRotate, star_mul']
    simp only [this, sum_star_character_mul]
    simp [kitaevChain, retained, hNc, eq_comm]
    split_ifs <;> simp
  · simp [kitaevSymbol, kitaevChain, retained]

end Loop

end Fermionic
