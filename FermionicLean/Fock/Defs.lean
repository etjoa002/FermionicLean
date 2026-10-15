/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Defs
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Fock space and Jordan–Wigner Majorana operators

Fock space of `n` modes is indexed by occupation configurations `Fin n → Fin 2`.
The Pauli matrices `X_j` (bit flip), `Z_j` (sign) and the Jordan–Wigner string
`S_j` are explicit matrices; the Majorana operators are `c_{x_j} = S_j X_j` and
`c_{y_j} = i S_j X_j Z_j`. Conventions follow Bravyi–Kitaev, Ann. Phys. 298 (2002).
-/

open Matrix

namespace Fermionic

/-- Occupation configurations of `n` modes. -/
abbrev FockIndex (n : ℕ) := Fin n → Fin 2

variable {n : ℕ}

/-- Flip the occupation of mode `j`. -/
def flip (j : Fin n) (s : FockIndex n) : FockIndex n :=
  Function.update s j (s j + 1)

lemma flip_apply_self (j : Fin n) (s : FockIndex n) : flip j s j = s j + 1 := by
  simp [flip]

lemma flip_apply_ne {j k : Fin n} (h : k ≠ j) (s : FockIndex n) : flip j s k = s k := by
  simp [flip, Function.update_of_ne h]

lemma flip_flip (j : Fin n) (s : FockIndex n) : flip j (flip j s) = s := by
  funext k
  by_cases h : k = j
  · subst h
    rw [flip_apply_self, flip_apply_self]
    generalize s k = b
    fin_cases b <;> decide
  · rw [flip_apply_ne h, flip_apply_ne h]

/-- The flip as a permutation of configurations. -/
def flipPerm (j : Fin n) : Equiv.Perm (FockIndex n) :=
  ⟨flip j, flip j, flip_flip j, flip_flip j⟩

/-- The sign `(-1)^b` of an occupation bit. -/
def bitSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

/-- Pauli `X` on mode `j`: the bit-flip permutation matrix. -/
def pauliX (j : Fin n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  (flipPerm j).toPEquiv.toMatrix

/-- Pauli `Z` on mode `j`: the diagonal sign matrix. -/
def pauliZ (j : Fin n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  Matrix.diagonal fun s => bitSign (s j)

/-- Jordan–Wigner string: the product of the signs of all modes before `j`. -/
def jwString (j : Fin n) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  Matrix.diagonal fun s => ∏ k : Fin n, if k < j then bitSign (s k) else 1

/-- Jordan–Wigner Majorana operators: `inl j ↦ S_j X_j`, `inr j ↦ i S_j X_j Z_j`. -/
def majorana : MajoranaIndex n → Matrix (FockIndex n) (FockIndex n) ℂ
  | Sum.inl j => jwString j * pauliX j
  | Sum.inr j => Complex.I • (jwString j * pauliX j * pauliZ j)

end Fermionic
