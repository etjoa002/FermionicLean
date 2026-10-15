/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Majorana covariance conventions

Finite-mode fermionic Gaussian states are described by real antisymmetric
covariance matrices in a Majorana basis. The conventions follow Bravyi,
Quantum Inf. Comput. 5, 216 (2005), Section 2. These matrix definitions do not
construct a fermionic state.
-/

namespace Fermionic

/-- Majorana coordinates of `n` modes: `inl j` is the x-type and `inr j` the y-type
Majorana operator of mode `j`. -/
abbrev MajoranaIndex (n : ℕ) := Fin n ⊕ Fin n

/-- Real antisymmetric covariance satisfying `Γᵀ Γ ≤ 1`. -/
def IsAdmissible {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : Prop :=
  Γ.transpose = -Γ ∧ (1 - Γ.transpose * Γ).PosSemidef

/-- Covariance of a pure fermionic Gaussian state: antisymmetric with `Γ² = -1`. -/
def IsPure {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) : Prop :=
  Γ.transpose = -Γ ∧ Γ * Γ = -1

end Fermionic
