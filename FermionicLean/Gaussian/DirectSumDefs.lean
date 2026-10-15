/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Gaussian.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-! Coordinate splitting and independent covariance sums for Majorana coordinates.
The definitions coincide with the bosonic constructions of GaussianLean. -/

namespace Fermionic

/-- Split grouped Majorana coordinates of `n + m` modes into the two grouped subsystems. -/
def splitModes {n m : ℕ} : MajoranaIndex (n + m) → MajoranaIndex n ⊕ MajoranaIndex m
  | Sum.inl i => match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (Sum.inl j)
    | Sum.inr j => Sum.inr (Sum.inl j)
  | Sum.inr i => match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (Sum.inr j)
    | Sum.inr j => Sum.inr (Sum.inr j)

/-- Independent covariance blocks, reordered to grouped x/y Majorana coordinates. -/
def directSumCov {n m : ℕ}
    (A : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (B : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ) :
    Matrix (MajoranaIndex (n + m)) (MajoranaIndex (n + m)) ℝ :=
  (Matrix.fromBlocks A 0 0 B).submatrix splitModes splitModes

end Fermionic
