/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean.Fock.Gap
import FermionicLean.Chain.KitaevState

/-! # The gap of the Kitaev chain Hamiltonian (G5, Package A)

The Kitaev chain Hamiltonian `H_{-K_N}` has the Kitaev chain state as its unique ground state
with energy `-N/2` (Theorem 12 of G4). The gap theorem of `Fock/Gap.lean` specialises: every
density operator orthogonal to the Kitaev chain state has energy at least `-N/2 + 1`, and this
bound is attained (Proposed Corollary, Kitaev gap).
-/

open Matrix

namespace Fermionic

variable {N : ℕ} [NeZero N]

/-- Proposed Corollary (Kitaev gap), bound: a density operator `ρ` with `Tr(ρ ρ_K) = 0` has
energy at least `-N/2 + 1` for `H_{-K_N}`. -/
theorem energy_kitaevHam_ge_of_trace_mul_eq_zero
    {ρ : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ} (hρ : IsDensity ρ)
    (horth : (ρ * kitaevState N).trace = 0) :
    -((N : ℝ) / 2) + 1 ≤ energy (-(kitaevCov N)) ρ := by
  have := energy_neg_ge_of_trace_mul_eq_zero isPure_kitaevCov isGaussian_kitaevState
    covariance_kitaevState hρ horth
  simpa using this

/-- Proposed Corollary (Kitaev gap), attainment: there is a density operator `ρ'` with
`Tr(ρ' ρ_K) = 0` and energy exactly `-N/2 + 1` for `H_{-K_N}`. -/
theorem exists_trace_mul_kitaevState_eq_zero_and_energy_eq :
    ∃ ρ' : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ,
      IsDensity ρ' ∧ (ρ' * kitaevState N).trace = 0 ∧
        energy (-(kitaevCov N)) ρ' = -((N : ℝ) / 2) + 1 := by
  have hN : 0 < N * 1 := by rw [Nat.mul_one]; exact Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨ρ', hρ', horth, hE⟩ := exists_trace_mul_eq_zero_and_energy_neg_eq isPure_kitaevCov
    isGaussian_kitaevState covariance_kitaevState hN
  refine ⟨ρ', hρ', horth, ?_⟩
  rw [hE]; simp

end Fermionic
