/-
Copyright (c) 2026 FermionicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FermionicLean contributors
-/
import FermionicLean

/-!
# The core statements of FermionicLean

This file states, without proofs, the main theorems of FermionicLean on fermionic Gaussian states
and Gaussian fermionic matrix product states. Part I concerns Majorana covariance matrices:
admissible and pure covariances, the contraction of covariances and the bond, periodic chains and
their three-site example, homogeneous chains in momentum space, the normal form, examples (product
chains and the Kitaev chain) and the entanglement rank of a chain. Part II concerns states on the
Fock space of n modes: the Majorana operators and the covariance of a state, quadratic
Hamiltonians and their ground states, the realization of a covariance by a state, thermal states
and evolution, Wick's theorem and the Gaussian class, the partial trace and the contraction of
Gaussian states, purity, the Kitaev ground state and the gap of its parent Hamiltonian. The
statements use definitions of FermionicLean; each is fixed in Mathlib's terms by an entry of this
file.

Every statement here is closed by `sorry`. The file `Solution.lean` in this folder repeats each
statement with the identical text and proves it. The tool `lake comparator`, configured by
`comparator.json` in this folder, checks that each theorem named there has exactly the same
statement in both files and that its proof in `Solution.lean` uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. The script `check_same_statements.py` checks the
same correspondence on the text of the two files.
-/

open Fermionic Matrix

namespace Sealed

/-! ## Covariance matrices

A system of $n$ fermionic modes $j = 0, \dots, n - 1$ has $2n$ Majorana labels: $x_j$ and $y_j$
label the two Majorana operators of mode $j$. The label set is the disjoint union of two copies
of $\{0, \dots, n - 1\}$, the first copy carrying the $x$ labels, so a matrix on the labels is
written in $2 \times 2$ block form with the $x$ labels first. A covariance matrix is a real
matrix $\Gamma$ on the labels. The covariance of a state $\rho$ with Majorana operators $c_a$ is
$\Gamma_{ab} = \operatorname{Re} \tfrac{i}{2} \operatorname{tr}(\rho [c_a, c_b])$ (second part);
with this sign the vacuum has covariance $-\Omega_n$, where
$\Omega_n = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$, so $\Gamma_{x_j y_j} = -1$ in the
vacuum. A real matrix $\Gamma$ on a finite index set is admissible when $\Gamma^T = -\Gamma$ and
$1 - \Gamma^T \Gamma$ is positive semidefinite, and pure when $\Gamma^T = -\Gamma$ and
$\Gamma^2 = -1$. A complex matrix $X$ is positive semidefinite when it is Hermitian and
$\bar v^T X v \ge 0$ for every complex vector $v$; for real matrices the vectors are real. A
real matrix $O$ is orthogonal when $O O^T = 1$. -/

/-- The definitions. The Majorana labels of $n$ modes are two copies of $\{0, \dots, n - 1\}$,
the $x$ labels first. A real matrix $\Gamma$ on them is admissible exactly when
$\Gamma^T = -\Gamma$ and $1 - \Gamma^T \Gamma$ is positive semidefinite, and pure exactly when
$\Gamma^T = -\Gamma$ and $\Gamma \Gamma = -1$. The same conditions define admissibility and
purity of a real matrix $\Gamma'$ on an arbitrary finite index set $\iota$. -/
theorem admissible_def {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ' : Matrix ι ι ℝ) :
    MajoranaIndex n = (Fin n ⊕ Fin n) ∧
    (IsAdmissible Γ ↔ Γᵀ = -Γ ∧ (1 - Γᵀ * Γ).PosSemidef) ∧
    (IsPure Γ ↔ Γᵀ = -Γ ∧ Γ * Γ = -1) ∧
    (Admissible Γ' ↔ Γ'ᵀ = -Γ' ∧ (1 - Γ'ᵀ * Γ').PosSemidef) ∧
    (Pure Γ' ↔ Γ'ᵀ = -Γ' ∧ Γ' * Γ' = -1) :=
  ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

open scoped ComplexOrder in
/-- Equivalent forms of admissibility. For a real antisymmetric matrix $\Gamma$ on the Majorana
labels of $n$ modes, the following are equivalent: $\Gamma$ is admissible;
$\|\Gamma v\|^2 \le \|v\|^2$ for every real vector $v$; the complex matrix $1 + i\Gamma$ is
positive semidefinite. -/
theorem admissible_forms {n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : Γᵀ = -Γ) :
    (IsAdmissible Γ ↔ ∀ v : MajoranaIndex n → ℝ, (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) ≤ v ⬝ᵥ v) ∧
    (IsAdmissible Γ ↔ (1 + Complex.I • Γ.map Complex.ofReal).PosSemidef) :=
  ⟨Fermionic.isAdmissible_iff_norm hΓ, Fermionic.isAdmissible_iff_hermitian hΓ⟩

/-- A pure covariance matrix $\Gamma$ on the Majorana labels of $n$ modes is orthogonal,
$\Gamma^T \Gamma = 1$, and admissible. -/
theorem pure_orthogonal {n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsPure Γ) : Γᵀ * Γ = 1 ∧ IsAdmissible Γ :=
  ⟨hΓ.transpose_mul_self, hΓ.isAdmissible⟩

/-- Orthogonal changes of Majorana basis. Let $O$ be a real orthogonal matrix on the Majorana
labels of $n$ modes ($O O^T = 1$). If $\Gamma$ is admissible, so is $O \Gamma O^T$; if $\Gamma$
is pure, so is $O \Gamma O^T$. -/
theorem orthogonal_congruence {n : ℕ} {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hO : O * Oᵀ = 1) :
    (IsAdmissible Γ → IsAdmissible (O * Γ * Oᵀ)) ∧ (IsPure Γ → IsPure (O * Γ * Oᵀ)) :=
  ⟨Fermionic.isAdmissible_orthogonalCongruence hO, Fermionic.isPure_orthogonalCongruence hO⟩

/-- Relabelling and block-diagonal sums. Let $e : \iota \to \kappa$ be a bijection of finite
index sets and $\Gamma$ a real matrix on $\kappa$; the relabelled matrix
$(\Gamma_{e(a) e(b)})_{a, b \in \iota}$ is admissible exactly when $\Gamma$ is, and pure exactly
when $\Gamma$ is. Let $\Delta_s$, $s \in \sigma$, be real matrices on a finite set $\iota$, with
$\sigma$ finite, and $\bigoplus_s \Delta_s$ the block-diagonal matrix on $\iota \times \sigma$
with entry $\delta_{st} (\Delta_s)_{ab}$ at $((a, s), (b, t))$; it is admissible exactly when
every $\Delta_s$ is, and pure exactly when every $\Delta_s$ is. -/
theorem relabel_block_diagonal {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype σ] [DecidableEq σ] (e : ι ≃ κ) (Γ : Matrix κ κ ℝ)
    (Δ : σ → Matrix ι ι ℝ) :
    (Admissible (Γ.submatrix e e) ↔ Admissible Γ) ∧ (Pure (Γ.submatrix e e) ↔ Pure Γ) ∧
    (Admissible (blockDiagonal Δ) ↔ ∀ s, Admissible (Δ s)) ∧
    (Pure (blockDiagonal Δ) ↔ ∀ s, Pure (Δ s)) :=
  ⟨Fermionic.admissible_submatrix_equiv_iff e Γ, Fermionic.pure_submatrix_equiv_iff e Γ,
    Fermionic.admissible_blockDiagonal_iff Δ, Fermionic.pure_blockDiagonal_iff Δ⟩

/-- Restriction to a subset of modes. Let $\Gamma$ be an admissible covariance matrix of $n$
modes and $e : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ injective. The restriction of
$\Gamma$ to the labels $x_{e(j)}, y_{e(j)}$, $j = 0, \dots, m - 1$, in this order, is an
admissible covariance matrix of $m$ modes. -/
theorem mode_restriction {m n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {e : Fin m → Fin n} (hΓ : IsAdmissible Γ) (he : Function.Injective e) :
    IsAdmissible (Γ.submatrix (Sum.map e e) (Sum.map e e)) :=
  Fermionic.isAdmissible_subsystem hΓ he

/-- Independent sums. Let $A$ be a real matrix on the Majorana labels of $n$ modes and $B$ one
on those of $m$ modes. Their independent sum $A \oplus B$ is a real matrix on the labels of
$n + m$ modes, the modes of $A$ first: the map $\sigma$ with $\sigma(x_j^A) = x_j$,
$\sigma(y_j^A) = y_j$, $\sigma(x_j^B) = x_{n+j}$, $\sigma(y_j^B) = y_{n+j}$ is a bijection from
the labels of $A$ followed by those of $B$ onto the labels of $n + m$ modes, and
$(A \oplus B)_{\sigma(u) \sigma(v)}$ is the $(u, v)$ entry of
$\begin{pmatrix} A & 0 \\ 0 & B \end{pmatrix}$. The sum is admissible exactly when $A$ and $B$
are, and pure exactly when $A$ and $B$ are. -/
theorem direct_sum {n m : ℕ} (A : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (B : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ)
    (σ : MajoranaIndex n ⊕ MajoranaIndex m → MajoranaIndex (n + m))
    (hσ : σ = Sum.elim
      (Sum.elim (fun j => Sum.inl (Fin.castAdd m j)) (fun j => Sum.inr (Fin.castAdd m j)))
      (Sum.elim (fun j => Sum.inl (Fin.natAdd n j)) (fun j => Sum.inr (Fin.natAdd n j)))) :
    Function.Bijective σ ∧
    (∀ u v, directSumCov A B (σ u) (σ v) = fromBlocks A 0 0 B u v) ∧
    (IsAdmissible (directSumCov A B) ↔ IsAdmissible A ∧ IsAdmissible B) ∧
    (IsPure (directSumCov A B) ↔ IsPure A ∧ IsPure B) := by
  have h1 : ∀ u, splitModes (σ u) = u := by
    subst hσ
    rintro ((j | j) | (j | j)) <;> simp [splitModes]
  have h2 : σ = ⇑(modeSplitEquiv n m).symm := funext fun u => by
    rw [Equiv.eq_symm_apply, Fermionic.modeSplitEquiv_coe, h1]
  refine ⟨h2 ▸ (modeSplitEquiv n m).symm.bijective, fun u v => ?_,
    Fermionic.isAdmissible_directSum_iff A B, Fermionic.isPure_directSum_iff A B⟩
  simp only [directSumCov, submatrix_apply, h1]

/-- One mode. Every real antisymmetric matrix $\Gamma$ on the two labels of one mode is
$\mu \omega$ for some real $\mu$, where $\omega = \begin{pmatrix} 0 & 1 \\ -1 & 0
\end{pmatrix}$; and for real $\lambda$, $\lambda \omega$ is admissible exactly when
$|\lambda| \le 1$ and pure exactly when $|\lambda| = 1$. -/
theorem one_mode (lam : ℝ) :
    (∀ Γ : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ, Γᵀ = -Γ →
      ∃ μ : ℝ, Γ = μ • (fromBlocks 0 1 (-1) 0 : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ)) ∧
    (IsAdmissible (lam • (fromBlocks 0 1 (-1) 0 : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ))
      ↔ |lam| ≤ 1) ∧
    (IsPure (lam • (fromBlocks 0 1 (-1) 0 : Matrix (MajoranaIndex 1) (MajoranaIndex 1) ℝ))
      ↔ |lam| = 1) :=
  ⟨fun _ hΓ => Fermionic.oneMode_eq_smul hΓ, Fermionic.isAdmissible_oneMode_iff lam,
    Fermionic.isPure_oneMode_iff lam⟩

/-- The standard pure covariances. On the Majorana labels of $n$ modes,
$\Omega_n = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ and $-\Omega_n$ (the vacuum
covariance in the sign convention above) are pure. -/
theorem standard_pure (n : ℕ) :
    IsPure (fromBlocks 0 1 (-1) 0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) ∧
    IsPure (-(fromBlocks 0 1 (-1) 0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)) := by
  have h := Fermionic.isPure_standardCovariance n
  refine ⟨h, ?_, ?_⟩
  · rw [transpose_neg, neg_inj]; exact h.1
  · rw [neg_mul_neg]; exact h.2

/-! ## Contraction and the bond

Let $\iota$ (retained labels) and $\kappa$ (eliminated labels) be finite index sets, $\Gamma$ a
real matrix on $\iota \sqcup \kappa$ with blocks $A = \Gamma_{\iota\iota}$,
$B = \Gamma_{\iota\kappa}$, $C = \Gamma_{\kappa\iota}$, $D = \Gamma_{\kappa\kappa}$, and $\beta$ a
real matrix on $\kappa$. The contraction of $\Gamma$ with $\beta$ is the matrix
$\Gamma \star \beta = A + B \beta (1 - D \beta)^{-1} C$ on $\iota$. It is meant under the
contraction condition $\det(1 - D \beta) \ne 0$; the inverse is the matrix inverse, which is $0$
for a singular matrix. For a finite set $L$ of modes, the bond is a covariance matrix of two
matched copies $L, L'$ of $L$, on the labels ordered $x_L, x_{L'}, y_L, y_{L'}$; it correlates
$x_a$ with $x_{a'}$ and $y_a$ with $y_{a'}$ for every $a \in L$. -/

/-- The definition of the contraction: $\Gamma \star \beta = A + B \beta (1 - D \beta)^{-1} C$
in the blocks of $\Gamma$, and the contraction condition is $\det(1 - D \beta) \ne 0$. -/
theorem contract_def {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (β : Matrix κ κ ℝ) :
    contract Γ β = Γ.toBlocks₁₁ + Γ.toBlocks₁₂ * β * (1 - Γ.toBlocks₂₂ * β)⁻¹ * Γ.toBlocks₂₁ ∧
    (ContractInvertible Γ β ↔ (1 - Γ.toBlocks₂₂ * β).det ≠ 0) :=
  ⟨rfl, isUnit_iff_ne_zero⟩

/-- Contraction preserves antisymmetry and admissibility. Under the contraction condition: if
$\Gamma$ and $\beta$ are antisymmetric, so is $\Gamma \star \beta$; if $\Gamma$ and $\beta$ are
admissible, so is $\Gamma \star \beta$. -/
theorem contraction_admissible {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {β : Matrix κ κ ℝ}
    (hinv : ContractInvertible Γ β) :
    (Γᵀ = -Γ → βᵀ = -β → (contract Γ β)ᵀ = -contract Γ β) ∧
    (Admissible Γ → Admissible β → Admissible (contract Γ β)) :=
  ⟨fun hΓ hβ => Fermionic.contract_transpose hΓ hβ hinv,
    fun hΓ hβ => Fermionic.contract_admissible hΓ hβ hinv⟩

/-- Contraction with a pure $\beta$. If $\beta$ is pure, the contraction condition holds exactly
when $\det(D + \beta) \ne 0$, and for antisymmetric $\Gamma$ satisfying it,
$\Gamma \star \beta = A + B (D + \beta)^{-1} B^T$. -/
theorem contraction_pure_bond {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) {β : Matrix κ κ ℝ} (hβ : Pure β) :
    (ContractInvertible Γ β ↔ (Γ.toBlocks₂₂ + β).det ≠ 0) ∧
    (Γᵀ = -Γ → ContractInvertible Γ β →
      contract Γ β = Γ.toBlocks₁₁ + Γ.toBlocks₁₂ * (Γ.toBlocks₂₂ + β)⁻¹ * Γ.toBlocks₁₂ᵀ) :=
  ⟨(Fermionic.contractInvertible_iff_of_pure Γ hβ).trans isUnit_iff_ne_zero,
    fun hΓ hinv => Fermionic.contract_eq_schur_of_pure hΓ hβ hinv⟩

/-- Contraction of pure covariances is pure. Let $\Gamma$ be a pure matrix on the Majorana labels
of $n$ retained modes followed by those of $m$ eliminated modes, and $\beta$ a pure covariance
matrix of the $m$ eliminated modes, with the contraction condition. Then $\Gamma \star \beta$ is
a pure covariance matrix of the $n$ retained modes. -/
theorem contraction_pure {n m : ℕ}
    {Γ : Matrix (MajoranaIndex n ⊕ MajoranaIndex m) (MajoranaIndex n ⊕ MajoranaIndex m) ℝ}
    {β : Matrix (MajoranaIndex m) (MajoranaIndex m) ℝ} (hΓ : Pure Γ) (hβ : IsPure β)
    (hinv : ContractInvertible Γ β) : IsPure (contract Γ β) := by
  set Γ' := Γ.submatrix (labelSplit n m) (labelSplit n m) with hΓ'
  have h1 : IsPure Γ' := (Fermionic.pure_submatrix_equiv_iff (labelSplit n m) Γ).2 hΓ
  have h2 : contractCov Γ' β = contract Γ β := by
    rw [Fermionic.contractCov_eq_contract, hΓ', submatrix_submatrix]
    simp
  have h3 : blockE Γ' = Γ.toBlocks₂₂ := by
    ext a b
    simp [blockE, embedE, hΓ', toBlocks₂₂]
  rw [← h2]
  exact Fermionic.isPure_contractCov_of_isPure h1 hβ (by rw [h3]; exact hinv)

/-- The bond. For a finite set $L$, the labels of the bond are four copies of $L$, ordered
$x_L, x_{L'}, y_L, y_{L'}$; the bond is $\begin{pmatrix} \omega & 0 \\ 0 & -\omega \end{pmatrix}$
with $\omega = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ on $(L, L')$, so
$\Gamma_{x_a x_{a'}} = 1$ and $\Gamma_{y_a y_{a'}} = -1$ for $a \in L$. The bond is pure. -/
theorem bond_pure (L : Type*) [Fintype L] [DecidableEq L] :
    PairIndex L = ((L ⊕ L) ⊕ (L ⊕ L)) ∧
    bond L = fromBlocks (fromBlocks 0 1 (-1) 0) 0 0 (-(fromBlocks 0 1 (-1) 0)) ∧
    Pure (bond L) :=
  ⟨rfl, rfl, Fermionic.pure_bond⟩

/-- Entanglement swapping through a bond. Take two bonds, on $(A_1, B_1)$ and on $(A_2, B_2)$,
each mode set a copy of $L$ and each bond on its labels $(x_A, x_B, y_A, y_B)$, and form their
block-diagonal sum. Read it on the retained labels $(x_{A_1}, x_{B_2}, y_{A_1}, y_{B_2})$
followed by the eliminated labels $(x_{B_1}, x_{A_2}, y_{B_1}, y_{A_2})$, through the map $\tau$
sending each of these labels to the label of the same name in the sum. The result is
$\begin{pmatrix} 0 & X \\ -X^T & 0 \end{pmatrix}$ with $X = \operatorname{diag}(1, -1, -1, 1)$
in blocks of size $|L|$, and its contraction with the bond on $(B_1, A_2)$ is the bond on
$(A_1, B_2)$. -/
theorem teleportation (L : Type*) [Fintype L] [DecidableEq L]
    (X : Matrix (PairIndex L) (PairIndex L) ℝ)
    (hX : X = fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (fromBlocks (-1) 0 0 1))
    (τ : PairIndex L ⊕ PairIndex L → PairIndex L ⊕ PairIndex L)
    (hτ : τ = Sum.elim
      (Sum.elim
        (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a)))
          (fun b => Sum.inr (Sum.inl (Sum.inr b))))
        (Sum.elim (fun a => Sum.inl (Sum.inr (Sum.inl a)))
          (fun b => Sum.inr (Sum.inr (Sum.inr b)))))
      (Sum.elim
        (Sum.elim (fun b => Sum.inl (Sum.inl (Sum.inr b)))
          (fun a => Sum.inr (Sum.inl (Sum.inl a))))
        (Sum.elim (fun b => Sum.inl (Sum.inr (Sum.inr b)))
          (fun a => Sum.inr (Sum.inr (Sum.inl a)))))) :
    (fromBlocks (bond L) 0 0 (bond L)).submatrix τ τ = fromBlocks 0 X (-Xᵀ) 0 ∧
    contract (fromBlocks 0 X (-Xᵀ) 0) (bond L) = bond L := by
  have hX' : fromBlocks 0 X (-Xᵀ) 0 = teleportInput L := by rw [hX]; rfl
  have hτ' : τ = teleportRelabel := by
    rw [hτ]; funext u
    rcases u with ((a | a) | (a | a)) | ((a | a) | (a | a)) <;> rfl
  rw [hX', hτ']
  exact ⟨Fermionic.teleportInput_eq_submatrix, Fermionic.contract_teleportInput⟩

/-! ## Periodic chains and three sites

A periodic chain has $N$ sites $0, \dots, N - 1$, read modulo $N$; $i + 1$ and $i - 1$ are the
cyclic successor and predecessor. Each site carries $M$ left virtual modes $A$, $M$ right virtual
modes $B$ and $P$ physical modes $C$ (each numbered from $0$); its Majorana labels are ordered
$x_A, x_B, x_C, y_A, y_B, y_C$. The chain data are real matrices $\Gamma_i$ on the labels of site
$i$. The retained labels of the chain are the physical labels $x_{(i,c)}, y_{(i,c)}$ of all sites,
$x$ first. The eliminated labels are the bond labels $x_L, x_{L'}, y_L, y_{L'}$ with
$L = L' = \{\text{sites}\} \times \{\text{virtual modes}\}$: the label $(i, a)$ of $L$ is the mode
$A_a$ of site $i$, and the label $(i, a)$ of $L'$ is the mode $B_a$ of site $i - 1$, so that bond
$i$ joins site $i - 1$ to site $i$. The periodic input is the block-diagonal sum of the
$\Gamma_i$ on these labels, the periodic bond is the bond on $L$, and the periodic covariance
$\Gamma_N$ is the contraction of the periodic input with the periodic bond, a matrix on the
physical labels. -/

/-- The label sets of a chain: the labels of a site are $(A, B, C)$ for $x$, then $(A, B, C)$
for $y$; the retained labels are the pairs (site, physical mode) for $x$, then for $y$; the
eliminated labels are the bond labels on the pairs (site, virtual mode). -/
theorem chain_labels (N M P : ℕ) :
    SiteLabel M P = (((Fin M ⊕ Fin M) ⊕ Fin P) ⊕ ((Fin M ⊕ Fin M) ⊕ Fin P)) ∧
    Retained N P = ((Fin N × Fin P) ⊕ (Fin N × Fin P)) ∧
    Eliminated N M = PairIndex (Fin N × Fin M) :=
  ⟨rfl, rfl, rfl⟩

/-- The definition of the periodic chain. The periodic input of chain data $\Gamma_i$ is the
block-diagonal matrix $\bigoplus_i \Gamma_i$ on (site label, site) relabelled by $\sigma$, which
sends $x_{(i,c)} \mapsto (x_{C_c}, i)$, $y_{(i,c)} \mapsto (y_{C_c}, i)$, the $L$ labels
$x_{(i,a)} \mapsto (x_{A_a}, i)$, $y_{(i,a)} \mapsto (y_{A_a}, i)$, and the $L'$ labels
$x_{(i,a)} \mapsto (x_{B_a}, i - 1)$, $y_{(i,a)} \mapsto (y_{B_a}, i - 1)$. The periodic bond is
the bond on $L$, and the periodic covariance is the contraction of the periodic input with the
periodic bond. -/
theorem periodic_def {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (σ : Retained N P ⊕ Eliminated N M → SiteLabel M P × Fin N)
    (hσ : σ = Sum.elim
      (Sum.elim (fun p => (Sum.inl (Sum.inr p.2), p.1)) (fun p => (Sum.inr (Sum.inr p.2), p.1)))
      (Sum.elim
        (Sum.elim (fun p => (Sum.inl (Sum.inl (Sum.inl p.2)), p.1))
          (fun p => (Sum.inl (Sum.inl (Sum.inr p.2)), (finRotate N).symm p.1)))
        (Sum.elim (fun p => (Sum.inr (Sum.inl (Sum.inl p.2)), p.1))
          (fun p => (Sum.inr (Sum.inl (Sum.inr p.2)), (finRotate N).symm p.1))))) :
    periodicInput Γ = (blockDiagonal Γ).submatrix σ σ ∧
    periodicBond N M = bond (Fin N × Fin M) ∧
    periodicCovariance Γ = contract (periodicInput Γ) (periodicBond N M) := by
  refine ⟨?_, rfl, rfl⟩
  have h : σ = fun u => siteMajorEquiv N M P (chainEquiv N M P u) := by
    subst hσ; funext u
    rcases u with (⟨i, c⟩ | ⟨i, c⟩) | ((⟨i, a⟩ | ⟨i, a⟩) | (⟨i, a⟩ | ⟨i, a⟩)) <;> rfl
  rw [h]; rfl

/-- Admissibility of the chain. The periodic input is admissible exactly when every $\Gamma_i$
is, and pure exactly when every $\Gamma_i$ is. If every $\Gamma_i$ is admissible and the
contraction condition holds for the periodic input and the periodic bond, the periodic
covariance $\Gamma_N$ is admissible. -/
theorem periodic_admissible {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    (Admissible (periodicInput Γ) ↔ ∀ i, Admissible (Γ i)) ∧
    (Pure (periodicInput Γ) ↔ ∀ i, Pure (Γ i)) ∧
    ((∀ i, Admissible (Γ i)) → ContractInvertible (periodicInput Γ) (periodicBond N M) →
      Admissible (periodicCovariance Γ)) :=
  ⟨Fermionic.admissible_periodicInput_iff Γ, Fermionic.pure_periodicInput_iff Γ,
    fun h hinv => Fermionic.periodicCovariance_admissible Γ h hinv⟩

/-- Purity of the chain. If every $\Gamma_i$ is pure and the contraction condition holds, the
periodic covariance $\Gamma_N$ is pure. -/
theorem periodic_pure {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hpure : ∀ i, Pure (Γ i)) (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) :
    Pure (periodicCovariance Γ) :=
  Fermionic.pure_periodicCovariance_of_forall_pure Γ hpure hinv

/-- A three-site chain, evaluated exactly. Take $N = 3$ sites, $M = P = 1$, and at every site
the matrix $G$ that, on the labels ordered $(x_A, x_B, x_C, y_A, y_B, y_C)$, is
$\tfrac15 \begin{pmatrix} 0 & 3 & -4 & 0 & 0 & 0 \\ -3 & 0 & 0 & 0 & 0 & -4 \\
4 & 0 & 0 & 0 & 0 & -3 \\ 0 & 0 & 0 & 0 & -5 & 0 \\ 0 & 0 & 0 & 5 & 0 & 0 \\
0 & 4 & 3 & 0 & 0 & 0 \end{pmatrix}$. Then $G$ is pure, the contraction condition holds with
$\det(1 - D\beta_3) = (304/125)^2$ ($D$ the block of the input on the eliminated labels,
$\beta_3$ the bond), and the periodic covariance, on the physical labels ordered
$(x_{C_0}, x_{C_1}, x_{C_2}, y_{C_0}, y_{C_1}, y_{C_2})$, is
$\tfrac1{19} \begin{pmatrix} 0 & 0 & 0 & -15 & 6 & -10 \\ 0 & 0 & 0 & -10 & -15 & 6 \\
0 & 0 & 0 & 6 & -10 & -15 \\ 15 & 10 & -6 & 0 & 0 & 0 \\ -6 & 15 & 10 & 0 & 0 & 0 \\
10 & -6 & 15 & 0 & 0 & 0 \end{pmatrix}$. -/
theorem three_site (G : Matrix (SiteLabel 1 1) (SiteLabel 1 1) ℝ) (f : SiteLabel 1 1 → Fin 6)
    (hf : f = Sum.elim (Sum.elim (Sum.elim (fun _ => 0) (fun _ => 1)) (fun _ => 2))
      (Sum.elim (Sum.elim (fun _ => 3) (fun _ => 4)) (fun _ => 5)))
    (hG : G = (5 : ℝ)⁻¹ • (!![0, 3, -4, 0, 0, 0;
      -3, 0, 0, 0, 0, -4;
      4, 0, 0, 0, 0, -3;
      0, 0, 0, 0, -5, 0;
      0, 0, 0, 5, 0, 0;
      0, 4, 3, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℝ).submatrix f f)
    (g : Retained 3 1 → Fin 6)
    (hg : g = Sum.elim (fun p => Fin.castAdd 3 p.1) (fun p => Fin.natAdd 3 p.1)) :
    Pure G ∧ ContractInvertible (periodicInput fun _ : Fin 3 => G) (periodicBond 3 1) ∧
    (1 - (periodicInput fun _ : Fin 3 => G).toBlocks₂₂ * periodicBond 3 1).det =
      (304 / 125 : ℝ) ^ 2 ∧
    periodicCovariance (fun _ : Fin 3 => G) = (19 : ℝ)⁻¹ • (!![0, 0, 0, -15, 6, -10;
      0, 0, 0, -10, -15, 6;
      0, 0, 0, 6, -10, -15;
      15, 10, -6, 0, 0, 0;
      -6, 15, 10, 0, 0, 0;
      10, -6, 15, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℝ).submatrix g g := by
  have hG' : G = threeSiteLocal := by
    subst hG hf
    ext (((a | a) | a) | ((a | a) | a)) (((b | b) | b) | ((b | b) | b)) <;>
      simp [threeSiteLocal, threeSiteLocalZ, siteLabelIdx]
  subst hG'
  refine ⟨Fermionic.pure_threeSiteLocal, Fermionic.threeSite_contractInvertible,
    Fermionic.threeSite_det, ?_⟩
  rw [Fermionic.periodicCovariance_threeSite]
  subst hg
  ext (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩) <;> fin_cases i <;> fin_cases j <;>
    simp [threeSiteOutput, threeSiteOutputZ, retainedIdx]

/-! ## Momentum space

A homogeneous chain has the same matrix $\Gamma$ on the labels of every site, and $N \ge 1$
sites. For sites $i$ and momenta $k$ in $\{0, \dots, N - 1\}$ the character is
$\chi_k(i) = e^{-2\pi i k i / N}$ and the phase of one step is $\omega_k = e^{-2\pi i k / N}$; the
momentum $-k$ is $N - k$ modulo $N$. The twist $t_k$ is the function on the labels of a site
that is $\omega_k$ on the labels $x_B, y_B$ and $1$ on all others. The twisted local matrix
$T_k = \operatorname{diag}(t_k)\, \Gamma\, \operatorname{diag}(t_k)^*$ is a complex matrix,
written in the split of the site labels into the physical labels $(x_C, y_C)$ and the virtual
labels $(x_L, x_{L'}, y_L, y_{L'}) = (x_A, x_B, y_A, y_B)$. The momentum-space covariance
$\Sigma(k)$ is the contraction of $T_k$ with the bond $\beta_M$ of one site's $M$ virtual modes,
computed over $\mathbb C$ with the complex matrix inverse; it is a complex matrix on the physical
labels $(x_C, y_C)$ of one site. A physical label $u$ of a site, placed at site $i$, is written
$(i, u)$; $\Gamma_N$ is the periodic covariance of the homogeneous chain. For a complex matrix,
$X^*$ is the conjugate transpose and $\bar X$ the entrywise conjugate. -/

/-- The definition of the momentum-space covariance. With $\omega_k = e^{-2\pi i k / N}$, the
twist $t_k$ equal to $\omega_k$ on $x_B, y_B$ and $1$ elsewhere, and $s$ the split of the site
labels sending the physical labels $x_c, y_c$ to $x_{C_c}, y_{C_c}$ and the virtual labels
$x_L, x_{L'}, y_L, y_{L'}$ to $x_A, x_B, y_A, y_B$: the twisted local matrix is
$T_k = (\operatorname{diag}(t_k)\, \Gamma\, \operatorname{diag}(t_k)^*)_{s(u) s(v)}$, the
one-site bond is the bond on $M$ modes regarded as a complex matrix, and
$\Sigma(k) = A_k + B_k \beta_M (1 - D_k \beta_M)^{-1} C_k$ in the blocks
$A_k, B_k, C_k, D_k$ of $T_k$ (physical, then virtual). -/
theorem momentum_def {N M P : ℕ} (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) (k : Fin N)
    (t : SiteLabel M P → ℂ)
    (ht : t = Sum.elim
      (Sum.elim (Sum.elim (fun _ => 1)
        (fun _ => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ))))
        (fun _ => 1))
      (Sum.elim (Sum.elim (fun _ => 1)
        (fun _ => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ))))
        (fun _ => 1)))
    (s : (Fin P ⊕ Fin P) ⊕ PairIndex (Fin M) → SiteLabel M P)
    (hs : s = Sum.elim
      (Sum.elim (fun c => Sum.inl (Sum.inr c)) (fun c => Sum.inr (Sum.inr c)))
      (Sum.elim
        (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl a))) (fun a => Sum.inl (Sum.inl (Sum.inr a))))
        (Sum.elim (fun a => Sum.inr (Sum.inl (Sum.inl a)))
          (fun a => Sum.inr (Sum.inl (Sum.inr a)))))) :
    twistedSplit Γ k = (diagonal t * Γ.map Complex.ofReal * (diagonal t)ᴴ).submatrix s s ∧
    bondC M = (bond (Fin M)).map Complex.ofReal ∧
    momentumCovariance Γ k = (twistedSplit Γ k).toBlocks₁₁ +
      (twistedSplit Γ k).toBlocks₁₂ * bondC M * (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M)⁻¹ *
        (twistedSplit Γ k).toBlocks₂₁ := by
  refine ⟨?_, rfl, rfl⟩
  have h1 : twist k = t := by
    subst ht; funext u
    rcases u with ((a | a) | c) | ((a | a) | c) <;> rfl
  have h2 : ⇑(siteSplit M P) = s := by
    subst hs; funext w
    rcases w with (c | c) | ((a | a) | (a | a)) <;> rfl
  unfold twistedSplit twistedLocal
  rw [h1, h2]

/-- The determinant factorizes over momenta. For a homogeneous chain,
$\det(1 - D \beta_N) = \prod_k \det(1 - D_k \beta_M)$, where $D$ is the virtual block of the
periodic input, $\beta_N$ the periodic bond, and $D_k$ the virtual block of $T_k$. In particular,
under the contraction condition of the chain every $\det(1 - D_k \beta_M)$ is nonzero. -/
theorem momentum_det {N M P : ℕ} [NeZero N] (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) :
    (((1 - (periodicInput fun _ : Fin N => Γ).toBlocks₂₂ * periodicBond N M).det : ℝ) : ℂ) =
      ∏ k : Fin N, (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M).det ∧
    (ContractInvertible (periodicInput fun _ : Fin N => Γ) (periodicBond N M) →
      ∀ k : Fin N, (1 - (twistedSplit Γ k).toBlocks₂₂ * bondC M).det ≠ 0) :=
  ⟨Fermionic.det_one_sub_periodic_eq_prod Γ,
    fun hinv k => (Fermionic.momentum_isUnit_det_of_contractInvertible Γ hinv k).ne_zero⟩

/-- Diagonalization by the Fourier transform. For a homogeneous chain with the contraction
condition, momenta $k, l$ and physical labels $a, b$ of a site,
$\frac1N \sum_{i,j} \chi_k(i)\, (\Gamma_N)_{(i,a)(j,b)}\, \overline{\chi_l(j)} = \delta_{kl}\,
\Sigma(k)_{ab}$. -/
theorem fourier_diagonal {N M P : ℕ} [NeZero N] (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hinv : ContractInvertible (periodicInput fun _ : Fin N => Γ) (periodicBond N M))
    (k l : Fin N) (a b : Fin P ⊕ Fin P) :
    (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) * (i.val : ℂ) / (N : ℂ)) *
        ((periodicCovariance (fun _ : Fin N => Γ) (Sum.map (Prod.mk i) (Prod.mk i) a)
          (Sum.map (Prod.mk j) (Prod.mk j) b) : ℝ) : ℂ) *
        star (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (l.val : ℂ) * (j.val : ℂ) / (N : ℂ)))
      = if k = l then momentumCovariance Γ k a b else 0 := by
  have e : ∀ (i : Fin N) (a : Fin P ⊕ Fin P), Sum.map (Prod.mk i) (Prod.mk i) a = retained i a :=
    fun i a => by cases a <;> rfl
  simp only [e]
  exact Fermionic.fourierEntry_eq Γ hinv k l a b

/-- Reconstruction and translation invariance. For a homogeneous chain with the contraction
condition, sites $i, j$ and physical labels $a, b$ of a site,
$(\Gamma_N)_{(i,a)(j,b)} = \frac1N \sum_k \overline{\chi_k(i)}\, \Sigma(k)_{ab}\, \chi_k(j)$, and
$(\Gamma_N)_{(i+1,a)(j+1,b)} = (\Gamma_N)_{(i,a)(j,b)}$. -/
theorem fourier_reconstruct {N M P : ℕ} [NeZero N]
    (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hinv : ContractInvertible (periodicInput fun _ : Fin N => Γ) (periodicBond N M))
    (i j : Fin N) (a b : Fin P ⊕ Fin P) :
    ((periodicCovariance (fun _ : Fin N => Γ) (Sum.map (Prod.mk i) (Prod.mk i) a)
        (Sum.map (Prod.mk j) (Prod.mk j) b) : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ k : Fin N,
        star (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) * (i.val : ℂ) / (N : ℂ))) *
          momentumCovariance Γ k a b *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) * (j.val : ℂ) / (N : ℂ)) ∧
    periodicCovariance (fun _ : Fin N => Γ)
        (Sum.map (Prod.mk (finRotate N i)) (Prod.mk (finRotate N i)) a)
        (Sum.map (Prod.mk (finRotate N j)) (Prod.mk (finRotate N j)) b) =
      periodicCovariance (fun _ : Fin N => Γ) (Sum.map (Prod.mk i) (Prod.mk i) a)
        (Sum.map (Prod.mk j) (Prod.mk j) b) := by
  have e : ∀ (i : Fin N) (a : Fin P ⊕ Fin P), Sum.map (Prod.mk i) (Prod.mk i) a = retained i a :=
    fun i a => by cases a <;> rfl
  simp only [e]
  exact ⟨Fermionic.homogeneousCovariance_reconstruct Γ hinv i j a b,
    Fermionic.homogeneousCovariance_translation Γ hinv i j a b⟩

open scoped ComplexOrder in
/-- Symmetries of the momentum-space covariance. For a homogeneous chain and every momentum $k$:
$\Sigma(-k) = \overline{\Sigma(k)}$. If $\Gamma$ is antisymmetric and the contraction condition
holds, $\Sigma(k)^* = -\Sigma(k)$. If $\Gamma$ is admissible and the contraction condition holds,
$1 - \Sigma(k)^* \Sigma(k)$ is positive semidefinite. -/
theorem momentum_symmetries {N M P : ℕ} [NeZero N]
    (Γ : Matrix (SiteLabel M P) (SiteLabel M P) ℝ) (k : Fin N) :
    momentumCovariance Γ (-k) = (momentumCovariance Γ k).map star ∧
    (Γᵀ = -Γ → ContractInvertible (periodicInput fun _ : Fin N => Γ) (periodicBond N M) →
      (momentumCovariance Γ k)ᴴ = -momentumCovariance Γ k) ∧
    (Admissible Γ → ContractInvertible (periodicInput fun _ : Fin N => Γ) (periodicBond N M) →
      (1 - (momentumCovariance Γ k)ᴴ * momentumCovariance Γ k).PosSemidef) :=
  ⟨Fermionic.momentumCovariance_neg Γ k,
    fun hΓ hinv => Fermionic.momentumCovariance_conjTranspose Γ hΓ hinv k,
    fun hΓ hinv => Fermionic.momentumCovariance_posSemidef Γ hΓ hinv k⟩

/-! ## Normal form and rotations

For real numbers $\varepsilon_0, \dots, \varepsilon_{n-1}$, the block form $D(\varepsilon)$ is the
real matrix on the Majorana labels of $n$ modes with $D(\varepsilon)_{x_j y_j} = \varepsilon_j$,
$D(\varepsilon)_{y_j x_j} = -\varepsilon_j$ and all other entries $0$. A plane rotation on a
finite index set $\iota$ acts as the rotation by the angle with cosine $c$ and sine $s$ in the
plane of two distinct labels $a, b$ and as the identity elsewhere. The exponential of a square
matrix is the sum of its exponential series. -/

/-- The block form: $D(\varepsilon) = \begin{pmatrix} 0 & \operatorname{diag}(\varepsilon) \\
-\operatorname{diag}(\varepsilon) & 0 \end{pmatrix}$. It is admissible exactly when every
$|\varepsilon_j| \le 1$, and pure exactly when every $|\varepsilon_j| = 1$. -/
theorem block_form {n : ℕ} (ε : Fin n → ℝ) :
    blockForm ε = fromBlocks 0 (diagonal ε) (-diagonal ε) 0 ∧
    (IsAdmissible (blockForm ε) ↔ ∀ j, |ε j| ≤ 1) ∧
    (IsPure (blockForm ε) ↔ ∀ j, |ε j| = 1) :=
  ⟨rfl, Fermionic.isAdmissible_blockForm_iff ε, Fermionic.isPure_blockForm_iff ε⟩

/-- The normal form. Every real antisymmetric matrix $\Gamma$ on the Majorana labels of $n$
modes is $\Gamma = O D(\varepsilon) O^T$ with $O$ orthogonal and every $\varepsilon_j \ge 0$; and
also $\Gamma = O' D(\varepsilon') O'^T$ with $O'$ orthogonal of determinant $1$. -/
theorem normal_form {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hΓ : Γᵀ = -Γ) :
    (∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * Oᵀ = 1 ∧ (∀ j, 0 ≤ ε j) ∧ Γ = O * blockForm ε * Oᵀ) ∧
    (∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * Oᵀ = 1 ∧ O.det = 1 ∧ Γ = O * blockForm ε * Oᵀ) :=
  ⟨Fermionic.exists_normalForm Γ hΓ, Fermionic.exists_normalForm_special Γ hΓ⟩

/-- The values of the normal form. If $\Gamma = O D(\varepsilon) O^T$ with $O$ orthogonal, then
$\Gamma$ is admissible exactly when every $|\varepsilon_j| \le 1$, and pure exactly when every
$|\varepsilon_j| = 1$. -/
theorem normal_form_values {n : ℕ} {O Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} (hO : O * Oᵀ = 1) (h : Γ = O * blockForm ε * Oᵀ) :
    (IsAdmissible Γ ↔ ∀ j, |ε j| ≤ 1) ∧ (IsPure Γ ↔ ∀ j, |ε j| = 1) := by
  refine ⟨⟨Fermionic.abs_le_one_of_isAdmissible_normalForm hO h, fun hε => ?_⟩,
    ⟨Fermionic.abs_eq_one_of_isPure_normalForm hO h, fun hε => ?_⟩⟩
  · rw [h]
    exact Fermionic.isAdmissible_orthogonalCongruence hO
      ((Fermionic.isAdmissible_blockForm_iff ε).2 hε)
  · rw [h]
    exact Fermionic.isPure_orthogonalCongruence hO ((Fermionic.isPure_blockForm_iff ε).2 hε)

/-- The exponential of a block form. For real $\theta_0, \dots, \theta_{n-1}$,
$e^{D(\theta)} = \begin{pmatrix} \operatorname{diag}(\cos\theta) & \operatorname{diag}(\sin\theta)
\\ -\operatorname{diag}(\sin\theta) & \operatorname{diag}(\cos\theta) \end{pmatrix}$, and this
matrix $R$ is orthogonal, $R R^T = 1$. -/
theorem block_exponential {n : ℕ} (θ : Fin n → ℝ) :
    NormedSpace.exp (blockForm θ) =
      fromBlocks (diagonal fun j => Real.cos (θ j)) (diagonal fun j => Real.sin (θ j))
        (-diagonal fun j => Real.sin (θ j)) (diagonal fun j => Real.cos (θ j)) ∧
    NormedSpace.exp (blockForm θ) * (NormedSpace.exp (blockForm θ))ᵀ = 1 := by
  rw [Fermionic.exp_blockForm]
  refine ⟨?_, Fermionic.blockRotation_mul_transpose _⟩
  simp [blockRotation, Real.cos_neg, Real.sin_neg, diagonal_neg]

/-- Rotations generate the special orthogonal group. For labels $a \ne b$ of a finite index
set $\iota$, the plane rotation $R_{ab}(c, s)$ has rows $a$ and $b$ equal to $(c, -s)$ and
$(s, c)$ on the columns $(a, b)$ and zero elsewhere, and every other row equal to that of the
identity (for $a = b$ the defining formula gives the identity with $c$ at $(a, a)$; the products
below use only $a \ne b$). A real matrix $O$
on $\iota$ is orthogonal with $\det O = 1$ exactly when it is a finite product (possibly empty)
of plane rotations $R_{ab}(c, s)$ with $a \ne b$ and $c^2 + s^2 = 1$. -/
theorem rotation_products {ι : Type*} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℝ) :
    (∀ (c s : ℝ) (a b u v : ι), planeRot c s a b u v =
      if u = a then (if v = a then c else if v = b then -s else 0)
      else if u = b then (if v = a then s else if v = b then c else 0)
      else if v = u then 1 else 0) ∧
    (O * Oᵀ = 1 ∧ O.det = 1 ↔
      ∃ l : List (Matrix ι ι ℝ), (∀ R ∈ l, ∃ (c s : ℝ) (a b : ι),
        a ≠ b ∧ c * c + s * s = 1 ∧ R = planeRot c s a b) ∧ O = l.prod) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
  have key : ∀ R : Matrix ι ι ℝ, IsRotProduct R → ∃ l : List (Matrix ι ι ℝ),
      (∀ R ∈ l, ∃ (c s : ℝ) (a b : ι), a ≠ b ∧ c * c + s * s = 1 ∧ R = planeRot c s a b) ∧
        R = l.prod := by
    intro R hR
    induction hR with
    | one => exact ⟨[], by simp, by simp⟩
    | @mul_planeRot R c s a b _ hab hcs ih =>
      obtain ⟨l, hl, rfl⟩ := ih
      refine ⟨l ++ [planeRot c s a b], fun R' hR' => ?_, by simp⟩
      rcases List.mem_append.1 hR' with h | h
      · exact hl R' h
      · rw [List.mem_singleton] at h
        exact ⟨c, s, a, b, hab, hcs, h⟩
  have back : ∀ l : List (Matrix ι ι ℝ), (∀ R ∈ l, ∃ (c s : ℝ) (a b : ι),
      a ≠ b ∧ c * c + s * s = 1 ∧ R = planeRot c s a b) → IsRotProduct l.prod := by
    intro l
    induction l with
    | nil => intro _; exact IsRotProduct.one
    | cons R l ih =>
      intro hl
      obtain ⟨c, s, a, b, hab, hcs, rfl⟩ := hl R List.mem_cons_self
      rw [List.prod_cons]
      exact (IsRotProduct.planeRot hab hcs).mul (ih fun R' h => hl R' (List.mem_cons_of_mem _ h))
  constructor
  · rintro ⟨hO, hdet⟩
    exact key O (Fermionic.isRotProduct_of_special_orthogonal O hO hdet)
  · rintro ⟨l, hl, rfl⟩
    exact ⟨(back l hl).mul_transpose_self, (back l hl).det⟩

/-! ## Examples: product chains and the Kitaev chain

A chain without virtual modes ($M = 0$) has no bonds. The Kitaev chain at its solvable point has
one physical and one virtual mode per site ($M = P = 1$); the labels of a site are written
$x_A, x_B, x_C, y_A, y_B, y_C$, and those of the chain $x_i, y_i$ for the physical mode of site
$i$. For labels $u, v$, $E_{uv}$ is the matrix with entry $1$ at $(u, v)$ and $0$ elsewhere. -/

/-- Chains without virtual modes are products. For chain data $\Gamma_i$ with $M = 0$, the
contraction condition holds; the periodic covariance couples only labels of the same site,
$(\Gamma_N)_{(i,a)(j,b)} = \delta_{ij} (\Gamma_i)_{C_a C_b}$ for physical labels $a, b$, where
$C_a$ is the site label $x_{C_c}$ for $a = x_c$ and $y_{C_c}$ for $a = y_c$; and $\Gamma_N$ is
admissible exactly when every $\Gamma_i$ is, pure exactly when every $\Gamma_i$ is. -/
theorem product_chain {N P : ℕ} (Γ : Fin N → Matrix (SiteLabel 0 P) (SiteLabel 0 P) ℝ) :
    ContractInvertible (periodicInput Γ) (periodicBond N 0) ∧
    (∀ (i j : Fin N) (a b : Fin P ⊕ Fin P),
      periodicCovariance Γ (Sum.map (Prod.mk i) (Prod.mk i) a) (Sum.map (Prod.mk j) (Prod.mk j) b)
        = if i = j then Γ i (Sum.map Sum.inr Sum.inr a) (Sum.map Sum.inr Sum.inr b) else 0) ∧
    (Admissible (periodicCovariance Γ) ↔ ∀ i, Admissible (Γ i)) ∧
    (Pure (periodicCovariance Γ) ↔ ∀ i, Pure (Γ i)) := by
  refine ⟨Fermionic.contractInvertible_zero Γ, fun i j a b => ?_,
    Fermionic.admissible_periodicCovariance_zero_iff Γ,
    Fermionic.pure_periodicCovariance_zero_iff Γ⟩
  have e : ∀ (i : Fin N) (a : Fin P ⊕ Fin P), Sum.map (Prod.mk i) (Prod.mk i) a = retained i a :=
    fun i a => by cases a <;> rfl
  have e' : ∀ a : Fin P ⊕ Fin P, Sum.map Sum.inr Sum.inr a = siteSplit 0 P (Sum.inl a) :=
    fun a => by cases a <;> rfl
  simp only [e, e']
  exact Fermionic.periodicCovariance_zero_apply Γ i j a b

/-- The Kitaev on-site covariance $K = E_{x_C x_A} - E_{x_A x_C} + E_{y_C x_B} - E_{x_B y_C}$
correlates $x_C$ with $x_A$ and $y_C$ with $x_B$. It is admissible and not pure. -/
theorem kitaev_local :
    kitaevLocal =
      single (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inl (Sum.inl 0))) 1 -
      single (Sum.inl (Sum.inl (Sum.inl 0))) (Sum.inl (Sum.inr 0)) 1 +
      single (Sum.inr (Sum.inr 0)) (Sum.inl (Sum.inl (Sum.inr 0))) 1 -
      single (Sum.inl (Sum.inl (Sum.inr 0))) (Sum.inr (Sum.inr 0)) 1 ∧
    Admissible kitaevLocal ∧ ¬ Pure kitaevLocal := by
  refine ⟨?_, Fermionic.admissible_kitaevLocal, Fermionic.not_pure_kitaevLocal⟩
  ext (((a | a) | a) | ((a | a) | a)) (((b | b) | b) | ((b | b) | b)) <;>
    simp [kitaevLocal, Fin.eq_zero]

/-- The Kitaev chain. The matrix $K_N$ on the physical labels of $N$ sites has
$(K_N)_{y_i x_j} = 1$ and $(K_N)_{x_j y_i} = -1$ when $j = i + 1$, and all other entries $0$. For
$N \ge 1$, the chain with $K$ at every site satisfies the contraction condition, its periodic
covariance is $K_N$, and $K_N$ is pure. -/
theorem kitaev_chain {N : ℕ} [NeZero N] :
    (∀ (i j : Fin N) (c d : Fin 1),
      kitaevChain N (Sum.inr (i, c)) (Sum.inl (j, d)) = (if j = finRotate N i then 1 else 0) ∧
      kitaevChain N (Sum.inl (j, d)) (Sum.inr (i, c)) = (if j = finRotate N i then -1 else 0) ∧
      kitaevChain N (Sum.inl (i, c)) (Sum.inl (j, d)) = 0 ∧
      kitaevChain N (Sum.inr (i, c)) (Sum.inr (j, d)) = 0) ∧
    ContractInvertible (periodicInput fun _ : Fin N => kitaevLocal) (periodicBond N 1) ∧
    periodicCovariance (fun _ : Fin N => kitaevLocal) = kitaevChain N ∧
    Pure (kitaevChain N) :=
  ⟨fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩, Fermionic.kitaev_contractInvertible,
    Fermionic.periodicCovariance_kitaev, Fermionic.pure_kitaevChain⟩

/-- The Kitaev chain in momentum space. For $N \ge 1$ and every momentum $k$, the
momentum-space covariance of the Kitaev on-site covariance $K$ is
$\Sigma(k) = \begin{pmatrix} 0 & -\omega_k \\ \overline{\omega_k} & 0 \end{pmatrix}$ on
$(x_C, y_C)$, with $\omega_k = e^{-2\pi i k / N}$. -/
theorem kitaev_momentum {N : ℕ} [NeZero N] (k : Fin N) :
    momentumCovariance kitaevLocal k =
      fromBlocks 0
        (of fun _ _ => -Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ)))
        (of fun _ _ => star (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ))))
        0 := by
  rw [Fermionic.momentumCovariance_kitaev]
  ext (a | a) (b | b) <;> simp [kitaevSymbol, sitePhase]

/-- A pure completion of the Kitaev on-site covariance. The matrix
$K' = K - E_{y_A y_B} + E_{y_B y_A}$ is pure. For $N \ge 1$, the chain with $K'$ at every site
has $\det(1 - D \beta_N) = (1 - (-1)^N)^2$, where $D$ is the virtual block of the periodic input
and $\beta_N$ the periodic bond, so the contraction condition fails for even $N$; for odd $N$ it
holds and the periodic covariance is the Kitaev chain $K_N$. -/
theorem kitaev_completion {N : ℕ} [NeZero N] :
    kitaevPure = kitaevLocal -
      single (Sum.inr (Sum.inl (Sum.inl 0))) (Sum.inr (Sum.inl (Sum.inr 0))) 1 +
      single (Sum.inr (Sum.inl (Sum.inr 0))) (Sum.inr (Sum.inl (Sum.inl 0))) 1 ∧
    Pure kitaevPure ∧
    (1 - (periodicInput fun _ : Fin N => kitaevPure).toBlocks₂₂ * periodicBond N 1).det =
      (1 - (-1 : ℝ) ^ N) ^ 2 ∧
    (Odd N → ContractInvertible (periodicInput fun _ : Fin N => kitaevPure) (periodicBond N 1) ∧
      periodicCovariance (fun _ : Fin N => kitaevPure) = kitaevChain N) := by
  refine ⟨?_, Fermionic.pure_kitaevPure, Fermionic.det_one_sub_kitaevPure,
    Fermionic.periodicCovariance_kitaevPure_of_odd⟩
  ext (((a | a) | a) | ((a | a) | a)) (((b | b) | b) | ((b | b) | b)) <;>
    simp [kitaevPure, kitaevLocal, Fin.eq_zero]

/-! ## Entanglement rank

For a periodic chain and a set $S$ of sites, $R_S$ is the set of physical labels of the sites in
$S$ and $R_{S^c}$ that of the sites outside $S$. For a matrix $X$ on the physical labels, the
cross block is $C_S = X_{R_S R_{S^c}}$ and the block covariance is $\Gamma_S = X_{R_S R_S}$.
Bond $i$ joins site $i - 1$ to site $i$ and is cut by $S$ when exactly one of the two sites lies
in $S$; $b(S)$ is the number of cut bonds. The rank of a matrix is the dimension of its column
space. -/

/-- The definitions of the cut. The site of the physical labels $x_{(i,c)}, y_{(i,c)}$ is $i$;
$R_S$ and $R_{S^c}$ are the physical labels whose site is in $S$, respectively not in $S$; the
cross block $C_S$ and the block covariance $\Gamma_S$ are the corresponding submatrices of $X$;
and the cut bonds are the sites $i$ such that exactly one of $i$ and $i - 1$ lies in $S$. -/
theorem cut_def {N P : ℕ} (S : Finset (Fin N)) (X : Matrix (Retained N P) (Retained N P) ℝ) :
    (∀ (i : Fin N) (c : Fin P), siteRetained (Sum.inl (i, c) : Retained N P) = i ∧
      siteRetained (Sum.inr (i, c) : Retained N P) = i) ∧
    RetainedIn (P := P) S = {a : Retained N P // siteRetained a ∈ S} ∧
    RetainedOut (P := P) S = {a : Retained N P // siteRetained a ∉ S} ∧
    crossBlock S X = X.submatrix Subtype.val Subtype.val ∧
    blockCov S X = X.submatrix Subtype.val Subtype.val ∧
    cutBonds S = Finset.univ.filter fun i => ¬ (i ∈ S ↔ (finRotate N).symm i ∈ S) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The cross-block rank bound. For chain data $\Gamma_i$ with the contraction condition and
every set $S$ of sites, the cross block of the periodic covariance has
$\operatorname{rank} C_S \le 2 M\, b(S)$. -/
theorem cross_block_rank {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M)) (S : Finset (Fin N)) :
    (crossBlock S (periodicCovariance Γ)).rank ≤ 2 * M * (cutBonds S).card :=
  Fermionic.rank_crossBlock_periodicCovariance_le Γ hinv S

/-- The entanglement rank bound. For every pure matrix $X$ on the physical labels and every set
$S$ of sites, $1 + \Gamma_S^2 = C_S C_S^T$. Consequently, for chain data with the contraction
condition whose periodic covariance is pure, $\operatorname{rank}(1 + \Gamma_S^2) \le 2 M\,
b(S)$. -/
theorem entanglement_rank {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (S : Finset (Fin N)) :
    (∀ X : Matrix (Retained N P) (Retained N P) ℝ, Pure X →
      1 + blockCov S X * blockCov S X = crossBlock S X * (crossBlock S X)ᵀ) ∧
    (ContractInvertible (periodicInput Γ) (periodicBond N M) → Pure (periodicCovariance Γ) →
      (1 + blockCov S (periodicCovariance Γ) * blockCov S (periodicCovariance Γ)).rank ≤
        2 * M * (cutBonds S).card) :=
  ⟨fun _ hX => Fermionic.one_add_blockCov_sq_eq S hX,
    fun hinv hpure => Fermionic.rank_one_add_blockCov_sq_le Γ hinv hpure S⟩

/-- The rank of $1 + \Gamma^2$ in the normal form. If $O$ is a real orthogonal matrix on the
Majorana labels of $n$ modes and $\Gamma = O D(\lambda) O^T$, then
$\operatorname{rank}(1 + \Gamma^2) = 2\, \#\{j : \lambda_j^2 \ne 1\}$. -/
theorem rank_normal_form {n : ℕ} {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hO : O * Oᵀ = 1) (lam : Fin n → ℝ) :
    (1 + (O * blockForm lam * Oᵀ) * (O * blockForm lam * Oᵀ)).rank =
      2 * (Finset.univ.filter fun j => lam j ^ 2 ≠ 1).card :=
  Fermionic.rank_one_add_sq_normalForm hO lam

/-- The nullity lemma. For an invertible real matrix $X$ on a disjoint union $\iota \sqcup
\kappa$ of finite sets, the $(\iota, \kappa)$ block of $X^{-1}$ has the same rank as the
$(\iota, \kappa)$ block of $X$. -/
theorem nullity_rank {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hX : X.det ≠ 0) :
    (X⁻¹).toBlocks₁₂.rank = X.toBlocks₁₂.rank :=
  Fermionic.rank_toBlocks12_inv X (isUnit_iff_ne_zero.2 hX)

/-! ## Majorana operators and covariances of states

Fock space of $n$ fermionic modes is $\mathbb C^{\{0,1\}^n}$, with basis vectors $|s\rangle$
indexed by the configurations $s = (s_0, \dots, s_{n-1}) \in \{0,1\}^n$ ($s_j = 1$: mode $j$
occupied); operators on it are complex matrices indexed by configurations, and $s^{(j)}$ is $s$
with its bit $j$ flipped. The Majorana labels of $n$ modes are $x_0, \dots, x_{n-1}$ followed by
$y_0, \dots, y_{n-1}$; a real matrix on the labels is written in blocks
$\begin{pmatrix} A & B \\ C & D \end{pmatrix}$ for this order (the $x$-block first), and
$D(\varepsilon) = \begin{pmatrix} 0 & \mathrm{diag}\,\varepsilon \\ -\mathrm{diag}\,\varepsilon & 0
\end{pmatrix}$ for $\varepsilon \in \mathbb R^n$. A density matrix is a positive semidefinite
matrix of trace $1$. The covariance of a matrix $\rho$ is the real matrix
$\Gamma(\rho)_{ab} = \mathrm{Re}\,\tfrac i2 \mathrm{Tr}(\rho\,[c_a, c_b])$; with this sign the
vacuum $|0\cdots0\rangle$ has covariance $\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$.
Admissible and pure covariances are as in the first part: $\Gamma^T = -\Gamma$ with
$1 - \Gamma^T\Gamma$ positive semidefinite, respectively $\Gamma^T = -\Gamma$ with
$\Gamma^2 = -1$. A unitary $U$ implements a real matrix $O$ on the labels when
$U c_a U^* = \sum_b O_{ab} c_b$ for every label $a$. -/

/-- The index sets: the configurations of $n$ modes are the maps from $\{0, \dots, n-1\}$ to
$\{0, 1\}$, and the Majorana labels of $n$ modes are two copies of $\{0, \dots, n-1\}$, the
$x$-labels and then the $y$-labels. -/
theorem fock_labels (n : ℕ) :
    FockIndex n = (Fin n → Fin 2) ∧ MajoranaIndex n = (Fin n ⊕ Fin n) :=
  ⟨rfl, rfl⟩

/-- The Jordan–Wigner Majorana operators of $n$ modes. For every mode $j$ and configurations
$s, t$, the matrix entries are $\langle s|c_{x_j}|t\rangle = \prod_{k<j}(-1)^{s_k}$ and
$\langle s|c_{y_j}|t\rangle = -i\,(-1)^{s_j}\prod_{k<j}(-1)^{s_k}$ when $t = s^{(j)}$, and $0$
otherwise. -/
theorem majorana_entries {n : ℕ} (j : Fin n) (s t : FockIndex n) :
    majorana (Sum.inl j) s t =
      (if t = Function.update s j (s j + 1) then
        ∏ k : Fin n, (if k < j then (if s k = 0 then (1 : ℂ) else -1) else 1) else 0) ∧
    majorana (Sum.inr j) s t =
      (if t = Function.update s j (s j + 1) then
        -Complex.I * (∏ k : Fin n, (if k < j then (if s k = 0 then (1 : ℂ) else -1) else 1)) *
          (if s j = 0 then 1 else -1) else 0) := by
  have key : ∀ a : MajoranaIndex n, mode a = j → majorana a s t =
      if t = Function.update s j (s j + 1) then majoranaSign a s else 0 := by
    intro a ha
    rw [majorana_eq_diagonal_mul, Matrix.diagonal_mul, ha]
    by_cases ht : t = Function.update s j (s j + 1)
    · subst ht
      simp [pauliX, PEquiv.toMatrix_apply, flipPerm_apply, Fermionic.flip]
    · have h' : ¬ Fermionic.flip j s = t := fun h => ht h.symm
      simp [pauliX, PEquiv.toMatrix_apply, flipPerm_apply, h', ht]
  exact ⟨by rw [key _ rfl]; rfl, by rw [key _ rfl]; rfl⟩

/-- The canonical anticommutation relations: the Majorana operators are Hermitian,
$c_a^* = c_a$, and $c_a c_b + c_b c_a = 2\delta_{ab}\,1$ for all labels $a, b$. -/
theorem majorana_car {n : ℕ} (a b : MajoranaIndex n) :
    (majorana a)ᴴ = majorana a ∧
    majorana a * majorana b + majorana b * majorana a =
      (if a = b then (2 : ℂ) else 0) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) :=
  ⟨majorana_conjTranspose a, majorana_anticommute a b⟩

open scoped ComplexOrder in
/-- Density matrices and the covariance of a state: $\rho$ is a density matrix exactly when it
is positive semidefinite with $\mathrm{Tr}\,\rho = 1$; the covariance entry is
$\Gamma(\rho)_{ab} = \mathrm{Re}\,\tfrac i2 \mathrm{Tr}(\rho\,(c_a c_b - c_b c_a))$; and for
Hermitian $\rho$ the number $\tfrac i2 \mathrm{Tr}(\rho\,(c_a c_b - c_b c_a))$ is real, equal to
$\Gamma(\rho)_{ab}$. -/
theorem state_covariance {n : ℕ} (ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
    (a b : MajoranaIndex n) :
    (IsDensity ρ ↔ ρ.PosSemidef ∧ ρ.trace = 1) ∧
    covariance ρ a b =
      ((Complex.I / 2) * (ρ * (majorana a * majorana b - majorana b * majorana a)).trace).re ∧
    (ρ.IsHermitian → (Complex.I / 2) *
      (ρ * (majorana a * majorana b - majorana b * majorana a)).trace =
        (covariance ρ a b : ℂ)) :=
  ⟨Iff.rfl, rfl, fun h => (coe_covariance h a b).symm⟩

/-- The covariance of every matrix $\rho$ is antisymmetric, and for labels $a \ne b$ its entry
is $\Gamma(\rho)_{ab} = \mathrm{Re}\,(i\,\mathrm{Tr}(\rho\, c_a c_b))$. The covariance of a
density matrix is admissible. -/
theorem covariance_of_density {n : ℕ} (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (covariance ρ)ᵀ = -covariance ρ ∧
    (∀ a b : MajoranaIndex n, a ≠ b →
      covariance ρ a b = (Complex.I * (ρ * (majorana a * majorana b)).trace).re) ∧
    (IsDensity ρ → IsAdmissible (covariance ρ)) :=
  ⟨covariance_transpose ρ, fun _ _ h => covariance_of_ne ρ h,
    fun h => h.isAdmissible_covariance⟩

/-- Occupation-number states. For a configuration $s$ the state $|s\rangle\langle s|$ is the
matrix with the single nonzero entry $1$ at $(s, s)$. It is a density matrix, its covariance is
$\begin{pmatrix} 0 & D_s \\ -D_s & 0 \end{pmatrix}$ with $D_s$ diagonal, $(D_s)_{jj} = -1$ if
$s_j = 0$ and $+1$ if $s_j = 1$, and this covariance is pure. In particular the vacuum
$|0\cdots0\rangle$ has covariance $\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
theorem occupation_state {n : ℕ} (s : FockIndex n) :
    occupation s = Matrix.single s s 1 ∧ IsDensity (occupation s) ∧
    covariance (occupation s) =
      Matrix.fromBlocks 0 (Matrix.diagonal fun j => if s j = 0 then -1 else 1)
        (-(Matrix.diagonal fun j => if s j = 0 then -1 else 1)) 0 ∧
    IsPure (covariance (occupation s)) ∧
    covariance (occupation (fun _ : Fin n => (0 : Fin 2))) = Matrix.fromBlocks 0 (-1) 1 0 := by
  refine ⟨rfl, isDensity_occupation s, covariance_occupation s,
    isPure_covariance_occupation s, ?_⟩
  rw [covariance_vacuum, standardCovariance, Matrix.fromBlocks_neg]
  simp

/-- The bond state. Let $\psi = (|00\rangle + i\,|11\rangle)/\sqrt 2$ on two modes, that is
$\psi_{00} = 1/\sqrt 2$, $\psi_{11} = i/\sqrt 2$ and $\psi_{01} = \psi_{10} = 0$. Then
$|\psi\rangle\langle\psi|$ is a density matrix, and its covariance has the nonzero entries
$\Gamma_{x_0 x_1} = -\Gamma_{x_1 x_0} = 1$ and $\Gamma_{y_0 y_1} = -\Gamma_{y_1 y_0} = -1$. -/
theorem bond_state (ψ : FockIndex 2 → ℂ)
    (hψ : ∀ s, ψ s = if s = (fun _ => 0) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
      else if s = (fun _ => 1) then Complex.I * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0) :
    IsDensity (Matrix.vecMulVec ψ (star ψ)) ∧
    covariance (Matrix.vecMulVec ψ (star ψ)) =
      Matrix.fromBlocks !![0, 1; -1, 0] 0 0 !![0, -1; 1, 0] := by
  have e : ψ = bondVec := funext fun s => by rw [hψ s]; rfl
  subst e
  refine ⟨isDensity_bondState, ?_⟩
  change covariance bondState = _
  rw [covariance_bondState]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [bond, pairing, bondLabel, Matrix.fromBlocks]

/-- Conjugation by an implementing unitary. Let $U$ be a unitary on Fock space implementing a
real matrix $O$. Then $O$ is orthogonal, $O O^T = 1$, and for every density matrix $\rho$ the
matrix $U \rho U^*$ is a density matrix with covariance $O^T \Gamma(\rho)\, O$. -/
theorem unitary_conjugation {n : ℕ} {U : Matrix (FockIndex n) (FockIndex n) ℂ}
    {O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (hO : ∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) :
    O * Oᵀ = 1 ∧ ∀ ρ, IsDensity ρ →
      IsDensity (U * ρ * Uᴴ) ∧ covariance (U * ρ * Uᴴ) = Oᵀ * covariance ρ * O :=
  ⟨orthogonal_of_conjugatesMajorana hU' hO, fun _ hρ => covariance_conj hU hU' hO hρ⟩

/-- Hopping gates. For modes $j \ne k$ and $\varphi \in \mathbb R$ let
$U = (\cos\varphi + \sin\varphi\, c_{x_j} c_{x_k})(\cos\varphi + \sin\varphi\, c_{y_j} c_{y_k})$.
Then $U$ is unitary; with $\theta = 2\varphi$ it acts on the Majorana operators by
$U c_{x_j} U^* = \cos\theta\, c_{x_j} - \sin\theta\, c_{x_k}$,
$U c_{x_k} U^* = \sin\theta\, c_{x_j} + \cos\theta\, c_{x_k}$, the same formulas with $y$ in
place of $x$, and $U c_a U^* = c_a$ for the labels $a$ of every other mode. On two modes, with
$j = 0$ and $k = 1$, the state $U |10\rangle\langle 10| U^*$ (mode $0$ occupied) has covariance
$\begin{pmatrix} 0 & X \\ -X^T & 0 \end{pmatrix}$ with
$X = \begin{pmatrix} \cos 4\varphi & -\sin 4\varphi \\ -\sin 4\varphi & -\cos 4\varphi
\end{pmatrix}$. -/
theorem hopping_gate {n : ℕ} (φ : ℝ) {j k : Fin n} (hjk : j ≠ k)
    (U : Matrix (FockIndex n) (FockIndex n) ℂ)
    (hU : U = ((Real.cos φ : ℂ) • 1 + (Real.sin φ : ℂ) • (majorana (Sum.inl j) *
      majorana (Sum.inl k))) * ((Real.cos φ : ℂ) • 1 + (Real.sin φ : ℂ) •
        (majorana (Sum.inr j) * majorana (Sum.inr k)))) :
    U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
    (∀ x : Fin n → MajoranaIndex n, (x = Sum.inl ∨ x = Sum.inr) →
      U * majorana (x j) * Uᴴ = (Real.cos (2 * φ) : ℂ) • majorana (x j) -
        (Real.sin (2 * φ) : ℂ) • majorana (x k) ∧
      U * majorana (x k) * Uᴴ = (Real.sin (2 * φ) : ℂ) • majorana (x j) +
        (Real.cos (2 * φ) : ℂ) • majorana (x k) ∧
      ∀ l, l ≠ j → l ≠ k → U * majorana (x l) * Uᴴ = majorana (x l)) ∧
    ∀ V : Matrix (FockIndex 2) (FockIndex 2) ℂ,
      V = ((Real.cos φ : ℂ) • 1 + (Real.sin φ : ℂ) • (majorana (Sum.inl 0) *
        majorana (Sum.inl 1))) * ((Real.cos φ : ℂ) • 1 + (Real.sin φ : ℂ) •
          (majorana (Sum.inr 0) * majorana (Sum.inr 1))) →
      covariance (V * Matrix.single ![1, 0] ![1, 0] 1 * Vᴴ) =
        Matrix.fromBlocks 0 !![Real.cos (4 * φ), -Real.sin (4 * φ);
          -Real.sin (4 * φ), -Real.cos (4 * φ)]
          (-!![Real.cos (4 * φ), -Real.sin (4 * φ); -Real.sin (4 * φ), -Real.cos (4 * φ)]ᵀ)
          0 := by
  have hU0 : U = hoppingGate φ j k := hU
  subst hU0
  refine ⟨hoppingGate_mul_conjTranspose hjk, conjTranspose_mul_hoppingGate hjk, ?_, ?_⟩
  · rintro x (rfl | rfl)
    all_goals
      refine ⟨?_, ?_, fun l hlj hlk => ?_⟩
      · rw [hoppingGate_conj hjk, sum_hoppingRotation_smul]
        simp only [planeRotation, ite_true]
        rw [sum_rowTwo_smul hjk]; push_cast; module
      · rw [hoppingGate_conj hjk, sum_hoppingRotation_smul]
        simp only [planeRotation, Ne.symm hjk, ite_true, ite_false]
        rw [sum_rowTwo_smul hjk]
      · rw [hoppingGate_conj hjk, sum_hoppingRotation_smul]
        simp only [planeRotation, hlj, hlk, ite_false]
        rw [sum_rowOne_smul]
  · intro V hV
    have hV0 : V = hoppingGate φ (0 : Fin 2) 1 := hV
    subst hV0
    have e : (![1, 0] : FockIndex 2) = occ10 := by
      funext i; fin_cases i <;> rfl
    rw [e]
    exact covariance_gate_occ10 φ

/-! ## Quadratic Hamiltonians and ground states

For a real matrix $h$ on the Majorana labels of $n$ modes the quadratic Hamiltonian is
$H_h = \tfrac i4 \sum_{a,b} h_{ab}\, c_a c_b$, and the energy of a matrix $\rho$ is
$E_h(\rho) = \mathrm{Re}\,\mathrm{Tr}(\rho H_h)$. On real matrices $\Gamma$ on the labels the
energy form is $\tfrac14 \sum_{a,b} h_{ab}\Gamma_{ab}$. A normal form of $h$ is a factorization
$h = O D(\varepsilon) O^T$ with $O$ real orthogonal and $\varepsilon \in \mathbb R^n$. -/

/-- Quadratic Hamiltonians. For every real $h$, $H_h = \sum_{a,b} \tfrac i4 h_{ab}\, c_a c_b$ and
$E_h(\rho) = \mathrm{Re}\,\mathrm{Tr}(\rho H_h)$. If $h^T = -h$, then $H_h$ is Hermitian; for
Hermitian $\rho$ the trace $\mathrm{Tr}(\rho H_h)$ is real and equals
$\tfrac14\sum_{a,b} h_{ab}\Gamma(\rho)_{ab}$; and the generator identity
$i\,[H_h, c_a] = \sum_b h_{ab} c_b$ holds. For every $h$, a unitary $U$ implementing a real
matrix $O$ satisfies $U H_h U^* = H_{O^T h O}$. -/
theorem quadratic_hamiltonian {n : ℕ} (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    quadHam h = ∑ a, ∑ b, (Complex.I / 4 * (h a b : ℂ)) • (majorana a * majorana b) ∧
    (∀ ρ, energy h ρ = (ρ * quadHam h).trace.re) ∧
    (hᵀ = -h →
      (quadHam h)ᴴ = quadHam h ∧
      (∀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, ρ.IsHermitian →
        (ρ * quadHam h).trace = ((1 / 4 * ∑ a, ∑ b, h a b * covariance ρ a b : ℝ) : ℂ)) ∧
      (∀ a, Complex.I • (quadHam h * majorana a - majorana a * quadHam h) =
        ∑ b, (h a b : ℂ) • majorana b)) ∧
    ∀ (U : Matrix (FockIndex n) (FockIndex n) ℂ)
      (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ), U * Uᴴ = 1 → Uᴴ * U = 1 →
      (∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) →
      U * quadHam h * Uᴴ = quadHam (Oᵀ * h * O) :=
  ⟨rfl, fun _ => rfl,
    fun hh => ⟨quadHam_conjTranspose hh, fun _ hρ => trace_mul_quadHam hh hρ,
      I_smul_commutator_quadHam hh⟩,
    fun _ _ _ hU' hO => conj_quadHam hU' hO⟩

/-- The Hamiltonian of $D(\varepsilon)$ is diagonal in the occupation basis:
$\langle s|H_{D(\varepsilon)}|s\rangle = \sum_j \varepsilon_j (s_j - \tfrac12)$ for every
configuration $s$, and all off-diagonal entries vanish. -/
theorem block_hamiltonian {n : ℕ} (ε : Fin n → ℝ) :
    quadHam (Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0) =
      Matrix.diagonal fun s : FockIndex n => ((∑ j, ε j * ((s j : ℕ) - 1 / 2) : ℝ) : ℂ) :=
  quadHam_blockForm ε

/-- Ground states in a normal form. Let $h = O D(\varepsilon) O^T$ with $O$ orthogonal, let $U$
be a unitary implementing $O$, let $s^\varepsilon$ be the configuration with
$s^\varepsilon_j = 1$ exactly when $\varepsilon_j < 0$, let
$\rho_0 = U^* |s^\varepsilon\rangle\langle s^\varepsilon| U$ and
$E_0 = -\tfrac12\sum_j|\varepsilon_j|$. Then $E_h(\rho) \ge E_0$ for every density matrix
$\rho$; $\rho_0$ is a density matrix with $E_h(\rho_0) = E_0$; its covariance is
$O D(\eta) O^T$ with $\eta_j = 1$ if $\varepsilon_j < 0$ and $\eta_j = -1$ otherwise, and is
pure. If moreover every $\varepsilon_j \ne 0$, then $\rho_0$ is the only density matrix with
energy $E_0$, the energy form satisfies $\tfrac14\sum_{a,b} h_{ab}\Gamma_{ab} \ge E_0$ for
admissible $\Gamma$, and for admissible $\Gamma$ equality holds exactly when
$\Gamma = \Gamma(\rho_0)$. -/
theorem normal_form_ground {n : ℕ} {h O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} {U : Matrix (FockIndex n) (FockIndex n) ℂ} (hO : O * Oᵀ = 1)
    (hOε : h = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (hUO : ∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b)
    (s₀ : FockIndex n) (hs₀ : ∀ j, s₀ j = if ε j < 0 then 1 else 0) :
    (∀ ρ, IsDensity ρ → -(1 / 2) * ∑ j, |ε j| ≤ energy h ρ) ∧
    IsDensity (Uᴴ * occupation s₀ * U) ∧
    energy h (Uᴴ * occupation s₀ * U) = -(1 / 2) * ∑ j, |ε j| ∧
    covariance (Uᴴ * occupation s₀ * U) =
      O * Matrix.fromBlocks 0 (Matrix.diagonal fun j => if ε j < 0 then 1 else -1)
        (-(Matrix.diagonal fun j => if ε j < 0 then 1 else -1)) 0 * Oᵀ ∧
    IsPure (covariance (Uᴴ * occupation s₀ * U)) ∧
    ((∀ j, ε j ≠ 0) →
      (∀ ρ, IsDensity ρ → energy h ρ = -(1 / 2) * ∑ j, |ε j| →
        ρ = Uᴴ * occupation s₀ * U) ∧
      (∀ Γ, IsAdmissible Γ → -(1 / 2) * ∑ j, |ε j| ≤ 1 / 4 * ∑ a, ∑ b, h a b * Γ a b) ∧
      (∀ Γ, IsAdmissible Γ → (1 / 4 * ∑ a, ∑ b, h a b * Γ a b = -(1 / 2) * ∑ j, |ε j| ↔
        Γ = covariance (Uᴴ * occupation s₀ * U)))) := by
  have e : s₀ = groundConfig ε := funext hs₀
  subst e
  obtain ⟨h1, h2, h3, h4, h5⟩ := groundState_of_normalForm hO hOε hU hU' hUO
  have e2 : (fun j => if ε j < 0 then (1 : ℝ) else -1) = fun j => -sgn' (ε j) := by
    funext j; unfold sgn'; split_ifs <;> norm_num
  rw [e2]
  exact ⟨h1, h2, h3, h4, h5, fun hε => groundState_unique_of_normalForm hO hOε hU hU' hUO hε⟩

/-- Every quadratic Hamiltonian has a pure ground state. For every real $h$ with $h^T = -h$
there are a special orthogonal $O$ ($O O^T = 1$, $\det O = 1$), a vector $\varepsilon$ with
$h = O D(\varepsilon) O^T$, and a unitary $U$ implementing $O$; and there is a density matrix
$\rho_0$ with pure covariance and $E_h(\rho_0) \le E_h(\rho)$ for every density matrix
$\rho$. -/
theorem ground_state_exists {n : ℕ} (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : hᵀ = -h) :
    (∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ)
      (U : Matrix (FockIndex n) (FockIndex n) ℂ),
      O * Oᵀ = 1 ∧ O.det = 1 ∧
      h = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ ∧
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ ∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) ∧
    ∃ ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ, IsDensity ρ₀ ∧ IsPure (covariance ρ₀) ∧
      ∀ ρ, IsDensity ρ → energy h ρ₀ ≤ energy h ρ :=
  ⟨exists_normalForm_unitary h hh, exists_groundState h hh⟩

/-! ## Realization

A real matrix $\Gamma$ on the labels is realized by a density matrix $\rho$ when
$\Gamma(\rho) = \Gamma$. For $\lambda \in \mathbb R^n$ the product mixture is
$\rho_\lambda = \sum_s \prod_j p_j(s_j)\, |s\rangle\langle s|$ with
$p_j(0) = (1 - \lambda_j)/2$ and $p_j(1) = (1 + \lambda_j)/2$. -/

/-- Implementing unitaries exist: for every real matrix $O$ on the labels with $O O^T = 1$ and
$\det O = 1$ there is a unitary $U$ on Fock space implementing $O$. -/
theorem special_orthogonal_unitary {n : ℕ} (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hO : O * Oᵀ = 1) (hdet : O.det = 1) :
    ∃ U : Matrix (FockIndex n) (FockIndex n) ℂ, U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      ∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b :=
  exists_unitary_conjugatesMajorana O hO hdet

/-- Product mixtures. For every $\lambda \in \mathbb R^n$,
$\rho_\lambda = \sum_s \prod_j p_j(s_j)\,|s\rangle\langle s|$ has covariance $D(\lambda)$; if
every $|\lambda_j| \le 1$ it is a density matrix; and if every $|\lambda_j| = 1$ it is the
occupation state $|s\rangle\langle s|$ with $s_j = 1$ exactly when $\lambda_j = 1$. -/
theorem product_mixture {n : ℕ} (lam : Fin n → ℝ) :
    productMixture lam = ∑ s : FockIndex n,
      ((∏ j, (if s j = 0 then (1 - lam j) / 2 else (1 + lam j) / 2) : ℝ) : ℂ) •
        Matrix.single s s 1 ∧
    covariance (productMixture lam) =
      Matrix.fromBlocks 0 (Matrix.diagonal lam) (-(Matrix.diagonal lam)) 0 ∧
    ((∀ j, |lam j| ≤ 1) → IsDensity (productMixture lam)) ∧
    ((∀ j, |lam j| = 1) → productMixture lam =
      Matrix.single (fun j => if lam j = 1 then 1 else 0) (fun j => if lam j = 1 then 1 else 0)
        1) :=
  ⟨rfl, covariance_productMixture lam, isDensity_productMixture, productMixture_of_abs_eq_one⟩

/-- Realization of covariances. If $\Gamma = O D(\varepsilon) O^T$ is admissible, $O$ is
orthogonal and $U$ is a unitary implementing $O$, then $U^* \rho_\varepsilon U$ is a density
matrix with covariance $\Gamma$. Every admissible $\Gamma$ is the covariance of a density
matrix. Every pure $\Gamma$ is the covariance of a density matrix
$U^*|s\rangle\langle s|U$ with $U$ unitary and $s$ a configuration. Two density matrices with
the same pure covariance $\Gamma$ are equal. -/
theorem covariance_realization {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) :
    (∀ (U : Matrix (FockIndex n) (FockIndex n) ℂ)
      (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      U * Uᴴ = 1 → Uᴴ * U = 1 → (∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) →
      O * Oᵀ = 1 →
      Γ = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ →
      IsAdmissible Γ →
      IsDensity (Uᴴ * productMixture ε * U) ∧ covariance (Uᴴ * productMixture ε * U) = Γ) ∧
    (IsAdmissible Γ → ∃ ρ : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsDensity ρ ∧ covariance ρ = Γ) ∧
    (IsPure Γ → ∃ (U : Matrix (FockIndex n) (FockIndex n) ℂ) (s : FockIndex n),
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ IsDensity (Uᴴ * occupation s * U) ∧
      covariance (Uᴴ * occupation s * U) = Γ) ∧
    (IsPure Γ → ∀ ρ σ : Matrix (FockIndex n) (FockIndex n) ℂ, IsDensity ρ → IsDensity σ →
      covariance ρ = Γ → covariance σ = Γ → ρ = σ) :=
  ⟨fun _ _ _ hU hU' hUO hO hΓ hadm => isDensity_realization_and_covariance hU hU' hUO hO hΓ hadm,
    exists_isDensity_covariance_eq Γ, exists_pure_state_of_isPure Γ,
    fun hp _ _ hρ hσ h1 h2 => eq_of_covariance_eq_of_isPure hρ hσ (h1 ▸ hp) (h1.trans h2.symm)⟩

/-! ## Thermal states and evolution

$e^X$ is the exponential of a square matrix $X$. For a real matrix $h$ on the labels the
exponential state is $\rho_h = e^{-H_h} / \mathrm{Tr}\, e^{-H_h}$, the thermal state at inverse
temperature $\beta \in \mathbb R$ is $\rho_{\beta h}$, and the evolution operator is
$U_h(t) = e^{-itH_h}$ for $t \in \mathbb R$. A real matrix $\Gamma$ on the labels is strictly
admissible when $\Gamma^T = -\Gamma$ and $1 - \Gamma^T\Gamma$ is positive definite. -/

/-- The exponential and thermal states: $\rho_h = (\mathrm{Tr}\,e^{-H_h})^{-1} e^{-H_h}$, and the
thermal state of $H_h$ at inverse temperature $\beta$ is $\rho_{\beta h}$. -/
theorem exponential_state_def {n : ℕ} (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (β : ℝ) :
    gaussianState h = ((NormedSpace.exp (-quadHam h)).trace)⁻¹ • NormedSpace.exp (-quadHam h) ∧
    thermalState β h = gaussianState (β • h) :=
  ⟨rfl, rfl⟩

/-- Strict admissibility: $\Gamma$ is strictly admissible exactly when $\Gamma^T = -\Gamma$ and
$1 - \Gamma^T\Gamma$ is positive definite; a strictly admissible matrix is admissible; and
$D(\lambda)$ is strictly admissible exactly when every $|\lambda_j| < 1$. -/
theorem strictly_admissible {n : ℕ} (Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (lam : Fin n → ℝ) :
    (IsStrictlyAdmissible Γ ↔ Γᵀ = -Γ ∧ (1 - Γᵀ * Γ).PosDef) ∧
    (IsStrictlyAdmissible Γ → IsAdmissible Γ) ∧
    (IsStrictlyAdmissible (Matrix.fromBlocks 0 (Matrix.diagonal lam) (-(Matrix.diagonal lam)) 0)
      ↔ ∀ j, |lam j| < 1) :=
  ⟨Iff.rfl, IsStrictlyAdmissible.isAdmissible, isStrictlyAdmissible_blockForm_iff lam⟩

/-- Exponential states. Let $h^T = -h$. Then $\mathrm{Tr}\,e^{-H_h}$ is a positive real number
and $\rho_h$ is a density matrix. There are a special orthogonal $O$ and a vector
$\varepsilon$ with $h = O D(\varepsilon) O^T$ and
$\Gamma(\rho_h) = O D(-\tanh(\varepsilon/2)) O^T$, the hyperbolic tangent taken entrywise. The
covariance $\Gamma(\rho_h)$ is strictly admissible, and for $n \ge 1$ it is not pure. -/
theorem exponential_state {n : ℕ} (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : hᵀ = -h) :
    (∃ z : ℝ, 0 < z ∧ (NormedSpace.exp (-quadHam h)).trace = z) ∧
    IsDensity (gaussianState h) ∧
    (∃ (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
      O * Oᵀ = 1 ∧ O.det = 1 ∧
      h = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ ∧
      covariance (gaussianState h) = O * Matrix.fromBlocks 0
        (Matrix.diagonal fun j => -Real.tanh (ε j / 2))
        (-(Matrix.diagonal fun j => -Real.tanh (ε j / 2))) 0 * Oᵀ) ∧
    IsStrictlyAdmissible (covariance (gaussianState h)) ∧
    (0 < n → ¬ IsPure (covariance (gaussianState h))) :=
  ⟨exists_partitionFunction_eq h hh, isDensity_gaussianState h hh,
    exists_covariance_gaussianState h hh, isStrictlyAdmissible_covariance_gaussianState h hh,
    fun hn => not_isPure_covariance_gaussianState hn h hh⟩

/-- Thermal states in a normal form. Let $h = O D(\varepsilon) O^T$ with $O$ orthogonal and let
$U$ be a unitary implementing $O$. Then
$\mathrm{Tr}\,e^{-H_h} = \prod_j 2\cosh(\varepsilon_j/2)$, and for every $\beta \in \mathbb R$
the thermal state $\rho_{\beta h}$ is a density matrix with covariance
$O D(-\tanh(\beta\varepsilon/2)) O^T$ and energy
$E_h(\rho_{\beta h}) = -\tfrac12\sum_j \varepsilon_j \tanh(\beta\varepsilon_j/2)$. -/
theorem thermal_state {n : ℕ} {h O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    {ε : Fin n → ℝ} {U : Matrix (FockIndex n) (FockIndex n) ℂ} (hO : O * Oᵀ = 1)
    (hOε : h = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (hUO : ∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) (β : ℝ) :
    (NormedSpace.exp (-quadHam h)).trace = ((∏ j, 2 * Real.cosh (ε j / 2) : ℝ) : ℂ) ∧
    IsDensity (thermalState β h) ∧
    covariance (thermalState β h) = O * Matrix.fromBlocks 0
      (Matrix.diagonal fun j => -Real.tanh (β * ε j / 2))
      (-(Matrix.diagonal fun j => -Real.tanh (β * ε j / 2))) 0 * Oᵀ ∧
    energy h (thermalState β h) = -(1 / 2 * ∑ j, ε j * Real.tanh (β * ε j / 2)) := by
  subst hOε
  exact ⟨partitionFunction_conj hU hU' hUO hO, isDensity_thermalState hU hU' hUO hO β,
    covariance_thermalState hU hU' hUO hO β, energy_thermalState hU hU' hUO hO β⟩

/-- Realization by exponential states. Every strictly admissible $\Gamma$ is the covariance of
an exponential state $\rho_h$ with $h^T = -h$. Two exponential states $\rho_h, \rho_{h'}$
($h^T = -h$, $h'^T = -h'$) with the same covariance are equal. If $O$ is orthogonal, $U$ is a
unitary implementing $O$ and every $|\eta_j| < 1$, then $h = O D(-2\,\mathrm{artanh}\,\eta) O^T$
has $\Gamma(\rho_h) = O D(\eta) O^T$. The exponential state of $h = 0$ is the maximally mixed
state $2^{-n}\,1$, with covariance $0$. -/
theorem exponential_realization {n : ℕ} :
    (∀ Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ, IsStrictlyAdmissible Γ →
      ∃ h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ,
        hᵀ = -h ∧ covariance (gaussianState h) = Γ) ∧
    (∀ h h' : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ, hᵀ = -h → h'ᵀ = -h' →
      covariance (gaussianState h) = covariance (gaussianState h') →
        gaussianState h = gaussianState h') ∧
    (∀ (U : Matrix (FockIndex n) (FockIndex n) ℂ)
      (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (η : Fin n → ℝ),
      U * Uᴴ = 1 → Uᴴ * U = 1 → (∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) →
      O * Oᵀ = 1 → (∀ j, |η j| < 1) →
      covariance (gaussianState (O * Matrix.fromBlocks 0
        (Matrix.diagonal fun j => -(2 * Real.artanh (η j)))
        (-(Matrix.diagonal fun j => -(2 * Real.artanh (η j)))) 0 * Oᵀ)) =
        O * Matrix.fromBlocks 0 (Matrix.diagonal η) (-(Matrix.diagonal η)) 0 * Oᵀ) ∧
    gaussianState (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) = ((2 : ℂ) ^ n)⁻¹ • 1 ∧
    covariance (gaussianState (0 : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)) = 0 :=
  ⟨exists_gaussianState_covariance_eq,
    fun _ _ hh hh' hc => gaussianState_eq_of_covariance_eq hh hh' hc,
    fun _ _ _ hU hU' hUO hO hη => covariance_gaussianState_artanh hU hU' hUO hO hη,
    gaussianState_zero, covariance_gaussianState_zero⟩

/-- Time evolution. Let $h^T = -h$ and $s, t \in \mathbb R$. Then
$U_h(t) = e^{-itH_h}$ is unitary, $U_h(t)^* = U_h(-t)$ and $U_h(s) U_h(t) = U_h(s + t)$;
$U_h(t)$ implements the real matrix $e^{-th}$, that is
$U_h(t) c_a U_h(t)^* = \sum_b (e^{-th})_{ab} c_b$; for every density matrix $\sigma$ the matrix
$U_h(t)\sigma U_h(t)^*$ is a density matrix with covariance $e^{th}\,\Gamma(\sigma)\,e^{-th}$; and
the exponential state is stationary, $U_h(t) \rho_h U_h(t)^* = \rho_h$. -/
theorem time_evolution {n : ℕ} (h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ)
    (hh : hᵀ = -h) (s t : ℝ) :
    evolution h t = NormedSpace.exp ((-(Complex.I * t)) • quadHam h) ∧
    evolution h t * (evolution h t)ᴴ = 1 ∧ (evolution h t)ᴴ = evolution h (-t) ∧
    evolution h s * evolution h t = evolution h (s + t) ∧
    (∀ a, evolution h t * majorana a * (evolution h t)ᴴ =
      ∑ b, (NormedSpace.exp (-(t • h)) a b : ℂ) • majorana b) ∧
    (∀ σ, IsDensity σ → IsDensity (evolution h t * σ * (evolution h t)ᴴ) ∧
      covariance (evolution h t * σ * (evolution h t)ᴴ) =
        NormedSpace.exp (t • h) * covariance σ * NormedSpace.exp (-(t • h))) ∧
    evolution h t * gaussianState h * (evolution h t)ᴴ = gaussianState h :=
  ⟨rfl, evolution_mul_conjTranspose hh t, evolution_conjTranspose hh t, evolution_add s t,
    conjugatesMajorana_evolution hh t, fun _ hσ => covariance_evolution hh t hσ,
    evolution_conj_gaussianState hh t⟩

/-! ## Wick's theorem and the Gaussian class

For a complex vector $v$ on the labels, $v \cdot c = \sum_a v_a c_a$, and
$v^T G w = \sum_{a,b} v_a G_{ab} w_b$ (no complex conjugation). The two-point matrix of $\rho$ is
the complex matrix $G(\rho) = 1 - i\,\Gamma(\rho)$. Lists $(w_0, \dots, w_{k-1})$ of vectors are
indexed from $0$, and a hat marks an omitted factor. A Gaussian state is a density matrix whose
moments obey Wick's rule in the recursive form of the first entry below. -/

/-- The Gaussian class. A matrix $\rho$ is Gaussian exactly when it is a density matrix and,
with $G = G(\rho)$, for every vector $v$ and every list $(w_0, \dots, w_{k-1})$,
$\mathrm{Tr}(\rho\,(v\cdot c)(w_0\cdot c)\cdots(w_{k-1}\cdot c)) = \sum_{j<k} (-1)^j\,
(v^T G w_j)\, \mathrm{Tr}(\rho\,(w_0\cdot c)\cdots\widehat{(w_j\cdot c)}\cdots
(w_{k-1}\cdot c))$. -/
theorem gaussian_iff {n : ℕ} (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    IsGaussian ρ ↔ IsDensity ρ ∧ ∀ (v : MajoranaIndex n → ℂ) (l : List (MajoranaIndex n → ℂ)),
      (ρ * ((v :: l).map fun w => ∑ a, w a • majorana a).prod).trace =
        ∑ j : Fin l.length, (-1) ^ (j : ℕ) *
          (v ⬝ᵥ (1 - Complex.I • (covariance ρ).map (fun x : ℝ => (x : ℂ))) *ᵥ l[(j : ℕ)]) *
          (ρ * ((l.eraseIdx j).map fun w => ∑ a, w a • majorana a).prod).trace := by
  constructor
  · intro hG
    refine ⟨hG.1, fun v l => ?_⟩
    change momentList ρ (v :: l) = ∑ j : Fin l.length, _ * momentList ρ (l.eraseIdx j)
    rw [hG.2, wick_cons]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG.2]
    rfl
  · rintro ⟨hd, hrec⟩
    refine ⟨hd, ?_⟩
    suffices H : ∀ k (l : List (MajoranaIndex n → ℂ)), l.length = k →
        momentList ρ l = wick (twoPoint ρ) l from fun l => H _ l rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro l hl
      cases l with
      | nil => exact momentList_nil hd
      | cons v l =>
        change (ρ * ((v :: l).map lincomb).prod).trace = _
        rw [show (ρ * ((v :: l).map lincomb).prod).trace = _ from hrec v l, wick_cons]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hlen : (l.eraseIdx j).length < k := by
          have := List.length_eraseIdx_le l j
          simp only [List.length_cons] at hl
          omega
        rw [← ih _ hlen (l.eraseIdx j) rfl]
        rfl

/-- Order two. For complex vectors $v, w$ on the labels,
$(v\cdot c)(w\cdot c) + (w\cdot c)(v\cdot c) = 2\,(v^T w)\,1$, and every density matrix $\rho$
satisfies $\mathrm{Tr}(\rho\,(v\cdot c)(w\cdot c)) = v^T G(\rho)\, w$. -/
theorem two_point_moment {n : ℕ} (v w : MajoranaIndex n → ℂ) :
    (∑ a, v a • majorana a) * (∑ a, w a • majorana a) +
      (∑ a, w a • majorana a) * (∑ a, v a • majorana a) =
      (2 * (v ⬝ᵥ w)) • (1 : Matrix (FockIndex n) (FockIndex n) ℂ) ∧
    ∀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, IsDensity ρ →
      (ρ * ((∑ a, v a • majorana a) * (∑ a, w a • majorana a))).trace =
        v ⬝ᵥ (1 - Complex.I • (covariance ρ).map (fun x : ℝ => (x : ℂ))) *ᵥ w :=
  ⟨lincomb_anticommute v w, fun _ hρ => trace_mul_lincomb_mul_lincomb hρ v w⟩

/-- The relation form of the Gaussian class. A matrix $\rho$ is Gaussian exactly when it is a
density matrix, $\mathrm{Tr}(\rho\,(w_0\cdot c)\cdots(w_{k-1}\cdot c)) = 0$ for every list of odd
length $k$, and, with $G = G(\rho)$, $((G^T v)\cdot c)\,\rho = \rho\,((G v)\cdot c)$ for every
vector $v$. -/
theorem gaussian_relation {n : ℕ} (ρ : Matrix (FockIndex n) (FockIndex n) ℂ) :
    IsGaussian ρ ↔ IsDensity ρ ∧
      (∀ l : List (MajoranaIndex n → ℂ), Odd l.length →
        (ρ * (l.map fun w => ∑ a, w a • majorana a).prod).trace = 0) ∧
      ∀ v : MajoranaIndex n → ℂ,
        (∑ a, ((1 - Complex.I • (covariance ρ).map (fun x : ℝ => (x : ℂ)))ᵀ *ᵥ v) a •
          majorana a) * ρ =
        ρ * ∑ a, ((1 - Complex.I • (covariance ρ).map (fun x : ℝ => (x : ℂ))) *ᵥ v) a •
          majorana a := by
  constructor
  · intro hG
    exact ⟨hG.1, fun l hl => (hG.2 l).trans (wick_odd l hl), hG.relation⟩
  · rintro ⟨hd, hodd, hrel⟩
    exact isGaussian_of_relation hd hodd hrel

/-- Examples of Gaussian states: the product mixtures $\rho_\lambda$ with every
$|\lambda_j| \le 1$; the occupation states $|s\rangle\langle s|$; for $h^T = -h$ the exponential
state $\rho_h$ and every thermal state $\rho_{\beta h}$, $\beta \in \mathbb R$. If $U$ is a
unitary implementing a real matrix $O$ and $\rho$ is Gaussian, then $U^* \rho U$ is Gaussian. -/
theorem gaussian_examples {n : ℕ} :
    (∀ lam : Fin n → ℝ, (∀ j, |lam j| ≤ 1) → IsGaussian (productMixture lam)) ∧
    (∀ s : FockIndex n, IsGaussian (occupation s)) ∧
    (∀ h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ, hᵀ = -h →
      IsGaussian (gaussianState h) ∧ ∀ β : ℝ, IsGaussian (thermalState β h)) ∧
    ∀ (U ρ : Matrix (FockIndex n) (FockIndex n) ℂ)
      (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ), U * Uᴴ = 1 → Uᴴ * U = 1 →
      (∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) →
      IsGaussian ρ → IsGaussian (Uᴴ * ρ * U) :=
  ⟨fun _ h => isGaussian_productMixture h, isGaussian_occupation,
    fun h hh => ⟨isGaussian_gaussianState h hh, fun β => isGaussian_thermalState β h hh⟩,
    fun _ _ _ hU hU' hO hρ => isGaussian_conj hU hU' hO hρ⟩

/-- Gaussian states and their covariances. Every admissible $\Gamma$ is the covariance of a
Gaussian state, and two Gaussian states with the same covariance are equal. Every Gaussian
state $\rho$ has the form $\rho = U^* \rho_\varepsilon U$ with $U$ a unitary implementing an
orthogonal $O$, every $|\varepsilon_j| \le 1$ and $\Gamma(\rho) = O D(\varepsilon) O^T$. A
Gaussian state with strictly admissible covariance is an exponential state $\rho_h$ with
$h^T = -h$. -/
theorem gaussian_covariance {n : ℕ} :
    (∀ Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ, IsAdmissible Γ →
      ∃ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, IsGaussian ρ ∧ covariance ρ = Γ) ∧
    (∀ ρ σ : Matrix (FockIndex n) (FockIndex n) ℂ, IsGaussian ρ → IsGaussian σ →
      covariance ρ = covariance σ → ρ = σ) ∧
    (∀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, IsGaussian ρ →
      ∃ (U : Matrix (FockIndex n) (FockIndex n) ℂ)
        (O : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ) (ε : Fin n → ℝ),
        U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ (∀ a, U * majorana a * Uᴴ = ∑ b, (O a b : ℂ) • majorana b) ∧
        O * Oᵀ = 1 ∧ (∀ j, |ε j| ≤ 1) ∧
        covariance ρ = O * Matrix.fromBlocks 0 (Matrix.diagonal ε) (-(Matrix.diagonal ε)) 0 * Oᵀ ∧
        ρ = Uᴴ * productMixture ε * U) ∧
    (∀ ρ : Matrix (FockIndex n) (FockIndex n) ℂ, IsGaussian ρ →
      IsStrictlyAdmissible (covariance ρ) →
      ∃ h : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ, hᵀ = -h ∧ ρ = gaussianState h) :=
  ⟨exists_isGaussian_covariance_eq, fun _ _ hρ hσ h => hρ.eq_of_covariance_eq hσ h,
    fun _ hρ => hρ.exists_realization_eq,
    fun _ hρ hΓ => hρ.exists_gaussianState_eq_of_isStrictlyAdmissible hΓ⟩

/-- The Majorana monomials. For a set $S$ of labels, $c_S$ is the product of the $c_a$,
$a \in S$, in the order $x_0 < \dots < x_{n-1} < y_0 < \dots < y_{n-1}$ (so $c_\emptyset = 1$).
For all sets $S, T$ of labels, $\mathrm{Tr}(c_S^* c_T) = 2^n$ if $S = T$ and $0$ otherwise; the
monomials, indexed by the sets of labels, are linearly independent over $\mathbb C$; every
complex matrix $A$ on Fock space equals $2^{-n}\sum_S \mathrm{Tr}(A c_S^*)\, c_S$; and two
matrices $A, B$ with $\mathrm{Tr}(A c_S) = \mathrm{Tr}(B c_S)$ for every $S$ are equal. -/
theorem majorana_monomials {n : ℕ} (S T : Finset (MajoranaIndex n))
    (A B : Matrix (FockIndex n) (FockIndex n) ℂ) :
    monomial S = ((((List.finRange (n + n)).map finSumFinEquiv.symm).filter
      fun a => decide (a ∈ S)).map majorana).prod ∧
    ((monomial S)ᴴ * monomial T).trace = (if S = T then (2 : ℂ) ^ n else 0) ∧
    LinearIndependent ℂ
      (monomial : Finset (MajoranaIndex n) → Matrix (FockIndex n) (FockIndex n) ℂ) ∧
    A = ((2 : ℂ) ^ n)⁻¹ • ∑ R, (A * (monomial R)ᴴ).trace • monomial R ∧
    ((∀ R, (A * monomial R).trace = (B * monomial R).trace) → A = B) :=
  ⟨rfl, trace_conjTranspose_monomial_mul_monomial S T, linearIndependent_monomial,
    eq_sum_trace_mul_conjTranspose_monomial_smul A, eq_of_trace_mul_monomial_eq⟩

/-! ## Partial trace and contraction of Gaussian states, the chain state

A configuration of $n + m$ modes is written $(s, u)$, with $s \in \{0,1\}^n$ its first $n$ bits
(the retained modes) and $u \in \{0,1\}^m$ its last $m$ bits (the eliminated modes). The
retained Majorana labels are $x_j, y_j$ for $j < n$ and the eliminated ones $x_{n+j}, y_{n+j}$
for $j < m$; for a real matrix $\Gamma$ on the labels of $n + m$ modes, $A$, $B$, $C$, $D$ are
its retained–retained, retained–eliminated, eliminated–retained and eliminated–eliminated
blocks, each with the $x$-labels before the $y$-labels. $\mathrm{Tr}_E$ and $\mathrm{Tr}_R$ are
the partial traces over the eliminated and over the retained modes, and $X \otimes Y$ is the
tensor product of a matrix $X$ on $n$ modes with a matrix $Y$ on $m$ modes. The contraction of a
matrix $\rho$ on $n + m$ modes with a matrix $\sigma$ on $m$ modes has normalization
$Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma))$ and is the matrix
$Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))$ on $n$ modes. -/

/-- The partial traces and the tensor product: for matrices $M$ on $n + m$ modes, $X$ on $n$
modes and $Y$ on $m$ modes and for all configurations,
$\mathrm{Tr}_E(M)_{st} = \sum_w M_{(s,w),(t,w)}$,
$\mathrm{Tr}_R(M)_{uv} = \sum_w M_{(w,u),(w,v)}$ and
$(X \otimes Y)_{(s,u),(t,v)} = X_{st}\,Y_{uv}$. -/
theorem partial_trace {n m : ℕ} (M : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
    (X : Matrix (FockIndex n) (FockIndex n) ℂ) (Y : Matrix (FockIndex m) (FockIndex m) ℂ)
    (s t : FockIndex n) (u v : FockIndex m) :
    ptraceE M s t = ∑ w : FockIndex m, M (Fin.append s w) (Fin.append t w) ∧
    ptraceR M u v = ∑ w : FockIndex n, M (Fin.append w u) (Fin.append w v) ∧
    tensor X Y (Fin.append s u) (Fin.append t v) = X s t * Y u v := by
  have key : ∀ (s : FockIndex n) (u : FockIndex m),
      (fockSplit n m).symm (s, u) = Fin.append s u := by
    intro s u
    funext i
    induction i using Fin.addCases with
    | left j => rw [fockSplit_symm_apply_castAdd, Fin.append_left]
    | right j => rw [fockSplit_symm_apply_natAdd, Fin.append_right]
  refine ⟨?_, ?_, ?_⟩
  · rw [ptraceE_apply]; simp only [key]
  · rw [ptraceR_apply]; simp only [key]
  · rw [← key, ← key, tensor_apply_symm]

/-- Marginals. For every matrix $\rho$ on $n + m$ modes, the covariance of $\mathrm{Tr}_E\rho$ is
the retained block $A$ of $\Gamma(\rho)$ and the covariance of $\mathrm{Tr}_R\rho$ is the
eliminated block $D$. If $\rho$ is a density matrix, so are both marginals; if $\rho$ is
Gaussian, so are both marginals. -/
theorem gaussian_marginal {n m : ℕ} (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ) :
    (IsDensity ρ → IsDensity (ptraceE ρ) ∧ IsDensity (ptraceR ρ)) ∧
    covariance (ptraceE ρ) = (covariance ρ).submatrix (Sum.map (Fin.castAdd m) (Fin.castAdd m))
      (Sum.map (Fin.castAdd m) (Fin.castAdd m)) ∧
    covariance (ptraceR ρ) = (covariance ρ).submatrix (Sum.map (Fin.natAdd n) (Fin.natAdd n))
      (Sum.map (Fin.natAdd n) (Fin.natAdd n)) ∧
    (IsGaussian ρ → IsGaussian (ptraceE ρ) ∧ IsGaussian (ptraceR ρ)) := by
  have eR : (embedR : MajoranaIndex n → MajoranaIndex (n + m)) =
      Sum.map (Fin.castAdd m) (Fin.castAdd m) := by
    funext a; rcases a with j | j <;> simp
  have eE : (embedE : MajoranaIndex m → MajoranaIndex (n + m)) =
      Sum.map (Fin.natAdd n) (Fin.natAdd n) := by
    funext a; rcases a with j | j <;> simp
  refine ⟨fun h => ⟨isDensity_ptraceE ρ h, isDensity_ptraceR ρ h⟩, ?_, ?_,
    fun h => ⟨isGaussian_ptraceE h, isGaussian_ptraceR h⟩⟩
  · rw [covariance_ptraceE, eR]
  · rw [covariance_ptraceR, eE]

open scoped ComplexOrder in
/-- Contraction of Gaussian states. For positive semidefinite $\rho$ on $n + m$ modes and
$\sigma$ on $m$ modes with $Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma)) \ne 0$, the contraction
$Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))$ is a density matrix. Let $\rho$ and $\sigma$
be Gaussian, with $A, B, C, D$ the blocks of $\Gamma(\rho)$ and $\beta = \Gamma(\sigma)$, and
let $1 - D\beta$ be invertible. Then $Z$ is a positive real number, the contraction is Gaussian,
and its covariance is $A + B\beta(1 - D\beta)^{-1}C$. -/
theorem gaussian_contraction {n m : ℕ} :
    (∀ (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
      (σ : Matrix (FockIndex m) (FockIndex m) ℂ), ρ.PosSemidef → σ.PosSemidef →
      (ρ * tensor 1 σ).trace ≠ 0 →
      IsDensity ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ))) ∧
    ∀ (ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ)
      (σ : Matrix (FockIndex m) (FockIndex m) ℂ), IsGaussian ρ → IsGaussian σ →
      IsUnit (1 - (covariance ρ).submatrix (Sum.map (Fin.natAdd n) (Fin.natAdd n))
        (Sum.map (Fin.natAdd n) (Fin.natAdd n)) * covariance σ).det →
      (∃ z : ℝ, 0 < z ∧ (ρ * tensor 1 σ).trace = (z : ℂ)) ∧
      IsGaussian ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) ∧
      covariance ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) =
        (covariance ρ).submatrix (Sum.map (Fin.castAdd m) (Fin.castAdd m))
          (Sum.map (Fin.castAdd m) (Fin.castAdd m)) +
        (covariance ρ).submatrix (Sum.map (Fin.castAdd m) (Fin.castAdd m))
          (Sum.map (Fin.natAdd n) (Fin.natAdd n)) * covariance σ *
        (1 - (covariance ρ).submatrix (Sum.map (Fin.natAdd n) (Fin.natAdd n))
          (Sum.map (Fin.natAdd n) (Fin.natAdd n)) * covariance σ)⁻¹ *
        (covariance ρ).submatrix (Sum.map (Fin.natAdd n) (Fin.natAdd n))
          (Sum.map (Fin.castAdd m) (Fin.castAdd m)) := by
  have eR : (embedR : MajoranaIndex n → MajoranaIndex (n + m)) =
      Sum.map (Fin.castAdd m) (Fin.castAdd m) := by
    funext a; rcases a with j | j <;> simp
  have eE : (embedE : MajoranaIndex m → MajoranaIndex (n + m)) =
      Sum.map (Fin.natAdd n) (Fin.natAdd n) := by
    funext a; rcases a with j | j <;> simp
  refine ⟨fun ρ σ hρ hσ hZ => isDensity_contractState hρ hσ hZ, fun ρ σ hρ hσ hinv => ?_⟩
  have hinv' : IsUnit (1 - blockE (covariance ρ) * covariance σ).det := by
    rw [blockE, eE]; exact hinv
  obtain ⟨hG, hcov⟩ := isGaussian_contractState' hρ hσ hinv'
  have hpos := Complex.pos_iff.mp (normalization_pos hρ hσ hinv')
  unfold normalization at hpos
  refine ⟨⟨(ρ * tensor 1 σ).trace.re, hpos.1, Complex.ext rfl (by simp [← hpos.2])⟩, hG, ?_⟩
  change covariance (contractState ρ σ) = _
  rw [hcov, contractCov, blockR, blockRE, blockER, blockE, eR, eE]

/-- The chain state. Let $\Gamma_0, \dots, \Gamma_{N-1}$ be admissible covariances of single
sites with $P$ physical and $2M$ virtual modes, let $\Gamma_{\mathrm{in}}$, $\beta_N$ and
$\Gamma_N$ be the periodic input, bond and periodic covariances of the chain built from them
(defined in the first part), and let the invertibility condition of the contraction of
$\Gamma_{\mathrm{in}}$ with $\beta_N$ (also defined there) hold. Number the modes of the chain as
follows: physical mode $c$ of site $i$ is mode $iP + c$; the $N M$ virtual modes $L$ follow,
$(i, a)$ being mode $NP + iM + a$; then the $N M$ virtual modes $L'$, $(i, b)$ being mode
$NP + NM + iM + b$. On the $2NM$ virtual modes alone, $L$ is numbered $(i, a) \mapsto iM + a$
and $L'$ is numbered $(i, b) \mapsto NM + iM + b$. Then there are Gaussian states $\rho$ on all
$NP + 2NM$ modes and $\sigma$ on the $2NM$ virtual modes whose covariances, read in this
numbering, are $\Gamma_{\mathrm{in}}$ and $\beta_N$. For any such $\rho$ and $\sigma$, the
normalization $Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma))$ is a positive real number, the
contraction $\tau = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))$ on the $NP$ physical modes is
Gaussian, its covariance, read in the numbering $iP + c$, is $\Gamma_N$, and if every
$\Gamma_i$ is pure then $\tau^2 = \tau$. -/
theorem chain_state {N M P : ℕ} (Γ : Fin N → Matrix (SiteLabel M P) (SiteLabel M P) ℝ)
    (hΓ : ∀ i, Admissible (Γ i))
    (hinv : ContractInvertible (periodicInput Γ) (periodicBond N M))
    (E : Retained N P ⊕ Eliminated N M → MajoranaIndex (N * P + (N * M + N * M)))
    (hE : E = Sum.elim
      (Sum.map (fun p => Fin.castAdd (N * M + N * M) (finProdFinEquiv p))
        (fun p => Fin.castAdd (N * M + N * M) (finProdFinEquiv p)))
      (Sum.map
        (Sum.elim (fun q => Fin.natAdd (N * P) (Fin.castAdd (N * M) (finProdFinEquiv q)))
          (fun q => Fin.natAdd (N * P) (Fin.natAdd (N * M) (finProdFinEquiv q))))
        (Sum.elim (fun q => Fin.natAdd (N * P) (Fin.castAdd (N * M) (finProdFinEquiv q)))
          (fun q => Fin.natAdd (N * P) (Fin.natAdd (N * M) (finProdFinEquiv q))))))
    (F : Eliminated N M → MajoranaIndex (N * M + N * M))
    (hF : F = Sum.map
      (Sum.elim (fun q => Fin.castAdd (N * M) (finProdFinEquiv q))
        (fun q => Fin.natAdd (N * M) (finProdFinEquiv q)))
      (Sum.elim (fun q => Fin.castAdd (N * M) (finProdFinEquiv q))
        (fun q => Fin.natAdd (N * M) (finProdFinEquiv q)))) :
    (∃ (ρ : Matrix (FockIndex (N * P + (N * M + N * M))) (FockIndex (N * P + (N * M + N * M))) ℂ)
      (σ : Matrix (FockIndex (N * M + N * M)) (FockIndex (N * M + N * M)) ℂ),
      IsGaussian ρ ∧ IsGaussian σ ∧ (covariance ρ).submatrix E E = periodicInput Γ ∧
      (covariance σ).submatrix F F = periodicBond N M) ∧
    ∀ (ρ : Matrix (FockIndex (N * P + (N * M + N * M))) (FockIndex (N * P + (N * M + N * M))) ℂ)
      (σ : Matrix (FockIndex (N * M + N * M)) (FockIndex (N * M + N * M)) ℂ),
      IsGaussian ρ → IsGaussian σ → (covariance ρ).submatrix E E = periodicInput Γ →
      (covariance σ).submatrix F F = periodicBond N M →
      (∃ z : ℝ, 0 < z ∧ (ρ * tensor 1 σ).trace = (z : ℂ)) ∧
      IsGaussian ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) ∧
      (covariance ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ))).submatrix
        (Sum.map finProdFinEquiv finProdFinEquiv) (Sum.map finProdFinEquiv finProdFinEquiv) =
        periodicCovariance Γ ∧
      ((∀ i, Pure (Γ i)) →
        ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) *
          ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) =
          (ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) := by
  have hE' : E = ⇑(chainLabelEquiv N M P) := by
    subst hE
    funext x
    rcases x with ((p | p) | ((q | q) | (q | q))) <;>
      simp [chainLabelEquiv, retainedModeEquiv, siteModeEquiv, eliminatedModeEquiv,
        virtualModeEquiv, Equiv.eq_symm_apply]
  have hF' : F = ⇑(eliminatedModeEquiv N M) := by
    subst hF
    funext x
    rcases x with ((q | q) | (q | q)) <;>
      simp [eliminatedModeEquiv, virtualModeEquiv, siteModeEquiv]
  have hρin : ∀ ρ : Matrix (FockIndex (N * P + (N * M + N * M)))
      (FockIndex (N * P + (N * M + N * M))) ℂ,
      (covariance ρ).submatrix E E = periodicInput Γ → covariance ρ = inputCov N M P Γ := by
    intro ρ h
    rw [inputCov, ← h, hE']
    ext a b
    simp
  have hσb : ∀ σ : Matrix (FockIndex (N * M + N * M)) (FockIndex (N * M + N * M)) ℂ,
      (covariance σ).submatrix F F = periodicBond N M → covariance σ = bondCov N M := by
    intro σ h
    rw [bondCov, ← h, hF']
    ext a b
    simp
  refine ⟨⟨inputState Γ hΓ, bondStateN N M, isGaussian_inputState Γ hΓ, isGaussian_bondStateN,
    ?_, ?_⟩, fun ρ σ hρ hσ hρE hσF => ?_⟩
  · rw [covariance_inputState, inputCov, hE']
    ext a b
    simp
  · rw [covariance_bondStateN, bondCov, hF']
    ext a b
    simp
  have e1 : ρ = inputState Γ hΓ := hρ.eq_of_covariance_eq (isGaussian_inputState Γ hΓ)
    (by rw [hρin ρ hρE, covariance_inputState])
  have e2 : σ = bondStateN N M := hσ.eq_of_covariance_eq isGaussian_bondStateN
    (by rw [hσb σ hσF, covariance_bondStateN])
  subst e1 e2
  have hpos := Complex.pos_iff.mp (normalization_chain_pos Γ hΓ hinv)
  unfold normalization at hpos
  refine ⟨⟨_, hpos.1, Complex.ext rfl (by simp [← hpos.2])⟩,
    isGaussian_chainState Γ hΓ hinv, ?_,
    fun hpure => chainState_mul_self_of_forall_pure Γ hΓ hpure hinv⟩
  change (covariance (chainState Γ hΓ)).submatrix _ _ = _
  rw [covariance_chainState Γ hΓ hinv]
  ext a b
  simp [retainedModeEquiv, siteModeEquiv]

/-! ## Purity and the Kitaev ground state

For a pure $\Gamma$ on the labels of $n$ modes, $H_{-\Gamma}$ is the quadratic Hamiltonian of
$-\Gamma$. The Kitaev chain has $N$ sites with one mode each; mode $i$ has the labels $x_i, y_i$,
and $i + 1$ is taken modulo $N$. The Kitaev covariance $K$ is the real matrix on these labels
with $K_{y_i x_{i+1}} = 1$, $K_{x_{i+1} y_i} = -1$ and all other entries $0$. -/

/-- Gaussian projections: a Gaussian state $\rho$ satisfies $\rho^2 = \rho$ exactly when its
covariance is pure, and then $\rho = |\psi\rangle\langle\psi|$ for a vector $\psi$. -/
theorem gaussian_projection {n : ℕ} {ρ : Matrix (FockIndex n) (FockIndex n) ℂ}
    (hρ : IsGaussian ρ) :
    (ρ * ρ = ρ ↔ IsPure (covariance ρ)) ∧
    (IsPure (covariance ρ) → ∃ ψ : FockIndex n → ℂ, ρ = Matrix.vecMulVec ψ (star ψ)) :=
  ⟨hρ.mul_self_iff_isPure, hρ.exists_vecMulVec_eq_of_isPure⟩

/-- Contraction of pure Gaussian states. Let $\rho$ on $n + m$ modes and $\sigma$ on $m$ modes
be Gaussian with pure covariances, and let $1 - D\beta$ be invertible, with $D$ the eliminated
block of $\Gamma(\rho)$ and $\beta = \Gamma(\sigma)$. Then the contraction
$\tau = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))$ satisfies $\tau^2 = \tau$ and its
covariance is pure. -/
theorem pure_contracted_state {n m : ℕ}
    {ρ : Matrix (FockIndex (n + m)) (FockIndex (n + m)) ℂ}
    {σ : Matrix (FockIndex m) (FockIndex m) ℂ} (hρ : IsGaussian ρ) (hσ : IsGaussian σ)
    (hρp : IsPure (covariance ρ)) (hσp : IsPure (covariance σ))
    (hinv : IsUnit (1 - (covariance ρ).submatrix (Sum.map (Fin.natAdd n) (Fin.natAdd n))
      (Sum.map (Fin.natAdd n) (Fin.natAdd n)) * covariance σ).det) :
    ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) *
      ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ)) =
      (ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ) ∧
    IsPure (covariance ((ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ))) := by
  have eE : (embedE : MajoranaIndex m → MajoranaIndex (n + m)) =
      Sum.map (Fin.natAdd n) (Fin.natAdd n) := by
    funext a; rcases a with j | j <;> simp
  have hinv' : IsUnit (1 - blockE (covariance ρ) * covariance σ).det := by
    rw [blockE, eE]; exact hinv
  refine ⟨contractState_mul_self_of_isPure hρ hσ hρp hσp hinv', ?_⟩
  change IsPure (covariance (contractState ρ σ))
  rw [covariance_contractState hρ hσ hinv' (normalization_ne_zero hρ hσ hinv')]
  exact isPure_contractCov_of_isPure hρp hσp hinv'

/-- Ground states of pure covariances. For every pure $\Gamma$ on the labels of $n$ modes there
is a Gaussian state $\rho_0$ with covariance $\Gamma$ such that $E_{-\Gamma}(\rho_0) = -n/2$,
$E_{-\Gamma}(\rho) \ge -n/2$ for every density matrix $\rho$, and every density matrix with
$E_{-\Gamma}(\rho) = -n/2$ equals $\rho_0$; on covariances,
$-\tfrac14\sum_{a,b}\Gamma_{ab}\Gamma'_{ab} \ge -n/2$ for every admissible $\Gamma'$, with
equality exactly when $\Gamma' = \Gamma$. -/
theorem pure_ground_state {n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ}
    (hΓ : IsPure Γ) :
    ∃ ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsGaussian ρ₀ ∧ covariance ρ₀ = Γ ∧ energy (-Γ) ρ₀ = -((n : ℝ) / 2) ∧
      (∀ ρ, IsDensity ρ → -((n : ℝ) / 2) ≤ energy (-Γ) ρ) ∧
      (∀ ρ, IsDensity ρ → energy (-Γ) ρ = -((n : ℝ) / 2) → ρ = ρ₀) ∧
      (∀ Γ', IsAdmissible Γ' → -((n : ℝ) / 2) ≤ 1 / 4 * ∑ a, ∑ b, (-Γ) a b * Γ' a b) ∧
      (∀ Γ', IsAdmissible Γ' →
        (1 / 4 * ∑ a, ∑ b, (-Γ) a b * Γ' a b = -((n : ℝ) / 2) ↔ Γ' = Γ)) :=
  groundState_of_isPure hΓ

/-- The Kitaev covariance and Hamiltonian. On the labels of the $N$ modes of the Kitaev chain,
for all $i, j$: $K_{x_i x_j} = K_{y_i y_j} = 0$, $K_{y_i x_j} = 1$ if $j = i + 1$ and $0$
otherwise, and $K_{x_j y_i} = -1$ if $j = i + 1$ and $0$ otherwise. The matrix $K$ is pure, and
$H_{-K} = \tfrac i2 \sum_i c_{x_{i+1}} c_{y_i}$. -/
theorem kitaev_hamiltonian (N : ℕ) :
    (∀ i j : Fin N,
      kitaevCov N (Sum.inl (finProdFinEquiv (i, 0))) (Sum.inl (finProdFinEquiv (j, 0))) = 0 ∧
      kitaevCov N (Sum.inr (finProdFinEquiv (i, 0))) (Sum.inr (finProdFinEquiv (j, 0))) = 0 ∧
      kitaevCov N (Sum.inr (finProdFinEquiv (i, 0))) (Sum.inl (finProdFinEquiv (j, 0))) =
        (if j = finRotate N i then 1 else 0) ∧
      kitaevCov N (Sum.inl (finProdFinEquiv (j, 0))) (Sum.inr (finProdFinEquiv (i, 0))) =
        (if j = finRotate N i then -1 else 0)) ∧
    IsPure (kitaevCov N) ∧
    quadHam (-(kitaevCov N)) = ∑ i : Fin N, (Complex.I / 2) •
      (majorana (Sum.inl (finProdFinEquiv (finRotate N i, 0))) *
        majorana (Sum.inr (finProdFinEquiv (i, 0)))) := by
  refine ⟨fun i j => ?_, isPure_kitaevCov, kitaevHam_eq⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [kitaevCov, kitaevChain, retainedModeEquiv, siteModeEquiv]

/-- The Kitaev ground state as a chain state. Let $N \ge 1$, and take the chain of $N$ sites
with $P = 1$ physical and $2M = 2$ virtual modes per site, every site carrying the Kitaev local
covariance (defined in the first part), with the numbering of the modes of the chain-state
entry. Then there are Gaussian states $\rho$ and $\sigma$ whose covariances, in this numbering,
are the periodic input and bond covariances. For any such $\rho$ and $\sigma$ the contraction
$\rho_K = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))$ is Gaussian with covariance $K$,
satisfies $\rho_K^2 = \rho_K$, has energy $E_{-K}(\rho_K) = -N/2$, and is the unique ground
state of $H_{-K}$: $E_{-K}(\rho') \ge -N/2$ for every density matrix $\rho'$, and every density
matrix with $E_{-K}(\rho') = -N/2$ equals $\rho_K$. -/
theorem kitaev_ground_state {N : ℕ} [NeZero N]
    (E : Retained N 1 ⊕ Eliminated N 1 → MajoranaIndex (N * 1 + (N * 1 + N * 1)))
    (hE : E = Sum.elim
      (Sum.map (fun p => Fin.castAdd (N * 1 + N * 1) (finProdFinEquiv p))
        (fun p => Fin.castAdd (N * 1 + N * 1) (finProdFinEquiv p)))
      (Sum.map
        (Sum.elim (fun q => Fin.natAdd (N * 1) (Fin.castAdd (N * 1) (finProdFinEquiv q)))
          (fun q => Fin.natAdd (N * 1) (Fin.natAdd (N * 1) (finProdFinEquiv q))))
        (Sum.elim (fun q => Fin.natAdd (N * 1) (Fin.castAdd (N * 1) (finProdFinEquiv q)))
          (fun q => Fin.natAdd (N * 1) (Fin.natAdd (N * 1) (finProdFinEquiv q))))))
    (F : Eliminated N 1 → MajoranaIndex (N * 1 + N * 1))
    (hF : F = Sum.map
      (Sum.elim (fun q => Fin.castAdd (N * 1) (finProdFinEquiv q))
        (fun q => Fin.natAdd (N * 1) (finProdFinEquiv q)))
      (Sum.elim (fun q => Fin.castAdd (N * 1) (finProdFinEquiv q))
        (fun q => Fin.natAdd (N * 1) (finProdFinEquiv q)))) :
    (∃ (ρ : Matrix (FockIndex (N * 1 + (N * 1 + N * 1))) (FockIndex (N * 1 + (N * 1 + N * 1))) ℂ)
      (σ : Matrix (FockIndex (N * 1 + N * 1)) (FockIndex (N * 1 + N * 1)) ℂ),
      IsGaussian ρ ∧ IsGaussian σ ∧
      (covariance ρ).submatrix E E = periodicInput (fun _ : Fin N => kitaevLocal) ∧
      (covariance σ).submatrix F F = periodicBond N 1) ∧
    ∀ (ρ : Matrix (FockIndex (N * 1 + (N * 1 + N * 1))) (FockIndex (N * 1 + (N * 1 + N * 1))) ℂ)
      (σ : Matrix (FockIndex (N * 1 + N * 1)) (FockIndex (N * 1 + N * 1)) ℂ),
      IsGaussian ρ → IsGaussian σ →
      (covariance ρ).submatrix E E = periodicInput (fun _ : Fin N => kitaevLocal) →
      (covariance σ).submatrix F F = periodicBond N 1 →
      ∀ ρK, ρK = (ρ * tensor 1 σ).trace⁻¹ • ptraceE (ρ * tensor 1 σ) →
        IsGaussian ρK ∧ covariance ρK = kitaevCov N ∧ ρK * ρK = ρK ∧
        energy (-(kitaevCov N)) ρK = -((N : ℝ) / 2) ∧
        (∀ ρ', IsDensity ρ' → -((N : ℝ) / 2) ≤ energy (-(kitaevCov N)) ρ') ∧
        (∀ ρ', IsDensity ρ' → energy (-(kitaevCov N)) ρ' = -((N : ℝ) / 2) → ρ' = ρK) := by
  have hE' : E = ⇑(chainLabelEquiv N 1 1) := by
    subst hE
    funext x
    rcases x with ((p | p) | ((q | q) | (q | q))) <;>
      simp [chainLabelEquiv, retainedModeEquiv, siteModeEquiv, eliminatedModeEquiv,
        virtualModeEquiv, Equiv.eq_symm_apply]
  have hF' : F = ⇑(eliminatedModeEquiv N 1) := by
    subst hF
    funext x
    rcases x with ((q | q) | (q | q)) <;>
      simp [eliminatedModeEquiv, virtualModeEquiv, siteModeEquiv]
  have hΓ : ∀ _ : Fin N, Admissible kitaevLocal := fun _ => admissible_kitaevLocal
  refine ⟨⟨inputState (fun _ : Fin N => kitaevLocal) hΓ, bondStateN N 1,
    isGaussian_inputState _ hΓ, isGaussian_bondStateN, ?_, ?_⟩,
    fun ρ σ hρ hσ hρE hσF ρK hK => ?_⟩
  · rw [covariance_inputState, inputCov, hE']
    ext a b
    simp
  · rw [covariance_bondStateN, bondCov, hF']
    ext a b
    simp
  have e1 : ρ = inputState (fun _ : Fin N => kitaevLocal) hΓ :=
    hρ.eq_of_covariance_eq (isGaussian_inputState _ hΓ) (by
      rw [covariance_inputState, inputCov, ← hρE, hE']
      ext a b
      simp)
  have e2 : σ = bondStateN N 1 := hσ.eq_of_covariance_eq isGaussian_bondStateN (by
    rw [covariance_bondStateN, bondCov, ← hσF, hF']
    ext a b
    simp)
  subst e1 e2
  have hK' : ρK = kitaevState N := hK
  subst hK'
  have hN : -(((N * 1 : ℕ) : ℝ) / 2) = -((N : ℝ) / 2) := by simp
  refine ⟨isGaussian_kitaevState, covariance_kitaevState, kitaevState_mul_self,
    energy_kitaevState', fun ρ' hρ' => ?_, fun ρ' hρ' h => ?_⟩
  · rw [← hN]; exact energy_kitaevHam_ge hρ'
  · exact eq_kitaevState_of_energy_eq hρ' (by rw [h, hN])

/-! ## The gap

For a pure $\Gamma$ the Hamiltonian $H_{-\Gamma}$ has ground energy $-n/2$ and a unique ground
state (previous section). The statements below bound the energy of density matrices orthogonal
to the ground state, orthogonality of $\rho$ and $\rho_0$ meaning
$\mathrm{Tr}(\rho\,\rho_0) = 0$. -/

/-- The gap of $H_{-\Gamma}$. Let $\Gamma$ be pure and let $\rho_0$ be a Gaussian state with
covariance $\Gamma$. Every density matrix $\rho$ with $\mathrm{Tr}(\rho\,\rho_0) = 0$ has
$E_{-\Gamma}(\rho) \ge -n/2 + 1$, and for $n \ge 1$ some density matrix $\rho'$ with
$\mathrm{Tr}(\rho'\rho_0) = 0$ has $E_{-\Gamma}(\rho') = -n/2 + 1$. -/
theorem pure_gap {n : ℕ} {Γ : Matrix (MajoranaIndex n) (MajoranaIndex n) ℝ} (hΓ : IsPure Γ)
    {ρ₀ : Matrix (FockIndex n) (FockIndex n) ℂ} (hρ₀ : IsGaussian ρ₀)
    (hcov : covariance ρ₀ = Γ) :
    (∀ ρ, IsDensity ρ → (ρ * ρ₀).trace = 0 → -((n : ℝ) / 2) + 1 ≤ energy (-Γ) ρ) ∧
    (0 < n → ∃ ρ' : Matrix (FockIndex n) (FockIndex n) ℂ,
      IsDensity ρ' ∧ (ρ' * ρ₀).trace = 0 ∧ energy (-Γ) ρ' = -((n : ℝ) / 2) + 1) :=
  ⟨fun _ hρ h => energy_neg_ge_of_trace_mul_eq_zero hΓ hρ₀ hcov hρ h,
    fun hn => exists_trace_mul_eq_zero_and_energy_neg_eq hΓ hρ₀ hcov hn⟩

/-- The gap of the Kitaev chain. Let $N \ge 1$ and let $\rho_K$ be a density matrix on the $N$
modes of the Kitaev chain with $E_{-K}(\rho_K) = -N/2$. Every density matrix $\rho$ with
$\mathrm{Tr}(\rho\,\rho_K) = 0$ has $E_{-K}(\rho) \ge -N/2 + 1$, and some density matrix
$\rho'$ with $\mathrm{Tr}(\rho'\rho_K) = 0$ has $E_{-K}(\rho') = -N/2 + 1$. -/
theorem kitaev_gap {N : ℕ} [NeZero N] {ρK : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ}
    (hK : IsDensity ρK) (hE : energy (-(kitaevCov N)) ρK = -((N : ℝ) / 2)) :
    (∀ ρ, IsDensity ρ → (ρ * ρK).trace = 0 →
      -((N : ℝ) / 2) + 1 ≤ energy (-(kitaevCov N)) ρ) ∧
    ∃ ρ' : Matrix (FockIndex (N * 1)) (FockIndex (N * 1)) ℂ,
      IsDensity ρ' ∧ (ρ' * ρK).trace = 0 ∧ energy (-(kitaevCov N)) ρ' = -((N : ℝ) / 2) + 1 := by
  have e : ρK = kitaevState N := eq_kitaevState_of_energy_eq hK (by rw [hE]; simp)
  subst e
  exact ⟨fun _ hρ h => energy_kitaevHam_ge_of_trace_mul_eq_zero hρ h,
    exists_trace_mul_kitaevState_eq_zero_and_energy_eq⟩

end Sealed
