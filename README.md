# FermionicLean

Fermionic Gaussian states of finitely many modes, formalized in Lean 4 over Mathlib, with Gaussian
fermionic matrix product states (Gaussian fMPS) as the first application.

A system of `n` fermionic modes carries `2n` Majorana operators `c_a`, Hermitian and satisfying
`c_a c_b + c_b c_a = 2δ_ab`. A state `ρ` has the **Majorana covariance**
`Γ_ab = Re (i/2) Tr(ρ [c_a, c_b])`, a real antisymmetric `2n × 2n` matrix, and the matrices that
arise in this way are exactly the **admissible** ones, `Γᵀ = −Γ` with `1 − ΓᵀΓ ⪰ 0`; pure
covariances have `Γ² = −1`. A Gaussian fMPS joins Gaussian on-site states through maximally
entangled pairs of virtual modes; on covariances this is the contraction
`Γ ⋆ β = A + Bβ(1 − Dβ)⁻¹C` of `Γ = [[A, B], [C, D]]` with the bond covariance `β`, which eliminates
the virtual labels.

The library proves that the contraction preserves admissibility and purity, builds the covariance
of a periodic chain and splits it in momentum space, constructs the Majorana operators as explicit
matrices on the `2^n`-dimensional Fock space, realizes every admissible matrix by a Gaussian state,
proves Wick's theorem in the recursive form that defines the Gaussian class, and shows that the
contraction of Gaussian states is Gaussian with covariance `Γ ⋆ β`, so that the periodic chain is a
Gaussian state on Fock space. For pure on-site states that state is pure; for the Kitaev chain it
is the unique ground state of the Kitaev Hamiltonian, with gap 1; and the correlations across a
cut have rank at most `2M` times the number of cut bonds.

## What is proved

| | Main results | Notes |
|---|---|---|
| Covariance matrices | For antisymmetric `Γ`, admissibility, defined as `Γᵀ = −Γ` with `1 − ΓᵀΓ ⪰ 0`, is equivalent to `‖Γv‖ ≤ ‖v‖` for every real `v` and to `1 + iΓ ⪰ 0`; pure matrices are orthogonal and admissible; both properties are preserved by orthogonal congruence and relabelling, admissibility passes to subsets of modes, and an independent sum is admissible (pure) exactly when its summands are; one mode, and the pure covariances `±Ω_n` | §1 |
| Contraction and the bond | The contraction of antisymmetric (admissible) matrices is antisymmetric (admissible) when `1 − Dβ` is invertible, and pure for pure inputs; for pure `β` the condition is `det(D + β) ≠ 0` and, for antisymmetric `Γ`, the contraction is the Schur form `A + B(D + β)⁻¹Bᵀ`; the bond is pure, and contracting two bonds through a bond gives the bond | §2 |
| Periodic chains | The chain covariance `Γ_N = Γ_in ⋆ β_N` of `N` sites with `M` virtual pairs and `P` physical modes per site is admissible for admissible on-site covariances and pure for pure ones when `det(1 − Dβ_N) ≠ 0`; a three-site example evaluated exactly, with pure on-site covariances, `det(1 − Dβ_3) = (304/125)²` and a circulant output | §3 |
| Momentum space | For a homogeneous chain `det(1 − Dβ_N) = ∏_k det(1 − D_k β_M)` over the `N` momenta; under the contraction condition the Fourier transform diagonalizes the chain covariance into `2P × 2P` blocks `Σ(k)`, from which it is reconstructed; `Σ(−k) = Σ(k)‾` always, and `Σ(k)* = −Σ(k)` and `1 − Σ(k)*Σ(k) ⪰ 0` for an admissible on-site covariance under that condition | §4 |
| Normal form and rotations | Every real antisymmetric matrix is `O D(ε) Oᵀ` with `O` orthogonal (or special orthogonal); it is admissible exactly when every `\|ε_j\| ≤ 1` and pure exactly when every `\|ε_j\| = 1`; the exponential of `D(θ)` in closed form; the special orthogonal matrices are the finite products of plane rotations | §1, §7 |
| Fock space | The Jordan–Wigner Majorana operators, Hermitian and satisfying the anticommutation relations; the covariance of every density matrix is antisymmetric and admissible; occupation states, with the vacuum at `−Ω_n`; the bond state `(\|00⟩ + i\|11⟩)/√2` of two modes, whose covariance is the one-pair bond; a unitary `U` with `U c_a U* = Σ_b O_ab c_b` makes `O` orthogonal and gives `Γ(UρU*) = OᵀΓ(ρ)O`; hopping gates | §5, §6 |
| Quadratic Hamiltonians and realization | For `H_h = (i/4) Σ h_ab c_a c_b` with antisymmetric `h` and Hermitian `ρ`, the energy is `(1/4) Σ h_ab Γ_ab`; every special orthogonal matrix is implemented by a unitary; every quadratic Hamiltonian has a pure ground state, with energy `−½ Σ \|ε_j\|` and unique when no `ε_j` vanishes; every admissible matrix is the covariance of a density matrix, every pure one of a pure state, and two density matrices with the same pure covariance are equal | §7 |
| Thermal states and evolution | `e^{−H_h}/Tr e^{−H_h}` is a density matrix with covariance `O D(−tanh(ε/2)) Oᵀ`, strictly admissible and, for `n ≥ 1`, not pure; the thermal states, their partition function and energy; every strictly admissible matrix is the covariance of exactly one exponential state `ρ_h` with `hᵀ = −h`; `e^{−itH_h}` is a unitary group acting on covariances by `Γ ↦ e^{th} Γ e^{−th}`, under which the exponential state is stationary | §8 |
| Wick's theorem and the Gaussian class | A density matrix is Gaussian when its moments obey Wick's rule in recursive form with respect to its own two-point matrix `G = 1 − iΓ`, equivalently when `(Gᵀv·c)ρ = ρ(Gv·c)` for every `v` and its odd moments vanish; product mixtures, occupation, exponential and thermal states are Gaussian; the Majorana monomials are linearly independent; every admissible matrix is the covariance of exactly one Gaussian state | §9 |
| Partial trace and the chain as a state | The partial traces keep density matrices and Gaussian states, with the principal blocks of the covariance; the contraction `Z⁻¹ Tr_E(ρ(1 ⊗ σ))` of Gaussian states with `1 − Dβ` invertible has `Z > 0`, is Gaussian and has covariance `Γ ⋆ β`; for admissible on-site covariances under the contraction condition, the periodic chain is a Gaussian state on Fock space with covariance `Γ_N` | §10 |
| Purity, ground states and the gap | A Gaussian state is a projection exactly when its covariance is pure, and the contraction of pure Gaussian states with `1 − Dβ` invertible is pure; for pure `Γ` the Gaussian state with covariance `Γ` is the unique ground state of `H_{−Γ}`, with energy `−n/2` and gap 1; the Kitaev chain: its covariance `K_N` is the chain covariance of the Kitaev on-site covariance, pure, and a pure on-site completion reproduces `K_N` for odd `N` (for even `N` the contraction condition fails); the chain state is the unique ground state of `H_{−K}`, with gap 1 | §6, §11 |
| Entanglement rank | The off-diagonal block of the inverse of an invertible matrix has the rank of the off-diagonal block; under the contraction condition, the cross block of `Γ_N` between a set `S` of sites and its complement has rank at most `2M b(S)`, `b(S)` the number of cut bonds, and for pure `Γ_N`, `rank(1 + Γ_S²) ≤ 2M b(S)`; and `rank(1 + (O D(λ) Oᵀ)²) = 2 #{j : λ_j² ≠ 1}` for orthogonal `O` | §12 |

Here `Ω_n = [[0, 1], [−1, 0]]` in block order and `D(ε) = [[0, diag ε], [−diag ε, 0]]`. The precise
statements are the 79 theorems of [`verify/CORE.md`](verify/CORE.md), under headings that refine
the rows of this table. Conventions are listed in `CONVENTIONS.md`.

## Verification

The 79 theorems of the core are 47 main results, 20 statements that describe the library's
definitions in Mathlib's terms (some with further facts), and 12 examples (the pure covariances
`±Ω_n`, the three-site chain, chains without virtual modes, the Kitaev chain with its momentum
form and its pure completion, occupation states, the bond state, a hopping gate acting on a
two-mode state, explicit Gaussian states, and the Kitaev ground state with its gap), which show
that the hypotheses can be met: the contraction of two pure covariances under the contraction
condition is exhibited by the three-site chain and by the pure Kitaev completion for odd `N`, and
that of two Gaussian states by the Kitaev chain state. `verify/Challenge.lean` states them
without proofs, and `verify/Solution.lean` proves them from the library. The command

```
lake comparator --config verify/comparator.json --paranoid
```

checks that every proved theorem has exactly the stated form, that no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` are used, and that Lean's kernel and four independently
written proof checkers accept every proof. A reader who accepts the 79 statements therefore need
not read any proof. Besides the definitions described in the core, only Mathlib's own structures
are used: real and complex matrices, their transpose, conjugate transpose, trace, determinant,
inverse, rank, exponential, block matrices and submatrices, positive semidefinite and positive
definite matrices, finite sets and lists, and the functions exp, cos, sin, cosh, tanh, artanh
and the square root. The same check runs on GitHub at every
change.

`lake comparator` is the proof judge maintained by the Lean developers for proofs whose author is
not trusted, including proofs produced by AI; see
[leanprover/comparator](https://github.com/leanprover/comparator) and the chapter
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator)
of the Lean reference manual. Among its checkers are
[lean4lean](https://github.com/digama0/lean4lean) and [nanoda](https://github.com/ammkrn/nanoda_lib).
On Linux it isolates the compiled code in a sandbox; elsewhere it needs the option
`--inadvisably-no-sandbox`.

## Build and verify

With the Lean installer `elan`:

```
git clone https://github.com/etjoa002/FermionicLean
cd FermionicLean
lake exe cache get          # download the precompiled Mathlib
lake build FermionicLean
lake comparator --config verify/comparator.json --paranoid
```

The library depends only on [Mathlib](https://github.com/leanprover-community/mathlib4); its
version and that of Lean are fixed in `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.
Libraries that build on this one, such as [LocalityLean](https://github.com/etjoa002/LocalityLean),
fix the same versions, and the versions are only ever changed together.

## Methods of proof

Admissibility is defined in its real form, so that the central fact about the contraction has a
short proof by energy: if `(u, v) = Γ(x, w)` and `w = βv`, admissibility of `Γ` gives
`‖u‖² + ‖v‖² ≤ ‖x‖² + ‖w‖²` and admissibility of `β` gives `‖w‖² ≤ ‖v‖²`, hence `‖u‖ ≤ ‖x‖` for
`u = (Γ ⋆ β)x`; no complexification and no Pfaffian is needed. On Fock space the Majorana operators
are explicit Kronecker products of Pauli matrices, and the real normal form of an antisymmetric
matrix together with the implementation of plane rotations by unitaries reduces every statement
about a state with given covariance to a product state of independent modes. The Gaussian class is
defined by Wick's rule in recursive form, again without Pfaffians, and the contraction of Gaussian
states is shown to be Gaussian through the linear relation `(Gᵀv·c)ρ = ρ(Gv·c)` that characterizes
them, which turns the composition of Gaussian maps into the matrix algebra of the contraction.
Explicit examples are decided in integer arithmetic and divided afterwards.

## The notes

[`docs/lecture-notes/FermionicLean.pdf`](docs/lecture-notes/FermionicLean.pdf) gives the account
with full proofs, in the sections listed in the table above, after a reading guide that translates
between the covariance conventions of the literature and those used here, and a roadmap of the
logical dependence of the sections. Part I treats covariance matrices alone (§1–§4); Part II
constructs the states (§5–§12). A tag beside a theorem links to the Lean declarations that prove
it; statements without a tag, motivating paragraphs and remarks are checked on paper only.

## Numerical checks

The scripts in `checks/` (Python with NumPy; `checks/requirements.txt`) test statements of the
notes independently of Lean: `bond_state_and_three_site.py` the covariance of the bond
state and of three-site chains for several pure on-site covariances; `three_site_exact.py` the
three-site example of §3 in exact rational arithmetic, every intermediate value of its proof;
`kitaev_block_modes.py` the entanglement count of a block of the Kitaev chain (§12), exactly, for
`N = 2, …, 9`; `normalization_overlap.py` the closed form `2^{−m} √det(1 − Dβ)` of the
normalization of a contraction (§10) for `n + m ≤ 4`. Each script asserts what it tests and exits
nonzero at a failure; run, for example, `python checks/three_site_exact.py`.
`checks/three-site-data.json` records the integer matrices of the three-site example.

## Library layout

`Gaussian/` real antisymmetric matrices: admissibility, purity, congruence, subsystems, direct
sums, the normal form, rotations, the nullity lemma; `Contraction/` the contraction of covariances,
the bond and the block identities used for states; `Chain/` periodic chains, their Fourier
splitting, the examples, and the chain as a state on Fock space; `Fock/` operators on Fock space:
Majorana operators, covariances of states, quadratic Hamiltonians, ground and thermal states,
Wick's theorem, the partial trace and the contraction of states; `verify/` the core.

<details>
<summary>Lean files and their imports</summary>

<!-- depgraph:start -->
- **Gaussian**
  - `Gaussian.Admissible` <- Gaussian.Defs
  - `Gaussian.BlockForm` <- Fock.Occupation, Gaussian.Examples
  - `Gaussian.BlockRotation` <- Gaussian.BlockForm
  - `Gaussian.Congruence` <- Gaussian.Admissible
  - `Gaussian.Defs` <- (Mathlib only)
  - `Gaussian.DirectSum` <- Gaussian.Admissible, Gaussian.DirectSumDefs
  - `Gaussian.DirectSumDefs` <- Gaussian.Defs
  - `Gaussian.Examples` <- Gaussian.Admissible
  - `Gaussian.NormalForm` <- Gaussian.BlockForm, Gaussian.Congruence
  - `Gaussian.Nullity` <- (Mathlib only)
  - `Gaussian.Rotation` <- (Mathlib only)
  - `Gaussian.Subsystem` <- Gaussian.Admissible
- **Contraction**
  - `Contraction.Admissible` <- Gaussian.Admissible
  - `Contraction.Basic` <- Contraction.Defs
  - `Contraction.BlockDet` <- Contraction.Defs
  - `Contraction.Bond` <- Contraction.Basic
  - `Contraction.Defs` <- Contraction.Admissible
  - `Contraction.PureInverse` <- Contraction.Basic
  - `Contraction.RowSolve` <- Contraction.Defs
- **Chain**
  - `Chain.Cut` <- Chain.Periodic, Contraction.PureInverse, Gaussian.BlockForm, Gaussian.Nullity
  - `Chain.Fourier` <- Chain.Periodic
  - `Chain.Kitaev` <- Chain.Fourier
  - `Chain.KitaevGap` <- Chain.KitaevState, Fock.Gap
  - `Chain.KitaevState` <- Chain.Kitaev, Chain.Pure, Fock.PureGround
  - `Chain.Periodic` <- Contraction.Bond
  - `Chain.Product` <- Chain.Fourier, Fock.Occupation
  - `Chain.Pure` <- Fock.Pure
  - `Chain.State` <- Chain.Product, Fock.GaussianMap
  - `Chain.ThreeSite` <- Chain.Periodic
  - `Chain.ThreeSiteDet` <- Chain.ThreeSite
- **Fock**
  - `Fock.BondState` <- Contraction.Bond, Fock.Occupation
  - `Fock.Covariance` <- Fock.Majorana, Gaussian.Admissible
  - `Fock.Defs` <- Gaussian.Defs
  - `Fock.Evolution` <- Fock.Thermal, Gaussian.BlockRotation
  - `Fock.Gap` <- Fock.PureGround
  - `Fock.Gate` <- Fock.Occupation
  - `Fock.Gaussian` <- Fock.Evolution, Fock.Monomial, Fock.Parity, Fock.Wick
  - `Fock.GaussianMap` <- Contraction.BlockDet, Contraction.RowSolve, Fock.PartialTrace, Fock.Relation
  - `Fock.GroundState` <- Fock.Hamiltonian, Gaussian.Congruence
  - `Fock.Hamiltonian` <- Fock.Gate, Gaussian.BlockForm
  - `Fock.Majorana` <- Fock.Pauli
  - `Fock.Mixture` <- Gaussian.BlockForm
  - `Fock.Monomial` <- Fock.Gate, Fock.Parity
  - `Fock.Occupation` <- Fock.Covariance, Gaussian.Examples
  - `Fock.Parity` <- Fock.Majorana
  - `Fock.PartialTrace` <- Fock.Hamiltonian, Fock.Parity, Fock.Wick
  - `Fock.Pauli` <- Fock.Defs
  - `Fock.Pure` <- Chain.State
  - `Fock.PureGround` <- Fock.Pure, Fock.Thermal
  - `Fock.Realization` <- Fock.GroundState, Fock.Mixture, Fock.Spin, Gaussian.NormalForm
  - `Fock.Relation` <- Fock.Gaussian
  - `Fock.Spin` <- Fock.Gate, Gaussian.Rotation
  - `Fock.Thermal` <- Fock.Realization
  - `Fock.Wick` <- Fock.Realization, Fock.Thermal
<!-- depgraph:end -->

</details>

## Status

The library is under development, and this repository is updated as the work progresses; see
`CONTRIBUTING.md` for problem reports and suggestions. Planned next is the thermodynamic limit
`N → ∞` of translation-invariant Gaussian fMPS, as the convergence of two-point functions to a
covariance integral and a compatible family of Gaussian states on finite regions; later the decay
of correlations, the entropy of Gaussian states, and non-Gaussian fermionic states and tensor
networks. Candidates for later theorems, from the notes: the closed form `2^{−m} √det(1 − Dβ)` of
the normalization of a contraction (checked numerically for `n + m ≤ 4`); the count of at most
`M b(S)` entangled modes across a cut and the Schmidt rank bound `2^{M b(S)}`, which the notes
draw from the rank bounds; the entanglement count of a block of the Kitaev chain (checked exactly
for small chains); that a tensor product of Gaussian states is Gaussian; the exponential form of
the hopping gate.

## Citation and licence

Erickson Tjoa, *FermionicLean: fermionic Gaussian states in Lean*, 2026,
https://github.com/etjoa002/FermionicLean. Apache 2.0 (`LICENSE`, `NOTICE`); `CITATION.cff` gives
the reference in machine-readable form. The conventions follow S. Bravyi, Quantum Inf. Comput. 5
(2005) 216, arXiv:quant-ph/0404180, and S. Bravyi and A. Kitaev, Ann. Phys. 298 (2002) 210; the
Gaussian fMPS construction is that of C. V. Kraus, N. Schuch, F. Verstraete and J. I. Cirac, Phys.
Rev. A 81 (2010) 052338. The other sources are cited in the notes.

Developed with AI assistance. The author approved every definition and theorem statement and is
responsible for the content; every proof is checked by Lean.
