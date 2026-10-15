# Conventions

## Mathematics

### Majorana labels and covariances

- A system of `n` modes has `2n` Majorana labels, the two labels `x_j`, `y_j` of each mode `j`.
  Every matrix is written in **block order** `(x_1, …, x_n, y_1, …, y_n)`; the interleaved
  numbering of the literature is `c_{2j−1} = x_j`, `c_{2j} = y_j`, and a matrix in interleaved
  order is obtained by permuting rows and columns accordingly. In this order
  `Ω_n = [[0, 1_n], [−1_n, 0]]`, and the canonical form is `D(ε) = [[0, diag ε], [−diag ε, 0]]`;
  in interleaved order they become `⊕_j [[0, 1], [−1, 0]]` and `⊕_j ε_j [[0, 1], [−1, 0]]`.
- Majorana operators are Hermitian with `c_a c_b + c_b c_a = 2δ_ab`. The covariance of a state is
  the real antisymmetric matrix `Γ_ab = Re((i/2) Tr(ρ [c_a, c_b]))` (the real part is redundant for
  Hermitian `ρ`), and the two-point matrix is `G = 1 − iΓ`, so that `Tr(ρ c_a c_b) = G_ab`. In part
  of the literature `Γ` denotes the correlation matrix `Tr(ρ c_a c_b)` or the matrix
  `Tr(ρ a_j* a_k)`; here it is always the antisymmetric matrix above.
- A real matrix `Γ` is **admissible** when `Γᵀ = −Γ` and `1 − ΓᵀΓ ⪰ 0` (the real form is the
  definition; `1 + iΓ ⪰ 0` and `‖Γx‖ ≤ ‖x‖` are theorems), **pure** when `Γᵀ = −Γ` and `Γ² = −1`,
  and **strictly admissible** when moreover all `|ε_j| < 1` in its normal form `O D(ε) Oᵀ`.
  Admissibility and purity are stated both for the labels of `n` modes and for an arbitrary finite
  label set; the two agree on Majorana labels.

### Fock space

- Fock space is `ℂ^{2^n}` with the configuration basis `|s⟩`, `s ∈ {0, 1}^n`. The Jordan–Wigner
  operators are `c_{x_j} = Z_{<j} X_j` and `c_{y_j} = i Z_{<j} X_j Z_j`, with `Z_{<j} = Z_1 ⋯ Z_{j−1}`;
  the annihilation operator of mode `j` is `a_j = (c_{x_j} + i c_{y_j})/2`, so `c_{y_j} = i(a_j* − a_j)`.
- With these choices the vacuum has `Γ = −Ω_n`, and `Ω_n` is the covariance of the state with every
  mode occupied. The occupation sign of a mode is `ν(b) = 2b − 1` (`−1` empty, `+1` occupied), and
  the occupation state `|s⟩⟨s|` has covariance `[[0, Λ_s], [−Λ_s, 0]]`, `Λ_s = diag(ν(s_j))`.
- A unitary `U` **implements** a real matrix `O` when `U c_a U* = Σ_b O_ab c_b`; then
  `Γ(U* ρ U) = O Γ(ρ) Oᵀ`.
- The quadratic Hamiltonian of a real antisymmetric `h` is `H_h = (i/4) Σ_{a,b} h_ab c_a c_b`, with
  energy `Tr(ρ H_h) = (1/4) Σ h_ab Γ_ab`. The exponential (Gibbs) state is
  `ρ_h = e^{−H_h} / Tr e^{−H_h}` (the physical sign), the thermal state at inverse temperature `τ`
  is `ρ_{τh}`, and the evolution is `e^{−itH_h}`, which implements `e^{th}`.
- A density operator is **Gaussian** when all its Majorana moments are given by Wick's rule from its
  own two-point matrix: the odd moments vanish and the even ones are expanded recursively; no
  Pfaffian is used.

### Contraction and chains

- A matrix on retained and eliminated labels `R ⊔ E` has blocks `A, B, C, D`; the contraction against
  a matrix `Γ_p` on `E` is `Γ ⋆ Γ_p = A + B Γ_p (1 − D Γ_p)⁻¹ C`, with the invertibility of
  `1 − D Γ_p` a hypothesis (for fermions the projected state can vanish). For pure `Γ_p` it equals
  the Schur form `A + B (D + Γ_p)⁻¹ Bᵀ`.
- The bond covariance on two matched copies `L`, `L'` of a set of modes, with labels
  `(x_L, x_{L'}, y_L, y_{L'})`, is `β = diag(J, −J)`, `J = [[0, 1_L], [−1_L, 0]]`: `β_{x_a x_{a'}} = +1`,
  `β_{y_a y_{a'}} = −1`. Its state is `(|00⟩ + i|11⟩)/√2` on each pair, which pairs `x` with `x`
  and `y` with `y`.
- A periodic chain has sites `i ∈ ℤ/N`, each with `M` left virtual modes `A_i`, `M` right virtual
  modes `B_i` and `P` physical modes `C_i`; the bonds join `(A_i, B_{i−1})`. The input matrix
  stacks the on-site covariances site by site and reorders the labels to physical first, then the
  bond pairs; the chain covariance is `Γ_N = Γ_in ⋆ β_N`. `N`, `M` and `P` are arbitrary.
- In momentum space the characters are `χ_k(j) = ω_k^j` with the phases `ω_k = e^{−2πik/N}`, and
  `Σ(k)` is the `2P × 2P` momentum-space covariance of a homogeneous chain.

## Lean

- Mathlib is the only dependency. All declarations live in the namespace `Fermionic`, in four
  folders: `Gaussian/` (matrices), `Contraction/`, `Chain/` and `Fock/` (operators on Fock space).
- Majorana labels of `n` modes are `MajoranaIndex n = Fin n ⊕ Fin n`, with `Sum.inl` the `x` block;
  Fock space is indexed by `FockIndex n`; matrices are Mathlib's `Matrix`, density operators are
  complex matrices that are positive semidefinite with trace one (`IsDensity`).
- Hypotheses such as the invertibility of `1 − DΓ_p` (`ContractInvertible`) are explicit arguments,
  and a total matrix inverse is used where a proof on paper would assume invertibility.
- Declaration names are ASCII and follow Mathlib's naming and style.
- No unfinished proofs, no added axioms, no unchecked computation, no blanket import of Mathlib.
