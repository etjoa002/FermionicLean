# The sealed statements

Generated from `verify/Challenge.lean` by `verify/make_core_page.py`: the 79 statements that `lake comparator` checks (see the section "Verification" of the front page). Each entry gives the statement in words and the name of its formal version in `Challenge.lean`.

## Covariance matrices

A system of $`n`$ fermionic modes $`j = 0, \dots, n - 1`$ has $`2n`$ Majorana labels: $`x_j`$ and $`y_j`$ label the two Majorana operators of mode $`j`$. The label set is the disjoint union of two copies of $`\{0, \dots, n - 1\}`$, the first copy carrying the $`x`$ labels, so a matrix on the labels is written in $`2 \times 2`$ block form with the $`x`$ labels first. A covariance matrix is a real matrix $`\Gamma`$ on the labels. The covariance of a state $`\rho`$ with Majorana operators $`c_a`$ is 

```math
\Gamma_{ab} = \mathrm{Re}\, \tfrac{i}{2} \mathrm{tr}\,(\rho [c_a, c_b])
```

(second part); with this sign the vacuum has covariance $`-\Omega_n`$, where 

```math
\Omega_n = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix},
```

so $`\Gamma_{x_j y_j} = -1`$ in the vacuum. A real matrix $`\Gamma`$ on a finite index set is admissible when $`\Gamma^T = -\Gamma`$ and $`1 - \Gamma^T \Gamma`$ is positive semidefinite, and pure when $`\Gamma^T = -\Gamma`$ and $`\Gamma^2 = -1`$. A complex matrix $`X`$ is positive semidefinite when it is Hermitian and $`\bar v^T X v \ge 0`$ for every complex vector $`v`$; for real matrices the vectors are real. A real matrix $`O`$ is orthogonal when $`O O^T = 1`$.

**1.** The definitions. The Majorana labels of $`n`$ modes are two copies of $`\{0, \dots, n - 1\}`$, the $`x`$ labels first. A real matrix $`\Gamma`$ on them is admissible exactly when $`\Gamma^T = -\Gamma`$ and $`1 - \Gamma^T \Gamma`$ is positive semidefinite, and pure exactly when $`\Gamma^T = -\Gamma`$ and $`\Gamma \Gamma = -1`$. The same conditions define admissibility and purity of a real matrix $`\Gamma'`$ on an arbitrary finite index set $`\iota`$.  
<sub>`Sealed.admissible_def`</sub>

**2.** Equivalent forms of admissibility. For a real antisymmetric matrix $`\Gamma`$ on the Majorana labels of $`n`$ modes, the following are equivalent: $`\Gamma`$ is admissible; $`\|\Gamma v\|^2 \le \|v\|^2`$ for every real vector $`v`$; the complex matrix $`1 + i\Gamma`$ is positive semidefinite.  
<sub>`Sealed.admissible_forms`</sub>

**3.** A pure covariance matrix $`\Gamma`$ on the Majorana labels of $`n`$ modes is orthogonal, $`\Gamma^T \Gamma = 1`$, and admissible.  
<sub>`Sealed.pure_orthogonal`</sub>

**4.** Orthogonal changes of Majorana basis. Let $`O`$ be a real orthogonal matrix on the Majorana labels of $`n`$ modes ($`O O^T = 1`$). If $`\Gamma`$ is admissible, so is $`O \Gamma O^T`$; if $`\Gamma`$ is pure, so is $`O \Gamma O^T`$.  
<sub>`Sealed.orthogonal_congruence`</sub>

**5.** Relabelling and block-diagonal sums. Let $`e : \iota \to \kappa`$ be a bijection of finite index sets and $`\Gamma`$ a real matrix on $`\kappa`$; the relabelled matrix $`(\Gamma_{e(a) e(b)})_{a, b \in \iota}`$ is admissible exactly when $`\Gamma`$ is, and pure exactly when $`\Gamma`$ is. Let $`\Delta_s`$, $`s \in \sigma`$, be real matrices on a finite set $`\iota`$, with $`\sigma`$ finite, and $`\bigoplus_s \Delta_s`$ the block-diagonal matrix on $`\iota \times \sigma`$ with entry $`\delta_{st} (\Delta_s)_{ab}`$ at $`((a, s), (b, t))`$; it is admissible exactly when every $`\Delta_s`$ is, and pure exactly when every $`\Delta_s`$ is.  
<sub>`Sealed.relabel_block_diagonal`</sub>

**6.** Restriction to a subset of modes. Let $`\Gamma`$ be an admissible covariance matrix of $`n`$ modes and $`e : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}`$ injective. The restriction of $`\Gamma`$ to the labels $`x_{e(j)}, y_{e(j)}`$, $`j = 0, \dots, m - 1`$, in this order, is an admissible covariance matrix of $`m`$ modes.  
<sub>`Sealed.mode_restriction`</sub>

**7.** Independent sums. Let $`A`$ be a real matrix on the Majorana labels of $`n`$ modes and $`B`$ one on those of $`m`$ modes. Their independent sum $`A \oplus B`$ is a real matrix on the labels of $`n + m`$ modes, the modes of $`A`$ first: the map $`\sigma`$ with $`\sigma(x_j^A) = x_j`$, $`\sigma(y_j^A) = y_j`$, $`\sigma(x_j^B) = x_{n+j}`$, $`\sigma(y_j^B) = y_{n+j}`$ is a bijection from the labels of $`A`$ followed by those of $`B`$ onto the labels of $`n + m`$ modes, and $`(A \oplus B)_{\sigma(u) \sigma(v)}`$ is the $`(u, v)`$ entry of 

```math
\begin{pmatrix} A & 0 \\ 0 & B \end{pmatrix}.
```

The sum is admissible exactly when $`A`$ and $`B`$ are, and pure exactly when $`A`$ and $`B`$ are.  
<sub>`Sealed.direct_sum`</sub>

**8.** One mode. Every real antisymmetric matrix $`\Gamma`$ on the two labels of one mode is $`\mu \omega`$ for some real $`\mu`$, where 

```math
\omega = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix};
```

and for real $`\lambda`$, $`\lambda \omega`$ is admissible exactly when $`|\lambda| \le 1`$ and pure exactly when $`|\lambda| = 1`$.  
<sub>`Sealed.one_mode`</sub>

**9.** The standard pure covariances. On the Majorana labels of $`n`$ modes, 

```math
\Omega_n = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}
```

and $`-\Omega_n`$ (the vacuum covariance in the sign convention above) are pure.  
<sub>`Sealed.standard_pure`</sub>

## Contraction and the bond

Let $`\iota`$ (retained labels) and $`\kappa`$ (eliminated labels) be finite index sets, $`\Gamma`$ a real matrix on $`\iota \sqcup \kappa`$ with blocks $`A = \Gamma_{\iota\iota}`$, $`B = \Gamma_{\iota\kappa}`$, $`C = \Gamma_{\kappa\iota}`$, $`D = \Gamma_{\kappa\kappa}`$, and $`\beta`$ a real matrix on $`\kappa`$. The contraction of $`\Gamma`$ with $`\beta`$ is the matrix 

```math
\Gamma \star \beta = A + B \beta (1 - D \beta)^{-1} C
```

on $`\iota`$. It is meant under the contraction condition $`\det(1 - D \beta) \ne 0`$; the inverse is the matrix inverse, which is $`0`$ for a singular matrix. For a finite set $`L`$ of modes, the bond is a covariance matrix of two matched copies $`L, L'`$ of $`L`$, on the labels ordered $`x_L, x_{L'}, y_L, y_{L'}`$; it correlates $`x_a`$ with $`x_{a'}`$ and $`y_a`$ with $`y_{a'}`$ for every $`a \in L`$.

**10.** The definition of the contraction: 

```math
\Gamma \star \beta = A + B \beta (1 - D \beta)^{-1} C
```

in the blocks of $`\Gamma`$, and the contraction condition is $`\det(1 - D \beta) \ne 0`$.  
<sub>`Sealed.contract_def`</sub>

**11.** Contraction preserves antisymmetry and admissibility. Under the contraction condition: if $`\Gamma`$ and $`\beta`$ are antisymmetric, so is $`\Gamma \star \beta`$; if $`\Gamma`$ and $`\beta`$ are admissible, so is $`\Gamma \star \beta`$.  
<sub>`Sealed.contraction_admissible`</sub>

**12.** Contraction with a pure $`\beta`$. If $`\beta`$ is pure, the contraction condition holds exactly when $`\det(D + \beta) \ne 0`$, and for antisymmetric $`\Gamma`$ satisfying it, 

```math
\Gamma \star \beta = A + B (D + \beta)^{-1} B^T.
```  
<sub>`Sealed.contraction_pure_bond`</sub>

**13.** Contraction of pure covariances is pure. Let $`\Gamma`$ be a pure matrix on the Majorana labels of $`n`$ retained modes followed by those of $`m`$ eliminated modes, and $`\beta`$ a pure covariance matrix of the $`m`$ eliminated modes, with the contraction condition. Then $`\Gamma \star \beta`$ is a pure covariance matrix of the $`n`$ retained modes.  
<sub>`Sealed.contraction_pure`</sub>

**14.** The bond. For a finite set $`L`$, the labels of the bond are four copies of $`L`$, ordered $`x_L, x_{L'}, y_L, y_{L'}`$; the bond is 

```math
\begin{pmatrix} \omega & 0 \\ 0 & -\omega \end{pmatrix}
```

with 

```math
\omega = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}
```

on $`(L, L')`$, so $`\Gamma_{x_a x_{a'}} = 1`$ and $`\Gamma_{y_a y_{a'}} = -1`$ for $`a \in L`$. The bond is pure.  
<sub>`Sealed.bond_pure`</sub>

**15.** Entanglement swapping through a bond. Take two bonds, on $`(A_1, B_1)`$ and on $`(A_2, B_2)`$, each mode set a copy of $`L`$ and each bond on its labels $`(x_A, x_B, y_A, y_B)`$, and form their block-diagonal sum. Read it on the retained labels $`(x_{A_1}, x_{B_2}, y_{A_1}, y_{B_2})`$ followed by the eliminated labels $`(x_{B_1}, x_{A_2}, y_{B_1}, y_{A_2})`$, through the map $`\tau`$ sending each of these labels to the label of the same name in the sum. The result is 

```math
\begin{pmatrix} 0 & X \\ -X^T & 0 \end{pmatrix}
```

with $`X = \mathrm{diag}\,(1, -1, -1, 1)`$ in blocks of size $`|L|`$, and its contraction with the bond on $`(B_1, A_2)`$ is the bond on $`(A_1, B_2)`$.  
<sub>`Sealed.teleportation`</sub>

## Periodic chains and three sites

A periodic chain has $`N`$ sites $`0, \dots, N - 1`$, read modulo $`N`$; $`i + 1`$ and $`i - 1`$ are the cyclic successor and predecessor. Each site carries $`M`$ left virtual modes $`A`$, $`M`$ right virtual modes $`B`$ and $`P`$ physical modes $`C`$ (each numbered from $`0`$); its Majorana labels are ordered $`x_A, x_B, x_C, y_A, y_B, y_C`$. The chain data are real matrices $`\Gamma_i`$ on the labels of site $`i`$. The retained labels of the chain are the physical labels $`x_{(i,c)}, y_{(i,c)}`$ of all sites, $`x`$ first. The eliminated labels are the bond labels $`x_L, x_{L'}, y_L, y_{L'}`$ with 

```math
L = L' = \{\text{sites}\} \times \{\text{virtual modes}\}:
```

the label $`(i, a)`$ of $`L`$ is the mode $`A_a`$ of site $`i`$, and the label $`(i, a)`$ of $`L'`$ is the mode $`B_a`$ of site $`i - 1`$, so that bond $`i`$ joins site $`i - 1`$ to site $`i`$. The periodic input is the block-diagonal sum of the $`\Gamma_i`$ on these labels, the periodic bond is the bond on $`L`$, and the periodic covariance $`\Gamma_N`$ is the contraction of the periodic input with the periodic bond, a matrix on the physical labels.

**16.** The label sets of a chain: the labels of a site are $`(A, B, C)`$ for $`x`$, then $`(A, B, C)`$ for $`y`$; the retained labels are the pairs (site, physical mode) for $`x`$, then for $`y`$; the eliminated labels are the bond labels on the pairs (site, virtual mode).  
<sub>`Sealed.chain_labels`</sub>

**17.** The definition of the periodic chain. The periodic input of chain data $`\Gamma_i`$ is the block-diagonal matrix $`\bigoplus_i \Gamma_i`$ on (site label, site) relabelled by $`\sigma`$, which sends $`x_{(i,c)} \mapsto (x_{C_c}, i)`$, $`y_{(i,c)} \mapsto (y_{C_c}, i)`$, the $`L`$ labels $`x_{(i,a)} \mapsto (x_{A_a}, i)`$, $`y_{(i,a)} \mapsto (y_{A_a}, i)`$, and the $`L'`$ labels $`x_{(i,a)} \mapsto (x_{B_a}, i - 1)`$, $`y_{(i,a)} \mapsto (y_{B_a}, i - 1)`$. The periodic bond is the bond on $`L`$, and the periodic covariance is the contraction of the periodic input with the periodic bond.  
<sub>`Sealed.periodic_def`</sub>

**18.** Admissibility of the chain. The periodic input is admissible exactly when every $`\Gamma_i`$ is, and pure exactly when every $`\Gamma_i`$ is. If every $`\Gamma_i`$ is admissible and the contraction condition holds for the periodic input and the periodic bond, the periodic covariance $`\Gamma_N`$ is admissible.  
<sub>`Sealed.periodic_admissible`</sub>

**19.** Purity of the chain. If every $`\Gamma_i`$ is pure and the contraction condition holds, the periodic covariance $`\Gamma_N`$ is pure.  
<sub>`Sealed.periodic_pure`</sub>

**20.** A three-site chain, evaluated exactly. Take $`N = 3`$ sites, $`M = P = 1`$, and at every site the matrix $`G`$ that, on the labels ordered $`(x_A, x_B, x_C, y_A, y_B, y_C)`$, is 

```math
\tfrac15 \begin{pmatrix} 0 & 3 & -4 & 0 & 0 & 0 \\ -3 & 0 & 0 & 0 & 0 & -4 \\ 4 & 0 & 0 & 0 & 0 & -3 \\ 0 & 0 & 0 & 0 & -5 & 0 \\ 0 & 0 & 0 & 5 & 0 & 0 \\ 0 & 4 & 3 & 0 & 0 & 0 \end{pmatrix}.
```

Then $`G`$ is pure, the contraction condition holds with $`\det(1 - D\beta_3) = (304/125)^2`$ ($`D`$ the block of the input on the eliminated labels, $`\beta_3`$ the bond), and the periodic covariance, on the physical labels ordered $`(x_{C_0}, x_{C_1}, x_{C_2}, y_{C_0}, y_{C_1}, y_{C_2})`$, is 

```math
\tfrac1{19} \begin{pmatrix} 0 & 0 & 0 & -15 & 6 & -10 \\ 0 & 0 & 0 & -10 & -15 & 6 \\ 0 & 0 & 0 & 6 & -10 & -15 \\ 15 & 10 & -6 & 0 & 0 & 0 \\ -6 & 15 & 10 & 0 & 0 & 0 \\ 10 & -6 & 15 & 0 & 0 & 0 \end{pmatrix}.
```  
<sub>`Sealed.three_site`</sub>

## Momentum space

A homogeneous chain has the same matrix $`\Gamma`$ on the labels of every site, and $`N \ge 1`$ sites. For sites $`i`$ and momenta $`k`$ in $`\{0, \dots, N - 1\}`$ the character is $`\chi_k(i) = e^{-2\pi i k i / N}`$ and the phase of one step is $`\omega_k = e^{-2\pi i k / N}`$; the momentum $`-k`$ is $`N - k`$ modulo $`N`$. The twist $`t_k`$ is the function on the labels of a site that is $`\omega_k`$ on the labels $`x_B, y_B`$ and $`1`$ on all others. The twisted local matrix 

```math
T_k = \mathrm{diag}\,(t_k)\, \Gamma\, \mathrm{diag}\,(t_k)^*
```

is a complex matrix, written in the split of the site labels into the physical labels $`(x_C, y_C)`$ and the virtual labels 

```math
(x_L, x_{L'}, y_L, y_{L'}) = (x_A, x_B, y_A, y_B).
```

The momentum-space covariance $`\Sigma(k)`$ is the contraction of $`T_k`$ with the bond $`\beta_M`$ of one site's $`M`$ virtual modes, computed over $`\mathbb C`$ with the complex matrix inverse; it is a complex matrix on the physical labels $`(x_C, y_C)`$ of one site. A physical label $`u`$ of a site, placed at site $`i`$, is written $`(i, u)`$; $`\Gamma_N`$ is the periodic covariance of the homogeneous chain. For a complex matrix, $`X^*`$ is the conjugate transpose and $`\bar X`$ the entrywise conjugate.

**21.** The definition of the momentum-space covariance. With $`\omega_k = e^{-2\pi i k / N}`$, the twist $`t_k`$ equal to $`\omega_k`$ on $`x_B, y_B`$ and $`1`$ elsewhere, and $`s`$ the split of the site labels sending the physical labels $`x_c, y_c`$ to $`x_{C_c}, y_{C_c}`$ and the virtual labels $`x_L, x_{L'}, y_L, y_{L'}`$ to $`x_A, x_B, y_A, y_B`$: the twisted local matrix is 

```math
T_k = (\mathrm{diag}\,(t_k)\, \Gamma\, \mathrm{diag}\,(t_k)^*)_{s(u) s(v)},
```

the one-site bond is the bond on $`M`$ modes regarded as a complex matrix, and 

```math
\Sigma(k) = A_k + B_k \beta_M (1 - D_k \beta_M)^{-1} C_k
```

in the blocks $`A_k, B_k, C_k, D_k`$ of $`T_k`$ (physical, then virtual).  
<sub>`Sealed.momentum_def`</sub>

**22.** The determinant factorizes over momenta. For a homogeneous chain, 

```math
\det(1 - D \beta_N) = \prod_k \det(1 - D_k \beta_M),
```

where $`D`$ is the virtual block of the periodic input, $`\beta_N`$ the periodic bond, and $`D_k`$ the virtual block of $`T_k`$. In particular, under the contraction condition of the chain every $`\det(1 - D_k \beta_M)`$ is nonzero.  
<sub>`Sealed.momentum_det`</sub>

**23.** Diagonalization by the Fourier transform. For a homogeneous chain with the contraction condition, momenta $`k, l`$ and physical labels $`a, b`$ of a site, 

```math
\frac1N \sum_{i,j} \chi_k(i)\, (\Gamma_N)_{(i,a)(j,b)}\, \overline{\chi_l(j)} = \delta_{kl}\, \Sigma(k)_{ab}.
```  
<sub>`Sealed.fourier_diagonal`</sub>

**24.** Reconstruction and translation invariance. For a homogeneous chain with the contraction condition, sites $`i, j`$ and physical labels $`a, b`$ of a site, 

```math
(\Gamma_N)_{(i,a)(j,b)} = \frac1N \sum_k \overline{\chi_k(i)}\, \Sigma(k)_{ab}\, \chi_k(j),
```

and 

```math
(\Gamma_N)_{(i+1,a)(j+1,b)} = (\Gamma_N)_{(i,a)(j,b)}.
```  
<sub>`Sealed.fourier_reconstruct`</sub>

**25.** Symmetries of the momentum-space covariance. For a homogeneous chain and every momentum $`k`$: $`\Sigma(-k) = \overline{\Sigma(k)}`$. If $`\Gamma`$ is antisymmetric and the contraction condition holds, $`\Sigma(k)^* = -\Sigma(k)`$. If $`\Gamma`$ is admissible and the contraction condition holds, $`1 - \Sigma(k)^* \Sigma(k)`$ is positive semidefinite.  
<sub>`Sealed.momentum_symmetries`</sub>

## Normal form and rotations

For real numbers $`\varepsilon_0, \dots, \varepsilon_{n-1}`$, the block form $`D(\varepsilon)`$ is the real matrix on the Majorana labels of $`n`$ modes with $`D(\varepsilon)_{x_j y_j} = \varepsilon_j`$, $`D(\varepsilon)_{y_j x_j} = -\varepsilon_j`$ and all other entries $`0`$. A plane rotation on a finite index set $`\iota`$ acts as the rotation by the angle with cosine $`c`$ and sine $`s`$ in the plane of two distinct labels $`a, b`$ and as the identity elsewhere. The exponential of a square matrix is the sum of its exponential series.

**26.** The block form: 

```math
D(\varepsilon) = \begin{pmatrix} 0 & \mathrm{diag}\,(\varepsilon) \\ -\mathrm{diag}\,(\varepsilon) & 0 \end{pmatrix}.
```

It is admissible exactly when every $`|\varepsilon_j| \le 1`$, and pure exactly when every $`|\varepsilon_j| = 1`$.  
<sub>`Sealed.block_form`</sub>

**27.** The normal form. Every real antisymmetric matrix $`\Gamma`$ on the Majorana labels of $`n`$ modes is $`\Gamma = O D(\varepsilon) O^T`$ with $`O`$ orthogonal and every $`\varepsilon_j \ge 0`$; and also $`\Gamma = O' D(\varepsilon') O'^T`$ with $`O'`$ orthogonal of determinant $`1`$.  
<sub>`Sealed.normal_form`</sub>

**28.** The values of the normal form. If $`\Gamma = O D(\varepsilon) O^T`$ with $`O`$ orthogonal, then $`\Gamma`$ is admissible exactly when every $`|\varepsilon_j| \le 1`$, and pure exactly when every $`|\varepsilon_j| = 1`$.  
<sub>`Sealed.normal_form_values`</sub>

**29.** The exponential of a block form. For real $`\theta_0, \dots, \theta_{n-1}`$, 

```math
e^{D(\theta)} = \begin{pmatrix} \mathrm{diag}\,(\cos\theta) & \mathrm{diag}\,(\sin\theta) \\ -\mathrm{diag}\,(\sin\theta) & \mathrm{diag}\,(\cos\theta) \end{pmatrix},
```

and this matrix $`R`$ is orthogonal, $`R R^T = 1`$.  
<sub>`Sealed.block_exponential`</sub>

**30.** Rotations generate the special orthogonal group. For labels $`a \ne b`$ of a finite index set $`\iota`$, the plane rotation $`R_{ab}(c, s)`$ has rows $`a`$ and $`b`$ equal to $`(c, -s)`$ and $`(s, c)`$ on the columns $`(a, b)`$ and zero elsewhere, and every other row equal to that of the identity (for $`a = b`$ the defining formula gives the identity with $`c`$ at $`(a, a)`$; the products below use only $`a \ne b`$). A real matrix $`O`$ on $`\iota`$ is orthogonal with $`\det O = 1`$ exactly when it is a finite product (possibly empty) of plane rotations $`R_{ab}(c, s)`$ with $`a \ne b`$ and $`c^2 + s^2 = 1`$.  
<sub>`Sealed.rotation_products`</sub>

## Examples: product chains and the Kitaev chain

A chain without virtual modes ($`M = 0`$) has no bonds. The Kitaev chain at its solvable point has one physical and one virtual mode per site ($`M = P = 1`$); the labels of a site are written $`x_A, x_B, x_C, y_A, y_B, y_C`$, and those of the chain $`x_i, y_i`$ for the physical mode of site $`i`$. For labels $`u, v`$, $`E_{uv}`$ is the matrix with entry $`1`$ at $`(u, v)`$ and $`0`$ elsewhere.

**31.** Chains without virtual modes are products. For chain data $`\Gamma_i`$ with $`M = 0`$, the contraction condition holds; the periodic covariance couples only labels of the same site, 

```math
(\Gamma_N)_{(i,a)(j,b)} = \delta_{ij} (\Gamma_i)_{C_a C_b}
```

for physical labels $`a, b`$, where $`C_a`$ is the site label $`x_{C_c}`$ for $`a = x_c`$ and $`y_{C_c}`$ for $`a = y_c`$; and $`\Gamma_N`$ is admissible exactly when every $`\Gamma_i`$ is, pure exactly when every $`\Gamma_i`$ is.  
<sub>`Sealed.product_chain`</sub>

**32.** The Kitaev on-site covariance 

```math
K = E_{x_C x_A} - E_{x_A x_C} + E_{y_C x_B} - E_{x_B y_C}
```

correlates $`x_C`$ with $`x_A`$ and $`y_C`$ with $`x_B`$. It is admissible and not pure.  
<sub>`Sealed.kitaev_local`</sub>

**33.** The Kitaev chain. The matrix $`K_N`$ on the physical labels of $`N`$ sites has $`(K_N)_{y_i x_j} = 1`$ and $`(K_N)_{x_j y_i} = -1`$ when $`j = i + 1`$, and all other entries $`0`$. For $`N \ge 1`$, the chain with $`K`$ at every site satisfies the contraction condition, its periodic covariance is $`K_N`$, and $`K_N`$ is pure.  
<sub>`Sealed.kitaev_chain`</sub>

**34.** The Kitaev chain in momentum space. For $`N \ge 1`$ and every momentum $`k`$, the momentum-space covariance of the Kitaev on-site covariance $`K`$ is 

```math
\Sigma(k) = \begin{pmatrix} 0 & -\omega_k \\ \overline{\omega_k} & 0 \end{pmatrix}
```

on $`(x_C, y_C)`$, with $`\omega_k = e^{-2\pi i k / N}`$.  
<sub>`Sealed.kitaev_momentum`</sub>

**35.** A pure completion of the Kitaev on-site covariance. The matrix 

```math
K' = K - E_{y_A y_B} + E_{y_B y_A}
```

is pure. For $`N \ge 1`$, the chain with $`K'`$ at every site has $`\det(1 - D \beta_N) = (1 - (-1)^N)^2`$, where $`D`$ is the virtual block of the periodic input and $`\beta_N`$ the periodic bond, so the contraction condition fails for even $`N`$; for odd $`N`$ it holds and the periodic covariance is the Kitaev chain $`K_N`$.  
<sub>`Sealed.kitaev_completion`</sub>

## Entanglement rank

For a periodic chain and a set $`S`$ of sites, $`R_S`$ is the set of physical labels of the sites in $`S`$ and $`R_{S^c}`$ that of the sites outside $`S`$. For a matrix $`X`$ on the physical labels, the cross block is $`C_S = X_{R_S R_{S^c}}`$ and the block covariance is $`\Gamma_S = X_{R_S R_S}`$. Bond $`i`$ joins site $`i - 1`$ to site $`i`$ and is cut by $`S`$ when exactly one of the two sites lies in $`S`$; $`b(S)`$ is the number of cut bonds. The rank of a matrix is the dimension of its column space.

**36.** The definitions of the cut. The site of the physical labels $`x_{(i,c)}, y_{(i,c)}`$ is $`i`$; $`R_S`$ and $`R_{S^c}`$ are the physical labels whose site is in $`S`$, respectively not in $`S`$; the cross block $`C_S`$ and the block covariance $`\Gamma_S`$ are the corresponding submatrices of $`X`$; and the cut bonds are the sites $`i`$ such that exactly one of $`i`$ and $`i - 1`$ lies in $`S`$.  
<sub>`Sealed.cut_def`</sub>

**37.** The cross-block rank bound. For chain data $`\Gamma_i`$ with the contraction condition and every set $`S`$ of sites, the cross block of the periodic covariance has $`\mathrm{rank}\, C_S \le 2 M\, b(S)`$.  
<sub>`Sealed.cross_block_rank`</sub>

**38.** The entanglement rank bound. For every pure matrix $`X`$ on the physical labels and every set $`S`$ of sites, $`1 + \Gamma_S^2 = C_S C_S^T`$. Consequently, for chain data with the contraction condition whose periodic covariance is pure, 

```math
\mathrm{rank}\,(1 + \Gamma_S^2) \le 2 M\, b(S).
```  
<sub>`Sealed.entanglement_rank`</sub>

**39.** The rank of $`1 + \Gamma^2`$ in the normal form. If $`O`$ is a real orthogonal matrix on the Majorana labels of $`n`$ modes and $`\Gamma = O D(\lambda) O^T`$, then 

```math
\mathrm{rank}\,(1 + \Gamma^2) = 2\, \#\{j : \lambda_j^2 \ne 1\}.
```  
<sub>`Sealed.rank_normal_form`</sub>

**40.** The nullity lemma. For an invertible real matrix $`X`$ on a disjoint union $`\iota \sqcup \kappa`$ of finite sets, the $`(\iota, \kappa)`$ block of $`X^{-1}`$ has the same rank as the $`(\iota, \kappa)`$ block of $`X`$.  
<sub>`Sealed.nullity_rank`</sub>

## Majorana operators and covariances of states

Fock space of $`n`$ fermionic modes is $`\mathbb C^{\{0,1\}^n}`$, with basis vectors $`|s\rangle`$ indexed by the configurations 

```math
s = (s_0, \dots, s_{n-1}) \in \{0,1\}^n
```

($`s_j = 1`$: mode $`j`$ occupied); operators on it are complex matrices indexed by configurations, and $`s^{(j)}`$ is $`s`$ with its bit $`j`$ flipped. The Majorana labels of $`n`$ modes are $`x_0, \dots, x_{n-1}`$ followed by $`y_0, \dots, y_{n-1}`$; a real matrix on the labels is written in blocks 

```math
\begin{pmatrix} A & B \\ C & D \end{pmatrix}
```

for this order (the $`x`$-block first), and 

```math
D(\varepsilon) = \begin{pmatrix} 0 & \mathrm{diag}\,\varepsilon \\ -\mathrm{diag}\,\varepsilon & 0 \end{pmatrix}
```

for $`\varepsilon \in \mathbb R^n`$. A density matrix is a positive semidefinite matrix of trace $`1`$. The covariance of a matrix $`\rho`$ is the real matrix 

```math
\Gamma(\rho)_{ab} = \mathrm{Re}\,\tfrac i2 \mathrm{Tr}(\rho\,[c_a, c_b]);
```

with this sign the vacuum $`|0\cdots0\rangle`$ has covariance 

```math
\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}.
```

Admissible and pure covariances are as in the first part: $`\Gamma^T = -\Gamma`$ with $`1 - \Gamma^T\Gamma`$ positive semidefinite, respectively $`\Gamma^T = -\Gamma`$ with $`\Gamma^2 = -1`$. A unitary $`U`$ implements a real matrix $`O`$ on the labels when 

```math
U c_a U^* = \sum_b O_{ab} c_b
```

for every label $`a`$.

**41.** The index sets: the configurations of $`n`$ modes are the maps from $`\{0, \dots, n-1\}`$ to $`\{0, 1\}`$, and the Majorana labels of $`n`$ modes are two copies of $`\{0, \dots, n-1\}`$, the $`x`$-labels and then the $`y`$-labels.  
<sub>`Sealed.fock_labels`</sub>

**42.** The Jordan–Wigner Majorana operators of $`n`$ modes. For every mode $`j`$ and configurations $`s, t`$, the matrix entries are 

```math
\langle s|c_{x_j}|t\rangle = \prod_{k<j}(-1)^{s_k}
```

and 

```math
\langle s|c_{y_j}|t\rangle = -i\,(-1)^{s_j}\prod_{k<j}(-1)^{s_k}
```

when $`t = s^{(j)}`$, and $`0`$ otherwise.  
<sub>`Sealed.majorana_entries`</sub>

**43.** The canonical anticommutation relations: the Majorana operators are Hermitian, $`c_a^* = c_a`$, and 

```math
c_a c_b + c_b c_a = 2\delta_{ab}\,1
```

for all labels $`a, b`$.  
<sub>`Sealed.majorana_car`</sub>

**44.** Density matrices and the covariance of a state: $`\rho`$ is a density matrix exactly when it is positive semidefinite with $`\mathrm{Tr}\,\rho = 1`$; the covariance entry is 

```math
\Gamma(\rho)_{ab} = \mathrm{Re}\,\tfrac i2 \mathrm{Tr}(\rho\,(c_a c_b - c_b c_a));
```

and for Hermitian $`\rho`$ the number $`\tfrac i2 \mathrm{Tr}(\rho\,(c_a c_b - c_b c_a))`$ is real, equal to $`\Gamma(\rho)_{ab}`$.  
<sub>`Sealed.state_covariance`</sub>

**45.** The covariance of every matrix $`\rho`$ is antisymmetric, and for labels $`a \ne b`$ its entry is 

```math
\Gamma(\rho)_{ab} = \mathrm{Re}\,(i\,\mathrm{Tr}(\rho\, c_a c_b)).
```

The covariance of a density matrix is admissible.  
<sub>`Sealed.covariance_of_density`</sub>

**46.** Occupation-number states. For a configuration $`s`$ the state $`|s\rangle\langle s|`$ is the matrix with the single nonzero entry $`1`$ at $`(s, s)`$. It is a density matrix, its covariance is 

```math
\begin{pmatrix} 0 & D_s \\ -D_s & 0 \end{pmatrix}
```

with $`D_s`$ diagonal, $`(D_s)_{jj} = -1`$ if $`s_j = 0`$ and $`+1`$ if $`s_j = 1`$, and this covariance is pure. In particular the vacuum $`|0\cdots0\rangle`$ has covariance 

```math
\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}.
```  
<sub>`Sealed.occupation_state`</sub>

**47.** The bond state. Let 

```math
\psi = (|00\rangle + i\,|11\rangle)/\sqrt 2
```

on two modes, that is $`\psi_{00} = 1/\sqrt 2`$, $`\psi_{11} = i/\sqrt 2`$ and $`\psi_{01} = \psi_{10} = 0`$. Then $`|\psi\rangle\langle\psi|`$ is a density matrix, and its covariance has the nonzero entries 

```math
\Gamma_{x_0 x_1} = -\Gamma_{x_1 x_0} = 1
```

and 

```math
\Gamma_{y_0 y_1} = -\Gamma_{y_1 y_0} = -1.
```  
<sub>`Sealed.bond_state`</sub>

**48.** Conjugation by an implementing unitary. Let $`U`$ be a unitary on Fock space implementing a real matrix $`O`$. Then $`O`$ is orthogonal, $`O O^T = 1`$, and for every density matrix $`\rho`$ the matrix $`U \rho U^*`$ is a density matrix with covariance $`O^T \Gamma(\rho)\, O`$.  
<sub>`Sealed.unitary_conjugation`</sub>

**49.** Hopping gates. For modes $`j \ne k`$ and $`\varphi \in \mathbb R`$ let 

```math
U = (\cos\varphi + \sin\varphi\, c_{x_j} c_{x_k})(\cos\varphi + \sin\varphi\, c_{y_j} c_{y_k}).
```

Then $`U`$ is unitary; with $`\theta = 2\varphi`$ it acts on the Majorana operators by 

```math
U c_{x_j} U^* = \cos\theta\, c_{x_j} - \sin\theta\, c_{x_k},
```



```math
U c_{x_k} U^* = \sin\theta\, c_{x_j} + \cos\theta\, c_{x_k},
```

the same formulas with $`y`$ in place of $`x`$, and $`U c_a U^* = c_a`$ for the labels $`a`$ of every other mode. On two modes, with $`j = 0`$ and $`k = 1`$, the state $`U |10\rangle\langle 10| U^*`$ (mode $`0`$ occupied) has covariance 

```math
\begin{pmatrix} 0 & X \\ -X^T & 0 \end{pmatrix}
```

with 

```math
X = \begin{pmatrix} \cos 4\varphi & -\sin 4\varphi \\ -\sin 4\varphi & -\cos 4\varphi \end{pmatrix}.
```  
<sub>`Sealed.hopping_gate`</sub>

## Quadratic Hamiltonians and ground states

For a real matrix $`h`$ on the Majorana labels of $`n`$ modes the quadratic Hamiltonian is 

```math
H_h = \tfrac i4 \sum_{a,b} h_{ab}\, c_a c_b,
```

and the energy of a matrix $`\rho`$ is $`E_h(\rho) = \mathrm{Re}\,\mathrm{Tr}(\rho H_h)`$. On real matrices $`\Gamma`$ on the labels the energy form is $`\tfrac14 \sum_{a,b} h_{ab}\Gamma_{ab}`$. A normal form of $`h`$ is a factorization $`h = O D(\varepsilon) O^T`$ with $`O`$ real orthogonal and $`\varepsilon \in \mathbb R^n`$.

**50.** Quadratic Hamiltonians. For every real $`h`$, 

```math
H_h = \sum_{a,b} \tfrac i4 h_{ab}\, c_a c_b
```

and $`E_h(\rho) = \mathrm{Re}\,\mathrm{Tr}(\rho H_h)`$. If $`h^T = -h`$, then $`H_h`$ is Hermitian; for Hermitian $`\rho`$ the trace $`\mathrm{Tr}(\rho H_h)`$ is real and equals $`\tfrac14\sum_{a,b} h_{ab}\Gamma(\rho)_{ab}`$; and the generator identity 

```math
i\,[H_h, c_a] = \sum_b h_{ab} c_b
```

holds. For every $`h`$, a unitary $`U`$ implementing a real matrix $`O`$ satisfies $`U H_h U^* = H_{O^T h O}`$.  
<sub>`Sealed.quadratic_hamiltonian`</sub>

**51.** The Hamiltonian of $`D(\varepsilon)`$ is diagonal in the occupation basis: 

```math
\langle s|H_{D(\varepsilon)}|s\rangle = \sum_j \varepsilon_j (s_j - \tfrac12)
```

for every configuration $`s`$, and all off-diagonal entries vanish.  
<sub>`Sealed.block_hamiltonian`</sub>

**52.** Ground states in a normal form. Let $`h = O D(\varepsilon) O^T`$ with $`O`$ orthogonal, let $`U`$ be a unitary implementing $`O`$, let $`s^\varepsilon`$ be the configuration with $`s^\varepsilon_j = 1`$ exactly when $`\varepsilon_j < 0`$, let $`\rho_0 = U^* |s^\varepsilon\rangle\langle s^\varepsilon| U`$ and 

```math
E_0 = -\tfrac12\sum_j|\varepsilon_j|.
```

Then $`E_h(\rho) \ge E_0`$ for every density matrix $`\rho`$; $`\rho_0`$ is a density matrix with $`E_h(\rho_0) = E_0`$; its covariance is $`O D(\eta) O^T`$ with $`\eta_j = 1`$ if $`\varepsilon_j < 0`$ and $`\eta_j = -1`$ otherwise, and is pure. If moreover every $`\varepsilon_j \ne 0`$, then $`\rho_0`$ is the only density matrix with energy $`E_0`$, the energy form satisfies 

```math
\tfrac14\sum_{a,b} h_{ab}\Gamma_{ab} \ge E_0
```

for admissible $`\Gamma`$, and for admissible $`\Gamma`$ equality holds exactly when $`\Gamma = \Gamma(\rho_0)`$.  
<sub>`Sealed.normal_form_ground`</sub>

**53.** Every quadratic Hamiltonian has a pure ground state. For every real $`h`$ with $`h^T = -h`$ there are a special orthogonal $`O`$ ($`O O^T = 1`$, $`\det O = 1`$), a vector $`\varepsilon`$ with $`h = O D(\varepsilon) O^T`$, and a unitary $`U`$ implementing $`O`$; and there is a density matrix $`\rho_0`$ with pure covariance and $`E_h(\rho_0) \le E_h(\rho)`$ for every density matrix $`\rho`$.  
<sub>`Sealed.ground_state_exists`</sub>

## Realization

A real matrix $`\Gamma`$ on the labels is realized by a density matrix $`\rho`$ when $`\Gamma(\rho) = \Gamma`$. For $`\lambda \in \mathbb R^n`$ the product mixture is 

```math
\rho_\lambda = \sum_s \prod_j p_j(s_j)\, |s\rangle\langle s|
```

with $`p_j(0) = (1 - \lambda_j)/2`$ and $`p_j(1) = (1 + \lambda_j)/2`$.

**54.** Implementing unitaries exist: for every real matrix $`O`$ on the labels with $`O O^T = 1`$ and $`\det O = 1`$ there is a unitary $`U`$ on Fock space implementing $`O`$.  
<sub>`Sealed.special_orthogonal_unitary`</sub>

**55.** Product mixtures. For every $`\lambda \in \mathbb R^n`$, 

```math
\rho_\lambda = \sum_s \prod_j p_j(s_j)\,|s\rangle\langle s|
```

has covariance $`D(\lambda)`$; if every $`|\lambda_j| \le 1`$ it is a density matrix; and if every $`|\lambda_j| = 1`$ it is the occupation state $`|s\rangle\langle s|`$ with $`s_j = 1`$ exactly when $`\lambda_j = 1`$.  
<sub>`Sealed.product_mixture`</sub>

**56.** Realization of covariances. If $`\Gamma = O D(\varepsilon) O^T`$ is admissible, $`O`$ is orthogonal and $`U`$ is a unitary implementing $`O`$, then $`U^* \rho_\varepsilon U`$ is a density matrix with covariance $`\Gamma`$. Every admissible $`\Gamma`$ is the covariance of a density matrix. Every pure $`\Gamma`$ is the covariance of a density matrix $`U^*|s\rangle\langle s|U`$ with $`U`$ unitary and $`s`$ a configuration. Two density matrices with the same pure covariance $`\Gamma`$ are equal.  
<sub>`Sealed.covariance_realization`</sub>

## Thermal states and evolution

$`e^X`$ is the exponential of a square matrix $`X`$. For a real matrix $`h`$ on the labels the exponential state is 

```math
\rho_h = e^{-H_h} / \mathrm{Tr}\, e^{-H_h},
```

the thermal state at inverse temperature $`\beta \in \mathbb R`$ is $`\rho_{\beta h}`$, and the evolution operator is $`U_h(t) = e^{-itH_h}`$ for $`t \in \mathbb R`$. A real matrix $`\Gamma`$ on the labels is strictly admissible when $`\Gamma^T = -\Gamma`$ and $`1 - \Gamma^T\Gamma`$ is positive definite.

**57.** The exponential and thermal states: 

```math
\rho_h = (\mathrm{Tr}\,e^{-H_h})^{-1} e^{-H_h},
```

and the thermal state of $`H_h`$ at inverse temperature $`\beta`$ is $`\rho_{\beta h}`$.  
<sub>`Sealed.exponential_state_def`</sub>

**58.** Strict admissibility: $`\Gamma`$ is strictly admissible exactly when $`\Gamma^T = -\Gamma`$ and $`1 - \Gamma^T\Gamma`$ is positive definite; a strictly admissible matrix is admissible; and $`D(\lambda)`$ is strictly admissible exactly when every $`|\lambda_j| < 1`$.  
<sub>`Sealed.strictly_admissible`</sub>

**59.** Exponential states. Let $`h^T = -h`$. Then $`\mathrm{Tr}\,e^{-H_h}`$ is a positive real number and $`\rho_h`$ is a density matrix. There are a special orthogonal $`O`$ and a vector $`\varepsilon`$ with $`h = O D(\varepsilon) O^T`$ and $`\Gamma(\rho_h) = O D(-\tanh(\varepsilon/2)) O^T`$, the hyperbolic tangent taken entrywise. The covariance $`\Gamma(\rho_h)`$ is strictly admissible, and for $`n \ge 1`$ it is not pure.  
<sub>`Sealed.exponential_state`</sub>

**60.** Thermal states in a normal form. Let $`h = O D(\varepsilon) O^T`$ with $`O`$ orthogonal and let $`U`$ be a unitary implementing $`O`$. Then 

```math
\mathrm{Tr}\,e^{-H_h} = \prod_j 2\cosh(\varepsilon_j/2),
```

and for every $`\beta \in \mathbb R`$ the thermal state $`\rho_{\beta h}`$ is a density matrix with covariance $`O D(-\tanh(\beta\varepsilon/2)) O^T`$ and energy 

```math
E_h(\rho_{\beta h}) = -\tfrac12\sum_j \varepsilon_j \tanh(\beta\varepsilon_j/2).
```  
<sub>`Sealed.thermal_state`</sub>

**61.** Realization by exponential states. Every strictly admissible $`\Gamma`$ is the covariance of an exponential state $`\rho_h`$ with $`h^T = -h`$. Two exponential states $`\rho_h, \rho_{h'}`$ ($`h^T = -h`$, $`h'^T = -h'`$) with the same covariance are equal. If $`O`$ is orthogonal, $`U`$ is a unitary implementing $`O`$ and every $`|\eta_j| < 1`$, then $`h = O D(-2\,\mathrm{artanh}\,\eta) O^T`$ has $`\Gamma(\rho_h) = O D(\eta) O^T`$. The exponential state of $`h = 0`$ is the maximally mixed state $`2^{-n}\,1`$, with covariance $`0`$.  
<sub>`Sealed.exponential_realization`</sub>

**62.** Time evolution. Let $`h^T = -h`$ and $`s, t \in \mathbb R`$. Then $`U_h(t) = e^{-itH_h}`$ is unitary, $`U_h(t)^* = U_h(-t)`$ and $`U_h(s) U_h(t) = U_h(s + t)`$; $`U_h(t)`$ implements the real matrix $`e^{-th}`$, that is 

```math
U_h(t) c_a U_h(t)^* = \sum_b (e^{-th})_{ab} c_b;
```

for every density matrix $`\sigma`$ the matrix $`U_h(t)\sigma U_h(t)^*`$ is a density matrix with covariance $`e^{th}\,\Gamma(\sigma)\,e^{-th}`$; and the exponential state is stationary, $`U_h(t) \rho_h U_h(t)^* = \rho_h`$.  
<sub>`Sealed.time_evolution`</sub>

## Wick's theorem and the Gaussian class

For a complex vector $`v`$ on the labels, 

```math
v \cdot c = \sum_a v_a c_a,
```

and 

```math
v^T G w = \sum_{a,b} v_a G_{ab} w_b
```

(no complex conjugation). The two-point matrix of $`\rho`$ is the complex matrix $`G(\rho) = 1 - i\,\Gamma(\rho)`$. Lists $`(w_0, \dots, w_{k-1})`$ of vectors are indexed from $`0`$, and a hat marks an omitted factor. A Gaussian state is a density matrix whose moments obey Wick's rule in the recursive form of the first entry below.

**63.** The Gaussian class. A matrix $`\rho`$ is Gaussian exactly when it is a density matrix and, with $`G = G(\rho)`$, for every vector $`v`$ and every list $`(w_0, \dots, w_{k-1})`$, 

```math
\mathrm{Tr}(\rho\,(v\cdot c)(w_0\cdot c)\cdots(w_{k-1}\cdot c)) = \sum_{j<k} (-1)^j\, (v^T G w_j)\, \mathrm{Tr}(\rho\,(w_0\cdot c)\cdots\widehat{(w_j\cdot c)}\cdots (w_{k-1}\cdot c)).
```  
<sub>`Sealed.gaussian_iff`</sub>

**64.** Order two. For complex vectors $`v, w`$ on the labels, 

```math
(v\cdot c)(w\cdot c) + (w\cdot c)(v\cdot c) = 2\,(v^T w)\,1,
```

and every density matrix $`\rho`$ satisfies 

```math
\mathrm{Tr}(\rho\,(v\cdot c)(w\cdot c)) = v^T G(\rho)\, w.
```  
<sub>`Sealed.two_point_moment`</sub>

**65.** The relation form of the Gaussian class. A matrix $`\rho`$ is Gaussian exactly when it is a density matrix, 

```math
\mathrm{Tr}(\rho\,(w_0\cdot c)\cdots(w_{k-1}\cdot c)) = 0
```

for every list of odd length $`k`$, and, with $`G = G(\rho)`$, 

```math
((G^T v)\cdot c)\,\rho = \rho\,((G v)\cdot c)
```

for every vector $`v`$.  
<sub>`Sealed.gaussian_relation`</sub>

**66.** Examples of Gaussian states: the product mixtures $`\rho_\lambda`$ with every $`|\lambda_j| \le 1`$; the occupation states $`|s\rangle\langle s|`$; for $`h^T = -h`$ the exponential state $`\rho_h`$ and every thermal state $`\rho_{\beta h}`$, $`\beta \in \mathbb R`$. If $`U`$ is a unitary implementing a real matrix $`O`$ and $`\rho`$ is Gaussian, then $`U^* \rho U`$ is Gaussian.  
<sub>`Sealed.gaussian_examples`</sub>

**67.** Gaussian states and their covariances. Every admissible $`\Gamma`$ is the covariance of a Gaussian state, and two Gaussian states with the same covariance are equal. Every Gaussian state $`\rho`$ has the form $`\rho = U^* \rho_\varepsilon U`$ with $`U`$ a unitary implementing an orthogonal $`O`$, every $`|\varepsilon_j| \le 1`$ and $`\Gamma(\rho) = O D(\varepsilon) O^T`$. A Gaussian state with strictly admissible covariance is an exponential state $`\rho_h`$ with $`h^T = -h`$.  
<sub>`Sealed.gaussian_covariance`</sub>

**68.** The Majorana monomials. For a set $`S`$ of labels, $`c_S`$ is the product of the $`c_a`$, $`a \in S`$, in the order 

```math
x_0 < \dots < x_{n-1} < y_0 < \dots < y_{n-1}
```

(so $`c_\emptyset = 1`$). For all sets $`S, T`$ of labels, $`\mathrm{Tr}(c_S^* c_T) = 2^n`$ if $`S = T`$ and $`0`$ otherwise; the monomials, indexed by the sets of labels, are linearly independent over $`\mathbb C`$; every complex matrix $`A`$ on Fock space equals $`2^{-n}\sum_S \mathrm{Tr}(A c_S^*)\, c_S`$; and two matrices $`A, B`$ with $`\mathrm{Tr}(A c_S) = \mathrm{Tr}(B c_S)`$ for every $`S`$ are equal.  
<sub>`Sealed.majorana_monomials`</sub>

## Partial trace and contraction of Gaussian states, the chain state

A configuration of $`n + m`$ modes is written $`(s, u)`$, with $`s \in \{0,1\}^n`$ its first $`n`$ bits (the retained modes) and $`u \in \{0,1\}^m`$ its last $`m`$ bits (the eliminated modes). The retained Majorana labels are $`x_j, y_j`$ for $`j < n`$ and the eliminated ones $`x_{n+j}, y_{n+j}`$ for $`j < m`$; for a real matrix $`\Gamma`$ on the labels of $`n + m`$ modes, $`A`$, $`B`$, $`C`$, $`D`$ are its retained–retained, retained–eliminated, eliminated–retained and eliminated–eliminated blocks, each with the $`x`$-labels before the $`y`$-labels. $`\mathrm{Tr}_E`$ and $`\mathrm{Tr}_R`$ are the partial traces over the eliminated and over the retained modes, and $`X \otimes Y`$ is the tensor product of a matrix $`X`$ on $`n`$ modes with a matrix $`Y`$ on $`m`$ modes. The contraction of a matrix $`\rho`$ on $`n + m`$ modes with a matrix $`\sigma`$ on $`m`$ modes has normalization $`Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma))`$ and is the matrix $`Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))`$ on $`n`$ modes.

**69.** The partial traces and the tensor product: for matrices $`M`$ on $`n + m`$ modes, $`X`$ on $`n`$ modes and $`Y`$ on $`m`$ modes and for all configurations, 

```math
\mathrm{Tr}_E(M)_{st} = \sum_w M_{(s,w),(t,w)},
```



```math
\mathrm{Tr}_R(M)_{uv} = \sum_w M_{(w,u),(w,v)}
```

and 

```math
(X \otimes Y)_{(s,u),(t,v)} = X_{st}\,Y_{uv}.
```  
<sub>`Sealed.partial_trace`</sub>

**70.** Marginals. For every matrix $`\rho`$ on $`n + m`$ modes, the covariance of $`\mathrm{Tr}_E\rho`$ is the retained block $`A`$ of $`\Gamma(\rho)`$ and the covariance of $`\mathrm{Tr}_R\rho`$ is the eliminated block $`D`$. If $`\rho`$ is a density matrix, so are both marginals; if $`\rho`$ is Gaussian, so are both marginals.  
<sub>`Sealed.gaussian_marginal`</sub>

**71.** Contraction of Gaussian states. For positive semidefinite $`\rho`$ on $`n + m`$ modes and $`\sigma`$ on $`m`$ modes with $`Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma)) \ne 0`$, the contraction $`Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))`$ is a density matrix. Let $`\rho`$ and $`\sigma`$ be Gaussian, with $`A, B, C, D`$ the blocks of $`\Gamma(\rho)`$ and $`\beta = \Gamma(\sigma)`$, and let $`1 - D\beta`$ be invertible. Then $`Z`$ is a positive real number, the contraction is Gaussian, and its covariance is $`A + B\beta(1 - D\beta)^{-1}C`$.  
<sub>`Sealed.gaussian_contraction`</sub>

**72.** The chain state. Let $`\Gamma_0, \dots, \Gamma_{N-1}`$ be admissible covariances of single sites with $`P`$ physical and $`2M`$ virtual modes, let $`\Gamma_{\mathrm{in}}`$, $`\beta_N`$ and $`\Gamma_N`$ be the periodic input, bond and periodic covariances of the chain built from them (defined in the first part), and let the invertibility condition of the contraction of $`\Gamma_{\mathrm{in}}`$ with $`\beta_N`$ (also defined there) hold. Number the modes of the chain as follows: physical mode $`c`$ of site $`i`$ is mode $`iP + c`$; the $`N M`$ virtual modes $`L`$ follow, $`(i, a)`$ being mode $`NP + iM + a`$; then the $`N M`$ virtual modes $`L'`$, $`(i, b)`$ being mode $`NP + NM + iM + b`$. On the $`2NM`$ virtual modes alone, $`L`$ is numbered $`(i, a) \mapsto iM + a`$ and $`L'`$ is numbered $`(i, b) \mapsto NM + iM + b`$. Then there are Gaussian states $`\rho`$ on all $`NP + 2NM`$ modes and $`\sigma`$ on the $`2NM`$ virtual modes whose covariances, read in this numbering, are $`\Gamma_{\mathrm{in}}`$ and $`\beta_N`$. For any such $`\rho`$ and $`\sigma`$, the normalization $`Z = \mathrm{Tr}(\rho\,(1 \otimes \sigma))`$ is a positive real number, the contraction 

```math
\tau = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))
```

on the $`NP`$ physical modes is Gaussian, its covariance, read in the numbering $`iP + c`$, is $`\Gamma_N`$, and if every $`\Gamma_i`$ is pure then $`\tau^2 = \tau`$.  
<sub>`Sealed.chain_state`</sub>

## Purity and the Kitaev ground state

For a pure $`\Gamma`$ on the labels of $`n`$ modes, $`H_{-\Gamma}`$ is the quadratic Hamiltonian of $`-\Gamma`$. The Kitaev chain has $`N`$ sites with one mode each; mode $`i`$ has the labels $`x_i, y_i`$, and $`i + 1`$ is taken modulo $`N`$. The Kitaev covariance $`K`$ is the real matrix on these labels with $`K_{y_i x_{i+1}} = 1`$, $`K_{x_{i+1} y_i} = -1`$ and all other entries $`0`$.

**73.** Gaussian projections: a Gaussian state $`\rho`$ satisfies $`\rho^2 = \rho`$ exactly when its covariance is pure, and then $`\rho = |\psi\rangle\langle\psi|`$ for a vector $`\psi`$.  
<sub>`Sealed.gaussian_projection`</sub>

**74.** Contraction of pure Gaussian states. Let $`\rho`$ on $`n + m`$ modes and $`\sigma`$ on $`m`$ modes be Gaussian with pure covariances, and let $`1 - D\beta`$ be invertible, with $`D`$ the eliminated block of $`\Gamma(\rho)`$ and $`\beta = \Gamma(\sigma)`$. Then the contraction 

```math
\tau = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))
```

satisfies $`\tau^2 = \tau`$ and its covariance is pure.  
<sub>`Sealed.pure_contracted_state`</sub>

**75.** Ground states of pure covariances. For every pure $`\Gamma`$ on the labels of $`n`$ modes there is a Gaussian state $`\rho_0`$ with covariance $`\Gamma`$ such that $`E_{-\Gamma}(\rho_0) = -n/2`$, $`E_{-\Gamma}(\rho) \ge -n/2`$ for every density matrix $`\rho`$, and every density matrix with $`E_{-\Gamma}(\rho) = -n/2`$ equals $`\rho_0`$; on covariances, 

```math
-\tfrac14\sum_{a,b}\Gamma_{ab}\Gamma'_{ab} \ge -n/2
```

for every admissible $`\Gamma'`$, with equality exactly when $`\Gamma' = \Gamma`$.  
<sub>`Sealed.pure_ground_state`</sub>

**76.** The Kitaev covariance and Hamiltonian. On the labels of the $`N`$ modes of the Kitaev chain, for all $`i, j`$: $`K_{x_i x_j} = K_{y_i y_j} = 0`$, $`K_{y_i x_j} = 1`$ if $`j = i + 1`$ and $`0`$ otherwise, and $`K_{x_j y_i} = -1`$ if $`j = i + 1`$ and $`0`$ otherwise. The matrix $`K`$ is pure, and 

```math
H_{-K} = \tfrac i2 \sum_i c_{x_{i+1}} c_{y_i}.
```  
<sub>`Sealed.kitaev_hamiltonian`</sub>

**77.** The Kitaev ground state as a chain state. Let $`N \ge 1`$, and take the chain of $`N`$ sites with $`P = 1`$ physical and $`2M = 2`$ virtual modes per site, every site carrying the Kitaev local covariance (defined in the first part), with the numbering of the modes of the chain-state entry. Then there are Gaussian states $`\rho`$ and $`\sigma`$ whose covariances, in this numbering, are the periodic input and bond covariances. For any such $`\rho`$ and $`\sigma`$ the contraction 

```math
\rho_K = Z^{-1}\,\mathrm{Tr}_E(\rho\,(1 \otimes \sigma))
```

is Gaussian with covariance $`K`$, satisfies $`\rho_K^2 = \rho_K`$, has energy $`E_{-K}(\rho_K) = -N/2`$, and is the unique ground state of $`H_{-K}`$: $`E_{-K}(\rho') \ge -N/2`$ for every density matrix $`\rho'`$, and every density matrix with $`E_{-K}(\rho') = -N/2`$ equals $`\rho_K`$.  
<sub>`Sealed.kitaev_ground_state`</sub>

## The gap

For a pure $`\Gamma`$ the Hamiltonian $`H_{-\Gamma}`$ has ground energy $`-n/2`$ and a unique ground state (previous section). The statements below bound the energy of density matrices orthogonal to the ground state, orthogonality of $`\rho`$ and $`\rho_0`$ meaning $`\mathrm{Tr}(\rho\,\rho_0) = 0`$.

**78.** The gap of $`H_{-\Gamma}`$. Let $`\Gamma`$ be pure and let $`\rho_0`$ be a Gaussian state with covariance $`\Gamma`$. Every density matrix $`\rho`$ with $`\mathrm{Tr}(\rho\,\rho_0) = 0`$ has $`E_{-\Gamma}(\rho) \ge -n/2 + 1`$, and for $`n \ge 1`$ some density matrix $`\rho'`$ with $`\mathrm{Tr}(\rho'\rho_0) = 0`$ has $`E_{-\Gamma}(\rho') = -n/2 + 1`$.  
<sub>`Sealed.pure_gap`</sub>

**79.** The gap of the Kitaev chain. Let $`N \ge 1`$ and let $`\rho_K`$ be a density matrix on the $`N`$ modes of the Kitaev chain with $`E_{-K}(\rho_K) = -N/2`$. Every density matrix $`\rho`$ with $`\mathrm{Tr}(\rho\,\rho_K) = 0`$ has $`E_{-K}(\rho) \ge -N/2 + 1`$, and some density matrix $`\rho'`$ with $`\mathrm{Tr}(\rho'\rho_K) = 0`$ has $`E_{-K}(\rho') = -N/2 + 1`$.  
<sub>`Sealed.kitaev_gap`</sub>

---

SHA-256 of `verify/Challenge.lean` (LF line endings): `5b7362f7b9711f2eb83508704fe46c39e883cf053fc262965cf2eacc7c90199a`
