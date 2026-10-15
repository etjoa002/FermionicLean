"""The normalization of a contraction of Gaussian states (notes, Remark "rem:overlap").

The remark states, without proof, N(rho, sigma) = tr(rho (1 (x) sigma)) = 2^{-m} sqrt(det(1 - D beta)),
for rho Gaussian on n + m modes with covariance [[A, B], [C, D]] (D on the m eliminated modes) and
sigma Gaussian on m modes with covariance beta, and says it is verified numerically for n + m <= 4.
This script is that check, in floating point with NumPy, on Fock space built from the
Jordan-Wigner operators of the notes (c_{x_j} = Z_{<j} X_j, c_{y_j} = i Z_{<j} X_j Z_j, mode 1 the
first tensor factor, labels (x_1..x_N, y_1..y_N)), with Gamma_jk = Re((i/2) tr(rho [c_j, c_k])).

For every (n, m) with n + m <= 4 and m >= 1 it draws (seeded) Gaussian states of three kinds:
thermal states exp(-H)/Z and ground states of random quadratic Hamiltonians
H = (i/4) sum_ab W_ab c_a c_b, and, for sigma on m = 2 modes, the bond state (|00> + i|11>)/sqrt 2.
It checks, with absolute tolerance 1e-12 (all quantities are of order 1):
  (a) det(1 - D beta) is real and >= 0, and N(rho, sigma) = 2^{-m} sqrt(det(1 - D beta));
  (b) as a check of the conventions, the covariance of N^{-1} rho * sigma equals
      Gamma * beta = A + B beta (1 - D beta)^{-1} C (the proved Corollary "cor:contract-state").
Degenerate inputs: m = 0 (N = tr rho = 1), n = 0 (the overlap tr(rho sigma) of two Gaussian
states), and a singular case (eliminated modes of rho empty, sigma fully occupied: both sides 0).
Prints its results and writes no files. Requires NumPy.
"""
import itertools

import numpy as np

TOL = 1e-12
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)
I2 = np.eye(2, dtype=complex)


def kron(ms):
    out = np.eye(1, dtype=complex)
    for m in ms:
        out = np.kron(out, m)
    return out


def majoranas(N):
    """[c_{x_1}, ..., c_{x_N}, c_{y_1}, ..., c_{y_N}] on (C^2)^{(x) N}."""
    cx = [kron([Z] * j + [X] + [I2] * (N - j - 1)) for j in range(N)]
    cy = [kron([Z] * j + [1j * X @ Z] + [I2] * (N - j - 1)) for j in range(N)]
    return cx + cy


def covariance(rho, c):
    n2 = len(c)
    G = np.zeros((n2, n2))
    for a in range(n2):
        for b in range(n2):
            G[a, b] = (0.5j * np.trace(rho @ (c[a] @ c[b] - c[b] @ c[a]))).real
    return G


def quadratic(W, c):
    return sum(0.25j * W[a, b] * c[a] @ c[b] for a in range(len(c)) for b in range(len(c)))


def random_state(N, kind, rng, c):
    if N == 0:
        return np.eye(1, dtype=complex)
    W = rng.normal(size=(2 * N, 2 * N))
    W = W - W.T
    H = quadratic(W, c)
    H = (H + H.conj().T) / 2
    e, V = np.linalg.eigh(H)
    if kind == "thermal":
        w = np.exp(-(e - e[0]))
        rho = (V * w) @ V.conj().T
        return rho / np.trace(rho).real
    assert e[1] - e[0] > 1e-6, "ground state degenerate"
    v = V[:, 0]
    return np.outer(v, v.conj())


def bond_state():
    psi = np.zeros(4, dtype=complex)
    psi[0], psi[3] = 1, 1j
    psi /= np.sqrt(2)
    return np.outer(psi, psi.conj())


def labels(n, m):
    """Retained labels R and eliminated labels E inside (x_1..x_{n+m}, y_1..y_{n+m})."""
    N = n + m
    R = list(range(n)) + [N + j for j in range(n)]
    E = [n + j for j in range(m)] + [N + n + j for j in range(m)]
    return R, E


def check(n, m, rho, sigma, cN, cn, cm):
    Gam = covariance(rho, cN)
    beta = covariance(sigma, cm) if m else np.zeros((0, 0))
    R, E = labels(n, m)
    A, B = Gam[np.ix_(R, R)], Gam[np.ix_(R, E)]
    C, D = Gam[np.ix_(E, R)], Gam[np.ix_(E, E)]
    M = np.eye(2 * m) - D @ beta
    dM = np.linalg.det(M) if m else 1.0
    big = np.kron(np.eye(2 ** n), sigma)
    prod = rho @ big
    Nval = np.trace(prod)
    assert abs(Nval.imag) < TOL and abs(np.imag(dM)) < TOL and dM.real > -TOL
    singular = abs(dM) < 1e-9
    # det(1 - D beta) = 0 exactly when N = 0 (pure rho and sigma of opposite parity on E, say)
    assert singular == (abs(Nval) < TOL), (n, m, Nval, dM)
    pred = 0.0 if singular else 2.0 ** (-m) * np.sqrt(dM.real)
    dev = abs(Nval.real - pred)
    assert dev < TOL, (n, m, Nval, pred)
    cdev = 0.0
    if abs(dM) > 1e-8 and n > 0:
        red = np.einsum("iaja->ij", prod.reshape(2 ** n, 2 ** m, 2 ** n, 2 ** m))  # partial trace over E
        Gout = covariance(red / Nval.real, cn)
        Gstar = A + B @ beta @ np.linalg.solve(M, C) if m else A
        cdev = np.max(np.abs(Gout - Gstar))
        assert cdev < 1e-10, (n, m, cdev)
    return Nval.real, dM.real, dev, cdev


rng = np.random.default_rng(20261015)
print(f"tolerance: |N - 2^-m sqrt det(1 - D beta)| < {TOL:g}; covariance of the contracted state to 1e-10")
total = 0
for N in range(1, 5):
    for m in range(1, N + 1):
        n = N - m
        cN, cn, cm = majoranas(N), majoranas(n) if n else [], majoranas(m)
        kinds_s = ["thermal", "ground"] + (["bond"] if m == 2 else [])
        count, nsing, Nmin = 0, 0, 1.0
        for kr, ks in itertools.product(["thermal", "ground"], kinds_s):
            for _ in range(3):
                rho = random_state(N, kr, rng, cN)
                sigma = bond_state() if ks == "bond" else random_state(m, ks, rng, cm)
                Nval, dM, dev, cdev = check(n, m, rho, sigma, cN, cn, cm)
                if abs(dM) < 1e-9:
                    nsing += 1
                else:
                    Nmin = min(Nmin, Nval)
                count += 1
        total += count
        print(f"   n={n} m={m}: {count} pairs (rho thermal/ground x sigma {'/'.join(kinds_s)}) pass; "
              f"{nsing} with det(1 - D beta) = 0 = N; smallest nonzero N = {Nmin:.3f}")

print("\n=== degenerate inputs")
for N in (1, 2, 3):
    cN = majoranas(N)
    rho = random_state(N, "thermal", rng, cN)
    Nval, dM, dev, _ = check(N, 0, rho, np.eye(1, dtype=complex), cN, cN, [])
    assert abs(Nval - 1) < TOL and dM == 1.0
print("   m = 0 (nothing eliminated): N = tr rho = 1 = 2^0 sqrt(det of the empty matrix), N = 1, 2, 3")
print("   n = 0 (the overlap tr(rho sigma)) is included above as the rows n=0")
# singular: rho with its eliminated mode empty (D = -Omega_1 on E), sigma = |1><1| (beta = Omega_1)
for n in (0, 1, 2):
    N = n + 1
    cN, cn, cm = majoranas(N), majoranas(n) if n else [], majoranas(1)
    rhoR = random_state(n, "thermal", rng, cn) if n else np.eye(1, dtype=complex)
    rho = np.kron(rhoR, np.diag([1, 0]).astype(complex))
    sigma = np.diag([0, 1]).astype(complex)
    Nval, dM, dev, _ = check(n, 1, rho, sigma, cN, cn, cm)
    assert abs(Nval) < TOL and abs(dM) < TOL
print("   rho empty on the eliminated mode, sigma occupied: det(1 - D beta) = 0 and N = 0, n = 0, 1, 2")
print(f"\nall {total} pairs and the degenerate cases pass")
