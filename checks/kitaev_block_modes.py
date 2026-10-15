"""Entangled modes of a block of sites (notes, Remark "rem:kitaev-block" after Corollary "cor:ent-rank").

The remark is not checked in Lean. This script checks it in exact rational arithmetic (Python's
fractions; no floating point, no third-party package):

 1. Kitaev chain, Gamma_N = K_N ((K_N)_{y_i x_(i+1)} = 1, (K_N)_{x_(i+1) y_i} = -1), N = 2..9, every
    block S of k consecutive sites, 1 <= k <= N-1, at every starting site: the rows and columns of
    x_first and y_last of Gamma_S vanish; Gamma_S^T Gamma_S is the projector onto the other 2(k-1)
    labels (so k-1 normal modes with |lambda| = 1 and one with lambda = 0); the number of entangled
    modes (1/2) rank(1 + Gamma_S^2) is exactly 1, below M b(S) = 2; rank C_S = 2. K_N is also
    rebuilt by the chain construction from the on-site Kitaev covariance, as a cross-check.
 2. Generic pure on-site covariances: Gamma_site = O (-Omega) O^T with O a rational rotation (Cayley
    transform of a seeded random integer antisymmetric matrix), for (M, P) = (1, 1), (1, 2), (2, 1)
    and N = 2..6. For every block of k consecutive sites the number of entangled modes is compared
    with min(M b(S), P k, P (N-k)): the bound M b(S) = 2M can be attained only when the block and
    its complement each hold at least that many physical modes.
 3. Degenerate inputs: N = 1, the empty block and the whole ring (no entangled modes).

Conventions as in the notes: labels (x_A, x_B, x_C, y_A, y_B, y_C) per site, input matrix
relabelled with x^L_(i,a) = x_(A_i,a), x^L'_(i,a) = x_(B_(i-1),a), bonds (beta_N)_{x^L x^L'} = 1,
(beta_N)_{y^L y^L'} = -1, Gamma_N = A + B beta_N (1 - D beta_N)^{-1} C. Prints its results and
writes no files.
"""
import random
from fractions import Fraction as F

# ---------------------------------------------------------------- exact matrix helpers


def zeros(n, m=None):
    return [[F(0)] * (n if m is None else m) for _ in range(n)]


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mul(X, Y):
    Yt = list(zip(*Y))
    return [[sum((a * b for a, b in zip(r, c)), F(0)) for c in Yt] for r in X]


def add(X, Y):
    return [[a + b for a, b in zip(r, s)] for r, s in zip(X, Y)]


def sub(X, Y):
    return [[a - b for a, b in zip(r, s)] for r, s in zip(X, Y)]


def neg(X):
    return [[-a for a in r] for r in X]


def tr(X):
    return [list(r) for r in zip(*X)]


def sel(X, rows, cols):
    return [[X[i][j] for j in cols] for i in rows]


def rank(X):
    X = [list(r) for r in X]
    if not X or not X[0]:
        return 0
    rk, ncol = 0, len(X[0])
    for k in range(ncol):
        p = next((i for i in range(rk, len(X)) if X[i][k] != 0), None)
        if p is None:
            continue
        X[rk], X[p] = X[p], X[rk]
        for i in range(len(X)):
            if i != rk and X[i][k] != 0:
                f = X[i][k] / X[rk][k]
                X[i] = [a - f * b for a, b in zip(X[i], X[rk])]
        rk += 1
    return rk


def inv(X):
    n = len(X)
    A = [list(r) + e for r, e in zip(X, eye(n))]
    for k in range(n):
        p = next((i for i in range(k, n) if A[i][k] != 0), None)
        if p is None:
            return None
        A[k], A[p] = A[p], A[k]
        piv = A[k][k]
        A[k] = [a / piv for a in A[k]]
        for i in range(n):
            if i != k and A[i][k] != 0:
                f = A[i][k]
                A[i] = [a - f * b for a, b in zip(A[i], A[k])]
    return [r[n:] for r in A]


def is_pure(G):
    return tr(G) == neg(G) and mul(G, G) == neg(eye(len(G)))


# ---------------------------------------------------------------- the chain construction


def site_index(M, P):
    """Site labels (x_A[M], x_B[M], x_C[P], y_A[M], y_B[M], y_C[P]) -> 0..2(2M+P)-1."""
    d = 2 * M + P
    return {("xA", a): a for a in range(M)} | {("xB", a): M + a for a in range(M)} | \
        {("xC", c): 2 * M + c for c in range(P)} | {("yA", a): d + a for a in range(M)} | \
        {("yB", a): d + M + a for a in range(M)} | {("yC", c): d + 2 * M + c for c in range(P)}


def chain(N, M, P, site):
    """Gamma_N on R = (x_(i,c), y_(i,c)) (site-major) and the site of each retained label,
    or None when 1 - D beta_N is singular."""
    ix = site_index(M, P)
    R = [(i, ix[("xC", c)]) for i in range(N) for c in range(P)] + \
        [(i, ix[("yC", c)]) for i in range(N) for c in range(P)]
    E = [(i, ix[("xA", a)]) for i in range(N) for a in range(M)] + \
        [((i - 1) % N, ix[("xB", a)]) for i in range(N) for a in range(M)] + \
        [(i, ix[("yA", a)]) for i in range(N) for a in range(M)] + \
        [((i - 1) % N, ix[("yB", a)]) for i in range(N) for a in range(M)]

    def g(a, b):
        return site[a[1]][b[1]] if a[0] == b[0] else F(0)

    A = [[g(a, b) for b in R] for a in R]
    B = [[g(a, b) for b in E] for a in R]
    C = [[g(a, b) for b in R] for a in E]
    D = [[g(a, b) for b in E] for a in E]
    NM = N * M
    beta = zeros(4 * NM)
    for p in range(NM):
        beta[p][NM + p], beta[NM + p][p] = F(1), F(-1)
        beta[2 * NM + p][3 * NM + p], beta[3 * NM + p][2 * NM + p] = F(-1), F(1)
    Y = inv(sub(eye(4 * NM), mul(D, beta)))
    if Y is None:
        return None, None
    return add(A, mul(mul(mul(B, beta), Y), C)), [r[0] for r in R]


def block_data(G, sites, S):
    RS = [j for j, s in enumerate(sites) if s in S]
    RSc = [j for j, s in enumerate(sites) if s not in S]
    GS = sel(G, RS, RS)
    CS = sel(G, RS, RSc)
    one_plus = add(eye(len(RS)), mul(GS, GS)) if RS else []
    r = rank(one_plus) if RS else 0
    assert r % 2 == 0
    assert r == rank(CS) if RS and RSc else True     # corollary: rank(1 + G_S^2) = rank C_S
    return GS, r // 2, rank(CS) if RS and RSc else 0


def consecutive(N, s0, k):
    return {(s0 + j) % N for j in range(k)}


# ---------------------------------------------------------------- 1. the Kitaev chain

print("=== 1. Kitaev chain K_N (M = P = 1): blocks of k consecutive sites")


def kitaev(N):
    K = zeros(2 * N)   # labels (x_0..x_(N-1), y_0..y_(N-1))
    for i in range(N):
        K[N + i][(i + 1) % N] += 1
        K[(i + 1) % N][N + i] -= 1
    return K


ixK = site_index(1, 1)
GK = zeros(6)      # on-site Kitaev covariance: (x_C, x_A) = 1, (y_C, x_B) = 1, antisymmetric
GK[ixK[("xC", 0)]][ixK[("xA", 0)]], GK[ixK[("xA", 0)]][ixK[("xC", 0)]] = F(1), F(-1)
GK[ixK[("yC", 0)]][ixK[("xB", 0)]], GK[ixK[("xB", 0)]][ixK[("yC", 0)]] = F(1), F(-1)
for N in range(2, 10):
    K = kitaev(N)
    assert is_pure(K)
    Kc, sites = chain(N, 1, 1, GK)
    assert Kc == K, "chain construction with the on-site Kitaev covariance gives K_N"
    for k in range(1, N):
        for s0 in range(N):
            S = consecutive(N, s0, k)
            GS, ent, rC = block_data(K, sites, S)
            # Gamma_S is taken in the order (x_s, s in S sorted; y_s, s in S sorted): map labels
            RS = sorted(S)
            pos = {("x", s): j for j, s in enumerate(RS)} | {("y", s): k + j for j, s in enumerate(RS)}
            first, last = pos[("x", s0 % N)], pos[("y", (s0 + k - 1) % N)]
            assert all(GS[first][j] == GS[j][first] == GS[last][j] == GS[j][last] == 0
                       for j in range(2 * k)), "x_first and y_last decouple"
            P = mul(tr(GS), GS)
            assert P == [[F(int(i == j and i not in (first, last))) for j in range(2 * k)]
                         for i in range(2 * k)], "Gamma_S^T Gamma_S = projector off (x_first, y_last)"
            assert ent == 1 and rC == 2, (N, k, s0, ent, rC)
    print(f"   N = {N}: every block 1 <= k <= {N - 1} at all {N} positions: k-1 modes |lambda| = 1, "
          f"one mode lambda = 0; entangled modes 1 < M b(S) = 2; rank C_S = 2")

# ---------------------------------------------------------------- 2. generic pure on-site covariances

print("\n=== 2. generic pure on-site covariances (rational rotations, seeded)")


def cayley_rotation(n, rng):
    K = zeros(n)
    for i in range(n):
        for j in range(i + 1, n):
            v = F(rng.randint(-3, 3), rng.randint(1, 3))
            K[i][j], K[j][i] = v, -v
    return mul(sub(eye(n), K), inv(add(eye(n), K)))      # orthogonal, det 1, rational


def omega(d):
    O = zeros(2 * d)
    for j in range(d):
        O[j][d + j], O[d + j][j] = F(1), F(-1)
    return O


rng = random.Random(20261015)
draws_per_case = 3
for (M, P) in [(1, 1), (1, 2), (2, 1)]:
    d = 2 * M + P
    for N in range(2, 7 if (M, P) == (1, 1) else 6):
        tally = {}
        for _ in range(draws_per_case):
            while True:
                O = cayley_rotation(2 * d, rng)
                assert mul(O, tr(O)) == eye(2 * d)
                site = mul(mul(O, neg(omega(d))), tr(O))
                assert is_pure(site)
                G, sites = chain(N, M, P, site)
                if G is not None:
                    break
            assert is_pure(G)
            for k in range(1, N):
                for s0 in range(N):
                    _, ent, rC = block_data(G, sites, consecutive(N, s0, k))
                    bound = min(2 * M, P * k, P * (N - k))
                    # N = 2, P = 1: the physical state is a pure even state of two modes, invariant
                    # under the exchange of the two identical sites, which sends |11> to -|11> and
                    # fixes |00>; so it is |00> or |11>, a product: no entangled mode.
                    expected = 0 if (N, P) == (2, 1) else bound
                    assert ent <= 2 * M and rC <= 4 * M          # the theorem and the corollary
                    tally.setdefault(k, set()).add((ent, bound, expected))
        line = ", ".join(f"k={k}: " + "/".join(f"{e} (min {b})" for e, b, _ in sorted(v))
                         for k, v in sorted(tally.items()))
        ok = all(e == x for v in tally.values() for e, _, x in v)
        print(f"   M={M} P={P} N={N}: entangled modes {line}"
              + ("  [N = 2, P = 1: product, see comment]" if (N, P) == (2, 1) else ""))
        assert ok, "generic draw differs from the expected count"
print("   in every draw the count equals min(M b(S), P k, P (N-k)), except N = 2, P = 1 (count 0);")
print("   so it equals M b(S) = 2M only when P k >= 2M and P (N-k) >= 2M, and for M = P = 1")
print("   only for N >= 4 and 2 <= k <= N - 2")

# ---------------------------------------------------------------- 3. degenerate inputs

print("\n=== 3. degenerate inputs")
K1 = kitaev(1)
assert K1 == neg(omega(1)), "K_1 = -Omega_1 (vacuum)"
Kc1, sites1 = chain(1, 1, 1, GK)
assert Kc1 == K1
for N in (1, 2, 3):
    K = kitaev(N)
    _, sites = chain(N, 1, 1, GK)
    for S in (set(), set(range(N))):
        _, ent, rC = block_data(K, sites, S)
        assert ent == 0 and rC == 0
print("   K_1 = -Omega_1; the empty block and the whole ring (b(S) = 0) have no entangled modes, N = 1, 2, 3")
print("\nall assertions passed (exact rational arithmetic)")
