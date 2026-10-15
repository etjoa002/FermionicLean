"""Exact intermediate quantities of the three-site chain (notes, Proposition "Three-site chain").

Recomputes, in exact rational arithmetic (Python's fractions; no floating point, no third-party
package), every intermediate quantity a reader needs to reproduce the proposition by hand:

  the on-site covariance Gamma_site = O Gamma_seed O^T,
  the blocks A, B, C, D of the input matrix Gamma_in and the bonds beta_3,
  D beta_3 and 1 - D beta_3 (block diagonal with circulant blocks), its determinant,
  its inverse Y = (1 - D beta_3)^{-1}, the product B beta_3 Y C, and Theta.

Every value is asserted equal to the value stated in the notes (docs/lecture-notes/chain.tex)
and to the integer matrices of the Lean file FermionicLean/Chain/ThreeSite.lean, which are
copied below and also recorded in three-site-data.json next to this script. A final section
checks degenerate and neighbouring inputs (N = 1, 2, 5, the unrotated seed). The script prints
its results and writes no files.

Conventions (notes, Section "Periodic chains"): site labels (x_A, x_B, x_C, y_A, y_B, y_C);
retained labels R = (x_C0, x_C1, x_C2, y_C0, y_C1, y_C2); eliminated labels
E = (x^L_0..2, x^L'_0..2, y^L_0..2, y^L'_0..2) with x^L_i = x_{A_i} and x^L'_i = x_{B_{i-1}};
(beta_N)_{x^L_i x^L'_i} = 1, (beta_N)_{y^L_i y^L'_i} = -1; Omega_n = [[0, 1], [-1, 0]] in (x, y);
Gamma_N = A + B beta_N (1 - D beta_N)^{-1} C.
"""
import json
from fractions import Fraction as F
from pathlib import Path

# ---------------------------------------------------------------- exact matrix helpers


def mat(rows):
    return [[F(v) for v in r] for r in rows]


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


def scal(c, X):
    return [[F(c) * a for a in r] for r in X]


def tr(X):
    return [list(r) for r in zip(*X)]


def sel(X, rows, cols):
    return [[X[i][j] for j in cols] for i in rows]


def det(X):
    X = [list(r) for r in X]
    n, d = len(X), F(1)
    for k in range(n):
        p = next((i for i in range(k, n) if X[i][k] != 0), None)
        if p is None:
            return F(0)
        if p != k:
            X[k], X[p] = X[p], X[k]
            d = -d
        d *= X[k][k]
        for i in range(k + 1, n):
            f = X[i][k] / X[k][k]
            X[i] = [a - f * b for a, b in zip(X[i], X[k])]
    return d


def inv(X):
    n = len(X)
    A = [list(r) + e for r, e in zip(X, eye(n))]
    for k in range(n):
        p = next(i for i in range(k, n) if A[i][k] != 0)
        A[k], A[p] = A[p], A[k]
        piv = A[k][k]
        A[k] = [a / piv for a in A[k]]
        for i in range(n):
            if i != k and A[i][k] != 0:
                f = A[i][k]
                A[i] = [a - f * b for a, b in zip(A[i], A[k])]
    return [r[n:] for r in A]


def show(name, X, scale=1):
    print(f"{name}" + (f"  (times {scale})" if scale != 1 else "") + ":")
    for r in X:
        print("   " + " ".join(f"{str(a * scale):>6}" for a in r))


def shift(n):
    """Cyclic shift S on Z/n with S_{i,i+1} = 1."""
    return [[F(int(j == (i + 1) % n)) for j in range(n)] for i in range(n)]


def blockdiag(*Bs):
    n = sum(len(B) for B in Bs)
    out, o = zeros(n), 0
    for B in Bs:
        for i, r in enumerate(B):
            for j, a in enumerate(r):
                out[o + i][o + j] = a
        o += len(B)
    return out


# ---------------------------------------------------------------- the chain construction

XA, XB, XC, YA, YB, YC = range(6)   # site labels (x_A, x_B, x_C, y_A, y_B, y_C), M = P = 1


def chain_blocks(N, site):
    """Blocks A, B, C, D of Gamma_in and beta_N for M = P = 1 (Definitions of the input matrix
    and of the bonds). Labels: R = (x_C_i, y_C_i), E = (x^L_i, x^L'_i, y^L_i, y^L'_i), i in Z/N."""
    R = [(i, XC) for i in range(N)] + [(i, YC) for i in range(N)]
    E = ([(i, XA) for i in range(N)] + [((i - 1) % N, XB) for i in range(N)]
         + [(i, YA) for i in range(N)] + [((i - 1) % N, YB) for i in range(N)])

    def g(a, b):  # entry of diag(Gamma_i) relabelled by e: zero between different sites
        return site[a[1]][b[1]] if a[0] == b[0] else F(0)

    A = [[g(a, b) for b in R] for a in R]
    B = [[g(a, b) for b in E] for a in R]
    C = [[g(a, b) for b in R] for a in E]
    D = [[g(a, b) for b in E] for a in E]
    beta = zeros(4 * N)
    for i in range(N):
        beta[i][N + i], beta[N + i][i] = F(1), F(-1)                    # x^L_i, x^L'_i
        beta[2 * N + i][3 * N + i], beta[3 * N + i][2 * N + i] = F(-1), F(1)  # y^L_i, y^L'_i
    return A, B, C, D, beta


def chain_cov(N, site):
    A, B, C, D, beta = chain_blocks(N, site)
    M = sub(eye(4 * N), mul(D, beta))
    d = det(M)
    if d == 0:
        return d, None
    return d, add(A, mul(mul(mul(B, beta), inv(M)), C))


def is_pure(G):
    return tr(G) == scal(-1, G) and mul(G, G) == scal(-1, eye(len(G)))


# ---------------------------------------------------------------- values stated in the Lean file

LEAN_5_SITE = mat([[0, 3, -4, 0, 0, 0], [-3, 0, 0, 0, 0, -4], [4, 0, 0, 0, 0, -3],
                   [0, 0, 0, 0, -5, 0], [0, 0, 0, 5, 0, 0], [0, 4, 3, 0, 0, 0]])
LEAN_19_OUT = mat([[0, 0, 0, -15, 6, -10], [0, 0, 0, -10, -15, 6], [0, 0, 0, 6, -10, -15],
                   [15, 10, -6, 0, 0, 0], [-6, 15, 10, 0, 0, 0], [10, -6, 15, 0, 0, 0]])
_y1, _y2, _y3, _y4 = ([[125, -75, 45], [45, 125, -75], [-75, 45, 125]],
                      [[125, 45, -75], [-75, 125, 45], [45, -75, 125]],
                      [[76, -76, 76], [76, 76, -76], [-76, 76, 76]],
                      [[76, 76, -76], [-76, 76, 76], [76, -76, 76]])
LEAN_152_Y = blockdiag(mat(_y1), mat(_y2), mat(_y3), mat(_y4))

# ---------------------------------------------------------------- 1. on-site covariance

print("=== 1. on-site covariance (chain.tex, display before Proposition prop:three)")
seed = zeros(6)
seed[XA][XB], seed[XB][XA] = F(1), F(-1)      # bond covariance beta on (A, B): x-entry +1
seed[YA][YB], seed[YB][YA] = F(-1), F(1)      #                                y-entry -1
seed[XC][YC], seed[YC][XC] = F(-1), F(1)      # -Omega_1 on C
O = eye(6)
O[XA][XA] = O[YC][YC] = F(3, 5)
O[XA][YC], O[YC][XA] = F(-4, 5), F(4, 5)
assert mul(O, tr(O)) == eye(6) and det(O) == 1, "O is a rotation"
site = mul(mul(O, seed), tr(O))
show("Gamma_site", site, 5)
assert scal(5, site) == LEAN_5_SITE, "Gamma_site = notes' matrix = Lean threeSiteLocalZ / 5"
assert is_pure(site) and is_pure(seed)
print("   equals the notes' matrix and Lean's threeSiteLocalZ/5; pure (Gamma^T = -Gamma, Gamma^2 = -1)")

# ---------------------------------------------------------------- 2. blocks and bonds

print("\n=== 2. blocks of Gamma_in and the bonds beta_3 (proof of prop:three, item (a))")
N = 3
A, B, C, D, beta = chain_blocks(N, site)
S = shift(N)
Z3, I3 = zeros(3), eye(3)
Om3 = [r1 + r2 for r1, r2 in zip(Z3, I3)] + [[-a for a in r1] + r2 for r1, r2 in zip(I3, Z3)]
assert A == scal(F(-3, 5), Om3), "A = -(3/5) Omega_3"
# B: rows (x_C; y_C), column groups (x^L, x^L', y^L, y^L'): B = (4/5) [[1, 0, 0, 0], [0, S, 0, 0]]
B_expected = [r1 + r2 + r3 + r4 for r1, r2, r3, r4 in zip(I3, Z3, Z3, Z3)] + \
             [r1 + r2 + r3 + r4 for r1, r2, r3, r4 in zip(Z3, S, Z3, Z3)]
assert B == scal(F(4, 5), B_expected), "B_{x_Ci x^L_i} = B_{y_Ci x^L'_{i+1}} = 4/5, no others"
assert C == scal(-1, tr(B)), "C = -B^T"
St = tr(S)
D_expected = [[F(0)] * 12 for _ in range(12)]
for i in range(3):
    for j in range(3):
        D_expected[i][3 + j] = F(3, 5) * S[i][j]          # x^L_i  -> x^L'_{i+1}:  3/5
        D_expected[3 + i][j] = -F(3, 5) * St[i][j]        # x^L'_{i+1} -> x^L_i : -3/5
        D_expected[6 + i][9 + j] = -S[i][j]               # y^L_i  -> y^L'_{i+1}: -1
        D_expected[9 + i][6 + j] = St[i][j]               # y^L'_{i+1} -> y^L_i :  1
assert D == D_expected
beta_expected = blockdiag([[F(0)] * 6 for _ in range(6)], [[F(0)] * 6 for _ in range(6)])
for i in range(3):
    beta_expected[i][3 + i], beta_expected[3 + i][i] = F(1), F(-1)
    beta_expected[6 + i][9 + i], beta_expected[9 + i][6 + i] = F(-1), F(1)
assert beta == beta_expected and mul(beta, beta) == scal(-1, eye(12))
show("5 A", A, 5)
show("5 B", B, 5)
show("5 D", D, 5)
show("beta_3", beta)
data = json.loads((Path(__file__).resolve().parent / "three-site-data.json").read_text(encoding="utf-8"))
assert scal(5, A) == mat(data["fiveA"]) and scal(5, B) == mat(data["fiveB"])
assert scal(5, D) == mat(data["fiveD"]) and scal(5, site) == mat(data["fiveGammaLoc"])
print("   A = -(3/5) Omega_3; B = (4/5)[[1,0,0,0],[0,S,0,0]] (S the cyclic shift, S_{i,i+1} = 1);")
print("   C = -B^T; D = [[0,(3/5)S,0,0],[-(3/5)S^T,0,0,0],[0,0,0,-S],[0,0,S^T,0]]; match three-site-data.json")

# ---------------------------------------------------------------- 3. 1 - D beta, determinant, inverse

print("\n=== 3. D beta_3, 1 - D beta_3, its determinant and inverse (item (b))")
Dbeta = mul(D, beta)
t = F(3, 5)
assert Dbeta == blockdiag(scal(-t, S), scal(-t, St), scal(-1, S), scal(-1, St)), \
    "D beta_3 = diag(-(3/5)S, -(3/5)S^T, -S, -S^T)"
M = sub(eye(12), Dbeta)
blocks = [add(I3, scal(t, S)), add(I3, scal(t, St)), add(I3, S), add(I3, St)]
assert M == blockdiag(*blocks)
dets = [det(b) for b in blocks]
assert dets == [F(152, 125), F(152, 125), F(2), F(2)], "det(1 + tS_3) = 1 + t^3"
dM = det(M)
assert dM == F(304, 125) ** 2 == F(92416, 15625), "det(1 - D beta_3) = (304/125)^2"
assert det(sub(scal(5, eye(12)), mul(scal(5, D), beta))) == 38000 ** 2, \
    "integer form: det(5 - D_Z beta_Z) = 5^12 (304/125)^2 = 38000^2"
print(f"   1 - D beta_3 = diag(1 + (3/5)S, 1 + (3/5)S^T, 1 + S, 1 + S^T)")
print(f"   block determinants {[str(d) for d in dets]}; det(1 - D beta_3) = {dM} = (304/125)^2")
Y = inv(M)
assert mul(M, Y) == eye(12) and scal(152, Y) == LEAN_152_Y == mat(data["Y152"])
assert blockdiag(*[inv(b) for b in blocks]) == Y
# closed forms: (1 + tS)^{-1} = (1 - tS + t^2 S^2)/(1 + t^3)
S2 = mul(S, S)
assert inv(blocks[0]) == scal(F(1) / (1 + t ** 3), add(sub(I3, scal(t, S)), scal(t * t, S2)))
assert inv(blocks[2]) == scal(F(1, 2), add(sub(I3, S), S2))
show("Y = (1 - D beta_3)^{-1}", Y, 152)
print("   152 Y = diag(125 - 75S + 45S^2, its transpose, 76(1 - S + S^2), its transpose)")
print("   equals Lean's threeSiteInvZ and three-site-data.json Y152")
assert mul(sub(scal(5, eye(12)), mul(scal(5, D), beta)), LEAN_152_Y) == scal(760, eye(12)), \
    "Lean threeSite_inv_identity: (5 - D_Z beta_Z) Y_Z = 760"

# ---------------------------------------------------------------- 4. the product and Theta

print("\n=== 4. B beta_3 Y C and Theta (item (c))")
BbYC = mul(mul(mul(B, beta), Y), C)
show("B beta_3 Y C", BbYC, 95)
G3 = add(A, BbYC)
show("Gamma_3 = A + B beta_3 Y C", G3, 19)
assert scal(19, G3) == LEAN_19_OUT, "Gamma_3 = Lean threeSiteOutputZ / 19"
Theta = scal(-1, sel(G3, range(3), range(3, 6)))
assert sel(G3, range(3), range(3)) == Z3 and sel(G3, range(3, 6), range(3, 6)) == Z3
assert sel(G3, range(3, 6), range(3)) == tr(Theta)
Theta_notes = scal(F(1, 19), mat([[15, -6, 10], [10, 15, -6], [-6, 10, 15]]))
assert Theta == Theta_notes == scal(F(1, 19), mat(data["K19"])), "Theta as stated"
assert Theta == scal(F(1, 19), add(sub(scal(15, I3), scal(6, S)), scal(10, St))), \
    "Theta = (15 - 6S + 10S^T)/19"
assert mul(Theta, tr(Theta)) == I3 and is_pure(G3), "Theta Theta^T = 1, Gamma_3 pure"
assert all(Theta[i][j] == Theta[(i + 1) % 3][(j + 1) % 3] for i in range(3) for j in range(3)), \
    "circulant"
assert G3[0][3 + 1] == G3[1][3 + 2] == G3[2][3 + 0] == F(6, 19), "Gamma_{x_Ci y_C(i+1)} = 6/19"
assert G3[0][3 + 2] == G3[1][3 + 0] == G3[2][3 + 1] == F(-10, 19), "Gamma_{x_Ci y_C(i-1)} = -10/19"
# blockwise form: B beta Y C = -(16/25) [[0, Y_L' S^T], [-S Y_L, 0]]
YL, YLp = sel(Y, range(3), range(3)), sel(Y, range(3, 6), range(3, 6))
assert BbYC == scal(F(-16, 25), [r1 + r2 for r1, r2 in zip(Z3, mul(YLp, St))]
                    + [r1 + r2 for r1, r2 in zip(scal(-1, mul(S, YL)), Z3)])
assert scal(-1, sel(BbYC, range(3), range(3, 6))) == \
    scal(F(1, 95), add(sub(scal(18, I3), scal(30, S)), scal(50, St))), "-(B beta Y C)_{xy} = (18 - 30S + 50S^T)/95"
print("   Theta = (1/19)(15 - 6S + 10S^T) = -(A + B beta_3 Y C)_{x_C y_C}; Theta Theta^T = 1; circulant")
print("   Gamma_{x_Ci y_C(i+1)} = 6/19, Gamma_{x_Ci y_C(i-1)} = -10/19")
assert add(scal(14440, scal(5, A)), scal(19, mul(mul(mul(scal(5, B), beta), LEAN_152_Y), scal(5, C)))) \
    == scal(3800, LEAN_19_OUT), "Lean threeSite_output_identity"
print("   both integer identities of ThreeSite.lean hold")

# ---------------------------------------------------------------- 5. degenerate and neighbouring inputs

print("\n=== 5. degenerate and neighbouring inputs")
# the same on-site covariance on other ring lengths: det(1 - D beta_N) = (1 - (-3/5)^N)^2 (1 - (-1)^N)^2
for n in (1, 2, 3, 4, 5):
    d, G = chain_cov(n, site)
    expected = (1 - (-t) ** n) ** 2 * (1 - (-1) ** n) ** 2
    assert d == expected
    if G is not None:
        assert is_pure(G)
    print(f"   N = {n}: det(1 - D beta_N) = {d}" + ("  (singular: for even N the y-blocks 1 + S_N have the eigenvalue 1 + e^{i pi} = 0)"
                                                   if G is None else "; Gamma_N pure"))
# the unrotated seed: the chain state is the vacuum of the physical modes
d, G = chain_cov(3, seed)
assert d == 16 and G == scal(-1, Om3)
print(f"   seed without rotation, N = 3: det = {d}, Gamma_3 = -Omega_3 (vacuum)")
print("\nall assertions passed (exact rational arithmetic)")
