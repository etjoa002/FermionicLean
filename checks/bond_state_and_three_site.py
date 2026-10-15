"""Numerical exploration behind the bond state and the three-site example (notes, sections 3 and 5).

In floating point and independently of Lean: the Majorana covariance of the two-mode state
(|00> + i|11>)/sqrt 2 in the Jordan-Wigner convention of the library, and the covariance of the
periodic chain of three sites (one virtual pair and one physical mode per site) for several pure
on-site covariances, with a test of purity of the output. The integer matrices of the three-site
example proved in FermionicLean/Chain/ThreeSite.lean are recorded in three-site-data.json next to
this script. Requires NumPy; prints its results and writes no files.
"""
import numpy as np, itertools
np.set_printoptions(linewidth=200, precision=3, suppress=True)

# --- bond state check on 2 modes (JW as in FermionicLean: c_x j = S_j X_j, c_y j = i S_j X_j Z_j)
X = np.array([[0,1],[1,0]],complex); Z = np.diag([1,-1]).astype(complex); I2 = np.eye(2)
def kron(*ms):
    out = np.eye(1)
    for m in ms: out = np.kron(out, m)
    return out
# basis order: configurations s=(s1,s2) with index s1*2+s2 ; mode 1 is the first tensor factor
cx1 = kron(X, I2); cy1 = 1j*kron(X@Z, I2)
cx2 = kron(Z, X); cy2 = 1j*kron(Z, X@Z)
c = [cx1, cx2, cy1, cy2]   # labels x1,x2,y1,y2
psi = np.zeros(4,complex); psi[0]=1; psi[3]=1j; psi/=np.sqrt(2)
rho = np.outer(psi, psi.conj())
G = np.array([[ (1j/2*np.trace(rho@(c[a]@c[b]-c[b]@c[a]))).real for b in range(4)] for a in range(4)])
print("bond state covariance (x1,x2,y1,y2):\n", G)

# --- periodic chain contraction, generic
def contract(G, R, E, Gp):
    A=G[np.ix_(R,R)]; B=G[np.ix_(R,E)]; C=G[np.ix_(E,R)]; D=G[np.ix_(E,E)]
    M = np.eye(len(E)) - D@Gp
    print("det(1-D Gp) =", np.linalg.det(M))
    return A + B@Gp@np.linalg.inv(M)@C

def omega(n):
    return np.block([[np.zeros((n,n)), np.eye(n)],[-np.eye(n), np.zeros((n,n))]])

def chain(N, Gloc, M=1, P=1):
    # local labels per site: modes (A(M), B(M), C(P)); Majorana labels x then y: index x_m = m, y_m = d+m, d=2M+P
    d = 2*M+P
    n = N*d
    # global label: site-major modes, x first: x_(i,m) = i*d+m ; y_(i,m) = n + i*d+m
    G = np.zeros((2*n,2*n))
    for i in range(N):
        idx = [i*d+m for m in range(d)] + [n+i*d+m for m in range(d)]
        G[np.ix_(idx,idx)] = Gloc
    phys = [i*d+2*M+p for i in range(N) for p in range(P)]
    R = phys + [n+q for q in phys]
    Aids = [i*d+a for i in range(N) for a in range(M)]
    Bids = [i*d+M+b for i in range(N) for b in range(M)]
    # E ordered: x-part (A's then B's), y-part (A's then B's)
    E = Aids + Bids + [n+q for q in Aids] + [n+q for q in Bids]
    # bond on E: pair B_{i} with A_{i+1}: L = A-labels (i,a) , L' = B-labels (i-1,a)
    NM = N*M
    beta = np.zeros((4*NM,4*NM))
    for i in range(N):
        for a in range(M):
            iA = i*M+a                      # position of A_(i,a) in Aids
            iB = ((i-1)%N)*M+a              # position of B_(i-1,a) in Bids
            # x-sector: beta_{xA xB} = 1
            beta[iA, NM+iB] = 1; beta[NM+iB, iA] = -1
            # y-sector: -1
            beta[2*NM+iA, 3*NM+iB] = -1; beta[3*NM+iB, 2*NM+iA] = 1
    assert np.allclose(beta@beta, -np.eye(4*NM)) and np.allclose(beta.T, -beta)
    return contract(G, R, E, beta)

# candidate local state: 3 modes (A,B,C), M=P=1. Try: A-B bond + C vacuum  => local x-labels (A,B,C), y-labels
def local_bond_plus_vac():
    Gl = np.zeros((6,6))
    # bond between A(0) and B(1): beta_{xA xB}=1, beta_{yA yB}=-1
    Gl[0,1]=1; Gl[1,0]=-1; Gl[3,4]=-1; Gl[4,3]=1
    # C vacuum: -Omega_1 : entry (x_C, y_C) = -1
    Gl[2,5]=-1; Gl[5,2]=1
    return Gl
Gl = local_bond_plus_vac()
assert np.allclose(Gl@Gl, -np.eye(6))
out = chain(3, Gl)
print("three-site, local = bond(A,B) + vacuum(C):\n", out)

# candidate 2: a rotated state: rotate vacuum of (A,B,C) by an orthogonal O mixing x-labels (real rotation)
def rot(theta):
    # rotation in the (x_B, x_C) plane and (y_B, y_C) plane -> orthogonal on 6 labels
    O = np.eye(6); c,s=np.cos(theta),np.sin(theta)
    O[1,1]=c; O[1,2]=-s; O[2,1]=s; O[2,2]=c
    O[4,4]=c; O[4,5]=-s; O[5,4]=s; O[5,5]=c
    return O
O = rot(np.pi/4)
Gl2 = O@Gl@O.T
out2 = chain(3, Gl2)
print("three-site, rotated:\n", out2, "\npure?", np.allclose(out2@out2,-np.eye(6)))

def rot2(c,s, pairs):
    O = np.eye(6)
    for (p,q) in pairs:
        O[p,p]=c; O[p,q]=-s; O[q,p]=s; O[q,q]=c
    return O
for name,pairs in [("xB-xC & yB-yC",[(1,2),(4,5)]), ("xA-xC & yA-yC",[(0,2),(3,5)]), ("xB-yC & yB-xC",[(1,5),(4,2)]), ("xA-yC only",[(0,5)]), ("xB-yC only",[(1,5)]), ("xC-yB only",[(2,4)])]:
    O = rot2(3/5,4/5,pairs)
    G3 = O@Gl@O.T
    print("---",name, "local pure?", np.allclose(G3@G3,-np.eye(6)))
    o = chain(3, G3)
    print(o, "\npure?", np.allclose(o@o,-np.eye(6)), " product?", np.allclose(o[:3,:3],0) and np.allclose(o[:3,3:]-np.diag(np.diag(o[:3,3:])),0))
