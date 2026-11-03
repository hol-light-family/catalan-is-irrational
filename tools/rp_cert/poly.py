import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from data import *
from fractions import Fraction as F
# polynomials: lists of Fractions, low degree first
def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pscale(c, p): return [c*a for a in p]
def pmul(p, q):
    if not p or not q: return []
    r = [F(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q): r[i+j] += a*b
    return r
def pev(p, x):
    s = 0
    for a in reversed(p): s = s*x + a
    return s
def cmul(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def cheb_U(n):  # list of U_0..U_n polynomials
    U = [[F(1)], [F(0), F(2)]]
    while len(U) <= n: U.append(padd(pmul([F(0), F(2)], U[-1]), pscale(-1, U[-2])))
    return U
def cheb_T(n):
    T = [[F(1)], [F(0), F(1)]]
    while len(T) <= n: T.append(padd(pmul([F(0), F(2)], T[-1]), pscale(-1, T[-2])))
    return T
def is_real(cz): return cz[1][1] == 0 and cz[0][1] == 0
def tail_terms_T(tail):
    """derivative terms Re(c z / W), W = 1 - 2xz + z^2: returns list of (num, den) polys"""
    out = []
    for c, z in tail:
        cz = cmul(c, z); z2 = cmul(z, z)
        a0, a1 = 1 + z2[0], -2*z[0]   # Re W = a0 + a1 x
        b0, b1 = z2[1], -2*z[1]       # Im W
        if is_real((c, z)):
            out.append(([cz[0]], [a0, a1]))
        else:
            num = [cz[0]*a0 + cz[1]*b0, cz[0]*a1 + cz[1]*b1]
            den = [a0*a0 + b0*b0, 2*(a0*a1 + b0*b1), a1*a1 + b1*b1]
            out.append((num, den))
    return out
def tail_terms_S(tail):
    """Re(c z/(1 - x z))"""
    out = []
    for c, z in tail:
        cz = cmul(c, z)
        a0, a1 = F(1), -z[0]; b0, b1 = F(0), -z[1]
        if is_real((c, z)):
            out.append(([cz[0]], [a0, a1]))
        else:
            num = [cz[0]*a0 + cz[1]*b0, cz[0]*a1 + cz[1]*b1]
            den = [a0*a0 + b0*b0, 2*(a0*a1 + b0*b1), a1*a1 + b1*b1]
            out.append((num, den))
    return out
def combine(terms):
    """terms: list of (num, [den factors]); returns (A, Q) with Q = prod of all distinct factors"""
    facs = []
    for num, dens in terms:
        for d in dens:
            if d not in facs: facs.append(d)
    Q = [F(1)]
    for f in facs: Q = pmul(Q, f)
    A = []
    for num, dens in terms:
        rest = [F(1)]
        dl = list(dens)
        for f in facs:
            if f in dl: dl.remove(f)
            else: rest = pmul(rest, f)
        # factors repeated in dens (e.g. (1+x^2)^2) need Q to contain them twice: handled by caller
        assert not dl, dl
        A = padd(A, pmul(num, rest))
    return A, Q, facs
def X_terms(case):
    d = CASES[case]; k = d['kappa']; lam = d['lam']
    pfin, ptail = d['p']; vfin, vtail = d['v']
    one_p_x2 = [F(1), F(0), F(1)]
    terms = [([F(19, 48)], [[F(0), F(1)]]), ([F(-1, 12)], [[F(1), F(-1)]]),
             ([F(0), -(k + F(17, 24))], [one_p_x2])]
    if lam != 0:
        terms.append(([F(0), -4*lam], [one_p_x2, [F(1), F(0), F(1), F(0), F(0)][:3] + []]))
    U = cheb_U(len(pfin))
    poly = []
    for i, l in enumerate(pfin, 1): poly = padd(poly, pscale(-2*k*l, U[i-1]))
    for i, l in enumerate(vfin, 1): poly = padd(poly, pscale(-l, [F(0)]*(i-1) + [F(1)]))
    terms.append((poly, []))
    for num, den in tail_terms_T(ptail): terms.append((pscale(-2*k, num), [den]))
    for num, den in tail_terms_S(vtail): terms.append((pscale(-1, num), [den]))
    return terms
def Y_terms(case):
    d = CASES[case]; vfin, vtail = d['v']
    terms = [([F(7, 48)], [[F(0), F(1)]]), ([F(-1, 12)], [[F(1), F(-1)]])]
    U = cheb_U(len(vfin)); poly = []
    for i, l in enumerate(vfin, 1): poly = padd(poly, pscale(2*l, U[i-1]))
    terms.append((poly, []))
    for num, den in tail_terms_T(vtail): terms.append((pscale(2, num), [den]))
    return terms
