import os
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from poly import *
from math import gcd, comb
def intpoly(A):
    den = 1
    for a in A: den = den*a.denominator//gcd(den, a.denominator)
    Ai = [int(a*den) for a in A]; g = 0
    for a in Ai: g = gcd(g, a)
    Ai = [a//g for a in Ai]
    while Ai and Ai[-1] == 0: Ai.pop()
    return Ai, F(den, g)
def get(case, name):
    terms = X_terms(case) if name == 'X' else Y_terms(case)
    if case == 1 and name == 'X':
        t2 = []
        for nm, dens in terms:
            if len(dens) == 2: t2.append((nm, [[F(1),F(0),F(2),F(0),F(1)]]))
            elif dens == [[F(1),F(0),F(1)]]: t2.append((pmul(nm, [F(1),F(0),F(1)]), [[F(1),F(0),F(2),F(0),F(1)]]))
            else: t2.append((nm, dens))
        terms = t2
    A, Q, facs = combine(terms)
    return A, Q, facs, terms
def mobius(A, b, c, d=None):
    if d is None: d = len(A) - 1
    # sum_j A_j (b + c t)^j (1+t)^(d-j)
    res = [F(0)]*(d+1)
    for j, a in enumerate(A):
        if a == 0: continue
        p = [F(1)]
        for _ in range(j): p = pmul(p, [F(b), F(c)])
        for _ in range(d-j): p = pmul(p, [F(1), F(1)])
        res = padd(res, pscale(a, p))
    return res
def var(l):
    s = [x for x in l if x != 0]
    return sum(1 for i in range(len(s)-1) if (s[i] > 0) != (s[i+1] > 0))
