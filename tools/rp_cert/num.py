import os
import numpy as np, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from data import *
def cf(p): return complex(float(p[0]), float(p[1]))
def seq(u, K):
    fin, tail = u
    out = np.zeros(K+1)
    for k in range(1, K+1):
        s = float(fin[k-1]) if k <= len(fin) else 0.0
        for c, z in tail: s += (cf(c) * cf(z)**k).real
        out[k] = s
    return out
def cheb(k, x):
    return np.cos(k*np.arccos(np.clip(x, -1, 1)))
def Tser(u, x):
    fin, tail = u
    s = sum(float(l)*cheb(k, x)/k for k, l in enumerate(fin, 1))
    for c, z in tail:
        c, z = cf(c), cf(z)
        s = s - 0.5*(c*np.log(1-2*x*z+z*z)).real
    return s
def Sser(u, x):
    fin, tail = u
    s = sum(float(l)*x**k/k for k, l in enumerate(fin, 1))
    for c, z in tail:
        c, z = cf(c), cf(z)
        s = s - (c*np.log(1-x*z)).real
    return s
def nsq(u):
    fin, tail = u
    K = len(fin)
    t = seq((fin, tail), K)
    l = [0.0] + [float(a) for a in fin]
    s = sum((l[k]**2 + 2*l[k]*(t[k]-l[k]))/k for k in range(1, K+1))
    for c, z in tail:
        for c2, z2 in tail:
            c, z, c2, z2 = map(lambda q: q if isinstance(q, complex) else cf(q), (c, z, c2, z2))
            # Re(c z^k) Re(c2 z2^k) = 1/2 Re(c c2 (z z2)^k) + 1/2 Re(c conj(c2) (z conj z2)^k)
            s += -0.5*(c*c2*np.log(1-z*z2)).real - 0.5*(c*np.conj(c2)*np.log(1-z*np.conj(z2))).real
    return s
def X(case, x):
    d = CASES[case]; k = d['kappa']; lam = float(d['lam'])
    return (19/48*np.log(abs(x)) + 1/12*np.log(1-x) - (k/2+17/48)*np.log(1+x*x)
            + lam*(1/6 - 2*x*x/(1+x*x)) - 2*k*Tser(d['p'], x) - Sser(d['v'], x))
def Y(case, s):
    d = CASES[case]
    return 7/48*np.log(s) + 1/12*np.log(1-s) + 2*Tser(d['v'], s)
if __name__ == '__main__':
    for case in (2, 1):
        d = CASES[case]
        ns = d['kappa']*nsq(d['p']) + nsq(d['v'])/2
        # brute-force check of nsq
        K = 20000; ps = seq(d['p'], K); vs = seq(d['v'], K); ks = np.arange(1, K+1)
        ns2 = d['kappa']*np.sum(ps[1:]**2/ks) + np.sum(vs[1:]**2/ks)/2
        xs = np.concatenate([np.linspace(-1, -1e-6, 400001), np.linspace(1e-6, 1-1e-7, 400001)])
        xv = X(case, xs); sv = Y(case, np.linspace(1e-7, 1-1e-7, 800001))
        print(case, 'nsq', ns, ns2, 'supX', xv.max(), xs[xv.argmax()], 'supY', sv.max())
        print('total', -11/16*np.log(2) + ns + xv.max() + sv.max())
    # check Tser closed form vs series at a point
    for x in (0.3, -0.97, 0.99):
        K = 4000; vs = seq(CASES[2]['v'], K)
        print(x, sum(vs[k]*cheb(k, x)/k for k in range(1, K+1)), Tser(CASES[2]['v'], x),
              sum(vs[k]*x**k/k for k in range(1, K+1)), Sser(CASES[2]['v'], x))
