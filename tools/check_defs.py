from fractions import Fraction as Fr
from math import comb
def cheb(d,first):
    a,b=[1],[0,first]
    if d==0: return a
    for _ in range(d-1):
        c=[0]+[2*x for x in b]
        for i,x in enumerate(a): c[i]-=x
        a,b=b,c
    return b
def coef(c,k): return c[k] if 0<=k<len(c) else 0
def revc(C,c,m): return coef(c,C-1-m) if m<C else 0
def mulfac(h,cf,i): return sum((-1)**v*comb(h,v)*cf(i-v) for v in range(h+1) if v<=i)
def dist(N,r): return 4*N-r if r<4*N else r-4*N
def sgn(N,r): return -1 if r<4*N else (0 if r==4*N else 1)
def pcoef(N,r,i):
    T=cheb(dist(N,r),1); return mulfac(2*N,lambda m: revc(63*N,T,m),i)
def dcoef(N,r,i):
    U=cheb(max(dist(N,r)-1,0),2); return sgn(N,r)*mulfac(2*N,lambda m: revc(63*N,U,m),i)
def c(l): return Fr(comb(2*l,l),4**l)
def ckern(i,j): return c((i-j)//2) if j<=i and (i-j)%2==0 else Fr(0)
def m(i): return Fr(2)/((i+1)*c(i//2)) if i%2==0 else Fr(0)
KM={0:Fr(0),1:Fr(2)}; KP={0:Fr(0),1:Fr(0)}
def km(d):
    if d not in KM: KM[d]=((d-1)*km(d-2)+m(d-2)+m(d-1))/d
    return KM[d]
def kp(d):
    if d not in KP: KP[d]=((d-2)*kp(d-2)+Fr(2,d-1))/(d-1)
    return KP[d]
def M0(i,j):
    if j<=i: return km(i-j)-sum(m(i-j+k-1)/k for k in range(1,j+1))
    return kp(j-i)-sum(m(k-1)/(j-i+k) for k in range(1,i+1))
def harm(d,n): return sum(Fr(1,k**d) for k in range(1,n+1))
def Z0(i,j): return -harm(2,i) if i==j else (harm(1,i)-harm(1,j))/(i-j)
def rawq(z,N,r,j): return sum(pcoef(N,r,i)*(M0(i,j)+4*z*ckern(i,j)) for i in range(65*N+1)) - Fr(3,2)*sum(dcoef(N,r,i)*Z0(i,j) for i in range(65*N+1))
def entryq(z,N,r,k): return sum((-1)**v*comb(4*N,v)*rawq(z,N,r,7*N+k+v) for v in range(4*N+1))
N=1; bad=0
for r in range(49):
    for j in range(59):
        s=sum(pcoef(N,r,i)*ckern(j-1,i) for i in range(j)) - dcoef(N,r,j)
        if s!=0: bad+=1
print("zeta(2) cancellation failures, N=1, rows 0..48, j<59:",bad)
B=[[entryq(0,1,r,k) for k in range(48)] for r in range(49)]
p=101
def modp(x): return x.numerator*pow(x.denominator,-1,p)%p
for sig in (0,1,-1):
    R=[[modp(B[i][k]+sig*B[i+1][k]) for k in range(48)] for i in range(48)]
    piv=[];sw=[]
    for i in range(48):
        if R[i][i]==0:
            j=next(j for j in range(i+1,48) if R[j][i]); R[i],R[j]=R[j],R[i]; sw.append((i,j))
        d=R[i][i]; piv.append(d); inv=pow(d,-1,p)
        for j in range(i+1,48):
            f=R[j][i]*inv%p
            if f: R[j]=[(a-f*b)%p for a,b in zip(R[j],R[i])]
    print("sigma",sig,"swaps",sw); print(piv)
