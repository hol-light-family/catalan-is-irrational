# Trial data of the paper, Section 7.1 (exact rationals)
from fractions import Fraction as F
E8 = F(1, 10**8)
def fl(xs): return [F(x) * E8 for x in xs]
def D(s): return F(s)   # decimal string -> exact
# tails: list of (c, z) with c, z complex given as pairs of Fractions; u_k += Re(c z^k)
def real_tail(z, a): return ((F(a)*E8, F(0)), (D(z), F(0)))
def cpx_tail(zr, zi, a, b): return ((F(a)*E8, -F(b)*E8), (D(zr), D(zi)))
P2_fin = fl([45559127, -50750856, -6578767, 13970217, 4786184, -4292433, -576704, 1311615, 671564, -346453])
V2_fin = fl([-23910158, 21152432, -2885110, -11558199, 6485289, 1456821, -1912176, -2263524, 2742210, -1162454])
P2_tail = [real_tail('.85', -9338452), real_tail('.94', -2141509),
           cpx_tail('0', '.7', -66277922, -31907569), cpx_tail('0', '.85', -1231651, 6002645),
           cpx_tail('.092', '.92', -3225918, 8928234), cpx_tail('-.092', '.92', -2105536, -9091287)]
V2_tail = [real_tail('-.8', 15199211), real_tail('-.96', 4451662), real_tail('.88', 2545398),
           real_tail('.95', -4932634), real_tail('.984', 11618157),
           cpx_tail('0', '.78', 27238714, -38447936), cpx_tail('0', '.9', -31341084, -30188786),
           cpx_tail('0', '.955', -6693542, 11912254), cpx_tail('0', '.984', 2055213, -21715849)]
P1_fin = fl([11913521, -79993701, -21956443, 37903579, 10744022, -2073193, 570246, -24939103])
V1_fin = fl([-89913025, 52874280, 45168341, -30708629, -19269841, 33922112, 9819141, -16992389])
LAM1 = D('2.47405979')
CASES = {2: dict(kappa=2, lam=F(0), p=(P2_fin, P2_tail), v=(V2_fin, V2_tail)),
         1: dict(kappa=1, lam=LAM1, p=(P1_fin, []), v=(V1_fin, []))}
