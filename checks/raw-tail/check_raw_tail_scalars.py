"""Exact arithmetic checks for the raw omitted-pivot estimate.

This file checks the scalar premises and final rational sum. The universal
graph and cancellation arguments are mathematical inputs from the paper.
"""
from fractions import Fraction as F
import json
from pathlib import Path


class Q:
    # a+b*q, q^2=1-q, q=(sqrt(5)-1)/2.
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)
    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q) else Q(x)
    def __add__(self, other):
        y = Q.coerce(other)
        return Q(self.a+y.a, self.b+y.b)
    __radd__ = __add__
    def __neg__(self):
        return Q(-self.a, -self.b)
    def __sub__(self, other):
        return self + -Q.coerce(other)
    def __rsub__(self, other):
        return Q.coerce(other) + -self
    def __mul__(self, other):
        y = Q.coerce(other)
        return Q(self.a*y.a+self.b*y.b,
                 self.a*y.b+self.b*y.a-self.b*y.b)
    __rmul__ = __mul__
    def __truediv__(self, other):
        y = Q.coerce(other)
        norm = y.a*y.a-y.a*y.b-y.b*y.b
        return self * Q((y.a-y.b)/norm, -y.b/norm)
    def __rtruediv__(self, other):
        return Q.coerce(other) / self
    def __pow__(self, n):
        if n < 0:
            return (1/self)**(-n)
        result = Q(1)
        for _ in range(n):
            result = result*self
        return result
    def sign(self):
        if not self.b:
            return (self.a > 0)-(self.a < 0)
        t = 1-2*self.a/self.b
        root_comparison = 1 if t <= 0 else ((5-t*t > 0)-(5-t*t < 0))
        return ((self.b > 0)-(self.b < 0))*root_comparison
    def __lt__(self, other):
        return (self-other).sign() < 0
    def __le__(self, other):
        return (self-other).sign() <= 0
    def __abs__(self):
        return self if self.sign() >= 0 else -self
    def serial(self):
        return [str(self.a), str(self.b)]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


q=Q(0,1)
R=F(917,1000)
S=F(19,25)
k0=F(10003,10000)
chi=F(47597,50000)
t=F(95761,100000)
u=[F(1),F(13,50)]
v=[F(823,1250),F(97,625)]
nu=sum(a*b for a,b in zip(u,v))
require(nu==F(10918,15625), "nu transcription")
require(nu/R**3 < chi**2 < 1, "paid run contraction")
require(sum(a*a for a in u)*sum(a*a for a in v)/nu**2 < k0**2,
        "one endpoint factor per path")
require(S < R**3 and chi < t and R < t*t, "summation inequalities")
require(q*q < F(191,500), "carry subdominant eigenvalue")

slacks={}
for cap, bound, x in [(4,R,[10000,17164,23907,23907]),(3,S,[1,2,3])]:
    slacks[str(cap)]=[]
    for i in range(1,cap+1):
        slack=bound*x[i-1]-sum((q**j*x[j-1] for j in range(1,cap+1) if i+j>=4), Q())
        require(slack.sign()>0, "positive-vector norm certificate")
        slacks[str(cap)].append(slack.serial())

# D=H*A*H.  H times its two normalized carry eigenvectors is
# sqrt(q)/(sqrt(1+q^2)) times V and W, so all needed moments lie in Q(q).
A=[[Q(int(i+j>=4)) for j in range(1,5)] for i in range(1,5)]
WA=[[q**(i+1)*A[i][j] for j in range(4)] for i in range(4)]
V=[q,q,q*q,Q()]
W=[Q(1),-q*q,-q**3,Q()]
factor=q/(1+q*q)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q())
def mm(a,b): return [[dot(row,col) for col in zip(*b)] for row in a]
def form(a,m,b): return factor*dot(a,[dot(row,b) for row in m])
moments={}
M=A
for k in range(1,5):
    moments[k]={'alpha':form(V,M,V),'off':form(V,M,W),'beta':form(W,M,W)}
    M=mm(M,WA)
bounds={(1,'alpha'):F(823,1250),(2,'alpha'):F(823,1250),
        (1,'off'):F(171,1000),(2,'off'):F(1,40),
        (1,'beta'):F(41,1000),(2,'beta'):F(66,625),(4,'beta'):F(17,1000)}
for (k,name),bound in bounds.items():
    require(abs(moments[k][name]) < bound, f"moment {k}, {name}")
rank=[[x*y for y in v] for x in u]
a=F(823,1250); b=F(66,625); e=F(17,1000); rho=F(191,500)
for aa,oo,bb in [(a,F(171,1000),F(41,1000)),(a,F(1,40),b)]:
    require(aa<=rank[0][0] and oo*rho<rank[0][1] and oo<rank[1][0]
            and bb*rho<rank[1][1], "low-power block domination")
require(R*a<rank[0][0] and a*e<rank[1][0]**2
        and rho**2*a*e<rank[0][1]**2
        and rho**2*b*e<rank[1][1]**2
        and rho*e/R<rank[1][1], "Cauchy-Schwarz all-power extension")
s4=sum((q**j for j in range(1,5)),Q())
require((s4-1).sign()>0 and s4-q < 1, "total boundary norm")

# Independent residual certificates for K1 and K2, truncating their formal
# reciprocal at degree 80.  All operations below are exact rational operations.
qp=F(309017,500000)
require(q < qp and qp*qp+qp>1, "upper bound on critical point")
residuals=[]
for K in [[1,1,1],[1,1,2,1,0,-1,-1]]:
    inv=[F(1)]
    for n in range(1,81):
        inv.append(-sum(F(K[j])*inv[n-j] for j in range(1,min(n,len(K)-1)+1)))
    prod=[F(0)]*(len(K)+len(inv)-1)
    for i,x in enumerate(K):
        for j,y in enumerate(inv): prod[i+j]+=x*y
    E=[F(int(n==0))-x for n,x in enumerate(prod)]
    vnorm=sum(abs(x)*qp**n for n,x in enumerate(inv))
    enorm=sum(abs(x)*qp**n for n,x in enumerate(E))
    require(enorm<1, "reciprocal residual convergence")
    bound=vnorm/(1-enorm)
    require(bound<F(7,2), "fixed factor inverse norm")
    residuals.append({'residual_norm_decimal':float(enorm),'inverse_upper_decimal':float(bound)})
uu=qp*qp
aa=uu+uu**2+uu**3
tail=(1+uu)*uu**2/(1-uu)+uu**5/(1-uu**2)
mixed_inverse=1/((1-uu)*(1-aa)*(1-tail))
mixed_norm=(1+uu)*(1+aa)/(1-tail)
require(mixed_inverse<6 and mixed_norm<F(10,3), "uniform mixed-factor norms")
require(4-2*q < F(14,5), "K2 coefficient norm")
require(5 < (F(9,4)*(1-qp**16))**2, "signed Fibonacci coefficient conversion")

X=R*t*chi; Y=R*t*t; U=1-R*R*chi/t; VV=t/chi-1
require(0 < X < Y < 1 and U>0 and VV>0, "geometric sum convergence")
def geom_tail(x,K,abc):
    a,b,c=abc
    return x**K*((a*K*K+b*K+c)/(1-x)+(2*a*K+b)*x/(1-x)**2+a*x*(1+x)/(1-x)**3)
pref=945*qp**8*sum(qp**i for i in range(1,5))*k0**3*chi**-16/(R*t*t)
odd_even_x=(12*(chi+chi*chi),26*chi+38*chi*chi,16*chi+32*chi*chi)
odd_even_y=(12*(t+t*t),26*t+38*t*t,16*t+32*t*t)
bound=pref*(geom_tail(X,150,odd_even_x)/U+geom_tail(Y,150,odd_even_y)/VV)
require(bound<F(221714122,10**9), "sharp reported rounded bound")
require(bound<F(221715,10**6), "target RAW theorem constant")

report={'scope':'Exact scalar premises for the raw omitted-pivot estimate; universal graph arguments are mathematical inputs',
        'pass':True, 'norm_test_slacks_in_Qq':slacks,
        'moments_in_Qq':{str(k):{name:value.serial() for name,value in row.items()} for k,row in moments.items()},
        'fixed_factor_residual_certificates':residuals,
        'mixed_inverse_upper_decimal':float(mixed_inverse),
        'mixed_norm_upper_decimal':float(mixed_norm),
        'raw_tail_multiplier_decimal':float(bound),
        'raw_tail_multiplier_exact':str(bound)}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='raw_tail_multiplier_exact'},indent=2))
