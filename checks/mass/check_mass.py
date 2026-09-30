"""Exact rational checks for the finite mass inputs and scalar tails.

Omitted-pivot sums use a complete closed sum minus finite rows. Rational operations and
integer-square-root intervals are exact; decimals are outward ceilings only.
Finite boxes are supplied as separate exact interval outputs.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import itertools, json, sys
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent.parent/'data/mass'

def require(ok,label):
    if not ok: raise RuntimeError(label)

def upper(x,places=12):
    scale=10**places
    n=-((-x.numerator*scale)//x.denominator)
    return str(F(n,scale))

class Interval:
    def __init__(self,lo,hi=None):
        self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        require(self.lo<=self.hi,'interval order')
    def __add__(self,x):
        x=iv(x); return Interval(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,x):return self+-iv(x)
    def __rsub__(self,x):return iv(x)+-self
    def __mul__(self,x):
        x=iv(x); p=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return Interval(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=iv(x); require(x.lo>0 or x.hi<0,'division away from zero')
        return self*Interval(1/x.hi,1/x.lo)
    def __pow__(self,n):
        out=Interval(1)
        for _ in range(n):out*=self
        return out
    def root(self):
        require(self.lo>=0,'nonnegative root')
        scale=10**30
        low=isqrt(self.lo.numerator*scale*scale//self.lo.denominator)
        high=isqrt(self.hi.numerator*scale*scale//self.hi.denominator)+1
        lo,hi=F(low,scale),F(high,scale)
        require(lo*lo<=self.lo and hi*hi>self.hi,'root enclosure')
        return Interval(lo,hi)
    def absup(self):return max(abs(self.lo),abs(self.hi))

def iv(x):return x if isinstance(x,Interval) else Interval(x)
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Interval(0))
def mv(M,x):return [dot(row,x) for row in M]
def mm(M,N):return [[dot(row,col) for col in zip(*N)] for row in M]

z=F(1247,2000); a=z; b=z*z+z**3; s=a+b
epsilon=a*b*z**3/(s*(a*b+s*s)); delta=epsilon/(1+z)**2
beta=1-epsilon; T=(1-delta)/beta
R=F(23389,25000); S=F(72789,100000); L=F(101778011,10**8)
lam=(Interval(b)+Interval(b*b+4*a*b).root())/2
rho=(lam-b)/lam
require(lam.lo>1 and lam.hi<L and rho.hi<F(39,100),'carry bounds')
U=2**56
wu=isqrt(beta.numerator*U*U//beta.denominator)
if F(wu,U)**2<beta:wu+=1
w=F(wu,U)
require(w*w>=beta and w<1 and (w*L)**2<1,'w normalization')

slacks={}
for t,bound,vector in [(4,R,[1000000,1710962,2377416,2377416]),(3,S,[1000000,2146345,3002947])]:
    matrix=[[z**j if i+j>=4 else F(0) for j in range(1,t+1)] for i in range(1,t+1)]
    row=[bound*vector[i]-sum(matrix[i][j]*vector[j] for j in range(t)) for i in range(t)]
    require(min(row)>0,'positive norm test vector')
    slacks[str(t)]=[str(q) for q in row]

# Work in the rational asymmetric representation, conjugating only through
# the two normalization constants. This avoids square roots of each weight.
weights=[z**i for i in range(1,5)]
Tp=[[Interval(z**j if i+j>=4 else 0) for j in range(1,5)] for i in range(1,5)]
yplus=[Interval(b)/lam,Interval(1),Interval(1),Interval(0)]
yminus=[lam/z,Interval(-1),Interval(-1),Interval(0)]
kp=z*yplus[0]*yplus[0]+b; km=z*yminus[0]*yminus[0]+b
crossnorm=(kp*km).root()
def form(left,M,right):return dot([weights[i]*left[i] for i in range(4)],mv(M,right))
moments={}; power=Tp
for k in range(1,5):
    moments[k]={'alpha':form(yplus,power,yplus)/kp,
                'off':form(yplus,power,yminus)/crossnorm,
                'beta':form(yminus,power,yminus)/km}
    power=mm(power,Tp)
caps={(1,'alpha'):F(68,100),(2,'alpha'):F(69,100),(1,'off'):F(18,100),
      (2,'off'):F(3,100),(1,'beta'):F(5,100),(2,'beta'):F(11,100),(4,'beta'):F(2,100)}
for key,cap in caps.items():require(moments[key[0]][key[1]].absup()<cap,'moment '+str(key))
uv=[[F(47,50),F(9,50)],[F(7,25)*F(47,50),F(7,25)*F(9,50)]]
bare_beta2_lower=moments[2]['beta'].lo/R**2
require(bare_beta2_lower>F(12,100)>uv[1][1],
        'bare strong-run envelope fails: the carry-column factor is necessary')
tmu=F(39,100)
for k in (1,2):
    al,of,be=[caps[k,n] for n in ('alpha','off','beta')]
    for x,y in zip([al,of*tmu,of,be*tmu],[uv[0][0],uv[0][1],uv[1][0],uv[1][1]]):
        require(x<y*R**k,'low power normalized rank')
require(F(69,100)<uv[0][0]*R**2,'all power alpha')
require(F(69,100)*F(2,100)<(uv[1][0]*R**3)**2,'all power lower off')
require(tmu*tmu*F(69,100)*F(2,100)<(uv[0][1]*R**3)**2,'all power upper off')
require(tmu*tmu*F(11,100)*F(2,100)<(uv[1][1]*R**3)**2,'power three beta')
require(tmu*F(2,100)<uv[1][1]*R**4,'all higher beta')
for x,y in zip([F(68,100),F(18,100)*tmu,F(18,100),F(5,100)*tmu],sum(uv,[])):
    require(x<S*y,'single restricted strong edge')
ranknormsq=(1+F(7,25)**2)*(F(47,50)**2+F(9,50)**2)
ranktrace=F(47,50)+F(7,25)*F(9,50)
require(ranknormsq<1 and ranktrace<1,'rank path and cycle contraction')
require(sum(weights)>1 and sum(weights[1:])<1,'global endpoint factors')

# Multiple-five fourth Schatten norms: enumerate the complete trace polynomial.
z5=F(633,1000); aa=F(876716,10**6); bb=F(982645,10**6); tau=F(928171,10**6)
traces={}
for t,cap in ((5,aa),(4,bb)):
    tr=sum((z5**sum(q) for q in itertools.product(range(1,t+1),repeat=4)
            if all(q[i]+q[(i+1)%4]>=t for i in range(4))),F(0))
    require(tr<cap**4,'Schatten fourth power')
    traces[str(t)]=str(tr)
require(0<aa<bb<1 and sum(z5**i for i in range(1,6))>=bb,'Schatten side conditions')
require(sum(z5**i for i in range(3,6))<=aa and sum(z5**i for i in range(2,5))<=bb,'loop endpoint bounds')
require(F(1,4)<aa*bb<tau*tau and tau<1,'monotone square root replacement')
Bbound=z5**10*sum(z5**i for i in range(1,6))/(tau*(1-tau)*(1-aa)*(1-bb))
require(Bbound<113,'multiple five mass')

# Full parity strip H(A,B) from b=a+h..2a+u and b>2a+u.
def total_strip(A,B,sigma,u,v,weighted=False):
    h=0 if u<v else 1
    AB=A*B; ABB=A*B*B; Bs=B*sigma
    require(0<AB<1 and 0<ABB<1 and 0<Bs<1,'strip convergence')
    f1=B**h/((1-B)*(1-AB))
    f2=-B**(u+1)/((1-B)*(1-ABB))
    f3=B**(u+1)*sigma/((1-Bs)*(1-ABB))
    if not weighted:return f1+f2+f3
    # Apply 2(B d/dB-A d/dA)+(v-u) via exact logarithmic derivatives.
    return (f1*(2*h+2*B/(1-B)+v-u)
            +f2*(2*(u+1)+2*B/(1-B)+2*ABB/(1-ABB)+v-u)
            +f3*(2*(u+1)+2*Bs/(1-Bs)+2*ABB/(1-ABB)+v-u))

def geometric(x,n):
    if n<0:return F(0),F(0)
    require(x!=1,'geometric ratio differs from one')
    # sum x^a, sum a*x^a, for 0 <= a <= n.
    return (1-x**(n+1))/(1-x), (x-(n+1)*x**(n+1)+n*x**(n+2))/(1-x)**2

def row_strip(A,B,sigma,u,v,bindex,weighted=False):
    h=0 if u<v else 1; last=bindex-h
    if last<0:return F(0)
    split=min(last,(bindex-u-1)//2)
    q=A/sigma**2
    g,ag=geometric(q,split)
    low=sigma**(bindex-u)*g; low_a=sigma**(bindex-u)*ag
    g1,a1=geometric(A,last); g0,a0=geometric(A,split)
    tot=low+g1-g0; first=low_a+a1-a0
    return B**bindex*((2*bindex+v-u)*tot-2*first if weighted else tot)

def tail_strip(A,B,sigma,u,v,P,weighted=False):
    total=total_strip(A,B,sigma,u,v,weighted)
    prefix=sum((row_strip(A,B,sigma,u,v,j,weighted) for j in range((P-v)//2+1)),F(0))
    require(total>=prefix,'positive omitted tail')
    return total-prefix

eta=R/L; sigma=S/R
# Independently verify several complete finite rows against direct monomials.
identity_checks=0
for uu,vv in itertools.product((1,2),repeat=2):
    for jj in range(0,13):
        for weighted in (False,True):
            testA,testB=F(4,7),F(9,8)
            direct=sum(((2*jj-2*kk+vv-uu if weighted else 1)*testA**kk*testB**jj*sigma**max(jj-2*kk-uu,0)
                        for kk in range(jj-(0 if uu<vv else 1)+1)),F(0))
            require(row_strip(testA,testB,sigma,uu,vv,jj,weighted)==direct,'finite row identity')
            identity_checks+=1
cube=F(252061464497,250000000000)
require(cube**3>=T,'cube upper bound')

pieces={}
for P,pure in ((400,True),(100,False)):
    name=f'P{P}_z1247_2000_{"pure" if pure else "all"}_guarded.json'
    box=json.loads((SOURCE/name).read_text())
    require(box['P']==P and box['pure_only']==pure and box['scale']==U,'box scope')
    expected=P*(P-1) if pure else 2*P*(P+1)*(P-1)//3
    require(box['graphs']==expected,'complete box count')
    require(box['w_units']==wu,'box normalization')
    ll,lh=F(box['lambda_lo_units'],U),F(box['lambda_hi_units'],U)
    require(ll>b and ll*ll-b*ll-a*b<0<lh*lh-b*lh-a*b,'box lambda enclosure')
    require(F(box['T_lo_units'],U)<=T<=F(box['T_hi_units'],U),'box T enclosure')
    if pure:pieces['pure_prefix_400']=F(box['pure_hi_units'],U)
    else:
        pieces['short_prefix_100']=F(box['short_hi_units'],U)
        pieces['mixed_prefix_100']=F(box['mixed_hi_units'],U)

short=F(0);mixed=F(0);feedback=F(0)
J=L*L*beta
require(J<1,'feedback multiplicity convergence')
for u,v in itertools.product((1,2),repeat=2):
    short+=L**(2*v)*tail_strip(eta,eta*L**4,sigma,u,v,100)-L**v*tail_strip(eta,eta*L**2,sigma,u,v,100)
    mixA,mixB=eta/cube**2,eta*L**4*cube**2
    mixed+=L**(2*v)*cube**(v-u)*tail_strip(mixA,mixB,sigma,u,v,100,True)
    fbA,fbB=eta/cube**2,eta*J*beta**-2*cube**2
    M=(L**-2*J+L**-1) if v==1 else (L**-2+L**-1)*J
    feedback+=beta**-v*cube**(v-u)*M/(1-J)/eta*tail_strip(fbA,fbB,sigma,u,v,400)
prefactor=z**8*sum(weights)
pieces['short_tail_100']=prefactor*L**-2/(L-1)/eta*short
pieces['mixed_tail_100']=prefactor*(1+L)*L**-2*T/(1-tmu*tmu)/eta*mixed
pieces['whole_feedback_tail_400']=prefactor*T*feedback
mass=sum(pieces.values(),F(0))
require(all(x>0 for x in pieces.values()),'positive mass components')

qup=F(309017,500000);sqrt5up=F(223607,100000)
require(qup*qup+qup>1 and sqrt5up*sqrt5up>5 and qup<z<z5<1,'Binet constants')
out={'status':'PASS exact finite-mass scalar checks; stored interval boxes checked as inputs',
     'normalization':{'w':str(w),'epsilon':str(epsilon),'delta':str(delta),'beta':str(beta),
                      'T':str(T),'L_squared_w_squared_upper':upper((L*w)**2)},
     'matrix_slacks':slacks,'moment_upper_ceilings':{str(k):{key:upper(val.absup()) for key,val in row.items()} for k,row in moments.items()},
     'rank_norm_squared':str(ranknormsq),'rank_trace':str(ranktrace),'schatten_trace_exact':traces,
     'bare_strong_run_counterexample':'beta_2/R^2 > 3/25 > (7/25)(9/50); the second-column carry factor is necessary',
     'multiple_five_mass_upper_ceiling':upper(Bbound),'finite_row_identity_checks':identity_checks,
     'mass_component_upper_ceilings':{k:upper(v) for k,v in pieces.items()},'total_mass_upper_ceiling':upper(mass)}
(HERE/'check_mass.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('normalization','matrix_slacks','moment_upper_ceilings','schatten_trace_exact')},indent=2))
