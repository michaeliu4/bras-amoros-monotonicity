#!/usr/bin/env python3
"""Reconstruct binary and witnessed-reservoir arithmetic exactly.
All checks survive python -O.
This does not evaluate any raw-graph bridge or analytic graph mass.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
CHECKS=0

def require(x,msg):
    global CHECKS
    CHECKS+=1
    if not x:raise RuntimeError(msg)

def padd(a,b):
    r=[0]*max(len(a),len(b))
    for i,c in enumerate(a):r[i]+=c
    for i,c in enumerate(b):r[i]+=c
    while len(r)>1 and not r[-1]:r.pop()
    return tuple(r)

def pmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):r[i+j]+=c*d
    while len(r)>1 and not r[-1]:r.pop()
    return tuple(r)

def peval(p,x):
    ans=Q(0)
    for a in reversed(p):ans=x*ans+a
    return ans

class Rat:
    def __init__(self,n=0,d=(1,)):
        self.n=(n,) if isinstance(n,int) else tuple(n)
        self.d=tuple(d)
    @staticmethod
    def make(x):return x if isinstance(x,Rat) else Rat(x)
    def __add__(a,b):
        b=Rat.make(b)
        return Rat(padd(pmul(a.n,b.d),pmul(b.n,a.d)),pmul(a.d,b.d))
    __radd__=__add__
    def __neg__(a):return Rat(tuple(-x for x in a.n),a.d)
    def __sub__(a,b):return a+-Rat.make(b)
    def __rsub__(a,b):return Rat.make(b)+-a
    def __mul__(a,b):
        b=Rat.make(b);return Rat(pmul(a.n,b.n),pmul(a.d,b.d))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=Rat.make(b);return Rat(pmul(a.n,b.d),pmul(a.d,b.n))
    def __rtruediv__(a,b):return Rat.make(b)/a
    def __pow__(a,k):
        result=Rat(1)
        while k:
            if k%2:result=result*a
            k//=2
            if k:a=a*a
        return result
    def eval(a,x):return peval(a.n,x)/peval(a.d,x)
    def coefficients(a,N):
        require(a.d[0]==1,'formal unit denominator')
        result=[]
        for j in range(N+1):
            value=a.n[j] if j<len(a.n) else 0
            for k in range(1,min(j+1,len(a.d))):value-=a.d[k]*result[j-k]
            result.append(value)
        return result

N=1500
z=Rat((0,1));u=z**2+z**3;s=z+u;c=z+z**2;v=u*s
fib=[0,1]
for _ in range(2,N+2):fib.append(fib[-1]+fib[-2])
def series_sum(terms):
    result=[0]*(N+1)
    for t in terms:
        for i,n in enumerate(t.coefficients(N)):result[i]+=n
    return result

def k(k):
    a=sum((z**i for i in range((k+1)//2,k+1)),Rat(0))
    b=sum((z**(i+j) for i in range(1,k+1) for j in range(1,k+1) if i+j>=k),Rat(0))
    return (1+a)/(1-b)
a=z**4/(1-z);b=z**8*(7-6*z)/(1-z)**2
Mterms=[z**q*k(q)*k(q-1) for q in (6,7,8)]+[z**9*(1+a)**2/((1-z)*(1-b)**2)]
H=(z**4+z**5)/((1-u)*(1-u-z**4-z**5))
J=(2*z**12+4*z**14+2*z**15)/((1-2*z**5-z**6)*(1-u)*(1-3*z**4-2*z**5-z**6))
K=z**9/((1-u)**2*(1-u-z**4))
M=series_sum(Mterms);HH=H.coefficients(N);JJ=J.coefficients(N);KK=K.coefficients(N)
W=[a+b+c+d for a,b,c,d in zip(M,HH,JJ,KK)]
require(min(M+HH+JJ+KK)>=0,'nonnegative source majorants')
require(all(25*W[g]<=13*fib[g] for g in range(500)),'combined W initial budget')
r=Q(809,500)
require(r*r<r+1,'Fibonacci elementary base')
Wvalue=sum((t.eval(Q(63,100)) for t in Mterms+[H,J,K]),Q(0))
require(Wvalue<50,'W sharpened value')
require(all(1000*W[g]<=13*fib[g] for g in range(141,500)),'W sharpened finite input')
require(Q(63,100)*r>1 and 50*r*r/(Q(63,100)*r)**500<Q(13,1000),'W sharpened tail')

Cs=z**3*(1+u)/(1-v);Ce=z**6/((1-u)*(1-u**2));A=(1+z**2)/(1-2*z**3-z**4)
def Fs(t):
    return [Cs,z**6*u*(1+u)*t/((1-v)*(1-v*t)),z**6*t*(1+s*t)/((1-v*t)*(1-v*t**2))]
def Fe(t):
    return [Ce,z**9*t/((1-u**2)*(1-u)*(1-u*t)),z**9*u*t**2/((1-u*t)*(1-u**2)*(1-u**2*t)),z**9*u*t**4/((1-u*t)*(1-u**2*t)*(1-u**2*t**2))]
def failures(F):
    return [z*t/(1-c) for t in F(Rat(1))]+[-z*t/(1-c)+z*A*t for t in F(c)]
Ts=(z*Cs/(1-c)).coefficients(N);Te=(z*Ce/(1-c)).coefficients(N)
Us_terms=failures(Fs);Ue_terms=failures(Fe)
Us=series_sum(Us_terms);Ue=series_sum(Ue_terms)
require(min(Us+Ue)>=0,'nonnegative failure majorants')
Es=(1+z)*(1+z**2)**2/(1-v);Ee=z**4*(1+z+z**2)/((1-u)*(1-u**2))
identity_s=z*Cs/(1-c)-1/(1-c)+Es
identity_e=z*Ce/(1-c)-z**4/(1-c)+Ee-z**9*(2+2*z+z**2)/((1-u)*(1-u**2))
require(not any(identity_s.n) and not any(identity_e.n),'exact positive-error rational identities')
Svalue=sum((t.eval(Q(5,8)) for t in [Es,Ee]+Us_terms+Ue_terms),Q(0))
require(Svalue<78,'witness positive error at5/8')
require(78*r*r*Q(800,809)**1500<Q(1,10000),'witness error infinite tail')
require(all(10000*(fib[g+1]+fib[g-3])>=18541*fib[g] for g in (16,17)),'Fibonacci reservoir recurrence seeds')
require(all(500*(max(0,Ts[g]-Us[g])+max(0,Te[g]-Ue[g]))>=927*fib[g] for g in range(305,1500)),'nonbinary finite input')
for rho in (Q(63,100),):
    require(rho<1 and rho**8*(7-6*rho)/(1-rho)**2<1,'M geometric tail convergence')
    for q in range(5,9):
        require(sum(rho**(i+j) for i in range(1,q+1) for j in range(1,q+1) if i+j>=q)<1,'M reflection convergence')
for rho in (Q(63,100),):
    require(all(x<1 for x in [rho**2+rho**3,2*rho**5+rho**6,3*rho**4+2*rho**5+rho**6,rho**2+rho**3+rho**4]),'J K convergence')
require(sum(Q(63,100)**i for i in range(2,6))<1,'H convergence')
rho=Q(5,8);uu=rho**2+rho**3;ss=rho+uu;cc=rho+rho**2;vv=uu*ss
require(all(x<1 for x in [vv,vv*cc,vv*cc**2,uu,uu**2,uu*cc,uu**2*cc,uu**2*cc**2,2*rho**3+rho**4]),'witness geometric convergence')

# Read-only agreement checks against the arrays actually used by the comparator.
capacity_path=ROOT/'data/exact-capacity-lower.json'
binary_path=ROOT/'data/refined-binary-coefficients.json'
cap=json.loads(capacity_path.read_text())['rows'];bin=json.loads(binary_path.read_text())['rows']
for g in range(N+1):
    lb=max((12*fib[g]+24)//25,fib[g]-W[g]);ls=max(0,Ts[g]-Us[g]);le=max(0,Te[g]-Ue[g])
    require(cap[g]['g']==g and cap[g]['free_safe_lower']==ls and cap[g]['free_early_one_lower']==le,'nonbinary production row '+str(g))
    require(bin[g]['g']==g and bin[g]['spent_cost_majorant']==W[g] and bin[g]['free_binary_lower']==lb,'binary production row '+str(g))

report={'pass':True,'scope':'Exact capacity and reservoir coefficient arithmetic','checks':CHECKS,'coefficient_degree':N,'W_63_over_100':str(Wvalue),'positive_error_5_over_8':str(Svalue),'binary_all_g':'max(ceil(12 Fib_g/25), Fib_g-W_g)','nonbinary_from_305':'927/500 Fib_g','binary_from_141':'987/1000 Fib_g','combined_from_305':'2841/1000 Fib_g','stored_arrays_match':True,'hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (capacity_path,binary_path,Path(__file__))}}
(BASE/'numerical_input_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('W_63_over_100','positive_error_5_over_8','scalar_898_approximate_diagnostic','hashes')},indent=2))
