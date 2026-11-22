"""Exact controls for the 59_8 endgame: det(G)=64*F_118^2, 353 | F_118, pivot valuations,
Hilbert-symbol sanity, and Hasse(MM^T)=+1 on random integer matrices."""
import random, json
from math import isqrt
from fractions import Fraction
from finish59 import hilbert, hasse_C59
out={}
d=int(hasse_C59()['det']); a,b=0,1
for _ in range(118): a,b=b,a+b
out['det_equals_64_F118_sq']=d==64*a*a; out['353_divides_F118']=a%353==0
def diag(G):
    n=len(G); M=[[Fraction(x) for x in r] for r in G]; dd=[]
    for c in range(n):
        piv=M[c][c]
        if piv==0: return None
        dd.append(piv)
        for r in range(c+1,n):
            f=M[r][c]/piv
            for s in range(c,n): M[r][s]-=f*M[c][s]
    return dd
def hasse(G,p):
    dd=diag(G)
    if dd is None: return None
    h=1
    for i in range(len(dd)):
        for j in range(i+1,len(dd)): h*=hilbert(dd[i],dd[j],p)
    return h
random.seed(1); tot=good=0
for t in range(40):
    n=random.randint(3,9); A=[[random.randint(-6,6) for _ in range(n)] for _ in range(n)]
    G=[[sum(A[i][k]*A[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
    for p in (3,5,7,353):
        h=hasse(G,p)
        if h is None: continue
        tot+=1; good+=(h==1)
out['random_MMT_hasse_plus1']=f"{good}/{tot}"
n=59; G=[[1]*n for _ in range(n)]
for i in range(n):
    G[i][i]=8; G[i][(i+1)%n]-=1; G[i][(i-1)%n]-=1
dd=diag(G)
def val(x,p=353):
    num,den=x.numerator,x.denominator; e=0
    while num%p==0: num//=p;e+=1
    while den%p==0: den//=p;e-=1
    return e
out['pivots_with_nonzero_353_valuation']=[(i,val(x)) for i,x in enumerate(dd) if val(x)]
out['hasse_353_G']=hasse(G,353)
print(json.dumps(out,indent=1))
