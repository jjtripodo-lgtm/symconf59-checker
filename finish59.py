"""Independent endgame for 59_8: cross moments for the two mixed profiles, and the
353-adic Hasse invariant of 7I+J-adj(C59)."""
import itertools, json
from math import gcd, isqrt
from fractions import Fraction
from collections import Counter
from sieve import row_vectors

k=8

def labelled_vectors(a, lengths):
    """All labelled vectors (v_j for each labelled column cycle j) satisfying M1,M2,P."""
    cnt=Counter(lengths); cols=list(cnt.items())
    out=set()
    for vec in row_vectors(a,cols,k,True):
        per_len={b:combo for b,combo in vec}
        # distribute each multiset over the labelled cycles of that length
        idx_by_len={b:[j for j,l in enumerate(lengths) if l==b] for b in cnt}
        choices=[]
        for b in cnt:
            choices.append(set(itertools.permutations(per_len[b])))
        for combo in itertools.product(*choices):
            v=[None]*len(lengths)
            for b,perm in zip(cnt,combo):
                for j,x in zip(idx_by_len[b],perm): v[j]=x
            out.add(tuple(v))
    return sorted(out)

def cross_search(lengths):
    L=lengths
    vecs={a:labelled_vectors(a,L) for a in set(L)}
    # supports summary
    supp={a:sorted({tuple(sorted({L[j] for j,x in enumerate(v) if x})) for v in vecs[a]}) for a in vecs}
    n=len(L); sols=0
    order=sorted(range(n),key=lambda i:len(vecs[L[i]]))
    chosen={}
    def ok(i,v):
        for h,w in chosen.items():
            if sum(L[j]*v[j]*w[j] for j in range(n))!=L[i]*L[h]: return False
        return True
    def rec(t):
        nonlocal sols
        if t==n: sols+=1; return
        i=order[t]
        for v in vecs[L[i]]:
            if ok(i,v):
                chosen[i]=v; rec(t+1); del chosen[i]
                if sols: return
    rec(0)
    return dict(profile=L,vector_counts={a:len(vecs[a]) for a in vecs},supports=supp,full_assignments_found=sols)

def hilbert(a,b,p):
    # Hilbert symbol (a,b)_p for odd prime p, a,b nonzero rationals
    def split(x):
        x=Fraction(x); num,den=x.numerator,x.denominator
        e=0
        while num%p==0: num//=p; e+=1
        while den%p==0: den//=p; e-=1
        u=(num*pow(den,-1,p))%p
        return e,u
    def leg(u): return 1 if pow(u,(p-1)//2,p)==1 else -1
    ea,ua=split(a); eb,ub=split(b)
    eps=1 if ((p-1)//2)%2==0 else -1  # (-1)^((p-1)/2)
    return (eps**(ea*eb))*(leg(ua)**eb)*(leg(ub)**ea)

def hasse_C59(p=353):
    n=59
    G=[[Fraction(0)]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            G[i][j]=Fraction(1)
        G[i][i]=Fraction(8)       # 7 + 1
        G[i][(i+1)%n]-=1; G[i][(i-1)%n]-=1
    # symmetric Gaussian elimination -> diagonal entries d_i (G positive definite: no pivoting needed)
    M=[row[:] for row in G]; d=[]
    for c in range(n):
        piv=M[c][c]; assert piv>0
        d.append(piv)
        for r in range(c+1,n):
            f=M[r][c]/piv
            if f:
                for s in range(c,n): M[r][s]-=f*M[c][s]
    h=1
    for i in range(n):
        for j in range(i+1,n):
            h*=hilbert(d[i],d[j],p)
    det=1
    for x in d: det*=x
    return dict(p=p,hasse=h,det=str(det),det_is_square=(det.denominator == 1 and isqrt(det.numerator)**2 == det.numerator))

if __name__=='__main__':
    out={}
    out['mixed_3^3+5+15^3']=cross_search([3,3,3,5,15,15,15])
    # for 3^8+5^7 report supports only (full search not needed if supports are disjoint)
    L=[3]*8+[5]*7
    out['supports_3^8+5^7']={a:sorted({tuple(sorted({L[j] for j,x in enumerate(v) if x})) for v in labelled_vectors(a,L)}) for a in (3,5)}
    out['hasse_C59']=hasse_C59()
    print(json.dumps(out,indent=1,default=str))
