"""Independent re-implementation (written from the mathematical statement only) of the
deficiency-two cycle-profile sieve for symmetric configurations v_k, v = k^2-k+3.

For a v x v 0/1 matrix A, row/column sums k, no 2x2 all-ones rectangle:
  AA^T = (k-1)I + J - R, A^T A = (k-1)I + J - C, R,C 2-regular (unions of cycles, length>=3),
  RA = AC, same cycle multiset L. Block A_ij (row cycle length a=l_i, column cycle b=l_j) has
  constant column sum v_ij, with a*u_ij = b*v_ij, v_ij in [0,k].
  (M1) sum_j l_j v_ij = k * l_i
  (M2) sum_j l_j v_ij^2 = l_i (l_i + k - 3)
  (X)  sum_j l_j v_ij v_hj = l_i l_h   for distinct row cycles i != h
  (P)  for 0<d<a: sum_{j: gcd(a,l_j) | d} u_ij <= 1   (periodicity -> shared support)
  parity: number of cycles c must be odd.
"""
import sys, json, itertools
from math import gcd
from functools import lru_cache
from collections import Counter

def partitions(n, minpart=3):
    # nonincreasing partitions of n with parts >= minpart, as tuples (descending)
    out=[]
    def rec(rem, maxp, acc):
        if rem==0: out.append(tuple(acc)); return
        for p in range(min(rem,maxp), minpart-1, -1):
            if rem-p==0 or rem-p>=minpart:
                acc.append(p); rec(rem-p,p,acc); acc.pop()
    rec(n,n,[])
    return out

def row_vectors(a, cols, k, check_period):
    """cols: list of (b, multiplicity m) for distinct column-cycle lengths.
    Return all assignments v[j] for every individual column cycle (expanded),
    represented per distinct length as a sorted tuple of values (multiset), satisfying M1,M2,(P)."""
    target1=k*a; target2=a*(a+k-3)
    # allowed values for a block with column-cycle length b
    allowed={}
    for b,_ in cols:
        step=a//gcd(a,b)
        allowed[b]=[x for x in range(0,k+1) if x%step==0]
    res=[]
    cols=sorted(cols)
    def rec(idx, s1, s2, acc):
        if s1>target1 or s2>target2: return
        if idx==len(cols):
            if s1==target1 and s2==target2:
                res.append(tuple(acc))
            return
        b,m=cols[idx]
        # choose a multiset of m values from allowed[b] (nondecreasing)
        for combo in itertools.combinations_with_replacement(allowed[b], m):
            t1=s1+b*sum(combo); t2=s2+b*sum(x*x for x in combo)
            if t1>target1 or t2>target2: continue
            acc.append((b,combo)); rec(idx+1,t1,t2,acc); acc.pop()
    rec(0,0,0,[])
    if check_period:
        good=[]
        for vec in res:
            ok=True
            for d in range(1,a):
                q=0
                for b,combo in vec:
                    if d % gcd(a,b)==0:
                        q+=sum(b*x for x in combo)//a
                if q>=2: ok=False;break
            if ok: good.append(vec)
        res=good
    return res

def analyse(v,k, limit=None):
    parts=partitions(v)
    odd=[p for p in parts if len(p)%2==1]
    moment_ok=[]; period_ok=[]
    for p in odd:
        cnt=Counter(p); cols=list(cnt.items())
        surv_m=True; surv_p=True
        for a in cnt:
            if not row_vectors(a,cols,k,False): surv_m=False; break
        if not surv_m: continue
        moment_ok.append(p)
        for a in cnt:
            if not row_vectors(a,cols,k,True): surv_p=False; break
        if surv_p: period_ok.append(p)
    return parts,odd,moment_ok,period_ok

if __name__=='__main__':
    v,k=int(sys.argv[1]),int(sys.argv[2])
    parts,odd,mom,per=analyse(v,k)
    fmt=lambda p:'+'.join(f"{b}^{m}" if m>1 else str(b) for b,m in sorted(Counter(p).items()))
    print(json.dumps(dict(v=v,k=k,partitions=len(parts),odd_cycle_count=len(odd),
        moment_survivors=[fmt(p) for p in mom],periodic_survivors=[fmt(p) for p in per]),indent=1))
