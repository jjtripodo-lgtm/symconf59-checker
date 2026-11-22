"""Exact sieve using per-length aggregates. For row length a and column length b with
multiplicity m, the feasible (S, Q) = (sum of the m block column sums, sum of squares) pairs
are computed by DP. M1: sum_b b*S_b = k a ; M2: sum_b b*Q_b = a(a+k-3).
Periodicity uses only u-totals: Q_i(d) = sum_{b: gcd(a,b)|d} b*S_b/a <= 1."""
import sys, json, itertools
from math import gcd
from collections import Counter
from sieve import partitions

def pairs(a,b,m,k,t1,t2):
    step=a//gcd(a,b); vals=[x for x in range(0,k+1) if x%step==0]
    st={(0,0)}
    for _ in range(m):
        st={(s+x,q+x*x) for s,q in st for x in vals if b*(s+x)<=t1 and b*(q+x*x)<=t2}
    return sorted(st)

def feasible(a,cols,k,period):
    t1=k*a; t2=a*(a+k-3)
    P=[(b,pairs(a,b,m,k,t1,t2)) for b,m in cols]
    # combine across distinct lengths keeping the S_b choices (for periodicity)
    states={(0,0):[()]} if period else {(0,0):None}
    for b,pl in P:
        new={}
        for (s1,s2),hist in states.items():
            for S,Q in pl:
                n1=s1+b*S; n2=s2+b*Q
                if n1>t1 or n2>t2: continue
                key=(n1,n2)
                if period:
                    new.setdefault(key,set()).update(h+((b,S),) for h in hist)
                else: new[key]=None
        states={k_:(list(v) if period else None) for k_,v in new.items()}
    if (t1,t2) not in states: return False
    if not period: return True
    for h in states[(t1,t2)]:
        if all(sum(b*S for b,S in h if d%gcd(a,b)==0)//a<=1 for d in range(1,a)):
            return True
    return False

def run(v,k):
    parts=partitions(v); odd=[p for p in parts if len(p)%2]
    mom=[];per=[]
    for p in odd:
        cnt=Counter(p); cols=sorted(cnt.items())
        if all(feasible(a,cols,k,False) for a in cnt):
            mom.append(p)
            if all(feasible(a,cols,k,True) for a in cnt): per.append(p)
    return len(parts),len(odd),mom,per

if __name__=='__main__':
    v,k=int(sys.argv[1]),int(sys.argv[2])
    n,no,mom,per=run(v,k)
    fmt=lambda p:'+'.join(f"{b}^{m}" if m>1 else str(b) for b,m in sorted(Counter(p).items()))
    print(json.dumps(dict(v=v,k=k,partitions=n,odd=no,moment_count=len(mom),periodic_count=len(per),
        moment=[fmt(p) for p in mom],periodic=[fmt(p) for p in per]),indent=1))
