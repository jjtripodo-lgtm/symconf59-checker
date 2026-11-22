"""Fail-closed exact replay for the unrestricted symmetric configuration 59_8.

Checks parity-free 29,269 -> 15 -> 3 census, all twelve exhaustive shift
witnesses, the two mixed-profile exclusions, the mod-353 anisotropic kernel,
the legacy Hasse cross-checks, and the committed JSON outputs. No assertions:
all guards run identically under Python and Python -O.
"""
from collections import Counter
from math import gcd, isqrt
from pathlib import Path
import json
import subprocess
import sys

from fastsieve2 import feasible
from sieve import partitions, row_vectors

ROOT = Path(__file__).resolve().parent

MOMENT_ALL = {
    '59', '3+21+35', '10+14+35', '3+24+32', '5+24+30',
    '3+5+6+15+30', '3+8+12^2+24', '3+6^2+8+12+24',
    '3+7+14^2+21', '3+7^3+14+21', '3+7^5+21',
    '3^3+5+15^3', '3^3+5^2+10+15^2', '3^3+5^4+15^2',
    '3^8+5^7',
}
PERIODIC = {'59', '3^3+5+15^3', '3^8+5^7'}
MOMENT_ODD = {s for s in MOMENT_ALL if sum(int(p.split('^')[1]) if '^' in p else 1 for p in s.split('+')) % 2}
SHIFTS = (
    ('3+21+35',21,7), ('10+14+35',10,5),
    ('3+24+32',24,8), ('5+24+30',24,6),
    ('3+5+6+15+30',30,15), ('3+8+12^2+24',8,4),
    ('3+6^2+8+12+24',8,4), ('3+7+14^2+21',14,7),
    ('3+7^3+14+21',14,7), ('3+7^5+21',21,7),
    ('3^3+5^2+10+15^2',10,5), ('3^3+5^4+15^2',15,5),
)

def require(ok, context):
    if not ok:
        raise AssertionError('59_8 replay failed: ' + str(context))

def profile_str(p):
    return '+'.join(str(a) + ('^' + str(m) if m>1 else '')
                    for a,m in sorted(Counter(p).items()))

def unpack(s):
    out=[]
    for part in s.split('+'):
        if '^' in part:
            a,m=map(int,part.split('^'))
        else:
            a,m=int(part),1
        out.extend([a]*m)
    return out

def run_checker(name,*args):
    proc = subprocess.run([sys.executable,str(ROOT/name),*(str(x) for x in args)],
                          cwd=ROOT,capture_output=True,text=True,timeout=180)
    require(proc.returncode==0, name+' exited '+str(proc.returncode)+'\n'+proc.stderr[-1000:])
    try:
        return json.loads(proc.stdout)
    except (ValueError,TypeError) as e:
        raise AssertionError('59_8 malformed output from '+name) from e

def verify_census():
    parts=partitions(59)
    require(len(parts)==29269,'total partition count')
    require(len(set(parts))==29269,'duplicate partitions')
    require(all(sum(part)==59 and all(a>=3 for a in part) for part in parts),'partition validity')
    require(len([part for part in parts if len(part)%2])==14647,'odd partition count')
    moment=set(); periodic=set()
    for part in parts:
        name=profile_str(part)
        cols=tuple(sorted(Counter(part).items()))
        if all(feasible(a,cols,8,False) for a,_ in cols):
            moment.add(name)
            if all(feasible(a,cols,8,True) for a,_ in cols):
                periodic.add(name)
    require(moment==MOMENT_ALL,('parity-free moment',sorted(moment^MOMENT_ALL)))
    require(periodic==PERIODIC,('parity-free periodic',sorted(periodic^PERIODIC)))
    for name in MOMENT_ALL:
        cols=tuple(sorted(Counter(unpack(name)).items()))
        require(all(row_vectors(a,cols,8,False) for a,_ in cols),('direct moment',name))
        direct_period=all(row_vectors(a,cols,8,True) for a,_ in cols)
        require(direct_period==(name in PERIODIC),('direct periodic',name))
    return moment,periodic

def verify_shifts():
    require(len(SHIFTS)==12,'shift witness count')
    require({s for s,_,_ in SHIFTS}==MOMENT_ALL-PERIODIC,'witness profile coverage')
    for profile,a,d in SHIFTS:
        L=unpack(profile); cols=tuple(sorted(Counter(L).items()))
        require(sum(L)==59 and a in L and 0<d<a,('invalid witness',profile))
        vectors=row_vectors(a,cols,8,False)
        require(bool(vectors),('no moment vectors',profile,a))
        for vec in vectors:
            num=sum(b*sum(values) for b,values in vec if d%gcd(a,b)==0)
            require(num%a==0,('nonintegral Q',profile,a,d,num))
            require(num//a>=2,('bad shift witness',profile,a,d,num//a))

def verify_353():
    p=353;n=59
    require(all(p%d for d in range(2,isqrt(p)+1)),'353 not prime')
    def vector(x0,x1):
        x=[x0,x1]
        for i in range(1,n+1):
            x.append((7*x[-1]-x[-2])%p)
        require(x[n]==x[0] and x[n+1]==x[1],'periodic recurrence closure')
        return x[:n]
    K=[vector(1,0),vector(0,1)]
    def matvec(x):
        s=sum(x)
        return [7*x[i]+s-x[(i-1)%n]-x[(i+1)%n] for i in range(n)]
    for vec in K:
        require(sum(vec)%p==0,'kernel zero-sum')
        require(all(t%p==0 for t in matvec(vec)),'kernel calculation')
    # 64*S=0 modulo 353, so all kernel vectors have zero sum.
    # The recurrence fixes every coordinate from the first two.
    B=[]
    for v in K:
        row=[]
        for w in K:
            t=sum(x*y for x,y in zip(v,matvec(w)))
            require(t%p==0,'bilinear form divisible by 353')
            row.append(t//p%p)
        B.append(row)
    require(B==[[69,288],[288,69]],('kernel form',B))
    disc=(B[0][1]**2-B[0][0]*B[1][1])%p
    require(disc==170 and pow(disc,(p-1)//2,p)==p-1,('anisotropy',disc))

def verify_endgame():
    finish=run_checker('finish59.py')
    require('mixed_3^8+5^7' not in finish,'fabricated exhaustive mixed case')
    require(finish['supports_3^8+5^7']=={'3':[[3]],'5':[[5]]},'disjoint support')
    mixed=finish['mixed_3^3+5+15^3']
    require(mixed['vector_counts']=={'3':3,'5':3,'15':6},'mixed vector census')
    require(mixed['full_assignments_found']==0,'mixed cross-moment')
    h=finish['hasse_C59'];det=int(h['det'])
    require(h['p']==353 and h['hasse']==-1,'Hasse -1')
    require(h['det_is_square'] is True and isqrt(det)**2==det,'perfect square det')
    controls=run_checker('controls59.py')
    require(controls['det_equals_64_F118_sq'] is True,'Fibonacci determinant')
    require(controls['353_divides_F118'] is True,'353 divides Fibonacci')
    require(controls['random_MMT_hasse_plus1']=='160/160','legacy controls')
    require(controls['pivots_with_nonzero_353_valuation']==[[57,1],[58,1]],'pivot valuations')
    require(controls['hasse_353_G']==-1,'Hasse control')
    return finish,controls

def verify_saved(outputs):
    for name,actual in outputs:
        try:
            stored=json.loads((ROOT/name).read_text(encoding='utf-8'))
        except (OSError,ValueError) as e:
            raise AssertionError('59_8 missing/corrupt saved output: '+name) from e
        require(stored==actual,name+' differs from replay')

def main():
    moment,period=verify_census()
    old=run_checker('sieve.py',59,8)
    require(old['v']==59 and old['k']==8 and old['partitions']==29269 and
            old['odd_cycle_count']==14647,'legacy census')
    require(set(old['moment_survivors'])==MOMENT_ODD,'legacy moment survivors')
    require(set(old['periodic_survivors'])==PERIODIC,'legacy periodic survivors')
    verify_shifts()
    verify_353()
    finish,controls=verify_endgame()
    verify_saved((('sieve59.json',old),('finish59.json',finish),('controls59.json',controls)))
    print('PASS: parity-free 29,269 -> 15 -> 3; direct-profile recheck; 12 shifts; '
          'two mixed exclusions; 353 anisotropic kernel; Hasse and saved outputs')

if __name__=='__main__':
    main()
