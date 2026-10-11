"""How many |B|>=2 gap cases are closed by the new necessary condition (L-C)?
L-C:  H & m in B  =>  prod_{B\{m}} p > prod_A p ;   H & m in C => X > m*prod_A p.
So if (m in B and prod_{B\{m}}p <= prod_A p) or (m in C and X <= m*prod_A p) then NOT H."""
import sys
from math import gcd, prod

def sieve(n):
    spf=list(range(n+1)); i=2
    while i*i<=n:
        if spf[i]==i:
            for j in range(i*i,n+1,i):
                if spf[j]==j: spf[j]=i
        i+=1
    return spf
LIM=1<<22; spf=sieve(LIM)
def fac(n):
    s=[]
    while n>1:
        p=spf[n]; s.append(p)
        while n%p==0: n//=p
    return s
def minimize(lst):
    out=[]
    for x in sorted(set(lst)):
        if not any(x%y==0 for y in out): out.append(x)
    return out
def run(a1,B):
    seq=[a1]; Z={q:0 for q in fac(a1)}; M=minimize(fac(a1)); n=1
    while seq[-1]<=B and len(seq)<200000:
        k=seq[-1]+1
        while True:
            comp=(1<<n)-1
            for q in fac(k):
                z=Z.get(q)
                if z is not None:
                    comp&=z
                    if comp==0: break
            if comp==0: break
            k+=1
        an=k; D=fac(an)
        cand=[b for b in M if gcd(b,an)>1]
        for b in M:
            if gcd(b,an)==1:
                for p in D: cand.append(b*p)
        M=minimize(cand); seq.append(an)
        for q in list(Z):
            if q not in D: Z[q]|=(1<<n)
        for q in D:
            if q not in Z: Z[q]=(1<<n)-1
        n+=1
    return seq,M

hi=int(sys.argv[1]) if len(sys.argv)>1 else 1200
tot=0; closed=0; op=[]
for a1 in range(2,hi+1):
    B=int(12*a1); seq,M=run(a1,B); D1=set(fac(a1))
    for mu in M:
        if mu>B or mu<a1: continue
        S=sorted(fac(mu)); m=max(S); C=sorted(set(S)&D1); Bs=sorted(set(S)-D1); A=sorted(D1-set(S))
        if len(Bs)<2: continue
        tot+=1
        X=prod(Bs); pA=prod(A) if A else 1
        rest=prod([x for x in Bs if x!=m])
        ok = (rest<=pA) if (m in Bs) else (X<=m*pA)
        if ok: closed+=1
        else: op.append((a1,mu,S,A,Bs,X,m,pA,round(mu/a1,3),round(mu/(a1*m),4)))
print("a1<=",hi," |B|>=2 rows:",tot," closed by (L-C):",closed," open:",len(op))
for r in op[:20]: print("   ",r)
