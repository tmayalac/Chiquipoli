"""Independent cross-check of the first-order hypotheses for A16, A32, A64, Z32, Z64.

A second implementation of the certificate's numerical gates, written for
verification and sharing nothing with the Julia pipeline: Python's standard
library only, no IntervalArithmetic.jl, no Julia, no Lean, no NumPy. Interval
endpoints are integer multiples of 2**-256, rounded outward with integer floor,
ceiling and square root; sine and cosine are Taylor polynomials with an
explicit Lagrange remainder after reduction to |x| <= 3. Floating point is used
ONLY to propose a preconditioner, an approximate multiplier vector and (for
A_n) a pin value; every acceptance decision is exact integer arithmetic.

WHAT IS CHECKED, for each polygon: a root of its defining equation is isolated
by sign change with an interval derivative excluding zero; every inactive
squared distance is below 1; every support determinant is positive (strict
convexity, cyclic order); the preconditioned system M mu = b is regular
(||I - CM||_inf < 1), so the multipliers are enclosed and every active-diameter
multiplier is strictly positive; the active equality space has the dimension of
the Euclidean motions. That is the hypothesis of the first-order criterion.

WHAT IS NOT. For Z32 and Z64 the equalities of the sides and of the active
diameters are proved as exact polynomial identities in Q[c,s,y]/(s^2+c^2-1).
For A_n they are checked here only as interval enclosures containing the exact
value; their exact proof is the Julia pipeline's (exact_identities). Root
uniqueness on the whole search interval is the Julia pipeline's too. The A_n
constructor is a port of the verbatim upstream OPTIGON file; the Z_n
constructions are reconstructed from Propositions 1 and 2 of Bingane and Audet
(Arch. Math. 119 (2022)) and must be compared with that paper by hand.

    python3 pipeline/independent/verify.py            # all five
    python3 pipeline/independent/verify.py A32 Z64    # some
    CHIQUI_NO_RECORD=1 ...                            # print only

Writes results/independent/<name>.toml (no timings, so a re-run is identical).
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from pathlib import Path
import hashlib, json, os, re, sys, time

BITS=256
S=1<<BITS
ROOT_WIDTH=Q(1,10**55)
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results'/'independent'

def ceildiv(a,b): return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,a=0,b=None,raw=False):
        if raw: self.lo,self.hi=a,b
        else:
            a=Q(a); b=Q(b) if b is not None else a
            self.lo=a.numerator*S//a.denominator
            self.hi=ceildiv(b.numerator*S,b.denominator)
        assert self.lo<=self.hi
    def __add__(self,v):
        v=iv(v); return I(self.lo+v.lo,self.hi+v.hi,raw=True)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo,raw=True)
    def __sub__(self,v): return self+-iv(v)
    def __rsub__(self,v): return iv(v)+-self
    def __mul__(self,v):
        v=iv(v); a=[self.lo*v.lo,self.lo*v.hi,self.hi*v.lo,self.hi*v.hi]
        return I(min(a)//S,ceildiv(max(a),S),raw=True)
    __rmul__=__mul__
    def __truediv__(self,v):
        v=iv(v); assert not v.lo<=0<=v.hi, 'division across zero'
        r=I(S*S//v.hi,ceildiv(S*S,v.lo),raw=True)
        return self*r
    def __rtruediv__(self,v): return iv(v)/self
    def __pow__(self,k):
        assert k>=0
        if k==0: return I(1)
        if k==2:
            if self.lo<=0<=self.hi: return I(0,ceildiv(max(self.lo**2,self.hi**2),S),raw=True)
            return I(min(self.lo**2,self.hi**2)//S,ceildiv(max(self.lo**2,self.hi**2),S),raw=True)
        r=I(1)
        for _ in range(k): r=r*self
        return r
    def sqrt(self):
        assert self.lo>=0
        a=isqrt(self.lo*S); b=isqrt(self.hi*S)
        if b*b<self.hi*S: b+=1
        return I(a,b,raw=True)
    def mid(self): return Q(self.lo+self.hi,2*S)
    def contains_zero(self): return self.lo<=0<=self.hi

def iv(v): return v if isinstance(v,I) else I(v)

class D:
    __slots__=('v','d')
    def __init__(self,v,d=0): self.v,self.d=iv(v),iv(d)
    def __add__(self,b):
        b=dual(b); return D(self.v+b.v,self.d+b.d)
    __radd__=__add__
    def __neg__(self): return D(-self.v,-self.d)
    def __sub__(self,b): return self+-dual(b)
    def __rsub__(self,b): return dual(b)+-self
    def __mul__(self,b):
        b=dual(b); return D(self.v*b.v,self.d*b.v+self.v*b.d)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=dual(b); return D(self.v/b.v,(self.d*b.v-self.v*b.d)/(b.v**2))
    def __rtruediv__(self,b): return dual(b)/self
    def __pow__(self,k):
        assert k==2; return D(self.v**2,2*self.v*self.d)
    def sqrt(self):
        r=self.v.sqrt(); return D(r,self.d/(2*r))

def dual(v): return v if isinstance(v,D) else D(v)

_PI=[None]
def pi_interval():
    if _PI[0] is None:
        def atan_inverse(q):
            total=sum((Q((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(90)),Q(0))
            err=Q(1,181*q**181)
            return I(total-err,total+err)
        _PI[0]=16*atan_inverse(5)-4*atan_inverse(239)   # Machin
    return _PI[0]

def _taylor(x,cosine):
    term=I(1) if cosine else x
    total=term; xx=x*x
    for k in range(1,80):
        den=(2*k-1)*(2*k) if cosine else (2*k)*(2*k+1)
        term=-term*xx/den; total=total+term
    # Lagrange bound valid for both truncations and every |x|<=3.
    err=ceildiv(3**159*S,factorial(159))
    return I(total.lo-err,total.hi+err,raw=True)

def trig(x,cosine=False):
    """sin or cos of an interval or a dual. Arguments beyond |x|<=3 are reduced
    by m quarter turns, x = r + m*pi/2, with an enclosure of pi."""
    if isinstance(x,D):
        return D(trig(x.v,cosine),(-trig(x.v)*x.d if cosine else trig(x.v,True)*x.d))
    x=iv(x)
    if max(abs(x.lo),abs(x.hi))<=3*S: return _taylor(x,cosine)
    half=pi_interval()*Q(1,2)
    m=round(float(Q(x.lo+x.hi,2*S))/1.5707963267948966)
    r=x-m*half
    assert max(abs(r.lo),abs(r.hi))<=3*S,'argument reduction failed'
    s,c=_taylor(r,False),_taylor(r,True)
    sin_,cos_=[(s,c),(c,-s),(-s,-c),(-c,s)][m%4]
    return cos_ if cosine else sin_

def sin(x): return trig(x)
def cos(x): return trig(x,True)

class P:
    """Sparse exact polynomial; keys are powers (c,s,y), s power is 0 or 1."""
    def __init__(self,v=0):
        self.a=dict(v) if isinstance(v,dict) else ({(0,0,0):Q(v)} if v else {})
        self.a={k:Q(v) for k,v in self.a.items() if v}
    def __add__(self,b):
        b=pol(b); r=self.a.copy()
        for k,v in b.a.items(): r[k]=r.get(k,0)+v
        return P(r)
    __radd__=__add__
    def __neg__(self): return P({k:-v for k,v in self.a.items()})
    def __sub__(self,b): return self+-pol(b)
    def __rsub__(self,b): return pol(b)+-self
    def __mul__(self,b):
        b=pol(b); r={}
        for (c,s,y),v in self.a.items():
            for (cc,ss,yy),w in b.a.items():
                k=(c+cc,s+ss,y+yy); r[k]=r.get(k,0)+v*w
        z={}
        for (c,s,y),v in r.items():
            if s==2:
                k=(c,0,y); z[k]=z.get(k,0)+v
                k=(c+2,0,y); z[k]=z.get(k,0)-v
            else:
                k=(c,s,y); z[k]=z.get(k,0)+v
        return P(z)
    __rmul__=__mul__
    def __truediv__(self,b): return self*Q(1,b)
    def __pow__(self,k):
        assert k==2; return self*self
    def __eq__(self,b): return self.a==pol(b).a
    def serial(self): return [[*k,str(v)] for k,v in sorted(self.a.items())]

def pol(v): return v if isinstance(v,P) else P(v)
C=P({(1,0,0):1}); SIN=P({(0,1,0):1}); Y=P({(0,0,1):1})
TC=[P(1),C]; TS=[P(0),SIN]
for k in range(2,30):
    TC.append(2*C*TC[-1]-TC[-2]); TS.append(2*C*TS[-1]-TS[-2])
PATH64=[0,31,63,30,61,29,60,28,58,27,57,26,56,25,55,24,54,23,53,21,52,19,51,16]
ANGLES64=[1,2,3,5,6,7,8,10,11,12,13,14,15,16,17,18,19,20,22,23,25,26,29]
PEND64=[(30,62,4,-1),(28,59,9,-1),(53,22,21,1),(52,20,24,1),(51,18,27,1),(51,17,28,1)]

def make_vertices(n,sn,cs,y=None):
    z=sn(0); p=[None]*n; p[0]=(z,z); p[n//2]=(z,cs(0))
    if n==32:
        for k in range(1,6): p[16-k]=(sn(k),cs(k))
        for k in range(6,14): p[37-k]=(p[11][0]-sn(k),p[11][1]-cs(k))
        p[10]=(p[24][0]+sn(14),p[24][1]+cs(14))
        p[23]=(p[10][0]-sn(15),p[10][1]-cs(15))
    else:
        for k,(a,b,m) in enumerate(zip(PATH64,PATH64[1:],ANGLES64)):
            sg=1 if k%2==0 else -1
            p[b]=(p[a][0]+sg*sn(m),p[a][1]+sg*cs(m))
        for a,b,m,sg in PEND64: p[b]=(p[a][0]+sg*sn(m),p[a][1]+sg*cs(m))
    for i in range(1,n):
        if p[i] is not None: p[n-i]=(-p[i][0],p[i][1])
    if n==64:
        p[50]=(-cs(0)/2,y); p[14]=(cs(0)/2,y)
        p[15]=(-cs(0)/2+cs(1),y+sn(1)); p[49]=(cs(0)/2-cs(1),y+sn(1))
    assert all(v is not None for v in p)
    return p

def declared_edges(n):
    if n==32:
        edges={(0,16)}
        half=list(zip([0,11,24,10],[11,24,10,23]))+[(0,k) for k in range(12,16)]+[(11,k) for k in range(25,32)]
    else:
        edges={(0,32),(15,50),(14,50),(14,49)}
        half=list(zip(PATH64,PATH64[1:]))+[(a,b) for a,b,_,_ in PEND64]
    for a,b in half:
        edges.add(tuple(sorted((a,b)))); edges.add(tuple(sorted(((-a)%n,(-b)%n))))
    return sorted(edges)

def squared(p,i,j): return (p[j][0]-p[i][0])**2+(p[j][1]-p[i][1])**2

def exact_identities(n):
    p=make_vertices(n,lambda k:TS[k],lambda k:TC[k],Y)
    e2=2-2*C; zero=[]; nonzero={}
    for i in range(n):
        f=squared(p,i,(i+1)%n)-e2
        if f==0: zero.append(i)
        else: nonzero[i]=f
    edges=declared_edges(n)
    for i,j in edges: assert squared(p,i,j)==1,(n,i,j)
    if n==32:
        assert sorted(nonzero)==[9,22]; assert nonzero[9]==nonzero[22]
        formula=(2*(TS[5]-TS[13]+TS[14])-TS[15])**2+TC[15]**2-e2
        assert nonzero[9]==formula
        assert all(s==0 and y==0 for _,s,y in formula.a)
        eqs={'F32':formula.serial()}
    else:
        assert sorted(nonzero)==[13,15,48,50]
        assert nonzero[13]==nonzero[50] and nonzero[15]==nonzero[48]
        # Independently check the exact elimination y=y51+r used by reduced64.
        q=make_vertices(64,lambda k:TS[k],lambda k:TC[k],p[51][1]+Y)
        a=p[51][0]+Q(1,2)
        assert squared(q,51,50)-e2==Y**2+a**2-e2
        assert squared(q,16,15)-e2==(a+TS[29]-TC[1])**2+(TC[29]-TS[1]-Y)**2-e2
        eqs={'F64_51_50':nonzero[50].serial(),'F64_16_15':nonzero[15].serial()}
    return {'identically_zero_side_differences':zero,'root_equation_side_indices':sorted(nonzero),
            'exact_active_diameter_count':len(edges),'equations_in_Q_c_s_y_mod_s_squared_plus_c_squared_minus_1':eqs}
def reduced64(t):
    # y = y51 + sqrt(ell^2-(x51+1/2)^2) selects the published convex branch.
    sn=lambda k:sin(k*t); cs=lambda k:cos(k*t)
    p=make_vertices(64,sn,cs,0*t)
    A=p[51][0]+Q(1,2); e2=2-2*cs(1); r=(e2-A**2).sqrt()
    return (A+sn(29)-cs(1))**2+(cs(29)-sn(1)-r)**2-e2

def equation(n,t):
    if n==64: return reduced64(t)
    x=sin(5*t)-sin(13*t)+sin(14*t)
    return (2*x-sin(15*t))**2+cos(15*t)**2-(2-2*cos(t))

def dec(q,places=18,lower=True):
    q=Q(q); k=10**places
    v=q.numerator*k//q.denominator if lower else ceildiv(q.numerator*k,q.denominator)
    sign='-' if v<0 else ''; v=abs(v)
    return f'{sign}{v//k}.{v%k:0{places}d}'

def enclosure(v,places=24): return [dec(Q(v.lo,S),places,True),dec(Q(v.hi,S),places,False)]

# ---------------------------------------------------------------- A_n (OPTIGON)

def vertices_A(n,t):
    """The vertices of A_n for t an interval: the upstream constructor
    cstrt_audet_ngon.jl (OPTIGON), line by line; indices are the upstream's 1-based."""
    h=n//2; step=3*n//2-2; pi=pi_interval()
    th=lambda k: k*(2*t-pi*Q(1,2))
    a={}; b={}
    a[h-1]=sin(t); a[h+1]=-a[h-1]; b[h-1]=cos(t); b[h+1]=b[h-1]
    a[n-1]=a[h-1]-sin(2*t); a[1]=-a[n-1]; b[n-1]=b[h-1]-cos(2*t); b[1]=b[n-1]
    a[n-2]=a[h-1]-sin(3*t); a[2]=-a[n-2]; b[n-2]=b[h-1]-cos(3*t); b[2]=b[n-2]
    for i in range(1,n//8):
        j=(h-1+i*step)%n
        a[j]=sin(t)-(2*cos(t)-1)*sin(th(i))*sin(th(i+1))/cos(2*t); a[n-j]=-a[j]
        b[j]=cos(t)-(2*cos(t)-1)*sin(th(i))*cos(th(i+1))/cos(2*t); b[n-j]=b[j]
        sg=-1 if i%2 else 1
        for off,k in ((n-1,4*i+2),(n-2,4*i+3),(n,4*i+1)):
            m=(off+i*step)%n
            a[m]=a[j]-sg*sin(k*t); a[n-m]=-a[m]
            b[m]=b[j]-sg*cos(k*t); b[n-m]=b[m]
    a[h]=I(0); b[h]=I(1)
    assert sorted(a)==list(range(1,n)) and sorted(b)==list(range(1,n)),'constructor left a vertex undefined'
    return [(I(0),I(0))]+[(a[i],b[i]) for i in range(1,n)]

def equation_A(n,t):
    x=sin(t)-(2*cos(t)-1)*cos((n//4-2)*t)*sin(n*t/4)/cos(2*t)
    return (2*x+sin((n//2-1)*t))**2+cos((n//2-1)*t)**2-4*sin(t/2)**2

def read_A(n):
    """The declared active graph and the nominal root, parsed from the data the
    Julia pipeline certifies (the graph is data there too: it is CHECKED here)."""
    path=ROOT/'src'/'a16'/'data.jl' if n==16 else ROOT/'cases'/'family'/f'A{n}'/'candidate.jl'
    text=path.read_text(encoding='utf-8')
    block=re.search(r'ACTIVE_EDGES\s*=\s*\[(.*?)\]',text,re.S) if n==16 else re.search(r'active\s*=\s*Tuple\{Int,Int\}\[(.*?)\]',text,re.S)
    edges=sorted(tuple(sorted((int(i),int(j)))) for i,j in re.findall(r'\((\d+),\s*(\d+)\)',block.group(1)))
    z=Q(re.search(r'z_(?:nom|nominal)\s*=\s*big"([0-9.]+)"',text).group(1))
    assert len(edges)==n-1 and len(set(edges))==n-1
    return edges,z,path

# ---------------------------------------------------------------- shared gates

def isolate(equation,lo,hi):
    flo=equation(I(lo)); fhi=equation(I(hi))
    assert flo.lo>0 and fhi.hi<0 or flo.hi<0 and fhi.lo>0,'no sign change on the bracket'
    positive=flo.lo>0
    while hi-lo>ROOT_WIDTH:
        mid=(lo+hi)/2; f=equation(I(mid))
        assert not f.contains_zero(),'precision insufficient to decide sign'
        if (f.lo>0)==positive: lo=mid
        else: hi=mid
    derivative=equation(D(I(lo,hi),1)).d
    assert not derivative.contains_zero(),'derivative contains zero'
    final_left=equation(I(lo)); final_right=equation(I(hi))
    assert final_left.lo>0 and final_right.hi<0 or final_left.hi<0 and final_right.lo>0
    return I(lo,hi), {'lower':dec(lo,60,True),'upper':dec(hi,60,False),'width_below':'1e-55',
            'derivative_lower':dec(Q(derivative.lo,S),12,True),'derivative_upper':dec(Q(derivative.hi,S),12,False),
            'left_endpoint_residual':enclosure(final_left,70),'right_endpoint_residual':enclosure(final_right,70),
            'method':'IVT with exact interval endpoint signs; interval derivative excludes zero'}

def geometry(n,p,ell,y,edges):
    active=set(edges); largest=-1; nearest=None
    for i in range(n):
        for j in range(i+1,n):
            if (i,j) in active: continue
            v=squared(p,i,j)
            assert v.hi<S,('inactive diameter failed',n,i,j)
            if v.hi>largest: largest=v.hi; nearest=(i,j)
    margin=I(1)-I(largest,largest,raw=True).sqrt()
    smallest=None; corner=None
    for i in range(n):
        a=(p[(i+1)%n][0]-p[i][0],p[(i+1)%n][1]-p[i][1])
        for j in range(n):
            if j in (i,(i+1)%n): continue
            det=a[0]*(p[j][1]-p[i][1])-a[1]*(p[j][0]-p[i][0])
            assert det.lo>0,('convexity failed',n,i,j)
            if smallest is None or det.lo<smallest: smallest=det.lo; corner=(i,j)
    return {'inactive_pair_count':n*(n-1)//2-len(edges),'inactive_margin_lower_bound':dec(Q(margin.lo,S),18),
            'nearest_inactive_pair':nearest,'support_determinant_count':n*(n-2),
            'minimum_support_determinant_lower_bound':dec(Q(smallest,S),18),'minimum_support_indices':corner,
            'side_enclosure':enclosure(ell),'perimeter_enclosure':enclosure(n*ell),'y_enclosure':enclosure(y) if y else None}

def consistency_A(n,p,ell,edges):
    """The sides and active diameters of A_n, as interval enclosures: each
    squared length minus its target must CONTAIN zero. Evidence, not proof of
    equality; the exact proof is the Julia pipeline's."""
    e2=ell**2
    for i in range(n):
        assert (squared(p,i,(i+1)%n)-e2).contains_zero(),('side',i)
    for i,j in edges:
        assert (squared(p,i,j)-1).contains_zero(),('active diameter',i,j)
    return {'sides_and_active_diameters':'interval enclosures contain the target; exactness is certified by the Julia pipeline'}

def jacobian(n,p,ell,edges):
    A=[[I(0) for _ in range(2*n+1)] for _ in range(n+len(edges))]
    for i in range(n):
        j=(i+1)%n
        for k in (0,1):
            v=(p[j][k]-p[i][k])/ell; A[i][2*i+k]=-v; A[i][2*j+k]=v
        A[i][-1]=I(-1)
    for row,(i,j) in enumerate(edges,n):
        for k in (0,1):
            v=p[j][k]-p[i][k]; A[row][2*i+k]=-v; A[row][2*j+k]=v
    return A

# Floating point, used only to PROPOSE: a preconditioner, a centre, a pin.
def fmat(M): return [[float(v.mid()) for v in row] for row in M]

def inverse(Mf):
    n=len(Mf); W=[row[:]+[1.0 if i==j else 0.0 for j in range(n)] for i,row in enumerate(Mf)]
    for c in range(n):
        r=max(range(c,n),key=lambda i:abs(W[i][c])); W[c],W[r]=W[r],W[c]
        piv=W[c][c]; assert abs(piv)>1e-12,'singular candidate'
        W[c]=[v/piv for v in W[c]]
        for i in range(n):
            if i!=c and W[i][c]!=0.0:
                f=W[i][c]; Wc=W[c]; W[i]=[a-f*b for a,b in zip(W[i],Wc)]
    return [row[n:] for row in W]

def matvec(M,x): return [sum(a*b for a,b in zip(row,x)) for row in M]

def propose_pin(M,b,n):
    """For A_n the multipliers form a one-parameter affine family. Reduce the
    float system, take a pin column with large kernel component and the pin value
    that centres the active-diameter multipliers; return (column, value)."""
    Mf=fmat(M); bf=[float(v.mid()) for v in b]; rows=len(Mf); cols=len(Mf[0])
    W=[r[:]+[bf[i]] for i,r in enumerate(Mf)]; pivots=[]; r=0
    for c in range(cols):
        if r==rows: break
        k=max(range(r,rows),key=lambda i:abs(W[i][c]))
        if abs(W[k][c])<1e-9: continue
        W[r],W[k]=W[k],W[r]; W[r]=[v/W[r][c] for v in W[r]]
        for i in range(rows):
            if i!=r: f=W[i][c]; W[i]=[a-f*bb for a,bb in zip(W[i],W[r])]
        pivots.append(c); r+=1
    free=[c for c in range(cols) if c not in pivots]; assert len(free)==1,('kernel of the multiplier system',len(free))
    f=free[0]; xp=[0.0]*cols; nu=[0.0]*cols; nu[f]=1.0
    for i,c in enumerate(pivots): xp[c]=W[i][cols]; nu[c]=-W[i][f]
    lo=-1e300; hi=1e300
    for j in range(n,cols):
        if nu[j]>1e-12: lo=max(lo,-xp[j]/nu[j])
        elif nu[j]<-1e-12: hi=min(hi,-xp[j]/nu[j])
    assert lo<hi,'no positive multiplier vector exists on this graph'
    s=(lo+hi)/2 if hi<1e299 and lo>-1e299 else (lo+1.0 if hi>=1e299 else hi-1.0)
    col=max(range(n,cols),key=lambda j:abs(nu[j]))
    return col, xp[col]+s*nu[col]

def system(n,A,pin):
    omitted=[0,1,n]  # x0,y0,x_(n/2): the motion restriction has determinant -1
    keep=[k for k in range(2*n+1) if k not in omitted]
    M=[[row[k] for row in A] for k in keep]
    b=[I(n if k==2*n else 0) for k in keep]
    if pin=='auto':
        pin=propose_pin(M,b,n)
    if pin is not None:
        col,val=pin; row=[I(0) for _ in range(len(A))]; row[col]=I(1); M.append(row); b.append(I(Q(val)))
    assert len(M)==len(M[0])
    return M,b,omitted,pin

def preconditioner(M,b):
    Mf=fmat(M); bf=[float(v.mid()) for v in b]; Cf=inverse(Mf)
    mu=matvec(Cf,bf)
    for _ in range(2):
        res=[x-y for x,y in zip(bf,matvec(Mf,mu))]; mu=[m+d for m,d in zip(mu,matvec(Cf,res))]
    fixed=lambda v:(lambda q:q.numerator//q.denominator)(Q(v)*S)
    return [[fixed(v) for v in row] for row in Cf],[fixed(v) for v in mu]

def verify_linear(n,M,b,C0,mu0):
    dim=len(M)
    # Exact matrix products. Accumulate at scale S^2, without intermediate rounding.
    em=0
    for i in range(dim):
        rowbound=0
        for j in range(dim):
            low=high=0
            for k in range(dim):
                c=C0[i][k]; v=M[k][j]
                if c>=0: low+=c*v.lo; high+=c*v.hi
                else: low+=c*v.hi; high+=c*v.lo
            target=S*S if i==j else 0
            rowbound+=max(abs(target-low),abs(target-high))
        em=max(em,rowbound)
    assert em<S*S,'regularity test failed'
    # b-M*mu0 enclosure at scale S^2 (b may itself have nonzero width).
    residual=[]
    for i in range(dim):
        low=high=0
        for v,u in zip(M[i],mu0):
            if u>=0: low+=v.lo*u; high+=v.hi*u
            else: low+=v.hi*u; high+=v.lo*u
        residual.append((b[i].lo*S-high,b[i].hi*S-low))
    dmax=0
    for row in C0:
        low=high=0
        for c,(a,bh) in zip(row,residual):
            if c>=0: low+=c*a; high+=c*bh
            else: low+=c*bh; high+=c*a
        dmax=max(dmax,abs(low),abs(high))
    error=Q(dmax,S*(S*S-em))
    minimum=min(Q(v,S)-error for v in mu0[n:]); assert minimum>0
    return {'system_dimension':dim,'regularity_norm_upper_bound':dec(Q(em,S*S),18,False),
            'uniform_multiplier_error_upper_bound':dec(error,18,False),
            'minimum_diameter_multiplier_lower_bound':dec(minimum,18,True),
            'certified_rank':2*n-2,'active_equality_kernel_dimension':3,
            'omitted_stationarity_recovery':'Rigid-motion annihilation; restriction determinant = -1 exactly.'}, error

# ---------------------------------------------------------------- the polygons

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def spec(name):
    kind,n=name[0],int(name[1:])
    if kind=='Z':
        lo,hi=(Q('0.09817442866'),Q('0.09817442868')) if n==32 else (Q('0.04908735339'),Q('0.04908735341'))
        def vertices(t): return interval_vertices(n,t)
        return dict(n=n,edges=declared_edges(n),eq=lambda t:equation(n,t),bracket=(lo,hi),vertices=vertices,
            pin=(n+declared_edges(n).index((0,11)),Q(11,200)) if n==32 else None,exact=True,
            sources={'constructor':'Bingane and Audet, Arch. Math. 119 (2022), Section 4, Props. 1 and 2; reconstructed from the stated paths, pendant edges and reflection'})
    edges,z,path=read_A(n)
    def vertices(t):
        p=vertices_A(n,t); return p,2*sin(t/2),None
    up=ROOT/'cases'/'upstream'/'optigon'/'cstrt_audet_ngon.jl'
    return dict(n=n,edges=edges,eq=lambda t:equation_A(n,t),bracket=(z-Q(11,10**10),z+Q(23,10**10)),vertices=vertices,
        pin='auto',exact=False,
        sources={'constructor':'OPTIGON cstrt_ngon/cstrt_audet_ngon.jl, ported line by line',
                 'upstream_sha256':sha(up),'graph_and_nominal_root_file':str(path.relative_to(ROOT)),'graph_and_nominal_root_sha256':sha(path)})

def interval_vertices(n,t):
    sn={k:sin(k*t) for k in range(30)}; cs={k:cos(k*t) for k in range(30)}
    p=make_vertices(n,sn.__getitem__,cs.__getitem__,I(0))
    y=None
    if n==64:
        y=p[51][1]+(2-2*cs[1]-(p[51][0]+Q(1,2))**2).sqrt()
        p=make_vertices(n,sn.__getitem__,cs.__getitem__,y)
    return p,2*sin(t/2),y

def compact(exact):
    """The exact identities were checked in full; the record keeps their shape."""
    e=dict(exact); eqs=e.pop('equations_in_Q_c_s_y_mod_s_squared_plus_c_squared_minus_1')
    e['proved_in']='Q[c,s,y]/(s^2+c^2-1), by coefficient comparison'
    e['root_equations_terms']={k:len(v) for k,v in eqs.items()}
    return e

def verify(name,sp=None):
    sp=sp or spec(name); n=sp['n']; edges=sp['edges']
    exact=exact_identities(n) if sp['exact'] else None
    t,root=isolate(sp['eq'],*sp['bracket'])
    pi=pi_interval(); assert t.lo>0 and t.hi*n<pi.lo
    p,ell,y=sp['vertices'](t)
    cons=None if sp['exact'] else consistency_A(n,p,ell,edges)
    geo=geometry(n,p,ell,y,edges)
    A=jacobian(n,p,ell,edges); M,b,omitted,pin=system(n,A,sp['pin'])
    C0,mu0=preconditioner(M,b)
    linear,error=verify_linear(n,M,b,C0,mu0)
    rec={'name':name,'n':n,'status':'CERTIFIED: hypotheses of the first-order criterion hold',
         'precision_bits':BITS,'implementation':'pipeline/independent/verify.py (Python standard library; no Julia, no IntervalArithmetic.jl)',
         'sources':sp['sources'],'t_enclosure':enclosure(t),'root':root,
         'sides_and_diameters':compact(exact) if exact is not None else cons,
         'active_diameter_edges':[list(e) for e in edges],'geometry':geo,'linear_certificate':linear,
         'omitted_ambient_coordinates':omitted,
         'multiplier_pin':{'column':pin[0],'value':str(Q(pin[1]).limit_denominator(10**12))+' (approx.; a float used as an exact dyadic)'} if pin else None,
         'conclusion':'Strict local maximality modulo orientation-preserving Euclidean motions among convex equilateral small polygons. Global maximality is not established.'}
    return rec

def selftest():
    """Planted defects: every one must be REJECTED, or the verifier proves nothing."""
    def edit(name,**kw): sp=spec(name); sp.update(kw); return sp
    def bump(sp):
        old=sp['vertices']
        def vertices(t):
            p,ell,y=old(t); p=list(p); p[3]=(p[3][0]+I(Q(1,10**9)),p[3][1]); return p,ell,y
        return dict(sp,vertices=vertices)
    a32=spec('A32'); z32=spec('Z32'); a16=spec('A16')
    cases=[('A32: an active edge replaced',edit('A32',edges=sorted(set(a32['edges'])-{a32['edges'][5]}|{(1,30)}))),
           ('A16: an active edge dropped',edit('A16',edges=a16['edges'][:-1])),
           ('A32: a vertex moved by 1e-9',bump(a32)),
           ('A32: root bracket off the root',edit('A32',bracket=(a32['bracket'][0]+Q(1,10**5),a32['bracket'][1]+Q(2,10**5)))),
           ('Z32: an active edge dropped',edit('Z32',edges=z32['edges'][1:])),
           ('Z32: a wrong pin (a side column)',edit('Z32',pin=(0,Q(11,200))))]
    bad=0
    for label,sp in cases:
        try:
            verify(sp.get('name','?'),sp); print(f'  NOT REJECTED  {label}'); bad+=1
        except (AssertionError,ZeroDivisionError,KeyError,ValueError) as e:
            print(f'  rejected      {label}  ({str(e)[:50]})')
    return bad

def toml_value(v):
    if isinstance(v,bool): return 'true' if v else 'false'
    if isinstance(v,int): return str(v)
    if isinstance(v,str): return json.dumps(v,ensure_ascii=False)
    if isinstance(v,(list,tuple)): return '['+', '.join(toml_value(x) for x in v)+']'
    raise TypeError(type(v))

def toml_dump(d,prefix=''):
    """Scalars and arrays first, then sub-tables; None is omitted."""
    lines=[]; tables=[]
    for k,v in d.items():
        if v is None: continue
        if isinstance(v,dict): tables.append((k,v))
        else: lines.append(f'{k} = {toml_value(v)}')
    for k,v in tables:
        name=f'{prefix}.{k}' if prefix else k
        lines+=['',f'[{name}]']+toml_dump(v,name)
    return lines

def summary(rec):
    g=rec['geometry']; l=rec['linear_certificate']
    return (f"t in [{rec['t_enclosure'][0][:14]}..]; perimeter {rec['geometry']['perimeter_enclosure'][0][:12]}..; "
            f"inactive margin > {g['inactive_margin_lower_bound'][:10]}; min support det > {g['minimum_support_determinant_lower_bound'][:10]}; "
            f"min multiplier > {l['minimum_diameter_multiplier_lower_bound'][:10]}; ||I-CM|| < {l['regularity_norm_upper_bound'][:22]}")

def main(argv):
    if '--self-test' in argv:
        bad=selftest(); print('SELF-TEST:', 'PASSED' if not bad else f'FAILED ({bad} defects not rejected)'); return 1 if bad else 0
    names=[a for a in argv if not a.startswith('-')] or ['A16','A32','A64','Z32','Z64']
    write=os.environ.get('CHIQUI_NO_RECORD')!='1'
    bad=0
    for name in names:
        started=time.monotonic()
        try:
            rec=verify(name)
        except AssertionError as e:
            print(f'{name}  FAIL  {e}'); bad+=1; continue
        print(f'{name}  PASS  {summary(rec)}  ({time.monotonic()-started:.1f}s)',flush=True)
        if write:
            rec['verifier_sha256']=sha(__file__)
            OUT.mkdir(parents=True,exist_ok=True)
            (OUT/f'{name}.toml').write_text('# Independent cross-check of '+name+' — written by pipeline/independent/verify.py; do not edit.\n'+'\n'.join(toml_dump(rec))+'\n')
    if bad: print(f'INDEPENDENT CROSS-CHECK: FAILED ({bad} of {len(names)})'); return 1
    print(f'INDEPENDENT CROSS-CHECK: PASSED ({len(names)} of {len(names)}: {", ".join(names)})'); return 0

if __name__=='__main__':
    sys.exit(main(sys.argv[1:]))
