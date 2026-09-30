# Python mirror of ChiquipoliFamily/Interval/{FI,Base,Interp,Term}.lean — the SAME integer
# operations, so data computed here passes the kernel's `subset` checks exactly.
K = 384
S = 2 ** K

def ediv(a, b):
    # Lean Int `/` (Euclidean division); only used with b > 0, where it is floor division
    assert b > 0
    return a // b

def fl(a): return ediv(a, S)
def cl(a): return -ediv(-a, S)

class FI:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi): self.lo, self.hi = lo, hi
    def __repr__(self): return f"⟨{self.lo}, {self.hi}⟩"

def ofInt(k): return FI(k * S, k * S)
def add(a, b): return FI(a.lo + b.lo, a.hi + b.hi)
def neg(a): return FI(-a.hi, -a.lo)
def sub(a, b): return FI(a.lo - b.hi, a.hi - b.lo)
def mul(a, b):
    p1, p2, p3, p4 = a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi
    return FI(fl(min(min(p1, p2), min(p3, p4))), cl(max(max(p1, p2), max(p3, p4))))
def invPos(a):
    if 0 < a.lo:
        return FI(ediv(S * S, a.hi), -ediv(-(S * S), a.lo))
    return None
def inv(a):
    if 0 < a.lo: return invPos(a)
    if a.hi < 0:
        r = invPos(neg(a))
        return None if r is None else neg(r)
    return None
def div(a, b):
    r = inv(b)
    return None if r is None else mul(a, r)
def widen(a, r): return FI(a.lo - r, a.hi + r)

# ---- Base.lean ----
def taylorCS(Y):
    y2 = mul(Y, Y); y4 = mul(y2, y2); r = y4.hi
    one = ofInt(1); half = FI(S // 2, S // 2); sixth = FI(ediv(S, 6), -ediv(-S, 6))
    return (widen(sub(one, mul(half, y2)), r), widen(sub(Y, mul(sixth, mul(y2, Y))), r))
def dbl(cs):
    two = ofInt(2)
    return (sub(mul(two, mul(cs[0], cs[0])), ofInt(1)), mul(two, mul(cs[1], cs[0])))
def dblN(J, cs):
    for _ in range(J): cs = dbl(cs)
    return cs
def halfFI(N, J): return FI(ediv(N, 2 ** J), -ediv(-N, 2 ** J))
def pointCS(N, J): return dblN(J, taylorCS(halfFI(N, J)))
def rotStep(C, Sn, cs):
    return (sub(mul(cs[0], C), mul(cs[1], Sn)), add(mul(cs[1], C), mul(cs[0], Sn)))

# ---- Term.lean: the symbolic run ----
# terms as tuples: ('zero',), ('sQ', i), ('sub', a, b), ...
Z = ('zero',); ONE = ('one',); TWO = ('two',)
def initS(n):
    a = {}; b = {}
    A = lambda k: a.get(k, Z); B = lambda k: b.get(k, Z)
    a[n//2 - 1] = ('sinZ',)
    a[n//2 + 1] = ('neg', A(n//2 - 1))
    b[n//2 - 1] = ('cosZ',)
    b[n//2 + 1] = B(n//2 - 1)
    a[n - 1] = ('sub', A(n//2 - 1), ('sin2Z',))
    a[1] = ('neg', A(n - 1))
    b[n - 1] = ('sub', B(n//2 - 1), ('cos2Z',))
    b[1] = B(n - 1)
    a[n - 2] = ('sub', A(n//2 - 1), ('sin3Z',))
    a[2] = ('neg', A(n - 2))
    b[n - 2] = ('sub', B(n//2 - 1), ('cos3Z',))
    b[2] = B(n - 2)
    return a, b
def bodyS(n, a, b, i):
    A = lambda k: a.get(k, Z); B = lambda k: b.get(k, Z)
    j1 = (n//2 - 1 + i * (3*n//2 - 2)) % n
    j2 = (n - 1 + i * (3*n//2 - 2)) % n
    j3 = (n - 2 + i * (3*n//2 - 2)) % n
    j4 = (n + i * (3*n//2 - 2)) % n
    K2 = ('sub', ('mul', TWO, ('cosZ',)), ONE)
    a[j1] = ('sub', ('sinZ',), ('div', ('mul', ('mul', K2, ('sQ', i)), ('sQ1', i)), ('cos2Z',)))
    a[n - j1] = ('neg', A(j1))
    b[j1] = ('sub', ('cosZ',), ('div', ('mul', ('mul', K2, ('sQ', i)), ('cQ1', i)), ('cos2Z',)))
    b[n - j1] = B(j1)
    a[j2] = ('sub', A(j1), ('mul', ('pm', i), ('s42', i))); a[n - j2] = ('neg', A(j2))
    b[j2] = ('sub', B(j1), ('mul', ('pm', i), ('c42', i))); b[n - j2] = B(j2)
    a[j3] = ('sub', A(j1), ('mul', ('pm', i), ('s43', i))); a[n - j3] = ('neg', A(j3))
    b[j3] = ('sub', B(j1), ('mul', ('pm', i), ('c43', i))); b[n - j3] = B(j3)
    a[j4] = ('sub', A(j1), ('mul', ('pm', i), ('s41', i))); a[n - j4] = ('neg', A(j4))
    b[j4] = ('sub', B(j1), ('mul', ('pm', i), ('c41', i))); b[n - j4] = B(j4)
    return a, b
def abS(n):
    a, b = initS(n)
    for i in range(1, 1 + max(n // 8 - 1, 0)):
        a, b = bodyS(n, a, b, i)
    a[n//2] = Z; b[n//2] = ONE
    return a, b
def vertexS(n, k, ab=None):
    if k == 0: return (Z, Z)
    a, b = ab if ab is not None else abS(n)
    return (a.get(k, Z), b.get(k, Z))

# ---- Interp.lean ----
def encRS(r, cs):
    return [cs[1], neg(cs[0]), neg(cs[1]), cs[0]][min(r, 3)]
def encRC(r, cs):
    return [cs[0], cs[1], neg(cs[0]), neg(cs[1])][min(r, 3)]
def enc(tab, t):
    tag = t[0]
    look = lambda k: tab[k] if k < len(tab) else None
    def mp(k, f):
        e = look(k); return None if e is None else f(e)
    if tag == 'zero': return ofInt(0)
    if tag == 'one': return ofInt(1)
    if tag == 'two': return ofInt(2)
    if tag == 'sinZ': return mp(1, lambda e: e[1])
    if tag == 'cosZ': return mp(1, lambda e: e[0])
    if tag == 'sin2Z': return mp(2, lambda e: e[1])
    if tag == 'cos2Z': return mp(2, lambda e: e[0])
    if tag == 'sin3Z': return mp(3, lambda e: e[1])
    if tag == 'cos3Z': return mp(3, lambda e: e[0])
    if tag == 'sQ': i = t[1]; return mp(2 * i, lambda e: encRS(i % 4, e))
    if tag == 'sQ1': i = t[1]; return mp(2 * (i + 1), lambda e: encRS((i + 1) % 4, e))
    if tag == 'cQ1': i = t[1]; return mp(2 * (i + 1), lambda e: encRC((i + 1) % 4, e))
    if tag in ('s41', 's42', 's43'): i = t[1]; c = int(tag[2]); return mp(4 * i + c, lambda e: e[1])
    if tag in ('c41', 'c42', 'c43'): i = t[1]; c = int(tag[2]); return mp(4 * i + c, lambda e: e[0])
    if tag == 'pm': return ofInt(1) if t[1] % 2 == 0 else ofInt(-1)
    if tag == 'neg':
        x = enc(tab, t[1]); return None if x is None else neg(x)
    x = enc(tab, t[1]); y = enc(tab, t[2])
    if x is None or y is None: return None
    if tag == 'sub': return sub(x, y)
    if tag == 'mul': return mul(x, y)
    if tag == 'div': return div(x, y)
    raise ValueError(tag)

def crossFI(a, b, c):
    return sub(mul(sub(b[0], a[0]), sub(c[1], a[1])), mul(sub(b[1], a[1]), sub(c[0], a[0])))
def sqdFI(a, b):
    return add(mul(sub(b[0], a[0]), sub(b[0], a[0])), mul(sub(b[1], a[1]), sub(b[1], a[1])))

def gn_act(n, i, j):
    """Ayala Hoffmann's G_n, as the predicate the Lean `act` implements (i < j)."""
    h = n // 2
    for a, b in ((i, j), (j, i)):
        if a < h:
            if (b - a) % n == h and a != h // 2: return True
            if (b - a) % n == h - 1 and a % 4 in (2, 3): return True
            if (b - a) % n == h + 1 and a % 4 in (0, 3): return True
    return False

def lean_term(t):
    tag = t[0]
    if len(t) == 1: return f"Tm.{tag}"
    if tag in ('sQ','sQ1','cQ1','s41','s42','s43','c41','c42','c43','pm'): return f"(Tm.{tag} {t[1]})"
    if tag == 'neg': return f"(Tm.neg {lean_term(t[1])})"
    return f"(Tm.{tag} {lean_term(t[1])} {lean_term(t[2])})"

# ---- FSide.lean / FDeriv.lean ----
def look(tab, k): return tab[k] if k < len(tab) else None

def encF(m, tab):
    e1, e2, eb, ec, ea = look(tab, 1), look(tab, 2), look(tab, 2*m-2), look(tab, 2*m), look(tab, 4*m-1)
    if None in (e1, e2, eb, ec, ea): return None
    two = ofInt(2)
    Kk = sub(mul(two, e1[0]), ofInt(1))
    x = div(mul(mul(Kk, eb[0]), ec[1]), e2[0])
    if x is None: return None
    x = sub(e1[1], x)
    u = add(mul(two, x), ea[1])
    return sub(add(mul(u, u), mul(ea[0], ea[0])), sub(two, mul(two, e1[0])))

def encFd(m, tab):
    e1, e2, eb, ec, ea = look(tab, 1), look(tab, 2), look(tab, 2*m-2), look(tab, 2*m), look(tab, 4*m-1)
    if None in (e1, e2, eb, ec, ea): return None
    two = ofInt(2)
    bI, cI, aI = ofInt(2*m-2), ofInt(2*m), ofInt(4*m-1)
    Kk = sub(mul(two, e1[0]), ofInt(1))
    g = mul(eb[0], ec[1])
    g_ = add(neg(mul(mul(eb[1], bI), ec[1])), mul(eb[0], mul(ec[0], cI)))
    num = sub(mul(add(mul(neg(mul(two, e1[1])), g), mul(Kk, g_)), e2[0]), mul(mul(Kk, g), neg(mul(e2[1], two))))
    q = div(num, mul(e2[0], e2[0]))
    if q is None: return None
    xdI = sub(e1[0], q)
    x = div(mul(Kk, g), e2[0])
    if x is None: return None
    x = sub(e1[1], x)
    u = add(mul(two, x), ea[1])
    return sub(add(mul(mul(two, u), add(mul(two, xdI), mul(ea[0], aI))), mul(mul(two, ea[0]), neg(mul(ea[1], aI)))),
               mul(two, e1[1]))

def table(C, Sn, M):
    tab = [(ofInt(1), ofInt(0))]
    for _ in range(M):
        tab.append(rotStep(C, Sn, tab[-1]))
    return tab

def tab_at(N, J, r, M):
    """Table of (cos kz, sin kz), k = 0..M, valid for |z - N/2^K| <= r/2^K."""
    C, Sn = pointCS(N, J)
    return table(widen(C, r), widen(Sn, r), M)

# ---- Shapes.lean / Assemble.lean: the symbolic shapes ----
K2T = ('sub', ('mul', TWO, ('cosZ',)), ONE)
def tXa(i): return ('sub', ('sinZ',), ('div', ('mul', ('mul', K2T, ('sQ', i)), ('sQ1', i)), ('cos2Z',)))
def tXb(i): return ('sub', ('cosZ',), ('div', ('mul', ('mul', K2T, ('sQ', i)), ('cQ1', i)), ('cos2Z',)))
def tq(i): return (tXa(i), tXb(i))
def _off(i, s, c): return (('sub', tXa(i), ('mul', ('pm', i), (s, i))), ('sub', tXb(i), ('mul', ('pm', i), (c, i))))
def tr(i): return _off(i, 's42', 'c42')
def tu(i): return _off(i, 's43', 'c43')
def tt(i): return _off(i, 's41', 'c41')
tq0 = (('sinZ',), ('cosZ',))
tr0 = (('sub', ('sinZ',), ('sin2Z',)), ('sub', ('cosZ',), ('cos2Z',)))
tu0 = (('sub', ('sinZ',), ('sin3Z',)), ('sub', ('cosZ',), ('cos3Z',)))
tOrigin = (Z, Z)
tTop = (Z, ONE)
def tM(p): return (('neg', p[0]), p[1])

def shp_pts(tag, i=None):
    return {
        'fqr': lambda: (tr(i), tq(i)), 'fqu': lambda: (tu(i), tq(i)), 'fqt': lambda: (tt(i), tq(i)),
        'f0qr': lambda: (tr0, tq0), 'f0qu': lambda: (tu0, tq0), 'f0qt': lambda: (tOrigin, tq0),
        'otop': lambda: (tTop, tOrigin), 'cut': lambda: (tt(i + 1), tu(i)), 'c0ut': lambda: (tt(1), tu0),
        'sur': lambda: (tr(i), tu(i)), 'srt': lambda: (tt(i), tr(i)), 's0ur': lambda: (tr0, tu0),
        's0rt': lambda: (tOrigin, tr0), 's0top': lambda: (tTop, tq0), 'sqt': lambda: (tt(i + 1), tq(i)),
        'suq': lambda: (tq(i + 1), tu(i)), 's0qt': lambda: (tt(1), tq0), 's0uq': lambda: (tq(1), tu0),
        'clo': lambda: (tu(2 * i - 1), tM(tq(2 * i - 1))), "clo'": lambda: (tq(2 * i - 1), tM(tu(2 * i - 1))),
    }[tag]()
SHP_DIAM = ['fqr', 'fqu', 'fqt', 'f0qr', 'f0qu', 'f0qt', 'otop', 'cut', 'c0ut']
SHP_SIDE = ['sur', 'srt', 's0ur', 's0rt', 's0top', 'sqt', 'suq', 's0qt', 's0uq']
SHP_IDX = {'fqr', 'fqu', 'fqt', 'cut', 'sur', 'srt', 'sqt', 'suq', 'clo', "clo'"}

def nz(t): return Z if t == ('neg', Z) else t
def nzP(p): return (nz(p[0]), nz(p[1]))

def w_pts(tag, i, mir, flip):
    X, Y = shp_pts(tag, i)
    if mir: X, Y = tM(X), tM(Y)
    return (Y, X) if flip else (X, Y)

def find_witness(n, x, y, tags):
    """A witness (tag, i, mir, flip) with nzP x = nzP X, nzP y = nzP Y, or None."""
    nx, ny = nzP(x), nzP(y)
    for tag in tags:
        idx = [None] if tag not in SHP_IDX else (range(1, n // 16 + 1) if tag in ('clo', "clo'") else range(0, n // 8 + 1))
        for i in idx:
            for mir in (False, True):
                for flip in (False, True):
                    X, Y = w_pts(tag, i, mir, flip)
                    if nzP(X) == nx and nzP(Y) == ny:
                        return (tag, i, mir, flip)
    return None

def gn_edges(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if gn_act(n, i, j)]
