"""
Independent, from-scratch symbolic verification of the 31 claimed exact
equalities for the A16 (Bingane-Audet) 16-gon construction.

Method:
  - Work with c = cos(z) as the single free symbol (exact polynomial algebra
    over QQ), using the identities:
        sin(k*z) = sin(z) * U_{k-1}(c)      (Chebyshev 2nd kind)
        cos(k*z) = T_k(c)                   (Chebyshev 1st kind)
    so every vertex coordinate is either of the form  s*a(c)  (a polynomial
    "a" in c, times sin(z))  or purely  b(c)  (a polynomial in c).
  - Because every x-coordinate here is of the form s*a(c) and every
    y-coordinate is of the form b(c) (checked programmatically below, not
    assumed), any squared-distance
        |p_j - p_i|^2 = s^2*(a_j-a_i)^2 + (b_j-b_i)^2
                       = (1-c^2)*(a_j-a_i)^2 + (b_j-b_i)^2
    is a PURE polynomial in c (no leftover s). Subtracting the (also
    poly-in-c) target^2 gives D_ij(c), a polynomial in c alone.
  - F(t) reduces the same way to a pure polynomial Fpoly(c) in c.
  - Classify each D_ij(c):
        D_ij(c) == 0 identically            -> type (A) unconditional identity
        D_ij(c) != 0 but Fpoly(c) | D_ij(c) -> type (B) conditional on F(z)=0
        otherwise                            -> AMBIGUOUS / unexpected
"""
from sympy import symbols, chebyshevt, chebyshevu, expand, simplify, div, Poly, factor, sqrt, Rational

c = symbols('c')

def S(k):
    """sin(k*z) expressed as s * (poly in c); returns the poly-in-c part only
    (the caller tracks the overall factor of s separately)."""
    if k == 0:
        return 0
    return expand(chebyshevu(k-1, c))

def C(k):
    """cos(k*z) = T_k(c), a pure poly in c."""
    return expand(chebyshevt(k, c))

# x(z) = sin(z) - (2 cos(z)-1) sin(4z) = s*[ S(1) - (2c-1)*S(4) ]
# y(z) = cos(z) - (2 cos(z)-1) cos(4z) =    C(1) - (2c-1)*C(4)
x_a = expand(S(1) - (2*c - 1) * S(4))   # x = s * x_a(c)
y_b = expand(C(1) - (2*c - 1) * C(4))   # y = y_b(c)

# Each vertex represented as (a(c), b(c)) meaning actual coords = (s*a(c), b(c))
verts = {}
verts[0]  = (0, 0)
verts[1]  = (expand(S(2) - S(1)), expand(C(1) - C(2)))
verts[2]  = (expand(S(3) - S(1)), expand(C(1) - C(3)))
verts[3]  = (expand(-x_a), y_b)
verts[4]  = (expand(x_a + S(7)), expand(y_b + C(7)))
verts[5]  = (expand(x_a + S(6)), expand(y_b + C(6)))
verts[6]  = (expand(x_a + S(5)), expand(y_b + C(5)))
verts[7]  = (S(1), C(1))
verts[8]  = (0, 1)
verts[9]  = (expand(-S(1)), C(1))
verts[10] = (expand(-x_a - S(5)), expand(y_b + C(5)))
verts[11] = (expand(-x_a - S(6)), expand(y_b + C(6)))
verts[12] = (expand(-x_a - S(7)), expand(y_b + C(7)))
verts[13] = (x_a, y_b)
verts[14] = (expand(S(1) - S(3)), expand(C(1) - C(3)))
verts[15] = (expand(S(1) - S(2)), expand(C(1) - C(2)))

# Sanity: confirm the "x-coord = s*poly(c), y-coord = poly(c)" structural
# assumption isn't silently wrong by re-deriving each vertex directly with
# sin/cos of z as independent transcendentals and comparing numerically.
import mpmath as mp
mp.mp.dps = 60

def F_of_t(t):
    xt = mp.sin(t) - (2*mp.cos(t)-1)*mp.sin(4*t)
    yt = mp.cos(t) - (2*mp.cos(t)-1)*mp.cos(4*t)
    return (2*xt + mp.sin(7*t))**2 + mp.cos(7*t)**2 - 4*mp.sin(t/2)**2

# find root z in (2*asin(sin(pi/16)/2), pi/16) via mpmath findroot, independently
lo = 2*mp.asin(mp.sin(mp.pi/16)/2)
hi = mp.pi/16
z0 = mp.findroot(F_of_t, (lo+hi)/2)
print("Root z0 =", z0)
print("Given reference z ~ 0.19627037213032280086206121185805318446")
print("diff:", z0 - mp.mpf('0.19627037213032280086206121185805318446'))

s0 = mp.sin(z0); c0 = mp.cos(z0)

def numeric_vertex(i):
    a_poly, b_poly = verts[i]
    if a_poly == 0 and b_poly == 0:
        ax = mp.mpf(0)
    else:
        # evaluate polynomial a_poly(c) at c0
        ax = s0 * poly_eval(a_poly, c0) if a_poly != 0 else mp.mpf(0)
    by = b_poly if not hasattr(b_poly, 'free_symbols') else poly_eval(b_poly, c0)
    if not hasattr(b_poly, 'free_symbols'):
        by = mp.mpf(b_poly)
    return ax, by

def poly_eval(expr, cval):
    p = Poly(expr, c)
    coeffs = p.all_coeffs()  # highest degree first
    val = mp.mpf(0)
    for co in coeffs:
        val = val*cval + mp.mpf(str(co))
    return val

# direct numeric vertices from the ORIGINAL formulas (independent re-derivation)
def direct_vertices(z):
    xz = mp.sin(z) - (2*mp.cos(z)-1)*mp.sin(4*z)
    yz = mp.cos(z) - (2*mp.cos(z)-1)*mp.cos(4*z)
    P = {}
    P[0]  = (mp.mpf(0), mp.mpf(0))
    P[1]  = (mp.sin(2*z)-mp.sin(z), mp.cos(z)-mp.cos(2*z))
    P[2]  = (mp.sin(3*z)-mp.sin(z), mp.cos(z)-mp.cos(3*z))
    P[3]  = (-xz, yz)
    P[4]  = (xz+mp.sin(7*z), yz+mp.cos(7*z))
    P[5]  = (xz+mp.sin(6*z), yz+mp.cos(6*z))
    P[6]  = (xz+mp.sin(5*z), yz+mp.cos(5*z))
    P[7]  = (mp.sin(z), mp.cos(z))
    P[8]  = (mp.mpf(0), mp.mpf(1))
    P[9]  = (-mp.sin(z), mp.cos(z))
    P[10] = (-xz-mp.sin(5*z), yz+mp.cos(5*z))
    P[11] = (-xz-mp.sin(6*z), yz+mp.cos(6*z))
    P[12] = (-xz-mp.sin(7*z), yz+mp.cos(7*z))
    P[13] = (xz, yz)
    P[14] = (mp.sin(z)-mp.sin(3*z), mp.cos(z)-mp.cos(3*z))
    P[15] = (mp.sin(z)-mp.sin(2*z), mp.cos(z)-mp.cos(2*z))
    return P

Pdirect = direct_vertices(z0)
max_err = 0
for i in range(16):
    ax, by = numeric_vertex(i)
    dx = ax - Pdirect[i][0]
    dy = by - Pdirect[i][1]
    max_err = max(max_err, abs(dx), abs(dy))
print("max structural-form check error (should be ~0):", max_err)

# --- Build Fpoly(c) ---
# F(t) = (2x+sin7t)^2 + cos7t^2 - 4 sin^2(t/2), with 4 sin^2(t/2) = 2 - 2c
inner = expand(2*x_a + S(7))  # s * inner(c) = 2x + sin(7z)
Fpoly = expand((1 - c**2) * inner**2 + C(7)**2 - (2 - 2*c))
Fpoly = Poly(Fpoly, c)
print("\nFpoly(c) degree:", Fpoly.degree())
print("Fpoly(c) =", Fpoly.as_expr())

# numeric check of Fpoly at c0
Fval = poly_eval(Fpoly.as_expr(), c0)
print("Fpoly(c0) numeric (should be ~0):", Fval)

ell2 = expand(2 - 2*c)   # ell^2 = 4 sin^2(z/2) = 2-2c

def dist2_minus_target(i, j, target2):
    ai, bi = verts[i]
    aj, bj = verts[j]
    da = expand(aj - ai)
    db = expand(bj - bi)
    D = expand((1 - c**2)*da**2 + db**2 - target2)
    return expand(D)

sides = [(i, (i+1) % 16) for i in range(16)]
diam_pairs = [(0,7),(0,8),(0,9),(1,9),(2,9),(2,10),(3,10),(3,11),(3,12),
              (4,13),(5,13),(6,13),(6,14),(7,14),(7,15)]

results = []

print("\n--- SIDE equalities |p_{i+1}-p_i| = ell ---")
for (i, j) in sides:
    D = dist2_minus_target(i, j, ell2)
    Dp = Poly(D, c) if D != 0 else None
    if D == 0:
        cls = "A (identically zero)"
        rem_ok = None
    else:
        q, r = div(Dp.as_expr(), Fpoly.as_expr(), c)
        rem_ok = (expand(r) == 0)
        cls = "B (divisible by Fpoly, conditional)" if rem_ok else "AMBIGUOUS (nonzero, NOT divisible by Fpoly)"
    # numeric residual
    Dval = poly_eval(D, c0) if D != 0 else mp.mpf(0)
    results.append((f"side ({i},{j})", cls, Dval, D))
    print(f"side |p{ (i+1)%16 if False else j }-p{i}| : {cls}   numeric D(c0)={Dval}")

print("\n--- DIAMETER equalities |p_i-p_j| = 1 ---")
for (i, j) in diam_pairs:
    D = dist2_minus_target(i, j, 1)
    if D == 0:
        cls = "A (identically zero)"
    else:
        q, r = div(D, Fpoly.as_expr(), c)
        rem_ok = (expand(r) == 0)
        cls = "B (divisible by Fpoly, conditional)" if rem_ok else "AMBIGUOUS (nonzero, NOT divisible by Fpoly)"
    Dval = poly_eval(D, c0) if D != 0 else mp.mpf(0)
    results.append((f"diam ({i},{j})", cls, Dval, D))
    print(f"diam |p{i}-p{j}| : {cls}   numeric D(c0)={Dval}")

print("\n=== SUMMARY ===")
typeA = [r[0] for r in results if r[1].startswith("A")]
typeB = [r[0] for r in results if r[1].startswith("B")]
amb   = [r[0] for r in results if r[1].startswith("AMBIG")]
print("Type A (unconditional identities):", len(typeA))
for n in typeA: print("   ", n)
print("Type B (conditional on F(z)=0):", len(typeB))
for n in typeB: print("   ", n)
print("Ambiguous:", len(amb))
for n in amb: print("   ", n)

max_numeric_resid = max(abs(r[2]) for r in results)
print("\nmax |numeric residual| at root z0 across all 31:", max_numeric_resid)

print("\n--- Detail check on the two Type-B sides ---")
for (i,j) in [(3,4),(12,13)]:
    D = dist2_minus_target(i, j, ell2)
    q, r = div(D, Fpoly.as_expr(), c)
    print(f"pair ({i},{j}): D degree =", Poly(D,c).degree(), " remainder ==0 ?", expand(r)==0)
    print("   quotient q(c) =", expand(q))
    print("   D(c) =", D)
