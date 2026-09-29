# Reusable exact Q(c,s) coordinate builders for the benchmark families.
#
# Each function returns (coords_cs, Fc, side_target, diam_target, zbox) for the
# general ExactIdentity engine (closing referee point R2 as a shared capability,
# not per-case ad-hoc code). Loaded once by the driver; candidates reference it.
#
# Requires modules ExactIdentity (as EI) and A16Certificate in scope; the
# Bingane–Audet section at the end also needs IntervalArithmetic at call time.

const EI = ExactIdentity
using .ExactIdentity: CS, cs_c, cs_s, cs_const, cs_cos, cs_sin, csadd, cssub, csmul, csneg, csdiv, RPoly

_R(v) = Vector{Rational{BigInt}}(v)

# ---- Audet / A16 (root-parametrized, clean x=s·X, y=Y structure) ----------
function a16_cs()
    two = cs_const(2); one = cs_const(1)
    kk = cssub(csmul(two, cs_cos(1)), one)                 # 2cos z - 1
    X = cssub(cs_sin(1), csmul(kk, cs_sin(4)))
    Y = cssub(cs_cos(1), csmul(kk, cs_cos(4)))
    nX = csneg(X); Z0 = cs_const(0)
    s = cs_sin; c = cs_cos
    coords = [
        (Z0, Z0),
        (cssub(s(2),s(1)), cssub(c(1),c(2))),
        (cssub(s(3),s(1)), cssub(c(1),c(3))),
        (nX, Y),
        (csadd(X,s(7)), csadd(Y,c(7))),
        (csadd(X,s(6)), csadd(Y,c(6))),
        (csadd(X,s(5)), csadd(Y,c(5))),
        (s(1), c(1)),
        (Z0, one),
        (csneg(s(1)), c(1)),
        (cssub(nX,s(5)), csadd(Y,c(5))),
        (cssub(nX,s(6)), csadd(Y,c(6))),
        (cssub(nX,s(7)), csadd(Y,c(7))),
        (X, Y),
        (cssub(s(1),s(3)), cssub(c(1),c(3))),
        (cssub(s(1),s(2)), cssub(c(1),c(2))),
    ]
    Fc = _R(A16Certificate.Fc_poly())                       # degree 12 (candidate data)
    z = A16Certificate.z_nominal
    return coords, Fc, _R([2,-2]), _R([1]), interval(z-big"1e-30", z+big"1e-30")
end

# ---- Vincze / H8 (root-parametrized, seam sides need the B≢0 criterion) ----
function vincze8_cs()
    s = cs_sin; c = cs_cos; half = cs_const(1//2); Z0 = cs_const(0); one = cs_const(1)
    b2 = csdiv(csadd(cssub(cs_const(2), c(1)), cs_s()), csmul(cs_const(2), csadd(c(1), cs_s())))
    coords = [
        (Z0, Z0),
        (cssub(s(2),s(1)), cssub(c(1),c(2))),
        (half, b2),
        (s(1), c(1)),
        (Z0, one),
        (csneg(s(1)), c(1)),
        (csneg(half), b2),
        (cssub(s(1),s(2)), cssub(c(1),c(2))),
    ]
    # Fc is DERIVED from the constructor (Proposition 1, self-contained — no
    # dependency on the paper's sextic). The OPTIGON Vincze F(t)=0, reduced in
    # Q(c,s), is G(c)+s·H(c)=0 with G,H below; the defining polynomial is the
    # field norm Fc = G² − (1−c²)H². (It equals the Bingane–Audet §2 sextic
    # identically — a cross-check, verified in docs/audits/theory-audit.md, not an input.)
    pm(a,b) = (r=zeros(Rational{BigInt},length(a)+length(b)-1); for i in eachindex(a),j in eachindex(b); r[i+j-1]+=a[i]*b[j]; end; r)
    ps(a,b) = [(i<=length(a) ? a[i] : 0//1)-(i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b))]
    G = _R([1,-4,-4,8]); H = _R([0,-8,8])            # 8c³-4c²-4c+1 ; 8c²-8c
    Fc = _R(ps(pm(G,G), pm(_R([1,0,-1]), pm(H,H))))   # G² − (1−c²)H²
    z = big"0.3894068706089136310254731821232088177802669267863906566356996889936525347787489"
    return coords, Fc, _R([2,-2]), _R([1]), interval(z-big"1e-30", z+big"1e-30")
end

# ---- Regular n-gon (fixed-angle; even n has RATIONAL coordinates) ----------
function regular_cs(n::Int)
    # for n=4 the square (diamond) has exact rational vertices; identities are
    # exact rational (unconditional). We build them as CS constants.
    @assert n == 4
    h = cs_const(1//2); o = cs_const(1); Z0 = cs_const(0)
    coords = [(Z0,Z0),(h,h),(Z0,o),(csneg(h),h)]
    # side^2 = 1/2, diameter^2 = 1 (rational constants). Fc, zbox unused (all A≡0).
    return coords, _R([0,1]), _R([1//2]), _R([1]), interval(big"0.0")
end

# ---- Reinhardt R_{3,6} (fixed-angle θ=π/6, Fc = min poly of cos(π/6)) ------
function reinhardt36_cs()
    # angles are integer multiples of π/6; use cs_cos/cs_sin with base θ=π/6.
    c = cs_cos; s = cs_sin; two = cs_const(2)
    den = csmul(two, c(1))                                   # 2 cos(π/6)
    a2 = csdiv(s(4), den);            b2 = csdiv(cssub(cs_const(1), c(4)), den)
    a4 = csdiv(s(8), den);            b4 = csdiv(cssub(cs_const(1), c(8)), den)
    a3 = c(3);                        b3 = s(3)               # (0, 1)
    a5 = csadd(a2, c(7));             b5 = csadd(b2, s(7))
    a1 = csneg(a5);                   b1 = b5
    Z0 = cs_const(0)
    coords = [(Z0,Z0),(a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5)]
    Fc = _R([-3,0,4])                                        # 4c^2-3, min poly of cos(π/6)
    # Sign-check box: a CERTIFIED interval enclosure of the known angle θ = π/6
    # (via interval π), so θ ∈ box holds rigorously — not a box around a
    # floating approximation of π/6.
    zbox = interval(BigFloat, π) / 6
    return coords, Fc, _R([2,-2]), _R([1]), zbox
end

# ---- Bingane–Audet family, general n = 2^s ≥ 16 ------------------------------
#
# The members this package certifies, in one place: every script, test and
# report that iterates over the family reads these tuples.
#   FAMILY_N       the Julia family certificate (pipeline/certify_family.jl)
#   FAMILY_LEAN_N  the members with the per-case Lean certificate
#                  (lean/ChiquipoliFamily/A<n>/, polynomial, gen_family.jl)
#   FAMILY_TRIG_N  the members with the general Lean certificate: one theorem
#                  for every n = 16k (lean/ChiquipoliFamily/Trig/Assemble.lean)
#                  and kernel-checked data per n (ChiquipoliFamily/T<n>/,
#                  gen_trig.py). 16, 32, 64 are thus covered twice in Lean.
const FAMILY_N = (16, 32, 64, 128, 256, 512, 1024)
const FAMILY_LEAN_N = (16, 32, 64)
const FAMILY_TRIG_N = (16, 32, 64, 128, 256)

"""
    gn_edges(n) -> Vector{Tuple{Int,Int}}

The graph `G_n` of J. Ayala Hoffmann, *Moving-Frame Criteria and Powers-of-Two
Graph Recurrences for Equilateral Small Polygons* (Section 4), in closed form:

    E_0 = {{i, i+h}   : 0 ≤ i < h, i ≠ h/2}
    E_- = {{i, i+h-1} : 0 ≤ i < h, i ≡ 2, 3 (mod 4)}
    E_+ = {{i, i+h+1} : 0 ≤ i < h, i ≡ 0, 3 (mod 4)}        h = n/2, indices mod n,

returned as sorted pairs `(i, j)`, `i < j`. That paper proves `|E(G_n)| = n - 1`
and that the published constructor realises every edge as a unit chord for
every value of its parameter. Here it is used in two ways only: the candidate
files write their active graph out as data, and `test/literature.jl` checks
that data against this formula for every member. The certificate never trusts
either; it proves every listed pair has distance 1 and every other pair < 1.
"""
function gn_edges(n::Int)
    (ispow2(n) && n >= 16) || throw(DomainError(n, "n must be a power of 2 >= 16"))
    h = n ÷ 2
    E = Set{Tuple{Int,Int}}()
    for i in 0:h-1
        i != h ÷ 2 && push!(E, minmax(i, mod(i + h, n)))
        mod(i, 4) in (2, 3) && push!(E, minmax(i, mod(i + h - 1, n)))
        mod(i, 4) in (0, 3) && push!(E, minmax(i, mod(i + h + 1, n)))
    end
    return sort!(collect(E))
end
# The OPTIGON constructor `cstrt_audet_ngon(n)` written ONCE over an abstract
# angle algebra, so the same formulas give both the interval coordinates the
# certifier evaluates and the exact Q(c,s) coordinates the identity engine
# proves. `S(k)`, `C(k)` are sin/cos of k·z, `K(q)` a rational constant, and
# `ops = (add, sub, mul, dvd, neg)` the algebra's operations. Upstream writes
# sin(i(2z-π/2)) and cos(i(2z-π/2)); they are rewritten here exactly by i mod 4,
# so π enters neither version. Cross-checked against the verbatim upstream
# transcription (test/fixtures/optigon_reference.jl) in test/literature.jl.
# Vertices p_0..p_{n-1}, p_0 at the origin, as upstream.
function audet_generic(n, S, C, K, ops)
    add, sub, mul, dvd, neg = ops
    (ispow2(n) && n >= 16) || throw(DomainError(n, "n must be a power of 2 >= 16"))
    sinw(i) = (r = mod(i, 4); r == 0 ? S(2i) : r == 1 ? neg(C(2i)) : r == 2 ? neg(S(2i)) : C(2i))
    cosw(i) = (r = mod(i, 4); r == 0 ? C(2i) : r == 1 ? S(2i) : r == 2 ? neg(C(2i)) : neg(S(2i)))
    a = Vector{Any}(undef, n - 1); b = Vector{Any}(undef, n - 1)
    h = n ÷ 2
    a[h-1] = S(1);               a[h+1] = neg(a[h-1])
    b[h-1] = C(1);               b[h+1] = b[h-1]
    a[n-1] = sub(a[h-1], S(2));  a[1] = neg(a[n-1])
    b[n-1] = sub(b[h-1], C(2));  b[1] = b[n-1]
    a[n-2] = sub(a[h-1], S(3));  a[2] = neg(a[n-2])
    b[n-2] = sub(b[h-1], C(3));  b[2] = b[n-2]
    kk = sub(mul(K(2), C(1)), K(1))                       # 2cos z - 1
    step = 3n ÷ 2 - 2
    for i in 1:(n ÷ 8 - 1)
        j1 = mod(h - 1 + i*step, n); j2 = mod(n - 1 + i*step, n)
        j3 = mod(n - 2 + i*step, n); j4 = mod(n + i*step, n)
        sg(v) = isodd(i) ? neg(v) : v                     # (-1)^i · v
        a[j1] = sub(S(1), dvd(mul(kk, mul(sinw(i), sinw(i+1))), C(2)));  a[n-j1] = neg(a[j1])
        b[j1] = sub(C(1), dvd(mul(kk, mul(sinw(i), cosw(i+1))), C(2)));  b[n-j1] = b[j1]
        a[j2] = sub(a[j1], sg(S(4i+2)));  a[n-j2] = neg(a[j2])
        b[j2] = sub(b[j1], sg(C(4i+2)));  b[n-j2] = b[j2]
        a[j3] = sub(a[j1], sg(S(4i+3)));  a[n-j3] = neg(a[j3])
        b[j3] = sub(b[j1], sg(C(4i+3)));  b[n-j3] = b[j3]
        a[j4] = sub(a[j1], sg(S(4i+1)));  a[n-j4] = neg(a[j4])
        b[j4] = sub(b[j1], sg(C(4i+1)));  b[n-j4] = b[j4]
    end
    a[h] = K(0); b[h] = K(1)
    return vcat([(K(0), K(0))], [(a[i], b[i]) for i in 1:n-1])
end

# The constructor's defining equation F(z) = 0, same algebra:
#   x = sin z - (2cos z - 1) cos((n/4-2)z) sin(nz/4) / cos 2z,
#   F = (2x + sin((n/2-1)z))² + cos((n/2-1)z)² - 4 sin²(z/2),  4 sin²(z/2) = 2 - 2cos z.
function audet_F_generic(n, S, C, K, ops)
    add, sub, mul, dvd, neg = ops
    x = sub(S(1), dvd(mul(sub(mul(K(2), C(1)), K(1)), mul(C(n ÷ 4 - 2), S(n ÷ 4))), C(2)))
    u = add(mul(K(2), x), S(n ÷ 2 - 1)); v = C(n ÷ 2 - 1)
    return sub(add(mul(u, u), mul(v, v)), sub(K(2), mul(K(2), C(1))))
end

# Interval instance. Integer literals enter as guaranteed thin intervals so
# IntervalArithmetic keeps its `isguaranteed` flag (see n8_ahmp2004).
const _AUDET_NUM_OPS = (+, -, *, /, -)
_II(k) = interval(BigFloat, k)
function audet_coords(n)
    return function (z)
        P = audet_generic(n, k -> sin(_II(k)*z), k -> cos(_II(k)*z), q -> _II(q) + zero(z), _AUDET_NUM_OPS)
        p = Matrix{typeof(z)}(undef, n, 2)
        for i in 1:n; p[i, 1] = P[i][1]; p[i, 2] = P[i][2]; end
        return p
    end
end
audet_F(n) = z -> audet_F_generic(n, k -> sin(_II(k)*z), k -> cos(_II(k)*z), q -> _II(q) + zero(z), _AUDET_NUM_OPS)

# Exact Q(c,s) instance.
const _AUDET_CS_OPS = (csadd, cssub, csmul, csdiv, csneg)
audet_coords_cs(n) = audet_generic(n, cs_sin, cs_cos, cs_const, _AUDET_CS_OPS)

"""
    audet_Fc(n) -> (Fc, den)

`Fc` by Proposition 1, from the constructor alone: F = (A + s·B)/den in Q(c,s).
For this family B ≡ 0 (checked), so F(z*) = 0 with den(c*) ≠ 0 gives A(c*) = 0.
The factor g = gcd(A, den) divides den, hence g(c*) ≠ 0 wherever den(c*) ≠ 0,
and Fc = A/g (made monic) still has c* as a root. `den` is returned so that
den(c*) ≠ 0 can be certified by the caller; for n = 16 this `Fc` equals
`A16Certificate.Fc_poly` up to a constant (tested).
"""
function audet_Fc(n)
    F = audet_F_generic(n, cs_sin, cs_cos, cs_const, _AUDET_CS_OPS)
    EI.iszeropoly(F.B) || error("audet_Fc($n): F has an s-part; Proposition 1 needs the norm here")
    g = EI.pgcd(F.A, F.den)
    Fc = length(g) > 1 ? first(EI.pdivrem(F.A, g)) : F.A
    return _R(Fc ./ Fc[end]), F.den
end

function audet_cs(n, z)
    Fc, _ = audet_Fc(n)
    return audet_coords_cs(n), Fc, _R([2,-2]), _R([1]), interval(z-big"1e-30", z+big"1e-30")
end
