# Reusable exact Q(c,s) coordinate builders for the benchmark families.
#
# Each function returns (coords_cs, Fc, side_target, diam_target, zbox) for the
# general ExactIdentity engine (closing referee point R2 as a shared capability,
# not per-case ad-hoc code). Loaded once by the driver; candidates reference it.
#
# Requires modules ExactIdentity (as EI) and A16Certificate in scope.

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
    # identically — a cross-check, verified in docs/theory-audit.md, not an input.)
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
