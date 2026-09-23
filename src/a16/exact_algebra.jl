# Exact algebra in Q[c]: the Chebyshev reduction, the exact vertex polynomials,
# Fc, and the zero-remainder divisions that prove Lemma 6.1.
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

# ---------------------------------------------------------------------------
# Exact rational-polynomial reduction (sides + active diameters).
#
# Every multiple-angle term in `coordinates` is a Chebyshev polynomial in
# c := cos(z), with sin(k z) = sin(z) * U_{k-1}(c) and cos(k z) = T_k(c).
# Consequently every vertex has the exact form (sin(z)*Xc(c), Yc(c)), and every
# squared distance is
#     d(z)^2 = sin(z)^2*(ΔXc)^2 + (ΔYc)^2 = (1-c^2)*(ΔXc)^2 + (ΔYc)^2,
# a polynomial in c alone with rational coefficients (no interval, no
# floating point). F(z) reduces the same way to a rational polynomial Fc(c).
#
# If target(c) - d(z)^2's polynomial form is exactly divisible by Fc(c) in
# Q[c] (zero remainder under exact rational long division), then the
# equality holds identically whenever F(z) = 0 -- i.e. exactly at the
# constructor's root, not merely "numerically close". This is the reduction
# to F(z)=0 required by the Golden Rule: an interval containing zero never
# appears in this argument.
# ---------------------------------------------------------------------------

const RPoly = Vector{Rational{BigInt}}

function ptrim(a::RPoly)
    n = length(a)
    while n > 1 && a[n] == 0
        n -= 1
    end
    return a[1:n]
end

padd(a::RPoly,b::RPoly) = ptrim([ (i<=length(a) ? a[i] : 0//1) + (i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b)) ])
psub(a::RPoly,b::RPoly) = ptrim([ (i<=length(a) ? a[i] : 0//1) - (i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b)) ])
iszeropoly(a::RPoly) = all(==(0//1), a)

function pmul(a::RPoly,b::RPoly)
    if iszeropoly(a) || iszeropoly(b)
        return RPoly([0//1])
    end
    r = zeros(Rational{BigInt}, length(a)+length(b)-1)
    for i in eachindex(a), j in eachindex(b)
        r[i+j-1] += a[i]*b[j]
    end
    return ptrim(r)
end

pscale(a::RPoly,k) = ptrim([x*k for x in a])
psq(a::RPoly) = pmul(a,a)

"""
    pdivrem(a, b) -> (quotient, remainder)

Exact rational long division of polynomials in Q[c]. No floating point is
involved: coefficients are `Rational{BigInt}` throughout, so a returned
zero remainder is a proof, not an approximation.
"""
function pdivrem(a::RPoly,b::RPoly)
    a = ptrim(copy(a))
    bdeg = length(b)-1
    q = zeros(Rational{BigInt}, max(length(a)-length(b)+1,1))
    while length(a) - 1 >= bdeg && !iszeropoly(a)
        adeg = length(a)-1
        coeff = a[end] / b[end]
        shift = adeg - bdeg
        q[shift+1] = coeff
        sub = pmul(b, vcat(zeros(Rational{BigInt},shift), [coeff]))
        a = ptrim(psub(a, sub))
    end
    return ptrim(q), a
end

"""
    chebyshev(kmax) -> (T, U)

`T[k]` and `U[k]` are the degree-`k` Chebyshev polynomials of the first and
second kind, satisfying `cos(k*z) = T[k](cos z)` and
`sin((k+1)*z) = sin(z) * U[k](cos z)`, for `k = 0:kmax`.
"""
function chebyshev(kmax)
    T = Dict(0=>RPoly([1//1]), 1=>RPoly([0//1,1//1]))
    U = Dict(0=>RPoly([1//1]), 1=>RPoly([0//1,2//1]))
    c1 = RPoly([0//1,2//1])
    for k in 2:kmax
        T[k] = psub(pmul(c1,T[k-1]), T[k-2])
        U[k] = psub(pmul(c1,U[k-1]), U[k-2])
    end
    return T,U
end

# Cached rational-polynomial coordinate table: vertex k = (sin(z)*XC[k](c), YC[k](c)).
function _exact_coordinate_polys()
    T,U = chebyshev(8)
    sinpoly(m) = U[m-1]
    cospoly(m) = T[m]
    twoc_minus1 = RPoly([-1//1,2//1])
    P = psub(sinpoly(1), pmul(twoc_minus1, sinpoly(4)))
    Q = psub(cospoly(1), pmul(twoc_minus1, cospoly(4)))

    zeroP = RPoly([0//1])
    XC = Vector{RPoly}(undef,16)
    YC = Vector{RPoly}(undef,16)
    XC[0+1]=zeroP;                          YC[0+1]=zeroP
    XC[1+1]=psub(sinpoly(2),sinpoly(1));    YC[1+1]=psub(cospoly(1),cospoly(2))
    XC[2+1]=psub(sinpoly(3),sinpoly(1));    YC[2+1]=psub(cospoly(1),cospoly(3))
    XC[3+1]=pscale(P,-1);                   YC[3+1]=Q
    XC[4+1]=padd(P,sinpoly(7));             YC[4+1]=padd(Q,cospoly(7))
    XC[5+1]=padd(P,sinpoly(6));             YC[5+1]=padd(Q,cospoly(6))
    XC[6+1]=padd(P,sinpoly(5));             YC[6+1]=padd(Q,cospoly(5))
    XC[7+1]=sinpoly(1);                     YC[7+1]=cospoly(1)
    XC[8+1]=zeroP;                          YC[8+1]=RPoly([1//1])
    XC[9+1]=pscale(sinpoly(1),-1);          YC[9+1]=cospoly(1)
    XC[10+1]=psub(pscale(P,-1),sinpoly(5)); YC[10+1]=padd(Q,cospoly(5))
    XC[11+1]=psub(pscale(P,-1),sinpoly(6)); YC[11+1]=padd(Q,cospoly(6))
    XC[12+1]=psub(pscale(P,-1),sinpoly(7)); YC[12+1]=padd(Q,cospoly(7))
    XC[13+1]=P;                             YC[13+1]=Q
    XC[14+1]=psub(sinpoly(1),sinpoly(3));   YC[14+1]=psub(cospoly(1),cospoly(3))
    XC[15+1]=psub(sinpoly(1),sinpoly(2));   YC[15+1]=psub(cospoly(1),cospoly(2))
    return XC,YC,P,sinpoly(7),cospoly(7)
end

const _XC, _YC, _Ppoly, _sin7poly, _cos7poly = _exact_coordinate_polys()
const _ONE_MINUS_C2 = RPoly([1//1,0//1,-1//1])

"""
    sqdist_poly(i, j) -> RPoly

Exact rational polynomial in c = cos(z) equal to the squared Euclidean
distance between vertices i and j (0-indexed), valid for every real z.
"""
function sqdist_poly(i,j)
    dX = psub(_XC[j+1],_XC[i+1])
    dY = psub(_YC[j+1],_YC[i+1])
    return padd(pmul(_ONE_MINUS_C2, psq(dX)), psq(dY))
end

"Exact target polynomial for a side: ell(z)^2 = 4 sin^2(z/2) = 2 - 2c."
side_target_poly() = RPoly([2//1,-2//1])

"Exact target polynomial for an active diameter: constant 1."
diameter_target_poly() = RPoly([1//1])

"""
    Fc_poly() -> RPoly

Exact rational polynomial in c = cos(z) equal to F(z) (the defining equation
of the constructor's root), obtained by the same Chebyshev substitution.
F(z) = 0 for real z if and only if Fc(cos z) = 0.
"""
function Fc_poly()
    inner = padd(pscale(_Ppoly,2), _sin7poly)
    return psub(padd(pmul(_ONE_MINUS_C2, psq(inner)), psq(_cos7poly)), side_target_poly())
end
const _Fc = Fc_poly()

"""
    exact_identity_certificate(i, j, target)

Exact-arithmetic proof that `sqdist(i,j) == target` whenever `F(z)=0`.
Returns a named tuple with `proved::Bool`, the quotient/remainder of the
exact polynomial division, and a reconstruction check `q*Fc + r == R` that
guards against a silently broken division routine.
"""
function exact_identity_certificate(i, j, target::RPoly)
    R = psub(sqdist_poly(i,j), target)
    q, r = pdivrem(R, _Fc)
    reconstruction_ok = ptrim(padd(pmul(q,_Fc), r)) == ptrim(R)
    proved = iszeropoly(r) && reconstruction_ok
    return (proved=proved, quotient=q, remainder=r,
            reconstruction_ok=reconstruction_ok, Fc_degree=length(_Fc)-1)
end
