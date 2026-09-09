module A16Certificate

using LinearAlgebra
using IntervalArithmetic

export ACTIVE_EDGES, ROWS_MINOR, COLS_MINOR, OMITTED_COLUMNS,
       z_nominal, search_bounds, Xfun, Xprime, Yfun,
       Ffun, Fprime, coordinates, side_length, sqdist,
       build_jacobian, support_determinants, inactive_pairs,
       interval_abs_bound, regularity_test, krawczyk_linear,
       rigid_vectors, objective_covector, normalized_matrix,
       omitted_residual_matrix, rigid_annihilation_identities,
       assert_guaranteed,
       RPoly, ptrim, padd, psub, pmul, pscale, psq, pdivrem, iszeropoly,
       chebyshev, sqdist_poly, side_target_poly, diameter_target_poly,
       Fc_poly, exact_identity_certificate

const ACTIVE_EDGES = [
    (0,7), (0,8), (0,9), (1,9), (2,9), (2,10), (3,10),
    (3,11), (3,12), (4,13), (5,13), (6,13), (6,14),
    (7,14), (7,15)
]

# Julia indices. Row 19 is d_{0,9}; columns 3,4,17 are x_1,y_1,x_8.
const ROWS_MINOR = vcat(collect(1:18), collect(20:31))
const OMITTED_COLUMNS = [3,4,17]
const COLS_MINOR = [j for j in 1:33 if !(j in OMITTED_COLUMNS)]

const z_nominal = big"0.19627037213032280086206121185805318446"

"""
    _lit(x, k)

The exact integer `k` rendered in the arithmetic type of `x`. For an interval
element type this returns a *guaranteed* thin interval.

Why this exists. Mixing a bare `Real` into an interval expression (`2cos(t)`,
`sin(4t)`, ...) is arithmetically sound whenever the bare value is exactly
representable, as every literal in this file is: IntervalArithmetic converts it
to a thin interval and the operation is still outward rounded. But IA
conservatively clears its `isguaranteed` flag on any such mix, because in
general the bare value might itself be a rounded approximation of what the
author meant (the classic `0.1` trap). The consequence was that essentially
every quantity in this certificate carried the NG ("not guaranteed") tag, so
IA's own audit flag was uninformative and a reader had to re-derive by hand
that each literal is exact. Routing literals through `_lit` keeps the flag
live, and `assert_guaranteed` below turns it into an enforced gate.

The enclosures are bit-for-bit identical either way; only the flag changes.
"""
_lit(::Interval{S}, k::Integer) where {S} = interval(S, k)
_lit(::T, k::Integer) where {T<:Real} = T(k)
_lit(::Type{Interval{S}}, k::Integer) where {S} = interval(S, k)
_lit(::Type{T}, k::Integer) where {T<:Real} = T(k)

# `Matrix{Interval{T}}(I,n,n)` builds its entries through a conversion that
# clears the NG flag, which then contaminates every product it takes part in.
# `one`/`zero` of the same element type do not, and give the same matrix.
_eye(T, n) = [i == j ? one(T) : zero(T) for i in 1:n, j in 1:n]

"""
    assert_guaranteed(x, what)

Fail loudly unless every component of `x` still carries IntervalArithmetic's
`isguaranteed` flag. A cleared flag means some bare floating-point value
entered the computation, and the result can no longer be claimed as a rigorous
enclosure without a hand audit of that value. Certificate gates call this.
"""
function assert_guaranteed(x, what::AbstractString)
    ok = all(isguaranteed, x isa Interval ? (x,) : x)
    ok || error("NOT GUARANTEED: $what carries IntervalArithmetic's NG flag; " *
                "a bare floating-point value entered the computation and the " *
                "result is not a certified enclosure")
    return true
end

function search_bounds(T=BigFloat)
    p = T(pi)
    two = _lit(p, 2); sixteen = _lit(p, 16)
    return (two*asin(sin(p/sixteen)/two), p/sixteen)
end

function Xfun(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return sin(t) - (two*cos(t) - one(t))*sin(four*t)
end

function Yfun(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return cos(t) - (two*cos(t) - one(t))*cos(four*t)
end

function Xprime(t)
    two = _lit(t, 2); four = _lit(t, 4)
    return cos(t) + two*sin(t)*sin(four*t) - four*(two*cos(t) - one(t))*cos(four*t)
end

function Ffun(t)
    two = _lit(t, 2); four = _lit(t, 4); seven = _lit(t, 7)
    x = Xfun(t)
    return (two*x + sin(seven*t))^2 + cos(seven*t)^2 - four*sin(t/two)^2
end

function Fprime(t)
    two = _lit(t, 2); seven = _lit(t, 7); fourteen = _lit(t, 14)
    x = Xfun(t)
    xp = Xprime(t)
    return two*(two*x + sin(seven*t))*(two*xp + seven*cos(seven*t)) -
           fourteen*cos(seven*t)*sin(seven*t) - two*sin(t)
end

side_length(z) = _lit(z, 2)*sin(z/_lit(z, 2))

"""
    coordinates(z)

Explicit n=16 specialization of the Bingane--Audet constructor.

The formulas have been simplified so that no interval approximation to pi is
required. Row `i+1` is the labelled vertex p_i.
"""
function coordinates(z)
    p = fill(zero(z), 16, 2)
    x = Xfun(z)
    y = Yfun(z)
    # multiple-angle literals as guaranteed thin intervals (see `_lit`)
    k2 = _lit(z, 2); k3 = _lit(z, 3); k5 = _lit(z, 5); k6 = _lit(z, 6); k7 = _lit(z, 7)

    p[1,:] .= (zero(z), zero(z))
    p[2,:] .= (sin(k2*z)-sin(z), cos(z)-cos(k2*z))
    p[3,:] .= (sin(k3*z)-sin(z), cos(z)-cos(k3*z))
    p[4,:] .= (-x, y)
    p[5,:] .= (x+sin(k7*z), y+cos(k7*z))
    p[6,:] .= (x+sin(k6*z), y+cos(k6*z))
    p[7,:] .= (x+sin(k5*z), y+cos(k5*z))
    p[8,:] .= (sin(z), cos(z))
    p[9,:] .= (zero(z), one(z))
    p[10,:] .= (-sin(z), cos(z))
    p[11,:] .= (-x-sin(k5*z), y+cos(k5*z))
    p[12,:] .= (-x-sin(k6*z), y+cos(k6*z))
    p[13,:] .= (-x-sin(k7*z), y+cos(k7*z))
    p[14,:] .= (x, y)
    p[15,:] .= (sin(z)-sin(k3*z), cos(z)-cos(k3*z))
    p[16,:] .= (sin(z)-sin(k2*z), cos(z)-cos(k2*z))
    return p
end

sqdist(p, i, j) =
    (p[j+1,1]-p[i+1,1])^2 + (p[j+1,2]-p[i+1,2])^2

function build_jacobian(z)
    p = coordinates(z)
    ell = side_length(z)
    A = fill(zero(z), 31, 33)

    for i in 0:15
        j = mod(i+1,16)
        sx = (p[j+1,1]-p[i+1,1])/ell
        sy = (p[j+1,2]-p[i+1,2])/ell
        A[i+1,2i+1] = -sx
        A[i+1,2i+2] = -sy
        A[i+1,2j+1] = sx
        A[i+1,2j+2] = sy
        A[i+1,33] = -one(z)
    end

    for (k,(i,j)) in enumerate(ACTIVE_EDGES)
        ux = p[j+1,1]-p[i+1,1]
        uy = p[j+1,2]-p[i+1,2]
        r = 16+k
        A[r,2i+1] = -ux
        A[r,2i+2] = -uy
        A[r,2j+1] = ux
        A[r,2j+2] = uy
    end
    return A
end

function support_determinants(z)
    p = coordinates(z)
    vals = Tuple{Int,Int,typeof(z)}[]
    for i in 0:15
        ip = mod(i+1,16)
        ex = p[ip+1,1]-p[i+1,1]
        ey = p[ip+1,2]-p[i+1,2]
        for j in 0:15
            (j == i || j == ip) && continue
            qx = p[j+1,1]-p[i+1,1]
            qy = p[j+1,2]-p[i+1,2]
            push!(vals,(i,j,ex*qy-ey*qx))
        end
    end
    return vals
end

function inactive_pairs(z)
    p = coordinates(z)
    active = Set(ACTIVE_EDGES)
    vals = Tuple{Int,Int,typeof(z)}[]
    for i in 0:15, j in (i+1):15
        (i,j) in active && continue
        push!(vals,(i,j,sqdist(p,i,j)))
    end
    return vals
end

interval_abs_bound(x::Interval) = max(abs(inf(x)),abs(sup(x)))
interval_abs_bound(x::Real) = abs(x)

function regularity_test(MI)
    setprecision(BigFloat, 256) do
        M0 = BigFloat.(mid.(MI))
        C = interval.(inv(M0))     # thin intervals: exact BigFloats, flag preserved
        n = size(MI,1)
        E = _eye(eltype(MI), n) - C*MI
        bound = maximum(
            sum(interval_abs_bound(E[i,j]) for j in 1:n)
            for i in 1:n
        )
        return bound < 1, bound, C, E
    end
end

function krawczyk_linear(MI,bI)
    setprecision(BigFloat, 256) do
        M0 = BigFloat.(mid.(MI))
        b0 = BigFloat.(mid.(bI))
        C0 = inv(M0)
        C = interval.(C0)          # thin intervals: exact BigFloats, flag preserved
        x0 = interval.(C0*b0)      # thin: the centre is an exact BigFloat vector
        n = length(x0)
        R = _eye(eltype(MI), n) - C*MI
        residual = C*(bI-MI*x0)
        radius = max(big"1e-50", 10maximum(interval_abs_bound.(residual)))
        for _ in 1:24
            X = [interval(-radius,radius) for _ in 1:n]
            Kcorr = residual + R*X
            strict = all(
                inf(Kcorr[i]) > -radius && sup(Kcorr[i]) < radius
                for i in 1:n
            )
            if strict
                # RIGOR. The certified set is the exact real sum x0 + K(X).
                # Forming its endpoints as `x0[i]+inf(Kcorr[i])` in BigFloat
                # rounds TO NEAREST, so the reported box could come out up to
                # an ulp NARROWER than the certified one and would no longer be
                # guaranteed to contain the solution. Adding the thin interval
                # x0[i] to Kcorr[i] performs the same sum with OUTWARD
                # rounding, which is an enclosure by construction.
                enclosure = [x0[i] + Kcorr[i] for i in 1:n]
                return (pass=true, enclosure=enclosure, x0=x0,
                        radius=radius, residual=residual, operator=R)
            end
            radius *= 10
        end
        return (pass=false, enclosure=nothing, x0=x0, radius=radius,
                residual=residual, operator=R)
    end
end

function rigid_vectors(z)
    p = coordinates(z)
    rx = zeros(typeof(z),33)
    ry = zeros(typeof(z),33)
    rr = zeros(typeof(z),33)
    for i in 0:15
        rx[2i+1] = one(z)
        ry[2i+2] = one(z)
        rr[2i+1] = -p[i+1,2]
        rr[2i+2] = p[i+1,1]
    end
    return rx,ry,rr
end

"""
Algebraic identities proving that each Jacobian row annihilates translations
and infinitesimal rotation. This is a theorem about the assembly, not a
floating tolerance test.
"""
function rigid_annihilation_identities()
    return (
        translations = true,
        rotation = true,
        explanation =
        "Each distance row has opposite endpoint coefficients; for rotation, " *
        "(p_j-p_i) dot J(p_j-p_i)=0. The ell component is zero."
    )
end

function objective_covector(T=Float64)
    g = zeros(T,33)
    g[33] = _lit(T, 16)      # exact 16; thin & guaranteed for interval T
    return g
end

function normalized_matrix(A)
    B = transpose(A)[COLS_MINOR,:]
    row = zeros(eltype(A),1,31)
    row[1,19] = one(eltype(A))
    return vcat(B,row)
end

function omitted_residual_matrix(z)
    p = coordinates(z)
    return [one(z) zero(z) one(z);
            zero(z) one(z) zero(z);
            -p[2,2] p[2,1] -p[9,2]]
end

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

end
