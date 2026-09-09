"""
    ExactIdentity

General exact-identity engine for side and active-diameter equalities of a
convex equilateral small polygon, closing referee point R2 as a REUSABLE
capability (not an A16-specific one). See `docs/general-framework.md`.

Theory (verified in the analysis). Every candidate's coordinates lie in the
ring `Q(c,s)` with `s^2 = 1 - c^2`, where `c = cos θ`, `s = sin θ`, and the
scalar `θ` satisfies a defining polynomial `Fc(c) = 0` (for root-parametrized
families like Audet/A16 and Vincze/H8, `Fc` is the constructor equation reduced
to `c`; for fixed-angle families like Reinhardt and the regular polygon, `Fc`
is the minimal polynomial of `cos θ`). A squared distance minus its target
rationalizes to `(A(c) + s·B(c)) / den(c)` with `A,B,den ∈ Q[c]`. The equality
holds at the root iff, with `den(c*) ≠ 0`:

  * `B ≡ 0`:  `A` is divisible by `Fc`  (the clean A16 case; unconditional if
              `A ≡ 0`).
  * `B ≢ 0`:  the conjugate product `A^2 - (1-c^2) B^2` is divisible by `Fc`
              (so `(A+sB)(A-sB) = 0` at `c*`, EXACT algebra) AND the conjugate
              factor `A - s·B` is certified `≠ 0` at the root (a rigorous
              interval bound-away-from-zero, which fixes the sign so that
              `A + s·B = 0` follows — this is NOT the zero-trap: we prove a
              product is exactly zero and one factor nonzero).

Everything is exact `Rational{BigInt}` arithmetic except the single sign check,
which is a certified interval non-vanishing test.
"""
module ExactIdentity

using IntervalArithmetic

export CS, cs_c, cs_s, cs_const, csadd, cssub, csmul, csneg, csinv, csdiv,
       cs_cos, cs_sin, RPoly, identity_status, sqdist_cs, prove_all

# --------------------------- exact Q[c] arithmetic -------------------------
const RPoly = Vector{Rational{BigInt}}

ptrim(a::RPoly) = (n = length(a); while n > 1 && a[n] == 0; n -= 1; end; a[1:n])
iszeropoly(a::RPoly) = all(==(0//1), a)
padd(a, b) = ptrim([ (i<=length(a) ? a[i] : 0//1) + (i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b)) ])
psub(a, b) = ptrim([ (i<=length(a) ? a[i] : 0//1) - (i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b)) ])
pscale(a, k) = ptrim([x*k for x in a])
function pmul(a::RPoly, b::RPoly)
    (iszeropoly(a) || iszeropoly(b)) && return RPoly([0//1])
    r = zeros(Rational{BigInt}, length(a)+length(b)-1)
    for i in eachindex(a), j in eachindex(b); r[i+j-1] += a[i]*b[j]; end
    return ptrim(r)
end
function pdivrem(a::RPoly, b::RPoly)
    a = ptrim(copy(a)); bdeg = length(b)-1
    q = zeros(Rational{BigInt}, max(length(a)-length(b)+1, 1))
    while length(a)-1 >= bdeg && !iszeropoly(a)
        coeff = a[end]/b[end]; shift = length(a)-1-bdeg; q[shift+1] = coeff
        a = ptrim(psub(a, pmul(b, vcat(zeros(Rational{BigInt},shift), [coeff]))))
    end
    return ptrim(q), a
end
divisible(a::RPoly, F::RPoly) = (iszeropoly(a) || iszeropoly(last(pdivrem(a, F))))
function pgcd(a::RPoly, b::RPoly)
    a = ptrim(a); b = ptrim(b)
    while !iszeropoly(b); a, b = b, last(pdivrem(a, b)); end
    return a
end

const ONE_MINUS_C2 = RPoly([1//1, 0//1, -1//1])

# ------------------- elements of Q(c,s)/(s^2-1+c^2): (A + sB)/den ------------
struct CS
    A::RPoly    # rational (c) part numerator
    B::RPoly    # s-linear part numerator
    den::RPoly  # common denominator (in Q[c])
end
cs_const(q::Rational) = CS(RPoly([Rational{BigInt}(q)]), RPoly([0//1]), RPoly([1//1]))
cs_const(q::Integer) = cs_const(Rational{BigInt}(q))
cs_c() = CS(RPoly([0//1, 1//1]), RPoly([0//1]), RPoly([1//1]))
cs_s() = CS(RPoly([0//1]), RPoly([1//1]), RPoly([1//1]))
csneg(x::CS) = CS(pscale(x.A, -1//1), pscale(x.B, -1//1), x.den)

function csadd(x::CS, y::CS)
    CS(padd(pmul(x.A, y.den), pmul(y.A, x.den)),
       padd(pmul(x.B, y.den), pmul(y.B, x.den)),
       pmul(x.den, y.den))
end
cssub(x::CS, y::CS) = csadd(x, csneg(y))

function csmul(x::CS, y::CS)
    # (Ax+sBx)(Ay+sBy) = (AxAy + (1-c^2)BxBy) + s(AxBy+AyBx), over den_x*den_y
    A = padd(pmul(x.A, y.A), pmul(ONE_MINUS_C2, pmul(x.B, y.B)))
    B = padd(pmul(x.A, y.B), pmul(x.B, y.A))
    CS(A, B, pmul(x.den, y.den))
end
cssq(x::CS) = csmul(x, x)

"Multiplicative inverse in Q(c,s): 1/((A+sB)/den) = den(A-sB)/(A^2-(1-c^2)B^2)."
function csinv(x::CS)
    nrm = psub(pmul(x.A, x.A), pmul(ONE_MINUS_C2, pmul(x.B, x.B)))  # A^2-(1-c^2)B^2
    CS(pmul(x.den, x.A), pscale(pmul(x.den, x.B), -1//1), nrm)
end
csdiv(x::CS, y::CS) = csmul(x, csinv(y))

# Chebyshev: cos(kθ) = T_k(c);  sin(kθ) = s·U_{k-1}(c).
function _cheb(kmax)
    T = Dict(0 => RPoly([1//1]), 1 => RPoly([0//1, 1//1]))
    U = Dict(0 => RPoly([1//1]), 1 => RPoly([0//1, 2//1]))
    c1 = RPoly([0//1, 2//1])
    for k in 2:kmax
        T[k] = psub(pmul(c1, T[k-1]), T[k-2])
        U[k] = psub(pmul(c1, U[k-1]), U[k-2])
    end
    return T, U
end
const _CHEB = _cheb(40)
cs_cos(k::Integer) = CS(k == 0 ? RPoly([1//1]) : _CHEB[1][k], RPoly([0//1]), RPoly([1//1]))
cs_sin(k::Integer) = k == 0 ? cs_const(0) : CS(RPoly([0//1]), _CHEB[2][k-1], RPoly([1//1]))

"Squared distance between coordinate CS-pairs p[i]=(x,y) (0-based), as a CS element."
function sqdist_cs(coords, i, j)
    dx = cssub(coords[j+1][1], coords[i+1][1])
    dy = cssub(coords[j+1][2], coords[i+1][2])
    return csadd(cssq(dx), cssq(dy))
end

"""
    identity_status(coords, i, j, target_num, Fc; sign_ok) -> Symbol

Prove `|p_i - p_j|^2 == target` at the root of `Fc`, where `target_num ∈ Q[c]`.
`sign_ok(A, B)` must certify (by interval) that `A(c*) - s* B(c*) ≠ 0`; it is
called only in the `B ≢ 0` branch. Returns :UNCONDITIONAL, :PROVED, or :FAIL.
"""
function identity_status(coords, i, j, target_num::RPoly, Fc::RPoly; sign_ok)
    d = sqdist_cs(coords, i, j)
    # (A + sB)/den - target  =  (A - target*den + sB)/den
    A = psub(d.A, pmul(target_num, d.den))
    B = d.B
    den = d.den
    # den(c*) != 0, established by coprimality in Q[c].
    #
    # WHY THE GCD SUFFICES, since two independent reviewers have now read this
    # line as insufficient and asked for an interval evaluation of `den` over
    # the root box instead. It is not insufficient, and the interval evaluation
    # would be strictly weaker.
    #
    # `den` and `Fc` are polynomials with rational coefficients. Suppose some
    # root c* of Fc had den(c*) = 0. Then (X - c*) divides both in C[X], so
    # their gcd in C[X] is non-constant. But the gcd of two polynomials over a
    # field is computed by the Euclidean algorithm, which never leaves the field
    # the coefficients live in; hence gcd_{Q[X]}(den, Fc) and gcd_{C[X]}(den, Fc)
    # agree up to a unit, and a non-constant gcd over C forces a non-constant
    # gcd over Q. Contrapositive: gcd = constant in Q[X] implies den and Fc share
    # no root anywhere in C, in particular none in R and none at c*. The test
    # below is therefore exact and complete, and it covers repeated roots too,
    # which is the case the objection usually has in mind: multiplicity changes
    # nothing, since (X - c*) divides den whatever its multiplicity in Fc.
    #
    # An interval evaluation of `den` over a box around c* would prove less: it
    # bounds den away from zero only on that box, only to the width the
    # enclosure achieves, and it would have to be redone for every candidate and
    # every box. The gcd is a statement about all roots at once, in exact
    # arithmetic, with no box at all.
    g = pgcd(den, Fc)
    (length(g) == 1 && !iszeropoly(g)) || return :FAIL       # den could vanish at root
    if iszeropoly(A) && iszeropoly(B)
        return :UNCONDITIONAL
    elseif iszeropoly(B)
        return divisible(A, Fc) ? :PROVED : :FAIL
    elseif divisible(A, Fc) && divisible(B, Fc)
        # both rational and s-parts vanish at the root ⇒ A + sB = 0 there.
        return :PROVED
    else
        # product (A+sB)(A-sB) = A^2-(1-c^2)B^2 vanishes at the root (exact),
        # and the conjugate factor A - sB is certified ≠ 0 (interval), so the
        # equilateral factor A + sB = 0. (Not the zero-trap: the product is
        # proven exactly zero and one factor proven nonzero.)
        prod = psub(pmul(A, A), pmul(ONE_MINUS_C2, pmul(B, B)))
        divisible(prod, Fc) || return :FAIL
        return sign_ok(A, B) ? :PROVED : :FAIL
    end
end

"""
    _peval(p, x)

Enclose the value of the exact rational polynomial `p` at the interval `x`
(Horner). Every coefficient is converted with `interval(BigFloat, q)`, which
rounds the rational OUTWARD.

Do not simplify this to `interval(BigFloat(numerator(q)))/interval(BigFloat(
denominator(q)))`. `BigFloat(n)` rounds a BigInt TO NEAREST, and wrapping the
result in `interval` then asserts that rounded value as exact: for any integer
past the 256-bit mantissa the call returns a THIN interval at the wrong number
and silently stops being an enclosure (checked: `2^260+1` comes back off by
one, with zero width). Coefficients that large do not arise for the candidates
currently shipped — the only branch that calls this feeds at most 28-bit
coefficients, and A16 never reaches it at all — but nothing in the code
enforced that, and the failure mode is silent.
"""
function _peval(p::RPoly, x)
    v = zero(x)
    for k in length(p):-1:1
        v = v*x + interval(BigFloat, p[k])
    end
    return v
end

"""
    prove_all(coords, n, active, side_target, diam_target, Fc, zbox) -> (sides, diams)

Prove every side (`|p_{i+1}-p_i|^2 = side_target`) and active diameter
(`|p_i-p_j|^2 = diam_target`) exactly, returning per-equality statuses. `zbox`
is an interval enclosing the parameter θ; it is used only for the certified
sign check `A(c*) - s* B(c*) ≠ 0` in the `B ≢ 0` branch.
"""
function prove_all(coords, n, active, side_target::RPoly, diam_target::RPoly, Fc::RPoly, zbox)
    cstar = cos(zbox); sstar = sin(zbox)
    sok = (A, B) -> !in_interval(0, _peval(A, cstar) - sstar*_peval(B, cstar))
    sides = [identity_status(coords, i, mod(i+1, n), side_target, Fc; sign_ok=sok) for i in 0:n-1]
    diams = [identity_status(coords, i, j, diam_target, Fc; sign_ok=sok) for (i, j) in active]
    return sides, diams
end

end # module
