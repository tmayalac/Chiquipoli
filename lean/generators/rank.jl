# Exact elimination certificate for the rank/kernel gate (Prop 6.2(6)).
#
# What has to be shown is `I_eq = R_eq`: the only tangent vectors annihilated by
# every active constraint differential are the rigid infinitesimal motions. The
# inclusion `⊇` is a ring identity. This module produces the certificate for
# `⊆`, i.e. for `rank = 30`.
#
# The tangent variables are rescaled so that every coefficient is a polynomial
# in `c` alone. Writing `p_k = (sin z · XC_k, YC_k)` and a displacement
# `w_k = (w_k¹, w_k²)`, the differential of `|p_j - p_i|²` is
#
#     2 [ sin z · dXC · (w_j¹ - w_i¹) + dYC · (w_j² - w_i²) ]
#
# so with `V_{2k+1} := sin z · w_k¹`, `V_{2k+2} := w_k²` and `V_33 := dt/2`,
# every constraint reads `Σ_v B[k,v] · V_v = 0` with `B` over `Q[c]`.
#
# Elimination is done in `Q[c]/(Fc)`. That is not a convenience: measured on
# this system, eliminating without reduction reaches degree 1209 and 464-digit
# coefficients by step 30, whereas reducing at every step holds it to degree 11
# and 9 digits. The price is that each step is only valid modulo `Fc`, so the
# reduction quotient has to be recorded:
#
#     rowNEW = rowOLD − f · rowPIVOT − (Σ_j q_j V_j) · Fc
#
# which is exactly the shape `linear_combination` consumes. Julia divides;
# Lean adds back.

module RankCert

export elimination_certificate

const QQ = Rational{BigInt}

ptrim(a) = (n = length(a); while n > 1 && a[n] == 0; n -= 1; end; a[1:n])
iszp(a) = all(==(QQ(0)), a)
padd(a, b) = ptrim([(i <= length(a) ? a[i] : QQ(0)) + (i <= length(b) ? b[i] : QQ(0))
                    for i in 1:max(length(a), length(b))])
psub(a, b) = ptrim([(i <= length(a) ? a[i] : QQ(0)) - (i <= length(b) ? b[i] : QQ(0))
                    for i in 1:max(length(a), length(b))])
function pmul(a, b)
    (iszp(a) || iszp(b)) && return QQ[QQ(0)]
    r = zeros(QQ, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b); r[i+j-1] += a[i] * b[j]; end
    return ptrim(r)
end
function pdivrem(a, b)
    a = ptrim(copy(a)); bd = length(b) - 1
    q = zeros(QQ, max(length(a) - length(b) + 1, 1))
    while length(a) - 1 >= bd && !iszp(a)
        co = a[end] / b[end]; sh = length(a) - 1 - bd; q[sh+1] = co
        a = ptrim(psub(a, pmul(b, vcat(zeros(QQ, sh), [co]))))
    end
    return ptrim(q), a
end
function pgcdx(a, m)
    r0, r1 = ptrim(copy(m)), ptrim(copy(a))
    s0, s1 = QQ[QQ(0)], QQ[QQ(1)]
    while !iszp(r1)
        q, r = pdivrem(r0, r1); r0, r1 = r1, r
        s0, s1 = s1, psub(s0, pmul(q, s1))
    end
    return r0, s0
end

"""
    elimination_certificate(B, Fc; rows, kept, free)

Row-reduce the selected submatrix in `Q[c]/(Fc)` without ever physically
swapping rows: `pivrow[k]` records which original row serves as pivot at stage
`k`. Returns the reduced rows, the pivot order, and the per-step certificates.
"""
function elimination_certificate(B, Fc; rows, kept, free)
    red(a) = last(pdivrem(a, Fc))
    function inv_mod(a)
        g, u = pgcdx(red(a), Fc)
        length(g) == 1 && !iszp(g) || return nothing
        return red([x / g[1] for x in u])
    end
    cols = vcat(kept, free)
    n = length(rows); m = length(cols)
    R = [copy(B[rows[i], cols[j]]) for i in 1:n, j in 1:m]
    alive = collect(1:n)
    pivrow = Int[]
    steps = NamedTuple[]
    for k in 1:length(kept)
        pk = 0; pinv = nothing
        for r in alive
            iszp(R[r, k]) && continue
            ci = inv_mod(R[r, k])
            if ci !== nothing; pk = r; pinv = ci; break; end
        end
        pk == 0 && error("no invertible pivot at stage $k")
        push!(pivrow, pk)
        filter!(!=(pk), alive)
        for r in alive
            iszp(R[r, k]) && continue
            f = red(pmul(R[r, k], pinv))
            corr = Vector{Vector{QQ}}(undef, m)
            for j in 1:m
                raw = psub(R[r, j], pmul(f, R[k == 0 ? 1 : pk, j]))
                q, rem = pdivrem(raw, Fc)
                R[r, j] = rem; corr[j] = q
            end
            push!(steps, (row = r, piv = pk, stage = k, f = f, corr = corr))
        end
    end
    return (R = R, pivrow = pivrow, steps = steps, cols = cols,
            nkept = length(kept), nfree = length(free))
end

end # module
