# Exact multiplier witness for the A16 stationarity identity.
#
# Lean cannot be asked to *solve* the multiplier system — that would mean exact
# linear algebra over a number field inside the kernel. It can be asked to
# *check* a witness, which is cheap. This module computes that witness exactly.
#
# Formulation. Use the squared side length `t = ℓ²` as the scalar variable:
#
#     side i:      |p_{i+1} - p_i|² - t = 0
#     diameter ij: |p_i - p_j|²     - 1 = 0
#
# Maximising the perimeter `16√t` is equivalent to maximising `t`, so the
# objective covector is `e_t`. Both reparametrisations (`d ↦ d²`, `ℓ ↦ ℓ²`)
# rescale the multipliers by strictly positive factors, so strict positivity of
# the diameter multipliers is unaffected — but every Jacobian entry is now
# `2(p_j - p_i)`, with no division by `ℓ = √(2-2c)`. That keeps the whole
# computation inside `Q(c,s)` instead of a degree-4 extension.
#
# Factoring out `s`. Writing `p_k = (s·XC_k(c), YC_k(c))`, every x-variable row
# of the transposed Jacobian carries a common factor `s` and has right-hand
# side `0`, so it may be divided by `s ≠ 0`. What remains is a linear system
# over `Q[c]` alone:
#
#     16 x-rows :  Σ_i  (…poly in c…) · y_i = 0
#     16 y-rows :  Σ_i  (…poly in c…) · y_i = 0
#      1 t-row  :  −Σ_i α_i = 1
#
# Rank is 30, not 31 (LICQ fails), so as in the Julia certificate we drop the
# three variable rows `x₁, y₁, x₈` and pin one multiplier, solve the resulting
# 31×31 system, and then verify the three dropped equations separately.
#
# Arithmetic is done in `Q[c]/(Fc)`: every element stays of degree < 12, so
# Gaussian elimination never blows up the way a fraction-free solve over `Q(c)`
# would (intermediate degrees there reach ~180).

module Multipliers

export exact_multipliers

const QQ = Rational{BigInt}

# --- polynomial helpers (independent of A16Certificate's non-exported ones) --
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

"""Extended Euclid in Q[c]: returns (g, u) with u*a ≡ g (mod m)."""
function pgcdx(a, m)
    r0, r1 = ptrim(copy(m)), ptrim(copy(a))
    s0, s1 = QQ[QQ(0)], QQ[QQ(1)]
    while !iszp(r1)
        q, r = pdivrem(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, psub(s0, pmul(q, s1))
    end
    return r0, s0
end

struct ModRing
    Fc::Vector{QQ}
end
red(R::ModRing, a) = last(pdivrem(a, R.Fc))
madd(R, a, b) = red(R, padd(a, b))
msub(R, a, b) = red(R, psub(a, b))
mmul(R, a, b) = red(R, pmul(a, b))
function minv(R::ModRing, a)
    g, u = pgcdx(red(R, a), R.Fc)
    length(g) == 1 && !iszp(g) || return nothing      # not invertible mod Fc
    return red(R, [x / g[1] for x in u])
end

"""
Solve `M x = b` over `Q[c]/(Fc)` by Gaussian elimination with invertible-pivot
search. Returns `nothing` if no pivot is invertible in some column (which would
mean `Fc` factors in a way this system feels).
"""
function msolve(R::ModRing, M, b)
    n = size(M, 1)
    A = [copy(M[i, j]) for i in 1:n, j in 1:n]
    y = [copy(b[i]) for i in 1:n]
    for k in 1:n
        piv = 0; pinv = nothing
        for r in k:n
            iszp(A[r, k]) && continue
            ci = minv(R, A[r, k])
            if ci !== nothing; piv = r; pinv = ci; break; end
        end
        piv == 0 && return nothing
        if piv != k
            for j in 1:n; A[k, j], A[piv, j] = A[piv, j], A[k, j]; end
            y[k], y[piv] = y[piv], y[k]
        end
        for j in 1:n; A[k, j] = mmul(R, pinv, A[k, j]); end
        y[k] = mmul(R, pinv, y[k])
        for r in 1:n
            r == k && continue
            f = A[r, k]
            iszp(f) && continue
            for j in 1:n; A[r, j] = msub(R, A[r, j], mmul(R, f, A[k, j])); end
            y[r] = msub(R, y[r], mmul(R, f, y[k]))
        end
    end
    return y
end

"""
    exact_multipliers(XC, YC, Fc, active; pin_index, pin_value)

Returns `(y, residuals)` where `y[1:16]` are the side multipliers, `y[17:31]`
the active-diameter multipliers (each an element of `Q[c]/(Fc)`), and
`residuals` are the 33 stationarity defects reduced mod `Fc` (all must be zero).
"""
function exact_multipliers(XC, YC, Fc, active; pin_index::Int = 19,
                           pin_value::Vector{QQ} = QQ[QQ(1)],
                           omit::Vector{Int} = [3, 4, 17])
    R = ModRing(Fc)
    nC = 16 + length(active)                     # 31 constraints
    # rows[v] : coefficients of each constraint in variable-row v (1..33)
    rows = [[QQ[QQ(0)] for _ in 1:nC] for _ in 1:33]
    addto!(v, k, p) = (rows[v][k] = padd(rows[v][k], p))

    for i in 0:15                                # side constraints
        j = mod(i + 1, 16); k = i + 1
        dX = psub(XC[j+1], XC[i+1]); dY = psub(YC[j+1], YC[i+1])
        addto!(2i + 1, k, pmul(QQ[QQ(-1)], dX)); addto!(2i + 2, k, pmul(QQ[QQ(-1)], dY))
        addto!(2j + 1, k, dX);                   addto!(2j + 2, k, dY)
        addto!(33,     k, QQ[QQ(-1)])            # ∂/∂t  (the 2's cancel; see below)
    end
    for (m, (i, j)) in enumerate(active)         # active-diameter constraints
        k = 16 + m
        dX = psub(XC[j+1], XC[i+1]); dY = psub(YC[j+1], YC[i+1])
        addto!(2i + 1, k, pmul(QQ[QQ(-1)], dX)); addto!(2i + 2, k, pmul(QQ[QQ(-1)], dY))
        addto!(2j + 1, k, dX);                   addto!(2j + 2, k, dY)
    end
    # RHS is the objective covector e_t (the common factor 2 is dropped from
    # every gradient above, which only rescales the whole multiplier vector).
    # The t-row reads -Σ α_i = 1, i.e. Σ α_i = -1.
    rhs = [QQ[QQ(0)] for _ in 1:33]
    rhs[33] = QQ[QQ(1)]

    keep = [v for v in 1:33 if !(v in omit)]      # 30 equations
    @assert length(keep) == 30
    M = Array{Vector{QQ}}(undef, nC, nC)
    b = Vector{Vector{QQ}}(undef, nC)
    for (r, v) in enumerate(keep)
        for k in 1:nC; M[r, k] = rows[v][k]; end
        b[r] = rhs[v]
    end
    for k in 1:nC; M[nC, k] = (k == pin_index ? QQ[QQ(1)] : QQ[QQ(0)]); end
    b[nC] = pin_value

    y = msolve(R, M, b)
    y === nothing && return nothing

    residuals = Vector{Vector{QQ}}(undef, 33)
    for v in 1:33
        acc = QQ[QQ(0)]
        for k in 1:nC; acc = padd(acc, pmul(rows[v][k], y[k])); end
        residuals[v] = red(R, psub(acc, rhs[v]))
    end
    # Raw (unreduced) defects, and their exact quotients by Fc. Each reduces to
    # zero mod Fc, so the division is exact; the quotient is precisely the
    # coefficient Lean's `linear_combination` needs.
    raw = Vector{Vector{QQ}}(undef, 33)
    quot = Vector{Vector{QQ}}(undef, 33)
    for v in 1:33
        acc = QQ[QQ(0)]
        for k in 1:nC; acc = padd(acc, pmul(rows[v][k], y[k])); end
        raw[v] = psub(acc, rhs[v])
        q, r = pdivrem(raw[v], Fc)
        @assert iszp(r) "row $v: residual not divisible by Fc"
        quot[v] = q
    end
    return (y = y, residuals = residuals, rows = rows, raw = raw, quot = quot)
end

end # module
