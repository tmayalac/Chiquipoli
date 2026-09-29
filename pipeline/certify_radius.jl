# An EXPLICIT radius for the strict local maximality of A16.
#
#     julia --project=. pipeline/certify_radius.jl        (make radius)
#
# THE THEOREM (docs/guide/radius.md has the full proof). Let x = (p, l) be A16,
# A the Jacobian D(e,d) of build_jacobian (16 side rows divided by l, 15 active
# diameter rows), (alpha, lambda) the certified multipliers of stage 05, so that
#
#     16 eta = alpha . (A_E h) + lambda . (A_D h)      for every h = (v, eta),
#
# and V the three infinitesimal rigid motions. If
#
#     sigma^2 <= lambda_min(A'A + V V'),   r = sigma l / (2 (1 + |alpha|_2 / lambda_min)),
#
# then every labelled configuration (q, m) with |q_{i+1} - q_i| = m for all i,
# |q_i - q_j| <= 1 for all i, j, m >= l, and Procrustes distance
#     min over orientation-preserving motions g of |(g q - p, m - l)|_2  <  r
# is congruent to A16 (m = l). No convexity, cyclic order or inactive margin is
# used: only the equalities, the 15 active diameters, and the multipliers.
#
# PROOF IN ONE PARAGRAPH. At the optimal alignment h = (g q - p, m - l) is
# orthogonal to R_eq (first-order condition of the Procrustes problem). The
# squared constraints are quadratic, so their Taylor expansion at x is exact:
# 2l (A_E h)_i = -(|dh_i|^2 - eta^2) and 2 (A_D h)_e <= -|dh_e|^2 <= 0. The
# multiplier identity with eta >= 0 gives sum_e lambda_e |(A_D h)_e|
# <= |alpha|_2 |v_E|_2 / (2l), with |v_E|_2 <= 4 |h|^2. Hence
# |A h| <= (2/l)(1 + |alpha|_2/lambda_min) |h|^2, while |A h| >= sigma |h| on
# R_eq-perp. So h = 0 or |h| >= r.
#
# RIGOUR. Everything is outward-rounded interval arithmetic at 256 bits over the
# certified box Z_cert of stages 03-05 (which contains the root, see the box
# nesting gate of certify_a16.jl). sigma^2 is certified by an interval Cholesky
# factorisation of B - mu I, B = A'A + V V': if it does not break down, every
# symmetric matrix in the interval matrix is positive definite (Alefeld-Mayer),
# in particular B(z*) - mu I. Writes results/radius_certificate.toml.
include(joinpath(@__DIR__, "stages", "_bootstrap.jl"))
include(joinpath(@__DIR__, "stages", "05_certify_multipliers.jl"))

using TOML, Dates

"""
    interval_cholesky_pd(B) -> Bool

True when the interval Cholesky factorisation of the symmetric interval matrix
`B` runs to completion with every pivot strictly positive. Then every symmetric
real matrix enclosed by `B` is positive definite (Alefeld and Mayer, 1993).
Only the lower triangle of `B` is read.
"""
function interval_cholesky_pd(B)
    n = size(B, 1)
    L = similar(B)
    for j in 1:n
        s = B[j, j]
        for k in 1:j-1
            s -= L[j, k]^2
        end
        inf(s) > 0 || return false
        L[j, j] = sqrt(s)
        for i in j+1:n
            t = B[i, j]
            for k in 1:j-1
                t -= L[i, k] * L[j, k]
            end
            L[i, j] = t / L[j, j]
        end
    end
    return true
end

function run_radius(; radius=big"1e-28")
    setprecision(BigFloat, 256)
    r5 = run_multipliers_interval(radius=radius)
    r5.pass || return (pass=false, reason="multipliers not certified")
    Z = r5.Z
    A = build_jacobian(Z)
    rx, ry, rr = rigid_vectors(Z)
    V = hcat(rx, ry, rr)
    B = transpose(A) * A + V * transpose(V)
    assert_guaranteed(B, "A'A + VV'")

    # A floating estimate of the smallest eigenvalue, then the largest mu of the
    # form 0.99 * 0.9^k * estimate that the interval Cholesky certifies. The
    # factor 0.99 keeps the certified factorisation away from singularity, so
    # the result does not depend on the last bits of the floating estimate.
    Bm = Float64.(mid.(B))
    est = eigmin(Symmetric((Bm + transpose(Bm)) / 2))
    est > 0 || return (pass=false, reason="B not positive definite in floating point")
    mu = big"0.99" * BigFloat(est)
    certified = false
    for _ in 1:40
        muI = interval(mu)
        if interval_cholesky_pd(B - muI * A16Certificate._eye(eltype(B), size(B, 1)))
            certified = true
            break
        end
        mu *= big"0.9"
    end
    certified || return (pass=false, reason="interval Cholesky did not certify lambda_min")

    Y = r5.multiplier_enclosure
    alpha_norm = sqrt(sum(interval(max(abs(inf(Y[i])), abs(sup(Y[i]))))^2 for i in 1:16))
    lambda_min = interval(r5.lambda_lower)
    ell = side_length(Z)
    sigma = sqrt(interval(mu))
    rI = sigma * ell / (2 * (1 + alpha_norm / lambda_min))
    r_cert = inf(rI)          # a certified LOWER bound: the theorem holds for it

    println("lambda_min(A'A + VV') >= mu = ", Float64(mu), "   (floating estimate ", est, ")")
    println("sigma = sqrt(mu) >= ", Float64(inf(sigma)))
    println("|alpha|_2 <= ", Float64(sup(alpha_norm)), ",  lambda_min >= ", Float64(inf(lambda_min)))
    println("l in ", ell)
    println("CERTIFIED RADIUS r >= ", r_cert)
    return (pass=true, r=r_cert, mu=mu, alpha_norm=sup(alpha_norm), lambda_min=inf(lambda_min),
            ell_lower=inf(ell), Z=Z)
end

if abspath(PROGRAM_FILE) == @__FILE__
    res = run_radius()
    println("\n============================================================")
    println("EXPLICIT RADIUS OF STRICT LOCAL MAXIMALITY OF A16: ",
            res.pass ? "CERTIFIED r >= $(Float64(res.r))" : "NOT CERTIFIED ($(res.reason))")
    println("============================================================")
    if res.pass && get(ENV, "CHIQUI_NO_RECORD", "") != "1"
        projroot = normpath(joinpath(@__DIR__, ".."))
        rec = Dict{String,Any}(
            "meta" => Dict{String,Any}(
                "certificate" => "explicit radius of strict local maximality of A16 (pipeline/certify_radius.jl)",
                "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z",
                "bigfloat_precision_bits" => precision(BigFloat),
                "norm" => "Euclidean on (R^2)^16 x R, after optimal orientation-preserving alignment (Procrustes)"),
            "radius" => Dict{String,Any}(
                "r_lower_bound" => string(res.r),
                "sigma_squared_lower_bound" => string(res.mu),
                "alpha_norm_upper_bound" => string(res.alpha_norm),
                "lambda_min_lower_bound" => string(res.lambda_min),
                "ell_lower_bound" => string(res.ell_lower),
                "formula" => "r = sigma * ell / (2 * (1 + |alpha|_2 / lambda_min))"),
        )
        out = joinpath(projroot, "results", "radius_certificate.toml")
        open(out, "w") do io
            println(io, "# Explicit radius of strict local maximality of A16 — machine-readable record.")
            println(io, "# Auto-generated by pipeline/certify_radius.jl; do not edit.")
            TOML.print(io, rec; sorted=true)
        end
        println("wrote ", relpath(out, projroot))
    end
    res.pass || exit(1)
end
