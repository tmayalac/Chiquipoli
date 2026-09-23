# The Jacobian D(e,d), the preconditioned regularity test (rank, Proposition
# 6.2(6)) and the linear Krawczyk operator (multipliers, Proposition 6.2(5)).
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

# The Jacobian D(e,d) of the 16 side and 15 active diameter constraints.
#
# DEPENDS ON THE EXACT IDENTITIES. Each side row is divided by the common value
# ell(z) = 2 sin(z/2), not by that side's own length, and the diameter rows are
# not normalised at all. So this matrix is D(e,d) at z* only because, at z*,
# every side has length ell(z*) and every declared diameter has length 1 --
# which is Lemma 6.1, proved exactly in pipeline/stages/06_prove_exact_identities.jl. The rank
# and multiplier gates (04, 05) therefore certify properties of D(e,d) only in
# conjunction with gate 06; certify_a16.jl's verdict is their conjunction, so the
# certificate is sound, but a reader should not take the Jacobian gates as
# standing alone. (Flagged in the 2026-09 external audit; the general framework
# in SmallPolygons.jl normalises each row by its own length instead.)
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

interval_abs_bound(x::Interval) = max(abs(inf(x)),abs(sup(x)))
interval_abs_bound(x::Real) = abs(x)

function regularity_test(MI)
    setprecision(BigFloat, 256) do
        M0 = BigFloat.(mid.(MI))
        C = interval.(inv(M0))     # thin intervals: exact BigFloats, flag preserved
        n = size(MI,1)
        E = _eye(eltype(MI), n) - C*MI
        # Row sums accumulated as intervals and read off by their supremum, so
        # the reported bound is a directed upper bound on ‖I - CM‖∞ and not a
        # round-to-nearest sum of upper bounds. Each |E_ij| bound is an exact
        # BigFloat (abs of an endpoint), hence a guaranteed thin interval.
        # The decision `< 1` was never at risk (the error of a nearest sum of
        # ≤ 31 terms is ~31·2⁻²⁵⁶ relative, 25 orders below the margin), but the
        # constants the article prints must be certified bounds themselves
        # (2026-09 external audit, D05).
        bound = maximum(
            sup(sum(interval(interval_abs_bound(E[i,j])) for j in 1:n))
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

It is ARGUED here, not computed: the function returns constants and a textual
justification, and the rank upper bound rank D(e,d) <= 30 rests on that
argument plus the vertex distinctness supplied by the convexity gate. The same
statement is machine-checked in the Lean layer (`dsq_rigid`, `kernel_is_rigid`,
`rank_eq_thirty`), where it is a kernel-verified theorem.
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
