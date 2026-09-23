include(joinpath(@__DIR__, "_bootstrap.jl"))

# Rigorous interval-Newton existence/uniqueness certificate for the
# constructor root F(z)=0.
#
# IMPORTANT (rigor): the point value F(m) at the box midpoint m must itself be
# rigorously ENCLOSED, not approximated. Evaluating `Ffun(m)` on a bare
# BigFloat m rounds every sin/cos/product to nearest and returns only an
# approximation to the exact real F(m); the interval-Newton conclusion would
# then not be a proof. We instead evaluate F on the thin interval interval(m),
# so `Ffun(mI)` encloses the exact real F(m) and
#     N = m - F(m)/F'(Z)
# is a rigorous enclosure of the Newton operator. If N ⊆ int(Z) and
# 0 ∉ F'(Z), the interval-Newton theorem gives a UNIQUE root in Z.
#
# We additionally certify strict monotonicity of F on the whole declared
# search interval (2*asin(sin(pi/16)/2), pi/16): if 0 ∉ F'(search) with the
# endpoints rigorously enclosed (pi enclosed via interval(BigFloat, pi)), then
# F is strictly monotone there, so the root is unique not merely in the box
# but in the entire search interval of the constructor.

"Rigorous enclosures [loI, hiI] of the search-interval endpoints, pi enclosed."
function search_bounds_interval()
    piI = interval(BigFloat, π)
    two = interval(BigFloat, 2); sixteen = interval(BigFloat, 16)
    loI = two*asin(sin(piI/sixteen)/two)
    hiI = piI/sixteen
    return loI, hiI
end

function run_root_interval(; radii=[big"1e-30",big"1e-29",big"1e-28",
                                     big"1e-27",big"1e-26"])
    setprecision(BigFloat, 256)
    loI, hiI = search_bounds_interval()
    search = interval(inf(loI), sup(hiI))     # superset of the true (lo,hi)

    # Global monotonicity ⇒ at most one root in the whole search interval.
    Dsearch = Fprime(search)
    # IntervalArithmetic's own audit flag: a cleared NG flag means some bare
    # floating-point value entered the evaluation and the enclosure can no
    # longer be claimed rigorous. Gate on it rather than trusting it by eye.
    assert_guaranteed(search, "search interval")
    assert_guaranteed(Dsearch, "F'(search interval)")
    monotone_pass = !in_interval(0, Dsearch)
    println("search interval (enclosed) = ", search)
    println("F'(search) = ", Dsearch)
    println("strict monotonicity on search interval PASS = ", monotone_pass)

    for radius in radii
        Z = interval(z_nominal-radius, z_nominal+radius)
        m = mid(Z)
        D = Fprime(Z)
        derivative_pass = !in_interval(0, D)
        if !derivative_pass
            continue
        end

        # Rigorous point enclosure of F(m): evaluate on the thin interval [m,m].
        mI = interval(m)
        Fm = Ffun(mI)
        N = mI - Fm/D
        assert_guaranteed(Z,  "root box Z")
        assert_guaranteed(D,  "F'(Z)")
        assert_guaranteed(Fm, "F(m) enclosure")
        assert_guaranteed(N,  "Newton image N(Z)")

        # Rigorous domain check: prove Z ⊂ (lo,hi) using directed endpoint
        # bounds (sup(loI) is the largest possible lo, inf(hiI) the smallest hi).
        domain_pass = inf(Z) > sup(loI) && sup(Z) < inf(hiI)
        newton_pass = inf(N) > inf(Z) && sup(N) < sup(Z)

        println("radius = ", radius)
        println("Z = ", Z)
        println("F'(Z) = ", D)
        println("F(m) enclosure = ", Fm)
        println("N(Z) = ", N)
        println("domain PASS = ", domain_pass)
        println("derivative PASS = ", derivative_pass)
        println("Newton PASS = ", newton_pass)

        if domain_pass && newton_pass
            # Uniqueness in Z is guaranteed by the interval-Newton theorem
            # (N ⊆ int(Z), 0 ∉ F'(Z)). Uniqueness in the whole search interval
            # additionally requires monotone_pass.
            println("unique root in box PASS = true")
            println("unique root in whole search interval PASS = ", monotone_pass)
            return (Z=Z, derivative=D, newton=N, Fm=Fm, radius=radius,
                    pass=true, unique_in_box=true,
                    unique_in_search_interval=monotone_pass)
        end
    end

    println("ROOT CERTIFICATE FAILED for all prescribed radii")
    return (Z=nothing, derivative=nothing, newton=nothing, Fm=nothing,
            radius=nothing, pass=false, unique_in_box=false,
            unique_in_search_interval=false)
end

(abspath(PROGRAM_FILE) == @__FILE__) && run_root_interval()
