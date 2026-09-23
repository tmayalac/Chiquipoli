# The A16 certificate stages: pinned values, root, derivative, failure paths.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

@testset "Certified values have not drifted" begin
    # Regression guard on the numbers the article prints. A status of
    # :CERTIFIED does not catch a value that moves; these do.
    setprecision(BigFloat, 256)
    z = z_nominal

    ell = side_length(z)
    @test abs(ell      - big"0.1959554930055385228996085517576411062720") < big"1e-38"
    @test abs(16 * ell - big"3.1352878880886163663937368281222577003534") < big"1e-37"

    # smallest support determinant, article Proposition 6.2(3)
    @test minimum(v[3] for v in support_determinants(z)) > big"0.0074882049306989244"

    # inactive margin, article Proposition 6.2(4). inactive_pairs returns
    # SQUARED distances, and the margin is 1 - sqrt(worst).
    pairs = inactive_pairs(z)
    worst = maximum(v[3] for v in pairs)
    @test 1 - sqrt(worst) > big"0.0080997106581357295"
    # and it is attained at the critical pair the article names
    @test [(v[1], v[2]) for v in pairs if v[3] == worst] == [(4, 12)]
end

@testset "Rigorous root certificate" begin
    # Loads run_root_interval (guarded, does not auto-run on include).
    include(joinpath(@__DIR__, "..", "pipeline", "stages", "02_certify_root.jl"))
    r = run_root_interval()
    @test r.pass
    @test r.unique_in_box
    # F is strictly monotone on the whole search interval => unique root there.
    @test r.unique_in_search_interval
    # The point value F(m) must be a genuine ENCLOSURE, not a bare float:
    # a thin-interval evaluation has inf <= sup with positive rounding width.
    @test r.Fm isa Interval
    @test inf(r.Fm) <= sup(r.Fm)
    @test sup(r.Fm) - inf(r.Fm) > 0
end

@testset "Fprime is the derivative of Ffun (chain rule through Fc)" begin
    # Fprime is written by hand and carries the whole of Prop 6.2(1): interval
    # Newton and the monotonicity test on I_search both evaluate it. A wrong
    # derivative of the right sign would let both pass without supporting their
    # conclusion, and no test compared it with the function it differentiates
    # (2026-09 external audit, D08). F(t) = Fc(cos t) exactly, so
    # F'(t) = -sin t * Fc'(cos t), with Fc' taken exactly from the rational
    # coefficients of Fc_poly() -- an independent route to the same derivative.
    setprecision(BigFloat, 256) do
        Fc = Fc_poly()                                   # ascending: Fc[k+1] is the c^k coefficient
        dFc = [k * Fc[k+1] for k in 1:length(Fc)-1]      # exact derivative, still rational
        ev(p, c) = sum(BigFloat(p[k]) * c^(k-1) for k in eachindex(p))
        for t in (big"0.11", big"0.17", z_nominal, big"0.23", big"0.31")
            c = cos(t)
            @test abs(ev(Fc, c) - Ffun(t)) < big"1e-60"              # F = Fc∘cos
            @test abs(Fprime(t) + sin(t) * ev(dFc, c)) < big"1e-60"   # F' = -sin·Fc'∘cos
        end
    end
end

@testset "failure paths report instead of crashing" begin
    # certify_a16.jl reads the fields of each stage's result to write the
    # certificate. A failed multiplier solve used to return only (pass, reason),
    # so a NOT CERTIFIED run then crashed on `r5.lambda_lower` before the
    # certificate was written (2026-09 external audit, D02). Every stage must
    # return the same fields whether it passes or fails.
    include(joinpath(@__DIR__, "..", "pipeline", "stages", "05_certify_multipliers.jl"))
    quiet(f) = redirect_stdout(f, devnull)
    ok5  = quiet(() -> run_multipliers_interval())
    bad5 = quiet(() -> run_multipliers_interval(radius=big"1e-2"))   # too wide: regularity fails
    @test ok5.pass && !bad5.pass
    @test keys(ok5) == keys(bad5)
    ok2  = quiet(() -> run_root_interval())
    bad2 = quiet(() -> run_root_interval(radii=[big"1e-2"]))         # leaves I_search: rejected
    @test ok2.pass && !bad2.pass
    @test keys(ok2) == keys(bad2)
end
