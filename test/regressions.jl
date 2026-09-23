# Regression tests for defects found by audits.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

# ---------------------------------------------------------------------------
# Rigor regressions. Each of these locks in a defect found by a line-by-line
# audit of the interval/algebra layer; each one FAILED before its fix.
# ---------------------------------------------------------------------------
@testset "Rigor regressions" begin
    setprecision(BigFloat, 256)
    Zc = interval(z_nominal - big"1e-28", z_nominal + big"1e-28")
    A  = build_jacobian(Zc)

    # (1) IntervalArithmetic's own NG flag must stay live across the whole
    # dedicated certificate. It was cleared everywhere by bare integer
    # literals meeting intervals (`2cos(t)`, `sin(4t)`, `Interval{BigFloat}(16)`,
    # `Matrix{Interval}(I,n,n)`), so IA could not vouch for a single quantity.
    @test isguaranteed(Ffun(Zc))
    @test isguaranteed(Fprime(Zc))
    @test isguaranteed(side_length(Zc))
    @test all(isguaranteed, coordinates(Zc))
    @test all(isguaranteed, A)
    @test all(isguaranteed, [v for (_,_,v) in support_determinants(Zc)])
    @test all(isguaranteed, [v for (_,_,v) in inactive_pairs(Zc)])
    @test isguaranteed(objective_covector(eltype(A))[33])
    @test all(isguaranteed, normalized_matrix(A))
    @test all(isguaranteed, omitted_residual_matrix(Zc))
    # and the gate itself must actually reject an NG value
    @test_throws ErrorException assert_guaranteed(2 * Zc, "deliberately NG")

    # (2) The Krawczyk enclosure must be built with OUTWARD rounding. Forming
    # the endpoints as `x0[i] + inf(K[i])` in BigFloat rounds to nearest and
    # returned a box up to an ulp NARROWER than the certified set, so the
    # reported interval was not guaranteed to contain the solution.
    M = normalized_matrix(A)
    g = objective_covector(eltype(A))
    onefifth = interval(BigFloat(1//5, RoundDown), BigFloat(1//5, RoundUp))
    sol = krawczyk_linear(M, vcat(g[COLS_MINOR], onefifth))
    @test sol.pass
    @test all(isguaranteed, sol.enclosure)
    # Sharp check: rebuild the certified set x0 + K(X) from the returned
    # operator and compare endpoint by endpoint. A tolerance test cannot see
    # this — the defect was ~1e-77 wide — so the reported box is compared
    # against the outward-rounded truth directly. Under the old
    # round-to-nearest construction 22 of these 31 assertions failed.
    Xr = [interval(-sol.radius, sol.radius) for _ in 1:31]
    Kx = sol.residual + sol.operator * Xr
    @test all(inf(sol.enclosure[i]) <= inf(sol.x0[i] + Kx[i]) &&
              sup(sol.enclosure[i]) >= sup(sol.x0[i] + Kx[i]) for i in 1:31)
    @test all(inf(sol.enclosure[i]) < sup(sol.enclosure[i]) for i in 1:31)

    # (3) The paper normalises by the exact rational lambda_{0,9} = 1/5.
    # `interval(big"0.2")` is a thin interval at fl(1/5), which is not 1/5.
    @test inf(onefifth) <= big"0.2" <= sup(onefifth)
    @test Rational{BigInt}(inf(onefifth)) <= 1//5 <= Rational{BigInt}(sup(onefifth))

    # (4) SmallPolygons.build_jacobian must use each constraint's OWN length.
    # It divided every side row by side 0's length, so on a non-equilateral
    # input the rows were not gradients of anything (off by 0.3 here) while the
    # module still reported rank and multipliers as CERTIFIED.
    BF = x -> interval(BigFloat(x))
    q = [BF(0) BF(0); BF(1) BF(0); BF(13)/BF(10) BF(1); BF(0) BF(1)]
    ell0 = sqrt((q[2,1]-q[1,1])^2 + (q[2,2]-q[1,2])^2)
    J = SmallPolygons.build_jacobian(q, 4, Tuple{Int,Int}[], ell0)
    for i in 0:3
        j = mod(i+1, 4)
        dx = q[j+1,1]-q[i+1,1]; dy = q[j+1,2]-q[i+1,2]; d = sqrt(dx^2 + dy^2)
        @test interval_abs_bound(J[i+1, 2j+1] - dx/d) < big"1e-70"
        @test interval_abs_bound(J[i+1, 2j+2] - dy/d) < big"1e-70"
    end

    # (5) general_multipliers must refuse, not throw, when there are fewer than
    # 2n-2 constraints (it handed a non-square matrix to `inv`).
    n10 = 10
    act = [(0,5),(0,6),(1,6),(1,7),(2,7),(2,8),(3,8)]      # d = 7-10+2 = -1
    pts = vcat([[BF(cos(2*pi*k/n10)) BF(sin(2*pi*k/n10))] for k in 0:n10-1]...)
    e10 = sqrt((pts[2,1]-pts[1,1])^2 + (pts[2,2]-pts[1,2])^2)
    mc = SmallPolygons.general_multipliers(pts, n10, act, e10)
    @test mc.pass == false
    @test occursin("underdetermined", mc.reason)

    # (6) ExactIdentity._peval must convert rational coefficients OUTWARD.
    # `interval(BigFloat(numerator(q)))` rounds a BigInt to nearest and then
    # asserts it as exact, returning a THIN interval at the wrong value once
    # the integer passes the 256-bit mantissa.
    big_c = Rational{BigInt}(BigInt(2)^300 + 1, 1)
    enc = ExactIdentity._peval(ExactIdentity.RPoly([big_c]), interval(big"0.0"))
    @test Rational{BigInt}(inf(enc)) <= big_c <= Rational{BigInt}(sup(enc))
    @test inf(enc) < sup(enc)          # genuinely widened, not a thin lie
end
