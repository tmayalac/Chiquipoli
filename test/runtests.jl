using Test
include(joinpath(@__DIR__,"..","src","A16Certificate.jl"))
using .A16Certificate
include(joinpath(@__DIR__,"..","src","ExactIdentity.jl"))
using .ExactIdentity
include(joinpath(@__DIR__,"..","src","SmallPolygons.jl"))
using .SmallPolygons
include(joinpath(@__DIR__,"..","examples","literature","exact_coords.jl"))
include(joinpath(@__DIR__,"optigon_reference.jl"))
using IntervalArithmetic
using LinearAlgebra
using SHA
using Random

# ---- General framework: literature benchmark ------------------------------
# Declared at top level: `const` is not allowed inside the outer testset.
const LITROOT = normpath(joinpath(@__DIR__, "..", "examples", "literature"))
loadcand(rel) = include(joinpath(LITROOT, rel, "candidate.jl"))

# One outer testset, so a failure anywhere does not abort the run. Without it a
# top-level @testset throws when it finishes and every later testset is
# skipped: a broken constructor used to stop the suite after two of twelve.
@testset verbose = true "Chiquipoli" begin

@testset "Static conventions" begin
    @test length(ACTIVE_EDGES) == 15
    @test length(ROWS_MINOR) == 30
    @test length(COLS_MINOR) == 30
    @test OMITTED_COLUMNS == [3,4,17]
end

@testset "Nominal constructor" begin
    setprecision(BigFloat,256)
    z = z_nominal
    p = coordinates(z)
    @test size(p) == (16,2)
    @test p[1,1] == 0
    @test p[1,2] == 0
    @test p[9,1] == 0
    @test p[9,2] == 1
    @test abs(Ffun(z)) < big"1e-25"
    @test abs(Fprime(z)) > big"1e-3"
end

@testset "Jacobian assembly" begin
    z = z_nominal
    A = build_jacobian(z)
    @test size(A) == (31,33)
    rx,ry,rr = rigid_vectors(z)
    @test maximum(abs.(A*rx)) < big"1e-30"
    @test maximum(abs.(A*ry)) < big"1e-30"
    @test maximum(abs.(A*rr)) < big"1e-25"
    @test rigid_annihilation_identities().translations
    @test rigid_annihilation_identities().rotation
end

@testset "Interval smoke tests" begin
    Z = interval(z_nominal-big"1e-28",z_nominal+big"1e-28")
    @test !in_interval(0, Fprime(Z))
    A = build_jacobian(Z)
    @test size(A[ROWS_MINOR,COLS_MINOR]) == (30,30)
    @test size(normalized_matrix(A)) == (31,31)
    @test size(omitted_residual_matrix(Z)) == (3,3)
end

# ---------------------------------------------------------------------------
# The Chebyshev basis and the two copies of the polynomial utilities.
#
# A typo in the T/U recurrence is already caught: inverting one sign there fails
# 39 assertions across four testsets, because the rational coordinate table
# would stop reproducing the trigonometric one. But it is caught downstream, far
# from the cause. These check the basis where it is defined, so a failure names
# the culprit.
#
# `A16Certificate` and `ExactIdentity` each carry their own copy of the rational
# polynomial utilities. They are deliberately independent — the second engine
# was written to be reusable without pulling in the A16 specialisation — but two
# copies can drift apart silently, and every exact identity in the package rests
# on both. The second testset holds them to each other.
# ---------------------------------------------------------------------------
@testset "certify rejects a malformed exact-identity hook" begin
    # `meta[:exact]` is supplied by the candidate, so its output is input to the
    # exact_identities block rather than a result of it, and its shape has to be
    # checked before its content is read. It was not: `all(f, [])` is true in
    # Julia, so a candidate returning two empty vectors was reported
    # ":PROVEN  0 sides + 0 active diameters" with structural_pass true — the
    # strongest label in the report, awarded for proving nothing. A short vector
    # was as bad: two statuses for a 16-gon passed while the other twenty nine
    # equalities went unexamined. No shipped candidate is affected; every one of
    # them returns the right lengths. The framework accepted the wrong ones.
    setprecision(BigFloat, 256)
    BF(x) = interval(BigFloat(x))
    aa = BF(1) / sqrt(BF(2)) / BF(2)
    square = t -> [aa aa; -aa aa; -aa -aa; aa -aa]
    exact_block(r) = r.blocks[findfirst(b -> b.name == "exact_identities", r.blocks)]

    for (why, hook) in [("empty",        sbox -> (Symbol[], Symbol[])),
                        ("too few",      sbox -> ([:PROVED, :PROVED], [:PROVED])),
                        ("too many",     sbox -> (fill(:PROVED, 9), fill(:PROVED, 2))),
                        ("diameters off", sbox -> (fill(:PROVED, 4), fill(:PROVED, 5)))]
        r = certify(Candidate("malformed-" * why, 4, square, nothing, [(0,2), (1,3)],
                              Dict{Symbol,Any}(:exact => hook)))
        @test exact_block(r).status == :FAIL
        @test !structural_pass(r)
    end

    # and a well-formed hook is still accepted
    r = certify(Candidate("well-formed", 4, square, nothing, [(0,2), (1,3)],
                          Dict{Symbol,Any}(:exact => sbox -> (fill(:PROVED, 4),
                                                              fill(:UNCONDITIONAL, 2)))))
    @test exact_block(r).status == :PROVEN
end

@testset "Chebyshev basis against its closed forms" begin
    T, U = chebyshev(12)
    ev(q, x) = (a = 0//1; for i in length(q):-1:1; a = a * x + q[i]; end; a)
    # low orders written out by hand
    @test ptrim(T[0]) == RPoly([1//1])
    @test ptrim(T[1]) == RPoly([0//1, 1//1])
    @test ptrim(T[2]) == RPoly([-1//1, 0//1, 2//1])          # 2c² − 1
    @test ptrim(T[3]) == RPoly([0//1, -3//1, 0//1, 4//1])    # 4c³ − 3c
    @test ptrim(U[0]) == RPoly([1//1])
    @test ptrim(U[1]) == RPoly([0//1, 2//1])                 # 2c
    @test ptrim(U[2]) == RPoly([-1//1, 0//1, 4//1])          # 4c² − 1
    @test ptrim(U[3]) == RPoly([0//1, -4//1, 0//1, 8//1])    # 8c³ − 4c
    # the defining trigonometric identities, at 256 bits
    setprecision(BigFloat, 256)
    for z in (big"0.31", big"1.27", big"2.03", z_nominal)
        c = cos(z); sn = sin(z)
        for k in 0:12
            tk = sum(BigFloat(T[k][i+1]) * c^i for i in 0:length(T[k])-1)
            @test abs(tk - cos(k*z)) < big"1e-60"
            uk = sum(BigFloat(U[k][i+1]) * c^i for i in 0:length(U[k])-1)
            @test abs(sn * uk - sin((k+1)*z)) < big"1e-60"
        end
    end
    # leading coefficients: T_k and U_k are 2^(k-1) and 2^k for k ≥ 1
    for k in 1:12
        @test ptrim(T[k])[end] == Rational{BigInt}(2)^(k-1)
        @test ptrim(U[k])[end] == Rational{BigInt}(2)^k
    end
end

@testset "the two polynomial engines agree" begin
    EI = ExactIdentity
    # A fixed seed on purpose: a randomised failure that cannot be reproduced is
    # worse than no test, and this file is part of a certification pipeline.
    rng = Random.Xoshiro(20260908)
    rnd(n) = RPoly([Rational{BigInt}(rand(rng, -9:9), rand(rng, 1:5)) for _ in 1:n])
    for _ in 1:40
        a = ptrim(rnd(rand(rng, 1:7))); b = ptrim(rnd(rand(rng, 1:7)))
        iszeropoly(b) && continue
        @test ptrim(padd(a, b))          == EI.ptrim(EI.padd(a, b))
        @test ptrim(psub(a, b))          == EI.ptrim(EI.psub(a, b))
        @test ptrim(pmul(a, b))          == EI.ptrim(EI.pmul(a, b))
        @test iszeropoly(a)              == EI.iszeropoly(a)
        qa, ra = pdivrem(a, b); qb, rb = EI.pdivrem(a, b)
        @test ptrim(qa) == EI.ptrim(qb) && ptrim(ra) == EI.ptrim(rb)
        # and the division is exact over Q: a = q*b + r, always
        @test ptrim(padd(pmul(qa, b), ra)) == ptrim(a)
    end
end

@testset "Exact polynomial arithmetic" begin
    a = RPoly([-1//1,0//1,1//1])  # c^2 - 1
    b = RPoly([-1//1,1//1])       # c - 1
    q,r = pdivrem(a,b)
    @test iszeropoly(r)
    @test ptrim(padd(pmul(q,b),r)) == ptrim(a)

    a2 = RPoly([0//1,0//1,1//1])  # c^2
    q2,r2 = pdivrem(a2,b)
    @test !iszeropoly(r2)
end

# The docstring of `_peval` warns against a refactor that would silently stop
# being an enclosure for coefficients past the 256-bit mantissa. This pins down
# that the SHIPPED conversion is outward at exactly that scale, so the warning
# can never quietly become a description of the code.
@testset "coefficient conversion stays an enclosure past the mantissa" begin
    setprecision(BigFloat, 256) do
        for q in (Rational{BigInt}(BigInt(2)^260 + 1, 1),
                  Rational{BigInt}(-(BigInt(2)^300) - 7, 1),
                  Rational{BigInt}(BigInt(2)^260 + 1, BigInt(3)))
            I = interval(BigFloat, q)
            @test inf(I) <= q <= sup(I)          # a true enclosure
            @test isguaranteed(I)
        end
        # Horner over such coefficients inherits the property.
        big = RPoly([Rational{BigInt}(BigInt(2)^260 + 1, 1), 1//1])
        v = ExactIdentity._peval(big, interval(BigFloat, 1//1))
        @test inf(v) <= (BigInt(2)^260 + 2) <= sup(v)
        # ...and the banned refactor really does fail, which is why it is banned.
        n = BigInt(2)^260 + 1
        bad = interval(BigFloat(n)) / interval(BigFloat(BigInt(1)))
        @test !(inf(bad) <= n <= sup(bad))
    end
end

@testset "Exact side and diameter identities" begin
    for i in 0:15
        j = mod(i+1,16)
        cert = exact_identity_certificate(i, j, side_target_poly())
        @test cert.proved
        @test cert.reconstruction_ok
    end
    for (i,j) in ACTIVE_EDGES
        cert = exact_identity_certificate(i, j, diameter_target_poly())
        @test cert.proved
        @test cert.reconstruction_ok
    end
    # Discrimination check: an inactive pair must NOT be exactly a diameter.
    inactive_sample = [(4,12),(0,4),(1,10),(2,13)]
    for (i,j) in inactive_sample
        cert = exact_identity_certificate(i, j, diameter_target_poly())
        @test !cert.proved
    end
end

@testset "Numeric and exact constructors agree" begin
    # src/A16Certificate.jl transcribes the constructor TWICE: once
    # trigonometrically (Xfun/Yfun, used by every interval gate) and once as
    # rational polynomials (_XC/_YC, used by all the exact algebra). Nothing
    # used to check that the two agree, so breaking one left the other proving
    # 31 identities about a different polygon.
    setprecision(BigFloat, 256)
    XC, YC = A16Certificate._XC, A16Certificate._YC
    horner(q, x) = (a = zero(x); for i in length(q):-1:1; a = a * x + BigFloat(q[i]); end; a)
    z = z_nominal; c = cos(z); s = sin(z); P = coordinates(z)
    @test length(XC) == 16 && length(YC) == 16
    for k in 0:15
        # vertex k is (sin z * XC_k(cos z), YC_k(cos z))
        @test abs(s * horner(XC[k+1], c) - P[k+1, 1]) < big"1e-70"
        @test abs(horner(YC[k+1], c) - P[k+1, 2]) < big"1e-70"
    end
end

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
    include(joinpath(@__DIR__, "..", "scripts", "02_root_interval.jl"))
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
    # run_all.jl reads the fields of each stage's result to write the
    # certificate. A failed multiplier solve used to return only (pass, reason),
    # so a NOT CERTIFIED run then crashed on `r5.lambda_lower` before the
    # certificate was written (2026-09 external audit, D02). Every stage must
    # return the same fields whether it passes or fails.
    include(joinpath(@__DIR__, "..", "scripts", "05_multipliers_interval.jl"))
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

@testset "Literature positive cases certify (local first-order structure)" begin
    for d in ("n4_regular", "n6_reinhardt", "n8_ahmp2004", "A16_bingane_audet")
        cand = loadcand(d)
        r = certify(cand; radius = cand.root === nothing ? big"0" : big"1e-24")
        @test structural_pass(r)
        @test !any(b.status == :FAIL for b in r.blocks)
        # Interval consistency is not certified equality (audit D11): the
        # equilaterality block is :CONSISTENT, the equality itself :PROVEN.
        st = Dict(b.name => b.status for b in r.blocks)
        @test st["equilaterality"] == :CONSISTENT
        @test st["exact_identities"] == :PROVEN
    end
    # `certify` works at its own precision and leaves the caller's alone (D12).
    cand = loadcand("n4_regular")
    setprecision(BigFloat, 128) do
        certify(cand; radius=big"0")
        @test precision(BigFloat) == 128
    end
end

@testset "Literature negative controls are rejected" begin
    for d in ("negative/broken_convexity", "negative/broken_equilateral", "negative/wrong_diameter")
        cand = loadcand(d)
        r = certify(cand)
        @test any(b.status == :FAIL for b in r.blocks)     # rejection is non-vacuous
    end
end

@testset "n=8 H8 cross-check vs AHMP-2004 degree-6 polynomial" begin
    setprecision(BigFloat, 256)
    # side² u of the vincze/H8 constructor must root the Bingane-Audet §2 poly.
    z = big"0.3894068706089136310254731821232088177802669267863906566356996889936525347787489"
    u = (2*sin(z/2))^2
    poly = 2u^6 - 18u^5 + 57u^4 - 78u^3 + 46u^2 - 12u + 1
    @test abs(poly) < big"1e-70"
    @test sin(BigFloat(π)/8)^2 < u < 4*sin(BigFloat(π)/16)^2

    # ------------------------------------------------------------------
    # Identification of the certified n = 8 configuration with the AHMP
    # optimum (referee point R4). The general path certifies that a root of
    # the constructor equation exists in the box, by a sign change; it does
    # not certify that the root is unique, nor that the box brackets *the*
    # published optimum rather than a nearby branch. The check above says u
    # roots the AHMP sextic and lies in the interval AHMP names, which is
    # necessary but not sufficient: a second root of that sextic in the same
    # interval would leave the identification open.
    #
    # A Sturm sequence settles it exactly. Everything below is
    # `Rational{BigInt}`: no floating point and no interval arithmetic enters
    # the root count, so it is a proof and not an enclosure.
    Rp(v) = RPoly([Rational{BigInt}(x) for x in v])
    dpoly(q::RPoly) = length(q) <= 1 ? RPoly([0//1]) : ptrim([q[k+1]*k for k in 1:length(q)-1])
    function gcdpoly(x::RPoly, y::RPoly)
        x = ptrim(copy(x)); y = ptrim(copy(y))
        while !iszeropoly(y); x, y = y, last(pdivrem(x, y)); end
        return x
    end
    function sturm(q::RPoly)
        ch = [ptrim(q), dpoly(q)]
        while !iszeropoly(ch[end])
            _, r = pdivrem(ch[end-1], ch[end])
            iszeropoly(r) && break
            push!(ch, pscale(r, -1//1))
        end
        return ch
    end
    ev(q::RPoly, x::Rational) = (v = Rational{BigInt}(0); for c in reverse(q); v = v*x + c; end; v)
    function changes(ch, x)
        sg = filter(!iszero, [sign(ev(q, x)) for q in ch])
        return count(i -> sg[i] != sg[i+1], 1:length(sg)-1)
    end
    nroots(ch, a, b) = changes(ch, a) - changes(ch, b)

    sextic = Rp([1, -12, 46, -78, 57, -18, 2])          # 1 −12u +46u² −78u³ +57u⁴ −18u⁵ +2u⁶
    gg = gcdpoly(sextic, dpoly(sextic))
    @test length(gg) == 1 && !iszeropoly(gg)             # squarefree: Sturm applies

    # Rational endpoints straddling the interval AHMP names, so the count over
    # [lo, hi] bounds the count over the AHMP interval from above.
    lo = Rational{BigInt}(146, 1000)
    hi = Rational{BigInt}(153, 1000)
    piI = interval(BigFloat, π)
    @test inf(sin(piI/interval(BigFloat, 8))^2) > big"0.146"          # lo < sin²(π/8)
    @test sup(interval(BigFloat, 4)*sin(piI/interval(BigFloat, 16))^2) < big"0.153"  # 4sin²(π/16) < hi

    ch = sturm(sextic)
    # Non-vacuity: the sextic really does have several real roots, so a count
    # of one over [lo, hi] is a discrimination and not an artefact of a chain
    # that returns one everywhere.
    @test nroots(ch, Rational{BigInt}(-10), Rational{BigInt}(10)) == 4
    @test nroots(ch, Rational{BigInt}(0), Rational{BigInt}(1)) == 1
    @test nroots(ch, lo, hi) == 1                        # exactly one root in [lo, hi]
    @test big"0.146" < u <= big"0.153"                   # and u is in there
    # Hence u is the unique root of the AHMP sextic in the published interval,
    # so the certified configuration is the AHMP optimum and not a branch of it.
end

@testset "R1+R2 general: certified multipliers and PROVEN exact identities" begin
    for d in ("n4_regular", "n6_reinhardt", "n8_ahmp2004", "A16_bingane_audet")
        cand = loadcand(d)
        r = certify(cand; radius = cand.root === nothing ? big"0" : big"1e-24")
        mult = findfirst(b -> b.name == "multipliers", r.blocks)
        exact = findfirst(b -> b.name == "exact_identities", r.blocks)
        @test mult !== nothing && r.blocks[mult].status == :CERTIFIED   # R1
        @test exact !== nothing && r.blocks[exact].status == :PROVEN     # R2
    end
end

@testset "Proposition 1: constructor-derived Fc equals the AHMP sextic (exact)" begin
    # Vincze reduced constructor G + s H = 0; norm Fc = G^2 - (1-c^2)H^2 must
    # equal the Bingane-Audet sec.2 sextic in u = 2-2c, as exact polynomials.
    Rp = Vector{Rational{BigInt}}
    pm(a,b) = (r=zeros(Rational{BigInt},length(a)+length(b)-1); for i in eachindex(a),j in eachindex(b); r[i+j-1]+=a[i]*b[j]; end; r)
    ps(a,b) = [(i<=length(a) ? a[i] : 0//1)-(i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b))]
    pa(a,b) = [(i<=length(a) ? a[i] : 0//1)+(i<=length(b) ? b[i] : 0//1) for i in 1:max(length(a),length(b))]
    G = Rp([1,-4,-4,8]); H = Rp([0,-8,8])
    Fc_norm = ps(pm(G,G), pm(Rp([1,0,-1]), pm(H,H)))
    u = Rp([2,-2]); up = Dict(0=>Rp([1])); for k in 1:6; up[k]=pm(up[k-1],u); end
    sextic = pa(pa(pa(pa(pa(pa((2//1).*up[6],(-18//1).*up[5]),(57//1).*up[4]),(-78//1).*up[3]),(46//1).*up[2]),(-12//1).*up[1]),Rp([1]))
    strip(v) = (n=length(v); while n>1 && v[n]==0; n-=1; end; v[1:n])
    @test strip(Fc_norm) == strip(sextic)
end

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

# ---------------------------------------------------------------------------
# Identification of the certified object with the published one (referee R5).
#
# Everything this package certifies is certified about
# `A16Certificate.coordinates`, an n = 16 specialisation written out by hand.
# That leaves one question a referee is entitled to press: is the object being
# certified really the published A16, or a transcription of it that drifted?
# These tests answer it by running the GENERAL n = 2^s OPTIGON constructor,
# transcribed line for line from upstream (see test/optigon_reference.jl for
# provenance, upstream SHA256 and the two deliberate deviations), and requiring
# it to reproduce the specialisation.
# ---------------------------------------------------------------------------
@testset "A16 is the published Bingane-Audet polygon (OPTIGON cross-check)" begin
    setprecision(BigFloat, 256)
    n = 16
    z_ref, a_ref, b_ref = optigon_audet_ngon(n, BigFloat)

    # Bisection converges to the root of the same F, so the agreement is limited
    # by the bracket halving, not by any difference in the formulas.
    @test abs(z_ref - z_nominal) < big"1e-35"

    # The general constructor returns n-1 vertices with the remaining one at the
    # origin, which is where the specialisation puts vertex 0.
    p_ref = vcat([(zero(BigFloat), zero(BigFloat))],
                 [(a_ref[i], b_ref[i]) for i in 1:n-1])
    q = coordinates(z_nominal)
    @test length(p_ref) == n
    for i in 1:n
        @test abs(p_ref[i][1] - q[i, 1]) < big"1e-35"
        @test abs(p_ref[i][2] - q[i, 2]) < big"1e-35"
    end

    # The structural data the certificate depends on must also be reproduced by
    # the upstream construction, not merely by our reading of it.
    dist(u, v) = sqrt((u[1] - v[1])^2 + (u[2] - v[2])^2)
    sides = [dist(p_ref[i], p_ref[mod(i, n) + 1]) for i in 1:n]
    @test maximum(sides) - minimum(sides) < big"1e-35"          # equilateral
    pairs = [(i - 1, j - 1, dist(p_ref[i], p_ref[j])) for i in 1:n for j in (i+1):n]
    act = Set((i, j) for (i, j, d) in pairs if abs(d - 1) < big"1e-30")
    @test act == Set(ACTIVE_EDGES)                              # same diameter graph
    @test maximum(d for (_, _, d) in pairs if abs(d - 1) >= big"1e-30") < 1
    @test abs(n * sides[1] - big"3.13528788808861636639373682812225770037") < big"1e-30"

    # Guard the vendored transcription against upstream drift. The file
    # test/optigon_reference.jl is a hand transcription, so "it reproduces the
    # specialisation" is evidence about its output, not about its fidelity to
    # the source. The upstream file is therefore stored verbatim beside it and
    # its hash checked here, so a reader can diff the two and see for
    # themselves what was transcribed and what was changed.
    upstream = joinpath(@__DIR__, "optigon_upstream_cstrt_audet_ngon.jl.txt")
    @test isfile(upstream)
    @test bytes2hex(SHA.sha256(read(upstream))) ==
          "376e838b87009f749c19dbee0407419f3c58b30021c406a952a01671aaf6d0ff"
    # and the three formulas the specialisation rests on are present verbatim
    up = read(upstream, String)
    @test occursin("x(t) = sin(t)-(2*cos(t)-1)*cos((n/4-2)*t)*sin(n*t/4)/cos(2*t)", up)
    @test occursin("F(t) = (2*x(t)+sin((n/2-1)*t))^2 + cos((n/2-1)*t)^2 - 4*sin(t/2)^2", up)
    @test occursin("find_zero(F,(2*asin(sin(pi/n)/2),pi/n))", up)

    # Guard the transcription itself: n = 16 is the case where the general
    # formulas collapse onto the specialisation, because
    # cos((n/4-2)t)*sin(n*t/4)/cos(2*t) = cos(2t)*sin(4t)/cos(2t) = sin(4t).
    # If that collapse ever stopped holding, the test above would still pass at
    # the root while the two functions differed elsewhere, so check it away from
    # the root as well.
    for t in (big"0.11", big"0.17", big"0.23")
        xgen = sin(t) - (2*cos(t) - 1) * cos(2*t) * sin(4*t) / cos(2*t)
        @test abs(xgen - Xfun(t)) < big"1e-70"
        Fgen = (2*xgen + sin(7*t))^2 + cos(7*t)^2 - 4*sin(t/2)^2
        @test abs(Fgen - Ffun(t)) < big"1e-70"
    end
end

end  # @testset "Chiquipoli"
