# The literature benchmark (n = 4, 6, 8, 16, 32, 64) and its negative controls.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

@testset "Literature positive cases certify (local first-order structure)" begin
    for d in ("n4_regular", "n6_reinhardt", "n8_ahmp2004", "A16_bingane_audet",
              "A32_bingane_audet", "A64_bingane_audet")
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
    for d in ("n4_regular", "n6_reinhardt", "n8_ahmp2004", "A16_bingane_audet",
              "A32_bingane_audet", "A64_bingane_audet")
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

@testset "Bingane–Audet family n = 16, 32, 64 (generic constructor)" begin
    setprecision(BigFloat, 256)
    R = Vector{Rational{BigInt}}
    maxerr(p, q) = maximum(abs(p[i][k] - q[i][k]) for i in eachindex(p), k in 1:2)
    csval(e, z) = (c = cos(z); s = sin(z); pv(p) = (v = zero(z); for k in length(p):-1:1; v = v*c + p[k]; end; v);
                   (pv(e.A) + s*pv(e.B)) / pv(e.den))

    # (1) The generic constructor IS the upstream one: interval and exact
    # instances against the verbatim OPTIGON transcription, for every n.
    for n in (16, 32, 64)
        z, ua, ub = optigon_audet_ngon(n, BigFloat)
        up = vcat([(big"0", big"0")], [(ua[i], ub[i]) for i in 1:n-1])
        pI = audet_coords(n)(interval(z))
        @test maxerr([(mid(pI[i,1]), mid(pI[i,2])) for i in 1:n], up) < big"1e-70"
        pcs = audet_coords_cs(n)
        @test maxerr([(csval(x, z), csval(y, z)) for (x, y) in pcs], up) < big"1e-60"
    end

    # (2) At n = 16 it reproduces the hand-written A16 module: coordinates and Fc.
    p16 = audet_coords(16)(interval(z_nominal))
    a16 = A16Certificate.coordinates(interval(z_nominal))
    @test all(mag(p16[i,k] - a16[i,k]) < big"1e-70" for i in 1:16, k in 1:2)
    Fc16, _ = audet_Fc(16)
    off = R(Fc_poly()); @test Fc16 == off ./ off[end]

    # (3) The structural pattern, observed (not proved) on the three members:
    # n-1 active diameters, LICQ defect 1, deg Fc = n-4, and exactly two of the
    # 2n-1 equalities need the root of Fc; the rest hold for every θ.
    for (n, d) in ((32, "A32_bingane_audet"), (64, "A64_bingane_audet"))
        cand = loadcand(d)
        @test length(cand.active) == n - 1
        @test n + length(cand.active) - (2n - 2) == 1
        Fc, den = audet_Fc(n)
        @test length(Fc) - 1 == n - 4
        (co, _, st, dt, zb) = audet_cs(n, cand.root.nominal)
        sides, diams = EI.prove_all(co, n, cand.active, st, dt, Fc, zb)
        all_st = vcat(sides, diams)
        @test count(==(:PROVED), all_st) == 2
        @test count(==(:UNCONDITIONAL), all_st) == 2n - 3
    end

    # (4) Uniqueness of the constructor root on its bracket, exactly (Sturm),
    # as for n = 8. z in (lo, hi) = (2 asin(sin(π/n)/2), π/n) maps injectively
    # to c = cos z in (cos hi, cos lo) ⊂ [a, b]; there den ≠ 0, so F(z) = 0
    # forces Fc(c) = 0. One root of Fc in [a, b] ⇒ at most one root of F on the
    # bracket, and the certified sign change supplies it.
    dp(q) = length(q) <= 1 ? RPoly([0//1]) : ptrim([q[k+1]*k for k in 1:length(q)-1])
    function sturmchain(q)
        ch = [ptrim(q), dp(q)]
        while !iszeropoly(ch[end])
            _, r = pdivrem(ch[end-1], ch[end]); iszeropoly(r) && break
            push!(ch, pscale(r, -1//1))
        end
        return ch
    end
    ev(q, x) = (v = Rational{BigInt}(0); for c in reverse(q); v = v*x + c; end; v)
    chg(ch, x) = (sg = filter(!iszero, [sign(ev(q, x)) for q in ch]); count(i -> sg[i] != sg[i+1], 1:length(sg)-1))
    nr(ch, a, b) = chg(ch, a) - chg(ch, b)
    piI = interval(BigFloat, π)
    for (n, a, b, total) in ((16, 196157//200000, 98097//100000, 9),
                             (32, 62199//62500, 995197//1000000, 19),
                             (64, 199759//200000, 998797//1000000, 37))
        a = Rational{BigInt}(a); b = Rational{BigInt}(b)
        nI = interval(BigFloat, n)
        @test inf(cos(piI/nI)) > a                                        # a < cos(π/n)
        @test sup(cos(interval(BigFloat, 2)*asin(sin(piI/nI)/interval(BigFloat, 2)))) < b   # cos(lo) < b
        Fc, den = audet_Fc(n)
        @test length(EI.pgcd(Fc, dp(Fc))) == 1                            # squarefree: Sturm applies
        cI = hull(interval(BigFloat, a), interval(BigFloat, b))
        @test !in_interval(0, EI._peval(den, cI))                          # den ≠ 0 on [a, b]
        ch = sturmchain(Fc)
        @test nr(ch, Rational{BigInt}(-1), Rational{BigInt}(1)) == total  # non-vacuity: many real roots
        @test nr(ch, a, b) == 1                                           # exactly one in [a, b]
    end

    # (5) Planted errors on A32 are rejected, so its PASS is not vacuous.
    cand = loadcand("A32_bingane_audet")
    function variant(; active = cand.active, coords = cand.coords, Fc = first(audet_Fc(32)))
        co = audet_coords_cs(32)
        Candidate(cand.name, 32, coords, cand.root, active,
            Dict{Symbol,Any}(:exact => sb -> EI.prove_all(co, 32, active, R([2,-2]), R([1]), Fc, sb)))
    end
    rej(c) = any(b.status == :FAIL for b in certify(c; radius = big"1e-24").blocks)
    @test !rej(variant())                                                  # the control passes
    @test rej(variant(Fc = EI.padd(first(audet_Fc(32)), R([1]))))         # wrong Fc
    @test rej(variant(active = vcat(cand.active, [(8, 24)])))              # spurious diameter
    @test rej(variant(coords = z -> (p = cand.coords(z); p[6,1] += interval(big"1e-20"); p)))  # moved vertex
end
