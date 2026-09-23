# A16 is the published Bingane-Audet polygon: the OPTIGON cross-check.
# Included by runtests.jl inside the outer "Chiquipoli" testset; run the
# whole suite with `make test` (a file on its own lacks the shared setup).

# ---------------------------------------------------------------------------
# Identification of the certified object with the published one (referee R5).
#
# Everything this package certifies is certified about
# `A16Certificate.coordinates`, an n = 16 specialisation written out by hand.
# That leaves one question a referee is entitled to press: is the object being
# certified really the published A16, or a transcription of it that drifted?
# These tests answer it by running the GENERAL n = 2^s OPTIGON constructor,
# transcribed line for line from upstream (see test/fixtures/optigon_reference.jl for
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
    # test/fixtures/optigon_reference.jl is a hand transcription, so "it reproduces the
    # specialisation" is evidence about its output, not about its fidelity to
    # the source. The upstream file is therefore stored verbatim beside it and
    # its hash checked here, so a reader can diff the two and see for
    # themselves what was transcribed and what was changed.
    upstream = joinpath(@__DIR__, "fixtures", "optigon_upstream_cstrt_audet_ngon.jl.txt")
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
