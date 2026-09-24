# Benchmark candidate: n=32, the Bingane–Audet construction A32.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 32-gon.
# Status: OPEN. A32 is the Bingane–Audet construction for n = 2^s, NOT a
#   proven global optimum. This framework certifies its LOCAL first-order
#   structure only. Unlike A16 there is no dedicated module and no Lean layer.
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x.  Constructor: OPTIGON
#   cstrt_audet_ngon(32) (C. Bingane, MIT), via the generic `audet_generic` in
#   cases/exact_coords.jl (cross-checked against upstream in test/literature.jl).
#
# The active graph below is data: the certifier CERTIFIES that every listed
# pair has distance 1 and every other pair distance < 1, it does not trust it.
# The root is unique on the constructor bracket (Sturm count on Fc, tested).

let
    n = 32
    z_nom = big"0.098172109009096166672231870051241111915647126137018093326165865051550675936277"
    P = BigFloat(π)
    # active diameters (i, j), 0-based: n - 1 of them, LICQ defect 1 as for A16
    active = Tuple{Int,Int}[(0, 15), (0, 16), (0, 17), (1, 17), (2, 17), (2, 18), (3, 18), (3, 19), (3, 20), (4, 20), (4, 21), (5, 21), (6, 21), (6, 22), (7, 22), (7, 23), (7, 24), (8, 25), (9, 25), (10, 25), (10, 26), (11, 26), (11, 27), (11, 28), (12, 28), (12, 29), (13, 29), (14, 29), (14, 30), (15, 30), (15, 31)]
    Candidate(
        "A32-bingane-audet", n,
        audet_coords(n),
        (F = audet_F(n), lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 32-gon",
            :status_literature => "OPEN — Bingane–Audet construction, NOT proven optimal",
            :perimeter_ref => "32ℓ ≈ 3.140246",
            :constructor => "OPTIGON cstrt_audet_ngon(32) (MIT) = audet_coords(32)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = audet_cs(n, z_nom)
                EI.prove_all(co, n, active, st, dt, Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
