# Benchmark candidate: n=64, the Bingane–Audet construction A64.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 64-gon.
# Status: OPEN. A64 is the Bingane–Audet construction for n = 2^s, NOT a
#   proven global optimum. This framework certifies its LOCAL first-order
#   structure only. Unlike A16 there is no dedicated module and no Lean layer.
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x.  Constructor: OPTIGON
#   cstrt_audet_ngon(64) (C. Bingane, MIT), via the generic `audet_generic` in
#   cases/exact_coords.jl (cross-checked against upstream in test/literature.jl).
#
# The active graph below is data: the certifier CERTIFIES that every listed
# pair has distance 1 and every other pair distance < 1, it does not trust it.
# The root is unique on the constructor bracket (Sturm count on Fc, tested).

let
    n = 64
    z_nom = big"0.049087298576449606088149765227582243555280577721423375580429659981221722708967"
    P = BigFloat(π)
    # active diameters (i, j), 0-based: n - 1 of them, LICQ defect 1 as for A16
    active = Tuple{Int,Int}[(0, 31), (0, 32), (0, 33), (1, 33), (2, 33), (2, 34), (3, 34), (3, 35), (3, 36), (4, 36), (4, 37), (5, 37), (6, 37), (6, 38), (7, 38), (7, 39), (7, 40), (8, 40), (8, 41), (9, 41), (10, 41), (10, 42), (11, 42), (11, 43), (11, 44), (12, 44), (12, 45), (13, 45), (14, 45), (14, 46), (15, 46), (15, 47), (15, 48), (16, 49), (17, 49), (18, 49), (18, 50), (19, 50), (19, 51), (19, 52), (20, 52), (20, 53), (21, 53), (22, 53), (22, 54), (23, 54), (23, 55), (23, 56), (24, 56), (24, 57), (25, 57), (26, 57), (26, 58), (27, 58), (27, 59), (27, 60), (28, 60), (28, 61), (29, 61), (30, 61), (30, 62), (31, 62), (31, 63)]
    Candidate(
        "A64-bingane-audet", n,
        audet_coords(n),
        (F = audet_F(n), lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 64-gon",
            :status_literature => "OPEN — Bingane–Audet construction, NOT proven optimal",
            :perimeter_ref => "64ℓ ≈ 3.141201",
            :constructor => "OPTIGON cstrt_audet_ngon(64) (MIT) = audet_coords(64)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = audet_cs(n, z_nom)
                EI.prove_all(co, n, active, st, dt, Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
