# Benchmark candidate: n=128, the Bingane–Audet construction A128.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 128-gon.
# Status: OPEN. A128 is the Bingane–Audet construction for n = 2^s, NOT a
#   proven global optimum. This framework certifies its LOCAL first-order
#   structure only (pipeline/certify_family.jl 128, make a128).
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x.  Constructor: OPTIGON
#   cstrt_audet_ngon(128) (C. Bingane, MIT), via the generic `audet_generic` in
#   cases/exact_coords.jl (cross-checked against upstream in test/literature.jl).
#
# The active graph below is data: the certifier CERTIFIES that every listed
# pair has distance 1 and every other pair distance < 1, it does not trust it.
# It is the graph G_n of Ayala Hoffmann's closed form (`gn_edges`, checked in
# test/literature.jl). The root literal is the zero of F to ~100 digits (mpmath);
# the certificate encloses the root by interval Newton and proves it is the
# only zero on the constructor bracket (0 ∉ Fc' there).

let
    n = 128
    z_nom = big"0.02454368983776405442344793422385910631924574176544704781982326465776680252314246220919175739707931708"
    P = BigFloat(π)
    # active diameters (i, j), 0-based: n - 1 of them, LICQ defect 1 as for A16
    active = Tuple{Int,Int}[(0, 63), (0, 64), (0, 65), (1, 65), (2, 65), (2, 66), (3, 66), (3, 67), (3, 68), (4, 68), (4, 69), (5, 69), (6, 69), (6, 70), (7, 70), (7, 71), (7, 72), (8, 72), (8, 73), (9, 73), (10, 73), (10, 74), (11, 74), (11, 75), (11, 76), (12, 76), (12, 77), (13, 77), (14, 77), (14, 78), (15, 78), (15, 79), (15, 80), (16, 80), (16, 81), (17, 81), (18, 81), (18, 82), (19, 82), (19, 83), (19, 84), (20, 84), (20, 85), (21, 85), (22, 85), (22, 86), (23, 86), (23, 87), (23, 88), (24, 88), (24, 89), (25, 89), (26, 89), (26, 90), (27, 90), (27, 91), (27, 92), (28, 92), (28, 93), (29, 93), (30, 93), (30, 94), (31, 94), (31, 95), (31, 96), (32, 97), (33, 97), (34, 97), (34, 98), (35, 98), (35, 99), (35, 100), (36, 100), (36, 101), (37, 101), (38, 101), (38, 102), (39, 102), (39, 103), (39, 104), (40, 104), (40, 105), (41, 105), (42, 105), (42, 106), (43, 106), (43, 107), (43, 108), (44, 108), (44, 109), (45, 109), (46, 109), (46, 110), (47, 110), (47, 111), (47, 112), (48, 112), (48, 113), (49, 113), (50, 113), (50, 114), (51, 114), (51, 115), (51, 116), (52, 116), (52, 117), (53, 117), (54, 117), (54, 118), (55, 118), (55, 119), (55, 120), (56, 120), (56, 121), (57, 121), (58, 121), (58, 122), (59, 122), (59, 123), (59, 124), (60, 124), (60, 125), (61, 125), (62, 125), (62, 126), (63, 126), (63, 127)]
    Candidate(
        "A128-bingane-audet", n,
        audet_coords(n),
        (F = audet_F(n), lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 128-gon",
            :status_literature => "OPEN — Bingane–Audet construction, NOT proven optimal",
            :perimeter_ref => "128ℓ ≈ 3.14151344681",
            :constructor => "OPTIGON cstrt_audet_ngon(128) (MIT) = audet_coords(128)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = audet_cs(n, z_nom)
                EI.prove_all(co, n, active, st, dt, Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
