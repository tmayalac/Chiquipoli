# Benchmark candidate: n=256, the Bingane–Audet construction A256.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 256-gon.
# Status: OPEN. A256 is the Bingane–Audet construction for n = 2^s, NOT a
#   proven global optimum. This framework certifies its LOCAL first-order
#   structure only (pipeline/certify_family.jl 256, make a256).
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x.  Constructor: OPTIGON
#   cstrt_audet_ngon(256) (C. Bingane, MIT), via the generic `audet_generic` in
#   cases/exact_coords.jl (cross-checked against upstream in test/literature.jl).
#
# The active graph below is data: the certifier CERTIFIES that every listed
# pair has distance 1 and every other pair distance < 1, it does not trust it.
# It is the graph G_n of Ayala Hoffmann's closed form (`gn_edges`, checked in
# test/literature.jl). The root literal is the zero of F to ~100 digits (mpmath);
# the certificate encloses the root by interval Newton and proves it is the
# only zero on the constructor bracket (0 ∉ Fc' there).

let
    n = 256
    z_nom = big"0.01227184621555529382975781092779596353733518503510407249292873167469797993568993635655705688009564562"
    P = BigFloat(π)
    # active diameters (i, j), 0-based: n - 1 of them, LICQ defect 1 as for A16
    active = Tuple{Int,Int}[(0, 127), (0, 128), (0, 129), (1, 129), (2, 129), (2, 130), (3, 130), (3, 131), (3, 132), (4, 132), (4, 133), (5, 133), (6, 133), (6, 134), (7, 134), (7, 135), (7, 136), (8, 136), (8, 137), (9, 137), (10, 137), (10, 138), (11, 138), (11, 139), (11, 140), (12, 140), (12, 141), (13, 141), (14, 141), (14, 142), (15, 142), (15, 143), (15, 144), (16, 144), (16, 145), (17, 145), (18, 145), (18, 146), (19, 146), (19, 147), (19, 148), (20, 148), (20, 149), (21, 149), (22, 149), (22, 150), (23, 150), (23, 151), (23, 152), (24, 152), (24, 153), (25, 153), (26, 153), (26, 154), (27, 154), (27, 155), (27, 156), (28, 156), (28, 157), (29, 157), (30, 157), (30, 158), (31, 158), (31, 159), (31, 160), (32, 160), (32, 161), (33, 161), (34, 161), (34, 162), (35, 162), (35, 163), (35, 164), (36, 164), (36, 165), (37, 165), (38, 165), (38, 166), (39, 166), (39, 167), (39, 168), (40, 168), (40, 169), (41, 169), (42, 169), (42, 170), (43, 170), (43, 171), (43, 172), (44, 172), (44, 173), (45, 173), (46, 173), (46, 174), (47, 174), (47, 175), (47, 176), (48, 176), (48, 177), (49, 177), (50, 177), (50, 178), (51, 178), (51, 179), (51, 180), (52, 180), (52, 181), (53, 181), (54, 181), (54, 182), (55, 182), (55, 183), (55, 184), (56, 184), (56, 185), (57, 185), (58, 185), (58, 186), (59, 186), (59, 187), (59, 188), (60, 188), (60, 189), (61, 189), (62, 189), (62, 190), (63, 190), (63, 191), (63, 192), (64, 193), (65, 193), (66, 193), (66, 194), (67, 194), (67, 195), (67, 196), (68, 196), (68, 197), (69, 197), (70, 197), (70, 198), (71, 198), (71, 199), (71, 200), (72, 200), (72, 201), (73, 201), (74, 201), (74, 202), (75, 202), (75, 203), (75, 204), (76, 204), (76, 205), (77, 205), (78, 205), (78, 206), (79, 206), (79, 207), (79, 208), (80, 208), (80, 209), (81, 209), (82, 209), (82, 210), (83, 210), (83, 211), (83, 212), (84, 212), (84, 213), (85, 213), (86, 213), (86, 214), (87, 214), (87, 215), (87, 216), (88, 216), (88, 217), (89, 217), (90, 217), (90, 218), (91, 218), (91, 219), (91, 220), (92, 220), (92, 221), (93, 221), (94, 221), (94, 222), (95, 222), (95, 223), (95, 224), (96, 224), (96, 225), (97, 225), (98, 225), (98, 226), (99, 226), (99, 227), (99, 228), (100, 228), (100, 229), (101, 229), (102, 229), (102, 230), (103, 230), (103, 231), (103, 232), (104, 232), (104, 233), (105, 233), (106, 233), (106, 234), (107, 234), (107, 235), (107, 236), (108, 236), (108, 237), (109, 237), (110, 237), (110, 238), (111, 238), (111, 239), (111, 240), (112, 240), (112, 241), (113, 241), (114, 241), (114, 242), (115, 242), (115, 243), (115, 244), (116, 244), (116, 245), (117, 245), (118, 245), (118, 246), (119, 246), (119, 247), (119, 248), (120, 248), (120, 249), (121, 249), (122, 249), (122, 250), (123, 250), (123, 251), (123, 252), (124, 252), (124, 253), (125, 253), (126, 253), (126, 254), (127, 254), (127, 255)]
    Candidate(
        "A256-bingane-audet", n,
        audet_coords(n),
        (F = audet_F(n), lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 256-gon",
            :status_literature => "OPEN — Bingane–Audet construction, NOT proven optimal",
            :perimeter_ref => "256ℓ ≈ 3.14157291796",
            :constructor => "OPTIGON cstrt_audet_ngon(256) (MIT) = audet_coords(256)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = audet_cs(n, z_nom)
                EI.prove_all(co, n, active, st, dt, Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
