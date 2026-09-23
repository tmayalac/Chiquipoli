# Benchmark candidate: n=4, the regular square.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 4-gon.
# Result: the regular square is the UNIQUE optimum (equilateral case);
#   ℓ*₄ = L(R₄) = 2√2 ≈ 2.828427. This is a PROVEN theorem (Vincze 1950),
#   NOT proven by this framework — the framework only re-certifies the local
#   structure. Coordinates are exact rationals (diamond with diagonals = 1).
#
# Reference: S. Vincze, "On a geometrical extremum problem", Acta Sci. Math.
#   (Szeged) 12 (1950) 136–142.  Construction: OPTIGON cstrt_regular_ngon(4)
#   (C. Bingane, MIT license), here as exact rational coordinates.

let
    coords = function (t)
        h = interval(big"0.5"); o = interval(big"1.0"); z = interval(big"0.0")
        # p0=(0,0) p1=(1/2,1/2) p2=(0,1) p3=(-1/2,1/2)  (counter-clockwise)
        return [z z; h h; z o; -h h]
    end
    Candidate(
        "n4-regular-square", 4, coords, nothing,
        [(0,2), (1,3)],                         # the two diagonals
        Dict{Symbol,Any}(
            :reference => "Vincze 1950, Acta Sci. Math. (Szeged) 12:136–142",
            :doi => "(pre-DOI)",
            :problem => "equilateral max-perimeter small 4-gon",
            :status_literature => "PROVEN global optimum (theorem); unique",
            :perimeter_ref => "2√2 ≈ 2.828427",
            :constructor => "OPTIGON cstrt_regular_ngon(4) (MIT); exact rationals",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = regular_cs(4)
                EI.prove_all(co, 4, [(0,2),(1,3)], st, dt, Fc,
                             sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
