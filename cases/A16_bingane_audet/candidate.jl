# Benchmark candidate: n=16, the Bingane–Audet A16 hexadecagon.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 16-gon.
# Status: OPEN. A16 is the best known construction (beats Mossinghoff's M16),
#   but is NOT a proven global optimum. This framework certifies its LOCAL
#   first-order structure only; the dedicated `A16Certificate` module provides
#   the full exact-identity + interval-multiplier certificate for A16.
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x.  Constructor: OPTIGON
#   cstrt_audet_ngon(16) (C. Bingane, MIT), identical to A16Certificate.coordinates.

let
    lo, hi = A16Certificate.search_bounds(BigFloat)
    Candidate(
        "A16-bingane-audet", 16,
        A16Certificate.coordinates,             # coords(z), interval-compatible
        (F = A16Certificate.Ffun, lo = lo, hi = hi,
         nominal = A16Certificate.z_nominal),
        A16Certificate.ACTIVE_EDGES,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 16-gon",
            :status_literature => "OPEN — best known construction, NOT proven optimal",
            :perimeter_ref => "16ℓ ≈ 3.135288",
            :constructor => "OPTIGON cstrt_audet_ngon(16) (MIT) = A16Certificate.coordinates",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = a16_cs()
                EI.prove_all(co, 16, A16Certificate.ACTIVE_EDGES, st, dt, Fc,
                             sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
