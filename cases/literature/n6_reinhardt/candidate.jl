# Benchmark candidate: n=6, the Reinhardt hexagon R_{3,6}.
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 6-gon.
# Result: R_{3,6} is the UNIQUE optimum (n=6 has odd factor m=3, prime, n/m=2),
#   ℓ*₆ = L₆ = 12 sin(π/12) ≈ 3.105829. PROVEN theorem (Reinhardt 1922), NOT
#   proven by this framework. Coordinates are exact closed forms (algebraic),
#   enclosed by interval trigonometry.
#
# Reference: K. Reinhardt, "Extremale Polygone gegebenen Durchmessers",
#   Jahresber. DMV 31 (1922) 251–270.  Construction: OPTIGON
#   cstrt_reinhardt_ngon(3,2) (C. Bingane, MIT).

let
    # Exact integer literals as guaranteed thin intervals. Mixing a bare `Real`
    # into an interval expression is sound when the value is exactly
    # representable, as every literal below is, but IntervalArithmetic then
    # clears its `isguaranteed` flag on the result and the engine can no longer
    # vouch for the enclosure without a hand audit. Routing them through `II`
    # keeps the flag live; the enclosures are bit-for-bit unchanged.
    II(k::Integer) = interval(BigFloat, k)
    coords = function (t)
        P = interval(BigFloat, π)
        den = II(2)*cos(P/II(6))
        a2 = sin(II(2)*P/II(3))/den;    b2 = (one(P) - cos(II(2)*P/II(3)))/den
        a4 = sin(II(4)*P/II(3))/den;    b4 = (one(P) - cos(II(4)*P/II(3)))/den
        a3 = cos(P/II(2));              b3 = sin(P/II(2))       # = (0, 1)
        a5 = a2 + cos(II(7)*P/II(6));   b5 = b2 + sin(II(7)*P/II(6))
        a1 = -a5;                       b1 = b5
        z = interval(big"0.0")
        # rows = vertices p0..p5
        return [z z; a1 b1; a2 b2; a3 b3; a4 b4; a5 b5]
    end
    Candidate(
        "n6-reinhardt-R36", 6, coords, nothing,
        [(0,2), (0,3), (0,4), (1,4), (2,4), (2,5)],
        Dict{Symbol,Any}(
            :reference => "Reinhardt 1922, Jahresber. DMV 31:251–270",
            :doi => "(pre-DOI)",
            :problem => "equilateral max-perimeter small 6-gon",
            :status_literature => "PROVEN global optimum (theorem); unique",
            :perimeter_ref => "12 sin(π/12) ≈ 3.105829",
            :constructor => "OPTIGON cstrt_reinhardt_ngon(3,2) (MIT)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = reinhardt36_cs()
                EI.prove_all(co, 6, [(0,2),(0,3),(0,4),(1,4),(2,4),(2,5)], st, dt, Fc,
                             sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
