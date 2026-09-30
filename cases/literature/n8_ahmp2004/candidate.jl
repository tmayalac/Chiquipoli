# Benchmark candidate: n=8, the optimal equilateral octagon H8 (AHMP 2004).
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 8-gon
#   (equivalently, minimum-diameter octagon with unit-length sides).
# Result: H8 is the UNIQUE optimum, ℓ*₈ ≈ 3.095609. PROVEN theorem
#   (Audet–Hansen–Messine–Perron 2004), NOT proven by this framework.
#   Its squared side length u is the unique root of
#   2u⁶−18u⁵+57u⁴−78u³+46u²−12u+1 = 0 in (sin²(π/8), 4sin²(π/16))
#   (Bingane–Audet 2022, §2) — cross-checked in the tests.
#
# References: C. Audet, P. Hansen, F. Messine, S. Perron, "The minimum
#   diameter octagon with unit-length sides: Vincze's wife's octagon is
#   suboptimal", JCTA 108(1) (2004) 63–75, DOI 10.1016/j.jcta.2004.06.009.
#   Constructor: OPTIGON cstrt_vincze_ngon(8) (C. Bingane, MIT).

let
    # Root of the constructor's defining equation F(t)=0 (interval-evaluable).
    # Exact integer literals as guaranteed thin intervals. Mixing a bare `Real`
    # into an interval expression is sound when the value is exactly
    # representable, as every literal below is, but IntervalArithmetic then
    # clears its `isguaranteed` flag on the result and the engine can no longer
    # vouch for the enclosure without a hand audit. Routing them through `II`
    # keeps the flag live; the enclosures are bit-for-bit unchanged.
    II(k::Integer) = interval(BigFloat, k)

    Ffun = function (t)
        (cos(t)^2 + sin(II(2)*t)^2 - II(2)*cos(t)*sin(II(2)*t)^2) /
            (II(2)*cos(t)^2*(one(t) + sin(II(2)*t))) - II(4)*sin(t/II(2))^2
    end
    z_nom = big"0.3894068706089136310254731821232088177802669267863906566356996889936525347787489"
    P = BigFloat(π)
    lo = 2*asin(sin(P/8)/2); hi = P/8

    coords = function (z)          # z = interval box around the root
        n = 8
        a = fill(zero(z), n-1); b = fill(zero(z), n-1)
        # loop i = 1 : n/4-1  (single iteration for n=8)
        idx = mod(1*(n÷2-1), n)                    # = 3
        a[idx] = sin(II(2)*z)/II(2)/cos(z)
        a[n-idx] = -a[idx]
        b[idx] = (one(z) + cos(II(2)*z))/II(2)/cos(z)
        b[n-idx] = b[idx]
        # "seam" vertex
        k1 = mod((n÷4)*(n÷2-1), n) + 1             # = 7
        kp = mod((n÷4-1)*(n÷2-1), n)               # = 3
        # (-1)^(n÷4-1) = -1 for n=8; written out so no bare Int meets an interval
        a[k1] = a[kp] - sin(II(2)*z)               # a[3] - sin(2z)
        a[n-k1] = -a[k1]
        b[k1] = b[kp] - cos(II(2)*z)
        b[n-k1] = b[k1]
        # side vertices at x = ±1/2
        a[n÷4] = interval(big(1)//2); a[3*(n÷4)] = -a[n÷4]
        b[n÷4] = (II(2)*cos(z) - cos(z)*(cos(z) - sin(z))) / (II(2)*cos(z)*(cos(z) + sin(z)))
        b[3*(n÷4)] = b[n÷4]
        p = Matrix{typeof(a[1])}(undef, n, 2)
        p[1,1] = zero(z); p[1,2] = zero(z)
        for i in 1:n-1; p[i+1,1] = a[i]; p[i+1,2] = b[i]; end
        p[n÷2+1,1] = zero(z); p[n÷2+1,2] = interval(big"1.0")   # apex p4 = (0,1)
        return p
    end

    Candidate(
        "n8-ahmp2004-H8", 8, coords,
        (F = Ffun, lo = lo, hi = hi, nominal = z_nom),
        [(0,3), (0,4), (0,5), (1,5), (2,6), (3,7)],
        Dict{Symbol,Any}(
            :reference => "Audet–Hansen–Messine–Perron 2004, JCTA 108(1):63–75",
            :doi => "10.1016/j.jcta.2004.06.009",
            :problem => "equilateral max-perimeter small 8-gon (H8)",
            :status_literature => "PROVEN global optimum (theorem); unique",
            :perimeter_ref => "8ℓ ≈ 3.095609; side² root of degree-6 poly (Bingane–Audet §2)",
            :constructor => "OPTIGON cstrt_vincze_ngon(8) (MIT)",
            :exact => (sbox) -> begin
                (co, Fc, st, dt, zb) = vincze8_cs()
                EI.prove_all(co, 8, [(0,3),(0,4),(0,5),(1,5),(2,6),(3,7)], st, dt, Fc,
                             sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
