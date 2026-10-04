# Benchmark candidate: n=32, the Bingane–Audet polygon Z32 (Proposition 1).
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 32-gon.
# Status: OPEN. Z32 is the 32-gon of larger perimeter that Bingane and Audet
#   report (3.14032023… against 3.14024609… for A32); it is NOT a proven global
#   optimum. This framework certifies its LOCAL first-order structure only, with
#   the same blocks as every other candidate. It is not a family member of the
#   dedicated pipeline (no published constructor file to compare it with, no Lean).
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x, Proposition 1.
#
# WHERE THE CONSTRUCTION COMES FROM. Not from OPTIGON (it ships only the A_n
# constructor): the vertices are rebuilt from the diameter path, the pendant
# edges and the reflection that Proposition 1 states, with t the root of
#     F32(t) = [2(S5 - S13 + S14) - S15]^2 + C15^2 - (2 - 2 cos t) = 0,
# S_k = sin(kt), C_k = cos(kt). A wrong index would not go unnoticed (the sides
# and the diameters are then proved unequal, exactly), but whether this is the
# polygon of the paper is a comparison with the paper, not something a program
# can decide; `pipeline/independent/verify.py` rebuilds it a second time, in
# another language, as a cross-check of the transcription.
#
# The active graph is data: the certifier CERTIFIES that every listed pair has
# distance 1 and every other pair distance < 1, it does not trust it.

let
    n = 32
    z_nom = big"0.09817442866964279340015033600268088794110681753796823552990663472282577"
    P = BigFloat(π)
    # active diameters (i, j), 0-based: n - 1 of them, LICQ defect 1 (as for A_n)
    active = Tuple{Int,Int}[(0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (0, 20), (0, 21), (1, 21), (2, 21), (3, 21), (4, 21), (5, 21), (6, 21), (7, 21), (8, 21), (8, 22), (9, 22), (10, 23), (10, 24), (11, 24), (11, 25), (11, 26), (11, 27), (11, 28), (11, 29), (11, 30), (11, 31)]

    # Generic over the arithmetic, as audet_generic in cases/exact_coords.jl.
    function z32_generic(S, C, K, ops)
        add, sub, mul, dvd, neg = ops
        p = Vector{Any}(nothing, 32)
        p[1] = (K(0), K(0)); p[17] = (K(0), K(1))              # p_0, p_16
        for k in 1:5;  p[16-k+1] = (S(k), C(k)); end           # p_{16-k}, k = 1..5
        for k in 6:13; p[37-k+1] = (sub(p[12][1], S(k)), sub(p[12][2], C(k))); end   # p_{37-k} = p_11 - (S_k, C_k)
        p[11] = (add(p[25][1], S(14)), add(p[25][2], C(14)))   # p_10 = p_24 + (S_14, C_14)
        p[24] = (sub(p[11][1], S(15)), sub(p[11][2], C(15)))   # p_23 = p_10 - (S_15, C_15)
        for i in 1:31                                          # p_{32-i} = (-x_i, y_i)
            q = p[i+1]; q === nothing && continue
            p[32-i+1] === nothing && (p[32-i+1] = (neg(q[1]), q[2]))
        end
        all(!isnothing, p) || error("Z32: a vertex is undefined")
        return p
    end
    function z32_F(S, C, K, ops)
        add, sub, mul, dvd, neg = ops
        x = add(sub(S(5), S(13)), S(14))
        u = sub(mul(K(2), x), S(15))
        return sub(add(mul(u, u), mul(C(15), C(15))), sub(K(2), mul(K(2), C(1))))
    end
    II(k) = interval(BigFloat, k)
    ops = (+, -, *, /, -)
    coords = function (z)
        Pv = z32_generic(k -> sin(II(k)*z), k -> cos(II(k)*z), q -> II(q) + zero(z), ops)
        p = Matrix{typeof(z)}(undef, n, 2)
        for i in 1:n; p[i, 1] = Pv[i][1]; p[i, 2] = Pv[i][2]; end
        return p
    end
    Ffun = z -> z32_F(k -> sin(II(k)*z), k -> cos(II(k)*z), q -> II(q) + zero(z), ops)

    Candidate(
        "z32-bingane-audet", n, coords,
        (F = Ffun, lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336, Proposition 1",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 32-gon (Z32)",
            :status_literature => "OPEN — Bingane–Audet polygon of larger perimeter than A32, NOT proven optimal",
            :perimeter_ref => "32ℓ ≈ 3.140320",
            :constructor => "rebuilt from Proposition 1 (path, pendant edges, reflection); cross-checked in pipeline/independent/verify.py",
            :exact => (sbox) -> begin
                cops = (csadd, cssub, csmul, csdiv, csneg)
                co = z32_generic(cs_sin, cs_cos, cs_const, cops)
                F = z32_F(cs_sin, cs_cos, cs_const, cops)
                EI.iszeropoly(F.B) || error("Z32: F has an s-part")
                Fc = _R(F.A ./ F.A[end])
                zb = interval(z_nom - big"1e-30", z_nom + big"1e-30")
                EI.prove_all(co, n, active, _R([2,-2]), _R([1]), Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
