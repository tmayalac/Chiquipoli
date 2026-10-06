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

    # z32_generic and z32_F_generic (generic over the arithmetic, as audet_generic)
    # are in cases/exact_coords.jl, the one source shared with the exact certifier
    # and the Lean generator.
    II(k) = interval(BigFloat, k)
    ops = (+, -, *, /, -)
    coords = function (z)
        Pv = z32_generic(k -> sin(II(k)*z), k -> cos(II(k)*z), q -> II(q) + zero(z), ops)
        p = Matrix{typeof(z)}(undef, n, 2)
        for i in 1:n; p[i, 1] = Pv[i][1]; p[i, 2] = Pv[i][2]; end
        return p
    end
    Ffun = z -> z32_F_generic(k -> sin(II(k)*z), k -> cos(II(k)*z), q -> II(q) + zero(z), ops)
    # F32'(t) = 2 u u' - 30 C15 S15 - 2 S1, with u = 2(S5 - S13 + S14) - S15 and
    # u' = 2(5 C5 - 13 C13 + 14 C14) - 15 C15. Checked against a finite difference in
    # test/literature.jl; the interval Newton step of pipeline/certify_z.jl uses it.
    Fprime = function (z)
        S = k -> sin(II(k)*z); C = k -> cos(II(k)*z)
        u  = II(2)*(S(5) - S(13) + S(14)) - S(15)
        du = II(2)*(II(5)*C(5) - II(13)*C(13) + II(14)*C(14)) - II(15)*C(15)
        return II(2)*u*du - II(30)*C(15)*S(15) - II(2)*S(1)
    end

    Candidate(
        "z32-bingane-audet", n, coords,
        (F = Ffun, Fp = Fprime, Fs = Ffun, lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
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
                Fc = z32_Fc()
                zb = interval(z_nom - big"1e-30", z_nom + big"1e-30")
                EI.prove_all(co, n, active, _R([2,-2]), _R([1]), Fc, sbox === nothing ? zb : sbox)
            end,
        ),
    )
end
