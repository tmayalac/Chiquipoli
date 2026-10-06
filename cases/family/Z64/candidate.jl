# Benchmark candidate: n=64, the Bingane–Audet polygon Z64 (Proposition 2).
#
# Problem: maximal-perimeter convex EQUILATERAL small (diameter-1) 64-gon.
# Status: OPEN. Z64 is the 64-gon of larger perimeter that Bingane and Audet
#   report (3.14127521… against 3.14127170… for A64); it is NOT a proven global
#   optimum. This framework certifies its LOCAL first-order structure only.
#
# Reference: C. Bingane, C. Audet, "Tight bounds on the maximal perimeter of
#   convex equilateral small polygons", Archiv der Mathematik 119 (2022)
#   325–336, DOI 10.1007/s00013-022-01745-x, Proposition 2.
#
# TWO UNKNOWNS, ONE ROOT. The paper chooses t and y so that two sides equal
# 2 sin(t/2). The first equation is solved for y in closed form: with
# a = x51 + 1/2, y = y51 + sqrt(2 - 2 cos t - a^2) (the branch of the paper's
# figure), so the polygon depends on t alone and the second equation becomes
#     H64(t) = [a + S29 - C1]^2 + [C29 - S1 - r]^2 - (2 - 2 cos t) = 0,
# r = sqrt(2 - 2 cos t - a^2), S_k = sin(kt), C_k = cos(kt): a single root,
# like every other candidate. Where the radicand is not positive on the whole
# evaluation box, r is the entire line and every certificate fails (see ysolve).
#
# WHERE THE CONSTRUCTION COMES FROM. Not from OPTIGON (it ships only the A_n
# constructor): from the half-path, the pendant edges and the reflection that
# Proposition 2 states. The paper gives no angle for the pendant edges; here
# they are the multiples of t that make each pendant edge a diameter, and the
# exact identities below prove that they do (every one of the 62 declared
# diameters is identically 1). pipeline/independent/verify.py rebuilds the
# polygon a second time, in another language.
#
# EXACT IDENTITIES in Q[c,s,y]/(s^2+c^2-1), y an indeterminate (the engine of
# src/ExactIdentity.jl has no square roots, so this candidate carries its own
# small ring): the 62 diameters are identically 1; 60 sides are identically
# ell^2; the other four are the two defining equations, EXACTLY, as polynomials
# in (c, s, y): E1 = (y - y51)^2 + a^2 - ell^2 (sides 13 and 50) and E2 = the
# second equation with r replaced by y - y51 (sides 15 and 48). They vanish at
# the polygon because y - y51 = r by construction, and E2 is then H64(t),
# whose zero the existence block certifies.

let
    n = 64
    z_nom = big"0.0490873533992997825741651747179742568747317119485661903"
    P = BigFloat(π)
    # PATH, ANGLES, PEND and the vertex builder z64_vertices are in cases/exact_coords.jl
    # (Z64_PATH, ...), the one source shared with the exact certifier and the Lean generator.
    active = Tuple{Int,Int}[(0, 31), (0, 32), (0, 33), (1, 33), (1, 34), (2, 34), (3, 34), (3, 35), (4, 35), (4, 36), (5, 36), (6, 36), (6, 37), (7, 37), (7, 38), (8, 38), (8, 39), (9, 39), (9, 40), (10, 40), (10, 41), (11, 41), (11, 42), (11, 43), (12, 43), (12, 44), (12, 45), (13, 45), (13, 46), (13, 47), (13, 48), (14, 49), (14, 50), (15, 50), (16, 51), (17, 51), (18, 51), (19, 51), (19, 52), (20, 52), (21, 52), (21, 53), (22, 53), (23, 53), (23, 54), (24, 54), (24, 55), (25, 55), (25, 56), (26, 56), (26, 57), (27, 57), (27, 58), (28, 58), (28, 59), (28, 60), (29, 60), (29, 61), (30, 61), (30, 62), (30, 63), (31, 63)]

    II(k) = interval(BigFloat, k)
    # y and the second equation, from t alone (interval instance)
    function ysolve(z)
        S = k -> sin(II(k)*z); C = k -> cos(II(k)*z); K = q -> II(numerator(q)) / II(denominator(q)) + zero(z)
        p0 = z64_vertices(S, C, K, K(0))
        a = p0[52][1] + K(1//2)                                # x51 + 1/2
        e2 = II(2) - II(2)*cos(z)
        rad = e2 - a*a
        # Where the radicand is not positive on the whole box, r is the entire
        # line, not a clipped square root: every certificate that needs r then
        # fails, which is the right verdict for a polygon that does not exist there.
        r = inf(rad) > 0 ? sqrt(rad) : interval(-floatmax(BigFloat), floatmax(BigFloat))
        return (S = S, C = C, K = K, p0 = p0, a = a, e2 = e2, r = r)
    end
    function Ffun(z)
        w = ysolve(z)
        return (w.a + w.S(29) - w.C(1))^2 + (w.C(29) - w.S(1) - w.r)^2 - w.e2
    end
    # H64'(t): the vertices differentiated through the same builder (sin kt ->
    # k cos kt, cos kt -> -k sin kt, constants -> 0), r' = (e2' - 2 a a')/(2 r).
    # Only defined where the radicand is positive on the box. Checked against a
    # finite difference in test/literature.jl.
    function Fprime(z)
        w = ysolve(z)
        dS = k -> II(k)*cos(II(k)*z); dC = k -> -II(k)*sin(II(k)*z); K0 = q -> zero(z)
        da = z64_vertices(dS, dC, K0, K0(0))[52][1]            # x51', the same for a
        de2 = II(2)*sin(z)
        dr = (de2 - II(2)*w.a*da) / (II(2)*w.r)
        return II(2)*(w.a + w.S(29) - w.C(1))*(da + dS(29) - dC(1)) +
               II(2)*(w.C(29) - w.S(1) - w.r)*(dC(29) - dS(1) - dr) - de2
    end
    # The equation over a box B for the root-uniqueness search of certify_z.jl: nothing
    # where the radicand is negative on all of B (no polygon exists there), else an
    # enclosure with the square root taken of the non-negative part of the radicand.
    # Sound for the search, which only discards boxes: a zero of the equation at a
    # t in B at which the polygon exists has r in [0, sqrt(sup rad)].
    function Fsearch(B)
        S = k -> sin(II(k)*B); C = k -> cos(II(k)*B); K = q -> II(numerator(q)) / II(denominator(q)) + zero(B)
        p0 = z64_vertices(S, C, K, K(0))
        a = p0[52][1] + K(1//2)
        e2 = II(2) - II(2)*cos(B)
        rad = e2 - a*a
        sup(rad) < 0 && return nothing
        r = sqrt(interval(max(inf(rad), zero(inf(rad))), sup(rad)))
        return (a + S(29) - C(1))^2 + (C(29) - S(1) - r)^2 - e2
    end
    function coords(z)
        w = ysolve(z)
        Pv = z64_vertices(w.S, w.C, w.K, w.p0[52][2] + w.r)
        p = Matrix{typeof(z)}(undef, n, 2)
        for i in 1:n; p[i, 1] = Pv[i][1]; p[i, 2] = Pv[i][2]; end
        return p
    end

    # ---- exact identities in Q[c,s,y]/(s^2 + c^2 - 1): the ring Z64Poly and the
    # polynomial vertices are in cases/exact_coords.jl ----
    function exact_statuses()
        p = z64_poly_vertices()
        (; E1, E2, e2) = z64_equations()
        sq(i, j) = (p[j+1][1] - p[i+1][1]) * (p[j+1][1] - p[i+1][1]) + (p[j+1][2] - p[i+1][2]) * (p[j+1][2] - p[i+1][2])
        sides = Symbol[]
        for i in 0:n-1
            f = sq(i, mod(i + 1, n)) - e2
            push!(sides, z64_iszero(f) ? :UNCONDITIONAL :
                         (i in (13, 50) && f == E1) || (i in (15, 48) && f == E2) ? :PROVED : :UNPROVED)
        end
        diams = [z64_iszero(sq(i, j) - Z64Poly(1)) ? :UNCONDITIONAL : :UNPROVED for (i, j) in active]
        return sides, diams
    end

    Candidate(
        "z64-bingane-audet", n, coords,
        (F = Ffun, Fp = Fprime, Fs = Fsearch, lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
        active,
        Dict{Symbol,Any}(
            :reference => "Bingane & Audet 2022, Archiv der Math. 119:325–336, Proposition 2",
            :doi => "10.1007/s00013-022-01745-x",
            :problem => "equilateral max-perimeter small 64-gon (Z64)",
            :status_literature => "OPEN — Bingane–Audet polygon of larger perimeter than A64, NOT proven optimal",
            :perimeter_ref => "64ℓ ≈ 3.141275",
            :constructor => "rebuilt from Proposition 2 (half-path, pendant edges, reflection); y solved from the first equation; cross-checked in pipeline/independent/verify.py",
            :exact_ring => "Q[c,s,y]",
            :exact => (sbox) -> exact_statuses(),
        ),
    )
end
