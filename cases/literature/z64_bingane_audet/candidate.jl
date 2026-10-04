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
    PATH   = [0,31,63,30,61,29,60,28,58,27,57,26,56,25,55,24,54,23,53,21,52,19,51,16]
    ANGLES = [1,2,3,5,6,7,8,10,11,12,13,14,15,16,17,18,19,20,22,23,25,26,29]
    PEND   = [(30,62,4,-1), (28,59,9,-1), (53,22,21,1), (52,20,24,1), (51,18,27,1), (51,17,28,1)]
    active = Tuple{Int,Int}[(0, 31), (0, 32), (0, 33), (1, 33), (1, 34), (2, 34), (3, 34), (3, 35), (4, 35), (4, 36), (5, 36), (6, 36), (6, 37), (7, 37), (7, 38), (8, 38), (8, 39), (9, 39), (9, 40), (10, 40), (10, 41), (11, 41), (11, 42), (11, 43), (12, 43), (12, 44), (12, 45), (13, 45), (13, 46), (13, 47), (13, 48), (14, 49), (14, 50), (15, 50), (16, 51), (17, 51), (18, 51), (19, 51), (19, 52), (20, 52), (21, 52), (21, 53), (22, 53), (23, 53), (23, 54), (24, 54), (24, 55), (25, 55), (25, 56), (26, 56), (26, 57), (27, 57), (27, 58), (28, 58), (28, 59), (28, 60), (29, 60), (29, 61), (30, 61), (30, 62), (30, 63), (31, 63)]

    # The vertices, generic over the number type. S, C: k -> sin(kt), cos(kt);
    # K: Rational -> a constant; y: the y coordinate shared by v14, v15, v49, v50.
    function z64_vertices(S, C, K, y)
        p = Vector{Any}(nothing, n)
        p[1] = (K(0), K(0)); p[33] = (K(0), K(1))
        for (k, ((a, b), m)) in enumerate(zip(zip(PATH, PATH[2:end]), ANGLES))
            sg = isodd(k) ? 1 : -1                              # alternating, starting with +
            p[b+1] = (sg > 0 ? p[a+1][1] + S(m) : p[a+1][1] - S(m),
                      sg > 0 ? p[a+1][2] + C(m) : p[a+1][2] - C(m))
        end
        for (a, b, m, sg) in PEND
            p[b+1] = (sg > 0 ? p[a+1][1] + S(m) : p[a+1][1] - S(m),
                      sg > 0 ? p[a+1][2] + C(m) : p[a+1][2] - C(m))
        end
        for i in 1:n-1                                         # p_{64-i} = (-x_i, y_i)
            q = p[i+1]; q === nothing && continue
            p[n-i+1] === nothing && (p[n-i+1] = (-q[1], q[2]))
        end
        h = K(1//2)
        p[51] = (-h, y); p[15] = (h, y)                        # v50, v14
        p[16] = (-h + C(1), y + S(1)); p[50] = (h - C(1), y + S(1))   # v15, v49
        all(!isnothing, p) || error("Z64: a vertex is undefined")
        return p
    end

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
    function coords(z)
        w = ysolve(z)
        Pv = z64_vertices(w.S, w.C, w.K, w.p0[52][2] + w.r)
        p = Matrix{typeof(z)}(undef, n, 2)
        for i in 1:n; p[i, 1] = Pv[i][1]; p[i, 2] = Pv[i][2]; end
        return p
    end

    # ---- exact identities in Q[c,s,y]/(s^2 + c^2 - 1) ----------------------
    QQ = Rational{BigInt}
    struct Pl; t::Dict{NTuple{3,Int},QQ}; end
    _clean(d) = Pl(Dict(k => v for (k, v) in d if v != 0))
    Pl(v::Integer) = Pl(Dict{NTuple{3,Int},QQ}(v == 0 ? () : ((0, 0, 0) => QQ(v),)))
    Pl(v::Rational) = _clean(Dict{NTuple{3,Int},QQ}((0, 0, 0) => QQ(v)))
    Base.:+(a::Pl, b::Pl) = (d = copy(a.t); for (k, v) in b.t; d[k] = get(d, k, QQ(0)) + v; end; _clean(d))
    Base.:-(a::Pl) = Pl(Dict(k => -v for (k, v) in a.t))
    Base.:-(a::Pl, b::Pl) = a + (-b)
    function Base.:*(a::Pl, b::Pl)
        r = Dict{NTuple{3,Int},QQ}()
        for ((c1, s1, y1), v) in a.t, ((c2, s2, y2), w) in b.t
            k = (c1 + c2, s1 + s2, y1 + y2)
            if k[2] >= 2                                       # s^2 = 1 - c^2, repeatedly
                e = k[2]; base = (k[1], e - 2, k[3])
                r[base] = get(r, base, QQ(0)) + v*w
                base2 = (k[1] + 2, e - 2, k[3])
                r[base2] = get(r, base2, QQ(0)) - v*w
            else
                r[k] = get(r, k, QQ(0)) + v*w
            end
        end
        _clean(r)
    end
    iszero_(a::Pl) = isempty(a.t)
    Base.:(==)(a::Pl, b::Pl) = iszero_(a - b)
    Cx = Pl(Dict{NTuple{3,Int},QQ}((1, 0, 0) => QQ(1)))
    Sx = Pl(Dict{NTuple{3,Int},QQ}((0, 1, 0) => QQ(1)))
    Yx = Pl(Dict{NTuple{3,Int},QQ}((0, 0, 1) => QQ(1)))
    TC = Pl[Pl(1), Cx]; TS = Pl[Pl(0), Sx]
    for k in 2:29
        push!(TC, Pl(2) * Cx * TC[end] - TC[end-1]); push!(TS, Pl(2) * Cx * TS[end] - TS[end-1])
    end
    function exact_statuses()
        S = k -> TS[k+1]; C = k -> TC[k+1]; K = q -> Pl(QQ(q))
        p = z64_vertices(S, C, K, Yx)
        e2 = Pl(2) - Pl(2) * Cx
        sq(i, j) = (p[j+1][1] - p[i+1][1]) * (p[j+1][1] - p[i+1][1]) + (p[j+1][2] - p[i+1][2]) * (p[j+1][2] - p[i+1][2])
        # the two defining equations, written independently of the vertices
        y51 = p[52][2]; a = p[52][1] + Pl(1//2); r = Yx - y51
        E1 = r * r + a * a - e2
        E2 = (a + S(29) - C(1)) * (a + S(29) - C(1)) + (C(29) - S(1) - r) * (C(29) - S(1) - r) - e2
        sides = Symbol[]
        for i in 0:n-1
            f = sq(i, mod(i + 1, n)) - e2
            push!(sides, iszero_(f) ? :UNCONDITIONAL :
                         (i in (13, 50) && f == E1) || (i in (15, 48) && f == E2) ? :PROVED : :UNPROVED)
        end
        diams = [iszero_(sq(i, j) - Pl(1)) ? :UNCONDITIONAL : :UNPROVED for (i, j) in active]
        return sides, diams
    end

    Candidate(
        "z64-bingane-audet", n, coords,
        (F = Ffun, lo = 2*asin(sin(P/n)/2), hi = P/n, nominal = z_nom),
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
