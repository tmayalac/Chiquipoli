# =============================================================================
# Faithful transcription of the upstream OPTIGON constructor, used ONLY as an
# independent reference for the A16 identification test.
#
#   Upstream file : cstrt_ngon/cstrt_audet_ngon.jl
#   Repository    : https://github.com/cbingane/optigon  (C. Bingane)
#   Raw URL       : https://raw.githubusercontent.com/cbingane/optigon/
#                   master/cstrt_ngon/cstrt_audet_ngon.jl
#   Retrieved     : 2026-09-08
#   Upstream size : 2681 bytes
#   Upstream SHA256: 376e838b87009f749c19dbee0407419f3c58b30021c406a952a01671aaf6d0ff
#   Licence       : MIT, Copyright (c) 2020 Christian Bingane
#   Cites         : C. Bingane and C. Audet, Tight bounds on the maximal
#                   perimeter of convex equilateral small polygons,
#                   Archiv der Mathematik 119 (2022), 325--336
#                   (preprint arXiv:2105.10618).
#
# WHY THIS FILE EXISTS. `A16Certificate.coordinates` is an n = 16
# specialisation, written out by hand. Everything this package certifies is
# certified about *that* function, so a referee is entitled to ask whether the
# object certified is really the published A16 or a transcription of it that
# drifted. This file answers that by construction: it is the general n = 2^s
# constructor, transcribed line for line from upstream, and the test in
# `runtests.jl` requires it to reproduce the specialisation.
#
# THE ONLY DEVIATIONS FROM UPSTREAM, both deliberate and both inert:
#   1. `find_zero` (Roots.jl) is replaced by plain bisection on the same
#      bracket `(2*asin(sin(pi/n)/2), pi/n)`, so that no dependency is added to
#      Project.toml and the pinned Manifest stays untouched. Bisection on a
#      bracket with a sign change converges to a root of the same F.
#   2. The element type is a parameter, so the reference can be evaluated in
#      BigFloat and compared against a 256-bit specialisation rather than at
#      Float64 noise level.
# The formulas themselves are byte-comparable with the upstream source.
#
# NOT part of the certificate. Nothing in `src/` depends on this file, and no
# gate of `certify_a16.jl` consults it. It supports one test: the identification of
# the certified configuration with the published one.
# =============================================================================

"Bisection on a bracket with a certified sign change; replaces `find_zero`."
function _optigon_bisect(F, lo, hi; iters = 400)
    flo = F(lo)
    @assert flo * F(hi) < 0 "no sign change on the constructor bracket"
    for _ in 1:iters
        m = (lo + hi) / 2
        fm = F(m)
        if flo * fm <= 0
            hi = m
        else
            lo = m
            flo = fm
        end
    end
    return (lo + hi) / 2
end

"""
    optigon_audet_ngon(n, T=Float64) -> (z, a, b)

Vertex coordinates `(a, b)` of a convex equilateral small `n`-gon for
`n = 2^s`, `s >= 4`, and the constructor root `z`. Vertices are returned
exactly as upstream: `n-1` entries, with the remaining vertex at the origin.
"""
function optigon_audet_ngon(n::Int, T = Float64)
    (mod(log2(n), 1) == 0 && n >= 16) ||
        throw(DomainError(n, "n must be a power of 2 >= 16"))
    x(t) = sin(t) - (2 * cos(t) - 1) * cos((n / 4 - 2) * t) * sin(n * t / 4) / cos(2 * t)
    F(t) = (2 * x(t) + sin((n / 2 - 1) * t))^2 + cos((n / 2 - 1) * t)^2 - 4 * sin(t / 2)^2
    pi_ = T(pi)
    z = _optigon_bisect(F, 2 * asin(sin(pi_ / n) / 2), pi_ / n)

    a = zeros(T, n - 1)
    b = zeros(T, n - 1)
    a[Int(n / 2 - 1)] = sin(z);              a[Int(n / 2 + 1)] = -a[Int(n / 2 - 1)]
    b[Int(n / 2 - 1)] = cos(z);              b[Int(n / 2 + 1)] =  b[Int(n / 2 - 1)]
    a[n - 1] = a[Int(n / 2 - 1)] - sin(2 * z);  a[1] = -a[n - 1]
    b[n - 1] = b[Int(n / 2 - 1)] - cos(2 * z);  b[1] =  b[n - 1]
    a[n - 2] = a[Int(n / 2 - 1)] - sin(3 * z);  a[2] = -a[n - 2]
    b[n - 2] = b[Int(n / 2 - 1)] - cos(3 * z);  b[2] =  b[n - 2]

    for i = 1:Int(n / 8 - 1)
        j1 = Int(mod(n / 2 - 1 + i * (3 * n / 2 - 2), n))
        j2 = Int(mod(n - 1     + i * (3 * n / 2 - 2), n))
        j3 = Int(mod(n - 2     + i * (3 * n / 2 - 2), n))
        j4 = Int(mod(n         + i * (3 * n / 2 - 2), n))
        a[j1] = sin(z) - (2 * cos(z) - 1) * sin(i * (2 * z - pi_ / 2)) *
                sin((i + 1) * (2 * z - pi_ / 2)) / cos(2 * z);   a[n - j1] = -a[j1]
        b[j1] = cos(z) - (2 * cos(z) - 1) * sin(i * (2 * z - pi_ / 2)) *
                cos((i + 1) * (2 * z - pi_ / 2)) / cos(2 * z);   b[n - j1] =  b[j1]
        a[j2] = a[j1] - (-1)^i * sin((4 * i + 2) * z);           a[n - j2] = -a[j2]
        b[j2] = b[j1] - (-1)^i * cos((4 * i + 2) * z);           b[n - j2] =  b[j2]
        a[j3] = a[j1] - (-1)^i * sin((4 * i + 3) * z);           a[n - j3] = -a[j3]
        b[j3] = b[j1] - (-1)^i * cos((4 * i + 3) * z);           b[n - j3] =  b[j3]
        a[j4] = a[j1] - (-1)^i * sin((4 * i + 1) * z);           a[n - j4] = -a[j4]
        b[j4] = b[j1] - (-1)^i * cos((4 * i + 1) * z);           b[n - j4] =  b[j4]
    end
    a[Int(n / 2)] = 0
    b[Int(n / 2)] = 1
    return z, a, b
end
