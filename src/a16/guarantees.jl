# Keeping IntervalArithmetic's `isguaranteed` flag live: exact literals in the
# arithmetic type of their argument (`_lit`), and the gate that enforces the flag.
#
# Part of module A16Certificate (src/A16Certificate.jl), which includes this
# file; it is not meant to be loaded on its own.

"""
    _lit(x, k)

The exact integer `k` rendered in the arithmetic type of `x`. For an interval
element type this returns a *guaranteed* thin interval.

Why this exists. Mixing a bare `Real` into an interval expression (`2cos(t)`,
`sin(4t)`, ...) is arithmetically sound whenever the bare value is exactly
representable, as every literal in this file is: IntervalArithmetic converts it
to a thin interval and the operation is still outward rounded. But IA
conservatively clears its `isguaranteed` flag on any such mix, because in
general the bare value might itself be a rounded approximation of what the
author meant (the classic `0.1` trap). The consequence was that essentially
every quantity in this certificate carried the NG ("not guaranteed") tag, so
IA's own audit flag was uninformative and a reader had to re-derive by hand
that each literal is exact. Routing literals through `_lit` keeps the flag
live, and `assert_guaranteed` below turns it into an enforced gate.

The enclosures are bit-for-bit identical either way; only the flag changes.
"""
_lit(::Interval{S}, k::Integer) where {S} = interval(S, k)
_lit(::T, k::Integer) where {T<:Real} = T(k)
_lit(::Type{Interval{S}}, k::Integer) where {S} = interval(S, k)
_lit(::Type{T}, k::Integer) where {T<:Real} = T(k)

# `Matrix{Interval{T}}(I,n,n)` builds its entries through a conversion that
# clears the NG flag, which then contaminates every product it takes part in.
# `one`/`zero` of the same element type do not, and give the same matrix.
_eye(T, n) = [i == j ? one(T) : zero(T) for i in 1:n, j in 1:n]

"""
    assert_guaranteed(x, what)

Fail loudly unless every component of `x` still carries IntervalArithmetic's
`isguaranteed` flag. A cleared flag means some bare floating-point value
entered the computation, and the result can no longer be claimed as a rigorous
enclosure without a hand audit of that value. Certificate gates call this.
"""
function assert_guaranteed(x, what::AbstractString)
    ok = all(isguaranteed, x isa Interval ? (x,) : x)
    ok || error("NOT GUARANTEED: $what carries IntervalArithmetic's NG flag; " *
                "a bare floating-point value entered the computation and the " *
                "result is not a certified enclosure")
    return true
end
