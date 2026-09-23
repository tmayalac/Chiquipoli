# The interval Newton step, on the smallest possible example: sqrt(2).
#
# If 0 is not in f'(X) and N(X) is strictly inside X, then f has exactly one
# root in X. That is the same operator, and the same two conditions, that
# pipeline/stages/02_certify_root.jl applies to the constructor equation F.
#
# Every integer literal is wrapped with `interval` so the result keeps
# IntervalArithmetic's `isguaranteed` flag. Mixing a bare `2` into an interval
# expression is sound here — 2 is exactly representable — but the library
# conservatively clears the flag, and a worked example is the wrong place to
# show output the library declines to vouch for.
using IntervalArithmetic

two = interval(2.0)
f(x)  = x^2 - two
fp(x) = two*x

X = interval(1.4, 1.5)
m = interval(mid(X))          # thin interval, so f(m) is enclosed, not approximated
N = m - f(m)/fp(X)

println("X          = ", X)
println("f'(X)      = ", fp(X), "   0 excluded = ", !in_interval(0, fp(X)))
println("N(X)       = ", N)
println("N(X) ⊂ int X = ", inf(N) > inf(X) && sup(N) < sup(X))
println("guaranteed = ", isguaranteed(N))
