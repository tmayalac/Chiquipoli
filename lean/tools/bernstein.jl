# Bernstein positivity certificates: emit Lean proofs that a rational
# polynomial is bounded below on a rational interval.
#
# The whole of "Category A" (convexity, inactive margin, multiplier positivity,
# root uniqueness) reduces to one question repeated: does this polynomial in
# `c` have this sign everywhere `c*` can live? This module answers it with a
# certificate the Lean kernel can re-check by `ring` plus sign lemmas — no
# interval arithmetic, no floating point.
#
# Method. On `[a,b]` with `h = b-a`, every polynomial of degree `n` has an
# exact Bernstein form
#
#     p(c) * h^n  =  Σ_k  A_k * (c-a)^k * (b-c)^(n-k),     A_k = C(n,k) * γ_k
#
# with rational `A_k`. If every `γ_k ≥ m` then, because
# `Σ_k C(n,k) (c-a)^k (b-c)^(n-k) = h^n`, we get `p ≥ m` on the whole interval.
# The Lean proof is therefore: one `ring` identity, plus `n+1` facts of the
# shape `0 ≤ nonneg_rational * (c-a)^i * (b-c)^j`.
#
# Bernstein bounds are *not* tight in general, but they converge under
# subdivision, and the margins here are ~1e-2 while the intervals are ~1e-6,
# so the plain form succeeds comfortably.

module Bernstein

export bern_coeffs, lean_lower_bound_lemma

const QQ = Rational{BigInt}

"""
    bern_coeffs(p, a, b) -> γ

Exact Bernstein coefficients of `p` (power-basis, ascending) on `[a,b]`:
`p(c)*h^n = Σ_k C(n,k)*γ_k*(c-a)^k*(b-c)^(n-k)`.
"""
function bern_coeffs(p::Vector{QQ}, a::QQ, b::QQ)
    n = length(p) - 1
    h = b - a
    # q = coefficients of p(a + h*u) in the variable u
    q = zeros(QQ, n + 1)
    for k in 0:n
        p[k+1] == 0 && continue
        for j in 0:k
            q[j+1] += p[k+1] * binomial(big(k), big(j)) * a^(k - j) * h^j
        end
    end
    # power basis -> Bernstein basis on [0,1]
    return QQ[sum(QQ(binomial(big(j), big(i)), binomial(big(n), big(i))) * q[i+1]
                 for i in 0:j) for j in 0:n]
end

lean_rat(q::QQ) = denominator(q) == 1 ?
    (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
    (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" :
                        "($(numerator(q))/$(denominator(q)))")

"""
    lean_lower_bound_lemma(name, polyexpr, p, a, b; m, alo, ahi, cvar)

Emit a Lean lemma `name : m ≤ polyexpr` valid for `alo ≤ c ≤ ahi`, together
with its Bernstein certificate. `m` defaults to a rational strictly below the
minimum Bernstein coefficient.
"""
function lean_lower_bound_lemma(name::String, polyexpr::String, p::Vector{QQ},
                                a::QQ, b::QQ; m::Union{QQ,Nothing}=nothing,
                                lo::String="clo", hi::String="chi",
                                cvar::String="c", unfolds::String="")
    n = length(p) - 1
    γ = bern_coeffs(p, a, b)
    γmin = minimum(γ)
    if m === nothing
        # a round rational safely below γmin (two significant decimals down)
        m = γmin > 0 ? QQ(floor(BigInt, γmin * 100), 100) : QQ(floor(BigInt, γmin * 100) - 1, 100)
    end
    @assert all(g -> g >= m, γ) "Bernstein bound fails: γmin=$(Float64(γmin)) < m=$(Float64(m))"
    # Degree 0: the "polynomial" is a constant, the Bernstein basis degenerates
    # to a single term and the scaffolding below is both unnecessary and
    # (because `(hi-lo)^0` reduces to 1) confusing for `linarith`. Emit the
    # arithmetic fact directly. Every other generated file has degree ≥ 1, so
    # this branch changes none of their output.
    if n == 0
        # The ℝ ascription is load-bearing: with a constant `polyexpr` there is
        # no `c : ℝ` in the statement to fix the type, and Lean would elaborate
        # the whole inequality in ℕ — where `1/100` truncates to `0` and the
        # lemma becomes true but vacuous.
        names = split(strip(unfolds))
        konst = lean_rat(p[1])
        # Built with explicit newlines: Julia dedents triple-quoted strings by
        # their minimum indentation, which silently flattens Lean's tactic
        # blocks.
        body = isempty(names) ? "  norm_num" :
            "  have hconst : ($polyexpr : ℝ) = $konst := by\n" *
            "    simp only [$(join(names, ", "))]\n" *
            "    try ring\n" *
            "  rw [hconst]\n" *
            "  norm_num"
        return """
/-- `$name`: the expression is constant in `$cvar`, so the bound is arithmetic
once that constancy is established by `ring`. -/
lemma $name ($cvar : ℝ) (h₁ : $lo ≤ $cvar) (h₂ : $cvar ≤ $hi) :
    ($(lean_rat(m)) : ℝ) ≤ ($polyexpr : ℝ) := by
$body
"""
    end
    h = b - a

    # coefficients of the *shifted* certificate  (p - m) :  A_k = C(n,k)*(γ_k - m)
    A = QQ[binomial(big(n), big(k)) * (γ[k+1] - m) for k in 0:n]

    terms = ["$(lean_rat(A[k+1])) * ($cvar - $lo) ^ $k * ($hi - $cvar) ^ $(n-k)" for k in 0:n]
    rhs = join(terms, " +\n        ")

    haves = join(["  have t$k : (0:ℝ) ≤ $(terms[k+1]) :=\n" *
                  "    term_nonneg hu hv $k $(n-k) (by norm_num)" for k in 0:n], "\n")
    nonneg = "add_nonneg " * "(" ^ n
    chain = "t0"
    for k in 1:n
        chain = "add_nonneg ($chain) t$k"
    end

    return """
/-- `$name`: Bernstein certificate, all $(n+1) coefficients ≥ $(Float64(m)). -/
lemma $name ($cvar : ℝ) (h₁ : $lo ≤ $cvar) (h₂ : $cvar ≤ $hi) :
    $(lean_rat(m)) ≤ $polyexpr := by
  have hu : (0:ℝ) ≤ $cvar - $lo := by linarith
  have hv : (0:ℝ) ≤ $hi - $cvar := by linarith
  have hh : (0:ℝ) < ($hi - $lo) ^ $n := by
    unfold $lo $hi; norm_num
  have key : ($polyexpr - $(lean_rat(m))) * ($hi - $lo) ^ $n =
      $rhs := by
    unfold $lo $hi$unfolds; ring
$haves
  have hsum : (0:ℝ) ≤ ($polyexpr - $(lean_rat(m))) * ($hi - $lo) ^ $n := by
    rw [key]; exact $chain
  -- Deterministic: strip the positive factor `h^n`. `nlinarith` also closes
  -- this, but it searches Positivstellensatz products of degree-$n terms with
  -- 60-digit coefficients and blows the heartbeat budget.
  linarith [(mul_nonneg_iff_of_pos_right hh).mp hsum]
"""
end

end # module
