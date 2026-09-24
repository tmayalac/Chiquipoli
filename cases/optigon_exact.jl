# Run the published constructor itself, unchanged, in exact arithmetic.
#
# `cases/upstream/optigon/cstrt_audet_ngon.jl` is Bingane's OPTIGON source, byte
# for byte (SHA-256 checked by `optigon_exact`). It is `include`d here into a
# sandbox module in which the few names it uses are exact:
#
#   * `find_zero(F, bracket)` does not search: it returns the root as the symbol
#     `z`, and keeps `F` so that the equation can be evaluated symbolically too;
#   * an angle is `q·z + r·π` with q, r rational, and `sin`/`cos` of such an
#     angle is an exact element of Q(c,s) (c = cos z, s = sin z) whenever the
#     shift r·π is a multiple of π/2 — upstream's `sin(i*(2z - π/2))` included;
#   * `sin(z/2)^2` is `(1 - c)/2`, the one half-angle upstream uses;
#   * `zeros(k)` returns an array that holds exact elements.
#
# Everything else — the assignments, their order, the index arithmetic, the
# loop, `(-1)^i`, the divisions — is upstream's own code, executed by Julia.
# The result is the polygon and the equation *upstream computes*, as exact
# elements of Q(c,s); `optigon_exact` compares them with the ones the
# certificate is about, by exact equality, not by a tolerance.
#
# What this does not remove: trust in Julia executing a Julia file. That is the
# same trust anyone running OPTIGON extends, and nothing narrower exists; a
# proof assistant cannot read Julia.

module OptigonSandbox

using ..ExactIdentity: CS, cs_const, cs_sin, cs_cos, csadd, cssub, csmul, csdiv, csneg, RPoly

const Q = Rational{BigInt}

"An angle `q·z + r·π`."
struct Ang
    q::Q
    r::Q
end
"The symbol `π` inside the sandbox; `π/k` is an exact angle."
struct PiSym end
"`sin(z/2)`: only its square is ever used, and that is exact."
struct HalfSin end

# Exact conversion of the numbers upstream writes (`n/4 - 2` is a Float64 in
# Julia, but a dyadic one: converting it back is exact, and asserted).
exq(x::Integer) = Q(x)
exq(x::Rational) = Q(x)
function exq(x::AbstractFloat)
    r = Q(x)
    @assert Float64(r) == x
    return r
end

const pi = PiSym()                               # shadows Base.pi here

# --- the arithmetic upstream's code performs, shadowing Base's operators ------
cs(x::CS) = x
cs(x::Real) = cs_const(exq(x))
# Fallbacks to Base for everything else; `a*b*c` parses as `*(a, b, c)`, so
# the n-ary forms reduce left to right through the methods below.
+(x) = x
+(x, y) = Base.:+(x, y)
+(x, y, z, r...) = +(+(x, y), z, r...)
-(x) = Base.:-(x)
-(x, y) = Base.:-(x, y)
*(x, y) = Base.:*(x, y)
*(x, y, z, r...) = *(*(x, y), z, r...)
/(x, y) = Base.:/(x, y)
^(x, k) = Base.:^(x, k)

+(x::CS, y::CS) = csadd(x, y);  +(x::CS, y::Real) = csadd(x, cs(y));  +(x::Real, y::CS) = csadd(cs(x), y)
-(x::CS, y::CS) = cssub(x, y);  -(x::CS, y::Real) = cssub(x, cs(y));  -(x::Real, y::CS) = cssub(cs(x), y)
-(x::CS) = csneg(x)
*(x::CS, y::CS) = csmul(x, y);  *(x::CS, y::Real) = csmul(x, cs(y));  *(x::Real, y::CS) = csmul(cs(x), y)
/(x::CS, y::CS) = csdiv(x, y);  /(x::CS, y::Real) = csdiv(x, cs(y))
^(x::CS, k::Integer) = (@assert k >= 0; foldl(csmul, fill(x, k); init = cs_const(1)))
^(::HalfSin, k::Integer) = (@assert k == 2; CS(RPoly([Q(1, 2), Q(-1, 2)]), RPoly([Q(0)]), RPoly([Q(1)])))

*(a::Real, t::Ang) = Ang(exq(a) * t.q, exq(a) * t.r);  *(t::Ang, a::Real) = a * t
/(t::Ang, a::Real) = Ang(t.q / exq(a), t.r / exq(a))
+(t::Ang, u::Ang) = Ang(t.q + u.q, t.r + u.r)
-(t::Ang, u::Ang) = Ang(t.q - u.q, t.r - u.r)
/(::PiSym, k::Real) = Ang(Q(0), 1 / exq(k))

# sin, cos of q·z + r·π. The shift must be a multiple of π/2 (it is, in upstream).
function _shift(t::Ang)
    m = 2 * t.r
    @assert denominator(m) == 1 "an angle shift that is not a multiple of π/2"
    @assert denominator(t.q) == 1 && t.q >= 0 "a multiple of z that is not a natural number: $t"
    return Int(t.q), mod(Int(m), 4)
end
function sin(t::Ang)
    (t.q == Q(1, 2) && t.r == 0) && return HalfSin()
    t.q == 0 && return Base.sin(Float64(t.r) * Base.pi)   # the bracket only: numbers
    k, m = _shift(t)
    return (cs_sin(k), cs_cos(k), csneg(cs_sin(k)), csneg(cs_cos(k)))[m+1]
end
function cos(t::Ang)
    t.q == 0 && return Base.cos(Float64(t.r) * Base.pi)
    k, m = _shift(t)
    return (cs_cos(k), csneg(cs_sin(k)), csneg(cs_cos(k)), cs_sin(k))[m+1]
end
sin(x::Real) = Base.sin(x)
cos(x::Real) = Base.cos(x)

"The root, symbolically; the equation is kept to be evaluated at it."
const CAPTURED_F = Ref{Any}(nothing)
function find_zero(F, bracket)
    CAPTURED_F[] = F
    return Ang(Q(1), Q(0))
end
zeros(k::Integer) = Any[cs_const(0) for _ in 1:k]

end # module OptigonSandbox

"""
    run_upstream(n, source) -> (a, b, F)

`include_string` the upstream source into a fresh module that imports the
sandbox's exact names (explicitly, so none of Base's is bound first), run
`cstrt_audet_ngon(n)`, and return upstream's arrays and its equation `F`
evaluated at the symbolic root. A fresh module per call, so a planted-error test
can run an altered copy of the source without touching the real one.
"""
function run_upstream(n, source::AbstractString)
    m = Module(:OptigonRun)
    Core.eval(m, :(import ..OptigonSandbox: +, -, *, /, ^, sin, cos, pi, find_zero, zeros))
    Base.include_string(m, source, "cstrt_audet_ngon.jl")
    a, b = Base.invokelatest(Base.invokelatest(getfield, m, :cstrt_audet_ngon), n)
    F = Base.invokelatest(OptigonSandbox.CAPTURED_F[], OptigonSandbox.Ang(1 // 1, 0 // 1))
    return a, b, F
end

const OPTIGON_UPSTREAM = joinpath(@__DIR__, "upstream", "optigon", "cstrt_audet_ngon.jl")
const OPTIGON_UPSTREAM_SHA256 = "376e838b87009f749c19dbee0407419f3c58b30021c406a952a01671aaf6d0ff"

"Exact equality in Q(c,s): (A + sB)/d = (A' + sB')/d'."
cs_equal(x, y) = EI.iszeropoly(EI.psub(EI.pmul(x.A, y.den), EI.pmul(y.A, x.den))) &&
                 EI.iszeropoly(EI.psub(EI.pmul(x.B, y.den), EI.pmul(y.B, x.den)))

"""
    optigon_exact(n) -> NamedTuple

Run upstream's `cstrt_audet_ngon(n)` in exact arithmetic and compare it with the
constructor the certificate uses (`audet_coords_cs`, `audet_F_generic`):

  * `sha_ok`      the upstream file is the recorded one, byte for byte;
  * `vertices_ok` every vertex upstream builds equals the certified one, exactly;
  * `F_ok`        upstream's equation equals the certified one, exactly;
  * `mismatch`    the first vertex that differs, if any.
"""
function optigon_exact(n; source = read(OPTIGON_UPSTREAM, String))
    sha = bytes2hex(SHA.sha256(source))
    a, b, Fup = run_upstream(n, source)
    toCS(v) = v isa CS ? v : cs_const(v)
    ours = audet_coords_cs(n)                       # vertex k+1 is (x, y) of p_k
    mismatch = nothing
    @assert cs_equal(ours[1][1], cs_const(0)) && cs_equal(ours[1][2], cs_const(0))
    for k in 1:n-1
        if !(cs_equal(toCS(a[k]), ours[k+1][1]) && cs_equal(toCS(b[k]), ours[k+1][2]))
            mismatch = k; break
        end
    end
    Fours = audet_F_generic(n, cs_sin, cs_cos, cs_const, _AUDET_CS_OPS)
    return (sha_ok = sha == OPTIGON_UPSTREAM_SHA256, vertices_ok = mismatch === nothing,
            F_ok = cs_equal(Fup, Fours), mismatch = mismatch, sha = sha)
end
