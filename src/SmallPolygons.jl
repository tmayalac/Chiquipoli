"""
    SmallPolygons

General framework to interval-certify LOCAL first-order structural properties
of a candidate convex equilateral small polygon, independent of `n`.

Scope and honesty (see `docs/guide/literature-validation.md`): this module certifies,
by rigorous interval arithmetic, the geometric and rank structure of a given
candidate. It NEVER proves global optimality, and it never upgrades a numerical
value to a certified or proven one. Each block returns an explicit epistemic
status:

  :PROVEN     — established by exact arithmetic / exact algebra.
  :CERTIFIED  — established rigorously by interval arithmetic (strict bounds).
  :CONSISTENT — interval enclosures compatible with an equality they cannot
                prove (Golden Rule); the equality itself needs :PROVEN elsewhere.
  :NUMERICAL  — high-precision floating diagnostic; NOT a certificate.
  :NA         — the block does not apply to this candidate.
  :FAIL       — the property was refuted (used for negative controls).

The dedicated `A16Certificate` module carries the flagship open case A16. The
multiplier and exact-identity blocks here are no longer A16-exclusive: both are
general (`general_multipliers`, and the `ExactIdentity` engine via
`meta[:exact]`), and both return :CERTIFIED / :PROVEN rather than :NUMERICAL.

Block dependencies. The rank and multiplier blocks describe the constraint set
`{e_i = 0, d_ij = 0}` AT the given configuration, so they are meaningful only
where that configuration is feasible. If the equilaterality block refutes
feasibility, those two blocks are reported :NA rather than computed and
labelled :CERTIFIED — a refuted configuration has no KKT multipliers, whatever
the linear algebra of its Jacobian happens to say.
"""
module SmallPolygons

using LinearAlgebra
using IntervalArithmetic

export Candidate, certify, BlockResult, CertifyReport

# ---------------------------------------------------------------------------
# Candidate specification (the "data" of a literature case).
# ---------------------------------------------------------------------------

"""
A literature candidate. `coords(t)` returns an `n×2` matrix of vertex
coordinates (row i+1 = vertex p_i, 0-based), evaluable at a `BigFloat` or an
`Interval{BigFloat}`. For root-defined families, `t` is the constructor scalar
and `root` carries the defining function and search interval; for fixed
(algebraic) candidates, `t` is ignored and `root === nothing`.
"""
struct Candidate
    name::String
    n::Int
    coords::Function                 # coords(t) -> n×2
    root::Union{Nothing,NamedTuple}  # (F=Function, lo, hi, nominal) or nothing
    active::Vector{Tuple{Int,Int}}   # declared active-diameter graph (0-based)
    meta::Dict{Symbol,Any}           # :reference, :doi, :status_literature, ...
end

struct BlockResult
    name::String
    status::Symbol
    detail::String
end

struct CertifyReport
    candidate::String
    n::Int
    blocks::Vector{BlockResult}
    meta::Dict{Symbol,Any}
end

# ---------------------------------------------------------------------------
# Generic geometry primitives (work for Real or Interval element types).
# ---------------------------------------------------------------------------

sqdist(p, i, j) = (p[j+1,1]-p[i+1,1])^2 + (p[j+1,2]-p[i+1,2])^2  # i,j 0-based

interval_abs_bound(x::Interval) = max(abs(inf(x)), abs(sup(x)))
interval_abs_bound(x::Real) = abs(x)

"""
    guarantee_note(x) -> String

IntervalArithmetic tags a result NG ("not guaranteed") as soon as a bare
floating-point value enters it, because in general that value may itself be a
rounded approximation of what the author meant. Candidate files are supplied by
users of this framework, so a cleared flag here is a property of the candidate,
not of the engine: report it beside the block instead of failing, so a reader
can see at a glance whether IA still vouches for the enclosure.
"""
guarantee_note(x) = all(isguaranteed, x isa Interval ? (x,) : x) ? "" :
    "  [WARNING: IntervalArithmetic NG flag — a bare floating-point value entered " *
    "this candidate's evaluation; the bound is only as good as that value is exact]"

"All support determinants H_{i,j}=det(p_{i+1}-p_i, p_j-p_i), i cyclic edges."
function support_determinants(p, n)
    vals = Tuple{Int,Int,eltype(p)}[]
    for i in 0:n-1
        ip = mod(i+1, n)
        ex = p[ip+1,1]-p[i+1,1]; ey = p[ip+1,2]-p[i+1,2]
        for j in 0:n-1
            (j == i || j == ip) && continue
            qx = p[j+1,1]-p[i+1,1]; qy = p[j+1,2]-p[i+1,2]
            push!(vals, (i, j, ex*qy - ey*qx))
        end
    end
    return vals
end

"""
Generic unsquared-constraint Jacobian D(e,d): (n sides + |active|) × (2n+1).

Rows are the true differentials of the UNSQUARED constraints
`e_i = |p_{i+1}-p_i| - ell` and `d_ij = |p_i-p_j| - 1`, i.e. each spatial block
is the corresponding UNIT vector. Each row is therefore divided by its own
edge length, never by a shared one.

This matters. An earlier version divided every side row by the single scalar
`ell` (the caller passes `|p_1-p_0|`) and left the diameter rows unnormalised.
On an equilateral configuration with unit diameters — which is every candidate
this framework is meant to certify — the two agree exactly, so the A16 and the
literature certificates are unaffected. But on any other input the rows were
not gradients of anything: on a test quadrilateral they were off by 0.3, while
the module still reported the resulting rank and multiplier blocks as
CERTIFIED. `ell` is retained in the signature for call compatibility and is no
longer used to scale rows.
"""
function build_jacobian(p, n, active, ell)
    m = n + length(active)
    A = fill(zero(eltype(p)), m, 2n+1)
    for i in 0:n-1
        j = mod(i+1, n)
        dx = p[j+1,1]-p[i+1,1]; dy = p[j+1,2]-p[i+1,2]
        len = sqrt(dx^2 + dy^2)                   # this side's own length
        sx = dx/len; sy = dy/len
        A[i+1, 2i+1] = -sx; A[i+1, 2i+2] = -sy
        A[i+1, 2j+1] =  sx; A[i+1, 2j+2] =  sy
        A[i+1, 2n+1] = -one(eltype(p))            # ∂e_i/∂ℓ = -1
    end
    for (k,(i,j)) in enumerate(active)
        ux = p[i+1,1]-p[j+1,1]; uy = p[i+1,2]-p[j+1,2]
        len = sqrt(ux^2 + uy^2)                   # this diameter's own length
        ux = ux/len; uy = uy/len
        r = n + k
        A[r, 2i+1] =  ux; A[r, 2i+2] =  uy
        A[r, 2j+1] = -ux; A[r, 2j+2] = -uy
    end
    return A
end

"Rigid-motion generators (translations x,y and rotation) as 3 vectors of R^{2n+1}."
function rigid_vectors(p, n)
    rx = zeros(eltype(p), 2n+1); ry = zeros(eltype(p), 2n+1); rr = zeros(eltype(p), 2n+1)
    for i in 0:n-1
        rx[2i+1] = one(eltype(p))
        ry[2i+2] = one(eltype(p))
        rr[2i+1] = -p[i+1,2]; rr[2i+2] = p[i+1,1]
    end
    return rx, ry, rr
end

# `Matrix{Interval{T}}(I,n,n)` builds its entries through a conversion that
# clears IntervalArithmetic's `isguaranteed` flag; `one`/`zero` of the same
# element type do not, and give the same matrix.
_eye(T, n) = [i == j ? one(T) : zero(T) for i in 1:n, j in 1:n]

"""
    f64_enclosure(M) -> Matrix or nothing

A `Float64` interval copy of the interval array `M`, each entry rounded OUTWARD
(`interval(Float64, inf, sup)`), so the copy ENCLOSES the original entry by
entry; `nothing` if some entry is not guaranteed (the caller then keeps the
original, so an NG flag is never lost in the conversion).

Why. The rank and multiplier blocks are dense linear algebra: a preconditioned
regularity test and a Krawczyk step, O(n³) interval operations each. In 256-bit
BigFloat they cost minutes at n = 256; in Float64 intervals seconds. The
products use IntervalArithmetic's `:fast` midpoint-radius mode (BLAS under
directed rounding), guarded by the run-time sentinel `fastmul_verified()`. Every
conclusion stays rigorous: a regular enclosure proves every matrix it contains
regular, and a Krawczyk inclusion for the wider system encloses the solution of
the true one. The only price is width, and the margins these blocks certify
(‖I - CM‖ ≪ 1, λ_min ≫ 10⁻¹⁵) are far above it.
"""
f64_enclosure(M) = all(isguaranteed, M) ? map(x -> interval(Float64, inf(x), sup(x)), M) : nothing

# ---------------------------------------------------------------------------
# Interval matrix products. For Float64 intervals, IntervalArithmetic offers a
# :fast mode: Rump's midpoint-radius product, computed by OpenBLAS with the
# rounding mode set downward and upward (a special OpenBLAS build,
# OpenBLASConsistentFPCSR, whose worker threads inherit the rounding mode). It
# is ~300 times faster than the entrywise :slow mode at n ~ 1000 and just as
# rigorous -- provided the platform really rounds as asked. That is checked
# here, on this machine, before the fast mode is used at all: a sentinel
# multiplies fixed pseudo-random matrices with full-mantissa entries and
# requires every entry of the result to contain the EXACT range of the product,
# computed in Rational{BigInt}. If a single entry fails, every product falls
# back to the :slow mode. The verdict is cached for the process and reported in
# the rank and multiplier blocks. The verdict is a property of the machine, not
# of any candidate, so one per-process cache is the right scope; the lock makes
# the first computation happen once even if several threads ask at the same time.
# ---------------------------------------------------------------------------
const _FASTMUL_VERIFIED = Ref{Union{Nothing,Bool}}(nothing)
const _FASTMUL_LOCK = ReentrantLock()

function _sentinel_matrix(state::Ref{UInt64}, m, k)
    next() = (state[] = state[] * 0x5851f42d4c957f2d + 0x14057b7ef767814f;
              (Int64(state[] >> 11) - (Int64(1) << 52)) / Float64(1 << 52) * 2.0^(Int(state[] % 17) - 8))
    return [next() for _ in 1:m, _ in 1:k]
end

function _exact_contains(C, A, B)
    Aq = Rational{BigInt}.(A isa AbstractMatrix{<:Interval} ? mid.(A) : A)
    thinA = !(eltype(A) <: Interval) || all(a -> inf(a) == sup(a), A)
    Blo = Rational{BigInt}.(inf.(B)); Bhi = Rational{BigInt}.(sup.(B))
    Alo = thinA ? Aq : Rational{BigInt}.(inf.(A)); Ahi = thinA ? Aq : Rational{BigInt}.(sup.(A))
    for i in axes(C, 1), j in axes(C, 2)
        lo = zero(Rational{BigInt}); hi = zero(Rational{BigInt})
        for t in axes(B, 1)
            ps = (Alo[i,t]*Blo[t,j], Alo[i,t]*Bhi[t,j], Ahi[i,t]*Blo[t,j], Ahi[i,t]*Bhi[t,j])
            lo += minimum(ps); hi += maximum(ps)
        end
        (Rational{BigInt}(inf(C[i,j])) <= lo && hi <= Rational{BigInt}(sup(C[i,j]))) || return false
    end
    return true
end

function fastmul_verified()
    v = _FASTMUL_VERIFIED[]
    v === nothing || return v                              # cached: no lock needed
    return lock(_compute_fastmul_verified, _FASTMUL_LOCK)
end

function _compute_fastmul_verified()
    v = _FASTMUL_VERIFIED[]
    v === nothing || return v                              # another thread got here first
    ok = true
    st = Ref(0x2026092800000001)
    for (m, k, p) in ((37, 53, 29), (64, 64, 64), (101, 17, 3), (9, 131, 47))
        A = _sentinel_matrix(st, m, k)
        Bm = _sentinel_matrix(st, k, p); Br = abs.(_sentinel_matrix(st, k, p)) .* 1e-13
        B = [interval(Bm[i,j] - Br[i,j], Bm[i,j] + Br[i,j]) for i in 1:k, j in 1:p]
        AI = interval.(A)                                   # thin, as a preconditioner
        C1 = similar(B, m, p); IntervalArithmetic._mul!(IntervalArithmetic.MatMulMode{:fast}(), C1, AI, B, interval(true), interval(false))
        ok &= _exact_contains(C1, A, B)
        # interval × interval, as in the Krawczyk step
        C2 = similar(B, m, p); IntervalArithmetic._mul!(IntervalArithmetic.MatMulMode{:fast}(), C2, [interval(a - 1e-14, a + 1e-14) for a in A], B, interval(true), interval(false))
        ok &= _exact_contains(C2, [interval(a - 1e-14, a + 1e-14) for a in A], B)
    end
    ok &= rounding(Float64) == RoundNearest               # the mode is restored afterwards
    _FASTMUL_VERIFIED[] = ok
    return ok
end

"`A*B` for interval arrays: the verified :fast product for Float64 intervals, else the :slow one."
function imul(A, B)
    T = eltype(B) <: Interval ? typeof(inf(first(B))) : eltype(B)
    if T === Float64 && fastmul_verified()
        C = similar(B, Interval{Float64}, size(A, 1), size(B)[2:end]...)
        return IntervalArithmetic._mul!(IntervalArithmetic.MatMulMode{:fast}(), C, A, B, interval(true), interval(false))
    end
    return A * B
end
matmul_mode() = fastmul_verified() ? "Float64 intervals, :fast product (sentinel verified on this machine)" :
                                     "Float64 intervals, :slow product (the :fast sentinel failed here)"

"Preconditioned interval regularity test: ||I - inv(mid M)·M||_inf < 1 ⇒ M regular."
function regularity_test(MI)
    T = typeof(inf(first(MI)))      # Float64 or BigFloat: the preconditioner in the same type
    M0 = T.(mid.(MI))
    C = interval.(inv(M0))          # thin: exact floats, keeps the NG flag live
    nn = size(MI, 1)
    E = _eye(eltype(MI), nn) - imul(C, MI)
    # Directed upper bound: row sums as intervals, then the supremum (see the
    # same function in src/a16/linear_algebra.jl).
    bound = maximum(sup(sum(interval(interval_abs_bound(E[i,j])) for j in 1:nn)) for i in 1:nn)
    return bound < 1, bound
end

"""
    select_minor(M0, k) -> (rows, cols)

Choose a `k×k` submatrix of `M0` with a well-conditioned pivot set, by column
pivoted QR on a `Float64` cast of the midpoint matrix.

This search is a HEURISTIC, and deliberately so. It decides only *which* minor
the rank block then tries to certify; the certification itself is the
preconditioned interval regularity test, which is rigorous. The two failure
directions are therefore not symmetric:

  * If the heuristic picks a minor that is in fact regular, the interval test
    certifies it and the rank bound holds.
  * If it picks a poor one, the interval test refuses and the block reports
    `:FAIL`. The certificate is weaker than it could have been, and nothing
    false is asserted.

There is no third case. A bad pivot choice cannot produce a spurious
`:CERTIFIED`, because the heuristic never decides the verdict — it only proposes
a candidate for a rigorous test. So this routine is sound but not complete: a
configuration whose Jacobian has a regular `k×k` minor that Float64 pivoting
fails to find would be refused rather than mis-certified. That has not occurred
for any candidate here (see `docs/audits/referee-report.md`, R8); falling back to
alternative minors on failure would close the completeness gap and change
nothing about soundness.
"""
function select_minor(M0, k)
    F = Float64.(M0)                       # pivoting is heuristic; see above
    qc = qr(F, ColumnNorm())
    cols = sort(qc.p[1:k])
    qr2 = qr(Matrix(transpose(F[:, cols])), ColumnNorm())
    rows = sort(qr2.p[1:k])
    return rows, cols
end

"Linear Krawczyk: rigorously enclose the solution of the square interval system MI·x=bI."
function krawczyk_linear(MI, bI)
    T = typeof(inf(first(MI)))
    M0 = T.(mid.(MI)); b0 = T.(mid.(bI))
    C0 = inv(M0)
    C = interval.(C0); x0 = interval.(C0*b0); nn = length(x0)
    Rm = _eye(eltype(MI), nn) - imul(C, MI)
    residual = imul(C, bI - imul(MI, x0))
    # The loop is a search for a radius at which the Krawczyk inclusion holds,
    # not a convergence argument: the inclusion test below is sound at every
    # radius (Krawczyk's theorem), so the starting radius, the factor 10 and the
    # budget of 24 attempts (radius up to 10^24 times the start) decide only
    # whether a certificate is found. Exhausting them returns pass=false.
    radius = max(T(1e-50), 10*maximum(interval_abs_bound.(residual)))
    for _ in 1:24
        X = [interval(-radius, radius) for _ in 1:nn]
        K = residual + imul(Rm, X)
        if all(inf(K[i]) > -radius && sup(K[i]) < radius for i in 1:nn)
            # The certified set is the exact real sum x0 + K(X). Forming its
            # endpoints in BigFloat rounds TO NEAREST and can report a box up
            # to an ulp NARROWER than the certified one; adding the thin
            # interval x0[i] performs the same sum with OUTWARD rounding.
            return (pass=true, enclosure=[x0[i] + K[i] for i in 1:nn])
        end
        radius *= 10
    end
    return (pass=false, enclosure=nothing)
end

"""
    general_multipliers(p, n, active, ell) -> NamedTuple

General R1 certificate: rigorously certify existence of KKT multipliers `y` with
`D(e,d)^T y = DL` and all active-diameter multipliers `λ_ij > 0`, for ANY
candidate (variable LICQ defect `d = (n+|active|) - (2n-2)`). Method (a direct
generalization of the A16 certificate, no A16-specific data): omit 3 gauge
coordinate-equations whose rigid-motion 3×3 matrix Q is regular; add `d`
normalizations fixing `d` multipliers to nominal values; certify the square
system regular; Krawczyk-enclose the solution; certify `λ>0`; and certify Q
regular (which recovers the 3 omitted stationarity equations exactly by the
rigid-invariance argument).
"""
function general_multipliers(p, n, active, ell)
    D = build_jacobian(p, n, active, ell)
    Df = f64_enclosure(D)
    D = Df === nothing ? D : Df                    # see f64_enclosure
    T = typeof(inf(first(D)))
    nconstr = n + length(active); amb = 2n + 1
    Dt = permutedims(D)
    g = fill(zero(eltype(D)), amb); g[amb] = interval(T(n))
    d = nconstr - (2n - 2)
    # The normalized system has (2n+1-3) + d = nconstr rows only when d >= 0.
    # With fewer than 2n-2 constraints there are not enough equations to pin a
    # multiplier vector and the construction below would hand a non-square
    # matrix to `inv`, throwing DimensionMismatch out of what is supposed to be
    # a total function. Report it as a refutation like every other failure.
    d < 0 && return (pass=false, d=d,
                     reason="only $(nconstr) constraints < 2n-2 = $(2n-2); " *
                            "the stationarity system is underdetermined and no " *
                            "multiplier vector can be certified")
    Dt0 = Float64.(mid.(Dt)); y0 = Dt0 \ Float64.(mid.(g))
    # gauge coords {x_i, y_i, x_j} with y_i ≠ y_j (⇒ Q regular)
    # The threshold 0.05 only picks which vertex j to use: any j with y_j clearly
    # away from y_0 keeps Q well conditioned. Soundness does not depend on it,
    # since Q's regularity is certified below (`regularity_test(Q)`); a bad pick
    # can only make the block fail.
    ys = [mid(p[k+1, 2]) for k in 0:n-1]
    jrel = findfirst(k -> abs(ys[k+1] - ys[1]) > 0.05, 1:n-1)
    jrel === nothing && return (pass=false, reason="no vertex with y≠y_0")
    j0 = jrel
    gauge = [1, 2, 2*j0 + 1]                       # x_0, y_0, x_j (1-based cols)
    keep = setdiff(1:amb, gauge)
    E = eltype(D)                                  # typed, so an empty block (d = 0) keeps it
    # Which multipliers to pin is a choice, not a claim: the pinned system is
    # CERTIFIED regular below, so no pick can make the verdict unsound, only
    # fail. The multiplier of largest magnitude is tried first; a kernel
    # direction of M that vanishes there makes the pinned system singular
    # (Z32 of Bingane and Audet is such a case: the sides have equal multipliers
    # that the kernel does not touch), so the next ones are tried in turn. The
    # first pick succeeds for every A_n, so nothing is retried there.
    order = sortperm(abs.(y0), rev=true)
    M = b = nothing; regM = false
    for r0 in 1:(d == 0 ? 1 : nconstr - d + 1)
        normidx = d == 0 ? Int[] : order[r0:r0+d-1]
        M = vcat(Dt[keep, :],
                 E[ (col == normidx[r] ? one(E) : zero(E)) for r in 1:d, col in 1:nconstr ])
        b = vcat(g[keep], [interval(T(y0[normidx[r]])) for r in 1:d])
        regM, _ = regularity_test(M)
        regM && break
    end
    regM || return (pass=false, reason="normalized system not regular")
    sol = krawczyk_linear(M, b)
    sol.pass || return (pass=false, reason="Krawczyk did not contract")
    # Strict positivity from the infimum alone, with no condition on the width.
    # The Krawczyk step certifies that the true multiplier vector lies inside
    # `sol.enclosure`; so if the infimum of a component is positive, the value it
    # encloses is positive, and that is the whole of the predicate. A narrow
    # enclosure says the value is well localised, which is a different question
    # and not one this block asks. Reviewers have twice suggested adding a
    # maximum-width tolerance here as a safeguard: it would reject certificates
    # that are perfectly sound, and would not make an unsound one impossible,
    # because unsoundness could only come from the enclosure being wrong rather
    # than from its being wide.
    lammin = minimum(inf(sol.enclosure[n + k]) for k in 1:length(active))
    rx, ry, rr = rigid_vectors(p, n)
    Q = [ rx[gauge[1]] rx[gauge[2]] rx[gauge[3]];
          ry[gauge[1]] ry[gauge[2]] ry[gauge[3]];
          rr[gauge[1]] rr[gauge[2]] rr[gauge[3]] ]
    regQ, _ = regularity_test(Q)
    return (pass = lammin > 0 && regQ, d = d, lammin = lammin, regQ = regQ,
            mode = Df === nothing ? "BigFloat intervals" : matmul_mode())
end

# ---------------------------------------------------------------------------
# The certification pipeline.
# ---------------------------------------------------------------------------

"""
    certify(cand; radius=big"1e-24", precision=256) -> CertifyReport

Run the generic blocks and return a report with an explicit epistemic status
per block. Never raises on a refuted property; instead marks the block :FAIL
(this is what negative controls exercise).

`radius` is the half-width of the box `Zbox` around the nominal root. The
interval blocks are evaluated on the whole box, and a root inside it is
certified by the sign change at its ends, so the value only has to be large
enough for the box to contain the root (so that the sign change is there to
be certified) and small enough for the enclosures to stay narrow at `precision`
bits; a bad value makes a block fail and cannot make one pass.
"""
function certify(cand::Candidate; radius=big"1e-24", precision=256)
    # Scoped, not global: a bare `setprecision(BigFloat, precision)` here used to
    # change the working precision of whoever called `certify` (2026-09 external
    # audit, D12).
    return setprecision(BigFloat, precision) do
        _certify(cand, radius)
    end
end

function _certify(cand::Candidate, radius)
    n = cand.n
    blocks = BlockResult[]
    # Candidate `coords`/`F` are often loaded at runtime via `include`; call
    # them through invokelatest so this works regardless of world age.
    _coords(t) = Base.invokelatest(cand.coords, t)
    _F(t) = Base.invokelatest(cand.root.F, t)

    # Evaluation point/box. Root-defined: interval box around nominal z.
    # Fixed: the exact algebraic coordinates, enclosed as a thin interval.
    local Zbox
    if cand.root === nothing
        Zbox = nothing
    else
        z = cand.root.nominal
        Zbox = interval(z-radius, z+radius)
    end

    # ---- Block: existence / uniqueness of the constructor root -------------
    if cand.root === nothing
        push!(blocks, BlockResult("existence", :NA,
            "fixed algebraic coordinates (no scalar root to certify)"))
    else
        F = cand.root.F
        # Rigorous existence by certified sign change at the box endpoints
        # (Intermediate Value Theorem): F is continuous, and if F(inf) and
        # F(sup) have strictly opposite certified signs, a root lies in Zbox.
        Flo = _F(interval(inf(Zbox))); Fhi = _F(interval(sup(Zbox)))
        sign_change = (sup(Flo) < 0 && inf(Fhi) > 0) || (inf(Flo) > 0 && sup(Fhi) < 0)
        st = sign_change ? :CERTIFIED : :FAIL
        push!(blocks, BlockResult("existence", st,
            "IVT sign change on box endpoints = $(sign_change) [F(lo)=$(Flo), F(hi)=$(Fhi)]; uniqueness on search interval delegated to dedicated certificate" * guarantee_note([Flo, Fhi])))
    end

    # ---- Coordinates as intervals at the certified point/box ---------------
    p = cand.root === nothing ? _coords(interval(big"0")) : _coords(Zbox)

    # ---- Block: equilaterality + side length -------------------------------
    # Interval arithmetic can RIGOROUSLY REFUTE equality (disjoint enclosures ⇒
    # sides differ) but cannot PROVE exact equality (Golden Rule). So: FAIL on
    # disjoint side² enclosures; otherwise :CONSISTENT -- not :CERTIFIED, which
    # would read as a certified equality (2026-09 external audit, D11). The
    # equality itself is :PROVEN by the exact_identities block below.
    sides2 = [sqdist(p, i, mod(i+1,n)) for i in 0:n-1]
    maxinf = maximum(inf(s) for s in sides2); minsup = minimum(sup(s) for s in sides2)
    ell = sqrt(sides2[1])   # interval side length
    equilateral_ok = !(maxinf > minsup)
    if maxinf > minsup
        push!(blocks, BlockResult("equilaterality", :FAIL,
            "side² enclosures are disjoint (max inf $(maxinf) > min sup $(minsup)) ⇒ sides NOT all equal (refuted)"))
    else
        push!(blocks, BlockResult("equilaterality", :CONSISTENT,
            "side² enclosures mutually consistent with a common value in [$(maxinf), $(minsup)]; not a proof of equality, which is the exact_identities block" * guarantee_note(sides2)))
    end

    # ---- Block: active graph + inactive margin -----------------------------
    activeset = Set(cand.active)
    active_ok = all(in_interval(1, sqdist(p, i, j)) for (i,j) in cand.active)
    worst_inactive = big"0"; wpair = (-1,-1)
    for i in 0:n-1, j in (i+1):n-1
        (i,j) in activeset && continue
        s = sup(sqdist(p, i, j))
        if s > worst_inactive; worst_inactive = s; wpair = (i,j); end
    end
    inactive_ok = worst_inactive < 1
    margin = inf(1 - sqrt(interval(worst_inactive)))
    if active_ok && inactive_ok
        push!(blocks, BlockResult("active_graph+margin", :CERTIFIED,
            "declared actives enclose diameter 1; worst inactive $(wpair) sqdist<1, margin≥$(margin)" * guarantee_note(p)))
    else
        push!(blocks, BlockResult("active_graph+margin", :FAIL,
            "active_ok=$(active_ok), inactive_ok=$(inactive_ok), worst inactive $(wpair)=$(worst_inactive)"))
    end

    # ---- Block: strict convexity + cyclic order (support determinants) -----
    dets = support_determinants(p, n)
    worst_det = minimum(inf(v) for (_,_,v) in dets)
    convexity_ok = worst_det > 0
    if convexity_ok
        push!(blocks, BlockResult("convexity", :CERTIFIED,
            "all support determinants > 0 (min inf = $(worst_det)); strictly convex, cyclic order (Lemma L2)" * guarantee_note([v for (_,_,v) in dets])))
    else
        push!(blocks, BlockResult("convexity", :FAIL,
            "a support determinant is not strictly positive (min inf = $(worst_det))"))
    end

    # ---- Block: local constant rank = 2n-2 (⇒ I_eq = R_eq) -----------------
    # SOUNDNESS NOTE. The lower bound rank ≥ 2n-2 is interval-rigorous (regular
    # minor). The upper bound rank ≤ 2n-2 is an ALGEBRAIC THEOREM, NOT a
    # numerical check: (i) the three rigid motions annihilate every distance
    # constraint EXACTLY — for a translation the endpoint velocities cancel; for
    # the rotation, (p_i-p_j)·(v_i-v_j)=0 since v_i-v_j is (p_i-p_j) rotated by
    # π/2 — so R_eq ⊆ ker D as an identity in the coordinates; (ii) the three
    # motions are linearly independent (Lemma L1) because certified convexity
    # implies the vertices are distinct. Hence dim ker D ≥ 3, rank ≤ 2n-2. We
    # therefore make the upper bound DEPEND on the convexity block and report
    # the interval max|Aρ| only as a numerical sanity check, never as the basis.
    A = build_jacobian(p, n, cand.active, ell)
    rank_target = 2n - 2
    if !equilateral_ok
        push!(blocks, BlockResult("rank", :NA,
            "equilaterality was refuted, so this configuration is not a feasible " *
            "point of the constraint set; rank D(e,d) there describes nothing and " *
            "is not reported"))
    elseif size(A,1) < rank_target
        push!(blocks, BlockResult("rank", :FAIL,
            "only $(size(A,1)) constraints < 2n-2 = $(rank_target); cannot reach full rank"))
    else
        M0 = BigFloat.(mid.(A))
        rows, cols = select_minor(M0, rank_target)
        Af = f64_enclosure(A[rows, cols])                     # see f64_enclosure
        reg, bound = regularity_test(Af === nothing ? A[rows, cols] : Af)   # rigorous lower bound
        rx, ry, rr = rigid_vectors(p, n)
        maxann = maximum(interval_abs_bound.(vcat(A*rx, A*ry, A*rr)))  # sanity only
        upper_ok = convexity_ok    # Lemma L1 via distinct vertices from convexity
        if reg && upper_ok
            push!(blocks, BlockResult("rank", :CERTIFIED,
                "regular $(rank_target)×$(rank_target) minor (‖I-CM‖∞=$(bound)<1) ⇒ rank≥2n-2; exact annihilation theorem + Lemma L1 (distinct vertices from certified convexity) ⇒ rank≤2n-2; hence rank=2n-2=$(rank_target), I_eq=R_eq [numerical sanity max|Aρ|=$(maxann)] [$(Af === nothing ? "BigFloat intervals" : matmul_mode())]"))
        elseif reg && !convexity_ok
            push!(blocks, BlockResult("rank", :FAIL,
                "regular minor gives rank≥2n-2, but the upper bound needs Lemma L1, which requires certified convexity (distinct vertices) — convexity not certified here"))
        else
            push!(blocks, BlockResult("rank", :FAIL,
                "no regular 2n-2 minor found by the pivot heuristic (bound=$(bound)); rank≥2n-2 not certified"))
        end
    end

    # ---- Block: multiplier identity + positivity (R1, general CERTIFIED) ----
    nconstr = n + length(cand.active)
    licq_defect = nconstr - rank_target
    # licq_defect < 0 means there are FEWER constraints than 2n-2, so the
    # stationarity system is underdetermined rather than LICQ-degenerate. The
    # paper's Section 4.2 rhombus is exactly this case (5 constraints, 2n-2=6),
    # and phrasing it as "LICQ fails by -1 ... a -1-parameter family" was
    # meaningless.
    licq = licq_defect == 0 ? "LICQ holds (constraints=rank=$(rank_target))" :
           licq_defect > 0  ? "LICQ fails by $(licq_defect); multipliers form a $(licq_defect)-parameter affine family" :
                              "only $(nconstr) constraints, fewer than 2n-2 = $(rank_target); rank D(e,d) < 2n-2, so I_eq is strictly larger than R_eq and hypothesis (ii) of Theorem 3.5 cannot hold"
    mc = equilateral_ok ? general_multipliers(p, n, cand.active, ell) : nothing
    if mc === nothing
        push!(blocks, BlockResult("multipliers", :NA,
            "$(licq); equilaterality was refuted, so the configuration is not " *
            "feasible and has no KKT multipliers to certify"))
    elseif mc.pass
        push!(blocks, BlockResult("multipliers", :CERTIFIED,
            "$(licq); certified KKT multipliers with all active-diameter multipliers λ_ij ≥ $(mc.lammin) > 0 (Krawczyk-enclosed; omitted equations recovered via regular Q) [$(mc.mode)]"))
    else
        push!(blocks, BlockResult("multipliers", :FAIL,
            "$(licq); could not certify positive multipliers: $(get(mc,:reason,"λmin=$(get(mc,:lammin,NaN))"))"))
    end

    # ---- Block: exact side/diameter identities (R2, general PROVEN) ---------
    # A candidate may supply meta[:exact] = (certbox) -> (side_statuses,
    # diam_statuses), built by the reusable ExactIdentity engine (exact Q(c,s)
    # algebra); `certbox` is the certified existence box passed below. Present
    # ⇒ the equalities are PROVEN exactly, not merely interval-enclosed.
    if haskey(cand.meta, :exact)
        # Pass the CERTIFIED existence box `Zbox` (root ∈ Zbox by the IVT
        # certificate above) so that the case-(c) sign check `A - sB ≠ 0` is
        # evaluated over a box guaranteed to contain the root, not over a
        # narrower nominal sub-box. For fixed-angle candidates `Zbox === nothing`
        # and the candidate supplies its own interval-π enclosure of the angle.
        sides_st, diams_st = Base.invokelatest(cand.meta[:exact], Zbox)
        good = st -> st in (:UNCONDITIONAL, :PROVED)
        # The candidate supplies `meta[:exact]`, so its output is input to this
        # block, not a result of it. Check its SHAPE before reading its content.
        # Without this the block was vacuously satisfiable: `all(f, [])` is true
        # in Julia, so a candidate returning two empty vectors reported
        # ":PROVEN  0 sides + 0 active diameters" and `structural_pass` stayed
        # true, i.e. the strongest label in the report was awarded for proving
        # nothing. A short vector was just as bad: two statuses for a 16-gon
        # passed while thirty of the thirty one equalities went unexamined.
        nsides = length(sides_st); ndiams = length(diams_st)
        shape_ok = nsides == n && ndiams == length(cand.active)
        allgood = shape_ok && !isempty(sides_st) &&
                  all(good, sides_st) && all(good, diams_st)
        nu = count(==(:UNCONDITIONAL), vcat(sides_st, diams_st))
        nc = count(==(:PROVED), vcat(sides_st, diams_st))
        if !shape_ok
            push!(blocks, BlockResult("exact_identities", :FAIL,
                "meta[:exact] returned $(nsides) side and $(ndiams) diameter statuses, " *
                "but this candidate has $(n) sides and $(length(cand.active)) active " *
                "diameters; the exact-identity engine and the declared configuration " *
                "disagree, so nothing is proved here"))
        else
            push!(blocks, BlockResult("exact_identities", allgood ? :PROVEN : :FAIL,
                "$(nsides) sides + $(ndiams) active diameters proved by exact $(get(cand.meta, :exact_ring, "Q(c,s)")) algebra ($(nu) hold for all θ; $(nc) hold at the root of Fc); side/diameter equalities hold EXACTLY, not only enclosed"))
        end
    end

    # The evaluation box is returned with the report, so a caller compares
    # against the box actually used rather than a rebuilt copy of it.
    return CertifyReport(cand.name, n, blocks, merge(cand.meta, Dict{Symbol,Any}(:Zbox => Zbox)))
end

# ---------------------------------------------------------------------------
# Pretty printing.
# ---------------------------------------------------------------------------

function Base.show(io::IO, r::CertifyReport)
    println(io, "── Certify: ", r.candidate, "  (n=", r.n, ") ──")
    if haskey(r.meta, :status_literature)
        println(io, "   literature: ", r.meta[:status_literature])
    end
    for b in r.blocks
        println(io, "   [", rpad(String(b.status), 10), "] ", rpad(b.name, 20), " ", b.detail)
    end
end

"Overall verdict: no block failed (existence/NA are allowed; all others CERTIFIED/PROVEN)."
function structural_pass(r::CertifyReport)
    return !any(b.status == :FAIL for b in r.blocks)
end
export structural_pass

end # module
