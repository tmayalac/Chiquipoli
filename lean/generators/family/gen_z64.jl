# Generate the Lean certificate of the Bingane-Audet polygon Z64.
#
#     julia --project=. lean/generators/family/gen_z64.jl 64
#
# writes lean/ChiquipoliFamily/Polynomial/Z64/*.lean. The general lemmas every file
# relies on are in lean/ChiquipoliFamily/Basic.lean and BasicZ.lean, proved once.
#
# This is gen_z.jl (the generator of Z32) for the one polygon whose vertices are not all
# of the form (sin z * X(c), Y(c)): four of the 64 vertices carry the unknown y of
# Proposition 2 of Bingane and Audet, a square root, and the constant h = 1/2 enters
# the abscissae of two of them. Everything is therefore a function of c = cos t alone:
#
#     sn c  = sqrt(1 - c^2)                       (= sin t)
#     rad c = 2 - 2c - (sn c * X51(c) + 1/2)^2     (radicand of y - y51)
#     rr c  = sqrt(rad c),   yv c = y51(c) + rr c  (= y)
#     XC_k c = A_k(c) + sn c * B_k(c) + yv c * D_k(c),  YC_k likewise (D_k in {0, 1})
#
# The two defining equations of the paper are E1 (the first fixes y, and holds by
# construction) and E2; the equation of the root is G c = E2e c (sn c) (yv c) = 0.
# What Lean proves is `locally_maximal_at`: at EVERY root c of G in the certified
# bracket, `P c` is a strictly convex equilateral small 64-gon, strictly locally
# maximal, and a root exists in the bracket (intermediate value theorem, the sign of G
# at the ends of the bracket by enclosure arithmetic). Uniqueness of the root of Z64
# in (0, pi/64) is proved by interval bisection in Julia and in Python, not in Lean.
#
# SOURCE OF TRUTH. `z64_vertices` and `z64_equations` in cases/exact_coords.jl, the
# same functions the interval candidate cases/family/Z64/candidate.jl and the exact
# certifier use. Every margin is checked here in exact rational arithmetic BEFORE any
# Lean is written, so a Lean failure can only mean a transcription or tactic problem.

const REPO = normpath(joinpath(@__DIR__, "..", "..", ".."))
include(joinpath(REPO, "src", "A16Certificate.jl"));  using .A16Certificate
include(joinpath(REPO, "src", "ExactIdentity.jl"));   using .ExactIdentity
include(joinpath(REPO, "src", "SmallPolygons.jl"));   using .SmallPolygons
include(joinpath(REPO, "cases", "exact_coords.jl"))
using IntervalArithmetic

const QQ = Rational{BigInt}
setprecision(BigFloat, 512)

n = parse(Int, ARGS[1])
n == 64 || error("gen_z64.jl: only Z64")

# Output root: `lean/` by default; CHIQUI_OUTDIR writes the same tree elsewhere, so that
# verify_family.sh can regenerate into a scratch directory and diff.
const LEANOUT = get(ENV, "CHIQUI_OUTDIR", joinpath(REPO, "lean"))
const MUTATE = ""            # no planted defects here (the negative controls play that role)
const UNGUARDED = false
# A pre-check: an inequality or identity that Lean will re-prove, checked here first in
# exact rational arithmetic.
guard(ok::Bool, msg) = ok ? nothing : error("pre-check failed: " * msg)
planted(file, decl) = nothing

const OUTDIR = joinpath(LEANOUT, "ChiquipoliFamily", "Polynomial", "Z$n")
const NCDIR = joinpath(LEANOUT, "negative_controls_family", "Z$n")
const NS = "Chiquipoli.Family.Z$n"
const MOD = "ChiquipoliFamily.Polynomial.Z$n"
const CONV_CHUNK = 60
const FAR_CHUNK = 80

# ---------------------------------------------------------------------------
# Exact data
# ---------------------------------------------------------------------------
cand = include(joinpath(REPO, "cases", "family", "Z$(n)", "candidate.jl"))
active = cand.active
m = length(active)
@assert m == n - 2

pv = z64_poly_vertices()
eqs = z64_equations()

ptrim(v) = (v = copy(v); while !isempty(v) && v[end] == 0; pop!(v); end; v)
"A coordinate P(c, s, y) = A(c) + s B(c) + y D(c): its three polynomials in c (ascending coefficients)."
function parts(zp::Z64Poly)
    d = Dict((0, 0) => QQ[], (1, 0) => QQ[], (0, 1) => QQ[])
    for ((i, j, l), v) in zp.t
        haskey(d, (j, l)) || error("a monomial with s^$j y^$l")
        vec = d[(j, l)]; length(vec) <= i && append!(vec, zeros(QQ, i + 1 - length(vec))); vec[i+1] = v
    end
    return (A = ptrim(d[(0, 0)]), B = ptrim(d[(1, 0)]), D = ptrim(d[(0, 1)]))
end
XP = [parts(pv[k][1]) for k in 1:n]; YP = [parts(pv[k][2]) for k in 1:n]
peval(p, x) = isempty(p) ? zero(x) : sum(p[i] * x^(i-1) for i in eachindex(p))

# The registry of the distinct polynomials in c, each a Lean definition plK.
PLIDX = Dict{Vector{QQ},Int}(); PLLIST = Vector{Vector{QQ}}()
function pl!(p)
    key = ptrim(QQ.(p))
    return get!(PLIDX, key) do; push!(PLLIST, key); length(PLLIST); end
end

# the polynomials the construction names
let x51 = XP[52], y51 = YP[52]
    @assert isempty(x51.A) && isempty(x51.D) "x51 is not s times a polynomial"
    @assert isempty(y51.B) && isempty(y51.D) "y51 is not a polynomial in c"
end
IX51 = pl!(XP[52].B)                                   # x51 = s * X51(c)
IYF  = pl!(YP[52].A)                                   # y51(c)
IE2  = pl!(QQ[2, -2])                                  # 2 - 2c = ell^2
let S29 = Z64_TS[30], C29 = Z64_TC[30]
    sp = parts(S29); cp = parts(C29)
    @assert isempty(sp.A) && isempty(sp.D) && isempty(cp.B) && isempty(cp.D)
    global IU29 = pl!(sp.B); global IT29 = pl!(cp.A)    # sin 29t = s U28(c), cos 29t = T29(c)
end

# ---- the rational interval around the root --------------------------------------
cstar = cos(BigFloat(cand.root.nominal))
"The rational of smallest denominator in [lo, hi] (continued fractions; lo, hi > 0)."
function simplest(lo, hi)
    a = QQ(lo); b = QQ(hi)
    @assert 0 < a <= b
    f = floor(a)
    f == a && return a
    f + 1 <= b && return f + 1
    return f + 1 / simplest(1 / (b - f), 1 / (a - f))
end
W = parse(BigFloat, get(ENV, "Z64_W", "1e-17"))                 # narrow: the stress recursion amplifies errors
CLO = simplest(cstar - W, cstar - W/4); CHI = simplest(cstar + W/4, cstar + W)
C0 = simplest(cstar - W/8, cstar + W/8); R0 = max(C0 - CLO, CHI - C0)
@assert CLO > 0

# G at c, numerically (BigFloat): the equation of the root
function Gnum(c)
    s = sqrt(1 - c^2)
    a = s * peval(PLLIST[IX51], c) + 1/BigFloat(2)
    rad = peval(PLLIST[IE2], c) - a * a
    y = peval(PLLIST[IYF], c) + sqrt(rad)
    u = a + s * peval(PLLIST[IU29], c) - c
    w = peval(PLLIST[IT29], c) - s - (y - peval(PLLIST[IYF], c))
    return u * u + w * w - peval(PLLIST[IE2], c)
end
sGlo = Int(sign(Gnum(BigFloat(CLO)))); sGhi = Int(sign(Gnum(BigFloat(CHI))))
guard(sGlo * sGhi < 0, "G does not change sign on [clo, chi]")
println("Z64: bracket width $(Float64(CHI - CLO)); G(clo) = $(Float64(Gnum(BigFloat(CLO)))), G(chi) = $(Float64(Gnum(BigFloat(CHI))))")

# ---- Taylor data -------------------------------------------------------------
function taylor(p, c0)
    d = length(p) - 1; t = zeros(QQ, d + 1)
    for k in 0:d, j in k:d; t[k+1] += p[j+1] * binomial(big(j), big(k)) * c0^(j - k); end
    t
end
tail(t) = length(t) > 1 ? sum(abs(t[j+1]) * R0^j for j in 1:length(t)-1) : QQ(0)
GG = big(10)^30
rdn(x) = QQ(floor(BigInt, x * GG), GG); rup(x) = QQ(ceil(BigInt, x * GG), GG)
rnd(x) = QQ(round(BigInt, x * GG), GG)

# ---------------------------------------------------------------------------
# Lean emission helpers (the first ones, needed by the enclosure trees)
# ---------------------------------------------------------------------------
lr(q::QQ) = denominator(q) == 1 ? (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
            (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" : "($(numerator(q))/$(denominator(q)))")
lr(q::Integer) = lr(QQ(q))
function lp(p, var = "c")
    p = ptrim(QQ.(p)); isempty(p) && return "0"
    d = length(p) - 1; d == 0 && return lr(p[1]); e = lr(p[d+1])
    for k in d-1:-1:0; e = p[k+1] == 0 ? "($e) * $var" : "($e) * $var + $(lr(p[k+1]))"; end
    e
end

# Centred-enclosure terms. Each carries its Lean term, an exact rational centre and
# radius, and a Lean proof of |term − centre| ≤ radius built from the lemmas of Basic.lean;
# every operation recentres to rounded rationals, so each side condition is small
# rational arithmetic. The definition of a quantity IS the term of its tree, so the
# definition and the proof of its enclosure cannot diverge.
struct En; t::String; c::QQ; r::QQ; pf::String; end
GR = big(10)^30
rn(x) = QQ(round(BigInt, x * GR), GR); ru(x) = QQ(ceil(BigInt, x * GR), GR)
function recen(t, a, r, pf)
    c = rn(a); e = ru(abs(a - c)); s_ = ru(r + e)
    En(t, c, s_, "(recenter (b := $(lr(c))) (e := $(lr(e))) (s := $(lr(s_))) $pf (by norm_num [rho]) (by norm_num [rho]))")
end
zeroEn = En("0", QQ(0), QQ(0), "(show |(0:ℝ) - 0| ≤ 0 by norm_num)")
eadd(x, y) = recen("($(x.t) + $(y.t))", x.c + y.c, x.r + y.r, "(add_close $(x.pf) $(y.pf))")
esub(x, y) = recen("($(x.t) - $(y.t))", x.c - y.c, x.r + y.r, "(sub_close' $(x.pf) $(y.pf))")
eneg(x) = recen("(-$(x.t))", -x.c, x.r, "(neg_close $(x.pf))")
emul(x, y) = recen("($(x.t) * $(y.t))", x.c * y.c, abs(x.c) * y.r + abs(y.c) * x.r + x.r * y.r, "(mul_close $(x.pf) $(y.pf))")
function ediv(x, d)
    @assert d.r < abs(d.c) "a denominator is not enclosed away from zero"
    d.c > 0 ?
        recen("($(x.t) / $(d.t))", x.c / d.c, (x.r * d.c + abs(x.c) * d.r) / ((d.c - d.r) * d.c),
              "(div_close $(x.pf) $(d.pf) (by norm_num [rho]))") :
        recen("($(x.t) / $(d.t))", x.c / d.c, (x.r * (-d.c) + abs(x.c) * d.r) / ((-d.c - d.r) * (-d.c)),
              "(div_close_neg $(x.pf) $(d.pf) (by norm_num [rho]))")
end
esum(xs) = isempty(xs) ? zeroEn : foldl(eadd, xs)

# ---------------------------------------------------------------------------
# The enclosures: polynomials, sn, rad, rr, yv, and the 128 coordinates
# ---------------------------------------------------------------------------
HALF = En("(1 / 2 : ℝ)", QQ(1, 2), QQ(0), "(show |((1 / 2 : ℝ)) - (1 / 2)| ≤ 0 by norm_num)")

# a polynomial leaf: centre and radius from the centred Taylor expansion at c0
PLENC = Dict{Int,Tuple{QQ,QQ}}()
function plenc(idx)
    get!(PLENC, idx) do
        p = PLLIST[idx]; t = taylor(p, C0)
        ctr = rnd(t[1]); (ctr, rup(abs(t[1] - ctr) + tail(t)))
    end
end
leafP(idx) = (e = plenc(idx); En("pl$idx c", e[1], e[2], "(encP$idx c h₁ h₂)"))

# sn c = sqrt(1 - c^2)
SQ0 = rnd(sqrt(BigFloat(1 - C0^2)))
ESQ_E = R0 * (2 * abs(C0) + R0) + abs((1 - C0^2) - SQ0^2)       # the E of enc_sqrt
ESQ = rup(ESQ_E / SQ0)
leafSn = En("sn c", SQ0, ESQ, "(enc_sn c h₁ h₂)")

# the trees, shared by the Lean definitions (symbolic leaves) and by the enclosures
radtree(Lp, Ls) = (a = eadd(emul(Ls, Lp(IX51)), HALF); esub(Lp(IE2), emul(a, a)))
yvtree(Lp, Lrr) = eadd(Lp(IYF), Lrr)
function e1tree(Lp, Ls, Ly)
    a = eadd(emul(Ls, Lp(IX51)), HALF); d = esub(Ly, Lp(IYF))
    esub(eadd(emul(d, d), emul(a, a)), Lp(IE2))
end
function e2tree(Lp, Ls, Ly, Lc)
    a = eadd(emul(Ls, Lp(IX51)), HALF)
    u = esub(eadd(a, emul(Ls, Lp(IU29))), Lc)
    w = esub(esub(Lp(IT29), Ls), esub(Ly, Lp(IYF)))
    esub(eadd(emul(u, u), emul(w, w)), Lp(IE2))
end

RADEN = radtree(leafP, leafSn)
guard(RADEN.c - RADEN.r > 0, "the radicand is not enclosed away from zero")
RR0 = rnd(sqrt(BigFloat(RADEN.c)))
RR_E = RADEN.r + abs(RADEN.c - RR0^2)
ERR = rup(RR_E / RR0)
leafRr = En("rr c", RR0, ERR, "(enc_rr c h₁ h₂)")
YVEN = yvtree(leafP, leafRr)
leafYv = En("yv c", YVEN.c, YVEN.r, "(enc_yv c h₁ h₂)")

# the coordinates
function coord_en(P)
    terms = En[]
    isempty(P.A) || push!(terms, leafP(pl!(P.A)))
    isempty(P.B) || push!(terms, emul(leafSn, leafP(pl!(P.B))))
    isempty(P.D) || push!(terms, emul(leafYv, leafP(pl!(P.D))))
    return esum(terms)
end
XEN = [coord_en(XP[k]) for k in 1:n]; YEN = [coord_en(YP[k]) for k in 1:n]
cx = Dict{Int,QQ}(k - 1 => XEN[k].c for k in 1:n); cy = Dict{Int,QQ}(k - 1 => YEN[k].c for k in 1:n)
RHO = rup(max(maximum(e.r for e in XEN), maximum(e.r for e in YEN)))
println("  enclosures: sn ±$(Float64(ESQ)), rad ±$(Float64(RADEN.r)), rr ±$(Float64(ERR)), y ±$(Float64(YVEN.r)); every coordinate within ρ = $(Float64(RHO))")
println("  $(length(PLLIST)) distinct polynomials in c, degrees ≤ $(maximum(length.(PLLIST)) - 1)")

# the endpoint evaluations of G, for the intermediate value theorem
function pointleaves(cpt, cname)
    Lp(idx) = (v = peval(PLLIST[idx], cpt); En("pl$idx $cname", v, QQ(0), "(show |pl$idx $cname - $(lr(v))| ≤ 0 by unfold pl$idx $cname; norm_num)"))
    s0 = rnd(sqrt(BigFloat(1 - cpt^2)))
    Esq = abs((1 - cpt^2) - s0^2)                                  # EU = 0 at a point
    Ls = En("sn $cname", s0, rup(Esq / s0), "(enc_sn_$cname)")
    rad = radtree(Lp, Ls)
    r0 = rnd(sqrt(BigFloat(rad.c)))
    Err = rup((rad.r + abs(rad.c - r0^2)) / r0)
    Lrr = En("rr $cname", r0, Err, "(enc_rr_$cname)")
    yv = yvtree(Lp, Lrr)
    Ly = En("yv $cname", yv.c, yv.r, "(enc_yv_$cname)")
    Lc = En(cname, cpt, QQ(0), "(show |$cname - $(lr(cpt))| ≤ 0 by unfold $cname; norm_num)")
    G = e2tree(Lp, Ls, Ly, Lc)
    return (Lp = Lp, s0 = s0, Esq = Esq, Ls = Ls, rad = rad, r0 = r0, Lrr = Lrr, yv = yv, Ly = Ly, G = G, Err = Err)
end
PT = Dict("clo" => pointleaves(CLO, "clo"), "chi" => pointleaves(CHI, "chi"))
for nm in ("clo", "chi")
    g = PT[nm].G
    println("  G($nm) ∈ $(Float64(g.c)) ± $(Float64(g.r))")
    guard(abs(g.c) > g.r, "the sign of G at $nm is not certified")
end
sGlo2 = PT["clo"].G.c < 0 ? -1 : 1; sGhi2 = PT["chi"].G.c < 0 ? -1 : 1
@assert sGlo2 == sGlo && sGhi2 == sGhi "the enclosure of G disagrees with its numerical sign"

# ---- sign-layer margins, all checked exactly here ------------------------------
function det_margin(x0, x1, x2, y0, y1, y2)
    r2 = 2RHO
    ((x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)) -
        (abs(x1 - x0) * r2 + abs(y2 - y0) * r2 + r2 * r2) -
        (abs(y1 - y0) * r2 + abs(x2 - x0) * r2 + r2 * r2)
end
triples = [(i, mod(i + 1, n), j) for i in 0:n-1 for j in 0:n-1 if j != i && j != mod(i + 1, n)]
conv_m = [det_margin(cx[i], cx[ip], cx[j], cy[i], cy[ip], cy[j]) for (i, ip, j) in triples]
guard(minimum(conv_m) > 0, "a support determinant is not certified by the enclosures")

activeset = Set(active)
farpairs = [(i, j) for i in 0:n-1 for j in i+1:n-1 if !((i, j) in activeset)]
far_ub(i, j) = (abs(cx[j] - cx[i]) + 2RHO)^2 + (abs(cy[j] - cy[i]) + 2RHO)^2
guard(maximum(far_ub(i, j) for (i, j) in farpairs) < 1, "an inactive pair is not certified below 1")

# ---- Henneberg order -----------------------------------------------------------
bars = vcat([(i, mod(i + 1, n)) for i in 0:n-1], active)
nbr = Dict(k => Int[] for k in 0:n-1)
for (a, b) in bars; push!(nbr[a], b); push!(nbr[b], a); end
hmargin(k, i, j) = det_margin(cx[k], cx[i], cx[j], cy[k], cy[i], cy[j])
best = nothing
for (a, b) in [(0, 1)]                      # pin side 0; greedy by margin
    done = Set([a, b]); order = Tuple{Int,Int,Int}[]; ok = true
    while length(done) < n
        cands = Tuple{QQ,Int,Int,Int}[]
        for k in 0:n-1
            k in done && continue
            back = [i for i in nbr[k] if i in done]
            for i in back, j in back
                i == j && continue
                push!(cands, (hmargin(k, i, j), k, i, j))
            end
        end
        isempty(cands) && (ok = false; break)
        (mg, k, i, j) = maximum(cands)
        guard(mg > 0, "Henneberg step at vertex $k is not certified")
        push!(done, k); push!(order, (k, i, j))
    end
    global BLOCKV = sort(collect(setdiff(Set(0:n-1), done)))
    ok || println("  Henneberg stalls; vertices left: ", BLOCKV)
    global best = order
end
HEN = best

# ---- the self-stress (the multipliers), by the reverse Henneberg recursion --------
# Every bar is exactly one of: the pinned bar (0,1); a Henneberg bar of its
# later-added endpoint; or the one "extra" bar the construction does not use (Z64 has
# 2n-2 bars, rank 2n-2 and a one-dimensional space of self-stresses). The extra bar
# carries a free rational stress t₁ (the overall scale and sign). In reverse Henneberg
# order, vertex k balances the forces of its already-known bars with its two
# Henneberg bars (Cramer, determinant henD_k ≠ 0); the pinned bar is fixed last
# by vertex 1, and vertices 0, 1 then balance by the global force and moment
# identities. Equilibrium is in the coordinates (XC, YC) themselves.
@assert isempty(XP[1].A) && isempty(XP[1].B) && isempty(XP[1].D) && isempty(YP[1].A) && isempty(YP[1].B) && isempty(YP[1].D) "vertex 0 is not at the origin"
barix = Dict{Tuple{Int,Int},Int}()
for (bi, (a, b)) in enumerate(bars); barix[(a, b)] = bi; barix[(b, a)] = bi; end
hbar = Dict{Int,Tuple{Int,Int,Int,Int}}()          # k => (i, j, bar_ki, bar_kj)
used = Set([barix[(0, 1)]])
for (k, i, j) in HEN
    hbar[k] = (i, j, barix[(k, i)], barix[(k, j)]); push!(used, barix[(k, i)], barix[(k, j)])
end
extra = sort([bi for bi in eachindex(bars) if !(bi in used)])
@assert BLOCKV == [14, 15, 49, 50] "the vertices no Henneberg step reaches are not the expected block"
BLOCKBARS = Dict{Symbol,Int}(:x1 => barix[(13, 14)], :x2 => barix[(14, 15)], :x3 => barix[(15, 16)], :x4 => barix[(48, 49)],
    :sg => barix[(49, 50)], :x6 => barix[(50, 51)], :x7 => barix[(14, 49)], :x8 => barix[(14, 50)], :x9 => barix[(15, 50)])
@assert sort(collect(values(BLOCKBARS))) == extra "the bars outside the Henneberg construction are not the nine bars of the block"
@assert all(haskey(barix, k) for k in ((13, 14), (14, 15), (15, 16), (48, 49), (49, 50), (50, 51), (14, 49), (14, 50), (15, 50)))
@assert all(length([i for i in nbr[k] if !(i in BLOCKV)]) == 1 for k in BLOCKV) "a block vertex has not exactly one pinned neighbour"
PIN = barix[(0, 1)]
incident(k) = sort([bi for (bi, (a, b)) in enumerate(bars) if a == k || b == k])
otherend(bi, k) = bars[bi][1] == k ? bars[bi][2] : bars[bi][1]
others(k) = [bi for bi in incident(k) if !(k in keys(hbar) && bi in hbar[k][3:4]) && !(k == 1 && bi == PIN)]


# ---------------------------------------------------------------------------
# The block 14, 15, 49, 50: stresses solved as a unit (no Henneberg step reaches it)
# ---------------------------------------------------------------------------
# Each block vertex has one pinned neighbour (13, 16, 48, 51), and the four are joined by
# five more bars: 9 bars, 8 equilibrium equations, one free stress t (the bar 15-50).
# The elimination: vertex 15 gives the bars 14-15, 15-16 as t times Cramer coefficients
# f2, f3; with σ the stress of the bar 49-50, vertex 49 gives 48-49, 14-49 as σ g4, σ g7,
# and vertex 50 gives 50-51, 14-50 as σ h6 + t j6, σ h8 + t j8; vertex 14 then fixes σ and
# the stress of 13-14 as t ρS, t ρ1 (`blockA`).
leafX(k) = En("XC$k c", cx[k], RHO, "(encX$k c h₁ h₂)")
leafY(k) = En("YC$k c", cy[k], RHO, "(encY$k c h₁ h₂)")
SC = Dict{Int,QQ}(); SR = Dict{Int,QQ}()
leafS(b) = En("st$(b-1) c", SC[b], SR[b], "(encS$(b-1) c h₁ h₂)")

dv(i, j) = (esub(leafX(j), leafX(i)), esub(leafY(j), leafY(i)))            # P_j - P_i
det2(u, v) = esub(emul(u[1], v[2]), emul(u[2], v[1]))
ipJ(u, v) = esub(emul(u[2], v[1]), emul(u[1], v[2]))                       # ip u (J v)
"The Cramer coefficients of cramer_lin: (D, ((-w1) b2 + w2 b1)/D, ((-w2) a1 + w1 a2)/D)."
function cramer_coef(w, a, b)
    D = det2(a, b)
    (D, ediv(eadd(emul(eneg(w[1]), b[2]), emul(w[2], b[1])), D), ediv(eadd(emul(eneg(w[2]), a[1]), emul(w[1], a[2])), D))
end

BK = Vector{Tuple{String,En}}()                    # named quantities, in dependency order
function named(name, en)
    push!(BK, (name, en))
    En("bk_$name c", en.c, en.r, "(enc_bk_$name c h₁ h₂)")
end
Tleaf(T) = En(lr(T), T, QQ(0), "(show |(($(lr(T)) : ℝ)) - $(lr(T))| ≤ 0 by norm_num)")

"The coefficient functions of the block and the stresses of its nine bars, for the free stress `T`."
function block_run(T)
    empty!(BK)
    a, b, c, d, a2, b2, c2, d2 = 14, 15, 49, 50, 13, 16, 48, 51
    Tl = Tleaf(T)
    (Db, f2e, f3e) = cramer_coef(dv(b, d), dv(b, a), dv(b, b2))
    named("Db", Db); f2 = named("f2", f2e); f3 = named("f3", f3e)
    (Dc, g4e, g7e) = cramer_coef(dv(c, d), dv(c, c2), dv(c, a))
    named("Dc", Dc); g4 = named("g4", g4e); g7 = named("g7", g7e)
    (Dd, h6e, h8e) = cramer_coef(dv(d, c), dv(d, d2), dv(d, a))
    (_, j6e, j8e) = cramer_coef(dv(d, b), dv(d, d2), dv(d, a))
    named("Dd", Dd); h6 = named("h6", h6e); h8 = named("h8", h8e); j6 = named("j6", j6e); j8 = named("j8", j8e)
    A = dv(a, a2); Bv = dv(a, b); Cv = dv(a, c); Dv = dv(a, d)
    Vx = named("Vx", eadd(emul(g7, Cv[1]), emul(h8, Dv[1]))); Vy = named("Vy", eadd(emul(g7, Cv[2]), emul(h8, Dv[2])))
    Wx = named("Wx", eadd(emul(f2, Bv[1]), emul(j8, Dv[1]))); Wy = named("Wy", eadd(emul(f2, Bv[2]), emul(j8, Dv[2])))
    DV = esub(emul(A[1], Vy), emul(A[2], Vx))
    named("DV", DV)
    rhoS = named("rhoS", ediv(eneg(esub(emul(A[1], Wy), emul(A[2], Wx))), DV))
    rho1 = named("rho1", ediv(eneg(esub(emul(Wx, Vy), emul(Wy, Vx))), DV))
    # the rigidity coefficients of block_pin
    pa2 = dv(a2, a); pb2 = dv(b2, b); pc2 = dv(c2, c); pd2 = dv(d2, d)      # P_x - P_x'
    A1 = named("A1", ipJ(dv(a, b), pb2)); A2 = named("A2", ipJ(dv(a, c), pc2)); A3 = named("A3", ipJ(dv(a, d), pd2))
    B2 = ipJ(dv(a, c), pa2); B3 = ipJ(dv(a, d), pa2); A4 = ipJ(dv(c, d), pd2); B4 = ipJ(dv(c, d), pc2)
    named("K", esub(emul(emul(B3, A4), A2), emul(emul(B2, B4), A3)))
    # the stresses
    st = Dict{Int,En}()
    st[BLOCKBARS[:x9]] = Tl
    st[BLOCKBARS[:x2]] = emul(Tl, f2); st[BLOCKBARS[:x3]] = emul(Tl, f3)
    stσ = emul(Tl, rhoS); st[BLOCKBARS[:sg]] = stσ
    SC[BLOCKBARS[:sg]] = stσ.c; SR[BLOCKBARS[:sg]] = stσ.r
    Sg = leafS(BLOCKBARS[:sg])
    st[BLOCKBARS[:x4]] = emul(Sg, g4); st[BLOCKBARS[:x7]] = emul(Sg, g7)
    st[BLOCKBARS[:x6]] = eadd(emul(Sg, h6), emul(Tl, j6)); st[BLOCKBARS[:x8]] = eadd(emul(Sg, h8), emul(Tl, j8))
    st[BLOCKBARS[:x1]] = emul(Tl, rho1)
    return st
end
BSTRESS1 = block_run(QQ(1))
# the order in which the block stresses are defined (dependencies first)
BORDER = [BLOCKBARS[k] for k in (:x9, :x2, :x3, :sg, :x4, :x7, :x6, :x8, :x1)]
# numeric stress (BigFloat at the rational centres) to choose t₁
function stress_numeric(t)
    X(k) = BigFloat(cx[k]); Yc(k) = BigFloat(cy[k])
    y = Dict{Int,BigFloat}(b => BigFloat(e.c) for (b, e) in BSTRESS1)
    for (k, i, j) in reverse(HEN)
        (_, _, p, q) = hbar[k]
        Fx = sum((y[b] * (X(otherend(b, k)) - X(k)) for b in others(k)); init = big(0.0))
        Fy = sum((y[b] * (Yc(otherend(b, k)) - Yc(k)) for b in others(k)); init = big(0.0))
        D = (X(i) - X(k)) * (Yc(j) - Yc(k)) - (Yc(i) - Yc(k)) * (X(j) - X(k))
        y[p] = (-Fx * (Yc(j) - Yc(k)) + Fy * (X(j) - X(k))) / D
        y[q] = (-Fy * (X(i) - X(k)) + Fx * (Yc(i) - Yc(k))) / D
    end
    Gx = sum(y[b] * (X(otherend(b, 1)) - X(1)) for b in others(1))
    Gy = sum(y[b] * (Yc(otherend(b, 1)) - Yc(1)) for b in others(1))
    ux = X(0) - X(1); uy = Yc(0) - Yc(1)
    y[PIN] = -(Gx * ux + Gy * uy) / (ux^2 + uy^2)
    y
end
yA = stress_numeric(nothing)
sgn = nothing
for sg in (1, -1)
    lam = minimum(sg * yA[b] for b in n+1:n+m); ssum = sum(sg * yA[b] for b in 1:n)
    (ssum < 0 && lam > 0) && (global sgn = sg; break)
end
@assert sgn !== nothing "neither sign of the self-stress gives positive diameter stresses"
ymax = maximum(abs(yA[b]) for b in eachindex(bars))
T1 = sgn * QQ(round(BigInt, 1 / ymax * 10^6), 10^6)            # scale: the largest stress is about 1

println("Z$n:  [clo,chi] = [$CLO, $CHI]  width $(Float64(CHI - CLO))   ρ = $(Float64(RHO))")
println("  convexity: $(length(triples)) determinants, worst certified margin $(Float64(minimum(conv_m)))")
println("  inactive:  $(length(farpairs)) pairs, worst certified bound $(Float64(maximum(far_ub(i,j) for (i,j) in farpairs)))")
println("  Henneberg: $(length(HEN)) steps, worst margin $(Float64(minimum(hmargin(k,i,j) for (k,i,j) in HEN)))")


# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------
mA(i) = "st$i"; mL(e) = "st$(n + e)"         # the stress on side i / on active diameter e (0-based)
header(doc, imports) = """/-
AUTO-GENERATED by `lean/generators/family/gen_z64.jl $n` — do not edit by hand.

$doc
-/
$(join(["import $im" for im in imports], "\n"))

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace $NS

open Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family
"""
footer() = "\nend $NS\n"
mkpath(OUTDIR)
for f in readdir(OUTDIR); endswith(f, ".lean") && rm(joinpath(OUTDIR, f)); end
function emit(name, body)
    open(joinpath(OUTDIR, name * ".lean"), "w") do io; print(io, body); end
end

# Emit `pieces` (Lean declarations) as a chain of files base1, base2, …, each
# importing the previous one. Lean keeps every proof of a file in memory while it
# elaborates that file, so large certificates are split; a compiled file is
# cheap to import. Advances the global `prev` to the last file of the chain.
function emit_chain(base, doc, pieces, chunk)
    chunks = collect(Iterators.partition(pieces, chunk))
    for (ci, ch) in enumerate(chunks)
        local buf = IOBuffer()
        print(buf, header("$doc\n\n(Part $ci of $(length(chunks)).)", [prev]))
        for pc in ch; print(buf, pc); end
        print(buf, footer())
        emit("$base$ci", String(take!(buf)))
        global prev = "$MOD.$base$ci"
    end
end

# Taylor proof of |poly(c) − ctr| ≤ rad  or  lb ≤ poly(c), on [lo, hi]. The
# expansion point and radius are Lean constants `cn`, `rn` with values `C`, `R`;
# `nr` is the lemma giving |c − cn| ≤ rn on the interval `lo..hi`.
function taylor_steps(pname, p; cn = "c0", rn = "r0", C = C0, R = R0)
    t = taylor(p, C); deg = length(t) - 1
    rhs = join(["$(lr(t[j+1])) * (c - $cn) ^ $j" for j in 0:deg], " + ")
    steps = join(["  obtain ⟨l$j, u$j⟩ := abs_le.mp (tbound ($(lr(t[j+1]))) ($(lr(abs(t[j+1])))) c $cn $rn $j hr (abs_le.mpr ⟨by norm_num, by norm_num⟩))" for j in 1:deg], "\n")
    tl = deg == 0 ? "0" : join(["$(lr(abs(t[j+1]))) * $rn ^ $j" for j in 1:deg], " + ")
    return t, deg, rhs, steps, tl
end
function encl_lemma(name, pname, p, ctr; rad = RHO, radname = "rho")
    t, deg, rhs, steps, tl = taylor_steps(pname, p)
    guard(abs(t[1] - ctr) + tail(t) <= rad, "the enclosure $name does not hold (hnum)")
    return encl_text(name, pname, t, deg, rhs, steps, tl, ctr, radname)
end
function encl_text(name, pname, t, deg, rhs, steps, tl, ctr, radname)
    unf = radname == "rho" ? "rho" : ""
    if deg == 0
        return """
lemma $name (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |$pname c - $(lr(ctr))| ≤ $radname := by
  unfold $pname $unf; norm_num
"""
    end
    """
lemma $name (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |$pname c - $(lr(ctr))| ≤ $radname := by
  have key : $pname c = $rhs := by
    unfold $pname c0; ring
  have hr : |c - c0| ≤ r0 := near c h₁ h₂
$steps
  have hnum : |($(lr(t[1])) : ℝ) - $(lr(ctr))| + ($tl) ≤ $radname := by
    unfold r0 $unf; norm_num
  have e1 := neg_abs_le (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  have e2 := le_abs_self (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  rw [key, abs_le]
  constructor <;> linarith
"""
end
function lb_lemma(name, pname, p, lb; lo = "clo", hi = "chi", cn = "c0", rn = "r0", nr = "near", C = C0, R = R0)
    t, deg, rhs, steps, tl = taylor_steps(pname, p; cn = cn, rn = rn, C = C, R = R)
    guard(lb <= t[1] - (deg == 0 ? 0 : sum(abs(t[j+1]) * R^j for j in 1:deg)), "the lower bound $name does not hold (hnum)")
    if deg == 0
        return """
lemma $name (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : ($(lr(lb)) : ℝ) ≤ $pname c := by
  unfold $pname; norm_num
"""
    end
    """
lemma $name (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : ($(lr(lb)) : ℝ) ≤ $pname c := by
  have key : $pname c = $rhs := by
    unfold $pname $cn; ring
  have hr : |c - $cn| ≤ $rn := $nr c h₁ h₂
$steps
  have hnum : ($(lr(lb)) : ℝ) ≤ $(lr(t[1])) - ($tl) := by
    unfold $rn; norm_num
  rw [key]
  linarith
"""
end


# ---------------------------------------------------------------------------
# Identities in Q[c, s, y] (unreduced), and their reduction modulo s^2 = 1 - c^2
# ---------------------------------------------------------------------------
struct P3; t::Dict{NTuple{3,Int},QQ}; end
p3clean(d) = P3(Dict(k => v for (k, v) in d if v != 0))
Base.:+(a::P3, b::P3) = (d = copy(a.t); for (k, v) in b.t; d[k] = get(d, k, QQ(0)) + v; end; p3clean(d))
Base.:-(a::P3) = P3(Dict(k => -v for (k, v) in a.t))
Base.:-(a::P3, b::P3) = a + (-b)
function Base.:*(a::P3, b::P3)
    r = Dict{NTuple{3,Int},QQ}()
    for ((i1, j1, l1), v) in a.t, ((i2, j2, l2), w) in b.t
        k = (i1 + i2, j1 + j2, l1 + l2); r[k] = get(r, k, QQ(0)) + v * w
    end
    p3clean(r)
end
p3const(v) = p3clean(Dict{NTuple{3,Int},QQ}((0, 0, 0) => QQ(v)))
p3poly(p) = p3clean(Dict{NTuple{3,Int},QQ}((i - 1, 0, 0) => p[i] for i in eachindex(p)))
const P3S = P3(Dict{NTuple{3,Int},QQ}((0, 1, 0) => QQ(1)))
const P3Y = P3(Dict{NTuple{3,Int},QQ}((0, 0, 1) => QQ(1)))
const P3C = P3(Dict{NTuple{3,Int},QQ}((1, 0, 0) => QQ(1)))
p3iszero(a::P3) = isempty(a.t)
p3coord(P) = p3poly(P.A) + P3S * p3poly(P.B) + P3Y * p3poly(P.D)
p3fromz64(zp::Z64Poly) = P3(Dict{NTuple{3,Int},QQ}(k => v for (k, v) in zp.t))
"p = rem + q (s^2 - (1 - c^2)), with rem of degree at most 1 in s."
function reduce_s(p::P3)
    rem = Dict{NTuple{3,Int},QQ}(); q = Dict{NTuple{3,Int},QQ}()
    work = copy(p.t)
    while !isempty(work)
        (k, v) = first(work); delete!(work, k)
        (i, j, l) = k
        if j < 2
            rem[k] = get(rem, k, QQ(0)) + v
        else
            qk = (i, j - 2, l); q[qk] = get(q, qk, QQ(0)) + v
            w1 = (i, j - 2, l); work[w1] = get(work, w1, QQ(0)) + v
            w2 = (i + 2, j - 2, l); work[w2] = get(work, w2, QQ(0)) - v
        end
    end
    return p3clean(rem), p3clean(q)
end
"A P3 as a Lean term in c, s = sn c and y = yv c."
function lp3(p::P3)
    isempty(p.t) && return "0"
    terms = String[]
    for ((i, j, l), v) in sort(collect(p.t); by = kv -> (kv[1][3], kv[1][2], kv[1][1]))
        fs = [lr(v)]
        i > 0 && push!(fs, i == 1 ? "c" : "c ^ $i")
        j > 0 && push!(fs, j == 1 ? "(sn c)" : "(sn c) ^ $j")
        l > 0 && push!(fs, l == 1 ? "(yv c)" : "(yv c) ^ $l")
        push!(terms, "(" * join(fs, " * ") * ")")
    end
    join(terms, " + ")
end

XQ = [p3coord(XP[k]) for k in 1:n]; YQ = [p3coord(YP[k]) for k in 1:n]
E2POLY = p3poly(PLLIST[IE2])
SQD(i, j) = (XQ[j+1] - XQ[i+1]) * (XQ[j+1] - XQ[i+1]) + (YQ[j+1] - YQ[i+1]) * (YQ[j+1] - YQ[i+1])
# the two equations, unreduced, exactly as the Lean definitions E1e, E2e (the trees e1tree, e2tree)
let a = P3S * p3poly(PLLIST[IX51]) + p3const(1//2), d = P3Y - p3poly(PLLIST[IYF])
    global E1U = d * d + a * a - E2POLY
    u = a + P3S * p3poly(PLLIST[IU29]) - P3C
    w = p3poly(PLLIST[IT29]) - P3S - d
    global E2U = u * u + w * w - E2POLY
end
E1R = p3fromz64(eqs.E1); E2R = p3fromz64(eqs.E2)
@assert p3iszero(reduce_s(E1U)[1] - E1R) "E1e does not reduce to the equation E1 of the candidate"
@assert p3iszero(reduce_s(E2U)[1] - E2R) "E2e does not reduce to the equation E2 of the candidate"

# every side: unconditional, or one of the two equations; every diameter: unconditional
SIDEKIND = Dict{Int,Symbol}(); SIDEQ = Dict{Int,P3}()
for i in 0:n-1
    f = SQD(i, mod(i + 1, n)) - E2POLY
    (rem, q) = reduce_s(f)
    if p3iszero(rem); SIDEKIND[i] = :U; SIDEQ[i] = q
    elseif p3iszero(rem - E1R); SIDEKIND[i] = :E1; (r2, q2) = reduce_s(f - E1U); @assert p3iszero(r2); SIDEQ[i] = q2
    elseif p3iszero(rem - E2R); SIDEKIND[i] = :E2; (r2, q2) = reduce_s(f - E2U); @assert p3iszero(r2); SIDEQ[i] = q2
    else error("side $i is neither an identity nor one of the two equations")
    end
end
DIAMQ = Dict{Int,P3}()
for (e, (i, j)) in enumerate(active)
    (rem, q) = reduce_s(SQD(i, j) - p3const(1)); @assert p3iszero(rem) "active diameter ($i,$j) is not identically 1"
    DIAMQ[e-1] = q
end
println("  sides: $(count(==(:U), values(SIDEKIND))) unconditional, E1 at $(sort([i for (i,k) in SIDEKIND if k == :E1])), E2 at $(sort([i for (i,k) in SIDEKIND if k == :E2])); $(length(DIAMQ)) diameters identically 1")
@assert sort([i for (i, k) in SIDEKIND if k == :E1]) == [13, 50] && sort([i for (i, k) in SIDEKIND if k == :E2]) == [15, 48]

# ---------------------------------------------------------------------------
# Poly.lean
# ---------------------------------------------------------------------------
global buf = IOBuffer()
print(buf, header("""**Z$n: the polynomial layer.** Everything is a function of `c = cos t`:
`sn c = √(1 − c²)` (this is `sin t`), the radicand `rad c` of `y − y₅₁`, `rr c = √(rad c)`,
`yv c = y₅₁(c) + rr c` (this is `y`), and every vertex coordinate
`A(c) + sn c · B(c) + yv c · D(c)` with `A, B, D` the polynomials `pl*`. `E1e`, `E2e` are the two
defining equations of Proposition 2 of Bingane and Audet in `(c, s, y)`, and
`G c = E2e c (sn c) (yv c)` is the equation of the root. `[clo, chi]` is a rational
interval of width about `10⁻¹⁷` around the root.""",
    ["ChiquipoliFamily.Basic", "ChiquipoliFamily.BasicZ"]))
println(buf, """
noncomputable def clo : ℝ := $(lr(CLO))
noncomputable def chi : ℝ := $(lr(CHI))
noncomputable def c0 : ℝ := $(lr(C0))
noncomputable def r0 : ℝ := $(lr(R0))
/-- Uniform radius of the vertex enclosures. -/
noncomputable def rho : ℝ := $(lr(RHO))

lemma near (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |c - c0| ≤ r0 :=
  near_of (by unfold c0 r0 clo; norm_num) (by unfold c0 r0 chi; norm_num) h₁ h₂
""")
for i in eachindex(PLLIST)
    println(buf, "noncomputable def pl$i (c : ℝ) : ℝ := ", lp(PLLIST[i]))
end
symLp(idx) = En("pl$idx c", QQ(0), QQ(0), "")
println(buf, """

/-- `sin t`, as a function of `c = cos t`. -/
noncomputable def sn (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)
/-- The radicand of `y - y₅₁` (`e² - a²` of Proposition 2). -/
noncomputable def rad (c : ℝ) : ℝ := $(RADEN.t)
noncomputable def rr (c : ℝ) : ℝ := Real.sqrt (rad c)
/-- The ordinate `y` shared by the vertices 14, 15, 49, 50. -/
noncomputable def yv (c : ℝ) : ℝ := $(YVEN.t)
""")
for k in 0:n-1
    println(buf, "noncomputable def XC$k (c : ℝ) : ℝ := ", XEN[k+1].t)
    println(buf, "noncomputable def YC$k (c : ℝ) : ℝ := ", YEN[k+1].t)
end
E1SYM = e1tree(symLp, En("s", QQ(0), QQ(0), ""), En("y", QQ(0), QQ(0), ""))
E2SYM = e2tree(symLp, En("s", QQ(0), QQ(0), ""), En("y", QQ(0), QQ(0), ""), En("c", QQ(0), QQ(0), ""))
println(buf, """

/-- The first defining equation of Proposition 2, in `(c, s, y)`: it fixes `y`. -/
noncomputable def E1e (c s y : ℝ) : ℝ := $(E1SYM.t)
/-- The second defining equation. -/
noncomputable def E2e (c s y : ℝ) : ℝ := $(E2SYM.t)
/-- The equation of the root. -/
noncomputable def G (c : ℝ) : ℝ := E2e c (sn c) (yv c)""")
print(buf, footer())
emit("Poly", String(take!(buf)))

# ---------------------------------------------------------------------------
# EnclP*.lean: the polynomials; EnclS.lean: sn, rad, rr, yv; EnclC*.lean: the coordinates
# ---------------------------------------------------------------------------
global prev = "$MOD.Poly"
emit_chain("EnclP", """**Z$n: the polynomial leaves.** Each polynomial in `c` is within an explicit radius of a
rational centre on `[clo, chi]`: centred Taylor expansion at `c0`, one `ring` identity per
polynomial, then one bound per term (`tbound`).""",
    [encl_lemma("encP$i", "pl$i", PLLIST[i], plenc(i)[1]; rad = plenc(i)[2], radname = lr(plenc(i)[2])) for i in eachindex(PLLIST)], 16)

global buf = IOBuffer()
print(buf, header("""**Z$n: `sin t`, the radicand, `y`.** `sn`, `rad`, `rr` and `yv` enclosed on `[clo, chi]`:
the square roots by `enc_sqrt` from an enclosure of the radicand, the radicand and `y` by
centred enclosure arithmetic on the polynomial leaves. The radicand is enclosed away from zero.""", [prev]))
println(buf, """
lemma one_sub_nonneg (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : 0 ≤ 1 - c ^ 2 := by
  have h3 : c ≤ 1 := by unfold chi at h₂; linarith
  have h4 : 0 ≤ c := by unfold clo at h₁; linarith
  nlinarith

/-- `sin² t = 1 − cos² t`. -/
lemma sn_sq (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : sn c ^ 2 = 1 - c ^ 2 := by
  unfold sn; exact Real.sq_sqrt (one_sub_nonneg c h₁ h₂)

lemma enc_sn (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |sn c - $(lr(SQ0))| ≤ $(lr(ESQ)) := by
  unfold sn
  exact enc_sqrt (E := $(lr(ESQ_E))) (one_sub_nonneg c h₁ h₂) (one_sub_sq_close (near c h₁ h₂)) (by norm_num)
    (by unfold r0 c0; norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma enc_rad (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |rad c - $(lr(RADEN.c))| ≤ $(lr(RADEN.r)) := by
  unfold rad; exact $(RADEN.pf)

lemma rad_nonneg (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : 0 ≤ rad c :=
  nonneg_of_close (enc_rad c h₁ h₂) (by norm_num)

lemma enc_rr (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |rr c - $(lr(RR0))| ≤ $(lr(ERR)) := by
  unfold rr
  exact enc_sqrt (E := $(lr(RR_E))) (rad_nonneg c h₁ h₂) (enc_rad c h₁ h₂) (by norm_num)
    (by norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma enc_yv (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |yv c - $(lr(YVEN.c))| ≤ $(lr(YVEN.r)) := by
  unfold yv; exact $(YVEN.pf)""")
print(buf, footer())
emit("EnclS", String(take!(buf)))
global prev = "$MOD.EnclS"

emit_chain("EnclC", """**Z$n: vertex enclosures.** Each vertex coordinate is within `rho` of a rational centre on
`[clo, chi]`, by centred enclosure arithmetic on the leaves: the proof follows the term of
its definition.""",
    [s_ for k in 0:n-1 for s_ in (
        "\nlemma encX$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |XC$k c - $(lr(cx[k]))| ≤ rho := by\n  unfold XC$k; exact loose $(XEN[k+1].pf) (by norm_num [rho])\n",
        "\nlemma encY$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |YC$k c - $(lr(cy[k]))| ≤ rho := by\n  unfold YC$k; exact loose $(YEN[k+1].pf) (by norm_num [rho])\n")], 16)
# ---------------------------------------------------------------------------
# Conv*.lean  (chained, so lake builds them one after another)
# ---------------------------------------------------------------------------
enc(nm, k) = "(enc$nm$k c h₁ h₂)"
function margin_expr(x0, x1, x2, y0, y1, y2)
    "(($(lr(x1)) - $(lr(x0))) * ($(lr(y2)) - $(lr(y0))) - ($(lr(y1)) - $(lr(y0))) * ($(lr(x2)) - $(lr(x0))))" *
    " - (|$(lr(x1)) - $(lr(x0))| * (2 * rho) + |$(lr(y2)) - $(lr(y0))| * (2 * rho) + (2 * rho) * (2 * rho))" *
    " - (|$(lr(y1)) - $(lr(y0))| * (2 * rho) + |$(lr(x2)) - $(lr(x0))| * (2 * rho) + (2 * rho) * (2 * rho))"
end
conv_chunks = collect(Iterators.partition(triples, CONV_CHUNK))
MUTATE == "conv" && planted("ChiquipoliFamily/Polynomial/Z$n/Conv1.lean", "convD_0_2")
for (ci, ch) in enumerate(conv_chunks)
    local buf = IOBuffer()
    print(buf, header("**Z$n: support determinants, part $ci of $(length(conv_chunks)).** Each is positive on\n`[clo, chi]`, from the vertex enclosures by `det_lb`.", [prev]))
    for (i0, ip0, j) in ch
        # mutation `conv`: the first determinant with its first two vertices
        # swapped — the orientation of the support line reversed.
        (i, ip) = (MUTATE == "conv" && (i0, ip0, j) == (0, 1, 2)) ? (ip0, i0) : (i0, ip0)
        guard(det_margin(cx[i], cx[ip], cx[j], cy[i], cy[ip], cy[j]) > 0, "support determinant ($i0,$ip0,$j) (hn)")
        println(buf, """
theorem convD_$(i0)_$(j) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    0 < (XC$ip c - XC$i c) * (YC$j c - YC$i c) - (YC$ip c - YC$i c) * (XC$j c - XC$i c) := by
  have h := det_lb $(enc("X", i)) $(enc("X", ip)) $(enc("X", j)) $(enc("Y", i)) $(enc("Y", ip)) $(enc("Y", j))
  have hn : (0 : ℝ) < $(margin_expr(cx[i], cx[ip], cx[j], cy[i], cy[ip], cy[j])) := by
    unfold rho; norm_num [abs_of_pos, abs_of_neg]
  linarith""")
    end
    print(buf, footer())
    emit("Conv$ci", String(take!(buf)))
    global prev = "$MOD.Conv$ci"
end


# ---------------------------------------------------------------------------
# Far*.lean — every non-active pair at distance < 1
# ---------------------------------------------------------------------------
far_chunks = [collect(ch) for ch in Iterators.partition(farpairs, FAR_CHUNK)]
for (fi, ch) in enumerate(far_chunks)
    local buf = IOBuffer()
    print(buf, header("**Z$n: non-active pairs, part $fi of $(length(far_chunks)).** Each is at squared distance\n`< 1`, from the vertex enclosures by `sqd_ub0`.", [prev]))
    for (i, j) in ch
        guard(far_ub(i, j) < 1, "pair ($i,$j) is not certified below 1 (hn)")
        println(buf, """
theorem far_$(i)_$(j) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    (XC$j c - XC$i c) * (XC$j c - XC$i c) + (YC$j c - YC$i c) * (YC$j c - YC$i c) < 1 := by
  have h := sqd_ub0 $(enc("X", i)) $(enc("X", j)) $(enc("Y", i)) $(enc("Y", j))
  have hn : (|$(lr(cx[j])) - $(lr(cx[i]))| + 2 * rho) ^ 2 + (|$(lr(cy[j])) - $(lr(cy[i]))| + 2 * rho) ^ 2 < 1 := by
    unfold rho; norm_num [abs_of_pos, abs_of_neg]
  nlinarith [h, hn]""")
    end
    print(buf, footer())
    emit("Far$fi", String(take!(buf)))
    global prev = "$MOD.Far$fi"
end

# ---------------------------------------------------------------------------
# Sides*.lean — the exact identities
# ---------------------------------------------------------------------------
# Every identity is a polynomial identity in (c, s, y) = (c, sn c, yv c) modulo s^2 = 1 - c^2;
# the cofactor q of the relation is computed here (reduce_s) and ring checks the rest. The
# four sides E1 (13, 50) and E2 (15, 48) hold only because y solves the two equations of
# Proposition 2: E1 by construction (E1_c), E2 at a root of G.
side_pieces = String[]
function pl_names(ks...)
    names = String[]
    for k in ks, P in (XP[k+1], YP[k+1]), part in (P.A, P.B, P.D)
        isempty(part) || push!(names, "pl$(pl!(part))")
    end
    names
end
EN1 = ["pl$IX51", "pl$IYF", "pl$IE2"]; EN2 = ["pl$IX51", "pl$IYF", "pl$IE2", "pl$IU29", "pl$IT29"]
for i in 0:n-1
    j = mod(i + 1, n)
    lhs = "(XC$j c - XC$i c) * (XC$j c - XC$i c) + (YC$j c - YC$i c) * (YC$j c - YC$i c) = 2 - 2 * c"
    q = lp3(SIDEQ[i])
    gn = pl_names(i, j)
    if SIDEKIND[i] == :U
        un = join(vcat(["XC$i", "XC$j", "YC$i", "YC$j"], gn), ", ")
        push!(side_pieces, "\ntheorem side_$i (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :\n    $lhs := by\n  have hs := sn_sq c h₁ h₂\n  simp only [$un]\n  linear_combination ($q) * hs\n")
    else
        en = SIDEKIND[i] == :E1 ? EN1 : EN2
        un = join(unique(vcat(["XC$i", "XC$j", "YC$i", "YC$j"], gn, en)), ", ")
        hyp = SIDEKIND[i] == :E1 ? "" : " (hG : G c = 0)"
        hE = SIDEKIND[i] == :E1 ? "  have hE := E1_c c h₁ h₂\n  simp only [E1e, $(join(unique(vcat(gn, en)), ", "))] at hE\n" :
                                  "  have hE := hG\n  simp only [G, E2e, $(join(unique(vcat(gn, en)), ", "))] at hE\n"
        push!(side_pieces, "\ntheorem side_$i (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi)$hyp :\n    $lhs := by\n  have hs := sn_sq c h₁ h₂\n$hE  simp only [$un]\n  linear_combination ($q) * hs + hE\n")
    end
end
for (e, (i, j)) in enumerate(active)
    q = lp3(DIAMQ[e-1])
    un = join(vcat(["XC$i", "XC$j", "YC$i", "YC$j"], pl_names(i, j)), ", ")
    push!(side_pieces, "\ntheorem diam_$(e-1) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :\n    (XC$j c - XC$i c) * (XC$j c - XC$i c) + (YC$j c - YC$i c) * (YC$j c - YC$i c) = 1 := by\n  have hs := sn_sq c h₁ h₂\n  simp only [$un]\n  linear_combination ($q) * hs\n")
end
# E1 holds at every c of the bracket: y - y51 = rr and rr^2 = rad
E1pre = """
theorem E1_c (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : E1e c (sn c) (yv c) = 0 := by
  have hrr : rr c * rr c = rad c := by unfold rr; exact Real.mul_self_sqrt (rad_nonneg c h₁ h₂)
  unfold E1e yv
  unfold rad at hrr
  linear_combination hrr
"""
global buf = IOBuffer()
print(buf, header("**Z$n: the first defining equation.** `E1e c (sn c) (yv c) = 0` for every `c` of the bracket: `y − y₅₁ = rr c` and `rr c ^ 2` is the radicand.", [prev]))
print(buf, E1pre)
print(buf, footer())
emit("E1", String(take!(buf)))
global prev = "$MOD.E1"
emit_chain("Sides", """**Z$n: sides and active diameters, exactly.** All $n sides equal `2 − 2c` in squared length
— $(count(==(:U), values(SIDEKIND))) for every `c` of the bracket, the sides 13 and 50 because `y` solves the first equation
(`E1_c`), the sides 15 and 48 at a root of `G` — and all $m active diameters are identically `1`.""", side_pieces, 16)
# ---------------------------------------------------------------------------
# Hen.lean
# ---------------------------------------------------------------------------
global buf = IOBuffer()
print(buf, header("**Z$n: the Henneberg determinants.** Pin side `0 → 1`; then each vertex, in\nthe order below, is joined to two pinned vertices by bars with independent\ndirections. Each determinant is positive on `[clo, chi]` by `det_lb`.", [prev]))
# mutation `hen`: the first Henneberg vertex pinned by two bars to the SAME
# vertex — a degenerate step, determinant identically 0.
MUTATE == "hen" && planted("ChiquipoliFamily/Polynomial/Z$n/Hen.lean", "henD_$(HEN[1][1])")
for (k, i, j0) in HEN
    j = (MUTATE == "hen" && k == HEN[1][1]) ? i : j0
    guard(hmargin(k, i, j) > 0, "Henneberg determinant at vertex $k (hn)")
    println(buf, """
theorem henD_$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    0 < (XC$i c - XC$k c) * (YC$j c - YC$k c) - (YC$i c - YC$k c) * (XC$j c - XC$k c) := by
  have h := det_lb $(enc("X", k)) $(enc("X", i)) $(enc("X", j)) $(enc("Y", k)) $(enc("Y", i)) $(enc("Y", j))
  have hn : (0 : ℝ) < $(margin_expr(cx[k], cx[i], cx[j], cy[k], cy[i], cy[j])) := by
    unfold rho; norm_num [abs_of_pos, abs_of_neg]
  linarith""")
end
print(buf, footer())
emit("Hen", String(take!(buf)))
prev = "$MOD.Hen"



# ---------------------------------------------------------------------------
# BlockDef.lean — the block 14, 15, 49, 50: its coefficient functions and their enclosures
# ---------------------------------------------------------------------------
block_run(T1)
BKF = copy(BK)
global buf = IOBuffer()
print(buf, header("""**Z$n: the block 14, 15, 49, 50.** No vertex addition by two bars reaches these four
vertices: each has one bar to a pinned neighbour (13, 16, 48, 51) and they are joined by five more.
Their stresses are solved as a unit (the coefficient functions below), and the displacements
are zero by `block_pin`, whose four coefficients `A1`, `A2`, `A3`, `K` are enclosed away from zero.
Every function is defined by the term of its enclosure tree, so the definition and the proof of its
enclosure cannot diverge.""", [prev]))
for (nm, en) in BKF
    println(buf, "noncomputable def bk_$nm (c : ℝ) : ℝ := $(en.t)")
end
for (nm, en) in BKF
    println(buf, "\nlemma enc_bk_$nm (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |bk_$nm c - $(lr(en.c))| ≤ $(lr(en.r)) := by\n  unfold bk_$nm; exact $(en.pf)")
end
for nm in ("Db", "Dc", "Dd", "DV", "A1", "A2", "A3", "K")
    en = only(e for (k, e) in BKF if k == nm)
    guard(abs(en.c) > en.r, "the block coefficient $nm is not enclosed away from zero")
    if en.c > 0
        println(buf, "\nlemma bk_$(nm)_ne (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : bk_$nm c ≠ 0 :=\n  (pos_of_close (enc_bk_$nm c h₁ h₂) (by norm_num)).ne'")
    else
        println(buf, "\nlemma bk_$(nm)_ne (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : bk_$nm c ≠ 0 :=\n  (neg_of_close (enc_bk_$nm c h₁ h₂) (by norm_num)).ne")
    end
    println("  block: $nm ∈ $(Float64(en.c)) ± $(Float64(en.r))")
end
print(buf, footer())
emit("BlockDef", String(take!(buf)))
global prev = "$MOD.BlockDef"
# ---------------------------------------------------------------------------
# Stress*.lean — the multipliers, as a self-stress (see the comment at `extra`)
# ---------------------------------------------------------------------------
# Centred-enclosure terms. Each carries its Lean term, an exact rational centre
# and radius, and a Lean proof of |term − centre| ≤ radius built from the lemmas
# of Basic.lean; every operation recentres to rounded rationals, so each side
# condition is small rational arithmetic. The definition of a stress IS the term
# of its tree, so the definition and the proof of its enclosure cannot diverge.
force(k, coord, bs) = esum([emul(leafS(b), esub(coord == "X" ? leafX(otherend(b, k)) : leafY(otherend(b, k)),
                                                    coord == "X" ? leafX(k) : leafY(k))) for b in bs])

stress_def = Dict{Int,String}(); stress_pf = Dict{Int,String}()
hen_terms = Dict{Int,NTuple{6,String}}(); pin_terms = ("", "", "", "")
BSTRESS = block_run(T1)
for b in BORDER
    e = BSTRESS[b]; SC[b] = e.c; SR[b] = e.r
    stress_def[b] = e.t
    stress_pf[b] = b == BLOCKBARS[:x9] ? "by unfold st$(b-1); norm_num" : "by unfold st$(b-1); exact $(e.pf)"
end
order_defs = copy(BORDER)
# mutation `stress`: Cramer's rule with one sign dropped, at the first vertex the
# reverse recursion solves — the classic transcription error. The stress it
# defines no longer balances that vertex.
KMUT = reverse(HEN)[1][1]
MUTATE == "stress" && planted("ChiquipoliFamily/Polynomial/Z$n/StressDef.lean", "bal_$KMUT")
for (k, i, j) in reverse(HEN)
    (_, _, p, q) = hbar[k]
    Fx = force(k, "X", others(k)); Fy = force(k, "Y", others(k))
    ui1 = esub(leafX(i), leafX(k)); ui2 = esub(leafY(i), leafY(k))
    uj1 = esub(leafX(j), leafX(k)); uj2 = esub(leafY(j), leafY(k))
    D = esub(emul(ui1, uj2), emul(ui2, uj1))
    sp = ediv(eadd(emul((MUTATE == "stress" && k == KMUT) ? Fx : eneg(Fx), uj2), emul(Fy, uj1)), D)
    sq = ediv(eadd(emul(eneg(Fy), ui1), emul(Fx, ui2)), D)
    hen_terms[k] = (Fx.t, Fy.t, ui1.t, ui2.t, uj1.t, uj2.t)
    for (b, e) in ((p, sp), (q, sq))
        SC[b] = e.c; SR[b] = e.r
        stress_def[b] = e.t; stress_pf[b] = "by unfold st$(b-1); exact $(e.pf)"
        push!(order_defs, b)
    end
end
let
    Gx = force(1, "X", others(1)); Gy = force(1, "Y", others(1))
    ux = esub(leafX(0), leafX(1)); uy = esub(leafY(0), leafY(1))
    sp = ediv(eneg(eadd(emul(Gx, ux), emul(Gy, uy))), eadd(emul(ux, ux), emul(uy, uy)))
    global pin_terms = (Gx.t, Gy.t, ux.t, uy.t)
    SC[PIN] = sp.c; SR[PIN] = sp.r
    stress_def[PIN] = sp.t; stress_pf[PIN] = "by unfold st$(PIN-1); exact $(sp.pf)"
    push!(order_defs, PIN)
end
@assert sort(order_defs) == collect(eachindex(bars))
SUM = esum([leafS(b) for b in 1:n])
lamlo = minimum(SC[b] - SR[b] for b in n+1:n+m)
guard(lamlo > 0, "a diameter stress is not certified positive (enclosures too wide)")
guard(SUM.c + SUM.r < 0, "the side stresses are not certified to sum below zero")
# Equilibrium at the centres. The true stresses balance exactly at every vertex;
# with |st_b − SC_b| ≤ SR_b and every coordinate within ρ of its centre, the
# residual at the centres is at most Σ_b SR_b (|Δ centre| + 2ρ) + |SC_b| 2ρ.
# Lean proves the balances symbolically (StressDef.lean); this is the numerical
# shadow of that proof, so a wrong Cramer formula is refused before it is written.
for k in 0:n-1, (C, coord) in ((cx, "x"), (cy, "y"))
    res = sum(SC[b] * (C[otherend(b, k)] - C[k]) for b in incident(k))
    tol = sum(SR[b] * (abs(C[otherend(b, k)] - C[k]) + 2RHO) + abs(SC[b]) * 2RHO for b in incident(k))
    guard(abs(res) <= tol, "vertex $k does not balance in $coord at the centres (residual $(Float64(res)))")
end
println("  multipliers: self-stress, free stress t = $(Float64(T1)) on the bar $(bars[BLOCKBARS[:x9]]); worst certified λ ≥ $(Float64(lamlo)), Σα ≤ $(Float64(SUM.c + SUM.r))")

# StressDef.lean: the definitions and the vertex balances
global buf = IOBuffer()
print(buf, header("""**Z$n: the multipliers, as a self-stress.** The nine bars of the block 14, 15, 49, 50 are
solved as a unit (`BlockDef.lean`), from the one free stress `t` of the bar 15–50; every other stress
is defined by Cramer's rule at the vertex that added it, in reverse order, and the stress on the
pinned side `0 → 1` last. Each vertex then balances
(`bal_*`, by `field_simp; ring` with its Henneberg determinant nonzero), and
vertices `0`, `1` by the global force and moment identities (`bal_base`).
Nothing here uses `Fc`: the equilibrium holds on the whole interval.""", [prev]))
for b in order_defs
    println(buf, "@[irreducible] noncomputable def st$(b-1) (c : ℝ) : ℝ := $(stress_def[b])")
end
for k in 0:n-1
    println(buf, "noncomputable def BX$k (c : ℝ) : ℝ := $(join(["st$(b-1) c * (XC$(otherend(b, k)) c - XC$k c)" for b in incident(k)], " + "))")
    println(buf, "noncomputable def BY$k (c : ℝ) : ℝ := $(join(["st$(b-1) c * (YC$(otherend(b, k)) c - YC$k c)" for b in incident(k)], " + "))")
end
for (k, i, j) in HEN
    (_, _, p, q) = hbar[k]
    (F1, F2, a1, a2, b1, b2) = hen_terms[k]
    println(buf, "\ntheorem bal_$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : BX$k c = 0 ∧ BY$k c = 0 := by\n" *
        "  have hD := (henD_$k c h₁ h₂).ne'\n" *
        "  obtain ⟨h1, h2⟩ := cramer_bal (F1 := $F1) (F2 := $F2)\n    (a1 := $a1) (a2 := $a2) (b1 := $b1) (b2 := $b2) hD\n" *
        "  unfold BX$k BY$k st$(p-1) st$(q-1)\n  exact ⟨by linear_combination h1, by linear_combination h2⟩")
end

# the four vertices of the block
st(key) = "st$(BLOCKBARS[key] - 1)"
function cl_inst(t, w, a, b)      # cramer_lin with t, force direction w = (i -> j), bar vectors a, b (pairs of vertex indices)
    (i1, j1) = w; (i2, j2) = a; (i3, j3) = b
    "cramer_lin (t := $t) (w1 := XC$j1 c - XC$i1 c) (w2 := YC$j1 c - YC$i1 c) (a1 := XC$j2 c - XC$i2 c) (a2 := YC$j2 c - YC$i2 c) (b1 := XC$j3 c - XC$i3 c) (b2 := YC$j3 c - YC$i3 c)"
end
Dne(nm, a1, a2, b1, b2) = "  have hD : $a1 * $b2 - $a2 * $b1 ≠ 0 := by\n    have h := bk_$(nm)_ne c h₁ h₂\n    unfold bk_$nm at h\n    exact h\n"
println(buf, "\ntheorem bal_15 (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : BX15 c = 0 ∧ BY15 c = 0 := by\n" *
    "  have hD : (XC14 c - XC15 c) * (YC16 c - YC15 c) - (YC14 c - YC15 c) * (XC16 c - XC15 c) ≠ 0 := by\n    have h := bk_Db_ne c h₁ h₂\n    unfold bk_Db at h\n    exact h\n" *
    "  obtain ⟨h1, h2⟩ := $(cl_inst(lr(T1), (15, 50), (15, 14), (15, 16))) hD\n" *
    "  unfold BX15 BY15 $(st(:x2)) $(st(:x3)) $(st(:x9)) bk_f2 bk_f3\n  exact ⟨by linear_combination h1, by linear_combination h2⟩")
println(buf, "\ntheorem bal_49 (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : BX49 c = 0 ∧ BY49 c = 0 := by\n" *
    "  have hD : (XC48 c - XC49 c) * (YC14 c - YC49 c) - (YC48 c - YC49 c) * (XC14 c - XC49 c) ≠ 0 := by\n    have h := bk_Dc_ne c h₁ h₂\n    unfold bk_Dc at h\n    exact h\n" *
    "  obtain ⟨h1, h2⟩ := $(cl_inst(st(:sg) * " c", (49, 50), (49, 48), (49, 14))) hD\n" *
    "  unfold BX49 BY49 $(st(:x4)) $(st(:x7)) bk_g4 bk_g7\n  exact ⟨by linear_combination h1, by linear_combination h2⟩")
println(buf, "\ntheorem bal_50 (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : BX50 c = 0 ∧ BY50 c = 0 := by\n" *
    "  have hD : (XC51 c - XC50 c) * (YC14 c - YC50 c) - (YC51 c - YC50 c) * (XC14 c - XC50 c) ≠ 0 := by\n    have h := bk_Dd_ne c h₁ h₂\n    unfold bk_Dd at h\n    exact h\n" *
    "  obtain ⟨h1, h2⟩ := $(cl_inst(st(:sg) * " c", (50, 49), (50, 51), (50, 14))) hD\n" *
    "  obtain ⟨h3, h4⟩ := $(cl_inst(lr(T1), (50, 15), (50, 51), (50, 14))) hD\n" *
    "  unfold BX50 BY50 $(st(:x6)) $(st(:x8)) $(st(:x9)) bk_h6 bk_h8 bk_j6 bk_j8\n  exact ⟨by linear_combination h1 + h3, by linear_combination h2 + h4⟩")
println(buf, "\ntheorem bal_14 (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : BX14 c = 0 ∧ BY14 c = 0 := by\n" *
      "  have hV : (XC13 c - XC14 c) * (bk_g7 c * (YC49 c - YC14 c) + bk_h8 c * (YC50 c - YC14 c)) - (YC13 c - YC14 c) * (bk_g7 c * (XC49 c - XC14 c) + bk_h8 c * (XC50 c - XC14 c)) ≠ 0 := by\n" *
    "    intro h0; apply bk_DV_ne c h₁ h₂\n    unfold bk_DV bk_Vx bk_Vy\n    linear_combination h0\n" *
    "  obtain ⟨h1, h2⟩ := blockA (A1 := XC13 c - XC14 c) (A2 := YC13 c - YC14 c) (B1 := XC15 c - XC14 c) (B2 := YC15 c - YC14 c)\n" *
    "    (C1 := XC49 c - XC14 c) (C2 := YC49 c - YC14 c) (D1 := XC50 c - XC14 c) (D2 := YC50 c - YC14 c)\n" *
    "    (t := $(lr(T1))) (f := bk_f2 c) (g := bk_g7 c) (h := bk_h8 c) (j := bk_j8 c) hV\n" *
    "  unfold BX14 BY14 $(st(:x1)) $(st(:x2)) $(st(:x7)) $(st(:x8)) $(st(:sg)) bk_rho1 bk_rhoS bk_Vx bk_Vy bk_Wx bk_Wy\n" *
    "  exact ⟨by linear_combination h1, by linear_combination h2⟩")
hk = vcat([k for (k, _, _) in HEN], [15, 49, 50, 14])
println(buf, "\ntheorem bal_base (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :\n    BX0 c = 0 ∧ BY0 c = 0 ∧ BX1 c = 0 ∧ BY1 c = 0 := by\n" *
    join(["  obtain ⟨x$k, y$k⟩ := bal_$k c h₁ h₂" for k in hk], "\n") * "\n" *
    "  have gX : $(join(["BX$k c" for k in 0:n-1], " + ")) = 0 := by\n    unfold $(join(["BX$k" for k in 0:n-1], " ")); ring\n" *
    "  have gY : $(join(["BY$k c" for k in 0:n-1], " + ")) = 0 := by\n    unfold $(join(["BY$k" for k in 0:n-1], " ")); ring\n" *
    "  have gM : $(join(["(XC$k c * BY$k c - YC$k c * BX$k c)" for k in 0:n-1], " + ")) = 0 := by\n    unfold $(join(["BX$k BY$k" for k in 0:n-1], " ")); ring\n" *
    "  have z0 : XC0 c = 0 := by unfold XC0; rfl\n" *
    "  have w0 : YC0 c = 0 := by unfold YC0; rfl\n" *
    "  have hx1 : 0 < XC1 c := pos_of_close (encX1 c h₁ h₂) (by norm_num [rho])\n" *
    "  have hu : $(pin_terms[3]) * $(pin_terms[3]) + $(pin_terms[4]) * $(pin_terms[4]) ≠ 0 := by\n" *
    "    rw [z0]; exact ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg (sub_neg.mpr hx1) (sub_neg.mpr hx1)) (mul_self_nonneg _))\n" *
    "  have hpin : BX1 c * (XC0 c - XC1 c) + BY1 c * (YC0 c - YC1 c) = 0 := by\n" *
    "    have h := pin_bal (G1 := $(pin_terms[1])) (G2 := $(pin_terms[2])) (u1 := $(pin_terms[3])) (u2 := $(pin_terms[4])) hu\n" *
    "    unfold BX1 BY1 st$(PIN-1)\n    linear_combination h\n" *
    "  rw [z0, w0] at hpin\n" *
    "  have e1 : BX0 c + BX1 c = 0 := by linear_combination gX $(join(["- x$k" for k in hk], " "))\n" *
    "  have e2 : BY0 c + BY1 c = 0 := by linear_combination gY $(join(["- y$k" for k in hk], " "))\n" *
    "  have e3 : XC1 c * BY1 c - YC1 c * BX1 c = 0 := by\n    linear_combination gM $(join(["- (XC$k c * y$k - YC$k c * x$k)" for k in hk], " ")) - BY0 c * z0 + BX0 c * w0\n" *
    "  have hne : XC1 c ^ 2 + YC1 c ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (pow_pos hx1 2) (sq_nonneg _))\n" *
    "  have hb1x : BX1 c = 0 := by\n    have hq : (XC1 c ^ 2 + YC1 c ^ 2) * BX1 c = 0 := by\n      linear_combination (-(XC1 c)) * hpin - (YC1 c) * e3\n    exact (mul_eq_zero.mp hq).resolve_left hne\n" *
    "  have hb1y : BY1 c = 0 := by\n    have hq : (XC1 c ^ 2 + YC1 c ^ 2) * BY1 c = 0 := by\n      linear_combination (-(YC1 c)) * hpin + (XC1 c) * e3\n    exact (mul_eq_zero.mp hq).resolve_left hne\n" *
    "  exact ⟨by linear_combination e1 - hb1x, by linear_combination e2 - hb1y, hb1x, hb1y⟩")
print(buf, footer())
emit("StressDef", String(take!(buf)))
prev = "$MOD.StressDef"

emit_chain("StressEnc", """**Z$n: stress enclosures.** Every stress is within an explicit radius of a
rational centre on `[clo, chi]`, by centred enclosure arithmetic on the vertex
enclosures; the proof of each follows the term of its definition.""",
    ["\ntheorem encS$(b-1) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :\n    |st$(b-1) c - $(lr(SC[b]))| ≤ $(lr(SR[b])) := $(stress_pf[b])\n" for b in order_defs], 8)

global buf = IOBuffer()
print(buf, header("**Z$n: signs of the stresses.** Every active-diameter stress is positive and the\nside stresses sum to a negative number, on `[clo, chi]`.", [prev]))
println(buf, "noncomputable def Ssum (c : ℝ) : ℝ := $(join(["st$(i) c" for i in 0:n-1], " + "))\n")
println(buf, "theorem Ssum_neg (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : Ssum c < 0 := by\n  unfold Ssum\n  exact neg_of_close $(SUM.pf) (by norm_num)")
for e in 0:m-1
    println(buf, "theorem stpos$(n+e) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : 0 < st$(n+e) c :=\n  pos_of_close (encS$(n+e) c h₁ h₂) (by norm_num)")
end
print(buf, footer())
emit("StressSign", String(take!(buf)))
prev = "$MOD.StressSign"


# ---------------------------------------------------------------------------
# Root.lean
# ---------------------------------------------------------------------------
global buf = IOBuffer()
print(buf, header("""**Z$n: the root.** `G` changes sign on `[clo, chi]`, so it has a root there (intermediate value
theorem). Its sign at each end is certified by enclosure arithmetic on the exact values of the
polynomials at that end and enclosures of `sn`, `rr` and `yv` there.""", [prev]))
println(buf, """
open Set

lemma clo_lt_chi : clo < chi := by unfold clo chi; norm_num
lemma clo_pos : 0 < clo := by unfold clo; norm_num
lemma chi_lt_one : chi < 1 := by unfold chi; norm_num
""")
for nm in ("clo", "chi")
    pt = PT[nm]
    cpt = nm == "clo" ? CLO : CHI
    println(buf, """
lemma enc_sn_$nm : |sn $nm - $(lr(pt.s0))| ≤ $(lr(pt.Ls.r)) := by
  unfold sn
  exact enc_sqrt (U0 := 1 - $nm ^ 2) (EU := 0) (E := $(lr(pt.Esq))) (by unfold $nm; norm_num) (by simp) (by norm_num)
    (by unfold $nm; norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma enc_rad_$nm : |rad $nm - $(lr(pt.rad.c))| ≤ $(lr(pt.rad.r)) := by
  unfold rad; exact $(pt.rad.pf)

lemma rad_nonneg_$nm : 0 ≤ rad $nm := nonneg_of_close enc_rad_$nm (by norm_num)

lemma enc_rr_$nm : |rr $nm - $(lr(pt.r0))| ≤ $(lr(pt.Lrr.r)) := by
  unfold rr
  exact enc_sqrt (E := $(lr(pt.rad.r + abs(pt.rad.c - pt.r0^2)))) rad_nonneg_$nm enc_rad_$nm (by norm_num)
    (by norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma enc_yv_$nm : |yv $nm - $(lr(pt.yv.c))| ≤ $(lr(pt.yv.r)) := by
  unfold yv; exact $(pt.yv.pf)
""")
    sg = pt.G.c < 0
    println(buf, "lemma G_$nm : G $nm $(sg ? "< 0" : "> 0") := by\n  unfold G\n  exact $(sg ? "neg_of_close" : "pos_of_close") $(pt.G.pf) (by norm_num)\n")
end
plnames_all = join(["pl$i" for i in eachindex(PLLIST)], " ")
lohi = sGlo < 0 ? ("G clo < 0", "0 < G chi", "intermediate_value_Ioo", "Ioo (G clo) (G chi)") :
                   ("0 < G clo", "G chi < 0", "intermediate_value_Ioo'", "Ioo (G chi) (G clo)")
println(buf, """
lemma G_continuous : Continuous G := by
  unfold G
  simp only [E2e, sn, yv, rr, rad, $(join(["pl$i" for i in eachindex(PLLIST)], ", "))]
  fun_prop

theorem G_root : ∃ c ∈ Ioo clo chi, G c = 0 := by
  have hsub := $(lohi[3]) clo_lt_chi.le G_continuous.continuousOn
  have h0 : (0 : ℝ) ∈ $(lohi[4]) := ⟨$(sGlo < 0 ? "G_clo, G_chi" : "G_chi, G_clo")⟩
  obtain ⟨c, hc, hfc⟩ := hsub h0
  exact ⟨c, hc, hfc⟩""")
print(buf, footer())
emit("Root", String(take!(buf)))
global prev = "$MOD.Root"

# ---------------------------------------------------------------------------
# Geometry.lean
# ---------------------------------------------------------------------------
fin(k) = "($k : Fin $n)"
global buf = IOBuffer()
print(buf, header("""**Z$n: the configuration and its feasibility.** `P c` is the labelled `$n`-gon, a function of
`c = cos t` alone. Strict convexity with the labelled cyclic order, every diameter at most `1`, every side
equal to `ell c = √(2 − 2c)`, and the $m declared diameters active — each assembled from the facts of the
previous files. The sides 15 and 48 need `G c = 0`.""", [prev]))
println(buf, """
/-- The `$n` vertices. -/
noncomputable def P (c : ℝ) : Fin $n → ℝ × ℝ :=
  ![$(join(["(XC$k c, YC$k c)" for k in 0:n-1], ",\n    "))]
""")
for k in 0:n-1
    println(buf, "@[simp] lemma P_$k (c : ℝ) : P c $(fin(k)) = (XC$k c, YC$k c) := rfl")
end
for k in 0:n-1
    println(buf, "@[simp] lemma succ_$k : $(fin(k)) + 1 = $(fin(mod(k+1, n))) := rfl")
end
println(buf, "\n/-- First endpoints of the active diameters. -/\ndef ea : Fin $m → Fin $n := ![$(join([a for (a, b) in active], ", "))]")
println(buf, "/-- Second endpoints of the active diameters. -/\ndef eb : Fin $m → Fin $n := ![$(join([b for (a, b) in active], ", "))]")
for e in 0:m-1
    println(buf, "@[simp] lemma ea_$e : ea ($e : Fin $m) = $(fin(active[e+1][1])) := rfl")
    println(buf, "@[simp] lemma eb_$e : eb ($e : Fin $m) = $(fin(active[e+1][2])) := rfl")
end
println(buf, """
/-- The side length `ℓ = √(2 − 2c) = 2 sin(t/2)`. -/
noncomputable def ell (c : ℝ) : ℝ := Real.sqrt (2 - 2 * c)

lemma ell_pos {c : ℝ} (h : c < 1) : 0 < ell c := Real.sqrt_pos.mpr (by linarith)
lemma ell_sq {c : ℝ} (h : c < 1) : ell c ^ 2 = 2 - 2 * c := Real.sq_sqrt (by linarith)
""")
for i in 0:n-1
    ip_ = mod(i + 1, n)
    bl = String[]
    for j in 0:n-1
        if j == i
            push!(bl, "  · exact absurd (by decide) hji")
        elseif j == ip_
            push!(bl, "  · exact absurd (by decide) hjn")
        else
            push!(bl, "  · show 0 < cross (P c $(fin(i))) (P c $(fin(ip_))) (P c $(fin(j)))\n    rw [P_$i, P_$ip_, P_$j, cross_eq]\n    exact convD_$(i)_$(j) _ h₁ h₂")
        end
    end
    println(buf, """
lemma convex_row_$i (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi)
    (j : Fin $n) (hji : j ≠ $(fin(i))) (hjn : j ≠ $(fin(i)) + 1) :
    0 < cross (P c $(fin(i))) (P c ($(fin(i)) + 1)) (P c j) := by
  rw [succ_$i] at hjn ⊢
  fin_cases j
$(join(bl, "\n"))""")
end
println(buf, """
theorem convexOrdered (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : ConvexOrdered (P c) := by
  intro i j hji hjn
  fin_cases i
$(join(["  · exact convex_row_$i c h₁ h₂ j hji hjn" for i in 0:n-1], "\n"))""")
activeidx = Dict((a, b) => e - 1 for (e, (a, b)) in enumerate(active))
for i in 0:n-1
    bl = String[]
    for j in 0:n-1
        if j <= i
            push!(bl, "  · exact absurd hij (by decide)")
        elseif haskey(activeidx, (i, j))
            push!(bl, "  · show dC $(fin(i)) $(fin(j)) (P c) ≤ 0\n    rw [dC, P_$i, P_$j]\n    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]\n    linarith [diam_$(activeidx[(i,j)]) c h₁ h₂]")
        else
            push!(bl, "  · show dC $(fin(i)) $(fin(j)) (P c) ≤ 0\n    rw [dC, P_$i, P_$j]\n    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]\n    linarith [far_$(i)_$(j) c h₁ h₂]")
        end
    end
    println(buf, """
lemma small_row_$i (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi)
    (j : Fin $n) (hij : $(fin(i)) < j) : dC $(fin(i)) j (P c) ≤ 0 := by
  fin_cases j
$(join(bl, "\n"))""")
end
sidearg(i) = SIDEKIND[i] == :E2 ? " hG" : ""
println(buf, """
theorem small (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : Small (P c) := by
  apply small_of_lt
  intro i j hij
  fin_cases i
$(join(["  · exact small_row_$i c h₁ h₂ j hij" for i in 0:n-1], "\n"))

theorem equilateral (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) (hG : G c = 0) (i : Fin $n) :
    eC i (P c, ell c) = 0 := by
  have hc1 : c < 1 := lt_of_le_of_lt h₂ chi_lt_one
  fin_cases i
$(join(["  · show nsq (P c ($(fin(i)) + 1) - P c $(fin(i))) - ell c ^ 2 = 0\n    rw [succ_$i, P_$(mod(i+1,n)), P_$i, ell_sq hc1]\n    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]\n    linarith [side_$i c h₁ h₂$(sidearg(i))]" for i in 0:n-1], "\n"))

theorem active_eq (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) (e : Fin $m) : dC (ea e) (eb e) (P c) = 0 := by
  fin_cases e
$(join(["  · show dC (ea ($(e) : Fin $m)) (eb ($(e) : Fin $m)) (P c) = 0\n    rw [ea_$e, eb_$e, dC, P_$(active[e+1][1]), P_$(active[e+1][2])]\n    simp only [nsq, ip, Prod.fst_sub, Prod.snd_sub]\n    linarith [diam_$e c h₁ h₂]" for e in 0:m-1], "\n"))""")
print(buf, footer())
emit("Geometry", String(take!(buf)))
global prev = "$MOD.Geometry"

# ---------------------------------------------------------------------------
# Main.lean
# ---------------------------------------------------------------------------
(pa_, pb_) = active[1]
barname(b) = "st$(b - 1)"
global buf = IOBuffer()
print(buf, header("""**Z$n: Theorem 3.5 applied — strict local maximality.** The multiplier identity (from the
self-stress balances, through `mult_of_stationary'`), strict positivity of the $m diameter
multipliers, `I_eq ⊆ R_eq` by Henneberg steps and one block step (`block_pin`), and the feasibility
facts of `Geometry.lean`, fed to the general `Feasible.thm_3_5`.""", [prev]))
println(buf, """
noncomputable def Av (c : ℝ) : Fin $n → ℝ := ![$(join([mA(i) * " c" for i in 0:n-1], ", "))]
noncomputable def Lv (c : ℝ) : Fin $m → ℝ := ![$(join([mL(e) * " c" for e in 0:m-1], ", "))]
""")
for i in 0:n-1; println(buf, "@[simp] lemma Av_$i (c : ℝ) : Av c $(fin(i)) = $(mA(i)) c := rfl"); end
for e in 0:m-1; println(buf, "@[simp] lemma Lv_$e (c : ℝ) : Lv c ($e : Fin $m) = $(mL(e)) c := rfl"); end
println(buf, """
lemma sum_n (f : Fin $n → ℝ) : ∑ i, f i = $(join(["f $(fin(i))" for i in 0:n-1], " + ")) := by
  simp [Fin.sum_univ_succ]; ring

lemma sum_m (g : Fin $m → ℝ) : ∑ e, g e = $(join(["g ($e : Fin $m)" for e in 0:m-1], " + ")) := by
  simp [Fin.sum_univ_succ]; ring
""")
for k in 0:n-1
    tx = String[]; ty = String[]
    for (bi, (a, b)) in enumerate(bars)
        w = barname(bi)
        sgs = b == k ? "" : a == k ? "-" : nothing
        sgs === nothing && continue
        push!(tx, "$(sgs)($w c * (XC$b c - XC$a c))")
        push!(ty, "$(sgs)($w c * (YC$b c - YC$a c))")
    end
    println(buf, """
lemma gx_$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    $(join(tx, " + ")) = 0 := by
  have h := $(k == 0 ? "(bal_base c h₁ h₂).1" : k == 1 ? "(bal_base c h₁ h₂).2.2.1" : "(bal_$k c h₁ h₂).1")
  unfold BX$k at h
  linear_combination (-1 : ℝ) * h
lemma gy_$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    $(join(ty, " + ")) = 0 := by
  have h := $(k == 0 ? "(bal_base c h₁ h₂).2.1" : k == 1 ? "(bal_base c h₁ h₂).2.2.2" : "(bal_$k c h₁ h₂).2")
  unfold BY$k at h
  linear_combination (-1 : ℝ) * h""")
end
simps = join(vcat(["P_$k" for k in 0:n-1], ["succ_$k" for k in 0:n-1], ["ea_$e" for e in 0:m-1],
                  ["eb_$e" for e in 0:m-1], ["Av_$i" for i in 0:n-1], ["Lv_$e" for e in 0:m-1]), ", ")
println(buf, """
set_option maxRecDepth 20000 in
theorem stationary (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) (v : Cfg $n) :
    (∑ i, Av c i * ip (P c (i + 1) - P c i) (v (i + 1) - v i))
      + ∑ e, Lv c e * ip (P c (eb e) - P c (ea e)) (v (eb e) - v (ea e)) = 0 := by
  rw [sum_n, sum_m]
  simp only [$simps, ip, Prod.fst_sub, Prod.snd_sub]
  linear_combination $(join(["(v $(fin(k))).1 * gx_$k c h₁ h₂ + (v $(fin(k))).2 * gy_$k c h₁ h₂" for k in 0:n-1], "\n    + "))

theorem side_sum (c : ℝ) : ∑ i, Av c i = Ssum c := by
  rw [sum_n]; simp only [$(join(["Av_$i" for i in 0:n-1], ", "))]
  rfl

theorem lam_pos (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) (e : Fin $m) : 0 < Lv c e := by
  fin_cases e
$(join(["  · show (0 : ℝ) < $(mL(e)) c\n    exact stpos$(n+e) c h₁ h₂" for e in 0:m-1], "\n"))
""")
# nonzero facts for the block
function ne_lemma(x, y)       # P c x - P c y ≠ 0, from a coordinate that differs by more than 2ρ
    dx = cx[x] - cx[y]; dy = cy[x] - cy[y]
    (coord, d) = abs(dx) >= abs(dy) ? ("X", dx) : ("Y", dy)
    guard(abs(d) > 2RHO, "P_$x - P_$y is not enclosed away from zero")
    sg = d > 0 ? "pos_of_close" : "neg_of_close"
    proj = coord == "X" ? "Prod.fst" : "Prod.snd"
    "theorem blk_ne$(x)_$(y) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : P c $(fin(x)) - P c $(fin(y)) ≠ 0 := by\n" *
    "  intro h0\n  have e := congrArg $proj h0\n" *
    "  simp only [P_$x, P_$y, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at e\n" *
    "  have hh := sub_close (enc$(coord)$(y) c h₁ h₂) (enc$(coord)$(x) c h₁ h₂)\n" *
    "  have := $sg hh (by norm_num [rho])\n  linarith\n"
end
for (x, y) in ((14, 13), (15, 16), (49, 48), (50, 51))
    println(buf, ne_lemma(x, y))
end
function blk_ip(nm, pa, pb, qa, qb, tag)   # ip (P pb - P pa) (J (P qa - P qb)) ≠ 0 from bk_nm
    "theorem blk_$tag (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :\n    ip (P c $(fin(pb)) - P c $(fin(pa))) (J (P c $(fin(qa)) - P c $(fin(qb)))) ≠ 0 := by\n" *
    "  intro h0; apply bk_$(nm)_ne c h₁ h₂\n  unfold bk_$nm\n  simp only [P_$pb, P_$pa, P_$qa, P_$qb, ip, J, Prod.fst_sub, Prod.snd_sub] at h0\n  linear_combination h0\n"
end
println(buf, blk_ip("A1", 14, 15, 15, 16, "A1"))
println(buf, blk_ip("A2", 14, 49, 49, 48, "A2"))
println(buf, blk_ip("A3", 14, 50, 50, 51, "A3"))
println(buf, """
theorem blk_K (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    ip (P c $(fin(50)) - P c $(fin(14))) (J (P c $(fin(14)) - P c $(fin(13)))) * ip (P c $(fin(50)) - P c $(fin(49))) (J (P c $(fin(50)) - P c $(fin(51)))) * ip (P c $(fin(49)) - P c $(fin(14))) (J (P c $(fin(49)) - P c $(fin(48))))
      - ip (P c $(fin(49)) - P c $(fin(14))) (J (P c $(fin(14)) - P c $(fin(13)))) * ip (P c $(fin(50)) - P c $(fin(49))) (J (P c $(fin(49)) - P c $(fin(48)))) * ip (P c $(fin(50)) - P c $(fin(14))) (J (P c $(fin(50)) - P c $(fin(51)))) ≠ 0 := by
  intro h0; apply bk_K_ne c h₁ h₂
  unfold bk_K bk_A2 bk_A3
  simp only [P_14, P_13, P_15, P_16, P_48, P_49, P_50, P_51, ip, J, Prod.fst_sub, Prod.snd_sub] at h0
  linear_combination h0
""")
println(buf, """
/-- **`I_eq ⊆ R_eq`.** Pin the first side by a rigid motion; every vertex but the block 14, 15, 49, 50
is then pinned in turn by two bars with independent directions (`henD_*`), and the block as a unit
(`block_pin`). The displacement minus the rigid motion vanishes. -/
theorem Ieq_imp_R (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi)
    (hl : ell c ≠ 0) (w : Cfg $n) (h : (dataOf (P c) (ell c) ea eb).Ieq w 0) :
    (dataOf (P c) (ell c) ea eb).R w := by
  obtain ⟨hs, hd⟩ := bars_of_Ieq hl h
  have hne : P c $(fin(0)) ≠ P c $(fin(1)) := by
    intro heq
    have := convexOrdered c h₁ h₂ $(fin(0)) $(fin(2)) (by decide) (by decide)
    rw [succ_0, heq] at this
    simp [cross_eq] at this
  have hb01 := hs $(fin(0))
  rw [succ_0] at hb01
  obtain ⟨t, ω, h0, h1⟩ := pin_bar hne hb01
  set w' : Cfg $n := fun k => w k - (t + ω • J (P c k)) with hw'
  have z0 : w' $(fin(0)) = 0 := by simp only [hw', h0, sub_self]
  have z1 : w' $(fin(1)) = 0 := by simp only [hw', h1, sub_self]""")
function barfact(k, x)
    for (i, (a, b)) in enumerate(bars)
        if (a, b) == (x, k) || (a, b) == (k, x)
            src = i <= n ? "(by have := hs $(fin(a)); rw [succ_$a] at this; exact this)" :
                           "(by have := hd ($(i - n - 1) : Fin $m); rw [ea_$(i-n-1), eb_$(i-n-1)] at this; exact this)"
            base = "(bar_sub_rigid (t := t) (ω := ω) $src)"
            return (a, b) == (x, k) ? base : "(bar_flip $base)"
        end
    end
    error("no bar between $k and $x")
end
for (k, i, j) in HEN
    println(buf, "  have z$k : w' $(fin(k)) = 0 := by\n" *
        "    apply henneberg_step (Pi := P c $(fin(i))) (Pj := P c $(fin(j))) (wi := w' $(fin(i))) (wj := w' $(fin(j)))\n" *
        "      $(barfact(k, i)) $(barfact(k, j)) z$i z$j\n" *
        "    rw [P_$k, P_$i, P_$j]\n    have hD := henD_$k c h₁ h₂\n    simp only [Prod.fst_sub, Prod.snd_sub]\n    intro h0; linarith")
end
pin0(k, x) = "(by have h : ip (P c $(fin(k)) - P c $(fin(x))) (w' $(fin(k)) - w' $(fin(x))) = 0 := $(barfact(k, x)); rw [z$x, sub_zero] at h; exact h)"
println(buf, "  obtain ⟨z14, z15, z49, z50⟩ := block_pin (Pa := P c $(fin(14))) (Pb := P c $(fin(15))) (Pc := P c $(fin(49))) (Pd := P c $(fin(50)))\n" *
    "    (Pa' := P c $(fin(13))) (Pb' := P c $(fin(16))) (Pc' := P c $(fin(48))) (Pd' := P c $(fin(51)))\n" *
    "    (wa := w' $(fin(14))) (wb := w' $(fin(15))) (wc := w' $(fin(49))) (wd := w' $(fin(50)))\n" *
    "    (blk_ne14_13 c h₁ h₂) (blk_ne15_16 c h₁ h₂) (blk_ne49_48 c h₁ h₂) (blk_ne50_51 c h₁ h₂)\n" *
    "    $(pin0(14, 13)) $(pin0(15, 16)) $(pin0(49, 48)) $(pin0(50, 51))\n" *
    "    $(barfact(15, 14)) $(barfact(49, 14)) $(barfact(50, 14)) $(barfact(50, 49))\n" *
    "    (blk_A1 c h₁ h₂) (blk_A2 c h₁ h₂) (blk_A3 c h₁ h₂) (blk_K c h₁ h₂)")
println(buf, "  refine ⟨t, ω, fun k => ?_⟩\n  show w k = t + ω • J (P c k)\n  fin_cases k\n" *
    join(["  · have := z$k; simp only [hw'] at this; exact sub_eq_zero.mp this" for k in 0:n-1], "\n"))
println(buf, """
/-- **Z$n at a root: strict local maximality, modulo Euclidean motions.** For every root `c ∈ (clo, chi)`
of `G`, `P c` is a strictly convex equilateral small `$n`-gon with side `ℓ = √(2 − 2c) > 0`, and every
feasible equilateral small `$n`-gon near it whose side is at least `ℓ` has side exactly `ℓ` and is
congruent to it. -/
theorem locally_maximal_at {c : ℝ} (hc : c ∈ Set.Ioo clo chi) (hG : G c = 0) :
    0 < ell c ∧ IsFeasibleConvex (P c, ell c) ∧
      (∀ᶠ y in nhds ((P c, ell c) : Amb $n), IsFeasible y →
        ell c ≤ y.2 → Congruent y.1 (P c) ∧ y.2 = ell c) ∧
      (∀ᶠ y in nhds ((P c, ell c) : Amb $n), IsFeasible y → y.2 ≤ ell c) := by
  have h₁ : clo ≤ c := hc.1.le
  have h₂ : c ≤ chi := hc.2.le
  have hc1 : c < 1 := lt_trans hc.2 chi_lt_one
  have hl := ell_pos hc1
  have hfeas : IsFeasibleConvex (P c, ell c) :=
    ⟨convexOrdered c h₁ h₂, small c h₁ h₂, equilateral c h₁ h₂ hG, hl⟩
  have hij : P c $(fin(pa_)) ≠ P c $(fin(pb_)) := by
    intro heq
    have h1 := active_eq c h₁ h₂ (0 : Fin $m)
    rw [ea_0, eb_0, dC, heq, sub_self] at h1
    simp [nsq, ip] at h1
  have hm := mult_of_stationary' hl.ne' ea eb (Av c) (Lv c)
    (Ssum c) (stationary c h₁ h₂) (side_sum c)
  have hkap : 0 < -(ell c * Ssum c) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hl (Ssum_neg _ h₁ h₂))
  have hmain := thm_3_5 hl hij hkap hm (lam_pos c h₁ h₂)
    (Ieq_imp_R c h₁ h₂ hl.ne') (equilateral c h₁ h₂ hG) (active_eq c h₁ h₂)
  refine ⟨hl, hfeas, hmain, ?_⟩
  filter_upwards [hmain] with y hy hf
  by_contra hlt
  push Not at hlt
  exact absurd (hy hf hlt.le).2 (ne_of_gt hlt)

/-- **Z$n is a strict local maximiser of the perimeter, modulo Euclidean motions.** There is a root
`c* ∈ (clo, chi)` of `G`, and at it the conclusions of `locally_maximal_at` hold. -/
theorem locally_maximal :
    ∃ c l : ℝ, 0 < l ∧ G c = 0 ∧ c ∈ Set.Ioo clo chi ∧
      IsFeasibleConvex (P c, l) ∧
      (∀ᶠ y in nhds ((P c, l) : Amb $n), IsFeasible y → l ≤ y.2 → Congruent y.1 (P c) ∧ y.2 = l) ∧
      (∀ᶠ y in nhds ((P c, l) : Amb $n), IsFeasible y → y.2 ≤ l) := by
  obtain ⟨c, hc, hFc⟩ := G_root
  obtain ⟨hl, hfeas, hev, hle⟩ := locally_maximal_at hc hFc
  exact ⟨c, ell c, hl, hFc, hc, hfeas, hev, hle⟩""")
print(buf, footer())
emit("Main", String(take!(buf)))
global prev = "$MOD.Main"

# root module of the case
open(joinpath(LEANOUT, "ChiquipoliFamily", "Polynomial", "Z$n.lean"), "w") do io
    print(io, "/-\nAUTO-GENERATED by `lean/generators/family/gen_z64.jl $n` — do not edit by hand.\n\nThe Lean certificate of Z$n: at every root of its equation in the certified bracket the\npolygon is a strict local maximiser of the perimeter, and a root exists; see `ChiquipoliFamily/Polynomial/Z$n/Main.lean`.\n-/\nimport $MOD.Main\n")
end
files = sort(filter(f -> endswith(f, ".lean"), readdir(OUTDIR)))
println("wrote $(length(files)) files to lean/ChiquipoliFamily/Polynomial/Z$n/: ", join(files, " "))

# ---------------------------------------------------------------------------
# negative_controls_family/Z<n>/ — the same nine controls as for Z32
# ---------------------------------------------------------------------------
# Each control is a FALSE statement about Z64, attempted with the proof the certificate
# itself uses; its twin, in twin/, is the same proof of the true statement. verify_family.sh
# requires every control to be rejected and every twin to compile, so a control cannot pass
# for an accidental reason: the twin shows the proof works, the control that it does not
# work for the false claim. Falsity is checked here, exactly or by an explicit witness.
let
    mkpath(joinpath(NCDIR, "twin"))
    for d in (NCDIR, joinpath(NCDIR, "twin")), f in readdir(d)
        endswith(f, ".lean") && rm(joinpath(d, f))
    end
    opens = "open Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family"
    function control(file, why, bad, good)
        body(kind, nm, thm) = "-- $kind\n-- AUTO-GENERATED by `lean/generators/family/gen_z64.jl $n` — do not edit by hand.\n" *
            join(["-- " * l for l in split(why, "\n")], "\n") *
            "\nimport $MOD\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 20000\nnamespace $NS\n$opens\n" * replace(thm, "THM" => nm) * "\nend $NS\n"
        open(io -> print(io, body("NEGATIVE CONTROL (Z$n). Must FAIL to compile; its twin, twin/$file.lean, must compile.", "bad", bad)),
             joinpath(NCDIR, "$file.lean"), "w")
        open(io -> print(io, body("TWIN of ../$file.lean: the same proof, of the true statement. Must COMPILE.", "good", good)),
             joinpath(NCDIR, "twin", "$file.lean"), "w")
    end
    hyp = "(c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi)"
    detS(k, i, j) = "(XC$i c - XC$k c) * (YC$j c - YC$k c) - (YC$i c - YC$k c) * (XC$j c - XC$k c)"
    detP(k, i, j) = "  have h := det_lb $(enc("X", k)) $(enc("X", i)) $(enc("X", j)) $(enc("Y", k)) $(enc("Y", i)) $(enc("Y", j))\n" *
                    "  have hn : (0 : ℝ) < $(margin_expr(cx[k], cx[i], cx[j], cy[k], cy[i], cy[j])) := by\n" *
                    "    unfold rho; norm_num [abs_of_pos, abs_of_neg]\n  linarith"

    # 1. a support determinant with the wrong sign
    @assert det_margin(cx[0], cx[1], cx[2], cy[0], cy[1], cy[2]) > 0
    control("fnc01_convexity_sign",
        "The support determinant (0,1,2) claimed NEGATIVE, by the certificate's own\nproof (det_lb from the enclosures). It is positive on the whole bracket.",
        "theorem THM $hyp :\n    $(detS(0, 1, 2)) < 0 := by\n$(detP(0, 1, 2))",
        "theorem THM $hyp :\n    0 < $(detS(0, 1, 2)) := by\n$(detP(0, 1, 2))")

    # 2. the tightest inactive pair, claimed further below 1 than it is
    (fi, fj) = farpairs[argmax([far_ub(i, j) for (i, j) in farpairs])]
    dlo = max(abs(cx[fj] - cx[fi]) - 2RHO, 0)^2 + max(abs(cy[fj] - cy[fi]) - 2RHO, 0)^2
    T = QQ(floor(BigInt, (dlo - QQ(1, 10^6)) * 10^6), 10^6)
    @assert 0 < T < dlo
    farS(bound) = "theorem THM $hyp :\n    (XC$fj c - XC$fi c) * (XC$fj c - XC$fi c) + (YC$fj c - YC$fi c) * (YC$fj c - YC$fi c) < $bound := by\n" *
        "  have h := sqd_ub0 $(enc("X", fi)) $(enc("X", fj)) $(enc("Y", fi)) $(enc("Y", fj))\n" *
        "  have hn : (|$(lr(cx[fj])) - $(lr(cx[fi]))| + 2 * rho) ^ 2 + (|$(lr(cy[fj])) - $(lr(cy[fi]))| + 2 * rho) ^ 2 < $bound := by\n" *
        "    unfold rho; norm_num [abs_of_pos, abs_of_neg]\n  nlinarith [h, hn]"
    control("fnc02_inactive_margin",
        "The tightest inactive pair, ($fi,$fj), is at squared distance about $(round(Float64(dlo), digits = 8)).\nClaimed below $(Float64(T)), by the certificate's proof: the margin to 1 is real, not slack.",
        farS(lr(T)), farS("1"))

    # 3. a side that needs G, proved for every c
    @assert SIDEKIND[15] == :E2 && SIDEKIND[0] == :U
    sideS(i) = (j = mod(i + 1, n); gn = pl_names(i, j);
        "theorem THM $hyp :\n    (XC$j c - XC$i c) * (XC$j c - XC$i c) + (YC$j c - YC$i c) * (YC$j c - YC$i c) = 2 - 2 * c := by\n  have hs := sn_sq c h₁ h₂\n  simp only [$(join(vcat(["XC$i", "XC$j", "YC$i", "YC$j"], gn), ", "))]\n  linear_combination ($(lp3(SIDEQ[i]))) * hs")
    control("fnc03_side_needs_G",
        "Side 15 is one of the sides (15 and 48) that hold only at a root of G, and 13, 50 follow\nfrom the first equation. Claimed for every c, by the proof of an unconditional side\n(`linear_combination` with the cofactor of s² = 1 − c² alone); the twin is side 0, which is unconditional.",
        sideS(15), sideS(0))

    # 4. the smallest diameter stress with the wrong sign
    bmin = n + argmin([SC[b] - SR[b] for b in n+1:n+m])
    @assert SC[bmin] - SR[bmin] > 0
    stS(claim) = "theorem THM $hyp : $claim := by\n  have h := encS$(bmin-1) c h₁ h₂\n  have := (abs_le.mp h).1\n  linarith"
    control("fnc04_stress_sign",
        "st$(bmin-1), the smallest active-diameter stress, is certified in [$(Float64(SC[bmin]-SR[bmin])), $(Float64(SC[bmin]+SR[bmin]))].\nClaimed non-positive from that same enclosure: the multiplier sign is not free.",
        stS("st$(bmin-1) c ≤ 0"), stS("0 < st$(bmin-1) c"))

    # 5. rigidity from the sides alone
    rigS(h, arg) = "theorem THM $hyp\n    (hl : ell c ≠ 0) (w : Cfg $n) ($h) :\n    (dataOf (P c) (ell c) ea eb).R w := by\n  exact Ieq_imp_R c h₁ h₂ hl w $arg"
    control("fnc05_rigidity_needs_bars",
        "Infinitesimal rigidity from the $n SIDE constraints alone. A $n-gon with free\ndiameters has a $(2n - n - 3)-dimensional space of non-trivial flexes, so this is false;\nthe Henneberg and block steps must not go through without the diameter bars.",
        rigS("hs : ∀ i, (dataOf (P c) (ell c) ea eb).sideD w 0 i = 0", "⟨hs, fun e => by simp [Data.diamD]⟩"),
        rigS("hs : (dataOf (P c) (ell c) ea eb).Ieq w 0", "hs"))

    # 6. the wrong sign of G at the lower end of the bracket
    sg6 = PT["clo"].G.c < 0
    control("fnc06_root_sign",
        "G at clo claimed with the opposite sign. The sign is certified by enclosure arithmetic on\nexact values and enclosures of sn, rr, yv there; the bracket brackets a root only with the true signs.",
        "theorem THM : $(sg6 ? "0 < G clo" : "G clo < 0") := by\n  unfold G\n  exact $(sg6 ? "pos_of_close" : "neg_of_close") $(PT["clo"].G.pf) (by norm_num)",
        "theorem THM : $(sg6 ? "G clo < 0" : "0 < G clo") := by\n  unfold G\n  exact $(sg6 ? "neg_of_close" : "pos_of_close") $(PT["clo"].G.pf) (by norm_num)")

    # 7. the bracket is not empty
    @assert CLO < CHI
    control("fnc07_bracket_nonempty",
        "Every sign fact of the certificate is stated for c in [clo, chi]. Were that\ninterval empty, all of them would be vacuous. It is not.",
        "theorem THM : chi < clo := by\n  unfold clo chi; norm_num", "theorem THM : clo < chi := by\n  unfold clo chi; norm_num")

    # 8. a degenerate Henneberg step
    (hk, hi, hj) = HEN[1]
    control("fnc08_henneberg_degenerate",
        "Vertex $hk, the first one the Henneberg construction adds, pinned by two bars to\nthe SAME vertex $hi instead of to $hi and $hj. The determinant is identically 0; the\nsame proof must not certify it positive.",
        "theorem THM $hyp :\n    0 < $(detS(hk, hi, hi)) := by\n$(detP(hk, hi, hi))",
        "theorem THM $hyp :\n    0 < $(detS(hk, hi, hj)) := by\n$(detP(hk, hi, hj))")

    # 9. an enclosure tighter than the truth
    cands9 = [(max(abs(peval(PLLIST[i], CLO) - plenc(i)[1]), abs(peval(PLLIST[i], CHI) - plenc(i)[1])), i) for i in eachindex(PLLIST) if length(PLLIST[i]) >= 2]
    (dev, ke) = maximum(cands9)
    eps = QQ(floor(BigInt, dev / 2 * big(10)^40), big(10)^40)
    @assert 0 < eps < dev
    tE = taylor_steps("pl$ke", PLLIST[ke])
    control("fnc09_enclosure_tight",
        "The enclosure of pl$ke claimed with radius $(Float64(eps)), half the distance the polynomial\nactually reaches from the centre at an end of the bracket. The certified radius is not slack\neither way: the twin is the certificate's.",
        replace(encl_text("THM", "pl$ke", tE..., plenc(ke)[1], lr(eps)), r"^\n?lemma" => "theorem"),
        replace(encl_text("THM", "pl$ke", tE..., plenc(ke)[1], lr(plenc(ke)[2])), r"^\n?lemma" => "theorem"))

    println("wrote 9 negative controls and their twins to lean/negative_controls_family/Z$n/")
end
