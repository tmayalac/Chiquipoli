# Generate the Lean certificate of a member A_n of the Bingane–Audet family.
#
#     julia --project=. lean/generators/family/gen_family.jl 32
#
# writes lean/ChiquipoliFamily/A32/*.lean. The general lemmas every file relies
# on are in lean/ChiquipoliFamily/Basic.lean, proved once for all n.
#
# SOURCE OF TRUTH. The exact coordinates are those of `audet_coords_cs(n)` in
# cases/exact_coords.jl (the generic OPTIGON constructor, cross-checked against
# upstream in test/literature.jl), reduced here to the form
# `p_k = (sin z · XC_k(c), YC_k(c))` with XC_k, YC_k ∈ Q[c] by EXACT division —
# asserted, never assumed. `Fc` is `audet_Fc(n)` (Proposition 1). The active
# graph and the constructor root are those of cases/A<n>_bingane_audet.
#
# WHAT LEAN CHECKS, AND HOW (see Basic.lean for the method):
#   Poly.lean   the polynomials, the rational interval [clo, chi] around c*
#   Encl.lean   |XC_k(c) − x̂_k| ≤ ρ, |YC_k(c) − ŷ_k| ≤ ρ  (centred Taylor)
#               and every diameter multiplier λ_e(c) > 0    (centred Taylor)
#   Conv*.lean  every support determinant > 0               (det_lb + norm_num)
#   Far*.lean   every non-active pair at distance < 1       (sqd_ub + norm_num)
#   Exact.lean  sides, active diameters, stationarity rows, Σα = −1   (ring)
#   Hen.lean    the n − 2 Henneberg determinants ≠ 0         (det_lb + norm_num)
#   Root.lean   Fc has a root in (clo, chi)                  (IVT, norm_num)
#   Geometry.lean, Main.lean   the configuration, its feasibility, the multiplier
#               identity, I_eq ⊆ R_eq, and Theorem 3.5 applied: strict local
#               maximality modulo Euclidean motions.
#
# Every margin is checked here in exact rational arithmetic BEFORE any Lean is
# written, so a Lean failure can only mean a transcription or tactic problem,
# never a margin that does not hold.

const REPO = normpath(joinpath(@__DIR__, "..", "..", ".."))
include(joinpath(REPO, "src", "A16Certificate.jl"));  using .A16Certificate
include(joinpath(REPO, "src", "ExactIdentity.jl"));   using .ExactIdentity
include(joinpath(REPO, "src", "SmallPolygons.jl"));   using .SmallPolygons
include(joinpath(REPO, "cases", "exact_coords.jl"))
include(joinpath(@__DIR__, "multipliers_n.jl"));      using .MultipliersN
using IntervalArithmetic

const QQ = Rational{BigInt}
setprecision(BigFloat, 512)

n = parse(Int, ARGS[1])
const OUTDIR = joinpath(REPO, "lean", "ChiquipoliFamily", "A$n")
const NS = "Chiquipoli.Family.A$n"
const MOD = "ChiquipoliFamily.A$n"
const CONV_CHUNK = 60
const FAR_CHUNK = 80

# ---------------------------------------------------------------------------
# Exact data
# ---------------------------------------------------------------------------
cand = include(joinpath(REPO, "cases", n == 16 ? "A16_bingane_audet" : "A$(n)_bingane_audet", "candidate.jl"))
active = cand.active
m = length(active)
@assert m == n - 1

function exdiv(a, d)
    q, r = EI.pdivrem(a, d)
    @assert EI.iszeropoly(r) "coordinate is not a polynomial: division not exact"
    return QQ.(EI.ptrim(q))
end
P = audet_coords_cs(n)
XC = Vector{Vector{QQ}}(undef, n); YC = similar(XC)
for k in 1:n
    x, y = P[k]
    @assert EI.iszeropoly(x.A) && EI.iszeropoly(y.B) "vertex $(k-1) is not of the form (s·X, Y)"
    XC[k] = exdiv(x.B, x.den); YC[k] = exdiv(y.A, y.den)
end
Fc, _ = audet_Fc(n); Fc = QQ.(Fc)

zstar = BigFloat(cand.root.nominal)
cstar = cos(zstar)
let v = sum(Fc[i] * cstar^(i-1) for i in eachindex(Fc)); println("Fc(c*) = ", Float64(v), "  max coef = ", Float64(maximum(abs.(Fc)))); @assert abs(v) < big"1e-30" "the nominal root is not a root of Fc" end   # sanity only: the root itself is certified by the IVT in Root.lean

pm(a, b) = QQ.(EI.pmul(a, b)); pa(a, b) = QQ.(EI.padd(a, b)); ps(a, b) = QQ.(EI.psub(a, b))
ONE_M_C2 = QQ[1, 0, -1]
sqdpoly(i, j) = pa(pm(ONE_M_C2, pm(ps(XC[j+1], XC[i+1]), ps(XC[j+1], XC[i+1]))),
                   pm(ps(YC[j+1], YC[i+1]), ps(YC[j+1], YC[i+1])))
detpoly(k, i, j) = ps(pm(ps(XC[i+1], XC[k+1]), ps(YC[j+1], YC[k+1])),
                      pm(ps(YC[i+1], YC[k+1]), ps(XC[j+1], XC[k+1])))   # (Xi−Xk)(Yj−Yk) − (Yi−Yk)(Xj−Xk)
peval(p, x) = sum(p[i] * x^(i-1) for i in eachindex(p))

# ---- the rational interval around c* -----------------------------------------
function simplest(lo, hi)
    q = 1
    while true
        p_ = ceil(BigInt, lo * q); p_ <= hi * q && return QQ(p_, q); q += 1
    end
end
W = big"1e-9"
CLO = simplest(cstar - W, cstar - W/4); CHI = simplest(cstar + W/4, cstar + W)
C0 = simplest(cstar - W/8, cstar + W/8); R0 = max(C0 - CLO, CHI - C0)
SB = 1 - CLO^2                                   # sin² z = 1 − c² ≤ 1 − clo²  (c ≥ clo > 0)
@assert CLO > 0
sFclo = sign(peval(Fc, CLO)); sFchi = sign(peval(Fc, CHI))
@assert sFclo * sFchi < 0 "Fc does not change sign on [clo, chi]"

# ---- Taylor data -------------------------------------------------------------
function taylor(p, c0)
    d = length(p) - 1; t = zeros(QQ, d + 1)
    for k in 0:d, j in k:d; t[k+1] += p[j+1] * binomial(big(j), big(k)) * c0^(j - k); end
    t
end
tail(t) = length(t) > 1 ? sum(abs(t[j+1]) * R0^j for j in 1:length(t)-1) : QQ(0)
G = big(10)^18
rdn(x) = QQ(floor(BigInt, x * G), G); rup(x) = QQ(ceil(BigInt, x * G), G)

cx = Dict{Int,QQ}(); cy = Dict{Int,QQ}(); rho = QQ(0)
for k in 0:n-1
    tx = taylor(XC[k+1], C0); ty = taylor(YC[k+1], C0)
    cx[k] = rdn(tx[1]); cy[k] = rdn(ty[1])
    global rho = max(rho, abs(tx[1] - cx[k]) + tail(tx), abs(ty[1] - cy[k]) + tail(ty))
end
RHO = rup(2rho)

# ---- sign-layer margins, all checked exactly here ------------------------------
function det_margin(x0, x1, x2, y0, y1, y2)
    r2 = 2RHO
    ((x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)) -
        (abs(x1 - x0) * r2 + abs(y2 - y0) * r2 + r2 * r2) -
        (abs(y1 - y0) * r2 + abs(x2 - x0) * r2 + r2 * r2)
end
triples = [(i, mod(i + 1, n), j) for i in 0:n-1 for j in 0:n-1 if j != i && j != mod(i + 1, n)]
conv_m = [det_margin(cx[i], cx[ip], cx[j], cy[i], cy[ip], cy[j]) for (i, ip, j) in triples]
@assert minimum(conv_m) > 0 "a support determinant is not certified by the enclosures"

activeset = Set(active)
farpairs = [(i, j) for i in 0:n-1 for j in i+1:n-1 if !((i, j) in activeset)]
far_ub(i, j) = SB * (abs(cx[j] - cx[i]) + 2RHO)^2 + (abs(cy[j] - cy[i]) + 2RHO)^2
@assert maximum(far_ub(i, j) for (i, j) in farpairs) < 1 "an inactive pair is not certified below 1"

# ---- exact identities ----------------------------------------------------------
side_quot = Dict{Int,Union{Nothing,Vector{QQ}}}()
for i in 0:n-1
    R = ps(sqdpoly(i, mod(i + 1, n)), QQ[2, -2])
    if EI.iszeropoly(R); side_quot[i] = nothing
    else
        q, r = EI.pdivrem(R, Fc); @assert EI.iszeropoly(r) "side $i does not reduce by Fc"
        side_quot[i] = QQ.(EI.ptrim(q))
    end
end
for (i, j) in active
    @assert EI.iszeropoly(ps(sqdpoly(i, j), QQ[1])) "active diameter ($i,$j) is not identically 1"
end

# ---- multipliers: exact witness, positive representative ------------------------
kapex = n ÷ 2                               # apex (0, 1): y differs from y_0
omit = [1, 2, 2kapex + 1]; pin = n + 4
solve(v) = MultipliersN.exact_multipliers(XC, YC, Fc, active; pin_index = pin, pin_value = QQ[QQ(v)], omit = omit)
s0 = solve(0); s1 = solve(1)
L0 = [peval(s0.y[n+e], cstar) for e in 1:m]; L1 = [peval(s1.y[n+e], cstar) for e in 1:m]
lo_mu = big(-Inf); hi_mu = big(Inf)
for e in 1:m
    sl = L1[e] - L0[e]
    if sl > 0; global lo_mu = max(lo_mu, -L0[e] / sl)
    elseif sl < 0; global hi_mu = min(hi_mu, -L0[e] / sl)
    else; @assert L0[e] > 0; end
end
@assert lo_mu < hi_mu "no strictly positive multiplier representative"
mu = simplest(lo_mu + (hi_mu - lo_mu) * 3 / 8, hi_mu - (hi_mu - lo_mu) * 3 / 8)
sol = solve(mu)
Y = [QQ.(p) for p in sol.y]                 # Y[1:n] side weights A_i, Y[n+1:n+m] diameter weights
lam_lb = Dict{Int,QQ}()
for e in 1:m
    t = taylor(Y[n+e], C0)
    lb = t[1] - tail(t)
    @assert lb > 0 "diameter multiplier $e is not certified positive"
    lam_lb[e] = QQ(floor(BigInt, lb * big(10)^12), big(10)^12)
    @assert lam_lb[e] > 0
end

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
        @assert mg > 0 "Henneberg step at vertex $k is not certified"
        push!(done, k); push!(order, (k, i, j))
    end
    @assert ok "no Henneberg order from bar ($a,$b)"
    global best = order
end
HEN = best

println("A$n:  [clo,chi] = [$CLO, $CHI]  width $(Float64(CHI - CLO))   ρ = $(Float64(RHO))")
println("  convexity: $(length(triples)) determinants, worst certified margin $(Float64(minimum(conv_m)))")
println("  inactive:  $(length(farpairs)) pairs, worst certified bound $(Float64(maximum(far_ub(i,j) for (i,j) in farpairs)))")
println("  multipliers: pin μ = $mu, worst certified λ ≥ $(Float64(minimum(values(lam_lb))))")
println("  Henneberg: $(length(HEN)) steps, worst margin $(Float64(minimum(hmargin(k,i,j) for (k,i,j) in HEN)))")
println("  sides needing Fc: $([i for i in 0:n-1 if side_quot[i] !== nothing])   deg Fc = $(length(Fc)-1)")

# ---------------------------------------------------------------------------
# Lean emission helpers
# ---------------------------------------------------------------------------
lr(q::QQ) = denominator(q) == 1 ? (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
            (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" : "($(numerator(q))/$(denominator(q)))")
lr(q::Integer) = lr(QQ(q))
function lp(p, var = "c")
    p = QQ.(EI.ptrim(p)); EI.iszeropoly(p) && return "0"
    d = length(p) - 1; d == 0 && return lr(p[1]); e = lr(p[d+1])
    for k in d-1:-1:0; e = p[k+1] == 0 ? "($e) * $var" : "($e) * $var + $(lr(p[k+1]))"; end
    e
end
mA(i) = "mA$i"; mL(e) = "mL$e"               # e is 0-based in Lean names
header(doc, imports) = """/-
AUTO-GENERATED by `lean/generators/family/gen_family.jl $n` — do not edit by hand.

$doc
-/
$(join(["import $im" for im in imports], "\n"))

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

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
function encl_lemma(name, pname, p, ctr)
    t, deg, rhs, steps, tl = taylor_steps(pname, p)
    if deg == 0
        return """
lemma $name (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |$pname c - $(lr(ctr))| ≤ rho := by
  unfold $pname rho; norm_num
"""
    end
    """
lemma $name (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |$pname c - $(lr(ctr))| ≤ rho := by
  have key : $pname c = $rhs := by
    unfold $pname c0; ring
  have hr : |c - c0| ≤ r0 := near c h₁ h₂
$steps
  have hnum : |($(lr(t[1])) : ℝ) - $(lr(ctr))| + ($tl) ≤ rho := by
    unfold r0 rho; norm_num
  have e1 := neg_abs_le (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  have e2 := le_abs_self (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  rw [key, abs_le]
  constructor <;> linarith
"""
end
function lb_lemma(name, pname, p, lb; lo = "clo", hi = "chi", cn = "c0", rn = "r0", nr = "near", C = C0, R = R0)
    t, deg, rhs, steps, tl = taylor_steps(pname, p; cn = cn, rn = rn, C = C, R = R)
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
# Poly.lean
# ---------------------------------------------------------------------------
global buf = IOBuffer()
print(buf, header("""**A$n: the polynomial layer.** Every vertex of the Bingane–Audet `$n`-gon is
`p_k = (sin z · XC_k(cos z), YC_k(cos z))` with `XC_k, YC_k ∈ Q[c]` (exact
division by `cos 2z`, asserted by the generator). `Fc` is the constructor
equation reduced to `c = cos z` (Proposition 1); `mA_i`, `mL_e` are the exact
multiplier witness, as elements of `Q[c]/(Fc)`. `[clo, chi]` is a rational
interval of width about `10⁻⁹` around the root; `c0`, `r0` centre it.""",
    ["ChiquipoliFamily.Basic"]))
println(buf, """
noncomputable def clo : ℝ := $(lr(CLO))
noncomputable def chi : ℝ := $(lr(CHI))
noncomputable def c0 : ℝ := $(lr(C0))
noncomputable def r0 : ℝ := $(lr(R0))
/-- Uniform radius of the vertex enclosures. -/
noncomputable def rho : ℝ := $(lr(RHO))
/-- Upper bound for `sin² z = 1 − cos² z` on the interval. -/
noncomputable def sb : ℝ := $(lr(SB))

lemma near (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : |c - c0| ≤ r0 :=
  near_of (by unfold c0 r0 clo; norm_num) (by unfold c0 r0 chi; norm_num) h₁ h₂

lemma sin2_bounds (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : 0 ≤ 1 - c ^ 2 ∧ 1 - c ^ 2 ≤ sb := by
  unfold clo chi sb at *
  constructor <;> nlinarith
""")
for k in 0:n-1
    println(buf, "noncomputable def XC$k (c : ℝ) : ℝ := ", lp(XC[k+1]))
    println(buf, "noncomputable def YC$k (c : ℝ) : ℝ := ", lp(YC[k+1]))
end
println(buf, "\n/-- The constructor equation in `c = cos z`. -/\nnoncomputable def Fc (c : ℝ) : ℝ := ", lp(Fc))
for i in 0:n-1; println(buf, "noncomputable def $(mA(i)) (c : ℝ) : ℝ := ", lp(Y[i+1])); end
for e in 0:m-1; println(buf, "noncomputable def $(mL(e)) (c : ℝ) : ℝ := ", lp(Y[n+e+1])); end
print(buf, footer())
emit("Poly", String(take!(buf)))

# ---------------------------------------------------------------------------
# Encl*.lean, Lam*.lean
# ---------------------------------------------------------------------------
prev = "$MOD.Poly"
emit_chain("Encl", """**A$n: vertex enclosures.** Each vertex coordinate polynomial is within
`rho` of a rational centre on `[clo, chi]`. Centred Taylor expansion at `c0`: one
`ring` identity per polynomial, then one bound per term (`tbound`).""",
    [s_ for k in 0:n-1 for s_ in (encl_lemma("encX$k", "XC$k", XC[k+1], cx[k]),
                                  encl_lemma("encY$k", "YC$k", YC[k+1], cy[k]))], 32)
emit_chain("Lam", """**A$n: the diameter multipliers are positive.** Each `mL_e` is bounded
below by a positive rational on `[clo, chi]`, by centred Taylor expansion.""",
    [lb_lemma("lam_lb$(e-1)", mL(e-1), Y[n+e], lam_lb[e]) for e in 1:m], 4)

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
for (ci, ch) in enumerate(conv_chunks)
    local buf = IOBuffer()
    print(buf, header("**A$n: support determinants, part $ci of $(length(conv_chunks)).** Each is positive on\n`[clo, chi]`, from the vertex enclosures by `det_lb`.", [prev]))
    for (i, ip, j) in ch
        println(buf, """
theorem convD_$(i)_$(j) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
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
# Far*.lean
# ---------------------------------------------------------------------------
far_chunks = collect(Iterators.partition(farpairs, FAR_CHUNK))
for (fi, ch) in enumerate(far_chunks)
    local buf = IOBuffer()
    print(buf, header("**A$n: non-active pairs, part $fi of $(length(far_chunks)).** Each is at squared distance\n`< 1`, from the vertex enclosures by `sqd_ub`.", [prev]))
    for (i, j) in ch
        println(buf, """
theorem far_$(i)_$(j) (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) :
    (1 - c ^ 2) * (XC$j c - XC$i c) ^ 2 + (YC$j c - YC$i c) ^ 2 < 1 := by
  obtain ⟨hs0, hs⟩ := sin2_bounds c h₁ h₂
  have h := sqd_ub $(enc("X", i)) $(enc("X", j)) $(enc("Y", i)) $(enc("Y", j)) hs0 hs
  have hn : sb * (|$(lr(cx[j])) - $(lr(cx[i]))| + 2 * rho) ^ 2 + (|$(lr(cy[j])) - $(lr(cy[i]))| + 2 * rho) ^ 2 < 1 := by
    unfold sb rho; norm_num [abs_of_pos, abs_of_neg]
  linarith""")
    end
    print(buf, footer())
    emit("Far$fi", String(take!(buf)))
    global prev = "$MOD.Far$fi"
end

# ---------------------------------------------------------------------------
# Sides*.lean, Rows*.lean  (the exact identities)
# ---------------------------------------------------------------------------
barname(b) = b <= n ? mA(b - 1) : mL(b - n - 1)
side_pieces = String[]
for i in 0:n-1
    j = mod(i + 1, n)
    lhs = "(1 - c ^ 2) * (XC$j c - XC$i c) ^ 2 + (YC$j c - YC$i c) ^ 2 = 2 - 2 * c"
    if side_quot[i] === nothing
        push!(side_pieces, "\ntheorem side_$i (c : ℝ) (hF : Fc c = 0) :\n    $lhs := by\n  unfold XC$i XC$j YC$i YC$j; ring\n")
    else
        push!(side_pieces, "\ntheorem side_$i (c : ℝ) (hF : Fc c = 0) :\n    $lhs := by\n  unfold XC$i XC$j YC$i YC$j\n  unfold Fc at hF\n  linear_combination ($(lp(side_quot[i]))) * hF\n")
    end
end
for (e, (i, j)) in enumerate(active)
    push!(side_pieces, "\ntheorem diam_$(e-1) (c : ℝ) :\n    (1 - c ^ 2) * (XC$j c - XC$i c) ^ 2 + (YC$j c - YC$i c) ^ 2 = 1 := by\n  unfold XC$i XC$j YC$i YC$j; ring\n")
end
emit_chain("Sides", """**A$n: sides and active diameters, exactly.** All $n sides equal `2 − 2c`
in squared length — all but $(count(!isnothing, values(side_quot))) for every `c`, those at a root of `Fc` —
and all $m active diameters are identically `1`. `ring` / `linear_combination`.""", side_pieces, 16)

# stationarity rows: at vertex k, Σ over bars (a→b) incident to k of ±weight·Δ
function row_terms(k, coord)
    t = String[]
    for (bi, (a, b)) in enumerate(bars)
        w = barname(bi)
        if b == k; push!(t, "$w c * ($(coord)$b c - $(coord)$a c)")
        elseif a == k; push!(t, "-($w c * ($(coord)$b c - $(coord)$a c))"); end
    end
    join(t, " + ")
end
rowquot(k, coord) = sol.quot[coord == "XC" ? 2k + 1 : 2k + 2]
row_pieces = String[]
for k in 0:n-1, coord in ("XC", "YC")
    ws = unique([barname(bi) for (bi, (a, b)) in enumerate(bars) if a == k || b == k])
    ps_ = unique([s_ for (a, b) in bars if a == k || b == k for s_ in ("$coord$a", "$coord$b")])
    push!(row_pieces, "\ntheorem row_$(coord)_$k (c : ℝ) (hF : Fc c = 0) :\n    $(row_terms(k, coord)) = 0 := by\n" *
        "  unfold $(join(ws, " ")) $(join(ps_, " "))\n  unfold Fc at hF\n  linear_combination ($(lp(rowquot(k, coord)))) * hF\n")
end
push!(row_pieces, "\ntheorem alpha_sum (c : ℝ) (hF : Fc c = 0) :\n    $(join([mA(i) * " c" for i in 0:n-1], " + ")) = -1 := by\n" *
    "  unfold $(join([mA(i) for i in 0:n-1], " "))\n  unfold Fc at hF\n  linear_combination ($(lp(-sol.quot[2n+1]))) * hF\n")
emit_chain("Rows", """**A$n: the stationarity rows.** At every vertex the weighted bar vectors of
the exact multiplier witness balance, in both coordinates, and the side weights
sum to `−1`; each identity is a multiple of `Fc`.""", row_pieces, 8)

# ---------------------------------------------------------------------------
# Hen.lean
# ---------------------------------------------------------------------------
global buf = IOBuffer()
print(buf, header("**A$n: the Henneberg determinants.** Pin side `0 → 1`; then each vertex, in\nthe order below, is joined to two pinned vertices by bars with independent\ndirections. Each determinant is positive on `[clo, chi]` by `det_lb`.", [prev]))
for (k, i, j) in HEN
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
# Root.lean
# ---------------------------------------------------------------------------
lohi = sFclo < 0 ? ("Fc clo < 0", "0 < Fc chi", "intermediate_value_Ioo", "Ioo (Fc clo) (Fc chi)") :
                   ("0 < Fc clo", "Fc chi < 0", "intermediate_value_Ioo'", "Ioo (Fc chi) (Fc clo)")
global buf = IOBuffer()
print(buf, header("**A$n: the root.** `Fc` changes sign on `[clo, chi]`, so it has a root there\n(intermediate value theorem). Both signs are exact rational evaluations.", [prev]))
println(buf, """
open Set

lemma clo_lt_chi : clo < chi := by unfold clo chi; norm_num
lemma clo_pos : 0 < clo := by unfold clo; norm_num
lemma chi_lt_one : chi < 1 := by unfold chi; norm_num
lemma Fc_continuous : Continuous Fc := by unfold Fc; fun_prop
lemma Fc_clo : $(lohi[1]) := by unfold Fc clo; norm_num
lemma Fc_chi : $(lohi[2]) := by unfold Fc chi; norm_num

theorem Fc_root : ∃ c ∈ Ioo clo chi, Fc c = 0 := by
  have hsub := $(lohi[3]) clo_lt_chi.le Fc_continuous.continuousOn
  have h0 : (0 : ℝ) ∈ $(lohi[4]) := ⟨$(sFclo < 0 ? "Fc_clo, Fc_chi" : "Fc_chi, Fc_clo")⟩
  obtain ⟨c, hc, hfc⟩ := hsub h0
  exact ⟨c, hc, hfc⟩""")
print(buf, footer())
emit("Root", String(take!(buf)))
prev = "$MOD.Root"

# ---------------------------------------------------------------------------
# Geometry.lean
# ---------------------------------------------------------------------------
fin(k) = "($k : Fin $n)"
global buf = IOBuffer()
print(buf, header("""**A$n: the configuration and its feasibility.** `P z` is the labelled
`$n`-gon in reduced form. Strict convexity with the labelled cyclic order, every
diameter at most `1`, every side equal to `2 sin(z/2)`, and the $m declared
diameters active — each assembled from the polynomial facts of the previous
files.""", [prev]))
println(buf, """
/-- The `$n` vertices, `p_k = (sin z · XC_k(cos z), YC_k(cos z))`. -/
noncomputable def P (z : ℝ) : Fin $n → ℝ × ℝ :=
  ![$(join(["(Real.sin z * XC$k (Real.cos z), YC$k (Real.cos z))" for k in 0:n-1], ",\n    "))]
""")
for k in 0:n-1
    println(buf, "@[simp] lemma P_$k (z : ℝ) : P z $(fin(k)) = (Real.sin z * XC$k (Real.cos z), YC$k (Real.cos z)) := rfl")
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
lemma pyth (z : ℝ) : Real.sin z ^ 2 = 1 - Real.cos z ^ 2 := by
  linear_combination Real.sin_sq_add_cos_sq z

/-- The side length `ℓ = 2 sin(z/2)`. -/
noncomputable def L (z : ℝ) : ℝ := 2 * Real.sin (z / 2)
""")
# convexity rows
for i in 0:n-1
    ip = mod(i + 1, n)
    bl = String[]
    for j in 0:n-1
        if j == i
            push!(bl, "  · exact absurd (by decide) hji")
        elseif j == ip
            push!(bl, "  · exact absurd (by decide) hjn")
        else
            push!(bl, "  · show 0 < cross (P z $(fin(i))) (P z $(fin(ip))) (P z $(fin(j)))\n    rw [P_$i, P_$ip, P_$j, cross_reduced]\n    exact mul_pos hsz (convD_$(i)_$(j) _ h₁ h₂)")
        end
    end
    println(buf, """
lemma convex_row_$i (z : ℝ) (hsz : 0 < Real.sin z) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi)
    (j : Fin $n) (hji : j ≠ $(fin(i))) (hjn : j ≠ $(fin(i)) + 1) :
    0 < cross (P z $(fin(i))) (P z ($(fin(i)) + 1)) (P z j) := by
  rw [succ_$i] at hjn ⊢
  fin_cases j
$(join(bl, "\n"))""")
end
println(buf, """
theorem convexOrdered (z : ℝ) (hsz : 0 < Real.sin z) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi) :
    ConvexOrdered (P z) := by
  intro i j hji hjn
  fin_cases i
$(join(["  · exact convex_row_$i z hsz h₁ h₂ j hji hjn" for i in 0:n-1], "\n"))""")
# smallness rows
activeidx = Dict((a, b) => e - 1 for (e, (a, b)) in enumerate(active))
for i in 0:n-1
    bl = String[]
    for j in 0:n-1
        if j <= i
            push!(bl, "  · exact absurd hij (by decide)")
        elseif haskey(activeidx, (i, j))
            push!(bl, "  · show dC $(fin(i)) $(fin(j)) (P z) ≤ 0\n    rw [dC, P_$i, P_$j, nsq_reduced _ _ _ _ _ _ (pyth z), diam_$(activeidx[(i,j)])]\n    norm_num")
        else
            push!(bl, "  · show dC $(fin(i)) $(fin(j)) (P z) ≤ 0\n    rw [dC, P_$i, P_$j, nsq_reduced _ _ _ _ _ _ (pyth z)]\n    linarith [far_$(i)_$(j) _ h₁ h₂]")
        end
    end
    println(buf, """
lemma small_row_$i (z : ℝ) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi)
    (j : Fin $n) (hij : $(fin(i)) < j) : dC $(fin(i)) j (P z) ≤ 0 := by
  fin_cases j
$(join(bl, "\n"))""")
end
println(buf, """
theorem small (z : ℝ) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi) : Small (P z) := by
  apply small_of_lt
  intro i j hij
  fin_cases i
$(join(["  · exact small_row_$i z h₁ h₂ j hij" for i in 0:n-1], "\n"))

theorem equilateral (z : ℝ) (hF : Fc (Real.cos z) = 0) (i : Fin $n) : eC i (P z, L z) = 0 := by
  fin_cases i
$(join(["  · show nsq (P z ($(fin(i)) + 1) - P z $(fin(i))) - L z ^ 2 = 0\n    rw [succ_$i, P_$(mod(i+1,n)), P_$i, nsq_reduced _ _ _ _ _ _ (pyth z), L, sq_two_sin_half, side_$i _ hF]\n    ring" for i in 0:n-1], "\n"))

theorem active_eq (z : ℝ) (e : Fin $m) : dC (ea e) (eb e) (P z) = 0 := by
  fin_cases e
$(join(["  · show dC (ea ($(e) : Fin $m)) (eb ($(e) : Fin $m)) (P z) = 0\n    rw [ea_$e, eb_$e, dC, P_$(active[e+1][1]), P_$(active[e+1][2]), nsq_reduced _ _ _ _ _ _ (pyth z), diam_$e]\n    ring" for e in 0:m-1], "\n"))""")
print(buf, footer())
emit("Geometry", String(take!(buf)))
prev = "$MOD.Geometry"

# ---------------------------------------------------------------------------
# Main.lean
# ---------------------------------------------------------------------------
(pa_, pb_) = active[1]
global buf = IOBuffer()
print(buf, header("""**A$n: Theorem 3.5 applied — strict local maximality.** The multiplier
identity (from the stationarity rows, through `mult_of_stationary`), strict
positivity of the $m diameter multipliers, `I_eq ⊆ R_eq` by the Henneberg
construction, and the feasibility facts of `Geometry.lean`, fed to the general
`Feasible.thm_3_5`.""", [prev]))
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
# vertex balance in actual coordinates
for k in 0:n-1
    tx = String[]; ty = String[]
    for (bi, (a, b)) in enumerate(bars)
        w = barname(bi)
        sgn = b == k ? "" : a == k ? "-" : nothing
        sgn === nothing && continue
        push!(tx, "$(sgn)($w (Real.cos z) * ((Real.sin z * XC$b (Real.cos z)) - (Real.sin z * XC$a (Real.cos z))))")
        push!(ty, "$(sgn)($w (Real.cos z) * (YC$b (Real.cos z) - YC$a (Real.cos z)))")
    end
    println(buf, """
lemma gx_$k (z : ℝ) (hF : Fc (Real.cos z) = 0) :
    $(join(tx, " + ")) = 0 := by
  linear_combination Real.sin z * row_XC_$k (Real.cos z) hF
lemma gy_$k (z : ℝ) (hF : Fc (Real.cos z) = 0) :
    $(join(ty, " + ")) = 0 := by
  linear_combination row_YC_$k (Real.cos z) hF""")
end
simps = join(vcat(["P_$k" for k in 0:n-1], ["succ_$k" for k in 0:n-1], ["ea_$e" for e in 0:m-1],
                  ["eb_$e" for e in 0:m-1], ["Av_$i" for i in 0:n-1], ["Lv_$e" for e in 0:m-1]), ", ")
println(buf, """
set_option maxRecDepth 20000 in
theorem stationary (z : ℝ) (hF : Fc (Real.cos z) = 0) (v : Cfg $n) :
    (∑ i, Av (Real.cos z) i * ip (P z (i + 1) - P z i) (v (i + 1) - v i))
      + ∑ e, Lv (Real.cos z) e * ip (P z (eb e) - P z (ea e)) (v (eb e) - v (ea e)) = 0 := by
  rw [sum_n, sum_m]
  simp only [$simps, ip, Prod.fst_sub, Prod.snd_sub]
  linear_combination $(join(["(v $(fin(k))).1 * gx_$k z hF + (v $(fin(k))).2 * gy_$k z hF" for k in 0:n-1], "\n    + "))

theorem alpha_total (z : ℝ) (hF : Fc (Real.cos z) = 0) : ∑ i, Av (Real.cos z) i = -1 := by
  rw [sum_n]; simp only [$(join(["Av_$i" for i in 0:n-1], ", "))]
  exact alpha_sum _ hF

theorem lam_pos (z : ℝ) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi) (e : Fin $m) :
    0 < Lv (Real.cos z) e := by
  fin_cases e
$(join(["  · show (0 : ℝ) < $(mL(e)) (Real.cos z)\n    linarith [lam_lb$e (Real.cos z) h₁ h₂]" for e in 0:m-1], "\n"))

theorem L_pos {z : ℝ} (h0 : 0 < z) (hpi : z < Real.pi) : 0 < L z := by
  unfold L
  have := Real.sin_pos_of_pos_of_lt_pi (x := z / 2) (by linarith) (by linarith [Real.pi_pos])
  linarith

/-- **`I_eq ⊆ R_eq`, by a Henneberg construction.** Pin the first side by a rigid
motion; then every other vertex is pinned in turn by two bars with independent
directions (`henD_*`). The displacement minus the rigid motion vanishes. -/
theorem Ieq_imp_R (z : ℝ) (hsz : 0 < Real.sin z) (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi)
    (hl : L z ≠ 0) (w : Cfg $n) (h : (dataOf (P z) (L z) ea eb).Ieq w 0) :
    (dataOf (P z) (L z) ea eb).R w := by
  obtain ⟨hs, hd⟩ := bars_of_Ieq hl h
  have hne : P z $(fin(0)) ≠ P z $(fin(1)) := by
    intro heq
    have := convexOrdered z hsz h₁ h₂ $(fin(0)) $(fin(2)) (by decide) (by decide)
    rw [succ_0, heq] at this
    simp [cross_eq] at this
  have hb01 := hs $(fin(0))
  rw [succ_0] at hb01
  obtain ⟨t, ω, h0, h1⟩ := pin_bar hne hb01
  set w' : Cfg $n := fun k => w k - (t + ω • J (P z k)) with hw'
  have z0 : w' $(fin(0)) = 0 := by simp only [hw', h0, sub_self]
  have z1 : w' $(fin(1)) = 0 := by simp only [hw', h1, sub_self]""")
# bar facts for each Henneberg step, as ip (P k − P x) (w' k − w' x) = 0
function barfact(k, x)
    # find the bar between k and x
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
        "    apply henneberg_step (Pi := P z $(fin(i))) (Pj := P z $(fin(j))) (wi := w' $(fin(i))) (wj := w' $(fin(j)))\n" *
        "      $(barfact(k, i)) $(barfact(k, j)) z$i z$j\n" *
        "    rw [P_$k, P_$i, P_$j, det_reduced]\n" *
        "    exact (mul_pos hsz (henD_$k _ h₁ h₂)).ne'")
end
println(buf, "  refine ⟨t, ω, fun k => ?_⟩\n  show w k = t + ω • J (P z k)\n  fin_cases k\n" *
    join(["  · have := z$k; simp only [hw'] at this; exact sub_eq_zero.mp this" for k in 0:n-1], "\n"))
println(buf, """
/-- **A$n at a root: strict local maximality, modulo Euclidean motions.** For every
root `c ∈ (clo, chi)` of the constructor equation, at `z = arccos c` the
configuration `P z` is a strictly convex equilateral small `$n`-gon with side
`ℓ = 2 sin(z/2) > 0`, and every feasible equilateral small `$n`-gon near it whose
side is at least `ℓ` has side exactly `ℓ` and is congruent to it. -/
theorem locally_maximal_at {c : ℝ} (hc : c ∈ Set.Ioo clo chi) (hFc : Fc c = 0) :
    0 < L (Real.arccos c) ∧ IsFeasibleConvex (P (Real.arccos c), L (Real.arccos c)) ∧
      (∀ᶠ y in nhds ((P (Real.arccos c), L (Real.arccos c)) : Amb $n), IsFeasible y →
        L (Real.arccos c) ≤ y.2 → Congruent y.1 (P (Real.arccos c)) ∧ y.2 = L (Real.arccos c)) ∧
      (∀ᶠ y in nhds ((P (Real.arccos c), L (Real.arccos c)) : Amb $n), IsFeasible y →
        y.2 ≤ L (Real.arccos c)) := by
  have hlo : (-1 : ℝ) < c := by have := hc.1; have := clo_pos; linarith
  have hhi : c < 1 := by have := hc.2; have := chi_lt_one; linarith
  set z := Real.arccos c with hz
  have hcos : Real.cos z = c := Real.cos_arccos hlo.le hhi.le
  have hsz : 0 < Real.sin z := by
    rw [hz, Real.sin_arccos]; exact Real.sqrt_pos.mpr (by nlinarith)
  have h0 : 0 < z := by
    rcases (Real.arccos_nonneg c).lt_or_eq with h | h
    · exact h
    · exact absurd hsz (by rw [hz, ← h]; simp)
  have hpi : z < Real.pi := by
    rcases (Real.arccos_le_pi c).lt_or_eq with h | h
    · exact h
    · exact absurd hsz (by rw [hz, h]; simp)
  have hF : Fc (Real.cos z) = 0 := by rw [hcos]; exact hFc
  have h₁ : clo ≤ Real.cos z := by rw [hcos]; exact hc.1.le
  have h₂ : Real.cos z ≤ chi := by rw [hcos]; exact hc.2.le
  have hl := L_pos h0 hpi
  have hfeas : IsFeasibleConvex (P z, L z) :=
    ⟨convexOrdered z hsz h₁ h₂, small z h₁ h₂, equilateral z hF, hl⟩
  have hij : P z $(fin(pa_)) ≠ P z $(fin(pb_)) := by
    intro heq
    have h1 := active_eq z (0 : Fin $m)
    rw [ea_0, eb_0, dC, heq, sub_self] at h1
    simp [nsq, ip] at h1
  have hm := mult_of_stationary hl.ne' ea eb (Av (Real.cos z)) (Lv (Real.cos z))
    (stationary z hF) (alpha_total z hF)
  have hmain := thm_3_5 hl hij hl hm (lam_pos z h₁ h₂)
    (Ieq_imp_R z hsz h₁ h₂ hl.ne') (equilateral z hF) (active_eq z)
  refine ⟨hl, hfeas, hmain, ?_⟩
  filter_upwards [hmain] with y hy hf
  by_contra hlt
  push Not at hlt
  exact absurd (hy hf hlt.le).2 (ne_of_gt hlt)

/-- **A$n is a strict local maximiser of the perimeter, modulo Euclidean motions.**
There is a root `c* ∈ (clo, chi)` of the constructor equation, and at
`z = arccos c*` the conclusions of `locally_maximal_at` hold. -/
theorem locally_maximal :
    ∃ z l : ℝ, 0 < l ∧ Fc (Real.cos z) = 0 ∧ Real.cos z ∈ Set.Ioo clo chi ∧
      IsFeasibleConvex (P z, l) ∧
      (∀ᶠ y in nhds ((P z, l) : Amb $n), IsFeasible y → l ≤ y.2 → Congruent y.1 (P z) ∧ y.2 = l) ∧
      (∀ᶠ y in nhds ((P z, l) : Amb $n), IsFeasible y → y.2 ≤ l) := by
  obtain ⟨c, hc, hFc⟩ := Fc_root
  have hcos : Real.cos (Real.arccos c) = c :=
    Real.cos_arccos (by have := hc.1; have := clo_pos; linarith) (by have := hc.2; have := chi_lt_one; linarith)
  obtain ⟨hl, hfeas, hev, hle⟩ := locally_maximal_at hc hFc
  exact ⟨Real.arccos c, L (Real.arccos c), hl, by rw [hcos]; exact hFc, by rw [hcos]; exact hc,
    hfeas, hev, hle⟩""")
print(buf, footer())
emit("Main", String(take!(buf)))
prev = "$MOD.Main"

# ---------------------------------------------------------------------------
# Unique.lean — the root is the only one in the article's search interval
# ---------------------------------------------------------------------------
# Search interval in z: (2 arcsin(sin(π/n)/2), π/n). In c = cos z it is
# (cos(π/n), (1 + cos²(π/n))/2), since cos(2 arcsin a) = 1 − 2a².
# cos(π/n) = sqrtTwoAddSeries 0 k / 2 with n = 2^(k+1) (Mathlib), bounded level
# by level with exact rationals.
kk = Int(log2(n)) - 1
GS = big(10)^24
lvl_lo = QQ[]; lvl_hi = QQ[]
let lo = QQ(0), hi = QQ(0)
    for j in 1:kk
        l_ = QQ(floor(BigInt, sqrt(BigFloat(2 + lo)) * GS), GS)
        u_ = QQ(ceil(BigInt, sqrt(BigFloat(2 + hi)) * GS), GS)
        @assert l_^2 < 2 + lo && u_^2 > 2 + hi
        push!(lvl_lo, l_); push!(lvl_hi, u_); lo, hi = l_, u_
    end
end
cosHi_lo = lvl_lo[end] / 2; cosHi_hi = lvl_hi[end] / 2      # bounds on cos(π/n)
SLO = cosHi_lo
SHI = (1 + cosHi_hi^2) / 2
@assert cosHi_hi <= CLO "the certified bracket does not lie above cos(π/n)"
@assert CHI <= (1 + cosHi_lo^2) / 2 "the certified bracket does not lie below cos(searchLo)"
dF = QQ[Fc[k+1] * k for k in 1:length(Fc)-1]
CS0 = simplest((SLO + SHI) / 2 - (SHI - SLO) / 16, (SLO + SHI) / 2 + (SHI - SLO) / 16)
RS0 = max(CS0 - SLO, SHI - CS0)
sgn = Int(sign(peval(dF, cstar)))   # an Int: a Float here would leak into the exact arithmetic
tdf = taylor(QQ(sgn) .* dF, CS0)
dlb = tdf[1] - sum(abs(tdf[j+1]) * RS0^j for j in 1:length(tdf)-1)
@assert dlb > 0 "Fc' is not certified of one sign on the search bracket"
DLB = QQ(floor(BigInt, dlb * 9 / 10 * big(10)^18), big(10)^18)
@assert DLB > 0
println("  uniqueness: search bracket [$(Float64(SLO)), $(Float64(SHI))], sign(Fc') = $sgn, |Fc'| ≥ $(Float64(DLB))")

# HasDerivAt chain for the Horner form written by `lp`
function deriv_chain(p)
    p = QQ.(EI.ptrim(p)); d = length(p) - 1
    t = "((hasDerivAt_id' (x := c)).const_mul ($(lr(p[d+1])) : ℝ))"
    p[d] != 0 && (t = "($t.add_const ($(lr(p[d])) : ℝ))")
    for k in d-2:-1:0
        t = "($t.mul (hasDerivAt_id' (x := c)))"
        p[k+1] != 0 && (t = "($t.add_const ($(lr(p[k+1])) : ℝ))")
    end
    t
end
dname = sgn > 0 ? "dFc" : "ndFc"
Ek(j) = j == 1 ? "√2" : "√(2 + $(Ek(j-1)))"
buf = IOBuffer()
print(buf, header("""**A$n: the root is unique in the article's search interval.** `Fc` is
strictly monotone on a rational bracket `[slo, shi]` (its derivative keeps one
sign there, by a centred Taylor bound), and the search interval
`(2 arcsin(sin(π/$n)/2), π/$n)` maps into that bracket under `cos` — using
`cos(π/2^(k+1)) = sqrtTwoAddSeries 0 k / 2` from Mathlib, bounded level by level
by exact rationals, and `cos(2 arcsin a) = 1 − 2a²`.""", [prev, "Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse", "Mathlib.Analysis.Calculus.Deriv.MeanValue"]))
println(buf, """
open Set Real

noncomputable def slo : ℝ := $(lr(SLO))
noncomputable def shi : ℝ := $(lr(SHI))
noncomputable def cs0 : ℝ := $(lr(CS0))
noncomputable def rs0 : ℝ := $(lr(RS0))

lemma nears (c : ℝ) (h₁ : slo ≤ c) (h₂ : c ≤ shi) : |c - cs0| ≤ rs0 :=
  near_of (by unfold cs0 rs0 slo; norm_num) (by unfold cs0 rs0 shi; norm_num) h₁ h₂

/-- The derivative of `Fc`, as an explicit polynomial. -/
noncomputable def dFc (c : ℝ) : ℝ := $(lp(dF))
$(sgn > 0 ? "" : "noncomputable def ndFc (c : ℝ) : ℝ := $(lp(-dF))\nlemma ndFc_eq (c : ℝ) : ndFc c = -dFc c := by unfold ndFc dFc; ring\n")
theorem hasDerivAt_Fc (c : ℝ) : HasDerivAt Fc (dFc c) c := by
  unfold Fc dFc
  exact $(deriv_chain(Fc)).congr_deriv (by simp only [Pi.mul_apply]; ring)
""")
print(buf, lb_lemma("dFc_lb", dname, QQ(sgn) .* dF, DLB; lo = "slo", hi = "shi", cn = "cs0", rn = "rs0", nr = "nears", C = CS0, R = RS0))
mono = sgn > 0 ? "StrictMonoOn" : "StrictAntiOn"
println(buf, """
theorem Fc_mono_search : $mono Fc (Icc slo shi) := by
  refine $(sgn > 0 ? "strictMonoOn_of_deriv_pos" : "strictAntiOn_of_deriv_neg") (convex_Icc _ _) Fc_continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_Fc x).deriv]
  have := dFc_lb x hx.1.le hx.2.le
  $(sgn > 0 ? "linarith" : "rw [ndFc_eq] at this; linarith")

/-- `Fc` has at most one root on `[slo, shi]`. -/
theorem Fc_root_unique_search {x y : ℝ} (hx : x ∈ Icc slo shi) (hy : y ∈ Icc slo shi)
    (hfx : Fc x = 0) (hfy : Fc y = 0) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := Fc_mono_search hx hy h; rw [hfx, hfy] at this; exact absurd this (lt_irrefl 0)
  · exact h
  · have := Fc_mono_search hy hx h; rw [hfx, hfy] at this; exact absurd this (lt_irrefl 0)

/-- The article's search interval, lower end. -/
noncomputable def searchLo : ℝ := 2 * Real.arcsin (Real.sin (π / $n) / 2)
/-- The article's search interval, upper end. -/
noncomputable def searchHi : ℝ := π / $n

/-- `cos(π/$n)`, bounded through Mathlib's nested radical. -/
lemma cos_searchHi : ($(lr(cosHi_lo)) : ℝ) < Real.cos searchHi ∧ Real.cos searchHi < $(lr(cosHi_hi)) := by
  have e : searchHi = π / 2 ^ ($kk + 1) := by unfold searchHi; norm_num
  rw [e, Real.cos_pi_over_two_pow]
  simp only [Real.sqrtTwoAddSeries, add_zero]""")
for j in 1:kk
    prevlo = j == 1 ? "0" : lr(lvl_lo[j-1]); prevhi = j == 1 ? "0" : lr(lvl_hi[j-1])
    println(buf, "  have hl$j : ($(lr(lvl_lo[j])) : ℝ) < $(Ek(j)) := by
" *
        "    rw [Real.lt_sqrt (by norm_num)]
" *
        (j == 1 ? "    norm_num" : "    have : ($(lr(lvl_lo[j])) : ℝ) ^ 2 < 2 + $prevlo := by norm_num
    linarith [hl$(j-1)]"))
    println(buf, "  have hu$j : $(Ek(j)) < ($(lr(lvl_hi[j])) : ℝ) := by
" *
        "    rw [Real.sqrt_lt' (by norm_num)]
" *
        (j == 1 ? "    norm_num" : "    have : 2 + $prevhi < ($(lr(lvl_hi[j])) : ℝ) ^ 2 := by norm_num
    linarith [hu$(j-1)]"))
end
println(buf, """  constructor <;> linarith

lemma sin_searchHi_pos : 0 < Real.sin (π / $n) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by have := Real.pi_pos; linarith)

lemma searchLo_pos : 0 < searchLo := by
  unfold searchLo
  have := sin_searchHi_pos
  have : 0 < Real.arcsin (Real.sin (π / $n) / 2) := Real.arcsin_pos.mpr (by linarith)
  linarith

lemma searchHi_le_pi : searchHi ≤ π := by
  unfold searchHi; have := Real.pi_pos; linarith

lemma searchLo_le_pi : searchLo ≤ π := by
  unfold searchLo; have := Real.arcsin_le_pi_div_two (Real.sin (π / $n) / 2); linarith

/-- `cos(2 arcsin a) = 1 − 2a²` with `a = sin(π/$n)/2`, i.e. `(1 + cos²(π/$n))/2`. -/
lemma cos_searchLo : Real.cos searchLo = (1 + Real.cos searchHi ^ 2) / 2 := by
  set a := Real.sin (π / $n) / 2 with ha
  have ha1 : a ≤ 1 := by have := Real.sin_le_one (π / $n); rw [ha]; linarith
  have ham : -1 ≤ a := by have := Real.neg_one_le_sin (π / $n); rw [ha]; linarith
  have hsin : Real.sin (Real.arcsin a) = a := Real.sin_arcsin ham ha1
  have hcos : Real.cos searchLo = 1 - 2 * a ^ 2 := by
    unfold searchLo; rw [← ha, Real.cos_two_mul', Real.cos_sq', hsin]; ring
  rw [hcos, ha, searchHi]
  have := Real.sin_sq_add_cos_sq (π / $n)
  nlinarith

/-- Every angle of the search interval has its cosine in `[slo, shi]`. -/
theorem cos_mem_of_search {z : ℝ} (hz : z ∈ Ioo searchLo searchHi) : Real.cos z ∈ Icc slo shi := by
  obtain ⟨h1, h2⟩ := hz
  have hlo := searchLo_pos
  have hHi := searchHi_le_pi
  have hc1 : Real.cos searchHi < Real.cos z := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hHi h2
  have hc2 : Real.cos z < Real.cos searchLo := Real.cos_lt_cos_of_nonneg_of_le_pi hlo.le (by linarith) h1
  obtain ⟨b1, b2⟩ := cos_searchHi
  rw [cos_searchLo] at hc2
  constructor
  · unfold slo; linarith
  · unfold shi; nlinarith

/-- The certified bracket `(clo, chi)` lies inside the search interval, in `c`. -/
lemma bracket_in_search : Real.cos searchHi < clo ∧ chi < Real.cos searchLo := by
  obtain ⟨b1, b2⟩ := cos_searchHi
  rw [cos_searchLo]
  constructor
  · unfold clo; linarith
  · unfold chi; nlinarith

/-- **A$n, with Proposition 6.2(1)'s uniqueness.** The certified configuration comes
from a root of the constructor equation that lies in the article's search
interval and is the only root there; it is a strictly convex equilateral small
`$n`-gon and a strict local maximiser of the perimeter, modulo Euclidean motions. -/
theorem locally_maximal_unique :
    ∃ z l : ℝ, 0 < l ∧ z ∈ Ioo searchLo searchHi ∧ Fc (Real.cos z) = 0 ∧
      (∀ z' ∈ Ioo searchLo searchHi, Fc (Real.cos z') = 0 → z' = z) ∧
      IsFeasibleConvex (P z, l) ∧
      (∀ᶠ y in nhds ((P z, l) : Amb $n), IsFeasible y → l ≤ y.2 → Congruent y.1 (P z) ∧ y.2 = l) ∧
      (∀ᶠ y in nhds ((P z, l) : Amb $n), IsFeasible y → y.2 ≤ l) := by
  obtain ⟨c, hc, hFc⟩ := Fc_root
  obtain ⟨hl, hfeas, hev, hle⟩ := locally_maximal_at hc hFc
  obtain ⟨bH, bL⟩ := bracket_in_search
  have hcm1 : (-1 : ℝ) ≤ c := by have := hc.1; have := clo_pos; linarith
  have hc1 : c ≤ 1 := by have := hc.2; have := chi_lt_one; linarith
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hcm1 hc1
  have hHi0 : 0 ≤ searchHi := by unfold searchHi; positivity
  have hmem : Real.arccos c ∈ Ioo searchLo searchHi := by
    constructor
    · have h := Real.arccos_lt_arccos hcm1 (by linarith [hc.2]) (Real.cos_le_one searchLo)
      rwa [Real.arccos_cos searchLo_pos.le searchLo_le_pi] at h
    · have h := Real.arccos_lt_arccos (Real.neg_one_le_cos searchHi) (by linarith [hc.1]) hc1
      rwa [Real.arccos_cos hHi0 searchHi_le_pi] at h
  refine ⟨Real.arccos c, L (Real.arccos c), hl, hmem, by rw [hcos]; exact hFc, ?_, hfeas, hev, hle⟩
  intro z' hz' hF'
  have hc' := cos_mem_of_search hz'
  have hcz := cos_mem_of_search hmem
  have heq : Real.cos z' = Real.cos (Real.arccos c) :=
    Fc_root_unique_search hc' hcz hF' (by rw [hcos]; exact hFc)
  have hsub : ∀ w ∈ Ioo searchLo searchHi, w ∈ Icc 0 π := fun w hw =>
    ⟨by linarith [hw.1, searchLo_pos], by linarith [hw.2, searchHi_le_pi]⟩
  exact Real.injOn_cos (hsub z' hz') (hsub _ hmem) heq""")
print(buf, footer())
emit("Unique", String(take!(buf)))
prev = "$MOD.Unique"

# root module of the case
open(joinpath(REPO, "lean", "ChiquipoliFamily", "A$n.lean"), "w") do io
    print(io, "/-\nAUTO-GENERATED by `lean/generators/family/gen_family.jl $n` — do not edit by hand.\n\nThe Lean certificate of A$n; see `ChiquipoliFamily/A$n/Unique.lean`.\n-/\nimport $MOD.Unique\n")
end
files = sort(filter(f -> endswith(f, ".lean"), readdir(OUTDIR)))
println("wrote $(length(files)) files to lean/ChiquipoliFamily/A$n/: ", join(files, " "))
