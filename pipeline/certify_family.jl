# The family certificate of one Bingane–Audet polygon A_n (n in FAMILY_N,
# cases/exact_coords.jl: 16, 32, ..., 1024): the same gates as the dedicated A16
# certificate, plus the published source.
#
#     julia --project=. pipeline/certify_family.jl 32        # or: make a32
#
# writes results/family/A32.toml (CHIQUI_NO_RECORD=1: prints only) and exits 1
# unless the verdict is CERTIFIED.
#
# WHY THIS EXISTS. A16 has a dedicated interval certificate with eight gates
# (pipeline/certify_a16.jl); A32 and A64 had only the general certifier, which
# checks six blocks, reports root uniqueness nowhere, encloses no side length
# and checks no box nesting. This script gives every member of the family the
# same gates, computed the same way, and one more that A16's dedicated
# certificate does not have: the published constructor itself, run unchanged.
#
# THE GATES (all enter the verdict):
#   published_constructor  upstream OPTIGON source, byte-identical (SHA-256), run in
#                          exact arithmetic: every vertex and the equation F equal
#                          the certified ones EXACTLY          (cases/optigon_exact.jl)
#   exact_identities       n sides and n-1 active diameters, exactly, in Q(c,s)
#   root                   interval Newton on Z_root: 0 ∉ F'(Z), N(Z) ⊂ int Z
#   root_unique_search     0 ∉ Fc' on a rational bracket containing cos(I_search)
#                          (centred interval evaluation), so Fc is monotone there;
#                          F = LEAD·Fc(cos z) exactly, so F has one zero on I_search
#   side_length            ℓ = 2 sin(z/2) and n·ℓ enclosed over Z_root
#   convexity              every support determinant > 0 over Z_cert
#   inactive_margin        declared actives at distance 1, every other pair < 1
#   rank                   rank D(e,d) = 2n-2 over Z_cert (I_eq = R_eq)
#   multipliers            Krawczyk-enclosed, every diameter multiplier > 0
#   box_nesting            Z_root ⊂ int Z_cert, by endpoints

const ROOT = normpath(joinpath(@__DIR__, ".."))
include(joinpath(ROOT, "src", "A16Certificate.jl"));  using .A16Certificate
include(joinpath(ROOT, "src", "ExactIdentity.jl"));   using .ExactIdentity
include(joinpath(ROOT, "src", "SmallPolygons.jl"));   using .SmallPolygons
include(joinpath(ROOT, "cases", "exact_coords.jl"))
using IntervalArithmetic, Dates, SHA, TOML
include(joinpath(ROOT, "cases", "optigon_exact.jl"))

setprecision(BigFloat, 256)
const QQ = Rational{BigInt}
const ROOT_RADIUS = big"1e-30"
const CERT_RADIUS = big"1e-28"

n = length(ARGS) == 1 ? parse(Int, ARGS[1]) : error("usage: certify_family.jl <n>, n in $(FAMILY_N)")
n in FAMILY_N || error("n must be one of $(FAMILY_N) (cases/exact_coords.jl, FAMILY_N)")
# The same path for every n: the generic constructor (the one the published
# source is compared with exactly, below), the candidate's active graph and
# nominal root, and exact identities from the generic Q(c,s) instance. For
# n = 16 this deliberately does NOT use the dedicated A16 constructor, so that
# A16 is certified here exactly as A32 and A64 are.
base = include(joinpath(ROOT, "cases", "family", "A$(n)", "candidate.jl"))
let Pn = BigFloat(π) / n
    global cand = Candidate("A$(n)-family", n, audet_coords(n),
        (F = audet_F(n), lo = 2 * asin(sin(Pn) / 2), hi = Pn, nominal = base.root.nominal),
        base.active,
        Dict{Symbol,Any}(:exact => sb -> begin
            (co, Fc_, st, dt, zb) = audet_cs(n, base.root.nominal)
            EI.prove_all(co, n, base.active, st, dt, Fc_, sb === nothing ? zb : sb)
        end))
end

gates = Dict{String,Any}[]
gate(id, pass, detail; extra...) = (push!(gates, Dict{String,Any}("id" => id, "passed" => pass,
    "status" => pass ? "CERTIFIED" : "FAIL", "detail" => detail, (string(k) => string(v) for (k, v) in extra)...));
    println(rpad(id, 24), pass ? "PASS  " : "FAIL  ", detail); pass)

println("="^78)
println("FAMILY CERTIFICATE — A$n (Bingane–Audet), every gate of the A16 certificate + the published source")
println("="^78)

# --- published_constructor ------------------------------------------------------
pub = optigon_exact(n)
gate("published_constructor", pub.sha_ok && pub.vertices_ok && pub.F_ok,
     "upstream cstrt_audet_ngon.jl, SHA-256 $(pub.sha_ok ? "as recorded" : "CHANGED"), run unchanged in exact Q(c,s): " *
     "vertices $(pub.vertices_ok ? "all equal" : "differ at $(pub.mismatch)"), F $(pub.F_ok ? "equal" : "differs")";
     sha256 = pub.sha)

# --- F = LEAD · Fc(cos z), exactly (used by the root gates) ---------------------
Fc, den = audet_Fc(n)
Fcs = audet_F_generic(n, cs_sin, cs_cos, cs_const, _AUDET_CS_OPS)
g = EI.pgcd(Fcs.A, Fcs.den)
AoverG = QQ.(EI.ptrim(first(EI.pdivrem(Fcs.A, g))))
rGD = QQ(g[1]) / QQ(Fcs.den[1])
LEAD = AoverG[end] * rGD
F_is_LEAD_Fc = EI.iszeropoly(Fcs.B) && QQ.(EI.ptrim(g)) == rGD .* QQ.(EI.ptrim(Fcs.den)) && AoverG ./ AoverG[end] == Fc
dFc = QQ[Fc[k+1] * k for k in 1:length(Fc)-1]
pev(p, x) = (v = zero(x); for c in reverse(p); v = v * x + interval(BigFloat, c); end; v)
# The same polynomial evaluated in the basis centred at c0 = mid(x): the
# coefficients of p(c0 + t) are computed by repeated synthetic division in
# interval arithmetic at 256 + 4·deg bits (enough to absorb the cancellation of
# the shift, whose intermediate terms reach ~4^deg), and only then is the small
# interval t = x - c0 substituted. Horner in the monomial basis over an
# interval multiplies its width by roughly Σ|k·p_k|·|x|^k, which for n ≥ 128
# (degree ≳ 64, coefficients ~ 4^deg) swamps the value; in the centred basis the
# width is multiplied only by the first Taylor coefficients. Every step is
# outward rounded, so the result is an enclosure of p(x) like `pev`'s.
function pev_centred(p, x)
    d = length(p)
    c0 = mid(x)                                        # a float: exact as a point
    q = setprecision(BigFloat, precision(BigFloat) + 4d) do
        q = [interval(BigFloat, QQ(c)) for c in p]
        c0I = interval(BigFloat, c0)
        for i in 1:d-1, j in d-1:-1:i
            q[j] += c0I * q[j+1]
        end
        q
    end
    t = x - interval(BigFloat, c0)
    v = zero(x)
    for c in reverse(q); v = v * t + c; end
    return v
end
qev(p, x) = (v = zero(QQ); for c in reverse(p); v = v * x + c; end; v)

# --- root: interval Newton on Z_root --------------------------------------------
z0 = cand.root.nominal
Zroot = interval(z0 - ROOT_RADIUS, z0 + ROOT_RADIUS)
Fnum = cand.root.F
m = interval(mid(Zroot))
Fm = Fnum(m)
Dz = -interval(BigFloat, LEAD) * sin(Zroot) * pev_centred(dFc, cos(Zroot))    # F'(z) = -LEAD sin z Fc'(cos z)
Nz = m - Fm / Dz
newton_ok = F_is_LEAD_Fc && !in_interval(0, Dz) && isinterior(Nz, Zroot) && isguaranteed(Nz)
gate("root", newton_ok,
     "interval Newton on Z_root (radius 1e-30): 0 ∉ F'(Z) = $(Dz), N(Z) ⊂ int Z = $(isinterior(Nz, Zroot)); " *
     "F' from the exact identity F = $(LEAD)·Fc(cos z) = $(F_is_LEAD_Fc)")

# --- root_unique_search: Fc strictly monotone on a rational bracket ⊇ cos(I_search)
# 0 ∉ Fc'([ra, rb]) (centred interval evaluation) makes Fc strictly monotone on
# [ra, rb], so it has at most one root there; cos is injective on I_search ⊂ (0, π)
# and F = LEAD·Fc(cos z) exactly with cos 2z ≠ 0, so F has at most one zero on
# I_search, and the Newton root (inside I_search, checked below) is that zero.
# This is the argument the Lean layer uses (Fc_mono_search); it replaces an
# exact Sturm count, whose rational coefficients explode beyond degree ~130
# (A256: deg Fc = 252). The Sturm count stays in test/literature.jl for n ≤ 64.
piI = interval(BigFloat, π); nI = interval(BigFloat, n)
hiI = piI / nI                                                       # hi = π/n
loI = interval(BigFloat, 2) * asin(sin(hiI) / interval(BigFloat, 2)) # lo
cHiI = cos(hiI); cLoI = cos(loI)
G = big(10)^30
ra = QQ(floor(BigInt, inf(cHiI) * G) - 1, G)                         # a < cos(π/n)
rb = QQ(ceil(BigInt, sup(cLoI) * G) + 1, G)                          # cos(lo) < b
Cbr = interval(BigFloat, ra, rb)
den_ok = !in_interval(0, pev(QQ.(den), Cbr))
dFc_br = pev_centred(dFc, Cbr)
mono_ok = !in_interval(0, dFc_br) && isguaranteed(dFc_br)
root_in_search = sup(loI) < inf(Zroot) && sup(Zroot) < inf(hiI)
unique_ok = mono_ok && den_ok && root_in_search && inf(cHiI) > ra && sup(cLoI) < rb &&
            ra > 0 && F_is_LEAD_Fc
gate("root_unique_search", unique_ok,
     "Fc' ∈ $(dFc_br) on [$(Float64(ra)), $(Float64(rb))] ⊃ cos(I_search), so 0 ∉ Fc' and Fc is strictly " *
     "monotone there (at most one root); I_search = (2 asin(sin(π/$n)/2), π/$n), Z_root ⊂ I_search = $(root_in_search), " *
     "cos 2z ≠ 0 there = $(den_ok); F = LEAD·Fc(cos z) exactly, cos injective on I_search ⇒ F has exactly one zero on I_search")

# --- side_length ----------------------------------------------------------------
ell = interval(BigFloat, 2) * sin(Zroot / interval(BigFloat, 2))
perim = nI * ell
side_ok = isguaranteed(ell) && diam(ell) < big"1e-28" && inf(ell) > 0
gate("side_length", side_ok, "ℓ = 2 sin(z/2) ∈ $(ell); perimeter $(n)ℓ ∈ $(perim)";
     ell = mid(ell), perimeter = mid(perim))

# --- the geometry gates, from the general certifier over Z_cert -------------------
rep = certify(cand; radius = CERT_RADIUS)
blk(name) = (i = findfirst(b -> b.name == name, rep.blocks); i === nothing ? nothing : rep.blocks[i])
for (id, name, good) in (("exact_identities", "exact_identities", :PROVEN), ("convexity", "convexity", :CERTIFIED),
                         ("inactive_margin", "active_graph+margin", :CERTIFIED), ("rank", "rank", :CERTIFIED),
                         ("multipliers", "multipliers", :CERTIFIED))
    b = blk(name)
    gate(id, b !== nothing && b.status == good, b === nothing ? "block missing" : b.detail)
end

# --- box_nesting, by endpoints --------------------------------------------------
# The box certify() actually evaluated (not a rebuilt copy of it).
Zcert = rep.meta[:Zbox]
gate("box_nesting", inf(Zcert) < inf(Zroot) && sup(Zroot) < sup(Zcert),
     "Z_root = [$(inf(Zroot)), $(sup(Zroot))] strictly inside Z_cert, by endpoints")

final_pass = all(gt["passed"] for gt in gates)
println("="^78)
println("FAMILY CERTIFICATE A$n: ", final_pass ? "CERTIFIED" : "NOT CERTIFIED",
        "  ($(count(gt -> gt["passed"], gates)) of $(length(gates)) gates)")
println("GLOBAL OPTIMALITY: NOT CLAIMED")
println("="^78)

if get(ENV, "CHIQUI_NO_RECORD", "") == "1"
    println("(CHIQUI_NO_RECORD=1 — results/family/A$n.toml was left untouched)")
else
    files = vcat(["src/" * f for f in readdir(joinpath(ROOT, "src")) if endswith(f, ".jl")],
                 ["cases/exact_coords.jl", "cases/optigon_exact.jl", "cases/upstream/optigon/cstrt_audet_ngon.jl",
                  "cases/family/A$(n)/candidate.jl", "pipeline/certify_family.jl", "Project.toml", "Manifest.toml"])
    commit = try strip(read(`git -C $ROOT rev-parse HEAD`, String)) catch; "(unavailable)" end
    clean = try isempty(strip(read(`git -C $ROOT status --porcelain -- src cases pipeline Project.toml Manifest.toml`, String))) catch; false end
    doc = Dict{String,Any}(
        "meta" => Dict{String,Any}("certificate" => "family certificate of A$n (Bingane–Audet)",
            "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z", "julia_version" => string(VERSION),
            "git_commit" => commit, "git_source_clean" => clean, "precision_bits" => 256,
            "intervalarithmetic_version" => string(pkgversion(IntervalArithmetic)),
            "matmul_mode" => SmallPolygons.matmul_mode(n),
            "root_radius" => string(ROOT_RADIUS), "cert_radius" => string(CERT_RADIUS), "n" => n),
        "gate" => gates,
        "certified" => final_pass,
        "verdict" => final_pass ? "CERTIFIED" : "NOT CERTIFIED",
        "global_optimality" => "NOT CLAIMED",
        "source_sha256" => [Dict("file" => f, "sha256" => bytes2hex(open(sha256, joinpath(ROOT, f)))) for f in files])
    mkpath(joinpath(ROOT, "results", "family"))
    open(joinpath(ROOT, "results", "family", "A$n.toml"), "w") do io
        println(io, "# Family certificate of A$n — machine-readable. Auto-generated by pipeline/certify_family.jl; do not edit.")
        TOML.print(io, doc; sorted = true)
    end
    println("wrote results/family/A$n.toml")
end
final_pass || exit(1)
