# The certificate of one Bingane–Audet polygon Z_n (n = 32, 64): the same gates
# as the family certificate of A_n (pipeline/certify_family.jl) that make sense
# for it, computed the same way, and a record in results/family/Z<n>.toml.
#
#     julia --project=. pipeline/certify_z.jl 32        # or: make z32
#
# writes results/family/Z32.toml (CHIQUI_NO_RECORD=1: prints only) and exits 1
# unless the verdict is CERTIFIED.
#
# THE GATES (all enter the verdict):
#   root              interval Newton on Z_root: 0 ∉ F'(Z), N(Z) ⊂ int Z; F' is the
#                     analytic derivative stored with the candidate (Fp), checked
#                     against a finite difference in test/literature.jl
#   root_unique_search  no other zero on (0, π/n], where the polygon exists, by
#                     interval bisection (SmallPolygons.no_other_root)
#   side_length       ℓ = 2 sin(z/2) and nℓ enclosed over Z_root
#   exact_identities  every side and every active diameter, exactly: in Q[c] for Z32,
#                     in Q[c,s,y] modulo s²+c²-1 for Z64
#   convexity         every support determinant > 0 over Z_cert
#   inactive_margin   declared actives at distance 1, every other pair < 1
#   rank              rank D(e,d) = 2n-2 over Z_cert (I_eq = R_eq)
#   multipliers       Krawczyk-enclosed, every diameter multiplier > 0
#   box_nesting       Z_root ⊂ int Z_cert, by endpoints
#
# WHAT IS NOT HERE, on purpose, and said in the record. There is no published
# constructor to run unchanged (OPTIGON ships only the A_n; Z_n is rebuilt from
# Propositions 1 and 2 of Bingane and Audet), so no `published_constructor` gate.
# Lean covers Z_n (lean/ChiquipoliFamily/Polynomial/Z<n>; the record
# results/lean_family_certificate.toml), but not the uniqueness of the root of Z_n in
# (0, π/n]: that is proved by bisection (gate root_unique_search), in Julia and in Python,
# not by the monotonicity argument of the A_n certificate, which has no analogue here.

const ROOT = normpath(joinpath(@__DIR__, ".."))
include(joinpath(ROOT, "src", "A16Certificate.jl"));  using .A16Certificate
include(joinpath(ROOT, "src", "ExactIdentity.jl"));   using .ExactIdentity
include(joinpath(ROOT, "src", "SmallPolygons.jl"));   using .SmallPolygons
include(joinpath(ROOT, "cases", "exact_coords.jl"))
using IntervalArithmetic, Dates, SHA, TOML

setprecision(BigFloat, 256)
const ROOT_RADIUS = big"1e-30"
const CERT_RADIUS = big"1e-28"

n = length(ARGS) == 1 ? parse(Int, ARGS[1]) : error("usage: certify_z.jl <n>, n in (32, 64)")
n in (32, 64) || error("n must be 32 or 64")
cand = include(joinpath(ROOT, "cases", "family", "Z$(n)", "candidate.jl"))

gates = Dict{String,Any}[]
gate(id, pass, detail; extra...) = (push!(gates, Dict{String,Any}("id" => id, "passed" => pass,
    "status" => pass ? "CERTIFIED" : "FAIL", "detail" => detail, (string(k) => string(v) for (k, v) in extra)...));
    println(rpad(id, 24), pass ? "PASS  " : "FAIL  ", detail); pass)

println("="^78)
println("FAMILY CERTIFICATE Z$n (Bingane–Audet, Proposition $(n == 32 ? 1 : 2)), the gates of the A_n certificate that apply")
println("="^78)

# --- root: interval Newton on Z_root --------------------------------------------
z0 = cand.root.nominal
Zroot = interval(z0 - ROOT_RADIUS, z0 + ROOT_RADIUS)
m = interval(mid(Zroot))
Fm = cand.root.F(m)
Dz = cand.root.Fp(Zroot)
Nz = m - Fm / Dz
newton_ok = !in_interval(0, Dz) && isinterior(Nz, Zroot) && isguaranteed(Nz) && isguaranteed(Dz)
gate("root", newton_ok,
     "interval Newton on Z_root (radius 1e-30): 0 ∉ F'(Z) = $(Dz), N(Z) ⊂ int Z = $(isinterior(Nz, Zroot)); " *
     "F' is the analytic derivative of the defining equation, checked against a finite difference in the tests")

# --- root_unique_search: no other zero on (0, pi/n] -----------------------------
# Interval bisection discards every box where the equation is nonzero or the
# polygon does not exist (Z64 needs a real square root); what is left is Z_root,
# in which Newton above shows exactly one zero. So t_n is the only zero in the
# interval (0, pi/n) that Bingane and Audet name, at which Z_n exists.
hiS = sup(interval(BigFloat, π) / interval(BigFloat, n))
uq = no_other_root(cand.root.Fs, Zroot, zero(BigFloat), hiS)
gate("root_unique_search", newton_ok && uq.ok,
     uq.ok ? "no zero of the defining equation in (0, π/$n] outside Z_root, by bisection ($(uq.boxes) boxes; boxes where " *
             "the polygon does not exist are discarded), and exactly one inside it (Newton above): t_n is the only zero in (0, π/$n)" :
             "NOT PROVED: $(uq.why)")

# --- side_length ----------------------------------------------------------------
nI = interval(BigFloat, n)
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
Zcert = rep.meta[:Zbox]
gate("box_nesting", inf(Zcert) < inf(Zroot) && sup(Zroot) < sup(Zcert),
     "Z_root = [$(inf(Zroot)), $(sup(Zroot))] strictly inside Z_cert, by endpoints")

final_pass = all(gt["passed"] for gt in gates)
println("="^78)
println("FAMILY CERTIFICATE Z$n: ", final_pass ? "CERTIFIED" : "NOT CERTIFIED",
        "  ($(count(gt -> gt["passed"], gates)) of $(length(gates)) gates)")
println("GLOBAL OPTIMALITY: NOT CLAIMED")
println("="^78)

if get(ENV, "CHIQUI_NO_RECORD", "") == "1"
    println("(CHIQUI_NO_RECORD=1 — results/family/Z$n.toml was left untouched)")
else
    files = vcat(["src/" * f for f in readdir(joinpath(ROOT, "src")) if endswith(f, ".jl")],
                 ["cases/exact_coords.jl", "cases/family/Z$(n)/candidate.jl", "pipeline/certify_z.jl",
                  "Project.toml", "Manifest.toml"])
    commit = try strip(read(`git -C $ROOT rev-parse HEAD`, String)) catch; "(unavailable)" end
    clean = try isempty(strip(read(`git -C $ROOT status --porcelain -- src cases pipeline Project.toml Manifest.toml`, String))) catch; false end
    doc = Dict{String,Any}(
        "meta" => Dict{String,Any}("certificate" => "certificate of Z$n (Bingane–Audet)",
            "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z", "julia_version" => string(VERSION),
            "git_commit" => commit, "git_source_clean" => clean, "precision_bits" => 256,
            "intervalarithmetic_version" => string(pkgversion(IntervalArithmetic)),
            "matmul_mode" => SmallPolygons.matmul_mode(),
            "root_radius" => string(ROOT_RADIUS), "cert_radius" => string(CERT_RADIUS), "n" => n),
        "gate" => gates,
        "certified" => final_pass,
        "verdict" => final_pass ? "CERTIFIED" : "NOT CERTIFIED",
        "global_optimality" => "NOT CLAIMED",
        "not_claimed" => ["a constructor published as code (Z_n is rebuilt from Propositions 1 and 2 of Bingane and Audet)"],
        "lean" => "lean/ChiquipoliFamily/Polynomial/Z$n: strict local maximality at every root of the defining equation in the certified bracket, and a root exists there (Chiquipoli.Family.Z$n.locally_maximal_at); not the uniqueness of the root in (0, pi/$n]",
        "source_sha256" => [Dict("file" => f, "sha256" => bytes2hex(open(sha256, joinpath(ROOT, f)))) for f in files])
    mkpath(joinpath(ROOT, "results", "family"))
    open(joinpath(ROOT, "results", "family", "Z$n.toml"), "w") do io
        println(io, "# Certificate of Z$n — machine-readable. Auto-generated by pipeline/certify_z.jl; do not edit.")
        TOML.print(io, doc; sorted = true)
    end
    println("wrote results/family/Z$n.toml")
end
final_pass || exit(1)
