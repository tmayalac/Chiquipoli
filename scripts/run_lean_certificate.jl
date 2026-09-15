# Lean 4 / Mathlib certificate for the computational hypotheses of the A16
# certificate.
#   julia --project=. scripts/run_lean_certificate.jl
# Runs lean/scripts/verify.sh and writes results/lean_certificate.toml.
#
# This script does not itself prove anything — it records, in the same
# machine-readable shape as the other certificates in results/, the outcome of
# the five checks that `lean/scripts/verify.sh` performs, together with the
# pinned toolchain, the pinned Mathlib revision, and SHA-256 hashes of every
# Lean source. See lean/README.md for the scope of what Lean does and does not
# establish.

const ROOT = normpath(joinpath(@__DIR__, ".."))
const LEAN = joinpath(ROOT, "lean")
using Dates, TOML, SHA

function git_state(root)
    try
        commit = strip(read(`git -C $root rev-parse HEAD`, String))
        dirty = !isempty(strip(read(`git -C $root status --porcelain -- src scripts examples lean Project.toml Manifest.toml`, String)))
        return commit, !dirty
    catch e; return "(unavailable: $e)", false; end
end

lean_sources() = sort!(vcat(
    ["ChiquipoliLean.lean"],
    ["ChiquipoliLean/" * f for f in readdir(joinpath(LEAN, "ChiquipoliLean")) if endswith(f, ".lean")],
    ["negative_controls/" * f for f in readdir(joinpath(LEAN, "negative_controls")) if endswith(f, ".lean")],
    ["scripts/verify.sh", "tools/extract_polys.jl", "lakefile.toml", "lean-toolchain"],
))

"""
Read mathlib's pinned revision out of lake-manifest.json without taking a JSON
dependency (the package's Manifest.toml is frozen for reproducibility). The
manifest lists one object per package; we take the `rev` nearest to the
`\"name\": \"mathlib\"` key.
"""
function mathlib_rev()
    try
        txt = read(joinpath(LEAN, "lake-manifest.json"), String)
        i = findfirst("\"name\": \"mathlib\"", txt)
        i === nothing && return "(mathlib not listed)"
        window = txt[max(1, first(i) - 600):min(lastindex(txt), last(i) + 600)]
        m = match(r"\"rev\"\s*:\s*\"([0-9a-f]{40})\"", window)
        return m === nothing ? "(rev not found)" : m.captures[1]
    catch e
        return "(unavailable: $e)"
    end
end

println("="^78)
println("LEAN 4 / MATHLIB CERTIFICATE — A16 computational hypotheses")
println("="^78)

out = IOBuffer()
verify_ok = try
    run(pipeline(Cmd(`./scripts/verify.sh`, dir = LEAN); stdout = out, stderr = out))
    true
catch
    false
end
report = String(take!(out))
print(report)

# Parse the five named checks out of the verifier's own report.
strip_ansi(s) = replace(s, r"\e\[[0-9;]*m" => "")
clean = strip_ansi(report)
haspass(pat) = occursin(Regex("PASS\\s+" * pat), clean)

axiom_m = match(r"PASS\s+(\d+) theorems depend only on", clean)
nc_pass = count(m -> true, eachmatch(r"PASS\s+nc\d+_", clean))
nc_total = length(filter(f -> endswith(f, ".lean"),
                        readdir(joinpath(LEAN, "negative_controls"))))

checks = Dict{String,Any}(
    "build"                    => haspass("lake build"),
    "no_sorry"                 => haspass("no 'sorry' in any source file"),
    "axiom_audit"              => axiom_m !== nothing,
    "negative_controls"        => (nc_pass == nc_total && nc_total > 0),
    "generated_matches_julia"  => haspass("Generated.lean reproduces byte-for-byte"),
)
all_pass = verify_ok && all(values(checks))

commit, srcclean = git_state(ROOT)
doc = Dict{String,Any}(
    "meta" => Dict{String,Any}(
        "certificate" => "Lean 4 / Mathlib formalization of the A16 certificate's computational hypotheses",
        "package" => "A16Certificate v$(TOML.parsefile(joinpath(ROOT,"Project.toml"))["version"])",
        "paper" => "First Order Geometry of Equilateral Small Polygons (accompanying article)",
        "lean_toolchain" => strip(read(joinpath(LEAN, "lean-toolchain"), String)),
        "mathlib_rev" => mathlib_rev(),
        "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z",
        "julia_version" => string(VERSION),
        "git_commit" => commit,
        "git_source_clean" => srcclean,
        "method" => "kernel-checked theorems; no interval arithmetic, no floating point",
    ),
    "checks" => checks,
    "theorems" => Dict{String,Any}(
        "identities_total" => 31,
        "sides_unconditional" => 14,
        "sides_conditional" => 2,
        "conditional_sides" => ["(3,4)", "(12,13)"],
        "conditional_quotient" => 1,
        "active_diameters" => 15,
        "axioms" => ["propext", "Classical.choice", "Quot.sound"],
        "axiom_audited_theorems" => axiom_m === nothing ? 0 : parse(Int, axiom_m.captures[1]),
        "negative_controls_rejected" => nc_pass,
        "negative_controls_total" => nc_total,
        "headline" => "Chiquipoli.Feasible.A16_locally_maximal",
        "headline_hypotheses" => "Chiquipoli.A16_certificate",
    ),
    "scope" => Dict{String,Any}(
        # Keep this list in step with the statement of `A16_certificate`
        # (lean/ChiquipoliLean/Certificate.lean). It was stale once already:
        # it still described `A16_exists`, the narrower Lemma-6.1-only theorem,
        # after the Category A modules had landed.
        "formalized" => [
            "Chebyshev multiple-angle reduction, k = 1..7",
            "hand-written trigonometric constructor equals the exact polynomial coordinates",
            "Fc(cos z) = F(z)",
            "Lemma 6.1: 16 side equalities + 15 active-diameter equalities",
            "existence of a constructor root, with sin z > 0 and cos z in a narrow rational bracket",
            "uniqueness of cos z as a root of Fc on the rational bracket [49/50, 491/500] (Prop 6.2(1), see the caveat below)",
            "strict convexity and labelled cyclic order: all 224 cross products strictly positive (Prop 6.2(3))",
            "the 89 strict inactive-diameter bounds, hence diameter exactly 1 (Prop 6.2(4)); the remaining 16 of the paper's 105 inactive pairs are the sides, covered by the equilateral identity",
            "stationarity at every vertex with all 15 active-diameter multipliers strictly positive (Prop 6.2(5))",
            "I_eq = R_eq: every admissible infinitesimal variation is a rigid motion — the conclusion the rank-30 computation of Prop 6.2(6) exists to supply",
            "Theorem 3.5, the abstract first-order criterion, in full: the feasible set, openness of convexity and the inactive margin, the first-order limits, invariance under Euclidean motions with the slice normalisation, and the blow-up (Chiquipoli.Feasible.thm_3_5)",
            "Theorem 6.3: the certified configuration is a strict local maximiser of the perimeter modulo orientation-preserving Euclidean motions (Chiquipoli.Feasible.A16_locally_maximal)",
            "Proposition 4.2: the square is a strict local maximiser, by the same route (Chiquipoli.Feasible.square_strict_local_max)",
        ],
        "not_formalized" => [
            "rank D(e,d) = 30 as a numerical rank statement (Prop 6.2(6)); Lean proves its consequence I_eq = R_eq directly instead",
            "the transfer of root uniqueness from the bracket in cos z back to the paper's t-interval I_search; the bracket does contain cos(I_search), but the change of variable is not itself formalized",
            "the identification of the certified configuration with the published Bingane-Audet polygon; that is an attribution, checked by running the upstream OPTIGON constructor and comparing coordinates, and no proof assistant can close it",
            "any lower bound on the radius of the neighbourhood of Theorem 6.3; the proof is by contradiction from a convergent sequence and yields none",
            "global optimality, which is not addressed anywhere in this package",
            "every interval-arithmetic step of the Julia certificate; Lean re-proves the exact-algebra and positivity layers by kernel-checked rational arithmetic rather than re-running it",
        ],
    ),
    "source_sha256" => [
        Dict{String,Any}("file" => "lean/" * f,
                         "sha256" => bytes2hex(sha256(read(joinpath(LEAN, f)))))
        for f in lean_sources() if isfile(joinpath(LEAN, f))
    ],
    "certified" => all_pass,
    "verdict" => all_pass ?
        "LEAN CERTIFICATE PASS — every computational hypothesis of the A16 certificate is kernel-verified" :
        "LEAN CERTIFICATE FAIL",
)

outpath = joinpath(ROOT, "results", "lean_certificate.toml")
open(outpath, "w") do io
    println(io, "# Lean 4 / Mathlib certificate for the A16 computational hypotheses — machine-readable.")
    println(io, "# Auto-generated by scripts/run_lean_certificate.jl; do not edit.")
    println(io, "# Scope (what Lean does and does not prove): lean/README.md.")
    TOML.print(io, doc; sorted = true)
end
println("wrote ", relpath(outpath, ROOT))
println(doc["verdict"])
(abspath(PROGRAM_FILE) == @__FILE__) && exit(all_pass ? 0 : 1)
