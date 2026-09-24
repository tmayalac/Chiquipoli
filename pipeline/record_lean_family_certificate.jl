# Lean 4 / Mathlib certificate of the Bingane–Audet family layer (A16, A32, A64).
#
#   julia --project=. pipeline/record_lean_family_certificate.jl          # run + record
#   julia --project=. pipeline/record_lean_family_certificate.jl --check  # compare only
#
# The first form runs lean/verify_family.sh (all five checks, all cases) and
# writes results/lean_family_certificate.toml. The second runs nothing: it
# recomputes the SHA-256 of every file the record lists and says whether the
# record still describes the tree, in seconds. `make paper-check` calls it.
#
# WHY THIS EXISTS. The project runs locally, not in CI, so a verification that
# is not written down leaves no evidence that it happened, or of what it was run
# on. This is the family's counterpart of results/lean_certificate.toml (A16):
# the verdict of each check, the certified numbers of each case, the toolchain,
# and a hash of every file the verdict depends on, so that any later edit to a
# certificate file, a control, the generator or its Julia inputs makes the
# record visibly stale instead of silently wrong.
#
# Like record_lean_certificate.jl, this script proves nothing itself; it
# records what verify_family.sh established. Scope: lean/ChiquipoliFamily/README.md.

const ROOT = normpath(joinpath(@__DIR__, ".."))
const LEAN = joinpath(ROOT, "lean")
const OUT  = joinpath(ROOT, "results", "lean_family_certificate.toml")
const CASES = (16, 32, 64)
using Dates, TOML, SHA

# Every file the verdict depends on, relative to the repository root: the Lean
# sources and controls, the verifier, the generator, and the generator's Julia
# inputs (it builds the certificate from them, so an edit there can change what
# a regeneration would produce).
function walk(sub, ext)
    out = String[]
    d = joinpath(ROOT, sub)
    isdir(d) || return out
    for (dir, _, fs) in walkdir(d), f in fs
        endswith(f, ext) && push!(out, relpath(joinpath(dir, f), ROOT))
    end
    out
end
tracked_files() = sort!(unique(vcat(
    ["lean/ChiquipoliFamily.lean", "lean/verify_family.sh", "lean/lakefile.toml",
     "lean/lean-toolchain", "lean/lake-manifest.json",
     "cases/exact_coords.jl", "Project.toml", "Manifest.toml",
     "test/fixtures/optigon_reference.jl", "test/literature.jl",
     "cases/optigon_exact.jl", "cases/upstream/optigon/cstrt_audet_ngon.jl"],
    ["cases/A$(n)_bingane_audet/candidate.jl" for n in CASES],
    walk("lean/ChiquipoliFamily", ".lean"),
    walk("lean/negative_controls_family", ".lean"),
    walk("lean/generators/family", ".jl"),
    walk("src", ".jl"),
)))
filehash(rel) = bytes2hex(sha256(read(joinpath(ROOT, rel))))

# --- --check: compare the record with the tree, run nothing -----------------
function check_record()
    if !isfile(OUT)
        println("no record: results/lean_family_certificate.toml is absent (run `make lean-family-certificate`)")
        return 2
    end
    rec = TOML.parsefile(OUT)
    recorded = Dict(e["file"] => e["sha256"] for e in rec["source_sha256"])
    now_files = tracked_files()
    changed = [f for f in now_files if haskey(recorded, f) && recorded[f] != filehash(f)]
    added   = [f for f in now_files if !haskey(recorded, f)]
    removed = [f for f in keys(recorded) if !isfile(joinpath(ROOT, f))]
    ok = get(rec, "certified", false) && isempty(changed) && isempty(added) && isempty(removed)
    println("record: ", get(rec, "verdict", "?"))
    println("        commit ", get(rec["meta"], "git_commit", "?"), ", ", get(rec["meta"], "utc", "?"))
    println("files:  $(length(recorded)) recorded, $(length(changed)) changed, $(length(added)) new, $(length(removed)) removed")
    for (lab, xs) in (("changed", changed), ("new", added), ("removed", removed)), f in first(sort(xs), 10)
        println("        $lab: $f")
    end
    println(ok ? "LEAN FAMILY RECORD CURRENT — it describes this tree" :
                 "LEAN FAMILY RECORD STALE — re-run `make lean-family-certificate`")
    return ok ? 0 : 1
end
if "--check" in ARGS
    exit(check_record())
end

# --- run verify_family.sh ---------------------------------------------------
function git_state()
    try
        commit = strip(read(`git -C $ROOT rev-parse HEAD`, String))
        dirty = !isempty(strip(read(`git -C $ROOT status --porcelain -- src cases lean Project.toml Manifest.toml`, String)))
        return commit, !dirty
    catch e; return "(unavailable: $e)", false; end
end
function mathlib_rev()
    txt = read(joinpath(LEAN, "lake-manifest.json"), String)
    i = findfirst("\"name\": \"mathlib\"", txt)
    i === nothing && return "(mathlib not listed)"
    m = match(r"\"rev\"\s*:\s*\"([0-9a-f]{40})\"", txt[max(1, first(i) - 600):min(lastindex(txt), last(i) + 600)])
    m === nothing ? "(rev not found)" : m.captures[1]
end

println("="^78)
println("LEAN 4 / MATHLIB CERTIFICATE — the Bingane–Audet family (A16, A32, A64)")
println("="^78)
t0 = time()
out = IOBuffer()
verify_ok = try
    # All steps, all cases: a restricted run is not a certification.
    run(pipeline(setenv(Cmd(`./verify_family.sh`, dir = LEAN), filter(p -> !startswith(p.first, "FAMILY_"), ENV));
                 stdout = out, stderr = out)); true
catch
    false
end
seconds = round(Int, time() - t0)
report = replace(String(take!(out)), r"\e\[[0-9;]*m" => "")
print(report)
haspass(pat) = occursin(Regex("PASS\\s+" * pat), report)
axm = match(r"PASS\s+(\d+) theorems depend only on", report)

# --- the certified numbers of each case, from the generator itself ------------
# The generator prints them while it checks every margin exactly; run it into a
# scratch directory (it never writes the tracked tree there) and read them back.
function case_numbers(n)
    scratch = mktempdir()
    txt = try
        read(setenv(Cmd(`julia --project=. lean/generators/family/gen_family.jl $n`; dir = ROOT),
                    merge(Dict(ENV), Dict("CHIQUI_OUTDIR" => scratch))), String)
    finally
        rm(scratch; recursive = true, force = true)
    end
    g(re) = (m = match(re, txt); m === nothing ? "?" : m.captures[1])
    Dict{String,Any}(
        "clo" => replace(g(r"\[clo,chi\] = \[([^,]+),"), "//" => "/"),
        "chi" => replace(g(r"\[clo,chi\] = \[[^,]+, ([^\]]+)\]"), "//" => "/"),
        "bracket_width" => g(r"width ([0-9.e+-]+)"),
        "enclosure_radius_rho" => g(r"ρ = ([0-9.e+-]+)"),
        "support_determinants" => parse(Int, g(r"convexity: (\d+) determinants")),
        "worst_support_margin" => g(r"worst certified margin ([0-9.e+-]+)"),
        "inactive_pairs" => parse(Int, g(r"inactive:\s+(\d+) pairs")),
        "worst_inactive_bound" => g(r"worst certified bound ([0-9.e+-]+)"),
        "henneberg_steps" => parse(Int, g(r"Henneberg: (\d+) steps")),
        "sides_needing_Fc" => g(r"sides needing Fc: (\[[^\]]*\])"),
        "deg_Fc" => parse(Int, g(r"deg Fc = (\d+)")),
        "min_diameter_stress_lower_bound" => g(r"worst certified λ ≥ ([0-9.e+-]+)"),
        "side_stress_sum_upper_bound" => g(r"Σα ≤ ([0-9.e+-]+)"),
        "search_bracket_cos" => g(r"search bracket (\[[^\]]*\])"),
        "Fc_derivative_lower_bound" => g(r"\|Fc'\| ≥ ([0-9.e+-]+)"),
        "generated_files" => length(filter(f -> endswith(f, ".lean"), readdir(joinpath(LEAN, "ChiquipoliFamily", "A$n")))),
        "headline" => "Chiquipoli.Family.A$n.locally_maximal_unique",
    )
end

checks = Dict{String,Any}(
    "build" => haspass("lake build ChiquipoliFamily"),
    "no_sorry" => haspass("no 'sorry', 'admit' or 'native_decide'"),
    "axiom_audit" => axm !== nothing && haspass("every case's headline theorems are audited by name"),
)
cases = Dict{String,Any}()
for n in CASES
    ctl = haspass("A$n: all \\d+ controls rejected by Lean, all \\d+ twins compile")
    gen = haspass("A$n: \\d+ certificate files, the root module and \\d+ control/twin files reproduce byte for byte")
    checks["A$(n)_controls_and_twins"] = ctl
    checks["A$(n)_regeneration"] = gen
    println("reading the certified numbers of A$n from the generator ...")
    cases["A$n"] = case_numbers(n)
end
all_pass = verify_ok && all(values(checks)) && occursin("FAMILY LEAN CERTIFICATE PASS", report)

commit, srcclean = git_state()
doc = Dict{String,Any}(
    "meta" => Dict{String,Any}(
        "certificate" => "Lean 4 / Mathlib certificate of the Bingane–Audet family layer",
        "package" => "A16Certificate v$(TOML.parsefile(joinpath(ROOT, "Project.toml"))["version"])",
        "lean_toolchain" => strip(read(joinpath(LEAN, "lean-toolchain"), String)),
        "mathlib_rev" => mathlib_rev(),
        "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z",
        "julia_version" => string(VERSION),
        "git_commit" => commit,
        "git_source_clean" => srcclean,
        "verify_seconds" => seconds,
        "method" => "vertex enclosures + sign lemmas proved once for every n; Henneberg rigidity; multipliers as a Henneberg self-stress; kernel-checked rational arithmetic, no floating point",
    ),
    "checks" => checks,
    "cases" => cases,
    "theorems" => Dict{String,Any}(
        "axioms" => ["propext", "Classical.choice", "Quot.sound"],
        "axiom_audited_theorems" => axm === nothing ? 0 : parse(Int, axm.captures[1]),
        "negative_controls_per_case" => parse(Int, match(r"NEGATIVE_CONTROLS_PER_CASE=(\d+)", read(joinpath(LEAN, "verify_family.sh"), String)).captures[1]),
        "headline_per_case" => ["published_locally_maximal", "locally_maximal_unique", "locally_maximal_at", "locally_maximal"],
    ),
    "scope" => Dict{String,Any}(
        "formalized" => [
            "for each of A16, A32, A64: a root of the constructor equation Fc exists in a rational bracket of width about 1e-17, and it is the only root in the article's search interval (2 arcsin(sin(pi/n)/2), pi/n)",
            "the configuration built from it is equilateral, has its n-1 active diameters equal to 1, is strictly convex in labelled cyclic order (all n(n-2) support determinants positive) and small (every other pair below 1)",
            "the multiplier identity with every active-diameter multiplier strictly positive and kappa > 0 (a self-stress built by the Henneberg recursion)",
            "I_eq = R_eq, by a Henneberg construction",
            "strict local maximality of the perimeter modulo orientation-preserving Euclidean motions, through the general Theorem 3.5 (Chiquipoli.Feasible.thm_3_5)",
            "the identification with the published polygon: ChiquipoliFamily/Optigon.lean transcribes the upstream OPTIGON constructor statement for statement for every n; for each case, every vertex it builds equals the certified vertex and its equation F equals a constant times Fc(cos z) wherever cos 2z != 0 (A<n>.Q_eq_P, A<n>.F_eq), and the headline result is stated about upstream's own F, bracket and polygon (A<n>.published_locally_maximal)",
        ],
        "not_formalized" => [
            "that the transcription ChiquipoliFamily/Optigon.lean says what the upstream Julia source says: no kernel reads Julia. It is bounded by running the upstream source itself, byte-identical (SHA-256), unchanged, in exact arithmetic (cases/optigon_exact.jl): its vertices and equation equal the certified ones exactly; by a test requiring every quoted upstream statement to occur verbatim in the vendored reference with the same number of assignments; and by four planted transcription slips each of which breaks the Lean identification",
            "that the pattern observed at n = 16, 32, 64 (n-1 active diameters, deg Fc = n-4, the Fc-sides are the two non-Henneberg bars) holds for every n = 2^s",
            "any lower bound on the radius of the neighbourhood of local maximality",
            "global optimality, which is not addressed anywhere in this package",
        ],
    ),
    "source_sha256" => [Dict{String,Any}("file" => f, "sha256" => filehash(f)) for f in tracked_files()],
    "certified" => all_pass,
    "verdict" => all_pass ?
        "LEAN FAMILY CERTIFICATE PASS — A16, A32 and A64 are kernel-verified strict local maximisers" :
        "LEAN FAMILY CERTIFICATE FAIL",
)
open(OUT, "w") do io
    println(io, "# Lean 4 / Mathlib certificate of the Bingane–Audet family layer — machine-readable.")
    println(io, "# Auto-generated by pipeline/record_lean_family_certificate.jl; do not edit.")
    println(io, "# `julia --project=. pipeline/record_lean_family_certificate.jl --check` says whether it still describes the tree.")
    println(io, "# Scope: lean/ChiquipoliFamily/README.md.")
    TOML.print(io, doc; sorted = true)
end
println("wrote ", relpath(OUT, ROOT), " (", length(doc["source_sha256"]), " files hashed)")
println(doc["verdict"])
(abspath(PROGRAM_FILE) == @__FILE__) && exit(all_pass ? 0 : 1)
