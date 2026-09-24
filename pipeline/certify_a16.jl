# The dedicated A16 certificate: runs stages 01-06 and writes
# results/a16_certificate.toml. `make verify` runs it and keeps the log.
include(joinpath(@__DIR__, "stages", "_bootstrap.jl"))
include(joinpath(@__DIR__, "stages", "01_nominal_configuration.jl"))
include(joinpath(@__DIR__, "stages", "02_certify_root.jl"))
include(joinpath(@__DIR__, "stages", "03_certify_geometry.jl"))
include(joinpath(@__DIR__, "stages", "04_certify_rank.jl"))
include(joinpath(@__DIR__, "stages", "05_certify_multipliers.jl"))
include(joinpath(@__DIR__, "stages", "06_prove_exact_identities.jl"))

using Dates, SHA, Pkg, TOML

# Load-bearing source files, and their SHA256 hashes, tying an archived run to
# the exact source that produced it. Single source of truth for both the
# printed provenance header and the machine-readable certificate below.
# The directories whose Julia files are load-bearing for this certificate. The
# git cleanliness check below looks at the same list, so the two cannot drift.
const SOURCE_DIRS = ("src", "pipeline", "test")

# `git status` restricted to the load-bearing paths. Built from an explicit
# argument vector: inside backticks, `$(SOURCE_DIRS...)` does not splat, it
# CONCATENATES ("srcpipelinetest"), git then reports nothing for a path that
# does not exist, and every run is recorded as clean. That happened here once.
_source_status_cmd(projroot) =
    Cmd(["git", "-C", projroot, "status", "--porcelain", "--",
         SOURCE_DIRS..., "Project.toml", "Manifest.toml"])

function _source_hashes(projroot)
    files = String[]
    for d in SOURCE_DIRS
        top = joinpath(projroot, d)
        isdir(top) || continue
        for (dir, _, fs) in walkdir(top), f in fs
            endswith(f, ".jl") && push!(files, relpath(joinpath(dir, f), projroot))
        end
    end
    sort!(files)
    append!(files, ["Project.toml", "Manifest.toml"])
    hashed = [(rel, bytes2hex(sha256(read(joinpath(projroot, rel)))))
              for rel in files if isfile(joinpath(projroot, rel))]
    # Guardrail. The scan is recursive, so a file moved into a subdirectory is
    # still covered, but a file moved OUT of src/, pipeline/ or test/ (or a
    # directory renamed) would drop out of the provenance chain with no error.
    # Pin the count so that fails loudly. If you add or remove a load-bearing
    # source, change this number deliberately.
    # 32 since pipeline/record_lean_family_certificate.jl, 33 since
    # pipeline/certify_family.jl (both 2026-09-24).
    @assert length(hashed) == 33 "provenance covers $(length(hashed)) files, expected 33 - a load-bearing source moved, was added, or was removed"
    return hashed
end

# git commit + whether the load-bearing source paths (not logs/results, which
# are the outputs being regenerated) match HEAD.
# Three states, not two. The supplementary material is distributed as an
# archive, so a referee runs this outside a git checkout, and collapsing that
# case into "dirty" printed a raw exception and two `fatal:` lines from git as
# the first thing they saw. Absent provenance is not failed provenance: it is
# reported as such, and `check_paper.jl` skips the clean-tree check rather than
# failing it. Inside a checkout the guarantee is unchanged.
# True only when there is a COMMIT to tie this run to. Two distinct situations
# fail it, and both must be quiet: the distributed archive, which is not a
# repository at all, and a freshly initialised repository whose first commit has
# not been made. Checking `--git-dir` alone covers only the first, and the
# second then printed `fatal: ambiguous argument 'HEAD'` and a raw Julia
# exception dump -- which is how this was found.
function _git_available(projroot)
    try
        success(pipeline(`git -C $projroot rev-parse --verify --quiet HEAD`;
                         stdout = devnull, stderr = devnull))
    catch
        false
    end
end

function _git_state(projroot)
    _git_available(projroot) || return "(no commit: extracted archive, or a repository with no commits yet)", false
    try
        commit = strip(read(`git -C $projroot rev-parse HEAD`, String))
        src_status = read(_source_status_cmd(projroot), String)
        return commit, isempty(strip(src_status))
    catch e
        return "(unavailable: $e)", false
    end
end

# Provenance header required by logs/README.md, so an archived run is
# cryptographically tied to the exact source that produced it.
function print_provenance()
    projroot = normpath(joinpath(@__DIR__, ".."))
    println("============================================================")
    println("PROVENANCE / REPRODUCIBILITY HEADER")
    println("============================================================")
    println("UTC timestamp        = ", Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS"), "Z")
    println("Julia version        = ", VERSION)
    try
        println("IntervalArithmetic   = v", pkgversion(IntervalArithmetic))
    catch e
        println("IntervalArithmetic   = (version query failed: ", e, ")")
    end
    println("BigFloat precision   = ", precision(BigFloat), " bits")

    # Directed-rounding self-check: a proper enclosure must be non-thin here.
    # Asserted, not only printed: 1/3 is not a binary number, so an interval
    # library that rounds both endpoints the same way returns a thin interval,
    # and every enclosure below would silently lose its guarantee. The article
    # (Subsection 6.1) says the rounding mode is verified at run time; this
    # assert is what makes that true.
    r = interval(BigFloat(1)) / 3
    println("directed-rounding self-check (interval(1)/3 has inf<sup) = ",
            inf(r) < sup(r), "   [", inf(r), ", ", sup(r), "]")
    # `1//3` is the exact rational, compared exactly with the BigFloat
    # endpoints; `big(1)/3` would not do, being itself one of the endpoints.
    @assert inf(r) < 1//3 < sup(r) "directed rounding is not in effect: interval(1)/3 = [$(inf(r)), $(sup(r))]"

    # git commit + source cleanliness. We check only the source paths (not
    # logs/, which is the output being regenerated) so the flag genuinely
    # answers: does the committed source match the code that just ran?
    if !_git_available(projroot)
        println("git commit           = (none — this is either the distributed archive or a")
        println("                        repository with no commits yet, so there is no")
        println("                        commit to tie this run to. The SHA256 list below")
        println("                        still ties it to the exact sources it read.)")
    else
        try
            commit = strip(read(`git -C $projroot rev-parse HEAD`, String))
            src_status = read(_source_status_cmd(projroot), String)
            dirty = !isempty(strip(src_status))
            println("git commit           = ", commit, dirty ? "  (SOURCE DIRTY — log not tied to this commit)" : "  (source clean — log matches this commit)")
        catch e
            println("git commit           = (unavailable: ", e, ")")
        end
    end

    # SHA256 of every load-bearing source file.
    # The same list as the certificate records, from the same function, so the
    # log and the TOML cannot disagree about which files were hashed.
    println("SHA256 of source files:")
    for (rel, h) in _source_hashes(projroot)
        println("  ", h, "  ", rel)
    end

    # Pkg.status(), required by logs/README.md. Project mode lists this
    # environment's direct dependencies; manifest mode additionally resolves
    # every transitive dependency, pinning the full dependency graph that
    # produced this run (not just the two top-level packages).
    println()
    println("Pkg.status() [project mode]:")
    Pkg.status()
    println()
    println("Pkg.status() [manifest mode, full resolved dependency graph]:")
    Pkg.status(; mode=Pkg.PKGMODE_MANIFEST)
    println("============================================================\n")
end

# Machine-readable record of the DEDICATED A16 certificate, one [[gate]] per
# hypothesis of the paper's Theorem 3.5 as verified for A16 (Lemma 6.1 +
# Proposition 6.2 (1)-(6)). Distinct from results/validation_certificate.toml,
# which is the GENERAL literature benchmark (certify_literature.jl). Every
# certified numeric bound is stringified at full BigFloat precision. Companion
# human-readable spec: docs/guide/certificate-spec.md.
# A value for the certificate file: TOML has no `nothing`, and a failed stage
# returns `nothing` in the fields it could not compute.
_s(x) = x === nothing ? "" : string(x)

"""
Prop 6.2(2): the side length ℓ = 2 sin(z/2) and the perimeter 16ℓ, enclosed.

The interval-Newton step of 02 proves z* ∈ r2.Z, so evaluating the same
expression over that box with outward rounding encloses ℓ rigorously. This is a
gate of the verdict: it passes only if the root was certified and the nominal
value lies in the enclosure (if not, the hard-coded literal and the certified
root disagree). It used to be recorded as passed unconditionally and left out
of `final_pass` (2026-09 external audit, D03).
"""
function certify_side_length(r2)
    ell = side_length(z_nominal)
    r2.Z === nothing && return (pass=false, ell=ell, ellI=nothing, perimI=nothing)
    ellI = side_length(r2.Z)
    # 16 as a guaranteed thin interval: a bare Int here would clear
    # IntervalArithmetic's NG flag on the certificate's headline perimeter.
    perimI = A16Certificate._lit(ellI, 16) * ellI
    assert_guaranteed(ellI, "ell enclosure over Z_root")
    assert_guaranteed(perimI, "perimeter enclosure over Z_root")
    println("ell enclosure over Z_root  = ", ellI)
    println("16*ell enclosure over Z_root = ", perimI)
    contains_nominal = inf(ellI) <= ell <= sup(ellI)
    println("nominal ell inside its certified enclosure PASS = ", contains_nominal)
    return (pass=contains_nominal, ell=ell, ellI=ellI, perimI=perimI)
end

function emit_a16_certificate(projroot, final_pass, r2, rl, r3, r4, r5, r6,
                              box_nesting_pass, cert_radius)
    z = z_nominal
    ell = rl.ell
    ellI = rl.ellI
    perimI = rl.perimI
    ell_certified = ellI !== nothing
    commit, clean = _git_state(projroot)
    pkg_version = TOML.parsefile(joinpath(projroot, "Project.toml"))["version"]
    cert = Dict{String,Any}(
        "meta" => Dict{String,Any}(
            "certificate" => "dedicated A16 first-order certificate (pipeline/certify_a16.jl)",
            "paper" => "First Order Geometry of Equilateral Small Polygons (accompanying article)",
            "package" => "A16Certificate v$(pkg_version) [AH26]",
            "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z",
            "julia_version" => string(VERSION),
            "intervalarithmetic_version" => string(pkgversion(IntervalArithmetic)),
            "bigfloat_precision_bits" => precision(BigFloat),
            "git_commit" => commit,
            "git_source_clean" => clean,
            "git_available" => _git_available(projroot),
            "z_root_radius" => _s(r2.radius),
            "z_cert_radius" => string(cert_radius),
        ),
        "verdict" => Dict{String,Any}(
            "first_order_certificate" => final_pass ? "CERTIFIED" : "NOT CERTIFIED",
            "certified" => final_pass,
            "root_unique_in_certified_box" => r2.unique_in_box,
            "root_unique_in_full_search_interval" => r2.unique_in_search_interval,
            "topological_local_maximality" =>
                "not certified by computation; given by paper Theorem 6.3 from " *
                "these certified hypotheses (strict, modulo orientation-preserving " *
                "Euclidean motions, via Theorem 3.5 / Lemma 3.4)",
            "global_optimality" => "not claimed (paper §7)",
        ),
        "configuration" => Dict{String,Any}(
            "n" => 16,
            "z_nominal" => string(z),
            "side_length_ell" => string(ell),
            "perimeter_16ell" => string(16ell),
            "active_diameter_edges" => [[i, j] for (i, j) in ACTIVE_EDGES],
        ),
        "gate" => Any[
            Dict{String,Any}("id"=>"existence", "ref"=>"Prop 6.2(1)",
                "hypothesis"=>"unique constructor root",
                "status"=> (r2.pass && r2.unique_in_search_interval) ? "CERTIFIED" : "FAIL",
                "passed"=> r2.pass && r2.unique_in_search_interval,
                "detail"=>"interval Newton: 0∉F'(Z_root), N(Z_root)⊂int Z_root; unique in box and in full search interval"),
            Dict{String,Any}("id"=>"side_length", "ref"=>"Prop 6.2(2)",
                "hypothesis"=>"common side length ℓ and perimeter 16ℓ",
                "status"=> rl.pass ? "CERTIFIED" : "FAIL",
                "passed"=>rl.pass,
                "detail"=>"ell = 2 sin(z/2) evaluated over the certified root box Z_root with outward rounding; the nominal value is the midpoint-literal evaluation, retained for display",
                "ell"=>string(ell), "perimeter_16ell"=>string(16ell),
                "ell_lower"=> ell_certified ? string(inf(ellI)) : "",
                "ell_upper"=> ell_certified ? string(sup(ellI)) : "",
                "perimeter_lower"=> ell_certified ? string(inf(perimI)) : "",
                "perimeter_upper"=> ell_certified ? string(sup(perimI)) : ""),
            Dict{String,Any}("id"=>"convexity", "ref"=>"Prop 6.2(3)",
                "hypothesis"=>"strict convexity and labelled cyclic order",
                "status"=> r3.support_pass ? "CERTIFIED" : "FAIL", "passed"=>r3.support_pass,
                "min_support_determinant"=>string(r3.worst_support[3]),
                "attained_at"=>[r3.worst_support[1], r3.worst_support[2]]),
            Dict{String,Any}("id"=>"inactive_margin", "ref"=>"Prop 6.2(4)",
                "hypothesis"=>"exact active diameter graph and strict inactive margin",
                "status"=> r3.inactive_pass ? "CERTIFIED" : "FAIL", "passed"=>r3.inactive_pass,
                "inactive_margin_lower_bound"=>string(r3.margin),
                "critical_pair"=>[r3.worst_inactive[1], r3.worst_inactive[2]]),
            Dict{String,Any}("id"=>"multipliers", "ref"=>"Prop 6.2(5)",
                "hypothesis"=>"strictly positive active-diameter multipliers + stationarity identity",
                "status"=> r5.pass ? "CERTIFIED" : "FAIL", "passed"=>r5.pass,
                "min_lambda_lower_bound"=>_s(r5.lambda_lower),
                "omitted_residual_matrix_regularity_bound"=>_s(r5.omitted_bound),
                "alpha_sum_contains_minus16_diagnostic"=>r5.alpha_balance_diagnostic,
                # Prop 6.2(5) states that the FULL multiplier enclosures are recorded
                # here, and the paper's Table 2 displays their midpoints. Emitting only
                # the minimum left both claims unverifiable from the released artifact:
                # a referee could not check a single entry of that table. The 31
                # enclosures below are the certified Krawczyk output, in the packing
                # used throughout: Y[1:16] are the side multipliers alpha_i, and
                # Y[16+k] is the active-diameter multiplier of ACTIVE_EDGES[k].
                "alpha_enclosure"=>[Dict{String,Any}(
                        "index"=>i-1,
                        "lower"=>string(inf(r5.multiplier_enclosure[i])),
                        "upper"=>string(sup(r5.multiplier_enclosure[i])))
                    for i in 1:16 if r5.multiplier_enclosure !== nothing],
                "lambda_enclosure"=>[Dict{String,Any}(
                        "edge"=>[ACTIVE_EDGES[k][1], ACTIVE_EDGES[k][2]],
                        "lower"=>string(inf(r5.multiplier_enclosure[16+k])),
                        "upper"=>string(sup(r5.multiplier_enclosure[16+k])))
                    for k in 1:length(ACTIVE_EDGES) if r5.multiplier_enclosure !== nothing]),
            Dict{String,Any}("id"=>"rank", "ref"=>"Prop 6.2(6)",
                "hypothesis"=>"rank D(e,d)=30 ⇒ I_eq=R_eq",
                "status"=> r4.pass ? "CERTIFIED" : "FAIL", "passed"=>r4.pass,
                "preconditioned_regularity_bound"=>string(r4.bound)),
            Dict{String,Any}("id"=>"exact_identities", "ref"=>"Lemma 6.1",
                "hypothesis"=>"16 side + 15 active-diameter equalities, exact Q[c] algebra (no interval containing zero)",
                "status"=> r6.pass ? "PROVEN" : "FAIL", "passed"=>r6.pass,
                "sides_proved"=>r6.sides, "sides_total"=>16,
                "diameters_proved"=>r6.diams, "diameters_total"=>15),
            Dict{String,Any}("id"=>"box_nesting", "ref"=>"Prop 6.2 (Z_root ⊂ int Z_cert)",
                "hypothesis"=>"root box nested inside certificate box (composition gate)",
                "status"=> box_nesting_pass ? "CERTIFIED" : "FAIL", "passed"=>box_nesting_pass),
        ],
        "source_sha256" => [Dict{String,Any}("file"=>f, "sha256"=>h)
                            for (f, h) in _source_hashes(projroot)],
    )
    outpath = joinpath(projroot, "results", "a16_certificate.toml")
    mkpath(dirname(outpath))
    open(outpath, "w") do io
        println(io, "# Dedicated A16 first-order certificate — machine-readable record.")
        println(io, "# Auto-generated by pipeline/certify_a16.jl; do not edit.")
        println(io, "# Reconstruct: git checkout <git_commit>; julia --project=. pipeline/certify_a16.jl")
        println(io, "# Companion human-readable spec: docs/guide/certificate-spec.md.")
        TOML.print(io, cert; sorted=true)
    end
    return outpath
end

# Shared box radius Z_cert for the geometry/rank/multiplier certificates
# (Prop 6.2 (3)-(6)). The root certificate (02) may succeed at a tighter radius
# Z_root; see the box nesting check below (docs/guide/provenance-mapping.md, Prop 6.2:
# Z_root ⊂ int Z_cert).
const CERT_RADIUS = big"1e-28"

print_provenance()

println("\n=== 01 NOMINAL ===")
run_nominal()
println("\n=== 02 ROOT ===")
r2 = run_root_interval()
println("\n=== 03 GEOMETRY ===")
r3 = run_geometry_interval(radius=CERT_RADIUS)
println("\n=== 04 RANK ===")
r4 = run_rank_interval(radius=CERT_RADIUS)
println("\n=== 05 MULTIPLIERS ===")
r5 = run_multipliers_interval(radius=CERT_RADIUS)
println("\n=== 06 EXACT IDENTITIES ===")
r6 = run_identity_audit()
println("\n=== SIDE LENGTH (Prop 6.2(2)) ===")
rl = certify_side_length(r2)

println("\n=== BOX NESTING (docs/guide/provenance-mapping.md, Prop 6.2: Z_root ⊂ int Z_cert) ===")
# Lemma 6.1's exact identities and Prop 6.2(3)-(6)'s interval certificates are
# only composable with Prop 6.2(1)'s certified root if the root box is nested
# inside the geometry/rank/multiplier box. Checked by comparing ENDPOINTS against
# the box each of stages 03, 04 and 05 actually evaluated -- not by comparing
# radii, which relied on every stage building its box by the same expression
# around the same centre (2026-09 external audit, D04).
strictly_inside(inner, outer) = inf(outer) < inf(inner) && sup(inner) < sup(outer)
box_nesting_pass = r2.pass &&
    all(strictly_inside(r2.Z, r.Z) for r in (r3, r4, r5))
println("root box radius = ", r2.radius)
println("geometry/rank/multiplier box radius = ", CERT_RADIUS)
println("root box inside the interior of the boxes of 03, 04, 05 PASS = ", box_nesting_pass)

# The verdict. Every gate enters it, including root uniqueness on the whole of
# I_search (which the article says is what pins the configuration; it used to
# be reported but not required, D01) and the side-length enclosure (D03). A
# failed gate yields NOT CERTIFIED and a certificate file with FAIL entries;
# nothing aborts except a lost guarantee flag, which is a bug in the code, not
# a failed hypothesis (D02).
final_pass = box_nesting_pass && r2.pass && r2.unique_in_search_interval &&
    rl.pass && r3.support_pass && r3.inactive_pass && r4.pass && r5.pass && r6.pass
println("\n============================================================")
println("FINAL FIRST-ORDER CERTIFICATE: ", final_pass ? "CERTIFIED" : "NOT CERTIFIED")
println("ROOT UNIQUENESS IN CERTIFIED BOX: ", r2.unique_in_box ? "PROVED" : "NOT PROVED")
println("ROOT UNIQUENESS IN FULL SEARCH INTERVAL: ",
        r2.unique_in_search_interval ? "PROVED (F strictly monotone there)" : "NOT PROVED")
println("TOPOLOGICAL LOCAL MAXIMALITY: NOT ESTABLISHED BY *THIS* RUN — PROVED IN LEAN")
println("    This interval certificate establishes the hypotheses of paper Thm 3.5,")
println("    not its conclusion. The conclusion is proved separately and kernel-checked:")
println("    Chiquipoli.Feasible.A16_locally_maximal (run `make lean`), giving strict")
println("    local maximality modulo orientation-preserving Euclidean motions.")
println("    What no computation establishes is that this configuration is the")
println("    published Bingane-Audet polygon (an attribution; see the OPTIGON")
println("    cross-check in the test suite) or anything about global optimality.")
println("GLOBAL OPTIMALITY: NOT CLAIMED")
println("============================================================")

# CHIQUI_NO_RECORD=1 (make A16, make check-case): every gate runs and the
# verdict is printed, but results/a16_certificate.toml is left untouched, so a
# check of one candidate never rewrites the record of a full run.
if get(ENV, "CHIQUI_NO_RECORD", "") == "1"
    println("\n(CHIQUI_NO_RECORD=1 — results/a16_certificate.toml was left untouched)")
else
    let projroot = normpath(joinpath(@__DIR__, ".."))
        outpath = emit_a16_certificate(projroot, final_pass, r2, rl, r3, r4, r5, r6,
                                       box_nesting_pass, CERT_RADIUS)
        println("\nwrote machine-readable certificate: ", relpath(outpath, projroot))
    end
end
# A run that is not CERTIFIED must fail as a process too, so that a caller
# (make, tools/check_all.sh) sees it without reading the text.
final_pass || exit(1)
