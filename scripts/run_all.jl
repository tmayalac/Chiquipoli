include(joinpath(@__DIR__, "_bootstrap.jl"))
include(joinpath(@__DIR__, "01_nominal.jl"))
include(joinpath(@__DIR__, "02_root_interval.jl"))
include(joinpath(@__DIR__, "03_geometry_interval.jl"))
include(joinpath(@__DIR__, "04_rank_interval.jl"))
include(joinpath(@__DIR__, "05_multipliers_interval.jl"))
include(joinpath(@__DIR__, "06_exact_identities.jl"))

using Dates, SHA, Pkg, TOML

# Load-bearing source files, and their SHA256 hashes, tying an archived run to
# the exact source that produced it. Single source of truth for both the
# printed provenance header and the machine-readable certificate below.
function _source_hashes(projroot)
    files = String[]
    for d in ("src", "scripts", "test")
        dir = joinpath(projroot, d)
        isdir(dir) || continue
        for f in sort(readdir(dir))
            endswith(f, ".jl") && push!(files, joinpath(d, f))
        end
    end
    append!(files, ["Project.toml", "Manifest.toml"])
    hashed = [(rel, bytes2hex(sha256(read(joinpath(projroot, rel)))))
              for rel in files if isfile(joinpath(projroot, rel))]
    # Guardrail. The scan above is directory-driven and NOT recursive: a
    # load-bearing file moved out of src/, scripts/ or test/, or into a
    # subdirectory of one of them, would drop out of the provenance chain with
    # no error at all. Pin the count so a restructuring fails loudly. If you
    # add or remove a load-bearing source, change this number deliberately.
    @assert length(hashed) == 18 "provenance covers $(length(hashed)) files, expected 18 - a load-bearing source moved, was added, or was removed"
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
        src_status = read(`git -C $projroot status --porcelain -- src scripts test Project.toml Manifest.toml`, String)
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
    r = interval(BigFloat(1)) / 3
    println("directed-rounding self-check (interval(1)/3 has inf<sup) = ",
            inf(r) < sup(r), "   [", inf(r), ", ", sup(r), "]")

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
            src_status = read(`git -C $projroot status --porcelain -- src scripts test Project.toml Manifest.toml`, String)
            dirty = !isempty(strip(src_status))
            println("git commit           = ", commit, dirty ? "  (SOURCE DIRTY — log not tied to this commit)" : "  (source clean — log matches this commit)")
        catch e
            println("git commit           = (unavailable: ", e, ")")
        end
    end

    # SHA256 of every load-bearing source file.
    println("SHA256 of source files:")
    files = String[]
    for d in ("src", "scripts", "test")
        dir = joinpath(projroot, d)
        isdir(dir) || continue
        for f in sort(readdir(dir))
            endswith(f, ".jl") && push!(files, joinpath(d, f))
        end
    end
    append!(files, ["Project.toml", "Manifest.toml"])
    for rel in files
        path = joinpath(projroot, rel)
        if isfile(path)
            h = bytes2hex(sha256(read(path)))
            println("  ", h, "  ", rel)
        end
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
# which is the GENERAL literature benchmark (run_literature.jl). Every
# certified numeric bound is stringified at full BigFloat precision. Companion
# human-readable spec: docs/certificate-spec.md.
function emit_a16_certificate(projroot, final_pass, r2, r3, r4, r5, r6,
                              box_nesting_pass, cert_radius)
    z = z_nominal
    ell = side_length(z)
    # Prop 6.2(2) states an ENCLOSURE of ℓ at the exact root, and the proof of
    # Prop 6.2 attributes items (2)-(4) to outward-rounded evaluation. The
    # nominal 2sin(z_nominal/2) above is a point evaluation at a hard-coded
    # literal, so on its own it did not support that claim — this gate was the
    # only one in the certificate marked NOMINAL rather than CERTIFIED.
    # The interval-Newton step of 02 proves z* ∈ r2.Z, so evaluating the same
    # expression over that box with outward rounding encloses ℓ rigorously.
    ellI = r2.Z === nothing ? nothing : side_length(r2.Z)
    ell_certified = ellI !== nothing
    # 16 as a guaranteed thin interval: a bare Int here would clear
    # IntervalArithmetic's NG flag on the certificate's headline perimeter.
    perimI = ell_certified ? A16Certificate._lit(ellI, 16) * ellI : nothing
    if ell_certified
        assert_guaranteed(ellI, "ell enclosure over Z_root")
        assert_guaranteed(perimI, "perimeter enclosure over Z_root")
        println("\nell enclosure over Z_root  = ", ellI)
        println("16*ell enclosure over Z_root = ", perimI)
        # The enclosure must contain the nominal value, or the hard-coded
        # literal and the certified root disagree.
        @assert inf(ellI) <= ell <= sup(ellI) "nominal ell outside its certified enclosure"
    end
    commit, clean = _git_state(projroot)
    pkg_version = TOML.parsefile(joinpath(projroot, "Project.toml"))["version"]
    cert = Dict{String,Any}(
        "meta" => Dict{String,Any}(
            "certificate" => "dedicated A16 first-order certificate (scripts/run_all.jl)",
            "paper" => "Stability of Equilateral Small Polygons (accompanying article)",
            "package" => "A16Certificate v$(pkg_version) [AH26]",
            "utc" => Dates.format(now(UTC), "yyyy-mm-ddTHH:MM:SS") * "Z",
            "julia_version" => string(VERSION),
            "intervalarithmetic_version" => string(pkgversion(IntervalArithmetic)),
            "bigfloat_precision_bits" => precision(BigFloat),
            "git_commit" => commit,
            "git_source_clean" => clean,
            "git_available" => _git_available(projroot),
            "z_root_radius" => string(r2.radius),
            "z_cert_radius" => string(cert_radius),
        ),
        "verdict" => Dict{String,Any}(
            "first_order_certificate" => final_pass ? "CERTIFIED" : "NOT CERTIFIED",
            "certified" => final_pass,
            "root_unique_in_certified_box" => r2.unique_in_box,
            "root_unique_in_full_search_interval" => r2.unique_in_search_interval,
            "topological_local_maximality" =>
                "not certified by computation; given by paper Theorem 6.4 from " *
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
                "status"=> r2.pass ? "CERTIFIED" : "FAIL", "passed"=>r2.pass,
                "detail"=>"interval Newton: 0∉F'(Z_root), N(Z_root)⊂int Z_root; unique in box and in full search interval"),
            Dict{String,Any}("id"=>"side_length", "ref"=>"Prop 6.2(2)",
                "hypothesis"=>"common side length ℓ and perimeter 16ℓ",
                "status"=> ell_certified ? "CERTIFIED" : "NOMINAL",
                "passed"=>true,
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
                "min_lambda_lower_bound"=>string(r5.lambda_lower),
                "omitted_residual_matrix_regularity_bound"=>string(r5.omitted_bound),
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
                    for i in 1:16],
                "lambda_enclosure"=>[Dict{String,Any}(
                        "edge"=>[ACTIVE_EDGES[k][1], ACTIVE_EDGES[k][2]],
                        "lower"=>string(inf(r5.multiplier_enclosure[16+k])),
                        "upper"=>string(sup(r5.multiplier_enclosure[16+k])))
                    for k in 1:length(ACTIVE_EDGES)]),
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
        println(io, "# Auto-generated by scripts/run_all.jl; do not edit.")
        println(io, "# Reconstruct: git checkout <git_commit>; julia --project=. scripts/run_all.jl")
        println(io, "# Companion human-readable spec: docs/certificate-spec.md.")
        TOML.print(io, cert; sorted=true)
    end
    return outpath
end

# Shared box radius Z_cert for the geometry/rank/multiplier certificates
# (Prop 6.2 (3)-(6)). The root certificate (02) may succeed at a tighter radius
# Z_root; see the box nesting check below (docs/provenance-mapping.md, Prop 6.2:
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

println("\n=== BOX NESTING (docs/provenance-mapping.md, Prop 6.2: Z_root ⊂ int Z_cert) ===")
# Lemma 6.1's exact identities and Prop 6.2(3)-(6)'s interval certificates are
# only composable with Prop 6.2(1)'s certified root if the root box is nested
# inside the geometry/rank/multiplier box. This was previously an unverified
# assumption from matching literal constants across scripts; now an explicit gate.
box_nesting_pass = r2.pass && (r2.radius <= CERT_RADIUS)
println("root box radius = ", r2.radius)
println("geometry/rank/multiplier box radius = ", CERT_RADIUS)
println("root box nested inside certificate box PASS = ", box_nesting_pass)
@assert box_nesting_pass "root-certified box is not nested inside the geometry/rank/multiplier box; the composition argument in docs/provenance-mapping.md (Prop 6.2, box nesting Z_root ⊂ int Z_cert) does not apply"

final_pass = box_nesting_pass && r2.pass && r3.support_pass && r3.inactive_pass && r4.pass && r5.pass && r6.pass
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

let projroot = normpath(joinpath(@__DIR__, ".."))
    outpath = emit_a16_certificate(projroot, final_pass, r2, r3, r4, r5, r6,
                                   box_nesting_pass, CERT_RADIUS)
    println("\nwrote machine-readable certificate: ", relpath(outpath, projroot))
end
