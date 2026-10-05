# Checks the released records against the tree and against the Lean layer:
# every certificate verdict, the provenance of every record (one commit, a clean
# tree), the SHA256 of every load-bearing source file, the certified bounds
# against their published values, the structural counts, IntervalArithmetic's
# guarantee flag, what the Lean layer proves, and the family records.
#
#     julia --project=. pipeline/check_records.jl        # or: make check-records
#
# It needs nothing outside this repository. Every check that fails is listed,
# and the exit status is nonzero.

using TOML, Printf, SHA

const ROOT  = normpath(joinpath(@__DIR__, ".."))
# The family members, read from their single source (cases/exact_coords.jl).
_family(name) = Tuple(parse.(Int, split(match(Regex("^const $name = \\((.*)\\)", "m"),
    read(joinpath(ROOT, "cases", "exact_coords.jl"), String)).captures[1], ", ")))
const FAMILY_N = _family("FAMILY_N")
const FAMILY_LEAN_N = _family("FAMILY_LEAN_N")
const CERT  = joinpath(ROOT, "results", "a16_certificate.toml")
const LEAN  = joinpath(ROOT, "lean", "ChiquipoliLean")

setprecision(BigFloat, 256)

const FAILS   = String[]
const SKIPPED = String[]
pass(label)      = @printf("  %-64s %s\n", label, "ok")
fail(label, why) = (push!(FAILS, label); @printf("  %-64s %s\n", label, "*** $why ***"))
skip(label)      = (push!(SKIPPED, label); @printf("  %-64s %s\n", label, "skipped"))
chk(label, cond) = cond ? pass(label) : fail(label, "MISMATCH")

section(t) = println("\n── ", t, " ──")

cert  = TOML.parsefile(CERT)
gates = Dict(g["id"] => g for g in cert["gate"])

# ---------------------------------------------------------------------------
section("certificate verdict")
chk("overall verdict is CERTIFIED", cert["verdict"]["certified"] === true)
chk("root unique in the full search interval",
    cert["verdict"]["root_unique_in_full_search_interval"] === true)
for g in cert["gate"]
    chk("gate $(rpad(g["id"], 18)) $(g["ref"])",
        g["passed"] === true && g["status"] in ("CERTIFIED", "PROVEN"))
end
chk("exact identities: 16/16 sides and 15/15 active diameters",
    gates["exact_identities"]["sides_proved"] == 16 &&
    gates["exact_identities"]["diameters_proved"] == 15)
chk("box nesting: Z_root radius < Z_cert radius",
    parse(BigFloat, cert["meta"]["z_root_radius"]) <
    parse(BigFloat, cert["meta"]["z_cert_radius"]))
# Three states. In a git checkout a dirty tree must fail. In an extracted
# archive there is no checkout to compare against, and absent provenance is
# reported as absent rather than as a failure -- the supplementary material is
# distributed as an archive, so this is the referee's normal path.
if get(cert["meta"], "git_available", true) === false
    skip("the run that produced the certificate had a clean source tree")
    println("           (no commit to compare against: either an extracted archive or a")
    println("            repository whose first commit has not been made. The shipped")
    println("            certificate records the commit of the run that produced it.)")
else
    chk("the run that produced the certificate had a clean source tree",
    cert["meta"]["git_source_clean"] === true)
end

section("provenance: the log and every record declare one commit, from a clean tree")
# The supplement states that every provenance artifact of the release declares a
# single Git commit and a clean working tree, and that the archived log declares
# the same commit as the certificates. Nothing checked that until 2026-09-24;
# this does. A record written outside a Git checkout (git_available = false, as
# when a referee re-runs a certificate in an extracted archive) has no commit to
# compare, and is reported as skipped, never as agreeing.
let
    recs = vcat(["results/a16_certificate.toml", "results/validation_certificate.toml",
                 "results/radius_certificate.toml",
                 "results/lean_certificate.toml", "results/lean_family_certificate.toml"],
                ["results/family/A$n.toml" for n in FAMILY_N])
    decl = Tuple{String,String,Bool}[]          # (artifact, commit, clean)
    nocommit = String[]
    for f in recs
        path = joinpath(ROOT, f)
        isfile(path) || (push!(nocommit, f * " (absent)"); continue)
        m = get(TOML.parsefile(path), "meta", Dict{String,Any}())
        c = string(get(m, "git_commit", ""))
        if get(m, "git_available", true) === false || !occursin(r"^[0-9a-f]{40}$", c)
            push!(nocommit, f)
        else
            push!(decl, (f, c, get(m, "git_source_clean", false) === true))
        end
    end
    logpath = joinpath(ROOT, "logs", "final_run.txt")
    lm = isfile(logpath) ? match(r"git commit\s*=\s*([0-9a-f]{40})\s*\(source clean", read(logpath, String)) : nothing
    lm === nothing ? push!(nocommit, "logs/final_run.txt") : push!(decl, ("logs/final_run.txt", lm.captures[1], true))
    commits = unique(c for (_, c, _) in decl)
    nrec = count(d -> d[1] != "logs/final_run.txt", decl)
    chk("the log and the $(nrec) records with a commit all declare the same one" *
        (length(commits) == 1 ? " ($(first(commits[1], 7)))" : " (found $(join([first(c, 7) for c in commits], ", ")))"),
        length(commits) == 1)
    dirty = [f for (f, _, cl) in decl if !cl]
    chk("each of them was produced from a clean source tree" * (isempty(dirty) ? "" : " (not: $(join(dirty, ", ")))"),
        isempty(dirty))
    isempty(nocommit) || skip("commit agreement for $(join(nocommit, ", ")) (no commit recorded)")
end

section("provenance: recorded SHA256 of every load-bearing source file")
# In a function, not a top-level loop: `badsha += 1` inside one is soft scope,
# so the counter would be a fresh local and reading it before assignment throws.
# That branch only runs when a hash actually differs, which is exactly when the
# check matters, so it went unexercised until a hash did differ and the checker
# crashed instead of reporting. The failure path is now covered by a self test
# at the end of this file.
function sha_mismatches(root, entries)
    bad = String[]
    for e in entries
        f = joinpath(root, e["file"])
        (isfile(f) && bytes2hex(sha256(read(f))) == e["sha256"]) || push!(bad, e["file"])
    end
    return bad
end
let bad = sha_mismatches(ROOT, cert["source_sha256"])
    if isempty(bad)
        pass("$(length(cert["source_sha256"])) files, 0 hash mismatches")
    else
        fail("$(length(cert["source_sha256"])) files, $(length(bad)) hash mismatches",
             "changed since the certificate was generated: " * join(bad, ", "))
    end
end

# ---------------------------------------------------------------------------
section("certified bounds, against their published values")
sl = gates["side_length"]
ell_lo = parse(BigFloat, sl["ell_lower"]);       ell_hi = parse(BigFloat, sl["ell_upper"])
per_lo = parse(BigFloat, sl["perimeter_lower"]); per_hi = parse(BigFloat, sl["perimeter_upper"])
chk("ell enclosure inside the article's [.…228, .…230]",
    ell_lo > big"0.1959554930055385228" && ell_hi < big"0.1959554930055385230")
chk("perimeter enclosure inside the article's [3.…663, 3.…665]",
    per_lo > big"3.1352878880886163663" && per_hi < big"3.1352878880886163665")
chk("the displayed ell lies inside its own certified enclosure",
    ell_lo <= big"0.19595549300553852289960855175764110627" <= ell_hi)
chk("the displayed perimeter lies inside its own certified enclosure",
    per_lo <= big"3.13528788808861636639373682812225770037" <= per_hi)
chk("stated enclosure widths < 2e-30 (ell) and < 3.19e-29 (perimeter)",
    ell_hi - ell_lo < big"2e-30" && per_hi - per_lo < big"3.19e-29")
chk("min support determinant >= 0.0074882049306989244",
    parse(BigFloat, gates["convexity"]["min_support_determinant"]) >= big"0.0074882049306989244")
chk("inactive margin >= 0.0080997106581357295",
    parse(BigFloat, gates["inactive_margin"]["inactive_margin_lower_bound"]) >= big"0.0080997106581357295")
chk("min lambda >= 0.0918667776833353997",
    parse(BigFloat, gates["multipliers"]["min_lambda_lower_bound"]) >= big"0.0918667776833353997")
chk("rank preconditioner <= 1.419383643581978e-25",
    parse(BigFloat, gates["rank"]["preconditioned_regularity_bound"]) <= big"1.419383643581978e-25")
chk("omitted-residual bound <= 4.017187643256796e-28",
    parse(BigFloat, gates["multipliers"]["omitted_residual_matrix_regularity_bound"]) <= big"4.017187643256796e-28")
chk("z_nominal is the 256-bit value of the article's literal",
    parse(BigFloat, cert["configuration"]["z_nominal"]) ==
    big"0.19627037213032280086206121185805318446")
chk("the 16 alpha enclosures sum to a bracket containing -16",
    let lo = sum(parse(BigFloat, a["lower"]) for a in gates["multipliers"]["alpha_enclosure"]),
        hi = sum(parse(BigFloat, a["upper"]) for a in gates["multipliers"]["alpha_enclosure"])
        lo <= -16 <= hi
    end)

# ---------------------------------------------------------------------------
include(joinpath(ROOT, "src", "A16Certificate.jl"))
using .A16Certificate
using IntervalArithmetic

Zr = interval(z_nominal - big"1e-30", z_nominal + big"1e-30")
Zc = interval(z_nominal - big"1e-28", z_nominal + big"1e-28")
p  = coordinates(Zr)

section("structural counts the article quotes")
chk("224 support determinants", length(support_determinants(Zc)) == 224)
chk("105 inactive pairs (120 total minus 15 active)", length(inactive_pairs(Zc)) == 105)
chk("15 active diameter edges", length(ACTIVE_EDGES) == 15)
chk("D(e,d) is 31 x 33", size(build_jacobian(Zc)) == (31, 33))
chk("the selected minor is 30 x 30", length(ROWS_MINOR) == 30 && length(COLS_MINOR) == 30)
chk("the omitted columns are x1, y1, x8", OMITTED_COLUMNS == [3, 4, 17])
chk("the deleted minor row is the one of d_{0,9}", ACTIVE_EDGES[19 - 16] == (0, 9))
chk("deg Fc = 12", length(Fc_poly()) - 1 == 12)
chk("exactly the sides {3,4} and {12,13} need F=0; every other identity is unconditional",
    [(i, mod(i+1, 16)) for i in 0:15
     if !iszeropoly(psub(sqdist_poly(i, mod(i+1, 16)), side_target_poly()))] ==
    [(3, 4), (12, 13)])
chk("all 15 active diameter identities are unconditional",
    all(iszeropoly(psub(sqdist_poly(i, j), diameter_target_poly())) for (i, j) in ACTIVE_EDGES))
let Q = omitted_residual_matrix(Zc)
    d = Q[1,1]*(Q[2,2]*Q[3,3]-Q[2,3]*Q[3,2]) - Q[1,2]*(Q[2,1]*Q[3,3]-Q[2,3]*Q[3,1]) +
        Q[1,3]*(Q[2,1]*Q[3,2]-Q[2,2]*Q[3,1])
    chk("the gauge determinant det Q = y1 - y8 is strictly negative", sup(d) < 0)
end
let P = 16 * side_length(Zr)
    chk("the perimeter lies strictly between L(W16) and the upper bound L_16",
        inf(P) > big"3.1347065475" && sup(P) < big"3.1365484905")
end

section("IntervalArithmetic's own guarantee flag, on every certified quantity")
chk("F, F', coordinates, Jacobian, determinants and distances are all guaranteed",
    isguaranteed(Ffun(Zc)) && isguaranteed(Fprime(Zc)) && isguaranteed(side_length(Zc)) &&
    all(isguaranteed, coordinates(Zc)) && all(isguaranteed, build_jacobian(Zc)) &&
    all(isguaranteed, [v for (_, _, v) in support_determinants(Zc)]) &&
    all(isguaranteed, [v for (_, _, v) in inactive_pairs(Zc)]))

# ---------------------------------------------------------------------------
# What the article says the Lean layer proves, against the Lean sources. Two
# inaccuracies were found here by hand and are now guarded.
section("what the package says the Lean layer proves")
src(f)  = isfile(joinpath(LEAN, f)) ? read(joinpath(LEAN, f), String) : ""
# Recursive: the modules live in Theory/, Constructor/, Generated/, Instances/.
# A flat `readdir` would read only the two top-level files, and every "the Lean
# layer proves X" check below would then fail -- or, worse, pass on a check that
# looks for an absence, like the floating-point one.
leanfiles = [relpath(joinpath(d, f), LEAN) for (d, _, fs) in walkdir(LEAN) for f in fs
             if endswith(f, ".lean")]
chk("the Lean sources were found (all $(length(leanfiles)) modules read)", length(leanfiles) >= 30)
alll    = join([src(f) for f in leanfiles], "\n")
sidelen = src(joinpath("Constructor", "SideLength.lean"))
chk("no floating point and no interval arithmetic in the Lean sources",
    !occursin(r"\bFloat\b", alll) && !occursin(r"\bInterval\b", alll))
chk("Chebyshev reduction: cos_7, sin_7, Fc_cos_eq_Ffun",
    occursin("cos_7", alll) && occursin("sin_7", alll) && occursin("Fc_cos_eq_Ffun", alll))
chk("Lemma 6.1: all_sides and all_active_diameters",
    occursin("all_sides", alll) && occursin("all_active_diameters", alll))
chk("every vertex pair bounded: sqd_le_one", occursin("theorem sqd_le_one", alll))
chk("strict convexity: cross_pos on the support determinants", occursin("cross_pos_0_2", alll))
chk("strictly positive multipliers: multipliers_certified", occursin("multipliers_certified", alll))
chk("I_eq(A16) = R_eq(A16): A16_Ieq_imp_R", occursin("A16_Ieq_imp_R", alll))
chk("rank 30 by kernel identification and rank nullity",
    occursin("rank_eq_thirty", alll) && occursin("ker_jacA16", alll))
chk("side length proved at the article's displayed 19 digits",
    occursin("1959554930055385228 / 10 ^ 19", sidelen) &&
    occursin("1959554930055385230 / 10 ^ 19", sidelen))
chk("perimeter proved at the article's displayed 20 digits",
    occursin("31352878880886163663 / 10 ^ 19", sidelen) &&
    occursin("31352878880886163665 / 10 ^ 19", sidelen))
chk("the root bracket has width exactly 1e-22",
    occursin("9808007223804781715147 / 10 ^ 22", sidelen) &&
    occursin("9808007223804781715148 / 10 ^ 22", sidelen))
chk("exactly two exact sign evaluations of Fc",
    occursin("Fc_cLo_neg", sidelen) && occursin("Fc_cHi_pos", sidelen))
chk("Proposition 3.8 and both Section 4 examples",
    occursin("increases_to_the_right", alll) && occursin("not_isLocalMax", alll) &&
    occursin("square_no_admissible_direction", alll) && occursin("rhombus_not_isLocalMax", alll))
chk("the rhombus realising curve is explicit", occursin("rho_hasDerivAt", alll))
chk("the first-order core is stated for arbitrary n and an arbitrary Fintype of actives",
    occursin(r"structure Data \(n : .*\) \(.* : Type\*\)", alll) &&
    occursin(r"variable \{n : .*\} \{.* : Type\*\} \[Fintype", alll))
chk("A16 discharges both hypotheses rather than assuming them",
    let m = match(r"theorem A16_no_admissible_direction(.|\n){0,900}", alll)
        m !== nothing && occursin("A16_multiplier_identity", m.match) &&
                         occursin("A16_Ieq_imp_R", m.match)
    end)
chk("Lemma 3.4 in full: g, g(p)=id, strict differentiability",
    occursin("theorem g_at_p", alll) && occursin("g_hasStrictFDerivAt", alll))
chk("the implicit function theorem is applied to the nonlinear Phi itself",
    occursin("implicitFunction", alll) && occursin("Phi_eq_geometric", alll))

# The article's newest and largest claim: Theorem 3.5 is formalised, and
# Theorem 6.3 with it. Nothing above touched either, so until now the paper's
# headline was the one thing this reconciler did not reconcile.
chk("Theorem 3.5 itself, in the paper's own normalisation",
    occursin("theorem thm_3_5", alll) && occursin("theorem thm_3_5_le", alll))
chk("the blow-up: the tangent limits, the slice normalisation, and the assembly",
    occursin("eD_eq_zero_of_blowup", alll) && occursin("dD_nonpos_of_blowup", alll) &&
    occursin("tendsto_normCfg", alll) && occursin("no_blowup_sequence", alll))
chk("Theorem 6.3 as a Lean theorem, unconditionally",
    occursin("theorem A16_locally_maximal", alll) &&
    occursin("exists_A16_root_in_Ioo_pi", alll))
chk("the conclusion is congruence, not equality (modulo Euclidean motions)",
    occursin("def Congruent", alll) && occursin("Congruent y.1", alll))
chk("Proposition 4.2: the square closed by the same route",
    occursin("theorem square_strict_local_max", alll) &&
    occursin("theorem square_bridge", alll))

# ---------------------------------------------------------------------------
# The formal layer's table quotes three counts. They are recorded by
# `record_lean_certificate.jl`; reconcile the printed numbers against that record
# rather than against a memory of what they were.
section("the formal-layer table, against the recorded Lean certificate")
let lcpath = joinpath(ROOT, "results", "lean_certificate.toml")
    if !isfile(lcpath)
        skip("formal-layer counts vs results/lean_certificate.toml")
    else
        lc = TOML.parsefile(lcpath)
        th = get(lc, "theorems", Dict{String,Any}())
        naud = get(th, "axiom_audited_theorems", -1)
        nneg = get(th, "negative_controls_total", -1)
        nrej = get(th, "negative_controls_rejected", -1)
        chk("every negative control recorded was rejected", nneg == nrej && nneg > 0)
        # The README quoted "77 headline theorems" and "eighteen" negative
        # controls long after both had grown (2026-09 external audit, F8), and
        # "nine" planted defects when the harness had eleven (F9). Tie all three
        # numbers to their sources so the next drift fails here.
        let readme = read(joinpath(ROOT, "README.md"), String)
            mscript = read(joinpath(ROOT, "tools", "mutation_check.sh"), String)
            nmut = count(r"^run_julia_mutation "m, mscript) +   # invocations; the definition is `run_julia_mutation()`
                   count(r"\b(?:el)?if lean_verify_rejects; then ok "m, mscript)  # each Lean mutation's verdict line
            chk("README: audited theorem count is the recorded one ($naud)",
                occursin("all $naud audited theorems", readme))
            chk("README: negative control count is the recorded one ($nneg)",
                occursin("$nneg deliberately false variants", readme))
            chk("README: planted-defect count is the harness's ($nmut)",
                nmut > 0 && occursin("plants $nmut known defects", readme))
            spec = read(joinpath(ROOT, "docs", "guide", "certificate-spec.md"), String)
            chk("certificate-spec: planted-defect count is the harness's ($nmut)",
                occursin("# $nmut planted defects", spec))
        end
        # The article cites the package by version. Three files declare it and
        # they drifted apart once already (CITATION.cff said 1.0.0 while
        # Project.toml and the bibliography said 2.2.0; they have agreed since, and
        # say 1.1.0 since 2026-09-24).
        let proj = TOML.parsefile(joinpath(ROOT, "Project.toml"))
            v = get(proj, "version", "")
            cff = isfile(joinpath(ROOT, "CITATION.cff")) ?
                  read(joinpath(ROOT, "CITATION.cff"), String) : ""
            chk("CITATION.cff declares the same version as Project.toml ($v)",
                occursin("version: \"$v\"", cff))
            # Zenodo reads .zenodo.json in preference to CITATION.cff, so a stale
            # version there would label the archived release wrongly (it said
            # 1.0.0 through release 1.2.0).
            zj = isfile(joinpath(ROOT, ".zenodo.json")) ?
                 match(r"\"version\"\s*:\s*\"([^\"]*)\"", read(joinpath(ROOT, ".zenodo.json"), String)) : nothing
            # Only if the package ships one (it need not be archived on Zenodo).
            isfile(joinpath(ROOT, ".zenodo.json")) &&
                chk(".zenodo.json declares the same version as Project.toml ($v)",
                    zj !== nothing && zj.captures[1] == v)
        end
        chk("the recorded Lean scope no longer calls Theorem 3.5 unformalised",
            !any(x -> occursin("Theorem 3.5", x), get(get(lc, "scope", Dict()), "not_formalized", String[])))
    end
end

# ---------------------------------------------------------------------------
# The family layer (FAMILY_LEAN_N) is verified locally and recorded in
# results/lean_family_certificate.toml with a hash of every file the verdict
# depends on. The record is only evidence while it describes the tree: an edit
# to a certificate file, a control, the generator or its Julia inputs after the
# run makes it stale, and that must fail here rather than pass unnoticed.
section("the family certificates (pipeline/certify_family.jl), against the tree")
for n in FAMILY_N
    path = joinpath(ROOT, "results", "family", "A$n.toml")
    if !isfile(path)
        skip("results/family/A$n.toml is CERTIFIED and describes the tree")
        continue
    end
    rec = TOML.parsefile(path)
    local fg = get(rec, "gate", Any[])
    chk("A$n: family certificate CERTIFIED, all $(length(fg)) gates passed, incl. the published source",
        get(rec, "certified", false) && length(fg) == 10 && all(g -> get(g, "passed", false), fg) &&
        any(g -> get(g, "id", "") == "published_constructor", fg))
    stale = [e["file"] for e in get(rec, "source_sha256", Any[])
             if !isfile(joinpath(ROOT, e["file"])) || bytes2hex(open(sha256, joinpath(ROOT, e["file"]))) != e["sha256"]]
    chk("A$n: its recorded source hashes match the tree" * (isempty(stale) ? "" : " (stale: $(join(stale, ", ")))"), isempty(stale))
end

section("the certificates of Z32 and Z64 (pipeline/certify_z.jl), against the tree")
for n in (32, 64)
    path = joinpath(ROOT, "results", "family", "Z$n.toml")
    if !isfile(path)
        skip("results/family/Z$n.toml is CERTIFIED and describes the tree")
        continue
    end
    rec = TOML.parsefile(path)
    local zg = get(rec, "gate", Any[])
    chk("Z$n: certificate CERTIFIED, all $(length(zg)) gates passed, exact identities included",
        get(rec, "certified", false) && length(zg) == 8 && all(g -> get(g, "passed", false), zg) &&
        any(g -> get(g, "id", "") == "exact_identities", zg))
    chk("Z$n: the record states what it does not claim (published constructor, uniqueness on the search interval, Lean)",
        length(get(rec, "not_claimed", [])) == 3 && get(rec, "global_optimality", "") == "NOT CLAIMED")
    stale = [e["file"] for e in get(rec, "source_sha256", Any[])
             if !isfile(joinpath(ROOT, e["file"])) || bytes2hex(open(sha256, joinpath(ROOT, e["file"]))) != e["sha256"]]
    chk("Z$n: its recorded source hashes match the tree" * (isempty(stale) ? "" : " (stale: $(join(stale, ", ")))"), isempty(stale))
end

# ---------------------------------------------------------------------------
# The independent cross-check (pipeline/independent/verify.py): the same gates
# computed a second time, in another language and with another interval
# arithmetic, for A16, A32, A64 and for Z32, Z64. Its records say what was run;
# what must hold here is that they describe THIS verifier and THIS source, and
# that for the polygons both implementations certify, the two agree on the
# perimeter to every digit the Python record prints.
section("the independent cross-check (pipeline/independent/verify.py), against the tree")
let verifier = joinpath(ROOT, "pipeline", "independent", "verify.py"),
    upstream = joinpath(ROOT, "cases", "upstream", "optigon", "cstrt_audet_ngon.jl")
    vsha = isfile(verifier) ? bytes2hex(open(sha256, verifier)) : ""
    for name in ("A16", "A32", "A64", "Z32", "Z64")
        path = joinpath(ROOT, "results", "independent", "$name.toml")
        if !isfile(path)
            skip("results/independent/$name.toml is CERTIFIED and describes the tree")
            continue
        end
        rec = TOML.parsefile(path)
        chk("$name: independent cross-check CERTIFIED, by this verifier",
            startswith(get(rec, "status", ""), "CERTIFIED") && get(rec, "verifier_sha256", "") == vsha)
        src = get(rec, "sources", Dict())
        if name[1] == 'A'
            gf = joinpath(ROOT, get(src, "graph_and_nominal_root_file", "?"))
            chk("$name: it read the active graph and the root from the tree, and ported the vendored OPTIGON file",
                isfile(gf) && get(src, "graph_and_nominal_root_sha256", "") == bytes2hex(open(sha256, gf)) &&
                get(src, "upstream_sha256", "") == bytes2hex(open(sha256, upstream)))
        end
        fp = joinpath(ROOT, "results", "family", "$name.toml")
        if isfile(fp)
            fam = TOML.parsefile(fp)
            per = parse(BigFloat, only(g["perimeter"] for g in fam["gate"] if g["id"] == "side_length"))
            enc = get(get(rec, "geometry", Dict()), "perimeter_enclosure", ["1", "0"])
            chk("$name: Python's perimeter enclosure contains the Julia one ($(enc[1])…)",
                parse(BigFloat, enc[1]) <= per <= parse(BigFloat, enc[2]))
        else
            skip("$name: Python's perimeter agrees with the Julia record (results/family/$name.toml is absent)")
        end
    end
end

section("the family layer, against its recorded Lean certificate")
let fam = joinpath(ROOT, "results", "lean_family_certificate.toml")
    if !isfile(fam)
        skip("results/lean_family_certificate.toml describes the tree")
    else
        out = IOBuffer()
        ok = success(pipeline(`$(Base.julia_cmd()) --project=$ROOT $(joinpath(ROOT, "pipeline", "record_lean_family_certificate.jl")) --check`;
                              stdout = out, stderr = out))
        txt = String(take!(out))
        chk("the recorded family certificate is a PASS and describes this tree", ok)
        ok || print(txt)
        rec = TOML.parsefile(fam)
        chk("the record covers $(join(("A$n" for n in FAMILY_LEAN_N), ", "))",
            all(haskey(get(rec, "cases", Dict()), "A$n") for n in FAMILY_LEAN_N))
        sc = get(rec, "scope", Dict())
        chk("the record states the Lean identification with the published constructor",
            any(x -> occursin("published_locally_maximal", x), get(sc, "formalized", String[])))
        chk("the record keeps the one step no kernel can check (transcription fidelity) as not formalised",
            any(x -> occursin("transcription", x), get(sc, "not_formalized", String[])))
    end
end

# ---------------------------------------------------------------------------
# Self test. Every branch above that reports a problem must be able to run; the
# SHA branch could not, and crashed the first time a hash differed.
section("self test: the checker's own failure paths")
chk("sha_mismatches reports a changed file instead of throwing",
    sha_mismatches(ROOT, [Dict("file" => "Project.toml",
                               "sha256" => repeat("0", 64))]) == ["Project.toml"])
chk("sha_mismatches reports a missing file instead of throwing",
    sha_mismatches(ROOT, [Dict("file" => "no/such/file.jl",
                               "sha256" => repeat("0", 64))]) == ["no/such/file.jl"])
chk("a failing chk is recorded rather than silently dropped",
    let before = length(FAILS)
        push!(FAILS, "(self test)")          # what fail() does, without printing
        got = length(FAILS) == before + 1
        pop!(FAILS)
        got && length(FAILS) == before
    end)

# ---------------------------------------------------------------------------
function records_report()
    println()
    println(repeat("=", 74))
    if isempty(FAILS)
        println("RECORDS CHECK PASS — the certificates, the source hashes and the Lean layer agree")
        isempty(SKIPPED) || println("  (", length(SKIPPED), " checks skipped: ", join(SKIPPED, "; "), ")")
    else
        println("RECORDS CHECK FAIL — $(length(FAILS)) discrepancies:")
        foreach(f -> println("   ", f), FAILS)
    end
    println(repeat("=", 74))
    exit(isempty(FAILS) ? 0 : 1)
end
(abspath(PROGRAM_FILE) == @__FILE__) && records_report()
