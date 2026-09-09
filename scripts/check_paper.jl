# Reconciles the article against the regenerated certificate and against the
# Lean sources. Run it after every edit to a16.tex, and before submitting.
#
#     julia --project=. scripts/check_paper.jl        # or: make paper-check
#
# WHY THIS EXISTS. Every number the article displays is produced by code in this
# repository, but the article itself is a working copy at the repository root
# and is not tracked (see .gitignore), so nothing tied the two together. Three
# defects got through that gap and were each found by hand: a side multiplier
# mistyped in a table, a cross reference that never resolved, and a bound stated
# in the wrong direction. Ad hoc checks written in a scratch directory do not
# survive the session that wrote them; this one does.
#
# It reads the COMPILED PDF, not the LaTeX source, because a typo in a table
# cell is invisible in the source until it is typeset, and because `\ref` only
# resolves at compile time. If `a16.pdf` is absent the checks that need it are
# skipped and reported as skipped, never as passed.

using TOML, Printf, SHA

const ROOT  = normpath(joinpath(@__DIR__, ".."))
const PDF   = joinpath(ROOT, "a16.pdf")
const TEX   = joinpath(ROOT, "a16.tex")
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

# ---------------------------------------------------------------------------
# `try` introduces a scope in Julia, so assigning inside it at top level would
# silently write a local and leave the global empty; every PDF check would then
# read "" and fail without saying why. Read through a function instead.
function _pdf_text(path)
    isfile(path) || return nothing
    try
        t = read(`pdftotext -layout $path -`, String)
        return isempty(strip(t)) ? nothing : t
    catch
        return nothing
    end
end
const PDFTEXT = _pdf_text(PDF)
const texsrc0 = isfile(TEX) ? read(TEX, String) : ""
const havepdf = PDFTEXT !== nothing
pdftext = havepdf ? PDFTEXT : ""
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
section("bounds the article states, against the certified values")
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
# Everything below is read out of the typeset PDF: a mistyped table cell is
# invisible in the source until it is set.
section("tables, read back out of the compiled PDF")
if !havepdf
    skip("Table 2 (active diameter multipliers) vs the certificate")
    skip("Table 3 (side multipliers) vs the certificate")
    skip("Table 1 (nominal coordinates) vs the certified enclosures")
    skip("no unresolved cross references in the PDF")
else
    lam = Dict((e["edge"][1], e["edge"][2]) =>
               (parse(BigFloat, e["lower"]) + parse(BigFloat, e["upper"])) / 2
               for e in gates["multipliers"]["lambda_enclosure"])
    function lambda_rows(lam, txt)
        seen = Dict{Tuple{Int,Int},BigFloat}()
        for m in eachmatch(r"\{(\d{1,2}),\s*(\d{1,2})\}\s+(0\.\d{8})", txt)
            key = (parse(Int, m.captures[1]), parse(Int, m.captures[2]))
            haskey(lam, key) && !haskey(seen, key) && (seen[key] = parse(BigFloat, m.captures[3]))
        end
        return seen
    end
    seen = lambda_rows(lam, pdftext)
    chk("Table 2: all 15 displayed lambda match the certificate",
        length(seen) == 15 && all(abs(lam[k] - v) <= big"5e-9" for (k, v) in seen))
    chk("every certified lambda has a strictly positive lower endpoint",
        all(parse(BigFloat, e["lower"]) > 0 for e in gates["multipliers"]["lambda_enclosure"]))

    alp = Dict(a["index"] => (parse(BigFloat, a["lower"]) + parse(BigFloat, a["upper"])) / 2
               for a in gates["multipliers"]["alpha_enclosure"])
    function alpha_rows(txt)
        d = Dict{Int,BigFloat}()
        for m in eachmatch(r"(?<![\d.])(\d{1,2})\s+(-[01]\.\d{8})", txt)
            i = parse(Int, m.captures[1]); v = parse(BigFloat, m.captures[2])
            (0 <= i <= 15 && -1.1 < v < -0.9 && !haskey(d, i)) && (d[i] = v)
        end
        return d
    end
    shown = alpha_rows(pdftext)
    chk("Table 3: all 16 displayed alpha match the certificate",
        length(shown) == 16 && all(abs(alp[i] - shown[i]) <= big"5e-9" for i in 0:15))
    chk("the 16 displayed alpha sum to -16 within display rounding",
        length(shown) == 16 && abs(sum(values(shown)) + 16) < big"1e-7")

    chk("no unresolved cross reference (??) anywhere in the PDF",
        !occursin("??", pdftext))
end

# ---------------------------------------------------------------------------
section("geometry the article prints, against the constructor")
include(joinpath(ROOT, "src", "A16Certificate.jl"))
using .A16Certificate
using IntervalArithmetic

Zr = interval(z_nominal - big"1e-30", z_nominal + big"1e-30")
Zc = interval(z_nominal - big"1e-28", z_nominal + big"1e-28")
p  = coordinates(Zr)

if havepdf
    function coord_rows(txt, p)
        rows = collect(eachmatch(
            r"(?m)^\s*(\d{1,2})\s+(-?[01]\.\d{10})\s+(-?[01]\.\d{10})\s*$", txt))
        bad = 0
        for m in rows
            i = parse(Int, m.captures[1])
            (0 <= i <= 15) || continue
            for (k, cap) in ((1, m.captures[2]), (2, m.captures[3]))
                want = parse(BigFloat, cap)
                # The table prints 10 decimals, far coarser than the enclosure
                # over Z_root, so the printed value cannot lie *inside* it.
                # What must hold is that it is the correct rounding of the
                # certified value.
                v = p[i+1, k]
                ok = (inf(v) <= want <= sup(v)) ||
                     (abs(BigFloat(mid(v)) - want) <= big"5e-11")
                ok || (bad += 1)
            end
        end
        return length(rows), bad
    end
    nrows, nbadc = coord_rows(pdftext, p)
    chk("Table 1: all $(2*nrows) printed coordinates lie in their enclosures",
        nrows == 16 && nbadc == 0)
else
    skip("Table 1 (nominal coordinates) vs the certified enclosures")
end

if isfile(TEX)
    function figure_vertices(tex, p)
        found = 0; bad = 0
        for i in 0:15
            m = match(Regex("\\\\coordinate \\(p$(i)\\) at \\((-?[0-9.]+),(-?[0-9.]+)\\);"), tex)
            m === nothing && continue
            found += 1
            fx = parse(Float64, m.captures[1]); fy = parse(Float64, m.captures[2])
            (fx == round(Float64(mid(p[i+1,1])), digits=5) &&
             fy == round(Float64(mid(p[i+1,2])), digits=5)) || (bad += 1)
        end
        return found, bad
    end
    nfound, nbadf = figure_vertices(read(TEX, String), p)
    chk("the figure's 16 TikZ vertices are the certified ones to 5 decimals",
        nfound == 16 && nbadf == 0)
else
    skip("figure coordinates vs the certified configuration")
end

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
    chk("the perimeter lies strictly between L(M16) and the upper bound L_16",
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
section("claims the article makes about the Lean layer")
src(f)  = isfile(joinpath(LEAN, f)) ? read(joinpath(LEAN, f), String) : ""
alll    = join([src(f) for f in readdir(LEAN) if endswith(f, ".lean")], "\n")
sidelen = src("SideLength.lean")
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
# Theorem 6.4 with it. Nothing above touched either, so until now the paper's
# headline was the one thing this reconciler did not reconcile.
chk("Theorem 3.5 itself, in the paper's own normalisation",
    occursin("theorem thm_3_5", alll) && occursin("theorem thm_3_5_le", alll))
chk("the blow-up: the tangent limits, the slice normalisation, and the assembly",
    occursin("eD_eq_zero_of_blowup", alll) && occursin("dD_nonpos_of_blowup", alll) &&
    occursin("tendsto_normCfg", alll) && occursin("no_blowup_sequence", alll))
chk("Theorem 6.4 as a Lean theorem, unconditionally",
    occursin("theorem A16_locally_maximal", alll) &&
    occursin("exists_A16_root_in_Ioo_pi", alll))
chk("the conclusion is congruence, not equality (modulo Euclidean motions)",
    occursin("def Congruent", alll) && occursin("Congruent y.1", alll))
chk("Proposition 4.2: the square closed by the same route",
    occursin("theorem square_strict_local_max", alll) &&
    occursin("theorem square_bridge", alll))

# ---------------------------------------------------------------------------
# The formal layer's table quotes three counts. They are recorded by
# `run_lean_certificate.jl`; reconcile the printed numbers against that record
# rather than against a memory of what they were.
section("the formal-layer table, against the recorded Lean certificate")
let lcpath = joinpath(ROOT, "results", "lean_certificate.toml")
    if !isfile(lcpath)
        skip("Table 6 counts vs results/lean_certificate.toml")
    else
        lc = TOML.parsefile(lcpath)
        th = get(lc, "theorems", Dict{String,Any}())
        naud = get(th, "axiom_audited_theorems", -1)
        nneg = get(th, "negative_controls_total", -1)
        nrej = get(th, "negative_controls_rejected", -1)
        chk("every negative control recorded was rejected", nneg == nrej && nneg > 0)
        if isempty(texsrc0)
            skip("Table 6: audited theorem count matches the record")
            skip("Table 6: negative control count matches the record")
        else
            chk("Table 6: audited theorem count matches the record ($naud)",
                occursin("Audited theorems & \\($naud\\)", texsrc0))
            chk("Table 6: negative control count matches the record ($nneg)",
                occursin("Negative controls & \\($nneg\\)", texsrc0))
        end
        # The article cites the package by version. Three files declare it and
        # they drifted apart once already (CITATION.cff said 1.0.0 while
        # Project.toml and the bibliography said 2.2.0; they are all 1.0.0 now).
        let proj = TOML.parsefile(joinpath(ROOT, "Project.toml"))
            v = get(proj, "version", "")
            cff = isfile(joinpath(ROOT, "CITATION.cff")) ?
                  read(joinpath(ROOT, "CITATION.cff"), String) : ""
            chk("CITATION.cff declares the same version as Project.toml ($v)",
                occursin("version: \"$v\"", cff))
            if isempty(texsrc0)
                skip("the article cites the package at the declared version")
            else
                chk("the article cites the package at version $v",
                    occursin("version $v", texsrc0))
            end
        end
        chk("the recorded Lean scope no longer calls Theorem 3.5 unformalised",
            !any(x -> occursin("Theorem 3.5", x), get(get(lc, "scope", Dict()), "not_formalized", String[])))
    end
end

# ---------------------------------------------------------------------------
# Every path the article tells a referee to run must exist. The article is not
# tracked, so a repository reorganisation cannot rewrite it, and the reader is
# the one who discovers the command is gone. This check closes that gap: the
# v1.0 restructuring left three dead commands in the supplementary table, and
# nothing here noticed.
section("every command the article prints actually exists")
let cmds = String[]
    texsrc = texsrc0
    for m in eachmatch(r"\\texttt\{([^}]*)\}", texsrc)
        t = replace(m.captures[1], "\\_" => "_", "-{}-" => "--")
        for tok in split(t)
            # Only paths into directories this repository ships. That excludes
            # URLs and references to upstream code (the OPTIGON constructor),
            # which are citations, not commands the reader is told to run.
            if any(d -> startswith(tok, d),
                   ("src/", "scripts/", "tools/", "test/", "docs/", "examples/",
                    "results/", "lean/", "./scripts/"))
                push!(cmds, tok)
            end
        end
    end
    unique!(cmds)
    missing_paths = String[]
    for c in cmds
        # `cd lean && ./scripts/verify.sh` is written relative to lean/
        cand = [joinpath(ROOT, c), joinpath(ROOT, "lean", lstrip(c, ['.', '/']))]
        any(isfile, cand) || push!(missing_paths, c)
    end
    if isempty(cmds)
        # No article, or an article that prints no path into this repository.
        # Either way nothing was verified, and reporting "ok" for a check that
        # examined zero paths is the same defect this section exists to catch.
        skip("every path printed in the article exists")
    elseif isempty(missing_paths)
        chk("all $(length(cmds)) paths printed in the article exist", true)
    else
        fail("paths printed in the article that do not exist", join(missing_paths, ", "))
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
println()
println(repeat("=", 74))
if isempty(FAILS)
    # The verdict must describe what was actually verified, not what this
    # script is named after. With the article absent, every check that reads it
    # is skipped, and announcing that "the article agrees with the certificate"
    # would be a pass claiming a verification that never ran — the exact failure
    # mode the rest of this package exists to prevent.
    if isempty(SKIPPED)
        println("PAPER CHECK PASS — the article agrees with the certificate and with Lean")
    else
        println("PARTIAL — the article was NOT checked: a16.tex/a16.pdf absent.")
        println()
        println("  Verified: the certificate, the source hashes, and the claims about Lean.")
        println("  NOT verified ($(length(SKIPPED)) checks skipped):")
        for sk in SKIPPED
            println("     ", sk)
        end
        println()
        println("  Nothing here says the article is consistent with the certificate.")
        println("  Run `make paper` first, with a16.tex present, for that.")
    end
else
    println("PAPER CHECK FAIL — $(length(FAILS)) discrepancies:")
    for f in FAILS
        println("   ", f)
    end
end
println(repeat("=", 74))
exit(isempty(FAILS) ? 0 : 1)
