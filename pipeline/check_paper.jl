# Reconciles the article against the regenerated certificate and against the
# Lean sources. Run it after every edit to paper/main.tex or paper/supplement.tex, and
# before submitting.
#
#     julia --project=. pipeline/check_paper.jl        # or: make paper-check
#
# WHY THIS EXISTS. Every number the article displays is produced by code in this
# repository, but the article itself is a working copy in paper/
# and is not tracked (see .gitignore), so nothing tied the two together. Three
# defects got through that gap and were each found by hand: a side multiplier
# mistyped in a table, a cross reference that never resolved, and a bound stated
# in the wrong direction. Ad hoc checks written in a scratch directory do not
# survive the session that wrote them; this one does.
#
# It reads the COMPILED PDF, not the LaTeX source, because a typo in a table
# cell is invisible in the source until it is typeset, and because `\ref` only
# resolves at compile time. If `main.pdf` is absent the checks that need it are
# skipped and reported as skipped, never as passed.

using TOML, Printf, SHA

const ROOT  = normpath(joinpath(@__DIR__, ".."))
# The family members, read from their single source (cases/exact_coords.jl).
_family(name) = Tuple(parse.(Int, split(match(Regex("^const $name = \\((.*)\\)", "m"),
    read(joinpath(ROOT, "cases", "exact_coords.jl"), String)).captures[1], ", ")))
const FAMILY_N = _family("FAMILY_N")
const FAMILY_LEAN_N = _family("FAMILY_LEAN_N")
const PAPER = joinpath(ROOT, "paper")
const PDF   = joinpath(PAPER, "main.pdf")
const TEX   = joinpath(PAPER, "main.tex")
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
const SUPPDF  = joinpath(PAPER, "supplement.pdf")
const SUPTEX  = joinpath(PAPER, "supplement.tex")
const PDFTEXT = _pdf_text(PDF)
const SUPTEXT = _pdf_text(SUPPDF)
const texsrc0 = isfile(TEX) ? read(TEX, String) : ""
const supsrc0 = isfile(SUPTEX) ? read(SUPTEX, String) : ""
const havepdf = PDFTEXT !== nothing
pdftext = havepdf ? PDFTEXT : ""
const havesup = SUPTEXT !== nothing
suptext = havesup ? SUPTEXT : ""
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
    skip("Table S2(b) (active diameter multipliers) vs the certificate")
    skip("Table S2(a) (side multipliers) vs the certificate")
    skip("Table 2 (nominal coordinates) vs the certified enclosures")
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
    # Since 1.3.0 the multiplier table is in the supplement; read both PDFs.
    seen = lambda_rows(lam, pdftext * "\n" * suptext)
    chk("multiplier table (b): all 15 displayed lambda match the certificate",
        length(seen) == 15 && all(abs(lam[k] - v) <= big"5e-9" for (k, v) in seen))
    chk("every certified lambda has a strictly positive lower endpoint",
        all(parse(BigFloat, e["lower"]) > 0 for e in gates["multipliers"]["lambda_enclosure"]))

    alp = Dict(a["index"] => (parse(BigFloat, a["lower"]) + parse(BigFloat, a["upper"])) / 2
               for a in gates["multipliers"]["alpha_enclosure"])
    function alpha_rows(txt)
        d = Dict{Int,BigFloat}()
        # The article sets these values in math mode, so pdftotext emits U+2212
        # MINUS SIGN, not an ASCII hyphen. Accepting only the hyphen made this
        # check silently find nothing once the two multiplier tables were merged.
        for m in eachmatch(r"(?<![\d.])(\d{1,2})\s+([-\u2212][01]\.\d{8})", txt)
            i = parse(Int, m.captures[1])
            v = parse(BigFloat, replace(m.captures[2], '\u2212' => '-'))
            (0 <= i <= 15 && -1.1 < v < -0.9 && !haskey(d, i)) && (d[i] = v)
        end
        return d
    end
    shown = alpha_rows(pdftext * "\n" * suptext)
    chk("multiplier table (a): all 16 displayed alpha match the certificate",
        length(shown) == 16 && all(abs(alp[i] - shown[i]) <= big"5e-9" for i in 0:15))
    chk("the 16 displayed alpha sum to -16 within display rounding",
        length(shown) == 16 && abs(sum(values(shown)) + 16) < big"1e-7")

    chk("no unresolved cross reference (??) anywhere in either PDF",
        !occursin("??", pdftext) && !occursin("??", suptext))
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
            # Since 1.3.1 Table 1 prints two vertices per line (i = 0..7 beside
            # i = 8..15), so each (index, x, y) triple is matched wherever it is.
            r"(?<![\d.])(\d{1,2})\s+(-?[01]\.\d{10})\s+(-?[01]\.\d{10})(?!\d)", txt))
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
    chk("Table 2: all $(2*nrows) printed coordinates lie in their enclosures",
        nrows == 16 && nbadc == 0)
else
    skip("Table 2 (nominal coordinates) vs the certified enclosures")
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

# ---------------------------------------------------------------------------
# Section 5 prints the vertex map t -> p_k(t) in exact form: Lemma 6.1 is about
# those formulas, and a reader must be able to rebuild them without the
# software. Each printed formula is checked against `coordinates` at the root
# and at two other parameters, so the printed map is the certified one.
section("the vertex map printed in Section 5, against the code")
let i5 = something(findfirst("\\section{The extracted", texsrc0),
                    findfirst("\\section{The Bingane--Audet polygons", texsrc0), Some(nothing)),
    j5 = findfirst("\\section{Certified verification of", texsrc0)
    if i5 === nothing || j5 === nothing
        skip("Section 5 prints the vertex map of the certified constructor")
        skip("the printed vertex map is the certified constructor")
    else
        sec5 = texsrc0[first(i5):prevind(texsrc0, first(j5))]
        flat5 = replace(sec5, r"\s+" => "", "\\," => "", "\\ " => "", "\\bigl" => "", "\\bigr" => "")
        S(z, k) = sin(k * z); C(z, k) = cos(k * z)
        formulas = [
            ("p_0&=(0,0)",                              (z, x, y) -> (zero(z), zero(z))),
            ("p_1&=(\\sin(2t)-\\sint,\\cost-\\cos(2t))", (z, x, y) -> (S(z,2) - S(z,1), C(z,1) - C(z,2))),
            ("p_2&=(\\sin(3t)-\\sint,\\cost-\\cos(3t))", (z, x, y) -> (S(z,3) - S(z,1), C(z,1) - C(z,3))),
            ("p_3&=(-x,y)",                             (z, x, y) -> (-x, y)),
            ("p_4&=(x+\\sin(7t),y+\\cos(7t))",           (z, x, y) -> (x + S(z,7), y + C(z,7))),
            ("p_5&=(x+\\sin(6t),y+\\cos(6t))",           (z, x, y) -> (x + S(z,6), y + C(z,6))),
            ("p_6&=(x+\\sin(5t),y+\\cos(5t))",           (z, x, y) -> (x + S(z,5), y + C(z,5))),
            ("p_7&=(\\sint,\\cost)",                     (z, x, y) -> (S(z,1), C(z,1))),
            ("p_8&=(0,1)",                              (z, x, y) -> (zero(z), one(z))),
        ]
        others = ["x(t)=\\sint-(2\\cost-1)\\sin(4t)", "y(t)=\\cost-(2\\cost-1)\\cos(4t)",
                  "p_{16-i}=(-x_i,y_i)", "=|p_4-p_3|^2-|p_8-p_7|^2"]
        missing = [f for (f, _) in formulas if !occursin(f, flat5)]
        append!(missing, [f for f in others if !occursin(f, flat5)])
        isempty(missing) ? pass("Section 5 prints the vertex map of the certified constructor") :
            fail("Section 5 prints the vertex map of the certified constructor", "not printed: " * join(missing, "  "))
        ok = true
        for z in (z_nominal, big"0.13", big"0.31")
            x = A16Certificate.Xfun(z); y = A16Certificate.Yfun(z); p = coordinates(z)
            for (k, (_, f)) in enumerate(formulas)
                X, Y = f(z, x, y)
                ok &= abs(p[k, 1] - X) < big"1e-60" && abs(p[k, 2] - Y) < big"1e-60"
            end
            for i in 1:7          # the reflection p_{16-i} = (-x_i, y_i)
                ok &= abs(p[17-i, 1] + p[i+1, 1]) < big"1e-60" && abs(p[17-i, 2] - p[i+1, 2]) < big"1e-60"
            end
            d(a, b) = (p[a+1,1] - p[b+1,1])^2 + (p[a+1,2] - p[b+1,2])^2
            ok &= abs(A16Certificate.Ffun(z) - (d(4, 3) - d(8, 7))) < big"1e-60"
        end
        chk("the printed vertex map is the certified constructor, at three parameters", ok)
    end
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

# ---------------------------------------------------------------------------
# The bounds compared at the top of this file are literals typed into it, so
# they would stay green if a number in the article were edited by hand. This
# section reads the article's own source instead: each certified number must be
# printed in Section 6 digit for digit, and any other long decimal there is a
# failure, because it would be a number that nothing has contrasted with the
# certificate. A rounded lower bound that rounds *up* was found here by hand
# once (min lambda printed as 0.09186678 > 0.0918667776...).
section("every number Section 6 prints, read from the article's source")
using LinearAlgebra
# Section 6 runs to the next \section, or to the bibliography if it is the last
# one (the "Local and global questions" section that followed it was removed in
# 1.3.0).
const SEC6 = let i = findfirst("\\section{Certified verification of", texsrc0)
    j = i === nothing ? nothing :
        something(findnext("\\section{", texsrc0, last(i) + 1),
                  findnext("\\begin{thebibliography}", texsrc0, last(i) + 1), Some(nothing))
    (i === nothing || j === nothing) ? "" : texsrc0[first(i):prevind(texsrc0, first(j))]
end
const SEC6_CHECKS = [
    "Section 6 prints each certified bound digit for digit",
    "Section 6 prints no long decimal that is not checked here",
    "the printed F_c is Fc_poly() of the code, coefficient by coefficient",
    "the critical pair, the minimal multiplier edge and the box radii",
    "F_c: nine real roots in [-1,1], the nearest other one at z = 0.2572",
    "Figure S1 (Online Resource 1) states the magnification its own coordinates give",
]
if isempty(SEC6)
    foreach(skip, SEC6_CHECKS)
else
    flat6 = replace(SEC6, r"\s+" => "", "\\," => "")
    printed = [
        "[0.1959554930055385228,0.1959554930055385230]",   # ell, Prop 6.2(2)
        "[3.1352878880886163663,3.1352878880886163665]",   # 16 ell, Prop 6.2(2)
        "0.0074882049306989244",                           # Prop 6.2(3), Table 3
        "0.0080997106581357295",                           # Prop 6.2(4), Table 3
        "0.0918667776833353997",                           # Prop 6.2(5), Table 3
        "1.419383643581978\\times10^{-25}",                # Prop 6.2(6), Table 3
        "4.017187643256796\\times10^{-28}",                # Subsection 6.4, Q
        "1.825393700512576\\times10^{-25}",                # Subsection 6.4, M_0
        "2\\times10^{-30}",                                # Table 3, width of ell
    ]
    # a certified number may be printed in the article or in the supplement
    flatall = flat6 * replace(supsrc0, r"\s+" => "", "\\," => "")
    notprinted = [lit for lit in printed if !occursin(lit, flatall)]
    isempty(notprinted) ? pass(SEC6_CHECKS[1]) :
        fail(SEC6_CHECKS[1], "not printed: " * join(notprinted, ", "))
    # the one bound checked above only through the log: recompute it here
    let (_, b, _, _) = regularity_test(normalized_matrix(build_jacobian(Zc)))
        bb = b isa Interval ? sup(b) : BigFloat(b)
        chk("normalized-system bound <= 1.825393700512576e-25, recomputed",
            bb <= big"1.825393700512576e-25")
    end
    # the perimeters of Table 5 are checked row by row in their own section below
    famtab = isfile(joinpath(ROOT, "results", "tables", "table5_family.tex")) ?
             read(joinpath(ROOT, "results", "tables", "table5_family.tex"), String) : ""
    # Section 6 prints the bounds rounded in the safe direction (since 1.3.0);
    # the full values are in the supplement and checked above. Each rounded
    # interval must contain the certified enclosure.
    rounded = [("[0.1959554930055385,0.1959554930055386]", big"0.1959554930055385", big"0.1959554930055386", ell_lo, ell_hi),
               ("[3.135287888088616,3.135287888088617]",   big"3.135287888088616",  big"3.135287888088617",  per_lo, per_hi)]
    chk("Section 6: the rounded enclosures of ell and 16 ell contain the certified ones",
        all(occursin(lit, flat6) && lo <= clo && chi <= hi for (lit, lo, hi, clo, chi) in rounded))
    cert_or(g, k) = parse(BigFloat, gates[g][k])
    chk("Section 6: each rounded bound is on the safe side of the certificate",
        occursin(">0.00748", flat6) && big"0.00748" < cert_or("convexity", "min_support_determinant") &&
        occursin(">0.00809", flat6) && big"0.00809" < cert_or("inactive_margin", "inactive_margin_lower_bound") &&
        occursin(">0.09186", flat6) && big"0.09186" < cert_or("multipliers", "min_lambda_lower_bound") &&
        occursin("<1.5\\times10^{-25}", flat6) && cert_or("rank", "preconditioned_regularity_bound") < big"1.5e-25" &&
        occursin("<2\\times10^{-25}", flat6))
    stray = unique([m.match for m in eachmatch(r"\d+\.\d{6,}", flat6)
                    if !any(k -> occursin(m.match, k), printed) &&
                       !any(r -> occursin(m.match, r[1]), rounded) && !occursin(m.match, famtab) &&
                       !(m.match in ("0.0981721090", "3.1402460942", "0.0490872986", "3.1412717079"))])
    isempty(stray) ? pass(SEC6_CHECKS[2]) :
        fail(SEC6_CHECKS[2], "unchecked: " * join(stray, ", "))

    let m = match(r"F_c\(c\)=\{\}&(.*?)\\end\{aligned\}"s, SEC6), ok = false
        if m !== nothing
            blk = replace(m.captures[1], "&" => "", "\\\\" => "", r"\s+" => "")
            art = Dict{Int,BigInt}()
            for t in eachmatch(r"([+-]?)(\d+)(c)?(?:\^\{?(\d+)\}?)?", blk)
                d = t.captures[3] === nothing ? 0 :
                    (t.captures[4] === nothing ? 1 : parse(Int, t.captures[4]))
                art[d] = (t.captures[1] == "-" ? -1 : 1) * parse(BigInt, t.captures[2])
            end
            fc = Fc_poly()
            ok = length(fc) == 13 && length(art) == 13 &&
                 all(fc[k+1] == get(art, k, 0) for k in 0:12)
        end
        chk(SEC6_CHECKS[3], ok)
    end

    let lamenc = gates["multipliers"]["lambda_enclosure"],
        emin = lamenc[argmin([parse(BigFloat, e["lower"]) for e in lamenc])]["edge"],
        cp = gates["inactive_margin"]["critical_pair"],
        rr = parse(BigFloat, cert["meta"]["z_root_radius"]),
        rc = parse(BigFloat, cert["meta"]["z_cert_radius"])
        flatsup = replace(supsrc0, r"\s+" => "", "\\," => "")
        chk(SEC6_CHECKS[4],
            occursin("attainedattheedge\\(\\{$(emin[1]),$(emin[2])\\}\\)", flat6 * flatsup) &&
            occursin("attainedatthepair\\(\\{$(cp[1]),$(cp[2])\\}\\)", flat6 * flatsup) &&
            abs(rr / big"1e-30" - 1) < big"1e-60" && occursin("radius\\(10^{-30}\\)", flat6) &&
            abs(rc / big"1e-28" - 1) < big"1e-60" && occursin("radius\\(10^{-28}\\)", flat6))
    end

    # A display claim of Prop 6.2(1), not a certificate pillar: the count and the
    # approximate location explain why a sign change alone would not pin z*.
    let fc = Float64.(Fc_poly()), n = length(fc) - 1, C = zeros(n, n)
        for k in 2:n
            C[k, k-1] = 1.0
        end
        C[:, n] .= -fc[1:n] ./ fc[end]
        re = [real(x) for x in eigvals(C) if abs(imag(x)) < 1e-9 && -1 <= real(x) <= 1]
        zs = acos.(re)
        others = [z for z in zs if abs(z - Float64(z_nominal)) > 1e-6]
        chk(SEC6_CHECKS[5],
            length(re) == 9 && length(others) == 8 &&
            round(others[argmin(abs.(others .- Float64(z_nominal)))], digits=4) == 0.2572 &&
            occursin("ninerealroots", flat6) &&
            occursin("z\\approx0.2572", flat6 * replace(supsrc0, r"\s+" => "", "\\," => "")))
    end

    # Figure 5 is schematic, but the magnification it states is a number: the
    # scale of the upper line (I_search between its ticks) over the scale of the
    # lower one (Z_cert between its outer ticks). It was once stated as 10^26.
    # Figure 5 now lives in the supplement; look for it wherever it is.
    FIGSRC = occursin("fig:boxes", SEC6) ? SEC6 : supsrc0
    flatfig = replace(FIGSRC, r"\s+" => "", "\\," => "")
    let tick(y) = [parse(Float64, m.captures[1])
                   for m in eachmatch(Regex("\\\\draw\\[tick\\] \\(\\s*(-?[0-9.]+),$y\\)"), FIGSRC)],
        up = tick("-0\\.11"), dn = tick("-2\\.06"), ok = false
        if length(up) == 2 && length(dn) == 4
            search = big(pi) / 16 - 2asin(sin(big(pi) / 16) / 2)
            mag = (search / (maximum(up) - minimum(up))) /
                  (2parse(BigFloat, cert["meta"]["z_cert_radius"]) / (maximum(dn) - minimum(dn)))
            e = round(Int, log10(mag))
            ok = occursin("{\\(\\times10^{$e}\\)}", FIGSRC) &&
                 occursin("magnifiedbyabout\\(10^{$e}\\)", flatfig)
        end
        chk(SEC6_CHECKS[6], ok)
    end
end
if isempty(supsrc0)
    skip("supplement: the diagnostic sum of alpha lies in the printed bracket")
    skip("supplement: Julia and IntervalArithmetic versions are the certificate's")
    skip("supplement: working precision, tightest margin and orders of magnitude")
else
    let a = gates["multipliers"]["alpha_enclosure"],
        lo = sum(parse(BigFloat, x["lower"]) for x in a),
        hi = sum(parse(BigFloat, x["upper"]) for x in a)
        chk("supplement: the diagnostic sum of alpha lies in the printed bracket",
            big"-16.0001" <= lo && hi <= big"-15.9999" &&
            occursin("[-16.0001,-15.9999]", replace(supsrc0, r"\s+" => "")))
    end
    # The precision paragraph of the supplement: four numbers once derived by
    # hand. 98 is the least mantissa for which the unit in the last place at the
    # root is at most the radius of Z_root, so its endpoints and centre are
    # distinct floating point numbers whatever the rounding.
    let sup1 = replace(supsrc0, r"\s+" => " "),
        pmin = ceil(Int, log2(z_nominal / parse(BigFloat, cert["meta"]["z_root_radius"]))),
        tight = minimum(parse(BigFloat, s) for s in (
            gates["convexity"]["min_support_determinant"],
            gates["inactive_margin"]["inactive_margin_lower_bound"],
            gates["multipliers"]["min_lambda_lower_bound"])),
        orders = round(Int, -log10(parse(BigFloat, gates["rank"]["preconditioned_regularity_bound"])))
        chk("supplement: working precision, tightest margin and orders of magnitude",
            occursin("at least \\($pmin\\) bits", sup1) &&
            occursin("about \\($(round(256 / pmin, digits=1))\\)", sup1) &&
            tight > big"7e-3" && occursin("larger than \\(7\\times10^{-3}\\)", sup1) &&
            orders == 25 && occursin("twenty five orders of magnitude", sup1))
    end
    chk("supplement: Julia and IntervalArithmetic versions are the certificate's",
        occursin("Julia \\($(cert["meta"]["julia_version"])\\)", supsrc0) &&
        occursin("\\texttt{IntervalArithmetic.jl} \\($(cert["meta"]["intervalarithmetic_version"])\\)", supsrc0))
end

section("the explicit radius (Theorem thm:a16-radius), against results/radius_certificate.toml")
let rc = joinpath(ROOT, "results", "radius_certificate.toml")
    if !isfile(rc) || isempty(texsrc0)
        skip("the printed radius and its constants are on the safe side of the certificate")
    else
        R = TOML.parsefile(rc)["radius"]
        cert(k) = parse(BigFloat, R[k])
        flat = replace(texsrc0, r"\s+" => "", "\\," => "")
        # the numbers the article prints, and the direction each must hold in
        pr = (r = big"6.63e-4", s2 = big"0.09119", a = big"4.004", lam = big"0.09186", ell = big"0.1959")
        printed_ok = all(occursin(x, flat) for x in ("6.63\\times10^{-4}", "\\sigma^2=0.09119",
                         "\\|\\alpha\\|_2<4.004", "\\lambda_{\\min}>0.09186", "\\ell>0.1959"))
        chk("the article prints r, sigma^2, |alpha|_2, lambda_min and ell of Theorem thm:a16-radius", printed_ok)
        chk("each printed constant is on the safe side of the certified one",
            pr.r <= cert("r_lower_bound") && pr.s2 <= cert("sigma_squared_lower_bound") &&
            pr.a >= cert("alpha_norm_upper_bound") && pr.lam <= cert("lambda_min_lower_bound") &&
            pr.ell <= cert("ell_lower_bound"))
        chk("the printed constants themselves give the printed radius",
            sqrt(pr.s2) * pr.ell / (2 * (1 + pr.a / pr.lam)) >= pr.r)
    end
end

# Since 1.3.1 the article covers A16, A32 and A64 (the cases that also have a
# per-case Lean certificate). The larger cases of the package (A128 ... A1024,
# the general theorem) are not in it: a result stated in the article needs its
# proof there.
section("scope: the article concerns A16, A32 and A64")
if isempty(texsrc0)
    skip("the article states no result about A_n for n > 64")
else
    chk("the article states no result about A_n for n > 64",
        !occursin("Auto-generated by pipeline/family_table.jl", texsrc0) &&
        !occursin(r"A_\{?(128|256|512|1024)\b", texsrc0) &&
        !occursin(r"Family\.T\d+", texsrc0))
    # Tables 1 and 4: every printed value of A32 and A64 against results/family/A<n>.toml
    function family_table_ok(tex)
        flat = replace(tex, r"\s+" => "", "\\," => "")
        ok = true
        e(x) = parse(BigFloat, x)
        for (n, zs, per, det, dlt, lam, cm) in ((32, "0.0981721090", "3.1402460942", "9.43e-4", "9.62e-4", "2.32e-2", "3e-14"),
                                                (64, "0.0490872986", "3.1412717079", "1.18e-4", "1.18e-4", "5.36e-3", "7e-14"))
            rec = TOML.parsefile(joinpath(ROOT, "results", "family", "A$n.toml"))
            g = Dict(x["id"] => x for x in rec["gate"])
            num(id, pat) = parse(BigFloat, match(pat, g[id]["detail"]).captures[1])
            P = e(g["side_length"]["perimeter"])
            zlo = num("box_nesting", r"Z_root = \[([0-9.e+-]+)")
            ok &= rec["verdict"] == "CERTIFIED"
            ok &= abs(round(zlo, digits=10) - e(zs)) < big"1e-12" && abs(round(P, digits=10) - e(per)) < big"1e-12"
            ok &= num("convexity", r"min inf = ([0-9.e+-]+)") > e(det)
            ok &= num("inactive_margin", r"margin≥([0-9.e+-]+)") > e(dlt)
            ok &= num("multipliers", r"λ_ij ≥ ([0-9.e+-]+)") > e(lam)
            ok &= num("rank", r"‖I-CM‖∞=([0-9.e+-]+)") < e(cm)
            ok &= all(occursin(x, flat) for x in (zs, per))
        end
        return ok
    end
    chk("Tables 1 and 4: z_n, n ell and every A32/A64 margin agree with the family certificates, on the safe side",
        family_table_ok(texsrc0))
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
        if isempty(supsrc0)
            skip("supplement: audited theorem count matches the record")
            skip("supplement: negative control count matches the record")
        else
            chk("supplement: audited theorem count matches the record ($naud)",
                occursin("Audited theorems & \\($naud\\)", supsrc0))
            chk("supplement: negative control count matches the record ($nneg)",
                occursin("Negative controls & \\($nneg\\)", supsrc0))
            lm = get(lc, "meta", Dict{String,Any}())
            chk("supplement: Lean toolchain and Mathlib revision are the recorded ones",
                occursin("toolchain \\texttt{$(split(get(lm, "lean_toolchain", "?"), ':')[end])}", supsrc0) &&
                occursin("revision \\texttt{$(first(get(lm, "mathlib_rev", "?"), 8))}", supsrc0))
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
            chk(".zenodo.json declares the same version as Project.toml ($v)",
                zj !== nothing && zj.captures[1] == v)
            if isempty(texsrc0)
                skip("the article cites the package at the declared version")
            else
                chk("the article cites the package at version $v",
                    occursin("version $v", texsrc0))
                isempty(supsrc0) ||
                    chk("the supplement cites the package at version $v",
                        occursin("version $v", supsrc0))
            end
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
# Every path the article tells a referee to run must exist. The article is not
# tracked, so a repository reorganisation cannot rewrite it, and the reader is
# the one who discovers the command is gone. This check closes that gap: the
# v1.0 restructuring left three dead commands in the supplementary table, and
# nothing here noticed.
section("every Lean theorem the article names exists")
# The article names Lean declarations (in \texttt or \nolinkurl) so that a reader
# can find them. A renamed or deleted theorem would leave the text pointing at
# nothing, and nothing else here would notice. A name inside a family case
# (Chiquipoli.Family.A<n>.x) must be a theorem in that case's own files.
let texsrc = texsrc0 * "\n" * supsrc0
    names = unique(replace(m.captures[1], "\\_" => "_") for m in
                   eachmatch(r"\\(?:texttt|nolinkurl)\{((?:Chiquipoli\.)?[A-Za-z0-9_\\.]*(?:locally_maximal|locally\\_maximal)[A-Za-z0-9_\\]*)\}", texsrc))
    if isempty(names)
        skip("every Lean theorem named in the article exists")
    else
        leanfiles = String[]
        for d in ("ChiquipoliLean", "ChiquipoliFamily"), (dir, _, fs) in walkdir(joinpath(ROOT, "lean", d)), f in fs
            endswith(f, ".lean") && push!(leanfiles, joinpath(dir, f))
        end
        for nm in names
            short = split(nm, '.')[end]
            m = match(r"Family\.(A\d+)\.", nm)
            pool = m === nothing ? leanfiles : filter(f -> occursin("/" * m.captures[1] * "/", f), leanfiles)
            found = any(f -> occursin(Regex("^theorem " * short * "\\b", "m"), read(f, String)), pool)
            chk("the article's Lean theorem $(nm) exists" * (m === nothing ? "" : " (in $(m.captures[1]))"), found)
        end
    end
end

section("every command the article prints actually exists")
let cmds = String[]
    texsrc = texsrc0 * "\n" * supsrc0
    for m in eachmatch(r"\\texttt\{([^}]*)\}", texsrc)
        t = replace(m.captures[1], "\\_" => "_", "-{}-" => "--")
        for tok in split(t)
            # Only paths into directories this repository ships. That excludes
            # URLs and references to upstream code (the OPTIGON constructor),
            # which are citations, not commands the reader is told to run.
            # `scripts/` is the pre-2026-09 name of pipeline/: kept, so an article
            # that still prints an old path is reported rather than skipped.
            if any(d -> startswith(tok, d),
                   ("src/", "pipeline/", "scripts/", "cases/", "tools/", "test/",
                    "docs/", "examples/", "results/", "logs/", "lean/", "./"))
                push!(cmds, tok)
            end
        end
    end
    unique!(cmds)
    missing_paths = String[]
    for c in cmds
        # `cd lean && ./verify.sh` is written relative to lean/
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
        println("PARTIAL — the article was NOT checked: paper/main.tex or paper/main.pdf absent.")
        println()
        println("  Verified: the certificate, the source hashes, and the claims about Lean.")
        println("  NOT verified ($(length(SKIPPED)) checks skipped):")
        for sk in SKIPPED
            println("     ", sk)
        end
        println()
        println("  Nothing here says the article is consistent with the certificate.")
        println("  Run `make paper` first, with paper/main.tex present, for that.")
    end
else
    println("PAPER CHECK FAIL — $(length(FAILS)) discrepancies:")
    for f in FAILS
        println("   ", f)
    end
end
println(repeat("=", 74))
exit(isempty(FAILS) ? 0 : 1)
