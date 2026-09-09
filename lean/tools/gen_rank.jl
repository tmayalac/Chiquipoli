# Generate lean/ChiquipoliLean/Rank.jl -> Rank.lean
#
#     julia --project=. lean/tools/gen_rank.jl
#
# **I_eq = R_eq (Prop 6.2(6)), verified by the Lean kernel.**
#
# The gate is not "rank = 30" as a number; it is that the only tangent vectors
# annihilated by every active constraint differential are the rigid
# infinitesimal motions. Stating it that way lets Lean avoid `Matrix.det` and
# the rank API entirely: dense linear algebra becomes a sparse chain of
# `linear_combination` steps.
#
#   ⊇  every rigid motion is in the kernel — a pure `ring` identity;
#   ⊆  the elimination certificate below.
#
# For ⊆ we subtract the rigid part first: given `w` in the kernel, set
# `δ = w − rigid(a,b,c)` with `a,b,c` chosen to kill the three free
# coordinates. Then `δ` is still in the kernel, and the triangular reduced
# system forces `δ = 0` one pivot at a time — much cleaner than a general
# back-substitution, because every right-hand side is already known to vanish.

include(joinpath(@__DIR__, "..", "..", "scripts", "_bootstrap.jl"))
include(joinpath(@__DIR__, "rank.jl"))
include(joinpath(@__DIR__, "bernstein.jl"))
using .RankCert, .Bernstein

const RC = RankCert
const AC = A16Certificate
const QQ = Rational{BigInt}
const OUT = joinpath(@__DIR__, "..", "ChiquipoliLean", "Rank.lean")
const A = QQ(613, 625)
const B0 = QQ(980801, 1000000)
const MPIV = QQ(1, 100)      # worst |pivot| clears 0.0575

lean_rat(q::QQ) = denominator(q) == 1 ?
    (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
    (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" :
                        "($(numerator(q))/$(denominator(q)))")

function horner(p, var)
    p = RC.ptrim(p)
    RC.iszp(p) && return "0"
    n = length(p) - 1
    n == 0 && return lean_rat(p[1])
    e = lean_rat(p[n+1])
    for k in (n-1):-1:0
        e = p[k+1] == 0 ? "($e) * $var" : "($e) * $var + $(lean_rat(p[k+1]))"
    end
    return e
end
hc(p) = horner(p, "Real.cos z")
hcv(p) = horner(p, "c")

function buildB(XC, YC, active)
    nC = 16 + length(active); B = [QQ[QQ(0)] for _ in 1:nC, _ in 1:33]
    add!(k, v, p) = (B[k, v] = RC.padd(B[k, v], p))
    for i in 0:15
        j = mod(i + 1, 16); k = i + 1
        dX = RC.psub(XC[j+1], XC[i+1]); dY = RC.psub(YC[j+1], YC[i+1])
        add!(k, 2i+1, RC.pmul(QQ[QQ(-1)], dX)); add!(k, 2i+2, RC.pmul(QQ[QQ(-1)], dY))
        add!(k, 2j+1, dX); add!(k, 2j+2, dY); add!(k, 33, QQ[QQ(-1)])
    end
    for (m, (i, j)) in enumerate(active)
        k = 16 + m
        dX = RC.psub(XC[j+1], XC[i+1]); dY = RC.psub(YC[j+1], YC[i+1])
        add!(k, 2i+1, RC.pmul(QQ[QQ(-1)], dX)); add!(k, 2i+2, RC.pmul(QQ[QQ(-1)], dY))
        add!(k, 2j+1, dX); add!(k, 2j+2, dY)
    end
    B
end

Fc = QQ.(AC.Fc_poly())
XC = [QQ.(p) for p in AC._XC]; YC = [QQ.(p) for p in AC._YC]
B  = buildB(XC, YC, AC.ACTIVE_EDGES)
free = [1, 2, 4]; rows = collect(1:30); kept = [v for v in 1:33 if !(v in free)]
cert = RC.elimination_certificate(B, Fc; rows = rows, kept = kept, free = free)
cols = cert.cols
println("elimination steps: ", length(cert.steps))

"Linear form Σ_j R[r,j] · V_{cols[j]-1}, emitting only nonzero entries."
function rowform(R, r)
    ts = String[]
    for j in 1:33
        RC.iszp(R[r, j]) && continue
        push!(ts, "($(hc(R[r,j]))) * V$(cols[j]-1)")
    end
    isempty(ts) ? "0" : join(ts, " +\n      ")
end

# --- replay the elimination, emitting a `have` per step ---------------------
R = [copy(B[rows[i], cols[j]]) for i in 1:30, j in 1:33]
ver = zeros(Int, 30)
ename(r, v) = "E$(r)_$(v)"
haves = String[]
for st in cert.steps
    corrterms = String[]
    for j in 1:33
        RC.iszp(st.corr[j]) && continue
        push!(corrterms, "($(hc(st.corr[j]))) * V$(cols[j]-1)")
    end
    corr = isempty(corrterms) ? "0" : "(" * join(corrterms, " + ") * ")"
    for j in 1:33
        R[st.row, j] = RC.psub(RC.psub(R[st.row, j], RC.pmul(st.f, R[st.piv, j])),
                               RC.pmul(st.corr[j], Fc))
    end
    old = ename(st.row, ver[st.row]); pv = ename(st.piv, ver[st.piv])
    ver[st.row] += 1
    push!(haves, "  have $(ename(st.row, ver[st.row])) :\n      " *
                 rowform(R, st.row) * " = 0 := by\n" *
                 "    linear_combination $old - ($(hc(st.f))) * $pv - $corr * hFc")
end
@assert all(RC.iszp(RC.psub(R[i,j], cert.R[i,j])) for i in 1:30, j in 1:33)

# --- pivot non-vanishing ----------------------------------------------------
pivlem = String[]; pivne = String[]
for k in 1:30
    r = cert.pivrow[k]; p = cert.R[r, k]
    γ = Bernstein.bern_coeffs(p, A, B0)
    neg = maximum(γ) < 0
    q = neg ? RC.pmul(QQ[QQ(-1)], p) : p
    γ2 = Bernstein.bern_coeffs(q, A, B0)
    @assert minimum(γ2) > MPIV "pivot $k margin $(Float64(minimum(γ2)))"
    push!(pivlem, Bernstein.lean_lower_bound_lemma("pivB$k", hcv(q), q, A, B0; m = MPIV))
    # `linarith`, not `rw`: for a negative pivot the Bernstein lemma bounds
    # `-p`, whose Horner form is a textually different expression, so there is
    # no syntactic occurrence of `p` to rewrite. `linarith` ring-normalises
    # both and finds the contradiction either way.
    push!(pivne, """
lemma pivNe$k (c : ℝ) (h₁ : clo ≤ c) (h₂ : c ≤ chi) : ($(hcv(p)) : ℝ) ≠ 0 := by
  intro hz
  have h := pivB$k c h₁ h₂
  linarith
""")
end

# --- back-substitution ------------------------------------------------------
back = String[]
for k in 30:-1:1
    r = cert.pivrow[k]
    subs = String[]
    for j in 1:33
        j == k && continue
        RC.iszp(cert.R[r, j]) && continue
        vname = j > 30 ? "hfree$(cols[j]-1)" : "Zc$(j)"
        push!(subs, "($(hc(cert.R[r,j]))) * $vname")
    end
    sub = isempty(subs) ? "" : " - " * join(subs, " - ")
    push!(back, """
  have Zm$k : ($(hc(cert.R[r,k]))) * V$(cols[k]-1) = 0 := by
    linear_combination $(ename(r, ver[r]))$sub
  have Zc$k : V$(cols[k]-1) = 0 :=
    (mul_eq_zero.mp Zm$k).resolve_left (pivNe$k (Real.cos z) (le_of_lt hcb.1) (le_of_lt hcb.2))
""")
end

# index (0-based) -> the fact proving that coordinate vanishes
idxproof = Dict{Int,String}()
idxproof[0] = "hfree0"; idxproof[1] = "hfree1"; idxproof[3] = "hfree3"
for k in 1:30; idxproof[cols[k]-1] = "Zc$k"; end
concl = [idxproof[i] for i in 0:32]

hyps = join(["    (E$(r)_0 :\n      " * rowform([copy(B[rows[i], cols[j]]) for i in 1:30, j in 1:33], r) *
             " = 0)" for r in 1:30], "\n")

# ---------------------------------------------------------------------------
# Geometric bridge.  `reduced_kernel` speaks about `V : Fin 33 → ℝ`; on its own
# that is exactly the kind of orphan algebra this project refuses to ship. The
# wrapper below ties `V` to the physical displacement of the polygon's vertices.
#
#   V_{2k}   = sin z · (δ_k)¹ ,  V_{2k+1} = (δ_k)² ,  V_32 = dt/2,
#   δ_k      = w_k − rigid a b e (p_k)
#
# with `a, b, e` chosen to kill the three free coordinates. Every one of the 30
# equations then holds for *arbitrary* `a, b, e` — because the rigid part is
# annihilated identically (`dsq_rigid`) — so only the three free-coordinate
# facts depend on the particular choice.
# ---------------------------------------------------------------------------

# XC1 is bounded below on the bracket; with sin z > 0 that makes (p1 z).1 ≠ 0,
# which is what makes the three rigid motions independent on the free
# coordinates x0, y0, y1.
xc1lem = Bernstein.lean_lower_bound_lemma("XC1_lower", "XC1 c", QQ.(AC._XC[2]), A, B0;
                                          m = QQ(9, 10), unfolds = " XC1")

# constraint list in row order: 16 sides, then the first 14 active diameters
constraints = Tuple{Int,Int,String}[]
for i in 0:15; push!(constraints, (i, mod(i + 1, 16), "hs$i")); end
for m in 1:14
    (i, j) = AC.ACTIVE_EDGES[m]; push!(constraints, (i, j, "hd$(m-1)"))
end
@assert length(constraints) == 30

hypdecl = join([(let (i, j, nm) = constraints[k]
    "    ($nm : dsq (p$i z) (p$j z) (w $i) (w $j) = $(k <= 16 ? "dt" : "0"))"
end) for k in 1:30], "\n")

Ventries = String[]
for k in 0:15
    push!(Ventries, "Real.sin z * ((w $k).1 - (a - e * (p$k z).2))")
    push!(Ventries, "(w $k).2 - (b + e * (p$k z).1)")
end
push!(Ventries, "dt / 2")
@assert length(Ventries) == 33

B0mat = [copy(B[rows[i], cols[j]]) for i in 1:30, j in 1:33]
"Row form with V replaced by the explicit geometric entries."
function rowform_geo(r)
    ts = String[]
    for j in 1:33
        RC.iszp(B0mat[r, j]) && continue
        push!(ts, "($(hc(B0mat[r,j]))) * ($(Ventries[cols[j]]))")
    end
    isempty(ts) ? "0" : join(ts, " +\n        ")
end

# Each of the 30 becomes its own declaration: keeping them inside
# `kernel_is_rigid` made a single elaboration unit far too large, and `isDefEq`
# timed out on the assembled application.
eqlemmas = String[]
eqcalls  = String[]
for k in 1:30
    (i, j, nm) = constraints[k]
    rhs = k <= 16 ? "dt" : "0"
    push!(eqlemmas,
        "/-- Constraint $k in reduced coordinates: the rigid part drops out\n" *
        "identically, so this holds for *arbitrary* `a b e`. -/\n" *
        "theorem Eg$k (z a b e dt : ℝ) (w : Fin 16 → ℝ × ℝ)\n" *
        "    (h : dsq (p$i z) (p$j z) (w $i) (w $j) = $rhs) :\n    " *
        rowform_geo(k) * " = 0 := by\n" *
        "  rw [red$i, red$j] at h ⊢\n" *
        "  simp only [dsq, XC$i, XC$j, YC$i, YC$j] at h ⊢\n" *
        "  linear_combination h / 2\n")
    push!(eqcalls, "  have E$(k)g := Eg$k z a b e dt w $nm")
end

extract = String[]
for k in 0:15
    push!(extract,
        "  · refine Prod.ext ?_ ?_\n" *
        "    · have h := (mul_eq_zero.mp K$(2k)).resolve_left (ne_of_gt hsz)\n" *
        "      simp only [rigid]; linarith\n" *
        "    · simp only [rigid]; linarith [K$(2k+1)]")
end

open(OUT, "w") do io
    print(io, """/-
AUTO-GENERATED by `lean/tools/gen_rank.jl` — do not edit by hand.

**`I_eq = R_eq` (Prop 6.2(6)), verified by the Lean kernel.**

The gate is not the number "rank = 30"; it is that the only tangent vectors
annihilated by every active constraint differential are the rigid infinitesimal
motions. Stated that way, Lean never touches `Matrix.det` or the rank API:
dense linear algebra becomes a sparse chain of `linear_combination` steps.

Scaling. With `p_k = (sin z · XC_k, YC_k)` the differential of `|p_j - p_i|²`
in a displacement `w` is `2[sin z · dXC · (w_j¹ - w_i¹) + dYC · (w_j² - w_i²)]`,
so setting `V_{2k} = sin z · w_k¹`, `V_{2k+1} = w_k²` and `V_32 = dt/2` makes
every coefficient a polynomial in `c` alone.

Why the reduction is modulo `Fc`. Measured on this very system, eliminating
*without* reducing reaches degree 1209 with 464-digit coefficients by step 30;
reducing at each step holds it to degree 11 and 9 digits. The price is that
each step is only valid mod `Fc`, so the reduction quotient is carried
explicitly:

    rowNEW = rowOLD − f · rowPIVOT − (Σ_j q_j V_j) · Fc

which is exactly what `linear_combination` consumes — Julia divides, Lean adds
back. There are $(length(cert.steps)) such steps, none with more than 13 correction terms,
and all 30 pivots are bounded away from zero on the bracket (worst |pivot| ≥
0.0575) by Bernstein certificates.
-/
import ChiquipoliLean.Multipliers

namespace Chiquipoli

/-- Directional derivative of `|p_b − p_a|²` when `p_a` moves by `u` and `p_b`
by `u'`. Linear in `(u, u')`, which is what lets the rigid part be subtracted. -/
noncomputable def dsq (a b u u' : ℝ × ℝ) : ℝ :=
  2 * ((b.1 - a.1) * (u'.1 - u.1) + (b.2 - a.2) * (u'.2 - u.2))

/-- A rigid infinitesimal motion: translation by `(a,b)` plus rotation at rate
`e` about the origin. -/
noncomputable def rigid (a b e : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (a - e * q.2, b + e * q.1)

/-- **`R_eq ⊆ I_eq`.** Every rigid infinitesimal motion is annihilated by every
constraint differential — and this needs no hypothesis at all: it is a ring
identity, true of any two points. -/
theorem dsq_rigid (a b e : ℝ) (p q : ℝ × ℝ) :
    dsq p q (rigid a b e p) (rigid a b e q) = 0 := by
  simp only [dsq, rigid]; ring

$(join(pivlem, "\n"))
$(join(pivne, "\n"))
-- The chain below is $(length(cert.steps)) elimination steps plus 30 back-substitutions in a
-- single declaration, so the default heartbeat budget is not enough. This is a
-- resource limit, not a soundness one.
set_option maxHeartbeats 2000000 in
/-- **`I_eq ⊆ R_eq`, in reduced coordinates.** If the $(length(rows)) constraint
differentials vanish on `V` and `V` vanishes on the three free coordinates,
then `V` vanishes identically. -/
theorem reduced_kernel (z : ℝ) (hF : Ffun z = 0)
    (hcb : Real.cos z ∈ Set.Ioo clo chi)
    ($(join(["V$i" for i in 0:32], " ")) : ℝ)
$hyps
    (hfree0 : V0 = 0) (hfree1 : V1 = 0) (hfree3 : V3 = 0) :
    $(join(["V$i = 0" for i in 0:32], " ∧ ")) := by
  have hFc : $(hc(Fc)) = 0 := by
    have := Fc_cos_eq_Ffun z; rw [hF] at this; simpa only [Fc] using this
$(join(haves, "\n"))
$(join(back, "\n"))
  exact ⟨$(join(concl, ", "))⟩

$xc1lem
/-- `(p₁)¹ ≠ 0`. This is what makes the three rigid motions independent on the
free coordinates `x₀, y₀, y₁`, and hence what lets `a, b, e` be solved for. -/
theorem p1_fst_ne (z : ℝ) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi) : (p1 z).1 ≠ 0 := by
  rw [red1]
  have h := XC1_lower (Real.cos z) (le_of_lt hcb.1) (le_of_lt hcb.2)
  have : (0:ℝ) < Real.sin z * XC1 (Real.cos z) := by positivity
  simpa using ne_of_gt this

$(join(eqlemmas, "\n"))
set_option maxHeartbeats 4000000 in
/-- **`I_eq = R_eq`, anchored to the polygon.**

If a displacement `w` of the sixteen vertices together with a change `dt` of the
squared side length annihilates every active constraint differential, then `dt`
is zero and `w` *is* a rigid infinitesimal motion — a translation plus a
rotation about the origin. This is the geometric content of Prop 6.2(6); the
algebra of `reduced_kernel` is here tied to the physical coordinates. -/
theorem kernel_is_rigid (z : ℝ) (hF : Ffun z = 0) (hsz : 0 < Real.sin z)
    (hcb : Real.cos z ∈ Set.Ioo clo chi)
    (w : Fin 16 → ℝ × ℝ) (dt : ℝ)
$hypdecl :
    dt = 0 ∧ ∃ a b e : ℝ,
$(join(["      w $k = rigid a b e (p$k z)" for k in 0:15], " ∧\n")) := by
  obtain ⟨a, ha⟩ : ∃ x : ℝ, x = (w 0).1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x : ℝ, x = (w 0).2 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ x : ℝ, x = ((w 1).2 - b) / (p1 z).1 := ⟨_, rfl⟩
  have hp1 := p1_fst_ne z hsz hcb
$(join(eqcalls, "\n"))
  have F0 : Real.sin z * ((w 0).1 - (a - e * (p0 z).2)) = 0 := by
    rw [ha]; simp only [p0]; ring
  have F1 : (w 0).2 - (b + e * (p0 z).1) = 0 := by
    rw [hb]; simp only [p0]; ring
  have F3 : (w 1).2 - (b + e * (p1 z).1) = 0 := by
    rw [he, div_mul_cancel₀ _ hp1]; ring
  obtain $(join(["K$i" for i in 0:32], ", ") |> x -> "⟨" * x * "⟩") :=
    reduced_kernel z hF hcb
$(join(["      ($v)" for v in Ventries], "\n"))
$(join(["      E$(k)g" for k in 1:30], "\n"))
      F0 F1 F3
  refine ⟨by linarith [K32], a, b, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
$(join(extract, "\n"))

end Chiquipoli
""")
end
println("wrote ", OUT)
