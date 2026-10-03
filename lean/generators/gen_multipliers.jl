# Generate lean/ChiquipoliLean/Generated/Multipliers.lean.
#
#     julia --project=. lean/generators/gen_multipliers.jl
#
# **Strictly positive multipliers and the stationarity identity (Prop 6.2(5)).**
#
# Anchored to the geometry, not stated as loose polynomial identities. The
# formulation uses the squared side length `t = ℓ²` as the scalar variable:
#
#     side i      :  |p_{i+1} - p_i|² - t = 0
#     diameter ij :  |p_i - p_j|²     - 1 = 0
#     objective   :  t                        (maximising 16√t ⟺ maximising t)
#
# Both reparametrisations (`d ↦ d²`, `ℓ ↦ ℓ²`) rescale multipliers by strictly
# positive factors, so strict positivity of the diameter multipliers is exactly
# the paper's condition. The payoff is that every Jacobian entry is
# `2(p_j - p_i)` — no division by `ℓ = √(2-2c)` — so the whole witness lives in
# `Q(c,s)` rather than a degree-4 extension.
#
# What Lean checks. The gradient of the Lagrangian with respect to vertex `k`
# is `2 · Σ_{C ∋ k} y_C · σ · (p_b - p_a)`; stationarity in the vertex
# directions is exactly that this vanishes for every `k`. Those 16 vector
# equations are stated over the *actual* vertices `p_k z` — so they are
# statements about the polygon, not about polynomials — plus the scalar
# equation `Σ α_i = -1` coming from the `t` direction.
#
# The witness itself is computed once, exactly, in `multipliers.jl` by Gaussian
# elimination over `Q[c]/(Fc)`. Lean never solves; it only checks.

include(joinpath(@__DIR__, "..", "..", "pipeline", "stages", "_bootstrap.jl"))
include(joinpath(@__DIR__, "multipliers.jl"))
include(joinpath(@__DIR__, "bernstein.jl"))
using .Multipliers, .Bernstein

const AC = A16Certificate
const QQ = Rational{BigInt}
const OUT = joinpath(@__DIR__, "..", "ChiquipoliLean", "Generated", "Multipliers.lean")

const A = QQ(613, 625)
const B = QQ(980801, 1000000)
const PIN = QQ(1, 375)      # inside the feasible window (0.00074, 0.00459)
const MLAM = QQ(1, 1000)    # uniform lower bound; worst λ clears 0.0012465

Fc = QQ.(AC.Fc_poly())
XC = [QQ.(p) for p in AC._XC]
YC = [QQ.(p) for p in AC._YC]
active = AC.ACTIVE_EDGES

sol = Multipliers.exact_multipliers(XC, YC, Fc, active; pin_value = QQ[PIN])
@assert sol !== nothing "multiplier solve failed"
@assert all(Multipliers.iszp, sol.residuals) "stationarity residuals are not all zero"
println("stationarity residuals: 33/33 exactly zero mod Fc")

# Σ α_i must be the constant polynomial -1.
sumα = reduce(Multipliers.padd, sol.y[1:16])
@assert Multipliers.iszp(Multipliers.padd(sumα, QQ[QQ(1)])) "Σα is not identically -1"
println("Σα ≡ -1 as a polynomial identity")

lean_rat(q::QQ) = denominator(q) == 1 ?
    (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
    (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" :
                        "($(numerator(q))/$(denominator(q)))")

function horner(p, var="c")
    p = Multipliers.ptrim(p)
    Multipliers.iszp(p) && return "0"
    n = length(p) - 1
    n == 0 && return lean_rat(p[1])
    e = lean_rat(p[n+1])
    for k in (n-1):-1:0
        e = p[k+1] == 0 ? "($e) * $var" : "($e) * $var + $(lean_rat(p[k+1]))"
    end
    return e
end

# --- names -----------------------------------------------------------------
aname(i) = "mA$i"                 # side multiplier for side (i, i+1)
lname(m) = "mL$(m-1)"             # diameter multiplier for active[m]

defs = String[]
for i in 1:16
    push!(defs, "/-- Side multiplier `α_$(i-1)` for the side `($(i-1), $(mod(i,16)))`. -/\n" *
                "noncomputable def $(aname(i-1)) (c : ℝ) : ℝ := $(horner(sol.y[i]))\n")
end
for m in 1:15
    (i, j) = active[m]
    push!(defs, "/-- Active-diameter multiplier `λ` for the pair `($i, $j)`. -/\n" *
                "noncomputable def $(lname(m)) (c : ℝ) : ℝ := $(horner(sol.y[16+m]))\n")
end

# --- constraint incidence ---------------------------------------------------
# Each constraint is (a, b, multiplier-name). Gradient wrt vertex k is
#   Σ_{C=(a,b), k=a} (-y_C)(p_b - p_a) + Σ_{C=(a,b), k=b} (+y_C)(p_b - p_a).
cons = Tuple{Int,Int,String}[]
for i in 0:15
    push!(cons, (i, mod(i + 1, 16), aname(i)))
end
for m in 1:15
    (i, j) = active[m]
    push!(cons, (i, j, lname(m)))
end

grads = String[]
gx = Dict{Int,String}(); gy = Dict{Int,String}()
for k in 0:15
    terms = String[]
    for (a, b, nm) in cons
        if k == a
            push!(terms, "-$nm (Real.cos z) * ((p$b z).%C - (p$a z).%C)")
        elseif k == b
            push!(terms, "$nm (Real.cos z) * ((p$b z).%C - (p$a z).%C)")
        end
    end
    @assert !isempty(terms)
    for (comp, lbl, vrow) in ((1, "x", 2k + 1), (2, "y", 2k + 2))
        body = join(replace.(terms, "%C" => string(comp)), " +\n      ")
        reds = sort(unique(vcat([a for (a, b, _) in cons if k == a || k == b],
                                [b for (a, b, _) in cons if k == a || k == b])))
        unf = join(["red$v" for v in reds], ", ")
        mults = join(unique([nm for (a, b, nm) in cons if k == a || k == b]), ", ")
        xcs = join(vcat(["XC$v" for v in reds], ["YC$v" for v in reds]), ", ")
        # The x-rows carry a common factor `sin z` (every vertex is
        # `(sin z * XC, YC)`), so it must appear in the linear_combination
        # coefficient; the y-rows do not.
        qexpr = horner(sol.quot[vrow], "Real.cos z")
        coeff = comp == 1 ? "(Real.sin z * ($qexpr))" : "($qexpr)"
        comp == 1 ? (gx[k] = body) : (gy[k] = body)
        push!(grads, """
/-- Stationarity at vertex $k, $lbl-component: the multiplier-weighted sum of
constraint gradients vanishes. Stated over the actual vertices `p_k z`, so this
is a statement about the polygon rather than about polynomials. -/
theorem grad$(lbl)_$k (z : ℝ) (hF : Ffun z = 0) :
    $body = 0 := by
  have hc : Fc (Real.cos z) = 0 := by rw [Fc_cos_eq_Ffun]; exact hF
  simp only [Fc] at hc
  rw [$unf]
  simp only [$mults, $xcs]
  linear_combination $coeff * hc
""")
    end
end

println("emitting ", length(defs), " multiplier defs and ", length(grads), " gradient identities")

# --- Bernstein positivity for the 15 λ -------------------------------------
function build_bern()
    out = String[]; w = nothing
    for m in 1:15
        p = sol.y[16+m]
        γ = Bernstein.bern_coeffs(p, A, B)
        mn = minimum(γ)
        @assert mn > MLAM "λ_$m margin $(Float64(mn)) below the uniform bound"
        w = w === nothing ? mn : min(w, mn)
        push!(out, Bernstein.lean_lower_bound_lemma(
            "$(lname(m))_pos", "$(lname(m)) c", p, A, B; m = MLAM, unfolds = " $(lname(m))"))
    end
    return out, w
end
bern, worst = build_bern()
println("worst Bernstein lower bound on λ: ", Float64(worst))

open(OUT, "w") do io
    print(io, """/-
AUTO-GENERATED by `lean/generators/gen_multipliers.jl` — do not edit by hand.

**Strictly positive multipliers and the stationarity identity (Prop 6.2(5)),
verified by the Lean kernel.**

Formulation. The scalar variable is the *squared* common side length `t = ℓ²`:

    side i      :  |p_{i+1} - p_i|² - t = 0
    diameter ij :  |p_i - p_j|²     - 1 = 0
    objective   :  t

Maximising the perimeter `16√t` is the same as maximising `t`, and both
reparametrisations (`d ↦ d²`, `ℓ ↦ ℓ²`) rescale the multipliers by strictly
positive factors — so strict positivity of the diameter multipliers below is
exactly the paper's condition. The gain is that every constraint gradient is
`2(p_j - p_i)` with no division by `ℓ = √(2-2c)`, keeping the entire witness
inside `Q(c,s)` instead of a degree-4 extension of `Q(c)`.

What is proved here, anchored to the geometry rather than to loose polynomial
identities:

  * `gradx_k`, `grady_k` (16 vertices, 32 statements) — at every vertex the
    multiplier-weighted sum of constraint gradients vanishes, stated over the
    actual vertices `p_k z`;
  * `alpha_sum` — `Σ α_i = -1`, the `t`-direction equation, which holds as an
    exact polynomial identity (not merely mod `Fc`);
  * `mL*_pos` — each of the 15 diameter multipliers is strictly positive
    throughout the bracket, by Bernstein certificates.

The witness is computed once, exactly, by Gaussian elimination over
`Q[c]/(Fc)` in `lean/generators/multipliers.jl`; Lean never solves a system, it
only checks one. Because the active Jacobian has rank 30 rather than 31 (LICQ
fails) the multipliers are a 1-parameter affine family; the normalisation is
pinned at `λ_(0,9) = $(PIN)`, chosen inside the feasible window
`(0.00074, 0.00459)` computed in Julia. The tightest λ clears `0.0012465`
against the uniform declared bound `$(MLAM)`.

NOT those of Table S2 (Online Resource 1 of the article). That table — and the
Julia certificate, which reproduces it exactly — exhibits a different point of that affine family,
and the ratio between the two is not even constant (0.0110 to 0.0138 across
edges). Theorem 3.5 asks only that *some* vector exist with every active
diameter multiplier strictly positive; both points witness that. Lean certifies
its own witness end to end and does not claim to reproduce the paper's. See
lean/README.md for the per-edge comparison.
-/
import ChiquipoliLean.Generated.Convexity

namespace Chiquipoli

$(join(defs, "\n"))
/-- The `t`-direction equation. This one is an exact polynomial identity: it
needs no appeal to `Fc = 0`. -/
theorem alpha_sum (c : ℝ) :
    $(join([aname(i) * " c" for i in 0:15], " + ")) = -1 := by
  simp only [$(join([aname(i) for i in 0:15], ", "))]; ring

$(join(bern, "\n"))
$(join(grads, "\n"))
/-- The multiplier-weighted sum of constraint gradients at vertex `k`, as an
honest vector in the plane. Stationarity in the vertex directions is exactly
that this vanishes for every `k`. -/
noncomputable def gradSum (k : Fin 16) (z : ℝ) : ℝ × ℝ :=
  ![$(join(["fun z => ($(gx[k]),\n      $(gy[k]))" for k in 0:15], ",\n    "))] k z

/-- **Stationarity at every vertex.** -/
theorem stationarity_vertex (z : ℝ) (hF : Ffun z = 0) (k : Fin 16) :
    gradSum k z = (0, 0) := by
  fin_cases k
$(join(["  · exact congrArg₂ Prod.mk (gradx_$k z hF) (grady_$k z hF)" for k in 0:15], "\n"))

/-- **Prop 6.2(5), assembled.** At the constructor root there are multipliers
for the sixteen side constraints and the fifteen active-diameter constraints
such that

  * the weighted sum of constraint gradients vanishes at every vertex,
  * the `t`-direction equation `Σ α_i = -1` holds, and
  * every active-diameter multiplier is **strictly positive**.

Together these are the stationarity identity with strictly positive active
multipliers that Theorem 3.5 requires. Note this does *not* require LICQ — the
active Jacobian has rank 30, not 31 — only that some such multiplier vector
exists, which is what is exhibited here. -/
theorem multipliers_certified (z : ℝ) (hF : Ffun z = 0)
    (hc : Real.cos z ∈ Set.Ioo clo chi) :
    (∀ k : Fin 16, gradSum k z = (0, 0)) ∧
    ($(join([aname(i) * " (Real.cos z)" for i in 0:15], " + ")) = -1) ∧
    ($(join(["0 < $(lname(m)) (Real.cos z)" for m in 1:15], " ∧ "))) := by
  refine ⟨stationarity_vertex z hF, alpha_sum _, ?_⟩
  refine ⟨$(join(["by linarith [$(lname(m))_pos (Real.cos z) (le_of_lt hc.1) (le_of_lt hc.2)]" for m in 1:15], ", "))⟩

end Chiquipoli
""")
end
println("wrote ", OUT)
