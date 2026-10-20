# Generate lean/ChiquipoliLean/Generated/Radius.lean.
#
#     julia --project=. lean/generators/gen_radius.jl
#
# The numerical half of the Lean proof of Theorem 6.4 (the explicit radius of
# A16). Everything emitted here is a rational number or a certificate the Lean
# kernel re-checks; nothing is trusted:
#
#   * two-sided Bernstein bounds for the 32 coordinate polynomials XC_i, YC_i on
#     the certified bracket [clo, chi], and a rational bracket for sin z;
#   * Bernstein lower bounds for the multipliers of Generated/Multipliers.lean
#     (the same witness, recomputed here exactly as gen_multipliers.jl does):
#     α_i ≥ -67/1000 and λ_e ≥ 3/2500;
#   * a rational configuration phR within radEps of A16, coordinate by
#     coordinate, and the rational matrix Chat of the squared-normalisation
#     Jacobian at phR stacked with the three rigid motions;
#   * an approximate LDLᵀ factorisation of ChatᵀChat - (11/400)·Id whose exact
#     rational residual has every absolute row sum ≤ 10^-12 (checked by the
#     kernel with `decide +kernel`).
#
# Floating point (BigFloat, 256 bits) is used only to *propose* L and d; the
# residual that the kernel checks is computed exactly.

include(joinpath(@__DIR__, "..", "..", "pipeline", "stages", "_bootstrap.jl"))
include(joinpath(@__DIR__, "multipliers.jl"))
include(joinpath(@__DIR__, "bernstein.jl"))
using .Bernstein

const AC = A16Certificate
const QQ = Rational{BigInt}
const OUT = joinpath(@__DIR__, "..", "ChiquipoliLean", "Generated", "Radius.lean")

# The bracket fixed in RootExists.lean, and the multiplier pin of gen_multipliers.jl.
const A = QQ(613, 625)
const B = QQ(980801, 1000000)
const PIN = QQ(1, 375)

# Constants of the certificate.
const ABOUND = QQ(67, 1000)        # -α_i ≤ ABOUND
const LBOUND = QQ(3, 2500)         # λ_e ≥ LBOUND
const S1 = QQ(1950112, 10^7)       # sin z ∈ [S1, S2]
const S2 = QQ(1950164, 10^7)
const DEN = big(10)^12             # denominators of phR
const SIGHAT = QQ(11, 400)         # Gram lower bound at phR, before the residual
const MU = QQ(1, big(10)^12)       # residual row-sum bound
const LDEN = big(10)^18            # denominators of L and d
const TT = QQ(1, 250)              # the splitting parameter t of Qform_perturb
const SIG2 = QQ(17, 625)           # σ2 handed to radius_of_certificate
const RAD = QQ(663, 10^6)          # the radius of Theorem 6.4

const ACTA = [0, 0, 0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 6, 7, 7]
const ACTB = [7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 13, 13, 14, 14, 15]

Fc = QQ.(AC.Fc_poly())
XC = [QQ.(p) for p in AC._XC]
YC = [QQ.(p) for p in AC._YC]
active = AC.ACTIVE_EDGES
@assert [e[1] for e in active] == ACTA && [e[2] for e in active] == ACTB "active edges differ"

lean_rat(q::QQ) = denominator(q) == 1 ?
    (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
    (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" :
                        "($(numerator(q))/$(denominator(q)))")
real_lit(q::QQ) = "($(lean_rat(q)) : ℝ)"

floorq(x::QQ, d) = QQ(fld(numerator(x) * d, denominator(x)), d)
ceilq(x::QQ, d)  = QQ(cld(numerator(x) * d, denominator(x)), d)
roundq(x::QQ, d) = QQ(div(2 * numerator(x) * d + denominator(x), 2 * denominator(x)), d)

# --- sin z bracket ----------------------------------------------------------
@assert S1 > 0 && S1^2 <= 1 - B^2 "S1 too large"
@assert S2^2 >= 1 - A^2 "S2 too small"

# --- coordinate bounds ------------------------------------------------------
# For a constant polynomial the Bernstein lemma degenerates to arithmetic; the
# bounds are widened by 10^-12 so that the emitted inequality is strict.
function bounds(p)
    γ = Bernstein.bern_coeffs(p, A, B)
    length(p) == 1 && return (p[1] - QQ(1, DEN), p[1] + QQ(1, DEN))
    return (floorq(minimum(γ), DEN), ceilq(maximum(γ), DEN))
end
xb = [bounds(XC[i+1]) for i in 0:15]
yb = [bounds(YC[i+1]) for i in 0:15]
xh = [roundq(((S1 + S2) / 2) * (xb[i+1][1] + xb[i+1][2]) / 2, DEN) for i in 0:15]
yh = [roundq((yb[i+1][1] + yb[i+1][2]) / 2, DEN) for i in 0:15]
# the four corners of s*X over [S1,S2]×[Xlo,Xhi], and the two ends of Y
errs = QQ[]
for i in 0:15
    (lo, hi) = xb[i+1]
    for v in (S1 * lo, S2 * lo, S1 * hi, S2 * hi); push!(errs, abs(v - xh[i+1])); end
    (ylo, yhi) = yb[i+1]
    push!(errs, abs(ylo - yh[i+1])); push!(errs, abs(yhi - yh[i+1]))
end
const EPS = ceilq(maximum(errs), big(10)^8)
println("radEps = ", EPS, " ≈ ", Float64(EPS))

# --- multipliers (the witness of Generated/Multipliers.lean) -----------------
sol = Multipliers.exact_multipliers(XC, YC, Fc, active; pin_value = QQ[PIN])
@assert sol !== nothing "multiplier solve failed"
@assert all(Multipliers.iszp, sol.residuals) "stationarity residuals are not all zero"
αmin = minimum(minimum(Bernstein.bern_coeffs(sol.y[i], A, B)) for i in 1:16)
λmin = minimum(minimum(Bernstein.bern_coeffs(sol.y[16+m], A, B)) for m in 1:15)
@assert αmin >= -ABOUND "α bound fails: $(Float64(αmin))"
@assert λmin >= LBOUND "λ bound fails: $(Float64(λmin))"
println("Bernstein: min α ≥ ", Float64(αmin), ", min λ ≥ ", Float64(λmin))

# --- the rational matrix Chat (34 × 33) -------------------------------------
P = [(xh[i+1], yh[i+1]) for i in 0:15]
Chat = [zeros(QQ, 33) for _ in 1:34]
for i in 0:15
    j = mod(i + 1, 16); r = Chat[i+1]
    dx = 2 * (P[j+1][1] - P[i+1][1]); dy = 2 * (P[j+1][2] - P[i+1][2])
    r[2j+1] += dx; r[2j+2] += dy; r[2i+1] -= dx; r[2i+2] -= dy; r[33] = -1
end
for (m, (a, b)) in enumerate(active)
    r = Chat[16+m]
    dx = 2 * (P[b+1][1] - P[a+1][1]); dy = 2 * (P[b+1][2] - P[a+1][2])
    r[2b+1] += dx; r[2b+2] += dy; r[2a+1] -= dx; r[2a+2] -= dy
end
for i in 0:15
    Chat[32][2i+1] = 1
    Chat[33][2i+2] = 1
    Chat[34][2i+1] = -P[i+1][2]; Chat[34][2i+2] = P[i+1][1]
end

# --- LDLᵀ of ChatᵀChat - SIGHAT·Id, proposed in BigFloat, checked exactly ---
G = [sum(Chat[r][i] * Chat[r][j] for r in 1:34) for i in 1:33, j in 1:33]
S = [G[i, j] - (i == j ? SIGHAT : QQ(0)) for i in 1:33, j in 1:33]
Lq = zeros(QQ, 33, 33); dq = zeros(QQ, 33)
setprecision(BigFloat, 256) do
    Sf = BigFloat.(S)
    L = zeros(BigFloat, 33, 33); d = zeros(BigFloat, 33)
    for j in 1:33
        d[j] = Sf[j, j] - sum((L[j, k]^2 * d[k] for k in 1:j-1); init = big(0.0))
        L[j, j] = 1
        for i in j+1:33
            L[i, j] = (Sf[i, j] - sum((L[i, k] * L[j, k] * d[k] for k in 1:j-1); init = big(0.0))) / d[j]
        end
    end
    for i in 1:33, j in 1:33
        Lq[i, j] = QQ(round(BigInt, L[i, j] * LDEN), LDEN)
    end
    for k in 1:33
        dq[k] = QQ(round(BigInt, d[k] * LDEN), LDEN)
    end
end
@assert all(>(0), dq) "a pivot is not positive"
E = [S[i, j] - sum(Lq[i, k] * dq[k] * Lq[j, k] for k in 1:33) for i in 1:33, j in 1:33]
rowmax = maximum(sum(abs(E[i, j]) for j in 1:33) for i in 1:33)
@assert rowmax <= MU "residual row sum $(Float64(rowmax)) exceeds MU"
println("min pivot ", Float64(minimum(dq)), ", max residual row sum ", Float64(rowmax))

# --- the arithmetic the instance file performs -------------------------------
KC = QQ(128 + 128 * 15 + 2 * 16)
avail = (1 - TT) * (SIGHAT - MU) - (1 // TT - 1) * KC * EPS^2
@assert SIG2 <= avail "σ2 = $(Float64(SIG2)) exceeds what the certificate gives, $(Float64(avail))"
@assert 16 * RAD^2 * (LBOUND^2 + ABOUND^2) <= SIG2 * LBOUND^2 "radius condition fails"
println("σ2 available ", Float64(avail), "; radius condition slack ",
        Float64(SIG2 * LBOUND^2 / (16 * RAD^2 * (LBOUND^2 + ABOUND^2))))

# --- emit -------------------------------------------------------------------
mat_lit(rows) = "!![" * join([join(lean_rat.(r), ", ") for r in rows], ";\n    ") * "]"
rows_of(M) = [M[i, :] for i in 1:size(M, 1)]

function row_rhs(k)
    k < 16 && return "Feasible.sideRow phR v dt $k"
    k < 31 && return "Feasible.diamRow phR radA radB v $(k - 16)"
    k == 31 && return "∑ i, (v i).1"
    k == 32 && return "∑ i, (v i).2"
    return "∑ i, ip (v i) (J (phR i))"
end
function row_proof(k)
    k < 16 && return "  simp [Fin.sum_univ_succ, Chat, flat, Feasible.sideRow, phR, ip]\n  ring"
    k < 31 && return "  simp [Fin.sum_univ_succ, Chat, flat, Feasible.diamRow, phR, ip, radA, radB]\n  ring"
    k < 33 && return "  rw [sum16r]\n  simp [Fin.sum_univ_succ, Chat, flat]\n  ring"
    return "  rw [sum16r]\n  simp [Fin.sum_univ_succ, Chat, flat, phR, ip, J]\n  ring"
end

io = IOBuffer()
print(io, """/-
AUTO-GENERATED by `lean/generators/gen_radius.jl` — do not edit by hand.

**The numerical certificate of Theorem 6.4 (the explicit radius of A16).**

`Theory/Radius.lean` proves the article's argument for Theorem 6.4 from four
hypotheses: the multiplier identity, a lower bound `Λ` on the active diameter
multipliers, an upper bound `A` on `-αᵢ`, and a coercivity bound `σ2` for the
squared-normalisation Jacobian on the complement of the rigid motions. This file
supplies the rational data from which `Instances/A16Radius.lean` derives them:

  * Bernstein bounds on the bracket `[clo, chi]` for the 32 coordinate
    polynomials (`XC*_lo`, `XC*_hi`, `YC*_lo`, `YC*_hi`) and for the multipliers
    of `Generated/Multipliers.lean` (`mA*_ge`: `αᵢ ≥ $(lean_rat(-ABOUND))`,
    `mL*_ge`: `λₑ ≥ $(lean_rat(LBOUND))`);
  * the rational bracket `radS1 ≤ sin z ≤ radS2` and, vertex by vertex, the
    enclosure `|p_i z − phR i| ≤ radEps` coordinatewise (`p*_enc`);
  * the rational configuration `phR`, the matrix `Chat` of the Jacobian at `phR`
    stacked with the three rigid motions, and an approximate `LDLᵀ`
    factorisation of `ChatᵀChat − ($(lean_rat(SIGHAT)))·Id` whose exact residual
    has every absolute row sum at most `$(lean_rat(MU))` (`gram_rows`, checked by
    `decide +kernel` in exact rational arithmetic);
  * `Qhat_lower`: `($(lean_rat(SIGHAT)) − $(lean_rat(MU))) (‖v‖² + dt²) ≤ Qform phR … v dt`.

Floating point only proposed `L` and `d`; every inequality here is exact.
radEps = $(lean_rat(EPS)) ≈ $(Float64(EPS)).
-/
import ChiquipoliLean.Generated.Multipliers
import ChiquipoliLean.Theory.Coercive

namespace Chiquipoli

open Chiquipoli.FirstOrder Chiquipoli.Feasible

/-! ## Constants -/

noncomputable def radS1 : ℝ := $(lean_rat(S1))
noncomputable def radS2 : ℝ := $(lean_rat(S2))
noncomputable def radEps : ℝ := $(lean_rat(EPS))

/-- `sin z` lies in `[radS1, radS2]` at every `z` with `sin z > 0` and `cos z` in
the bracket. -/
lemma sin_bracket (z : ℝ) (hsz : 0 < Real.sin z) (h₁ : clo ≤ Real.cos z)
    (h₂ : Real.cos z ≤ chi) : radS1 ≤ Real.sin z ∧ Real.sin z ≤ radS2 := by
  have hp := Real.sin_sq_add_cos_sq z
  have hc0 : 0 < Real.cos z := lt_of_lt_of_le (by unfold clo; norm_num) h₁
  unfold clo at h₁; unfold chi at h₂
  constructor
  · unfold radS1; nlinarith
  · unfold radS2; nlinarith

/-! ## Bernstein bounds: coordinates -/

""")
for (nm, polys, bnds) in (("XC", XC, xb), ("YC", YC, yb))
    for i in 0:15
        (lo, hi) = bnds[i+1]
        print(io, Bernstein.lean_lower_bound_lemma("$(nm)$(i)_lo", "$(nm)$(i) c", polys[i+1], A, B;
                                                   m = lo, unfolds = " $(nm)$(i)"), "\n")
        print(io, Bernstein.lean_lower_bound_lemma("$(nm)$(i)_hi", "(-$(nm)$(i) c)", -polys[i+1], A, B;
                                                   m = -hi, unfolds = " $(nm)$(i)"), "\n")
    end
end
print(io, "/-! ## Bernstein bounds: multipliers -/\n\n")
for i in 0:15
    print(io, Bernstein.lean_lower_bound_lemma("mA$(i)_ge", "mA$(i) c", sol.y[i+1], A, B;
                                               m = -ABOUND, unfolds = " mA$(i)"), "\n")
end
for m in 0:14
    print(io, Bernstein.lean_lower_bound_lemma("mL$(m)_ge", "mL$(m) c", sol.y[17+m], A, B;
                                               m = LBOUND, unfolds = " mL$(m)"), "\n")
end

print(io, """/-! ## The rational configuration and the vertex enclosures -/

/-- The rational configuration at which the Gram certificate is computed. -/
noncomputable def phR : Fin 16 → ℝ × ℝ :=
  ![$(join(["($(real_lit(xh[i+1])), $(real_lit(yh[i+1])))" for i in 0:15], ",\n    "))]

/-- The active diameters, in the order of `ACTIVE_EDGES`. -/
def radA : Fin 15 → Fin 16 := ![$(join(ACTA, ", "))]
def radB : Fin 15 → Fin 16 := ![$(join(ACTB, ", "))]

""")
for i in 0:15
    (lo, hi) = xb[i+1]; (ylo, yhi) = yb[i+1]
    print(io, """lemma p$(i)_enc (z : ℝ) (hs1 : radS1 ≤ Real.sin z) (hs2 : Real.sin z ≤ radS2)
    (h₁ : clo ≤ Real.cos z) (h₂ : Real.cos z ≤ chi) :
    |(p$(i) z - phR $(i)).1| ≤ radEps ∧ |(p$(i) z - phR $(i)).2| ≤ radEps := by
  have hxl := XC$(i)_lo (Real.cos z) h₁ h₂
  have hxh := XC$(i)_hi (Real.cos z) h₁ h₂
  have hyl := YC$(i)_lo (Real.cos z) h₁ h₂
  have hyh := YC$(i)_hi (Real.cos z) h₁ h₂
  rw [red$(i)]
  refine ⟨?_, ?_⟩
  · exact enclose_mul (s1 := radS1) (s2 := radS2) (xh := $(real_lit(xh[i+1])))
      (by unfold radS1; norm_num) hs1 hs2 hxl
      (show XC$(i) (Real.cos z) ≤ $(real_lit(hi)) by linarith)
      (by unfold radS1 radEps; norm_num) (by unfold radS2 radEps; norm_num)
      (by unfold radS1 radEps; norm_num) (by unfold radS2 radEps; norm_num)
  · exact enclose_one (yh := $(real_lit(yh[i+1]))) hyl
      (show YC$(i) (Real.cos z) ≤ $(real_lit(yhi)) by linarith)
      (by unfold radEps; norm_num) (by unfold radEps; norm_num)

""")
end

print(io, """/-! ## The Gram certificate -/

/-- Rows: the 16 sides, the 15 active diameters, the two translations and the
rotation; columns: `x₀, y₀, …, x₁₅, y₁₅, dt`. -/
def Chat : Fin 34 → Fin 33 → ℚ :=
  $(mat_lit(Chat))

/-- Proposed `L` of the `LDLᵀ` factorisation (exact rationals). -/
def Lq : Fin 33 → Fin 33 → ℚ :=
  $(mat_lit(rows_of(Lq)))

/-- Proposed diagonal `d` of the `LDLᵀ` factorisation. -/
def dq : Fin 33 → ℚ :=
  ![$(join(lean_rat.(dq), ", "))]

theorem dq_nonneg : ∀ k, 0 ≤ dq k := by decide +kernel

/-- **The kernel check.** Every absolute row sum of the exact residual
`ChatᵀChat − ($(lean_rat(SIGHAT)))·Id − Lq·diag(dq)·Lqᵀ` is at most `$(lean_rat(MU))`. -/
theorem gram_rows :
    ∀ i, ∑ j, |gramResidual Chat Lq dq ($(lean_rat(SIGHAT))) i j| ≤ $(lean_rat(MU)) := by
  decide +kernel

/-- The flattening `(v, dt) ↦ (x₀, y₀, …, x₁₅, y₁₅, dt)`. -/
noncomputable def flat (v : Fin 16 → ℝ × ℝ) (dt : ℝ) : Fin 33 → ℝ :=
  ![$(join(["(v $i).1, (v $i).2" for i in 0:15], ", ")), dt]

lemma sum16r (f : Fin 16 → ℝ) :
    ∑ i, f i = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11+f 12+f 13+f 14+f 15 := by
  simp [Fin.sum_univ_succ]; ring

lemma sum15r (f : Fin 15 → ℝ) :
    ∑ i, f i = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11+f 12+f 13+f 14 := by
  simp [Fin.sum_univ_succ]; ring

lemma sum34r (f : Fin 34 → ℝ) :
    ∑ i, f i = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10+f 11+f 12+f 13+f 14+f 15
      +f 16+f 17+f 18+f 19+f 20+f 21+f 22+f 23+f 24+f 25+f 26+f 27+f 28+f 29+f 30+f 31
      +f 32+f 33 := by
  simp [Fin.sum_univ_succ]; ring

lemma flat_sq (v : Fin 16 → ℝ × ℝ) (dt : ℝ) : ∑ i, flat v dt i ^ 2 = cip v v + dt ^ 2 := by
  rw [cip, sum16r]
  simp [Fin.sum_univ_succ, flat, ip]
  ring

""")
for k in 0:33
    print(io, """lemma chat_row_$(k) (v : Fin 16 → ℝ × ℝ) (dt : ℝ) :
    ∑ i, (Chat $(k) i : ℝ) * flat v dt i = $(row_rhs(k)) := by
$(row_proof(k))

""")
end
print(io, """/-- The form at `phR` is the squared norm of `Chat` applied to the flattening. -/
theorem Qhat_eq (v : Fin 16 → ℝ × ℝ) (dt : ℝ) :
    Qform phR radA radB v dt = ∑ k, (∑ i, (Chat k i : ℝ) * flat v dt i) ^ 2 := by
  rw [Qform, sum16r (fun i => Feasible.sideRow phR v dt i ^ 2),
    sum15r (fun e => Feasible.diamRow phR radA radB v e ^ 2),
    sum34r (fun k => (∑ i, (Chat k i : ℝ) * flat v dt i) ^ 2)]
  rw [$(join(["chat_row_$k" for k in 0:33], ", "))]
  ring

/-- **The Gram bound at `phR`.** -/
theorem Qhat_lower (v : Fin 16 → ℝ × ℝ) (dt : ℝ) :
    (($(lean_rat(SIGHAT)) - $(lean_rat(MU)) : ℚ) : ℝ) * (cip v v + dt ^ 2) ≤ Qform phR radA radB v dt := by
  have h := gram_lower Chat Lq dq ($(lean_rat(SIGHAT))) ($(lean_rat(MU))) dq_nonneg gram_rows (flat v dt)
  rw [flat_sq] at h
  rw [Qhat_eq]
  exact h

end Chiquipoli
""")
open(OUT, "w") do f
    write(f, String(take!(io)))
end
println("wrote ", OUT)
