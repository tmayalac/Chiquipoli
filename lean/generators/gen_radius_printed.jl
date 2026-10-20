# Generate lean/ChiquipoliLean/Generated/RadiusPrinted.lean.
#
#     julia --project=. lean/generators/gen_radius_printed.jl
#
# The numerical half of the Lean proof of Theorem 6.4 *with the printed
# constants* (Theory/RadiusPrinted.lean has the argument). Everything emitted is
# a rational number or a certificate the kernel re-checks:
#
#   * a second exact multiplier witness M0 (squared normalisation, pinned at
#     λ_(0,9) = 0), with its 32 stationarity identities; with the witness W1 of
#     Generated/Multipliers.lean (pinned at 1/375) it spans the affine family, and
#     the article's representative (Table S2, λ_(0,9) = 1/5 in the unit
#     normalisation) is (1-θ) M0 + θ W1 with θ = 75ℓ/16, rescaled;
#   * Bernstein bounds for M0 and W1 - M0 on a bracket of width 10^-16 that
#     contains the 10^-22 root bracket of Constructor/SideLength.lean, and from
#     them λ_e > 0.09186 for every active diameter and ‖α‖₂² < 4.004²;
#   * the rational matrix of the unit Jacobian B = D(e,d) at phR (the
#     configuration of Generated/Radius.lean), with ℓ replaced by rationals
#     LU1 ≤ ℓ ≤ LU2, stacked with the rigid motions, and an LDLᵀ certificate
#     of its Gram matrix minus SIGHAT·Id (checked by `decide +kernel`);
#   * the closing arithmetic: σ² = 0.09119 is available, and the printed radius
#     condition holds at r = 6.63e-4.
#
# Floating point (BigFloat) proposes L, d and the square roots; every inequality
# is then checked exactly here and again by the kernel.
include(joinpath(@__DIR__, "..", "..", "pipeline", "stages", "_bootstrap.jl"))
include(joinpath(@__DIR__, "multipliers.jl"))
include(joinpath(@__DIR__, "bernstein.jl"))
using .Bernstein
const AC = A16Certificate
const QQ = Rational{BigInt}
const OUT = joinpath(@__DIR__, "..", "ChiquipoliLean", "Generated", "RadiusPrinted.lean")

# --- brackets ------------------------------------------------------------------
const A = QQ(613, 625)                 # [clo, chi] of RootExists.lean
const B = QQ(980801, 1000000)
const CLO22 = QQ(9808007223804781715147, big(10)^22)   # cLo, cHi of SideLength.lean
const CHI22 = QQ(9808007223804781715148, big(10)^22)
const D16 = big(10)^16
const PLO = QQ(fld(numerator(CLO22) * D16, denominator(CLO22)), D16)
const PHI = QQ(cld(numerator(CHI22) * D16, denominator(CHI22)), D16)
@assert PLO <= CLO22 && CHI22 <= PHI && A <= PLO && PHI <= B
# ℓ = √(2 - 2c) on the tight bracket, to 10^-16
const PL1, PL2 = setprecision(BigFloat, 256) do
    (QQ(floor(BigInt, sqrt(BigFloat(2 - 2PHI)) * D16), D16),
     QQ(ceil(BigInt, sqrt(BigFloat(2 - 2PLO)) * D16), D16))
end
@assert PL1 > 0 && PL1^2 <= 2 - 2PHI && PL2^2 >= 2 - 2PLO
# ℓ on [clo, chi], for the Gram matrix (five digits keep its entries small)
const LU1 = QQ(19595, 100000)
const LU2 = QQ(19596, 100000)
@assert LU1^2 <= 2 - 2B && LU2^2 >= 2 - 2A

# --- the printed constants -----------------------------------------------------
const LAMP = QQ(9186, 100000)          # λ_min > 0.09186         (Prop 6.2(5))
const ALP = QQ(4004, 1000)             # ‖α‖₂ < 4.004            (Prop 6.2(5))
const SIGP = QQ(9119, 100000)          # s₃₀(B)² ≥ 0.09119       (Prop 6.2(7))
const ELL0 = QQ(1959, 10000)           # ℓ > 0.1959              (Prop 6.2(2))
const RAD = QQ(663, 10^6)              # r ≥ 6.63e-4             (Theorem 6.4)

# --- the Gram certificate constants ---------------------------------------------
const SIGHAT = QQ(919, 10000)
const MU = QQ(1, big(10)^12)
const LDEN = big(10)^18
const TT = QQ(1, 500)
# phR and radEps exactly as in gen_radius.jl
const S1 = QQ(1950112, 10^7)
const S2 = QQ(1950164, 10^7)
const DEN = big(10)^12

const ACTA = [0, 0, 0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 6, 7, 7]
const ACTB = [7, 8, 9, 9, 9, 10, 10, 11, 12, 13, 13, 13, 14, 14, 15]

Fc = QQ.(AC.Fc_poly())
XC = [QQ.(p) for p in AC._XC]
YC = [QQ.(p) for p in AC._YC]
active = AC.ACTIVE_EDGES
@assert [e[1] for e in active] == ACTA && [e[2] for e in active] == ACTB "active edges differ"
@assert active[3] == (0, 9) "the pinned multiplier is not λ_(0,9)"

lean_rat(q::QQ) = denominator(q) == 1 ?
    (numerator(q) < 0 ? "(-$(abs(numerator(q))))" : "$(numerator(q))") :
    (numerator(q) < 0 ? "(-$(abs(numerator(q)))/$(denominator(q)))" :
                        "($(numerator(q))/$(denominator(q)))")
real_lit(q::QQ) = "($(lean_rat(q)) : ℝ)"
floorq(x::QQ, d) = QQ(fld(numerator(x) * d, denominator(x)), d)
ceilq(x::QQ, d)  = QQ(cld(numerator(x) * d, denominator(x)), d)
roundq(x::QQ, d) = QQ(div(2 * numerator(x) * d + denominator(x), 2 * denominator(x)), d)

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

# --- the two witnesses -------------------------------------------------------------
W1 = Multipliers.exact_multipliers(XC, YC, Fc, active; pin_value = QQ[QQ(1, 375)])
M0 = Multipliers.exact_multipliers(XC, YC, Fc, active; pin_value = QQ[QQ(0)])
@assert W1 !== nothing && M0 !== nothing "multiplier solve failed"
@assert all(Multipliers.iszp, M0.residuals) "M0: stationarity residuals are not all zero"
sumα = reduce(Multipliers.padd, M0.y[1:16])
@assert Multipliers.iszp(Multipliers.padd(sumα, QQ[QQ(1)])) "M0: Σα is not identically -1"
Dp = [Multipliers.padd(W1.y[k], -M0.y[k]) for k in 1:31]
@assert Multipliers.ptrim(M0.y[16+3]) == QQ[QQ(0)] || Multipliers.iszp(M0.y[16+3])
@assert Multipliers.ptrim(W1.y[16+3]) == QQ[QQ(1, 375)]

# --- bounds on the tight bracket -----------------------------------------------------
γlo(p) = minimum(Bernstein.bern_coeffs(p, PLO, PHI))
γhi(p) = maximum(Bernstein.bern_coeffs(p, PLO, PHI))
const BD = big(10)^20
function lohi(p)
    length(Multipliers.ptrim(p)) <= 1 && (c0 = isempty(Multipliers.ptrim(p)) ? QQ(0) : Multipliers.ptrim(p)[1];
        return (c0 - QQ(1, BD), c0 + QQ(1, BD)))
    return (floorq(γlo(p), BD), ceilq(γhi(p), BD))
end
nAb = [lohi(M0.y[i]) for i in 1:16];  dAb = [lohi(Dp[i]) for i in 1:16]
nLb = [lohi(M0.y[16+m]) for m in 1:15]; dLb = [lohi(Dp[16+m]) for m in 1:15]
# λ^P_e = 16 nL/ℓ + 75 (mL - nL) ≥ 16 a/ℓ* + 75 b
lamstar(m) = nLb[m][1] >= 0 ? PL2 : PL1
lamlb = [16 * nLb[m][1] / lamstar(m) + 75 * dLb[m][1] for m in 1:15]
@assert all(>(LAMP), lamlb) "λ bound fails: $(Float64(minimum(lamlb)))"
println("certified min λ^P ≥ ", Float64(minimum(lamlb)), "  (printed 0.09186)")
# α^P_i = 16 nA + 75 ℓ (mA - nA) ∈ [Lo_i, Hi_i]
lstar_lo(i) = dAb[i][1] >= 0 ? PL1 : PL2
lstar_hi(i) = dAb[i][2] >= 0 ? PL2 : PL1
αLo = [floorq(16 * nAb[i][1] + 75 * lstar_lo(i) * dAb[i][1], DEN) for i in 1:16]
αHi = [ceilq(16 * nAb[i][2] + 75 * lstar_hi(i) * dAb[i][2], DEN) for i in 1:16]
@assert all(<(0), αHi) "some α^P is not certified negative"
αsq = sum(αLo[i]^2 for i in 1:16)
@assert αsq < ALP^2 "‖α‖₂² bound fails: $(Float64(αsq))"
println("certified ‖α^P‖₂² ≤ ", Float64(αsq), "  (printed 4.004² = ", Float64(ALP^2), ")")

# --- phR and radEps, exactly as gen_radius.jl ------------------------------------------
function bounds(p)
    γ = Bernstein.bern_coeffs(p, A, B)
    length(p) == 1 && return (p[1] - QQ(1, DEN), p[1] + QQ(1, DEN))
    return (floorq(minimum(γ), DEN), ceilq(maximum(γ), DEN))
end
xb = [bounds(XC[i+1]) for i in 0:15]
yb = [bounds(YC[i+1]) for i in 0:15]
xh = [roundq(((S1 + S2) / 2) * (xb[i+1][1] + xb[i+1][2]) / 2, DEN) for i in 0:15]
yh = [roundq((yb[i+1][1] + yb[i+1][2]) / 2, DEN) for i in 0:15]
errs = QQ[]
for i in 0:15
    (lo, hi) = xb[i+1]
    for v in (S1 * lo, S2 * lo, S1 * hi, S2 * hi); push!(errs, abs(v - xh[i+1])); end
    (ylo, yhi) = yb[i+1]
    push!(errs, abs(ylo - yh[i+1])); push!(errs, abs(yhi - yh[i+1]))
end
const EPS = ceilq(maximum(errs), big(10)^8)
@assert EPS == QQ(663, 50000000) "radEps differs from Generated/Radius.lean"

# --- the unit Jacobian at phR (34 × 33) -------------------------------------------------
P = [(xh[i+1], yh[i+1]) for i in 0:15]
C = [zeros(QQ, 33) for _ in 1:34]
for i in 0:15
    j = mod(i + 1, 16); r = C[i+1]
    dx = (P[j+1][1] - P[i+1][1]) / LU2; dy = (P[j+1][2] - P[i+1][2]) / LU2
    r[2j+1] += dx; r[2j+2] += dy; r[2i+1] -= dx; r[2i+2] -= dy; r[33] = -LU1 / LU2
end
for (m, (a, b)) in enumerate(active)
    r = C[16+m]
    dx = P[b+1][1] - P[a+1][1]; dy = P[b+1][2] - P[a+1][2]
    r[2b+1] += dx; r[2b+2] += dy; r[2a+1] -= dx; r[2a+2] -= dy
end
for i in 0:15
    C[32][2i+1] = 1 / (2LU2)
    C[33][2i+2] = 1 / (2LU2)
    C[34][2i+1] = -P[i+1][2] / (2LU2); C[34][2i+2] = P[i+1][1] / (2LU2)
end
G = [sum(C[r][i] * C[r][j] for r in 1:34) for i in 1:33, j in 1:33]
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
println("unit Gram: min pivot ", Float64(minimum(dq)), ", max residual row sum ", Float64(rowmax))

# --- the closing arithmetic ----------------------------------------------------------------
const C0 = 1 / (4 * LU2^2) - QQ(1, 4)
const KU = QQ(2080) / 4 + C0 * 160
availU = (1 - TT) * (SIGHAT - MU) - (1 // TT - 1) * KU * EPS^2
@assert SIGP <= availU "σ² = 0.09119 exceeds what the certificate gives, $(Float64(availU))"
@assert SIGP <= (1 - TT) * (SIGHAT - MU)
@assert 4 * RAD^2 * (LAMP + ALP)^2 <= SIGP * ELL0^2 * LAMP^2 "printed radius condition fails"
println("σ² available ", Float64(availU), "; printed radius condition slack ",
        Float64(SIGP * ELL0^2 * LAMP^2 / (4 * RAD^2 * (LAMP + ALP)^2)))

# --- emit ------------------------------------------------------------------------------------
io = IOBuffer()
mat_lit(rows) = "!![" * join([join(lean_rat.(r), ", ") for r in rows], ";\n    ") * "]"
rows_of(M) = [M[i, :] for i in 1:size(M, 1)]
LU1s = real_lit(LU1); LU2s = real_lit(LU2)
print(io, """/-
AUTO-GENERATED by `lean/generators/gen_radius_printed.jl` — do not edit by hand.

**The numerical certificate of Theorem 6.4 with the printed constants.**

`Theory/RadiusPrinted.lean` proves the printed argument of Theorem 6.4 from the
printed constants. This file supplies, with exact rational data only:

  * a second multiplier witness `nA*`, `nL*` (squared normalisation, pinned at
    `λ_(0,9) = 0`) with its stationarity identities `ngradx_k`, `ngrady_k` and
    `nalpha_sum`; with the witness `mA*`, `mL*` of `Generated/Multipliers.lean`
    (pinned at `1/375`) it gives the article's representative (Table S2);
  * Bernstein bounds for `nA*`, `nL*` and `mA* − nA*`, `mL* − nL*` on
    `[prLo, prHi]`, a bracket of width `10⁻¹⁶` containing the `10⁻²²` root
    bracket `[cLo, cHi]`, and from them `lamP_lb_*` (every printed-normalisation
    diameter multiplier exceeds `$(Float64(LAMP))`) and `alphaP_sq`
    (`‖α‖₂² < $(Float64(ALP))²`);
  * the rational matrix `ChatU` of the unit Jacobian `D(e,d)` at `phR`, with `ℓ`
    replaced by `$(Float64(LU1)) ≤ ℓ ≤ $(Float64(LU2))`, stacked with the rigid
    motions, and an `LDLᵀ` certificate of `ChatUᵀChatU − ($(lean_rat(SIGHAT)))·Id`
    (`gram_rowsU`, by `decide +kernel`), giving `QhatU_lower`;
  * `coerU_arith` and `printed_rad_arith`, the closing arithmetic.

Certified here (exact): min λ ≥ $(round(Float64(minimum(lamlb)), digits=10)),
‖α‖₂² ≤ $(round(Float64(αsq), digits=8)), σ² available $(round(Float64(availU), digits=6)).
-/
import ChiquipoliLean.Generated.Radius
import ChiquipoliLean.Theory.RadiusPrinted

namespace Chiquipoli

open Chiquipoli.FirstOrder Chiquipoli.Feasible

/-! ## Constants -/

/-- A bracket of width `10⁻¹⁶` containing the root bracket `[cLo, cHi]`. -/
noncomputable def prLo : ℝ := $(lean_rat(PLO))
noncomputable def prHi : ℝ := $(lean_rat(PHI))
/-- `ℓ = √(2 − 2c)` on `[prLo, prHi]` lies in `[prL1, prL2]`. -/
noncomputable def prL1 : ℝ := $(lean_rat(PL1))
noncomputable def prL2 : ℝ := $(lean_rat(PL2))

lemma prL1_sq : prL1 ^ 2 ≤ 2 - 2 * prHi := by unfold prL1 prHi; norm_num
lemma prL2_sq : 2 - 2 * prLo ≤ prL2 ^ 2 := by unfold prL2 prLo; norm_num
lemma prL1_pos : 0 < prL1 := by unfold prL1; norm_num
lemma prL2_pos : 0 < prL2 := by unfold prL2; norm_num

/-! ## The second witness (pinned at `λ_(0,9) = 0`) -/

""")
aname(i) = "nA$i"; lname(m) = "nL$(m-1)"
for i in 1:16
    print(io, "/-- Side multiplier of the second witness, side `($(i-1), $(mod(i,16)))`. -/\n",
          "noncomputable def $(aname(i-1)) (c : ℝ) : ℝ := $(horner(M0.y[i]))\n\n")
end
for m in 1:15
    (i, j) = active[m]
    print(io, "/-- Diameter multiplier of the second witness, pair `($i, $j)`. -/\n",
          "noncomputable def $(lname(m)) (c : ℝ) : ℝ := $(horner(M0.y[16+m]))\n\n")
end
print(io, """/-- The `t`-direction equation of the second witness. -/
theorem nalpha_sum (c : ℝ) :
    $(join([aname(i) * " c" for i in 0:15], " + ")) = -1 := by
  simp only [$(join([aname(i) for i in 0:15], ", "))]; ring

""")
cons = Tuple{Int,Int,String}[]
for i in 0:15; push!(cons, (i, mod(i + 1, 16), aname(i))); end
for m in 1:15; (i, j) = active[m]; push!(cons, (i, j, lname(m))); end
for k in 0:15
    terms = String[]
    for (a, b, nm) in cons
        if k == a
            push!(terms, "-$nm (Real.cos z) * ((p$b z).%C - (p$a z).%C)")
        elseif k == b
            push!(terms, "$nm (Real.cos z) * ((p$b z).%C - (p$a z).%C)")
        end
    end
    for (comp, lbl, vrow) in ((1, "x", 2k + 1), (2, "y", 2k + 2))
        body = join(replace.(terms, "%C" => string(comp)), " +\n      ")
        reds = sort(unique(vcat([a for (a, b, _) in cons if k == a || k == b],
                                [b for (a, b, _) in cons if k == a || k == b])))
        unf = join(["red$v" for v in reds], ", ")
        mults = join(unique([nm for (a, b, nm) in cons if k == a || k == b]), ", ")
        xcs = join(vcat(["XC$v" for v in reds], ["YC$v" for v in reds]), ", ")
        qexpr = horner(M0.quot[vrow], "Real.cos z")
        coeff = comp == 1 ? "(Real.sin z * ($qexpr))" : "($qexpr)"
        print(io, """/-- Stationarity of the second witness at vertex $k, $lbl-component. -/
theorem ngrad$(lbl)_$k (z : ℝ) (hF : Ffun z = 0) :
    $body = 0 := by
  have hc : Fc (Real.cos z) = 0 := by rw [Fc_cos_eq_Ffun]; exact hF
  simp only [Fc] at hc
  rw [$unf]
  simp only [$mults, $xcs]
  linear_combination $coeff * hc

""")
    end
end

print(io, "/-! ## Bernstein bounds on `[prLo, prHi]` -/\n\n")
bl(name, expr, p, m, unf) = print(io, Bernstein.lean_lower_bound_lemma(name, expr, p, PLO, PHI;
    m = m, lo = "prLo", hi = "prHi", unfolds = unf), "\n")
for i in 0:15
    bl("nA$(i)_lo", "nA$(i) c", M0.y[i+1], nAb[i+1][1], " nA$i")
    bl("nA$(i)_hi", "(-nA$(i) c)", -M0.y[i+1], -nAb[i+1][2], " nA$i")
    bl("dA$(i)_lo", "(mA$(i) c - nA$(i) c)", Dp[i+1], dAb[i+1][1], " mA$i nA$i")
    bl("dA$(i)_hi", "(-(mA$(i) c - nA$(i) c))", -Dp[i+1], -dAb[i+1][2], " mA$i nA$i")
end
for m in 0:14
    bl("nL$(m)_lo", "nL$(m) c", M0.y[17+m], nLb[m+1][1], " nL$m")
    bl("dL$(m)_lo", "(mL$(m) c - nL$(m) c)", Dp[17+m], dLb[m+1][1], " mL$m nL$m")
end

print(io, "/-! ## The article's multipliers: `λ > $(Float64(LAMP))`, `‖α‖₂ < $(Float64(ALP))` -/\n\n")
for m in 0:14
    a = nLb[m+1][1]; pos = a >= 0
    lst = pos ? "prL2" : "prL1"
    step = pos ?
        "div_lb_pos (a := 16 * $(real_lit(a))) (W := 16 * nL$(m) c) (by norm_num) (by linarith) hl hl2" :
        "div_lb_neg (a := 16 * $(real_lit(a))) (W := 16 * nL$(m) c) (by norm_num) (by linarith) prL1_pos hl1"
    print(io, """/-- The article's multiplier on the diameter `$(active[m+1])` exceeds `$(Float64(LAMP))`. -/
lemma lamP_lb_$(m) (c l : ℝ) (h₁ : prLo ≤ c) (h₂ : c ≤ prHi) (hl1 : prL1 ≤ l) (hl2 : l ≤ prL2) :
    $(real_lit(LAMP)) < 16 * nL$(m) c / l + 75 * (mL$(m) c - nL$(m) c) := by
  have ha := nL$(m)_lo c h₁ h₂
  have hb := dL$(m)_lo c h₁ h₂
  have hl : 0 < l := lt_of_lt_of_le prL1_pos hl1
  have hq := $step
  have hn : $(real_lit(LAMP)) < 16 * $(real_lit(a)) / $lst + 75 * $(real_lit(dLb[m+1][1])) := by
    unfold $lst; norm_num
  linarith

""")
end
for i in 0:15
    llo = lstar_lo(i+1) == PL1 ? "prL1" : "prL2"
    lhi = lstar_hi(i+1) == PL1 ? "prL1" : "prL2"
    print(io, """/-- The article's side multiplier `α_$i` lies in `[$(Float64(αLo[i+1])), $(Float64(αHi[i+1]))]`. -/
lemma alphaP_bd_$(i) (c l : ℝ) (h₁ : prLo ≤ c) (h₂ : c ≤ prHi) (hl1 : prL1 ≤ l) (hl2 : l ≤ prL2) :
    $(real_lit(αLo[i+1])) ≤ 16 * nA$(i) c + 75 * (l * (mA$(i) c - nA$(i) c)) ∧
      16 * nA$(i) c + 75 * (l * (mA$(i) c - nA$(i) c)) ≤ $(real_lit(αHi[i+1])) := by
  have h1 := nA$(i)_lo c h₁ h₂
  have h2 := nA$(i)_hi c h₁ h₂
  have h3 := dA$(i)_lo c h₁ h₂
  have h4 := dA$(i)_hi c h₁ h₂
  have hl : 0 < l := lt_of_lt_of_le prL1_pos hl1
  have k1 := mul_lb (d := mA$(i) c - nA$(i) c) (dlo := $(real_lit(dAb[i+1][1]))) (lstar := $llo)
    h3 hl (by nlinarith)
  have k2 := mul_ub (d := mA$(i) c - nA$(i) c) (dhi := $(real_lit(dAb[i+1][2]))) (lstar := $lhi)
    (by linarith) hl (by nlinarith)
  constructor
  · have : $(real_lit(αLo[i+1])) ≤ 16 * $(real_lit(nAb[i+1][1])) + 75 * ($llo * $(real_lit(dAb[i+1][1]))) := by
      unfold $llo; norm_num
    linarith
  · have : 16 * $(real_lit(nAb[i+1][2])) + 75 * ($lhi * $(real_lit(dAb[i+1][2]))) ≤ $(real_lit(αHi[i+1])) := by
      unfold $lhi; norm_num
    linarith

""")
end
xs = ["(16 * nA$(i) c + 75 * (l * (mA$(i) c - nA$(i) c)))" for i in 0:15]
print(io, """/-- `‖α‖₂² < $(Float64(ALP))²` for the article's side multipliers. -/
theorem alphaP_sq (c l : ℝ) (h₁ : prLo ≤ c) (h₂ : c ≤ prHi) (hl1 : prL1 ≤ l) (hl2 : l ≤ prL2) :
    $(join([x * " ^ 2" for x in xs], " +\n      ")) < $(real_lit(ALP)) ^ 2 := by
$(join(["  have b$i := alphaP_bd_$i c l h₁ h₂ hl1 hl2\n" *
        "  have s$i : $(xs[i+1]) ^ 2 ≤ $(real_lit(-αLo[i+1])) ^ 2 :=\n" *
        "    sq_le_sq' (by linarith [b$i.1]) (by linarith [b$i.2])" for i in 0:15], "\n"))
  have hsum : $(join([real_lit(-αLo[i+1]) * " ^ 2" for i in 0:15], " + ")) < $(real_lit(ALP)) ^ 2 := by
    norm_num
  exact lt_of_le_of_lt $(foldl((acc, i) -> "(add_le_add $acc s$i)", 1:15; init = "s0")) hsum

""")

function row_rhs(k)
    k < 16 && return "(1 / (2 * $LU2s)) * Feasible.sideRow phR v (2 * $LU1s * y) $k"
    k < 31 && return "(1 / 2) * Feasible.diamRow phR radA radB v $(k - 16)"
    k == 31 && return "(1 / (2 * $LU2s)) * ∑ i, (v i).1"
    k == 32 && return "(1 / (2 * $LU2s)) * ∑ i, (v i).2"
    return "(1 / (2 * $LU2s)) * ∑ i, ip (v i) (J (phR i))"
end
function row_proof(k)
    k < 16 && return "  simp [Fin.sum_univ_succ, ChatU, flat, Feasible.sideRow, phR, ip]\n  ring"
    k < 31 && return "  simp [Fin.sum_univ_succ, ChatU, flat, Feasible.diamRow, phR, ip, radA, radB]\n  ring"
    k < 33 && return "  rw [sum16r]\n  simp [Fin.sum_univ_succ, ChatU, flat]\n  ring"
    return "  rw [sum16r]\n  simp [Fin.sum_univ_succ, ChatU, flat, phR, ip, J]\n  ring"
end
print(io, """/-! ## The unit Jacobian at `phR`: the Gram certificate -/

/-- No diameters: indexes the side-and-rigid-motion part of `Qform`. -/
def prE0 : Fin 0 → Fin 16 := ![]

/-- Rows: the 16 sides `⟪Δp̂ᵢ/LU2, Δvᵢ⟫ − (LU1/LU2) y`, the 15 active diameters
`⟪Δp̂_e, Δv_e⟫`, and the two translations and the rotation scaled by `1/(2 LU2)`;
columns: `x₀, y₀, …, x₁₅, y₁₅, y`. -/
def ChatU : Fin 34 → Fin 33 → ℚ :=
  $(mat_lit(C))

/-- Proposed `L` of the `LDLᵀ` factorisation (exact rationals). -/
def LqU : Fin 33 → Fin 33 → ℚ :=
  $(mat_lit(rows_of(Lq)))

/-- Proposed diagonal `d` of the `LDLᵀ` factorisation. -/
def dqU : Fin 33 → ℚ :=
  ![$(join(lean_rat.(dq), ", "))]

theorem dqU_nonneg : ∀ k, 0 ≤ dqU k := by decide +kernel

/-- **The kernel check.** Every absolute row sum of the exact residual
`ChatUᵀChatU − ($(lean_rat(SIGHAT)))·Id − LqU·diag(dqU)·LqUᵀ` is at most `$(lean_rat(MU))`. -/
theorem gram_rowsU :
    ∀ i, ∑ j, |gramResidual ChatU LqU dqU ($(lean_rat(SIGHAT))) i j| ≤ $(lean_rat(MU)) := by
  decide +kernel

""")
for k in 0:33
    print(io, """lemma chatU_row_$(k) (v : Fin 16 → ℝ × ℝ) (y : ℝ) :
    ∑ i, (ChatU $(k) i : ℝ) * flat v y i = $(row_rhs(k)) := by
$(row_proof(k))

""")
end
print(io, """/-- The unit form at `phR`: a quarter of the full `Qform` plus a multiple of
its side-and-rigid part, in the variable `dt = 2·LU1·y`. -/
theorem QhatU_eq (v : Fin 16 → ℝ × ℝ) (y : ℝ) :
    (1 / 4) * Qform phR radA radB v (2 * $LU1s * y)
      + (1 / (4 * $LU2s ^ 2) - 1 / 4) * Qform phR prE0 prE0 v (2 * $LU1s * y)
      = ∑ k, (∑ i, (ChatU k i : ℝ) * flat v y i) ^ 2 := by
  rw [Qform, Qform, sum16r (fun i => Feasible.sideRow phR v (2 * $LU1s * y) i ^ 2),
    sum15r (fun e => Feasible.diamRow phR radA radB v e ^ 2), Fin.sum_univ_zero,
    sum34r (fun k => (∑ i, (ChatU k i : ℝ) * flat v y i) ^ 2)]
  rw [$(join(["chatU_row_$k" for k in 0:33], ", "))]
  ring

/-- **The Gram bound at `phR` for the unit Jacobian.** -/
theorem QhatU_lower (v : Fin 16 → ℝ × ℝ) (y : ℝ) :
    (($(lean_rat(SIGHAT)) - $(lean_rat(MU)) : ℚ) : ℝ) * (cip v v + y ^ 2) ≤
      (1 / 4) * Qform phR radA radB v (2 * $LU1s * y)
        + (1 / (4 * $LU2s ^ 2) - 1 / 4) * Qform phR prE0 prE0 v (2 * $LU1s * y) := by
  have h := gram_lower ChatU LqU dqU ($(lean_rat(SIGHAT))) ($(lean_rat(MU))) dqU_nonneg gram_rowsU (flat v y)
  rw [flat_sq] at h
  rw [QhatU_eq]
  exact h

/-! ## The closing arithmetic -/

/-- The coefficient left after perturbing from `phR` to `A16` (with
`Qform_perturb` at `t = $(lean_rat(TT))`, `K = 2080` with diameters and `160` without)
still exceeds the printed `σ² = $(Float64(SIGP))`. -/
lemma coerU_arith :
    $(real_lit(SIGP)) ≤ (1 - $(real_lit(TT))) * ((($(lean_rat(SIGHAT)) - $(lean_rat(MU)) : ℚ) : ℝ))
      - (1 / $(real_lit(TT)) - 1) * ((1 / 4) * 2080 + (1 / (4 * $LU2s ^ 2) - 1 / 4) * 160) * radEps ^ 2 := by
  unfold radEps; norm_num

lemma coerU_arith_eta :
    $(real_lit(SIGP)) ≤ (1 - $(real_lit(TT))) * ((($(lean_rat(SIGHAT)) - $(lean_rat(MU)) : ℚ) : ℝ)) := by
  norm_num

/-- **The printed radius condition.** `r = 6.63·10⁻⁴` satisfies
`r ≤ σℓ₀/(2(1 + ‖α‖₂/λ_min))` with the printed `σ² = 0.09119`, `ℓ₀ = 0.1959`,
`‖α‖₂ = 4.004`, `λ_min = 0.09186`, in the squared form
`4 r² (λ_min + ‖α‖₂)² ≤ σ² ℓ₀² λ_min²`. -/
lemma printed_rad_arith :
    4 * $(real_lit(RAD)) ^ 2 * ($(real_lit(LAMP)) + $(real_lit(ALP))) ^ 2
      ≤ $(real_lit(SIGP)) * $(real_lit(ELL0)) ^ 2 * $(real_lit(LAMP)) ^ 2 := by
  norm_num

end Chiquipoli
""")
open(OUT, "w") do f
    write(f, String(take!(io)))
end
println("wrote ", OUT)
