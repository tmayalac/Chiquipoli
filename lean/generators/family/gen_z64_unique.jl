# Unique.lean of Z64 — the root of G is the only one in (0, π/64] at which the polygon exists.
#
# Included by gen_z64.jl (it shares its helpers and its enclosure calculus `En`). Written before any
# Lean: every number and every inequality is first checked here in exact rational arithmetic.
#
# THE ARGUMENT. Write a = sn·X51 + 1/2 (X51 = pl1), so that rad = pl3 − a² and G = x² + w² − pl3
# with x = a + sn·pl4 − c, w = pl5 − sn − rr, rr = √rad. On [slo, 1), slo < cos(π/64):
#
#   (1) a' = N / sn with N = −c·pl1 + (1 − c²)·pl1' a polynomial, and N > 0 there (Taylor pieces);
#       a(slo) > 0 (a point); hence a > 0 and a' > 0 on [slo, 1).
#   (2) rad' = −2 − 2 a a' < 0: rad is strictly decreasing, and rad(cB) < 0 at a point cB
#       just above the end of the region where the polygon exists. So {rad ≥ 0} ∩ [slo, 1] is
#       an interval [slo, c0] with c0 < cB.
#   (3) On it G' = α − w·rad'/rr, with α = 2x·x' + 2w·(pl5' + c/sn) + 2. The second term is ≥ 0
#       (w ≥ 0, rad' < 0, rr > 0), and α > 0 by centred enclosures on sub-brackets of [slo, cB].
#
# So G is strictly increasing on {rad ≥ 0} ∩ [slo, 1) and has at most one root there.

@assert (IX51, IE2, IU29, IT29) == (1, 3, 4, 5) "the Lean names pl1, pl3, pl4, pl5 are used below"
@assert IYF == 2

# ---- polynomial helpers (ascending coefficients) -------------------------------------
pdd(a, b) = (m = max(length(a), length(b)); [(i <= length(a) ? a[i] : QQ(0)) + (i <= length(b) ? b[i] : QQ(0)) for i in 1:m])
pscl(k, a) = [k * x for x in a]
pmu(a, b) = (r = zeros(QQ, length(a) + length(b) - 1); for i in eachindex(a), j in eachindex(b); r[i+j-1] += a[i] * b[j]; end; r)
pdv(a) = QQ[(k - 1) * a[k] for k in 2:length(a)]                       # derivative
pev(a, x) = foldr((c, acc) -> c + x * acc, a; init = zero(x))        # Horner, any number type

UP1 = PLLIST[1]; UP3 = PLLIST[3]; UP4 = PLLIST[4]; UP5 = PLLIST[5]
UdP1 = pdv(UP1); UdP4 = pdv(UP4); UdP5 = pdv(UP5)
NV = ptrim(pdd(pscl(QQ(-1), pmu(QQ[0, 1], UP1)), pmu(QQ[1, 0, -1], UdP1)))   # N = −c·UP1 + (1 − c²)·UP1'

# ---- cos(π/64), through Mathlib's nested radical ----------------------------------------
UK = Int(log2(n)) - 1
UGS = big(10)^24
ulvl_lo = QQ[]; ulvl_hi = QQ[]
let lo = QQ(0), hi = QQ(0)
    for j in 1:UK
        l_ = QQ(floor(BigInt, sqrt(BigFloat(2 + lo)) * UGS), UGS)
        u_ = QQ(ceil(BigInt, sqrt(BigFloat(2 + hi)) * UGS), UGS)
        @assert l_^2 < 2 + lo && u_^2 > 2 + hi
        push!(ulvl_lo, l_); push!(ulvl_hi, u_); lo, hi = l_, u_
    end
end
UCOS_LO = ulvl_lo[end] / 2; UCOS_HI = ulvl_hi[end] / 2                  # bounds on cos(π/64)
SLO = UCOS_LO
guard(UCOS_HI <= CLO, "the certified bracket does not lie above cos(π/64)")

# ---- numerics in BigFloat, to choose the points --------------------------------------
unum(p, c) = pev(BigFloat.(p), BigFloat(c))
aa_num(c) = sqrt(1 - BigFloat(c)^2) * unum(UP1, c) + BigFloat(1) / 2
rad_num(c) = unum(UP3, c) - aa_num(c)^2
guard(rad_num(SLO) > 0, "rad(slo) is not positive")
guard(aa_num(SLO) > 0, "a(slo) is not positive")
guard(rad_num(CHI) > 0, "rad(chi) is not positive")
# the end c0 of the region where the polygon exists: rad(c0) = 0, bisected on (chi, 1)
C0END = let lo = BigFloat(CHI), hi = BigFloat(1) - big"1e-6"
    @assert rad_num(hi) < 0
    for _ in 1:300; m = (lo + hi) / 2; rad_num(m) > 0 ? (lo = m) : (hi = m); end
    hi
end
UCB = simplest(C0END + big"1e-6", C0END + big"2e-6")                       # a little above c0
guard(UCB < 1 && UCB > CHI && rad_num(UCB) < 0, "cB is not past the end of the region")
println("  Z64 uniqueness: slo = $(Float64(SLO)) < cos(π/64); the polygon exists up to c0 = $(Float64(C0END)); cB = $(Float64(UCB))")

# ---- pieces ----------------------------------------------------------------------------------
# A split of [lo, hi] into K pieces with simple rational breakpoints.
function usplit(lo::QQ, hi::QQ, K)
    brk = QQ[lo]
    for k in 1:K-1
        x = lo + (hi - lo) * k // K; d = (hi - lo) / (8K)
        push!(brk, simplest(x - d, x + d))
    end
    push!(brk, hi)
    @assert issorted(brk) && length(unique(brk)) == K + 1
    brk
end
piece_centre(a, b) = (c = simplest((a + b) / 2 - (b - a) / 16, (a + b) / 2 + (b - a) / 16); (c, max(c - a, b - c)))
# enclosure of a polynomial on a piece: centre (rounded) and radius (centred Taylor bound)
function upenc(p, ck, rk)
    t = taylor(p, ck); ctr = rnd(t[1])
    (ctr, rup(abs(t[1] - ctr) + (length(t) > 1 ? sum(abs(t[j+1]) * rk^j for j in 1:length(t)-1) : QQ(0))))
end

# ---- (1) N > 0 on [slo, 1] ---------------------------------------------------------------------
UNP = nothing
for K in (1, 2, 4, 8, 16, 32, 64)
    brk = usplit(SLO, QQ(1), K); ok = true; worst = QQ(1)
    for k in 1:K
        a, b = brk[k], brk[k+1]; ck, rk = piece_centre(a, b)
        t = taylor(NV, ck); lb = t[1] - sum(abs(t[j+1]) * rk^j for j in 1:length(t)-1)
        lb > 0 || (ok = false; break); worst = min(worst, lb)
    end
    if ok; global UNP = (K = K, brk = brk, worst = worst); break; end
end
guard(UNP !== nothing, "N is not certified positive on [slo, 1]")
UNLB = QQ(floor(BigInt, UNP.worst * 9 / 10 * big(10)^6), big(10)^6)           # a rounded-down lower bound, 9/10 of the worst
guard(UNLB > 0, "the lower bound of N is not positive")
println("  N > 0 on [slo, 1] in $(UNP.K) pieces, N ≥ $(Float64(UNLB))")

# ---- (3) α > 0 and w ≥ 0 on [slo, cB], on pieces -------------------------------------------------
TWO = En("(2 : ℝ)", QQ(2), QQ(0), "(show |((2 : ℝ)) - 2| ≤ 0 by norm_num)")
ONE = En("(1 : ℝ)", QQ(1), QQ(0), "(show |((1 : ℝ)) - 1| ≤ 0 by norm_num)")
# the tree of α, for the pieces; leaves are named by piece
function alpha_tree(k, pc, ps, pol, dpol, prr)
    Lc = En("c", pc[1], pc[2], "(show |c - $(lr(pc[1]))| ≤ $(lr(pc[2])) by have h := near$k c h₁ h₂; unfold cs$k rs$k at h; exact h)")
    Ls = En("sn c", ps[1], ps[2], "(enc_sn$k c h₁ h₂)")
    Lp(i) = En("pl$i c", pol[i][1], pol[i][2], "(encq$(k)_pl$i c h₁ h₂)")
    Ld(i) = En("dpl$i c", dpol[i][1], dpol[i][2], "(encq$(k)_dpl$i c h₁ h₂)")
    Lrr = En("rr c", prr[1], prr[2], "(rr_close$k c h₁ h₂ hrad)")
    a = eadd(emul(Ls, Lp(1)), HALF)
    x = esub(eadd(a, emul(Ls, Lp(4))), Lc)
    q = ediv(Lc, Ls)
    da = eadd(emul(eneg(q), Lp(1)), emul(Ls, Ld(1)))
    dx = esub(eadd(eadd(da, emul(eneg(q), Lp(4))), emul(Ls, Ld(4))), ONE)
    w = esub(esub(Lp(5), Ls), Lrr)
    q5 = eadd(Ld(5), q)
    al = eadd(eadd(emul(emul(TWO, x), dx), emul(emul(TWO, w), q5)), TWO)
    (alpha = al, w = w, x = x, dx = dx, q5 = q5, Lc = Lc, Ls = Ls, Lp = Lp, Ld = Ld, Lrr = Lrr)
end
function build_piece(k, a, b)
    ck, rk = piece_centre(a, b)
    s0 = rnd(sqrt(BigFloat(1 - ck^2)))
    esq_e = rk * (2 * abs(ck) + rk) + abs((1 - ck^2) - s0^2)
    ps = (s0, rup(esq_e / s0), esq_e)
    pol = Dict(1 => upenc(UP1, ck, rk), 3 => upenc(UP3, ck, rk), 4 => upenc(UP4, ck, rk), 5 => upenc(UP5, ck, rk))
    dpol = Dict(1 => upenc(UdP1, ck, rk), 4 => upenc(UdP4, ck, rk), 5 => upenc(UdP5, ck, rk))
    # the radicand on the piece, by the same tree as the Lean definition of rad
    Ls = En("sn c", ps[1], ps[2], "(enc_sn$k c h₁ h₂)")
    Lp(i) = En("pl$i c", pol[i][1], pol[i][2], "(encq$(k)_pl$i c h₁ h₂)")
    rad = esub(Lp(3), emul(eadd(emul(Ls, Lp(1)), HALF), eadd(emul(Ls, Lp(1)), HALF)))
    rhi = rad.c + rad.r
    mm = rup(sqrt(BigFloat(max(rhi, QQ(1, 10^12)))))                      # (2m)^2 ≥ rad_hi, with 2m = mm
    m = mm / 2
    prr = (m, m)
    tr = alpha_tree(k, (ck, rk), ps, pol, dpol, prr)
    (k = k, a = a, b = b, ck = ck, rk = rk, ps = ps, pol = pol, dpol = dpol, rad = rad, rhi = rhi, m = m, prr = prr, tr = tr)
end
UAP = nothing
for K in (1, 2, 4, 8, 16, 32, 64)
    brk = usplit(SLO, UCB, K); pcs = [build_piece(k, brk[k], brk[k+1]) for k in 1:K]
    okk = all(p -> p.tr.alpha.c - p.tr.alpha.r > 0 && p.tr.w.c - p.tr.w.r > 0, pcs)
    if okk; global UAP = (K = K, brk = brk, pcs = pcs); break; end
end
guard(UAP !== nothing, "α > 0 and w ≥ 0 are not certified on [slo, cB]")
println("  α > 0, w ≥ 0 on [slo, cB] in $(UAP.K) pieces; worst α ≥ $(Float64(minimum(p.tr.alpha.c - p.tr.alpha.r for p in UAP.pcs))), worst w ≥ $(Float64(minimum(p.tr.w.c - p.tr.w.r for p in UAP.pcs)))")

# =====================================================================================
# Lean emission
# =====================================================================================
deriv_chain_u(p) = begin
    p = QQ.(ptrim(p)); d = length(p) - 1
    t = "((hasDerivAt_id' (x := c)).const_mul ($(lr(p[d+1])) : ℝ))"
    p[d] != 0 && (t = "($t.add_const ($(lr(p[d])) : ℝ))")
    for k in d-2:-1:0
        t = "($t.mul (hasDerivAt_id' (x := c)))"
        p[k+1] != 0 && (t = "($t.add_const ($(lr(p[k+1])) : ℝ))")
    end
    t
end
uEk(j) = j == 1 ? "√2" : "√(2 + $(uEk(j-1)))"
function upoint(cpt, cname)
    Lp(idx) = (v = peval(PLLIST[idx], cpt); En("pl$idx $cname", v, QQ(0), "(show |pl$idx $cname - $(lr(v))| ≤ 0 by unfold pl$idx $cname; norm_num)"))
    s0 = rnd(sqrt(BigFloat(1 - cpt^2)))
    Esq = abs((1 - cpt^2) - s0^2)
    Ls = En("sn $cname", s0, rup(Esq / s0), "(enc_sn_$cname)")
    (Lp = Lp, s0 = s0, Esq = Esq, Ls = Ls)
end
upc_slo = upoint(SLO, "slo"); upc_cB = upoint(UCB, "cB")
aa_slo = eadd(emul(upc_slo.Ls, upc_slo.Lp(1)), HALF)
guard(aa_slo.c - aa_slo.r > 0, "a(slo) is not enclosed above zero")
rad_cB = radtree(upc_cB.Lp, upc_cB.Ls)
guard(rad_cB.c + rad_cB.r < 0, "rad(cB) is not enclosed below zero")

# a lemma `name : |pn c − ctr| ≤ rad` on a piece, from a centred Taylor expansion
function piece_enc(name, pn, p, ck, rk, cs, rs, near, lo, hi, ctr, rad; formula = pn)
    t, deg, rhs, steps, tl = taylor_steps(pn, p; cn = cs, rn = rs, C = ck, R = rk)
    guard(abs(t[1] - ctr) + (deg == 0 ? QQ(0) : sum(abs(t[j+1]) * rk^j for j in 1:deg)) <= rad, "the enclosure $name does not hold")
    if deg == 0
        return "lemma $name (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |$pn c - $(lr(ctr))| ≤ $(lr(rad)) := by\n  unfold $pn; norm_num\n"
    end
    """
lemma $name (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |$pn c - $(lr(ctr))| ≤ $(lr(rad)) := by
  have key : $pn c = $rhs := by
    unfold $pn $cs; ring
  have hr : |c - $cs| ≤ $rs := $near c h₁ h₂
$steps
  have hnum : |($(lr(t[1])) : ℝ) - $(lr(ctr))| + ($tl) ≤ $(lr(rad)) := by
    unfold $rs; norm_num
  have e1 := neg_abs_le (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  have e2 := le_abs_self (($(lr(t[1])) : ℝ) - $(lr(ctr)))
  rw [key, abs_le]
  constructor <;> linarith
"""
end

UNAME_LO(k) = k == 1 ? "slo" : "ub$(k-1)"
UNAME_HI(k, K) = k == K ? "cB" : "ub$k"
NNAME_LO(k, K) = k == 1 ? "slo" : "nb$(k-1)"
NNAME_HI(k, K) = k == K ? "1" : "nb$k"
global buf = IOBuffer()
print(buf, header("""**Z$n: the root is unique in the search interval `(0, π/$n]`, at the polygons that exist.** With
`a = sn·pl1 + 1/2` the radicand is `rad = pl3 − a²` and `G = x² + w² − pl3` (`x = a + sn·pl4 − c`,
`w = pl5 − sn − rr`). On `[slo, 1)` (`slo < cos(π/$n)`): `a' = N / sn` with `N` a polynomial, positive
by a centred Taylor bound; `a(slo) > 0`; so `a > 0`, `a' > 0`, and `rad' = −2 − 2 a a' < 0`: `rad` is
strictly decreasing, negative at a point `cB` past the end of the region where the polygon exists.
Where `rad > 0`, `G' = α − w·rad'/rr` with `α > 0` by centred enclosures on sub-brackets and the
second term `≥ 0`. Hence `G` is strictly increasing on `{rad ≥ 0} ∩ [slo, 1)`.""",
    [prev, "Mathlib.Analysis.SpecialFunctions.Sqrt", "Mathlib.Analysis.Calculus.Deriv.MeanValue"]))
println(buf, """
open Set Real

noncomputable def slo : ℝ := $(lr(SLO))
noncomputable def cB : ℝ := $(lr(UCB))
$(join(["noncomputable def ub$j : ℝ := $(lr(UAP.brk[j+1]))" for j in 1:UAP.K-1], "\n"))
$(join(["noncomputable def nb$j : ℝ := $(lr(UNP.brk[j+1]))" for j in 1:UNP.K-1], "\n"))
""")
for pc in UAP.pcs
    k = pc.k
    println(buf, "noncomputable def cs$k : ℝ := $(lr(pc.ck))\nnoncomputable def rs$k : ℝ := $(lr(pc.rk))")
end
for k in 1:UNP.K
    ck, rk = piece_centre(UNP.brk[k], UNP.brk[k+1])
    println(buf, "noncomputable def ncs$k : ℝ := $(lr(ck))\nnoncomputable def nrs$k : ℝ := $(lr(rk))")
end
println(buf)
for pc in UAP.pcs
    k = pc.k; lo = UNAME_LO(k); hi = UNAME_HI(k, UAP.K)
    println(buf, "lemma near$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |c - cs$k| ≤ rs$k :=\n  near_of (by unfold cs$k rs$k $lo; norm_num) (by unfold cs$k rs$k $hi; norm_num) h₁ h₂\n")
end
for k in 1:UNP.K
    lo = NNAME_LO(k, UNP.K); hi = NNAME_HI(k, UNP.K)
    println(buf, "lemma nnear$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |c - ncs$k| ≤ nrs$k :=\n  near_of (by unfold ncs$k nrs$k $lo; norm_num) (by unfold ncs$k nrs$k $(hi == "1" ? "" : hi); norm_num) h₁ h₂\n")
end
# ---- cos(π/64) ----
println(buf, """
/-- The article's search interval, upper end: `(0, searchHi]`. -/
noncomputable def searchHi : ℝ := π / $n

/-- `cos(π/$n)`, bounded through Mathlib's nested radical. -/
lemma cos_searchHi : ($(lr(UCOS_LO)) : ℝ) < Real.cos searchHi ∧ Real.cos searchHi < $(lr(UCOS_HI)) := by
  have e : searchHi = π / 2 ^ ($UK + 1) := by unfold searchHi; norm_num
  rw [e, Real.cos_pi_over_two_pow]
  simp only [Real.sqrtTwoAddSeries, add_zero]""")
for j in 1:UK
    prevlo = j == 1 ? "0" : lr(ulvl_lo[j-1]); prevhi = j == 1 ? "0" : lr(ulvl_hi[j-1])
    println(buf, "  have hl$j : ($(lr(ulvl_lo[j])) : ℝ) < $(uEk(j)) := by\n" *
        "    rw [Real.lt_sqrt (by norm_num)]\n" *
        (j == 1 ? "    norm_num" : "    have : ($(lr(ulvl_lo[j])) : ℝ) ^ 2 < 2 + $prevlo := by norm_num\n    linarith [hl$(j-1)]"))
    println(buf, "  have hu$j : $(uEk(j)) < ($(lr(ulvl_hi[j])) : ℝ) := by\n" *
        "    rw [Real.sqrt_lt' (by norm_num)]\n" *
        (j == 1 ? "    norm_num" : "    have : 2 + $prevhi < ($(lr(ulvl_hi[j])) : ℝ) ^ 2 := by norm_num\n    linarith [hu$(j-1)]"))
end
println(buf, "  constructor <;> linarith\n")
# ---- derivative polynomials ----
for (nm, dp, p) in (("dpl1", UdP1, UP1), ("dpl4", UdP4, UP4), ("dpl5", UdP5, UP5))
    i = nm[end]
    println(buf, "noncomputable def $nm (c : ℝ) : ℝ := $(lp(dp))\n")
    println(buf, "theorem hasDerivAt_pl$i (c : ℝ) : HasDerivAt pl$i ($nm c) c := by\n  unfold pl$i $nm\n  exact $(deriv_chain_u(p)).congr_deriv (by simp only [Pi.mul_apply]; ring)\n")
end
print(buf, "noncomputable def alpha (c : ℝ) : ℝ := $(UAP.pcs[1].tr.alpha.t)\n")

# ---- the theory (the same for every number above) ----------------------------------------
print(buf, raw"""
lemma sn_sq_of {c : ℝ} (h : 0 ≤ 1 - c ^ 2) : sn c ^ 2 = 1 - c ^ 2 := by
  unfold sn; exact Real.sq_sqrt h

lemma sn_pos_of {c : ℝ} (h : 0 < 1 - c ^ 2) : 0 < sn c := by
  unfold sn; exact Real.sqrt_pos.mpr h

lemma one_sub_nonneg_of {c lo hi : ℝ} (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (h₁ : lo ≤ c) (h₂ : c ≤ hi) :
    0 ≤ 1 - c ^ 2 := by nlinarith

lemma one_sub_pos_of {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : 0 < 1 - c ^ 2 := by nlinarith

/-- A square root of a nonnegative `u ≤ R ≤ (2m)²` is within `m` of `m`. -/
lemma sqrt_enc_half {u m R : ℝ} (hu : 0 ≤ u) (huR : u ≤ R) (hm : 0 < m) (hR : R ≤ (2 * m) ^ 2) :
    |Real.sqrt u - m| ≤ m := by
  have h2 : Real.sqrt u ≤ 2 * m := Real.sqrt_le_iff.mpr ⟨by linarith, huR.trans hR⟩
  have h0 := Real.sqrt_nonneg u
  rw [abs_le]; constructor <;> linarith

noncomputable def aa (c : ℝ) : ℝ := sn c * pl1 c + 1 / 2
noncomputable def da (c : ℝ) : ℝ := (-c / sn c) * pl1 c + sn c * dpl1 c
noncomputable def Nf (c : ℝ) : ℝ := -c * pl1 c + (1 - c ^ 2) * dpl1 c
noncomputable def dr (c : ℝ) : ℝ := -2 - 2 * aa c * da c
noncomputable def xx (c : ℝ) : ℝ := aa c + sn c * pl4 c - c
noncomputable def dxx (c : ℝ) : ℝ := da c + (-c / sn c) * pl4 c + sn c * dpl4 c - 1
noncomputable def ww (c : ℝ) : ℝ := pl5 c - sn c - rr c
noncomputable def Gd (c : ℝ) : ℝ :=
  2 * xx c * dxx c + 2 * ww c * (dpl5 c + c / sn c - dr c / (2 * rr c)) + 2

lemma G_eq (c : ℝ) : G c = xx c * xx c + ww c * ww c - pl3 c := by
  unfold G E2e yv xx ww aa; ring

lemma alpha_eq (c : ℝ) : alpha c = 2 * xx c * dxx c + 2 * ww c * (dpl5 c + c / sn c) + 2 := by
  unfold alpha xx dxx ww aa da; ring

lemma da_eq {c : ℝ} (h : 0 < 1 - c ^ 2) : da c = Nf c / sn c := by
  have hs := sn_pos_of h
  have hsq := sn_sq_of h.le
  unfold da Nf
  field_simp
  linear_combination (dpl1 c) * hsq

lemma hasDerivAt_sn {c : ℝ} (h : 0 < 1 - c ^ 2) : HasDerivAt sn (-c / sn c) c := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * c)) c := by
    simpa using (hasDerivAt_pow 2 c).const_sub 1
  have h2 := h1.sqrt h.ne'
  have hs := sn_pos_of h
  have e : -c / sn c = -(2 * c) / (2 * Real.sqrt (1 - c ^ 2)) := by
    unfold sn at hs ⊢; field_simp
  rw [e]
  exact h2

lemma hasDerivAt_pl3 (c : ℝ) : HasDerivAt pl3 (-2) c := by
  unfold pl3
  simpa using ((hasDerivAt_id' c).const_mul (-2 : ℝ)).add_const 2

lemma hasDerivAt_aa {c : ℝ} (h : 0 < 1 - c ^ 2) : HasDerivAt aa (da c) c := by
  have := ((hasDerivAt_sn h).mul (hasDerivAt_pl1 c)).add_const (1 / 2 : ℝ)
  exact this

lemma hasDerivAt_rad {c : ℝ} (h : 0 < 1 - c ^ 2) : HasDerivAt rad (dr c) c := by
  have h1 := (hasDerivAt_pl3 c).sub ((hasDerivAt_aa h).mul (hasDerivAt_aa h))
  show HasDerivAt (fun y => pl3 y - aa y * aa y) (dr c) c
  exact h1.congr_deriv (by unfold dr; ring)

lemma hasDerivAt_rr {c : ℝ} (h : 0 < 1 - c ^ 2) (hr : 0 < rad c) :
    HasDerivAt rr (dr c / (2 * rr c)) c := by
  have := (hasDerivAt_rad h).sqrt hr.ne'
  exact this

lemma hasDerivAt_G {c : ℝ} (h : 0 < 1 - c ^ 2) (hr : 0 < rad c) : HasDerivAt G (Gd c) c := by
  have hx : HasDerivAt xx (dxx c) c := by
    have := ((hasDerivAt_aa h).add ((hasDerivAt_sn h).mul (hasDerivAt_pl4 c))).sub (hasDerivAt_id' c)
    show HasDerivAt (fun y => aa y + sn y * pl4 y - y) (dxx c) c
    exact this.congr_deriv (by unfold dxx; ring)
  have hw : HasDerivAt ww (dpl5 c + c / sn c - dr c / (2 * rr c)) c := by
    have := ((hasDerivAt_pl5 c).sub (hasDerivAt_sn h)).sub (hasDerivAt_rr h hr)
    show HasDerivAt (fun y => pl5 y - sn y - rr y) (dpl5 c + c / sn c - dr c / (2 * rr c)) c
    exact this.congr_deriv (by ring)
  have e : G = fun y => xx y * xx y + ww y * ww y - pl3 y := by funext y; exact G_eq y
  have := ((hx.mul hx).add (hw.mul hw)).sub (hasDerivAt_pl3 c)
  rw [e]
  exact this.congr_deriv (by unfold Gd; ring)

lemma Gd_pos {c : ℝ} (hα : 0 < alpha c) (hw : 0 ≤ ww c) (hdr : dr c < 0) (hrr : 0 < rr c) : 0 < Gd c := by
  have e : Gd c = alpha c - ww c * dr c / rr c := by
    rw [alpha_eq]; unfold Gd; field_simp; ring
  have h : ww c * dr c / rr c ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hw hdr.le) hrr.le
  rw [e]; linarith

lemma continuous_aa : Continuous aa := by unfold aa sn pl1; fun_prop
lemma continuous_rad : Continuous rad := by unfold rad sn pl1 pl3; fun_prop

lemma dr_neg {c : ℝ} (ha : 0 < aa c) (hd : 0 < da c) : dr c < 0 := by
  unfold dr; nlinarith [mul_pos ha hd]

/-- `a > 0` and `a' > 0` on `[slo, 1)`, from `N > 0` and `a(slo) > 0`. -/
theorem aa_da_pos (hN : ∀ c ∈ Ico slo 1, 0 < Nf c) (h0 : 0 < aa slo) (hslo : 0 < slo) :
    ∀ c ∈ Ico slo 1, 0 < aa c ∧ 0 < da c := by
  have hd : ∀ x ∈ Ico slo 1, 0 < da x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hslo hx.1
    have hh := one_sub_pos_of hx0 hx.2
    rw [da_eq hh]; exact div_pos (hN x hx) (sn_pos_of hh)
  intro c hc
  refine ⟨?_, hd c hc⟩
  rcases hc.1.eq_or_lt with h | h
  · rw [← h]; exact h0
  · have hmono : StrictMonoOn aa (Icc slo c) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc slo c) continuous_aa.continuousOn ?_
      intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Ico slo 1 := ⟨hx.1.le, lt_trans hx.2 hc.2⟩
      have hx0 : 0 < x := lt_of_lt_of_le hslo hx'.1
      rw [(hasDerivAt_aa (one_sub_pos_of hx0 hx'.2)).deriv]
      exact hd x hx'
    have := hmono ⟨le_refl _, h.le⟩ ⟨h.le, le_refl _⟩ h
    linarith

/-- The radicand is strictly decreasing on `[slo, 1)`. -/
theorem rad_anti (hN : ∀ c ∈ Ico slo 1, 0 < Nf c) (h0 : 0 < aa slo) (hslo : 0 < slo) :
    StrictAntiOn rad (Ico slo 1) := by
  have hpos := aa_da_pos hN h0 hslo
  refine strictAntiOn_of_deriv_neg (convex_Ico slo 1) continuous_rad.continuousOn ?_
  intro x hx
  rw [interior_Ico] at hx
  have hx' : x ∈ Ico slo 1 := ⟨hx.1.le, hx.2⟩
  have hx0 : 0 < x := lt_trans hslo hx.1
  rw [(hasDerivAt_rad (one_sub_pos_of hx0 hx.2)).deriv]
  obtain ⟨ha, hd⟩ := hpos x hx'
  exact dr_neg ha hd

/-- Where the polygon exists (`rad ≥ 0`) on `[slo, 1)`, `c < cB`. -/
theorem lt_cB (hN : ∀ c ∈ Ico slo 1, 0 < Nf c) (h0 : 0 < aa slo) (hslo : 0 < slo)
    (hB : rad cB < 0) (hcB : cB < 1) (hsc : slo ≤ cB) {c : ℝ} (hc : c ∈ Ico slo 1) (hr : 0 ≤ rad c) : c < cB := by
  by_contra hge
  push Not at hge
  have hanti := rad_anti hN h0 hslo
  rcases hge.eq_or_lt with h | h
  · rw [h] at hB; linarith
  · have := hanti ⟨hsc, hcB⟩ hc h
    linarith

/-- `G` is strictly increasing where the polygon exists. -/
theorem G_lt (hN : ∀ c ∈ Ico slo 1, 0 < Nf c) (h0 : 0 < aa slo) (hslo : 0 < slo) (hcB : cB < 1)
    (hα : ∀ c ∈ Icc slo cB, 0 < rad c → 0 < alpha c ∧ 0 ≤ ww c) :
    ∀ x ∈ Ico slo cB, ∀ y ∈ Ico slo cB, 0 ≤ rad y → x < y → G x < G y := by
  have hanti := rad_anti hN h0 hslo
  have hpos := aa_da_pos hN h0 hslo
  intro x hx y hy hry hxy
  have hyI : y ∈ Ico slo 1 := ⟨hy.1, lt_trans hy.2 hcB⟩
  have hmono : StrictMonoOn G (Icc x y) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc x y) G_continuous.continuousOn ?_
    intro z hz
    rw [interior_Icc] at hz
    have hzI : z ∈ Ico slo 1 := ⟨hx.1.trans hz.1.le, lt_trans hz.2 hyI.2⟩
    have hz0 : 0 < z := lt_of_lt_of_le hslo hzI.1
    have hh := one_sub_pos_of hz0 hzI.2
    have hrz : 0 < rad z := lt_of_le_of_lt hry (hanti hzI hyI hz.2)
    rw [(hasDerivAt_G hh hrz).deriv]
    have hzc : z ∈ Icc slo cB := ⟨hzI.1, (lt_trans hz.2 hy.2).le⟩
    obtain ⟨hal, hw⟩ := hα z hzc hrz
    obtain ⟨ha, hd⟩ := hpos z hzI
    exact Gd_pos hal hw (dr_neg ha hd) (by unfold rr; exact Real.sqrt_pos.mpr hrz)
  exact hmono ⟨le_refl _, hxy.le⟩ ⟨hxy.le, le_refl _⟩ hxy

/-- At most one root of `G` where the polygon exists, in `[slo, cB)`. -/
theorem G_unique (hN : ∀ c ∈ Ico slo 1, 0 < Nf c) (h0 : 0 < aa slo) (hslo : 0 < slo) (hcB : cB < 1)
    (hα : ∀ c ∈ Icc slo cB, 0 < rad c → 0 < alpha c ∧ 0 ≤ ww c) :
    ∀ x ∈ Ico slo cB, ∀ y ∈ Ico slo cB, 0 ≤ rad x → 0 ≤ rad y → G x = 0 → G y = 0 → x = y := by
  intro x hx y hy hrx hry hGx hGy
  rcases lt_trichotomy x y with h | h | h
  · have := G_lt hN h0 hslo hcB hα x hx y hy hry h; linarith
  · exact h
  · have := G_lt hN h0 hslo hcB hα y hy x hx hrx h; linarith

lemma rad_one : rad 1 = -1 / 4 := by
  unfold rad sn pl3; norm_num
""")

# ---- the numeric lemmas ---------------------------------------------------------------------
println(buf, """
lemma enc_sn_slo : |sn slo - $(lr(upc_slo.s0))| ≤ $(lr(upc_slo.Ls.r)) := by
  unfold sn
  exact enc_sqrt (U0 := 1 - slo ^ 2) (EU := 0) (E := $(lr(upc_slo.Esq))) (by unfold slo; norm_num) (by simp) (by norm_num)
    (by unfold slo; norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma aa_slo_pos : 0 < aa slo := by
  unfold aa; exact pos_of_close $(aa_slo.pf) (by norm_num)

lemma enc_sn_cB : |sn cB - $(lr(upc_cB.s0))| ≤ $(lr(upc_cB.Ls.r)) := by
  unfold sn
  exact enc_sqrt (U0 := 1 - cB ^ 2) (EU := 0) (E := $(lr(upc_cB.Esq))) (by unfold cB; norm_num) (by simp) (by norm_num)
    (by unfold cB; norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma rad_cB_neg : rad cB < 0 := by
  unfold rad; exact neg_of_close $(rad_cB.pf) (by norm_num)
""")
for k in 1:UNP.K
    lo = NNAME_LO(k, UNP.K); hi = NNAME_HI(k, UNP.K)
    ck, rk = piece_centre(UNP.brk[k], UNP.brk[k+1])
    t, deg, rhs, steps, tl = taylor_steps("Nf", NV; cn = "ncs$k", rn = "nrs$k", C = ck, R = rk)
    guard(UNLB <= t[1] - sum(abs(t[j+1]) * rk^j for j in 1:deg), "the lower bound of N on piece $k does not hold")
    println(buf, """
lemma Nlb$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : ($(lr(UNLB)) : ℝ) ≤ Nf c := by
  have key : Nf c = $rhs := by
    unfold Nf pl1 dpl1 ncs$k; ring
  have hr : |c - ncs$k| ≤ nrs$k := nnear$k c h₁ h₂
$steps
  have hnum : ($(lr(UNLB)) : ℝ) ≤ $(lr(t[1])) - ($tl) := by
    unfold nrs$k; norm_num
  rw [key]
  linarith
""")
end
println(buf, "lemma N_pos : ∀ c ∈ Ico slo 1, 0 < Nf c := by\n  intro c hc\n  have h0 : (0 : ℝ) < $(lr(UNLB)) := by norm_num")
for k in 1:UNP.K-1
    prevh = k == 1 ? "hc.1" : "(le_of_lt (not_le.mp e$(k-1)))"
    println(buf, "  by_cases e$k : c ≤ nb$k\n  · have := Nlb$k c $prevh e$k; linarith")
end
println(buf, "  have := Nlb$(UNP.K) c $(UNP.K == 1 ? "hc.1" : "(le_of_lt (not_le.mp e$(UNP.K-1)))") hc.2.le\n  linarith\n")
for pc in UAP.pcs
    k = pc.k; lo = UNAME_LO(k); hi = UNAME_HI(k, UAP.K); tr = pc.tr
    for i in (1, 3, 4, 5)
        println(buf, piece_enc("encq$(k)_pl$i", "pl$i", PLLIST[i], pc.ck, pc.rk, "cs$k", "rs$k", "near$k", lo, hi, pc.pol[i][1], pc.pol[i][2]))
    end
    for (i, dp) in ((1, UdP1), (4, UdP4), (5, UdP5))
        println(buf, piece_enc("encq$(k)_dpl$i", "dpl$i", dp, pc.ck, pc.rk, "cs$k", "rs$k", "near$k", lo, hi, pc.dpol[i][1], pc.dpol[i][2]))
    end
    println(buf, """
lemma enc_sn$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |sn c - $(lr(pc.ps[1]))| ≤ $(lr(pc.ps[2])) := by
  unfold sn
  exact enc_sqrt (E := $(lr(pc.ps[3]))) (one_sub_nonneg_of (by unfold $lo; norm_num) (by unfold $hi; norm_num) h₁ h₂)
    (one_sub_sq_close (near$k c h₁ h₂)) (by norm_num)
    (by unfold rs$k cs$k; norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg]) (by norm_num)

lemma enc_rad$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) : |rad c - $(lr(pc.rad.c))| ≤ $(lr(pc.rad.r)) := by
  unfold rad; exact $(pc.rad.pf)

lemma rr_close$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) (hrad : 0 < rad c) : |rr c - $(lr(pc.m))| ≤ $(lr(pc.m)) := by
  unfold rr
  have hu := (abs_le.mp (enc_rad$k c h₁ h₂)).2
  exact sqrt_enc_half (R := $(lr(pc.rhi))) hrad.le (by linarith) (by norm_num) (by norm_num)

lemma alpha_pos$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) (hrad : 0 < rad c) : 0 < alpha c := by
  unfold alpha
  exact pos_of_close $(tr.alpha.pf) (by norm_num)

lemma ww_nonneg$k (c : ℝ) (h₁ : $lo ≤ c) (h₂ : c ≤ $hi) (hrad : 0 < rad c) : 0 ≤ ww c := by
  unfold ww
  exact (pos_of_close $(tr.w.pf) (by norm_num)).le
""")
end
println(buf, "lemma alpha_all : ∀ c ∈ Icc slo cB, 0 < rad c → 0 < alpha c ∧ 0 ≤ ww c := by\n  intro c hc hrad\n  obtain ⟨h₁, h₂⟩ := hc")
for k in 1:UAP.K-1
    prevh = k == 1 ? "h₁" : "(le_of_lt (not_le.mp e$(k-1)))"
    println(buf, "  by_cases e$k : c ≤ ub$k\n  · exact ⟨alpha_pos$k c $prevh e$k hrad, ww_nonneg$k c $prevh e$k hrad⟩")
end
lastp = UAP.K == 1 ? "h₁" : "(le_of_lt (not_le.mp e$(UAP.K-1)))"
println(buf, "  exact ⟨alpha_pos$(UAP.K) c $lastp h₂ hrad, ww_nonneg$(UAP.K) c $lastp h₂ hrad⟩\n")

# ---- the final theorem ------------------------------------------------------------------------
println(buf, """
lemma slo_pos : 0 < slo := by unfold slo; norm_num
lemma slo_le_clo : slo ≤ clo := by unfold slo clo; norm_num
lemma chi_lt_cB : chi < cB := by unfold chi cB; norm_num
lemma cB_lt_one : cB < 1 := by unfold cB; norm_num
lemma slo_le_cB : slo ≤ cB := by unfold slo cB; norm_num
lemma slo_lt_cos : slo < Real.cos searchHi := by unfold slo; exact cos_searchHi.1
lemma cos_lt_clo : Real.cos searchHi < clo := by
  have := cos_searchHi.2
  unfold clo; linarith

lemma searchHi_le_pi : searchHi ≤ π := by
  unfold searchHi; have := Real.pi_pos; linarith

/-- **Z$n, with the uniqueness of the root.** The certified configuration is the one of a root `z` of
the equation of `Z$n` in the search interval `(0, π/$n]`, and it is the only root there at which the
polygon exists (`rad ≥ 0`): a strictly convex equilateral small `$n`-gon and a strict local maximiser of
the perimeter, modulo Euclidean motions. -/
theorem locally_maximal_unique :
    ∃ z : ℝ, z ∈ Ioo 0 searchHi ∧ G (Real.cos z) = 0 ∧
      (∀ z' ∈ Ioc 0 searchHi, 0 ≤ rad (Real.cos z') → G (Real.cos z') = 0 → z' = z) ∧
      0 < ell (Real.cos z) ∧ IsFeasibleConvex (P (Real.cos z), ell (Real.cos z)) ∧
      (∀ᶠ y in nhds ((P (Real.cos z), ell (Real.cos z)) : Amb $n), IsFeasible y →
        ell (Real.cos z) ≤ y.2 → Congruent y.1 (P (Real.cos z)) ∧ y.2 = ell (Real.cos z)) ∧
      (∀ᶠ y in nhds ((P (Real.cos z), ell (Real.cos z)) : Amb $n), IsFeasible y →
        y.2 ≤ ell (Real.cos z)) := by
  have hN := N_pos
  have hu := G_unique hN aa_slo_pos slo_pos cB_lt_one alpha_all
  have hanti := rad_anti hN aa_slo_pos slo_pos
  have hlt := fun {c : ℝ} (hc : c ∈ Ico slo 1) (hr : 0 ≤ rad c) =>
    lt_cB hN aa_slo_pos slo_pos rad_cB_neg cB_lt_one slo_le_cB hc hr
  obtain ⟨c, hc, hG⟩ := G_root
  obtain ⟨hl, hfeas, hev, hle⟩ := locally_maximal_at hc hG
  have hclo := slo_le_clo
  have hc1 : c < 1 := lt_trans hc.2 chi_lt_one
  have hcm1 : (-1 : ℝ) ≤ c := by have := hc.1; have := clo_pos; linarith
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hcm1 hc1.le
  have hcI : c ∈ Ico slo 1 := ⟨by have := hc.1; linarith, hc1⟩
  have hchiI : chi ∈ Ico slo 1 := ⟨by have := slo_le_clo; have := clo_lt_chi; linarith, chi_lt_one⟩
  have hrc : 0 ≤ rad c := by
    have := hanti hcI hchiI hc.2
    have := rad_nonneg_chi
    linarith
  have hcB : c < cB := lt_trans hc.2 chi_lt_cB
  have hHi0 : 0 ≤ searchHi := by unfold searchHi; positivity
  have hmem : Real.arccos c ∈ Ioo 0 searchHi := by
    constructor
    · exact Real.arccos_pos.mpr hc1
    · have h := Real.arccos_lt_arccos (Real.neg_one_le_cos searchHi) (by linarith [hc.1, cos_lt_clo]) hc1.le
      rwa [Real.arccos_cos hHi0 searchHi_le_pi] at h
  refine ⟨Real.arccos c, hmem, by rw [hcos]; exact hG, ?_, by rw [hcos]; exact hl, by rw [hcos]; exact hfeas,
    by rw [hcos]; exact hev, by rw [hcos]; exact hle⟩
  intro z' hz' hr' hG'
  have hz'0 : 0 < z' := hz'.1
  have hzpi : z' ≤ π := hz'.2.trans searchHi_le_pi
  have hc' : Real.cos searchHi ≤ Real.cos z' := Real.cos_le_cos_of_nonneg_of_le_pi hz'0.le searchHi_le_pi hz'.2
  have hc'1 : Real.cos z' < 1 := by
    rcases (Real.cos_le_one z').lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, rad_one] at hr'; norm_num at hr'
  have hc'I : Real.cos z' ∈ Ico slo 1 := ⟨by linarith [slo_lt_cos], hc'1⟩
  have hc'B := hlt hc'I hr'
  have heq : Real.cos z' = Real.cos (Real.arccos c) := by
    rw [hcos]; exact hu _ ⟨hc'I.1, hc'B⟩ _ ⟨hcI.1, hcB⟩ hr' hrc hG' hG
  exact Real.injOn_cos ⟨hz'0.le, hzpi⟩ ⟨(hmem.1).le, (hmem.2.le.trans searchHi_le_pi)⟩ heq
""")
print(buf, footer())
emit("Unique", String(take!(buf)))
global prev = "$MOD.Unique"
println("  wrote Unique.lean ($(UAP.K) α-pieces, $(UNP.K) N-pieces)")
