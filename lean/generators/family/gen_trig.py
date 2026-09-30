#!/usr/bin/env python3
"""Generate the kernel-checked certificate of A<n> for the general Lean theorem
`Chiquipoli.Family.Trig.published_of_checks` (lean/ChiquipoliFamily/Interval/Assemble.lean).

    python3 lean/generators/family/gen_trig.py 256

writes lean/ChiquipoliFamily/Interval/T<n>/{Data,Checks*,Main}.lean. Standard library only.

Nothing produced here is trusted. The data (tables, enclosures, graph, shape
witnesses, Henneberg order, stress enclosures) are claims; every one is checked
by the Lean kernel (`decide +kernel`) and a wrong claim makes a check fail. The
integer interval arithmetic below mirrors ChiquipoliFamily/Interval/FI.lean
operation for operation (trigfi.py), so that honest data passes exactly.
"""
import math
import os
import re
import sys
import time
from decimal import Decimal, getcontext

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import trigfi  # noqa: E402
from trigfi import (FI, K, S, abS, add, div, enc, encF, encFd, find_witness, gn_edges, lean_term,  # noqa: E402
                    mul, neg, ofInt, pointCS, sub, sqdFI, crossFI, tab_at, vertexS, widen,
                    SHP_DIAM, SHP_SIDE, gn_act)

getcontext().prec = 250
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482"
             "534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964")
PI_LO = 314159265358979323846   # Mathlib `Real.pi_gt_d20`, times 10^20
PI_HI = 314159265358979323847   # Mathlib `Real.pi_lt_d20`
EXP_RR = 180                     # root bracket half-width 2^-180
PRESET_BITS = 30                 # preset stresses are N / 2^30


def die(msg):
    print(f"gen_trig: {msg}", file=sys.stderr)
    sys.exit(1)


def read_root(n):
    path = os.path.join(REPO, "cases", "family", f"A{n}", "candidate.jl")
    src = open(path).read()
    mt = re.search(r'z_nom\s*=\s*big"([0-9.eE+-]+)"', src)
    return Decimal(mt.group(1)) if mt else None


def bisect_root(n, J):
    """The zero of F on upstream's bracket, by bisection with the kernel's own F (float accuracy)."""
    m = n // 8
    hi = float(PI) / n
    lo = 2 * math.asin(math.sin(hi) / 2)
    a, b = lo * (1 + 1e-12), hi * (1 - 1e-12)
    for _ in range(80):
        c = (a + b) / 2
        Fi = encF(m, tab_at(int(Decimal(c) * 2 ** K), J, 0, n // 2))
        if mid(Fi) > 0:
            a = c
        else:
            b = c
    return Decimal((a + b) / 2)


def mid(I):
    return (I.lo + I.hi) // 2


def refine_root(n, J, z):
    """Newton on the dyadic grid, with F and F' evaluated by the kernel's own arithmetic."""
    m = n // 8
    N = int(z * 2 ** K)
    for _ in range(12):
        tab = tab_at(N, J, 0, n // 2)
        Fi, Di = encF(m, tab), encFd(m, tab)
        step = (mid(Fi) * 2 ** K) // mid(Di)
        N -= step
        if abs(step) < 2 ** (K - EXP_RR - 40):
            break
    return N - (N % 2)          # even, so that (N0 - rr) / 2 is an integer


def fmtFI(I):
    return f"⟨{I.lo}, {I.hi}⟩"


def fmtP(P):
    return f"({fmtFI(P[0])}, {fmtFI(P[1])})"


def lean_list(items, per_line=1, indent="  "):
    items = list(items)
    if not items:
        return "[]"
    lines = []
    for a in range(0, len(items), per_line):
        lines.append(", ".join(items[a:a + per_line]))
    return "[" + (",\n" + indent).join(lines) + "]"


def main():
    if len(sys.argv) < 2:
        die("usage: gen_trig.py N")
    n = int(sys.argv[1])
    if n < 16 or n % 16:
        die("n must be a multiple of 16")
    t_start = time.time()
    k = n // 16
    m8 = n // 8
    zc = read_root(n)
    J = max(1, int(round((K - 4 * math.log2(n / float(PI))) / 4)))

    # ---- the root and upstream's bracket ----
    z0 = bisect_root(n, J)
    N0 = refine_root(n, J, z0)
    if zc is not None and abs(Decimal(N0) / Decimal(2) ** K - zc) > Decimal(10) ** -50:
        die(f"the root disagrees with the candidate's z_nom: {Decimal(N0) / Decimal(2) ** K} vs {zc}")
    rr = 2 ** (K - EXP_RR)
    Flo = encF(m8, tab_at(N0 - rr, J, 0, n // 2))
    Fhi = encF(m8, tab_at(N0 + rr, J, 0, n // 2))
    if not (Flo.lo > 0 and Fhi.hi < 0):
        die(f"no sign change at the root bracket: {Flo}, {Fhi}")
    Np = int((PI / n) * 2 ** K)
    rp = 2
    while not ((Np - rp) * n * 10 ** 20 <= PI_LO * S and PI_HI * S <= (Np + rp) * n * 10 ** 20):
        rp *= 2
    hi_f = float(PI) / n
    lo_f = 2 * math.asin(math.sin(hi_f) / 2)
    a_N = int(Decimal(lo_f * (1 - 1e-9)) * 2 ** K)
    b_N = int(Decimal(hi_f * (1 + 1e-9)) * 2 ** K)
    a_N -= a_N % 2
    b_N += b_N % 2
    Nc = (a_N + b_N) // 2
    rc = (b_N - a_N) // 2
    if (Nc - rc) % 2:
        rc += 1
    Hlo = (N0 - rr) // 2
    Ha = (Nc - rc) // 2
    SP = widen(pointCS(Np, J)[1], rp)
    sin_ok = SP.hi < 2 * pointCS(Hlo, J)[1].lo and 2 * pointCS(Ha, J)[1].hi <= SP.lo
    if not sin_ok:
        die("bracket comparison of sin fails")
    bracket_ok = (0 < N0 - rr and 0 < rr and 4 * (N0 + rr) < 3 * S and 0 < Nc - rc and 0 <= rc
                  and 4 * (Nc + rc) < 3 * S and 0 <= Np <= S and 0 <= rp and 2 * Hlo == N0 - rr
                  and 2 * Ha == Nc - rc and N0 + rr < Np - rp and Np + rp <= Nc + rc)
    if not bracket_ok:
        die("bracket integer conditions fail")
    M = n // 2
    tabLo = tab_at(N0 - rr, J, 0, M)
    tabHi = tab_at(N0 + rr, J, 0, M)
    tabU = tab_at(Nc, J, rc, M)
    FdU = encFd(m8, tabU)
    if not (FdU is not None and FdU.hi < 0):
        die(f"Fd not negative on the bracket: {FdU}")
    tab = tab_at(N0, J, rr, M)

    # ---- the polygon ----
    ab = abS(n)
    VS = [vertexS(n, i, ab) for i in range(n)]
    vd = [(enc(tab, v[0]), enc(tab, v[1])) for v in VS]
    if any(a is None or b is None for a, b in vd):
        die("a vertex does not evaluate")
    conv_min = min(crossFI(vd[i], vd[(i + 1) % n], vd[(i + t) % n]).lo for i in range(n) for t in range(2, n))
    far_max = max(sqdFI(vd[i], vd[j]).hi for i in range(n) for j in range(i + 1, n) if not gn_act(n, i, j))
    if not (conv_min > 0 and far_max < S):
        die(f"convexity / far pairs fail: {conv_min}, {far_max}")
    E = gn_edges(n)
    m = len(E)
    nb = n + m
    sideW = []
    for i in range(n):
        w = find_witness(n, VS[(i + 1) % n], VS[i], SHP_SIDE + ["clo", "clo'"])
        if w is None:
            die(f"side {i}: no shape witness")
        sideW.append(w)
    diamW = []
    for (a, b) in E:
        w = find_witness(n, VS[b], VS[a], SHP_DIAM)
        if w is None:
            die(f"diameter {(a, b)}: no shape witness")
        diamW.append(w)
    BARS = [(i, (i + 1) % n) for i in range(n)] + E

    # ---- Henneberg order (greedy, best-conditioned pair first) ----
    P = [((mid(a)) / 2 ** K, (mid(b)) / 2 ** K) for a, b in vd]
    inc = {v: [b for b in range(nb) if v in BARS[b]] for v in range(n)}
    other = lambda b, v: BARS[b][0] if BARS[b][1] == v else BARS[b][1]
    placed, used, order = [0, 1], {0}, []
    rest = set(range(2, n))
    while rest:
        best = None
        for v in sorted(rest):
            cand = [b for b in inc[v] if other(b, v) in placed]
            for x in range(len(cand)):
                for y in range(x + 1, len(cand)):
                    bi, bj = cand[x], cand[y]
                    i, j = other(bi, v), other(bj, v)
                    u = (P[i][0] - P[v][0], P[i][1] - P[v][1])
                    w = (P[j][0] - P[v][0], P[j][1] - P[v][1])
                    d = abs(u[0] * w[1] - u[1] * w[0]) / (math.hypot(*u) * math.hypot(*w))
                    if best is None or d > best[0]:
                        best = (d, v, i, j, bi, bj)
        if best is None:
            die(f"greedy Henneberg order stuck after {len(placed)} vertices")
        _, v, i, j, bi, bj = best
        order.append((v, i, j, bi, bj))
        placed.append(v)
        used |= {bi, bj}
        rest.discard(v)
    extras = [b for b in range(nb) if b not in used]
    steps = list(reversed(order))
    pb = 0

    # ---- the self-stress: float basis, presets, then the exact FI recursion ----
    def recurse_float(pre):
        sig = dict(pre)
        for (v, i, j, bi, bj) in steps:
            F = [0.0, 0.0]
            for b in inc[v]:
                if b in (bi, bj):
                    continue
                o = other(b, v)
                F[0] += sig.get(b, 0.0) * (P[o][0] - P[v][0])
                F[1] += sig.get(b, 0.0) * (P[o][1] - P[v][1])
            u = (P[i][0] - P[v][0], P[i][1] - P[v][1])
            w = (P[j][0] - P[v][0], P[j][1] - P[v][1])
            D = u[0] * w[1] - u[1] * w[0]
            sig[bi] = (-F[0] * w[1] + F[1] * w[0]) / D
            sig[bj] = (-F[1] * u[0] + F[0] * u[1]) / D
        G = [0.0, 0.0]
        for b in inc[1]:
            if b == pb:
                continue
            o = other(b, 1)
            G[0] += sig.get(b, 0.0) * (P[o][0] - P[1][0])
            G[1] += sig.get(b, 0.0) * (P[o][1] - P[1][1])
        u = (P[0][0] - P[1][0], P[0][1] - P[1][1])
        sig[pb] = -(G[0] * u[0] + G[1] * u[1]) / (u[0] ** 2 + u[1] ** 2)
        return [sig.get(b, 0.0) for b in range(nb)]

    if len(extras) != 2:
        die(f"expected a 2-dimensional stress space, got {len(extras)} extra bars")
    s1 = recurse_float({extras[0]: 1.0})
    s2 = recurse_float({extras[1]: 1.0})
    best = None
    for t in range(7200):
        th = 2 * math.pi * t / 7200
        c1, c2 = math.cos(th), math.sin(th)
        sv = [c1 * x + c2 * y for x, y in zip(s1, s2)]
        sc = max(abs(v) for v in sv)
        marg = min(min(sv[n:]), -sum(sv[:n])) / sc
        if best is None or marg > best[0]:
            best = (marg, c1 / sc, c2 / sc)
    if best[0] <= 0:
        die("no positive multiplier vector in the stress space")
    ex = [(extras[0], round(best[1] * 2 ** PRESET_BITS)), (extras[1], round(best[2] * 2 ** PRESET_BITS))]

    sd = {b: FI(N * 2 ** (K - PRESET_BITS), N * 2 ** (K - PRESET_BITS)) for b, N in ex}
    known = [b for b, _ in ex]

    def force(v, x, y, known_set):
        F = (ofInt(0), ofInt(0))
        for b in range(nb):
            if v not in BARS[b] or b == x or b == y:
                continue
            if b not in known_set:
                die(f"force at {v}: bar {b} unknown")
            o = other(b, v)
            c = (sub(vd[o][0], vd[v][0]), sub(vd[o][1], vd[v][1]))
            F = (add(F[0], mul(sd[b], c[0])), add(F[1], mul(sd[b], c[1])))
        return F

    known_set = set(known)
    for (v, i, j, bi, bj) in steps:
        F = force(v, bi, bj, known_set)
        u = (sub(vd[i][0], vd[v][0]), sub(vd[i][1], vd[v][1]))
        w = (sub(vd[j][0], vd[v][0]), sub(vd[j][1], vd[v][1]))
        D = sub(mul(u[0], w[1]), mul(u[1], w[0]))
        c1 = div(add(mul(neg(F[0]), w[1]), mul(F[1], w[0])), D)
        c2 = div(add(mul(neg(F[1]), u[0]), mul(F[0], u[1])), D)
        if c1 is None or c2 is None:
            die(f"Cramer step at {v}: determinant interval contains 0")
        sd[bi], sd[bj] = c1, c2
        known_set |= {bi, bj}
    G = force(1, pb, pb, known_set)
    u = (sub(vd[0][0], vd[1][0]), sub(vd[0][1], vd[1][1]))
    cp = div(neg(add(mul(G[0], u[0]), mul(G[1], u[1]))), add(mul(u[0], u[0]), mul(u[1], u[1])))
    if cp is None:
        die("pin step fails")
    sd[pb] = cp
    if len(sd) != nb:
        die("some bar has no stress enclosure")
    sdl = [sd[b] for b in range(nb)]
    lam_min = min(I.lo for I in sdl[n:])
    ssum = ofInt(0)
    for I in reversed(sdl[:n]):
        ssum = add(I, ssum)
    wmax = max(I.hi - I.lo for I in sdl)
    if not (lam_min > 0 and ssum.hi < 0):
        die(f"stress enclosure too wide: min lambda lo {lam_min / S}, side sum hi {ssum.hi / S}")

    stats = dict(n=n, J=J, K=K, rr_exp=EXP_RR, conv_margin=conv_min / S, far_margin=1 - far_max / S,
                 lam_min=lam_min / S, side_sum=ssum.hi / S, sd_width=wmax / S, Fd=FdU.hi / S,
                 root_digits=str(Decimal(N0) / Decimal(2) ** K)[:40])
    for kk, vv in stats.items():
        print(f"  {kk}: {vv}", file=sys.stderr)
    emit(n, k, m, J, N0, rr, Np, rp, Nc, rc, Hlo, Ha, tab, tabLo, tabHi, tabU, VS, vd, E, sideW, diamW,
         BARS, order, steps, ex, pb, sdl, stats)
    print(f"gen_trig {n}: done in {time.time() - t_start:.1f}s", file=sys.stderr)


def wlean(w):
    tag, i, mir, flip = w
    s = f"Shp.{tag}" + (f" {i}" if i is not None else "")
    return f"⟨{'(' + s + ')' if i is not None else s}, {str(mir).lower()}, {str(flip).lower()}⟩"


def emit(n, k, m, J, N0, rr, Np, rp, Nc, rc, Hlo, Ha, tab, tabLo, tabHi, tabU, VS, vd, E, sideW, diamW,
         BARS, order, steps, ex, pb, sd, stats):
    nb = n + m
    base = os.environ.get("CHIQUI_OUTDIR") or os.path.join(REPO, "lean")
    out = os.path.join(base, "ChiquipoliFamily", "Interval", f"T{n}")
    os.makedirs(out, exist_ok=True)
    ns = f"Chiquipoli.Family.T{n}"
    hdr = (f"/-\nAUTO-GENERATED by `lean/generators/family/gen_trig.py {n}` — do not edit by hand.\n")
    opts = "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
    # ---------- Data ----------
    D = [hdr + f"""
The claimed data of the A{n} certificate. None of it is trusted: every entry is
checked by the kernel in `Checks*.lean`, and `Main.lean` feeds the checks to the
general `Chiquipoli.Family.Trig.published_of_checks`.
-/
import ChiquipoliFamily.Interval.Assemble

namespace {ns}

open Chiquipoli.Family.Trig FI

def J : ℕ := {J}
def N0 : ℤ := {N0}
def rr : ℤ := {rr}
def Np : ℤ := {Np}
def rp : ℤ := {rp}
def Nc : ℤ := {Nc}
def rc : ℤ := {rc}
def Hlo : ℤ := {Hlo}
def Ha : ℤ := {Ha}
"""]
    for name, t in (("tab", tab), ("tabLo", tabLo), ("tabHi", tabHi), ("tabU", tabU)):
        D.append(f"def {name} : List (FI × FI) := {lean_list(map(fmtP, t))}\n\n")
    D.append(f"def VS : List (Tm × Tm) := {lean_list(f'({lean_term(a)}, {lean_term(b)})' for a, b in VS)}\n\n")
    D.append(f"def vd : List (FI × FI) := {lean_list(map(fmtP, vd))}\n\n")
    D.append(f"def E : List (Fin {n} × Fin {n}) := {lean_list((f'({a}, {b})' for a, b in E), 12)}\n\n")
    D.append(f"def sideW : List W := {lean_list((wlean(w) for w in sideW), 4)}\n\n")
    D.append(f"def diamW : List W := {lean_list((wlean(w) for w in diamW), 4)}\n\n")
    D.append(f"def BARS : List (Fin {n} × Fin {n}) := {lean_list((f'({a}, {b})' for a, b in BARS), 12)}\n\n")
    D.append(f"def order : List (Fin {n} × Fin {n} × Fin {n}) := "
             f"{lean_list((f'({v}, {i}, {j})' for (v, i, j, _, _) in order), 10)}\n\n")
    D.append(f"def BL : List (Fin {nb} × (Fin {n} × Fin {n})) := "
             f"{lean_list((f'({b}, ({x}, {y}))' for b, (x, y) in enumerate(BARS)), 8)}\n\n")
    D.append(f"def steps : List (HStep {n} {nb}) := "
             f"{lean_list((f'⟨{v}, {i}, {j}, {bi}, {bj}⟩' for (v, i, j, bi, bj) in steps), 6)}\n\n")
    D.append(f"def ex : List (Fin {nb} × ℤ) := {lean_list(f'({b}, {N})' for b, N in ex)}\n\n")
    D.append(f"def pb : Fin {nb} := {pb}\n\n")
    D.append(f"def sd : List FI := {lean_list(map(fmtFI, sd))}\n\n")
    D.append(f"end {ns}\n")
    open(os.path.join(out, "Data.lean"), "w").write("".join(D))

    # ---------- Checks ----------
    CH = 16 if n >= 64 else max(1, n // 4)
    Q = (n + CH - 1) // CH
    QE = (m + CH - 1) // CH

    def chunks(name, f, q):
        return "".join(f"theorem {name}_{t} : (List.range' ({CH} * {t}) {CH}).all ({f}) = true := by decide +kernel\n"
                       for t in range(q))

    files = {
        "Checks1": ("root, bracket, tables", [
            f"theorem bracket : bracketOK {n} N0 rr Np rp Nc rc Hlo Ha = true := by decide +kernel\n",
            "theorem sinc : sinOK J Np rp Hlo Ha = true := by decide +kernel\n",
            "theorem lo_head : tabHead tabLo = true := by decide +kernel\n",
            "theorem lo_ok : tabOK ((pointCS (N0 - rr) J).1.widen 0) ((pointCS (N0 - rr) J).2.widen 0) tabLo = true := by decide +kernel\n",
            "theorem hi_head : tabHead tabHi = true := by decide +kernel\n",
            "theorem hi_ok : tabOK ((pointCS (N0 + rr) J).1.widen 0) ((pointCS (N0 + rr) J).2.widen 0) tabHi = true := by decide +kernel\n",
            "theorem u_head : tabHead tabU = true := by decide +kernel\n",
            "theorem u_ok : tabOK ((pointCS Nc J).1.widen rc) ((pointCS Nc J).2.widen rc) tabU = true := by decide +kernel\n",
            f"theorem root : rootOK {k} tabLo tabHi tabU = true := by decide +kernel\n",
            "theorem tab_head : tabHead tab = true := by decide +kernel\n",
            "theorem tab_ok : tabOK ((pointCS N0 J).1.widen rr) ((pointCS N0 J).2.widen rr) tab = true := by decide +kernel\n",
        ]),
        "Checks2": ("the symbolic vertices (upstream's code) and their enclosures", [
            chunks("vs", f"vsOK {n} VS", Q),
            f"theorem vd_len : vd.length = {n} := by decide +kernel\n",
            chunks("vdc", "vdOK tab VS vd", Q),
        ]),
        "Checks3": ("convexity", [chunks("conv", "sideOK vd", Q)]),
        "Checks4": ("far pairs and the active graph", [
            chunks("far", f"farRowOK (gnAct {n}) vd", Q),
            chunks("act", "actOK E", Q),
            f"theorem E_len : E.length = {m} := by decide +kernel\n",
        ]),
        "Checks5": ("exact identities, by shape witness", [
            chunks("sw", f"sideWOK {n} {k} VS sideW", Q),
            chunks("dw", "diamWOK VS E diamW", QE),
        ]),
        "Checks6": ("rigidity", [
            f"theorem bars : BARS = (List.finRange {n}).map (fun i => (i, i + 1)) ++ E := by decide +kernel\n",
            "theorem hen : henOK BARS [0, 1] order = true := by decide +kernel\n",
            "theorem cover : coverOK order = true := by decide +kernel\n",
            "theorem det : detOK vd (order.map fun s => (s.1.val, s.2.1.val, s.2.2.val)) = true := by decide +kernel\n",
        ]),
        "Checks7": ("the self-stress", [
            f"theorem bl : BL = (List.finRange {nb}).zip BARS := by decide +kernel\n",
            "theorem ord : order = steps.reverse.map fun s => (s.k, s.i, s.j) := by decide +kernel\n",
            "theorem steps_ok : stepsOK (barOf BARS) (ex.map (·.1)) [] [] steps = true := by decide +kernel\n",
            "theorem preset : presetOK sd ex = true := by decide +kernel\n",
            "theorem steps_fi : stepsFIOK vd sd BL (ex.map (·.1)) steps = true := by decide +kernel\n",
            "theorem pin : pinFIOK vd sd BL (knownAfter (ex.map (·.1)) steps) 0 1 pb = true := by decide +kernel\n",
            "theorem pb_bar : barOf BARS pb = (0, 1) := by decide +kernel\n",
            "theorem pb_steps : steps.all (fun s => decide (pb ≠ s.bi) && decide (pb ≠ s.bj)) = true := by decide +kernel\n",
            "theorem pb_ex : (ex.map (·.1)).contains pb = false := by decide +kernel\n",
            f"theorem cover_bars : (List.finRange {nb}).all (fun b => (pb :: knownAfter (ex.map (·.1)) steps).contains b) = true := by decide +kernel\n",
            f"theorem sd_len : sd.length = {nb} := by decide +kernel\n",
            f"theorem lam : (sd.drop {n}).all (fun I => decide (0 < I.lo)) = true := by decide +kernel\n",
            f"theorem ssum : (sumFI (sd.take {n})).hi < 0 := by decide +kernel\n",
        ]),
    }
    for fname, (what, parts) in files.items():
        txt = hdr + f"\nA{n}: kernel checks — {what}.\n-/\nimport ChiquipoliFamily.Interval.T{n}.Data\n\n{opts}\nnamespace {ns}\n\nopen Chiquipoli.Family.Trig FI\n\n"
        txt += "".join(parts) + f"\nend {ns}\n"
        open(os.path.join(out, f"{fname}.lean"), "w").write(txt)

    # ---------- Main ----------
    def chunk_proof(name, f, q, N, hN="by norm_num"):
        cases = "\n".join(f"      · exact {name}_{t}" for t in range(q))
        return (f"(forall_lt_of_chunks ({f}) {CH} {q} {N} (by norm_num) ({hN}) (fun t ht => by\n"
                f"      interval_cases t\n{cases}))")
    imports = "".join(f"import ChiquipoliFamily.Interval.T{n}.{f}\n" for f in files)
    main = hdr + f"""
**A{n}, stated about the published objects, proved by the general theorem.**
`Chiquipoli.Family.Trig.published_of_checks` (proved once, for every `n = 16k`)
applied to the kernel checks of `Checks1`–`Checks7`. The statement is the one of
`A16/Published.lean`: upstream's constructor equation `Optigon.F {n}` has exactly
one zero `z` in upstream's bracket, and the polygon upstream builds there is a
strictly convex equilateral small {n}-gon and a strict local maximiser of the
perimeter, modulo orientation-preserving Euclidean motions.
-/
{imports}
{opts}
namespace {ns}

open Chiquipoli.Family.Trig FI Chiquipoli.FirstOrder Chiquipoli.Feasible Chiquipoli.Family
open Set Real

/-- The published polygon: vertex `k` is upstream's `(a[k], b[k])`. -/
noncomputable def Q (z : ℝ) : Fin {n} → ℝ × ℝ := fun k => Optigon.vertex {n} z k

theorem published_locally_maximal :
    ∃ z : ℝ, z ∈ Ioo (Optigon.lo {n}) (Optigon.hi {n}) ∧ Optigon.F {n} z = 0 ∧
      (∀ z' ∈ Ioo (Optigon.lo {n}) (Optigon.hi {n}), Optigon.F {n} z' = 0 → z' = z) ∧
      0 < 2 * sin (z / 2) ∧ IsFeasibleConvex (Q z, 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Q z, 2 * sin (z / 2)) : Amb {n}), IsFeasible y → 2 * sin (z / 2) ≤ y.2 →
          Chiquipoli.Feasible.Congruent y.1 (Q z) ∧ y.2 = 2 * sin (z / 2)) ∧
      (∀ᶠ y in nhds ((Q z, 2 * sin (z / 2)) : Amb {n}), IsFeasible y → y.2 ≤ 2 * sin (z / 2)) :=
  published_of_checks {n} {k} {m} (by norm_num) (by norm_num) J N0 rr Np rp Nc rc Hlo Ha tabLo tabHi tabU
    bracket sinc ⟨lo_head, lo_ok⟩ ⟨hi_head, hi_ok⟩ ⟨u_head, u_ok⟩ root
    tab ⟨tab_head, tab_ok⟩ VS
    {chunk_proof("vs", f"vsOK {n} VS", Q, n)}
    vd vd_len
    {chunk_proof("vdc", "vdOK tab VS vd", Q, n)}
    {chunk_proof("conv", "sideOK vd", Q, n)}
    {chunk_proof("far", f"farRowOK (gnAct {n}) vd", Q, n)}
    E E_len
    {chunk_proof("act", "actOK E", Q, n)}
    sideW diamW
    {chunk_proof("sw", f"sideWOK {n} {k} VS sideW", Q, n)}
    {chunk_proof("dw", "diamWOK VS E diamW", QE, "E.length", "by rw [E_len]; norm_num")}
    BARS bars order hen cover det BL bl steps ord ex pb sd
    steps_ok preset steps_fi pin pb_bar pb_steps pb_ex cover_bars sd_len lam ssum

end {ns}
"""
    open(os.path.join(out, "Main.lean"), "w").write(main)
    stat = "".join(f"-- {kk}: {vv}\n" for kk, vv in stats.items())
    open(os.path.join(out, "STATS.txt"), "w").write(stat)
    emit_controls(base, n, k, m, E, order, sideW, diamW)


# Negative controls: each states a check on TAMPERED data, which the kernel must
# refute; its twin states the same check on the true data, which must compile.
# A rejection counts only if the twin compiles (verify_general.sh, step 4).
def emit_controls(base, n, k, m, E, order, sideW, diamW):
    d = os.path.join(base, "negative_controls_interval", f"T{n}")
    os.makedirs(os.path.join(d, "twin"), exist_ok=True)
    ns = f"Chiquipoli.Family.T{n}"
    a3, b3 = E[3]
    v0, i0, j0 = order[0][:3]
    vlast = order[-1][0]
    alt = next(t for t in range(n) if sideW[t] != sideW[1])
    C = {
        "vertex_mismatch": ("the symbolic vertex 3 replaced by vertex 4",
                            f"vsOK {n} (VS.set 3 (vsAt VS 4)) 3", f"vsOK {n} VS 3"),
        "table_tampered": ("entry 5 of the vertex table replaced by entry 6",
                           "tabOK ((pointCS N0 J).1.widen rr) ((pointCS N0 J).2.widen rr) (tab.set 5 (tab.getD 6 default))",
                           "tabOK ((pointCS N0 J).1.widen rr) ((pointCS N0 J).2.widen rr) tab"),
        "vertex_enclosure_shrunk": ("the enclosure of vertex 5 shrunk to its upper end",
                                    "vdOK tab VS (vd.set 5 (let v := vd.getD 5 default; (⟨v.1.hi, v.1.hi⟩, ⟨v.2.hi, v.2.hi⟩))) 5",
                                    "vdOK tab VS vd 5"),
        "convexity_broken": ("vertices 2 and 3 exchanged", "sideOK ((vd.set 2 (vd.getD 3 default)).set 3 (vd.getD 2 default)) 1",
                             "sideOK vd 1"),
        "far_pair_claimed": ("no pair declared active: the active diameters of row 0 must then be < 1",
                             "farRowOK (fun _ _ => false) vd 0", f"farRowOK (gnAct {n}) vd 0"),
        "edge_dropped": (f"the active diameter ({a3}, {b3}) removed from E", f"actOK (E.eraseIdx 3) {a3}", f"actOK E {a3}"),
        "side_shape_wrong": (f"side 1 given the witness of side {alt}", f"sideWOK {n} {k} VS (sideW.set 1 (sideW.getD {alt} default)) 1",
                             f"sideWOK {n} {k} VS sideW 1"),
        "diameter_shape_wrong": ("diameter 0 given its witness mirrored",
                                 "diamWOK VS E (diamW.set 0 (let w := diamW.getD 0 default; ⟨w.s, !w.mir, w.flip⟩)) 0",
                                 "diamWOK VS E diamW 0"),
        "root_bracket_swapped": ("the two ends of the root bracket exchanged", f"rootOK {k} tabHi tabLo tabU",
                                 f"rootOK {k} tabLo tabHi tabU"),
        "henneberg_unplaced": (f"the first Henneberg step joined to vertex {vlast}, not yet placed",
                               f"henOK BARS [0, 1] (order.set 0 ({v0}, {vlast}, {j0}))", "henOK BARS [0, 1] order"),
        "henneberg_degenerate": ("a Henneberg step with its two bars on the same vertex",
                                 f"detOK vd [({v0}, {i0}, {i0})]", f"detOK vd [({v0}, {i0}, {j0})]"),
        "pin_stress_wrong": ("the pinned bar's stress claimed to be exactly 0",
                             "pinFIOK vd (sd.set 0 ⟨0, 0⟩) BL (knownAfter (ex.map (·.1)) steps) 0 1 pb",
                             "pinFIOK vd sd BL (knownAfter (ex.map (·.1)) steps) 0 1 pb"),
    }
    for name, (what, bad, good) in C.items():
        for sub_, stmt in (("", bad), ("twin", good)):
            role = ("NEGATIVE CONTROL — must NOT compile: " + what) if not sub_ else \
                   ("TWIN of the control of the same name — must compile: the same check on the true data")
            txt = (f"/-\nAUTO-GENERATED by `lean/generators/family/gen_trig.py {n}` — do not edit by hand.\n\n"
                   f"{role}.\n-/\nimport ChiquipoliFamily.Interval.T{n}.Data\n\nset_option maxHeartbeats 0\n"
                   f"set_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen Chiquipoli.Family.Trig FI\n\n"
                   f"theorem {name} : {stmt} = true := by decide +kernel\n\nend {ns}\n")
            open(os.path.join(d, sub_, f"{name}.lean"), "w").write(txt)


if __name__ == "__main__":
    main()
