# Independent check (mpmath, 50 digits; floating point, not a certificate) that the
# printed Propositions 1 and 2 of Bingane-Audet (arXiv:2105.10618v4, Section 4) give
# the polygons Z32, Z64 of this package. The formulas below are typed from the
# printed text, not from cases/exact_coords.jl. Run: python3 docs/audits/ba_propositions_check.py
# Expected: Z32 L = 3.14032023396656835667..., Z64 L = 3.14127521551138087450...,
# matching results/family/Z32.toml and Z64.toml (perimeter).
from mpmath import mp, mpf, sin, cos, pi, findroot, sqrt
mp.dps = 50
# Proposition 1, as printed: (2(sin5t - sin13t + sin14t) - sin15t)^2 + cos^2 15t = 4 sin^2(t/2), t in (0, pi/32)
f32 = lambda t: (2*(sin(5*t)-sin(13*t)+sin(14*t))-sin(15*t))**2 + cos(15*t)**2 - 4*sin(t/2)**2
t32 = findroot(f32, mpf('0.098174'))
print("Z32 t =", t32, " < pi/32:", t32 < pi/32, " pi/32 - t =", mp.nstr(pi/32 - t32, 5), " L =", 64*sin(t32/2))
# Proposition 2, as printed
def x51(t): return (sin(t)-sin(2*t)+sin(3*t)-sin(5*t)+sin(6*t)-sin(7*t)+sin(8*t)
    - sum((-1)**k*sin(k*t) for k in range(10,21)) + sin(22*t)-sin(23*t)+sin(25*t)-sin(26*t))
def y51(t): return (cos(t)-cos(2*t)+cos(3*t)-cos(5*t)+cos(6*t)-cos(7*t)+cos(8*t)
    - sum((-1)**k*cos(k*t) for k in range(10,21)) + cos(22*t)-cos(23*t)+cos(25*t)-cos(26*t))
def eqs(t, y):
    x16, y16 = x51(t)+sin(29*t), y51(t)+cos(29*t)
    x50, y50 = mpf(-1)/2, y
    x15, y15 = x50+cos(t), y50+sin(t)
    d = 2*sin(t/2)
    return [(x51(t)-x50)**2+(y51(t)-y50)**2-d**2, (x16-x15)**2+(y16-y15)**2-d**2]
# Newton from a single start can land on t = pi/60 > pi/64; scan the start in y instead.
sols = []
for y0 in [mpf(k)/20 for k in range(2, 20)]:
    try:
        t, y = findroot(eqs, (mpf('0.0490873533'), y0))
    except Exception:
        continue
    if 0 < t < pi/64 and all(abs(r) < mpf(10)**-40 for r in eqs(t, y)):
        if not any(abs(t-s[0]) < mpf(10)**-30 and abs(y-s[1]) < mpf(10)**-30 for s in sols):
            sols.append((t, y))
for t, y in sols:
    print("Z64 root in (0,pi/64): t =", mp.nstr(t, 30), " y =", mp.nstr(y, 30), " L =", mp.nstr(128*sin(t/2), 40))
