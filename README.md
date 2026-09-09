# Chiquipoli — interval and exact verification package for $A_{16}$

Supplementary computational material for the article *Stability of Equilateral
Small Polygons*, which cites this package as **[AH26]**.

The package certifies, by rigorous interval arithmetic and exact rational
algebra, the computational hypotheses that the article's first-order criterion
consumes for the Bingane–Audet hexadecagon $A_{16}$.

---

## What is certified

The article's abstract criterion (Theorem 3.5) has exactly two hypotheses. This
package establishes both for $A_{16}$, and nothing else:

1. **A multiplier identity holds with every active-diameter multiplier
   strictly positive.**
2. **The active equality space consists only of infinitesimal Euclidean
   motions**, $\mathcal I_{\mathrm{eq}} = R_{\mathrm{eq}}$.

Eight gates, all `CERTIFIED` or `PROVEN`:

| Gate | Method | Certified bound |
|---|---|---|
| Unique constructor root | interval Newton, plus monotonicity on the whole search interval | $0 \notin F'$, $N(Z)\subset\operatorname{int}Z$ |
| 16 side + 15 active-diameter equalities | exact division in $\mathbb Q[c]$ | zero remainder, no rounding |
| Side length $\ell$, perimeter $16\ell$ | enclosure over the root box | widths $< 2\times10^{-30}$ and $< 3.19\times10^{-29}$ |
| Strict convexity (224 support determinants) | outward-rounded evaluation | $\geq 0.0074882049306989244$ |
| Exact active graph (105 inactive pairs) | outward-rounded evaluation | $\delta_{\mathrm{inact}} \geq 0.0080997106581357295$ |
| Positive multipliers | Krawczyk, plus algebraic gauge recovery | $\min\lambda \geq 0.0918667776833353997$ |
| $\operatorname{rank} D(e,d) = 30$ | preconditioned regularity test | $\lVert \mathrm{Id}-CM\rVert_\infty \leq 1.42\times10^{-25}$ |
| Box nesting | interval containment | $Z_{\mathrm{root}} \subset \operatorname{int} Z_{\mathrm{cert}}$ |

The certified object is identified with the published one by computation:
`test/optigon_reference.jl` vendors the upstream OPTIGON general $n=2^s$
constructor (URL, retrieval date, upstream SHA256 and MIT attribution recorded
in the file), and the suite requires it to reproduce the $n=16$ specialisation
— the root, all sixteen vertices, the diameter graph, equilaterality and the
perimeter. So "the polygon this package certifies" and "the polygon
Bingane–Audet published" are checked to be the same object, not assumed to be.

Every one of those enclosures also carries IntervalArithmetic's own
`isguaranteed` flag, and each gate asserts it (`assert_guaranteed`). The flag is
cleared as soon as a bare floating-point value enters a computation, so a live
flag is the library's statement that it still vouches for the enclosure — a
machine-checked version of what would otherwise be a hand audit of every
numeric literal in the source. The pipeline emits no `NG`-tagged value.

## What is *not* certified

Theorem 3.5 and Theorem 6.4 used to be listed here. They no longer are:
`Chiquipoli.Feasible.A16_locally_maximal` proves, kernel-checked and
`sorry`-free, that the configuration built from the unique constructor root in
the bracket is a strictly convex equilateral small hexadecagon and a strict
local maximiser of the perimeter modulo orientation-preserving Euclidean
motions. `Feasible.thm_3_5` is the general statement. See
`docs/theorem-3.5-formalisation.md`.

- **Global optimality.** $A_{16}$ is shown to be a strict *local* maximiser of
  perimeter, modulo orientation-preserving Euclidean motions. Whether it is
  globally optimal among convex equilateral small hexadecagons is not addressed.
- **That the certified object is the polygon of the literature.** That is an
  attribution, checked separately by running the original OPTIGON constructor
  and comparing coordinates; see `docs/provenance-mapping.md`.

`docs/scope-and-limitations.md` states the full scope, and `docs/referee-report.md` is our
own adversarial review of this package.

---

## Quick start

Julia 1.10 or later. The exact dependency versions are pinned in
`Manifest.toml`, so the environment reproduces bit for bit.

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate()'
make test        # the test suite
make verify      # the certificate; writes results/a16_certificate.toml
```

`make verify` is a single non-interactive run with no search or tuning between
its steps. It completes in **under six seconds**, so the certificate can be
re-executed rather than taken on trust. It prints a provenance header (commit,
versions, per-file SHA256), then each gate, then:

```
FINAL FIRST-ORDER CERTIFICATE: CERTIFIED
```

Other targets:

```bash
make literature  # re-certify the solved n=4,6,8 cases and the negative controls
make nominal     # print the nominal configuration only, no certificate
make help        # all targets
```

## The Lean layer

An independent formalisation in Lean 4, checked against Mathlib, re-proves the
exact algebra and the positivity layer by kernel-checked rational arithmetic —
no interval arithmetic, no floating point.

```bash
make lean-cache  # once: prebuilt Mathlib oleans, about 7 GB
make lean        # the five checks
```

The five checks are: the development builds; no source admits a goal with
`sorry`; all 77 headline theorems depend only on Lean's three standard axioms;
eighteen deliberately false variants **fail** to compile, so the true statements
are not vacuous; and seven generated files reproduce byte for byte from the
Julia source, so the Lean layer cannot silently drift from the certified
arithmetic.

Beyond the eight gates, the Lean layer carries the article's **Theorem 3.5 in
full** — stated for arbitrary $n$ (`thm_3_5`), with Lemma 3.4 obtained from
Mathlib's implicit function theorem applied to the nonlinear slice map itself —
and instantiates it twice: at $A_{16}$, with both hypotheses discharged from the
certified data (`A16_locally_maximal`, the article's Theorem 6.4), and at the
square of Section 4 (`square_strict_local_max`, its Proposition 4.2). Its
boundary is stated above and in `lean/README.md`.

Scope, and what Lean does *not* prove, is in `lean/README.md`.

## Showing the checks can fail

A suite that has never failed is not a tested suite. Every check above asserts
that something holds; none of them, on its own, shows it is capable of
rejecting anything.

```bash
make mutation-check
```

This plants nine known defects and requires the verification to reject each
one: four realistic transcription errors — in the constructor, in the
constructor equation, in the root literal and in the active graph — which the
Julia suite must reject; and five weakenings of the Lean layer — an admitted
goal, an unresolvable name in the axiom audit, a deleted negative control, a
wrong factor in the bridge tying the Theorem 3.5 layer to the certified
arithmetic, and one digit off in the tight root bracket — which `verify.sh`
must reject. Each is restored afterwards, and the run
asserts the working tree comes back clean.

All three Lean mutations were reported as PASS before the harness was fixed;
they are in the script so that failure mode cannot return unnoticed.

It does not prove the harness complete. It detects blindness to the mutations
someone thought of. A hole nobody imagined stays invisible — which is exactly
what those five were until they were looked for.

---

## Repository layout

| Path | Contents |
|---|---|
| `src/` | the constructor, exact $\mathbb Q[c]$ identities, interval geometry |
| `scripts/` | the numbered certificate stages, `run_all.jl` drives them |
| `test/` | the test suite |
| `lean/` | the Lean 4 formalisation and its verification script |
| `results/` | machine-readable certificates and validation output |
| `logs/` | the execution record, archived read-only under a UTC name |
| `examples/` | worked cases: the square, the literature polygons, negative controls |
| `tools/` | an independent SymPy re-derivation of the exact identities |
| `docs/` | scope, limitations, theory audits, literature validation |

## Where to start reading

1. `docs/certificate-spec.md` — the canonical statement of what is certified.
2. `results/a16_certificate.toml` — the gates and values, machine-readable.
3. `docs/provenance-mapping.md` — line-by-line mapping of code to the article's
   Section 6, per gate.
4. `docs/scope-and-limitations.md` — the boundaries of every claim.

## Reproducibility

Every artifact records the Git commit it was produced at, whether the working
tree was clean, the language and library versions, and a SHA256 per load-bearing
source file. The archived log declares the same commit as the certificate.

Exact equalities are never inferred from an interval evaluation that contains
zero. They are proved by exact polynomial reduction with zero remainder, in
integer arithmetic.

## Citation

If you use this package, please cite the accompanying article together with this
software, giving the version you used.

## License

MIT. See `LICENSE`.
