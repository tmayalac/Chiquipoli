# Chiquipoli — interval and exact verification package for $A_{16}$

Supplementary computational material for the article *First Order Geometry of
Equilateral Small Polygons*, which cites this package as **[AH26]**.

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
| Unique constructor root | interval Newton, plus monotonicity on the whole search interval | $0 \notin F'$, $N(Z)\subset\mathrm{int}\,Z$ |
| 16 side + 15 active-diameter equalities | exact division in $\mathbb Q[c]$ | zero remainder, no rounding |
| Side length $\ell$, perimeter $16\ell$ | enclosure over the root box | widths $< 2\times10^{-30}$ and $< 3.19\times10^{-29}$ |
| Strict convexity (224 support determinants) | outward-rounded evaluation | $\geq 0.0074882049306989244$ |
| Exact active graph (105 inactive pairs) | outward-rounded evaluation | $\delta_{\mathrm{inact}} \geq 0.0080997106581357295$ |
| Positive multipliers | Krawczyk, plus algebraic gauge recovery | $\min\lambda \geq 0.0918667776833353997$ |
| $\mathrm{rank}\, D(e,d) = 30$ | preconditioned regularity test | $\lVert \mathrm{Id}-CM\rVert_\infty \leq 1.42\times10^{-25}$ |
| Box nesting | interval containment | $Z_{\mathrm{root}} \subset \mathrm{int}\, Z_{\mathrm{cert}}$ |

The certified object is identified with the published one by computation:
`test/fixtures/optigon_reference.jl` vendors the upstream OPTIGON general $n=2^s$
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

Theorem 3.5 and Theorem 6.3 used to be listed here. They no longer are:
`Chiquipoli.Feasible.A16_locally_maximal` proves, kernel-checked and
`sorry`-free, that the configuration built from the unique constructor root in
the bracket is a strictly convex equilateral small hexadecagon and a strict
local maximiser of the perimeter modulo orientation-preserving Euclidean
motions. `Feasible.thm_3_5` is the general statement. See
`docs/guide/theorem-3.5-formalisation.md`.

- **Global optimality.** $A_{16}$ is shown to be a strict *local* maximiser of
  perimeter, modulo orientation-preserving Euclidean motions. Whether it is
  globally optimal among convex equilateral small hexadecagons is not addressed.
- **That the certified object is the polygon of the literature.** That is an
  attribution, checked separately by running the original OPTIGON constructor
  and comparing coordinates; see `docs/guide/provenance-mapping.md`.

`docs/guide/scope-and-limitations.md` states the full scope, and `docs/audits/referee-report.md` is our
own adversarial review of this package.

---

## Running it

### What you need

| Tool | Needed for | macOS | Linux | Windows |
|---|---|---|---|---|
| Julia 1.12 | everything in Julia | `brew install juliaup`, then `juliaup add 1.12` | `curl -fsSL https://install.julialang.org \| sh` | `winget install julia -s msstore` |
| `make` | the short commands below (optional) | `xcode-select --install` | usually present; else `sudo apt install make` | not needed: use the right-hand column |
| elan (Lean) | the Lean layer only | `curl https://elan.lean-lang.org/elan-init.sh -sSf \| sh` | same as macOS | [elan installer for Windows](https://github.com/leanprover/elan) |
| bash, git, python3 | the Lean checks, the mutation harness, log archiving | preinstalled | preinstalled | WSL (recommended) or Git Bash |

The exact dependency versions are pinned in `Manifest.toml`, resolved by Julia
1.12, which reproduces the recorded environment bit for bit; every recorded
certificate was produced with it. Julia 1.10 and 1.11 also work, but not with
this Manifest (Pkg cannot instantiate a 1.12 Manifest on older Julia): delete
`Manifest.toml` first so Pkg re-resolves from `Project.toml`. CI runs the test
suite, the certificate and the literature benchmark that way on both.

Once, after cloning, from the repository root (same command on every system):

```
julia --project=. -e "using Pkg; Pkg.instantiate()"
```

### In one command

```bash
make check                 # quick: Julia only, ~5 min, writes nothing
make check-all             # everything, in order, and refreshes every record in results/ (~30 min, 16 GB)
make check-lean            # both Lean layers, verified and recorded
make check-case N=32       # one case: N = 4, 6, 8 (certifier) or 16, 32, 64 (certifier, Lean, stress)
```

Every stage runs even if an earlier one fails, and the run ends with a table
of PASS, FAIL and SKIP per stage (logs in `logs/check_all/`, not tracked). The
mutation check and the harness part of the stress test edit tracked files and
restore them from git, so on a dirty tree they are *skipped*, never counted as
passed, and the verdict is then `INCOMPLETE`, not `ALL CHECKS PASS`. Commit
first for a full run.

### Every command

All commands run from the repository root. `make` is a shortcut; the
right-hand column is what it runs, and works the same in a macOS or Linux
terminal and in Windows PowerShell.

| What it does | macOS / Linux | Without `make` (any system) |
|---|---|---|
| Run the test suite (714 assertions) | `make test` | `julia --project=. test/runtests.jl` |
| **The A16 certificate** → `results/a16_certificate.toml` | `make verify` | `julia --project=. pipeline/certify_a16.jl` |
| The literature benchmark (n = 4, 6, 8, 16, 32, 64 and 3 broken controls) → `results/validation_certificate.toml` | `make literature` | `julia --project=. pipeline/certify_literature.jl` |
| One literature case only (`4`, `6`, `8`, `16`, `32`, `64`, `neg`, or a name) | — | `julia --project=. pipeline/certify_literature.jl 8` |
| The nominal configuration, uncertified | `make nominal` | `julia --project=. pipeline/stages/01_nominal_configuration.jl` |
| Download the Mathlib cache (once, about 7 GB) | `make lean-cache` | `cd lean`, then `lake exe cache get` |
| The five Lean checks | `make lean` | `cd lean`, then `./verify.sh` (bash) |
| The Lean checks, recorded → `results/lean_certificate.toml` | `make lean-certificate` | `julia --project=. pipeline/record_lean_certificate.jl` (bash) |
| The same five checks for the family layer (A16, A32, A64) | `make lean-family` | `cd lean`, then `./verify_family.sh` (bash) |
| The family checks, recorded → `results/lean_family_certificate.toml` | `make lean-family-certificate` | `julia --project=. pipeline/record_lean_family_certificate.jl` |
| Does that record still describe the tree? (hashes only, seconds) | `make lean-family-record` | `julia --project=. pipeline/record_lean_family_certificate.jl --check` |
| One case of the family in Lean (a partial run) | `make lean-family-case N=32` | `cd lean`, then `FAMILY_CASES=32 ./verify_family.sh` |
| One case of the family, planted defects | `make stress-case N=32` | `STRESS_CASES=32 bash tools/stress_family.sh generator`, then `... lean` |
| One case of the literature benchmark | `make literature-case N=8` | `julia --project=. pipeline/certify_literature.jl 8` |
| The article against the certificates | `make paper-check` | `julia --project=. pipeline/check_paper.jl` |
| Plant 16 defects; the checks must reject each | `make mutation-check` | `bash tools/mutation_check.sh` (needs a clean git tree) |
| Stress test of the family layer: 24 generator defects, each refused by the generator AND by Lean; 11 harness defects | `make stress-family` | `bash tools/stress_family.sh all` (the harness part needs a clean git tree) |
| Archive the latest log, read-only | `make archive-log` | `bash tools/archive_log.sh logs/final_run.txt` |
| List the targets | `make help` | — |

`make verify` also saves the full output to `logs/final_run.txt`. Without
`make`, add `| tee logs/final_run.txt` on macOS or Linux, or
`| Tee-Object -FilePath logs/final_run.txt` in PowerShell 7.

The article itself is not distributed, so `make paper` has nothing to compile
in a fresh clone, and `make paper-check` checks the certificates, the source
hashes and the claims about Lean, and reports the article checks as skipped
(`PARTIAL`), never as passed.

### Notes for Windows

- **The Julia side runs natively.** Everything in the table that starts with
  `julia` works as written in PowerShell or `cmd`; forward slashes in paths are
  fine.
- **Use PowerShell 7** (`winget install Microsoft.PowerShell`) if you save the
  log with `Tee-Object`. Windows PowerShell 5.1 writes UTF-16, which
  `tools/archive_log.sh` cannot read.
- **The rows marked (bash)** need a bash shell, because `lean/verify.sh` and
  the tools are bash scripts. The simplest route is WSL (`wsl --install`, then
  follow the Linux column inside it, where `make` also works). Git Bash works
  for the Lean checks; the mutation harness also needs `python3` on the PATH.
- The continuous integration runs on Linux, and everything was developed on
  macOS. Windows is not exercised by CI.

### What a run looks like

`make verify` is a single non-interactive run with no tuning between its
steps. Two operators adapt inside a step, deterministically and without
affecting what is proved: the root step tries the radii `1e-30, …, 1e-26` and
accepts the first that passes (it is `1e-30`), and the Krawczyk step inflates
its box by factors of ten until the inclusion holds. Whatever box is accepted,
the conclusion is a proof. It completes in **under six seconds**, so the
certificate can be re-executed rather than taken on trust. It prints a
provenance header (commit, versions, per-file SHA256), then each gate, then:

```
FINAL FIRST-ORDER CERTIFICATE: CERTIFIED
```

## The Lean layer

An independent formalisation in Lean 4, checked against Mathlib, re-proves the
exact algebra and the positivity layer by kernel-checked rational arithmetic —
no interval arithmetic, no floating point.

Run it with `make lean-cache` once and then `make lean` (commands for every
system are in the table above). The five checks are: the development builds; no source admits a goal with
`sorry`; all 108 audited theorems depend only on Lean's three standard axioms;
26 deliberately false variants **fail** to compile, so the true statements
are not vacuous; and seven generated files reproduce byte for byte from the
Julia source, so the Lean layer cannot silently drift from the certified
arithmetic.

Beyond the eight gates, the Lean layer carries the article's **Theorem 3.5 in
full** — stated for arbitrary $n$ (`thm_3_5`), with Lemma 3.4 obtained from
Mathlib's implicit function theorem applied to the nonlinear slice map itself —
and instantiates it twice: at $A_{16}$, with both hypotheses discharged from the
certified data (`A16_locally_maximal`, the article's Theorem 6.3), and at the
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

This plants 16 known defects and requires the verification to reject each
one: eleven that the Julia suite must reject — a transcription error in the
constructor, one in the constructor equation, a sign error in one vertex, one
digit of the root literal, one wrong active edge, a Krawczyk enclosure rebuilt
with round-to-nearest instead of outward rounding, and a derivative `Fprime`
that is wrong but keeps its sign (interval Newton still passes with it; only
the chain-rule test against `Fc` catches it), the root-uniqueness gate dropped
from the verdict, and three in the Bingane–Audet
family (a sign error in the generic constructor that only exists for n ≥ 32,
one digit of the A64 root, one wrong A32 active edge); and five weakenings of the Lean
layer — an admitted
goal, an unresolvable name in the axiom audit, a deleted negative control, a
wrong factor in the bridge tying the Theorem 3.5 layer to the certified
arithmetic, and one digit off in the tight root bracket — which `verify.sh`
must reject. Each is restored afterwards, and the run
asserts the working tree comes back clean.

The first three Lean mutations were all reported as PASS before the harness
was fixed; they are in the script so that failure mode cannot return unnoticed.

It does not prove the harness complete. It detects blindness to the mutations
someone thought of. A hole nobody imagined stays invisible — which is exactly
what those five were until they were looked for.

The family layer (A16, A32, A64) has its own stress test, `make stress-family`.
Its certificate has two lines of defence — the generator checks every margin
in exact arithmetic before writing Lean, and Lean re-proves everything — and
the stress test checks that **each one alone** is enough: eight kinds of
generator defect (a vertex centre off by 10⁴ρ, a reversed support line, an
active diameter listed as inactive, a side that needs `Fc` proved for every c,
a degenerate Henneberg step, Cramer's rule with a sign dropped, swapped root
signs, a derivative bound that is false) are planted in each case. With the
pre-checks on, the generator must refuse all 24; with them switched off, Lean
must reject all 24, with every error inside the planted declaration and every
upstream module identical to the certified one. A third part sabotages
`verify_family.sh` itself (11 ways) and requires the responsible step to fail.
Each case also carries ten negative controls, each paired with a *twin* — the
same proof of the true statement — that must compile, so a control cannot be
rejected for an accidental reason. Details: `lean/ChiquipoliFamily/README.md`.

---

## Repository map

The package is two independent layers that meet at one point. **Julia is the
engine**: it computes the certificate by interval arithmetic and exact algebra.
**Lean is the verifier**: it re-proves the same facts in the kernel, with no
floating point, and proves the theorem they feed. The meeting point is
`lean/generators/`, which writes Lean files from the Julia exact arithmetic;
`lean/verify.sh` requires them to reproduce byte for byte.

```
src/                          THE ENGINE: a library, no side effects
  A16Certificate.jl             the A16 module: exports and includes
  a16/
    data.jl                     active diameter graph, the minor, the root literal
    guarantees.jl               _lit and assert_guaranteed: keeping IA's flag live
    constructor.jl              F, F', the sixteen vertices, the side length
    geometry.jl                 support determinants, inactive pairs
    linear_algebra.jl           Jacobian D(e,d), regularity test, Krawczyk
    exact_algebra.jl            Q[c]: Chebyshev reduction, Fc, exact divisions
  ExactIdentity.jl              exact identities for any n (Q(c,s) arithmetic)
  SmallPolygons.jl              the general certifier (n = 4, 6, 8, 16, 32, 64)

pipeline/                     THE CERTIFICATES: programs that write results/
  certify_a16.jl                make verify      -> results/a16_certificate.toml
  certify_literature.jl         make literature  -> results/validation_certificate.toml
  record_lean_certificate.jl    make lean-certificate -> results/lean_certificate.toml
  check_paper.jl                make paper-check: the article against all three
  stages/                       the six steps of certify_a16.jl, in order
    01_nominal_configuration.jl   the configuration, uncertified
    02_certify_root.jl            Prop 6.2(1): interval Newton, uniqueness
    03_certify_geometry.jl        Prop 6.2(3)-(4): convexity, inactive margin
    04_certify_rank.jl            Prop 6.2(6): rank D(e,d) = 30
    05_certify_multipliers.jl     Prop 6.2(5): positive multipliers
    06_prove_exact_identities.jl  Lemma 6.1: the 31 equalities, exactly

cases/                        inputs of the literature certificate: one
                              candidate.jl per case, and 3 broken controls;
                              exact_coords.jl: exact coordinates, including
                              the Bingane-Audet constructor for any n = 2^s
test/                         make test: runtests.jl and one file per theme;
                              fixtures/ holds the vendored OPTIGON constructor
lean/                         THE VERIFIER (see lean/README.md)
  ChiquipoliLean/Theory/        Theorem 3.5 for any n
  ChiquipoliLean/Constructor/   the A16 constructor and its root
  ChiquipoliLean/Generated/     written by generators/, never by hand
  ChiquipoliLean/Instances/     the theory at A16 and at the square
  ChiquipoliFamily/             A32, A64 (and A16 again), a method that scales in n;
                                built and checked by verify_family.sh
  negative_controls/            26 false statements that must not compile
  negative_controls_family/     10 per family case, each with a twin that must compile
  generators/                   Julia -> Lean, the bridge between the layers
  verify.sh                     make lean: the five checks
results/                      the three certificates (TOML) and the article's tables
logs/                         final_run.txt; archive/ holds read-only copies
docs/                         guide/ (what is certified, and how), audits/ (records)
tools/                        mutation_check.sh, stress_family.sh, archive_log.sh, independent_check/
examples/                     two worked tutorials: the square, interval Newton
```

To find the code behind a statement of the article:

| The article says | Julia computes it in | Lean proves it in |
|---|---|---|
| Lemma 6.1, the 31 equalities | `pipeline/stages/06_prove_exact_identities.jl` | `Constructor/Identities.lean` |
| Prop 6.2(1), the root | `pipeline/stages/02_certify_root.jl` | `Constructor/RootExists.lean`, `SearchInterval.lean` |
| Prop 6.2(2), side length | `pipeline/certify_a16.jl` (`certify_side_length`) | `Constructor/SideLength.lean` |
| Prop 6.2(3), convexity | `pipeline/stages/03_certify_geometry.jl` | `Generated/Convexity.lean` |
| Prop 6.2(4), inactive margin | `pipeline/stages/03_certify_geometry.jl` | `Generated/InactiveMargin.lean`, `Diameter.lean` |
| Prop 6.2(5), multipliers | `pipeline/stages/05_certify_multipliers.jl` | `Generated/Multipliers.lean` |
| Prop 6.2(6), rank 30 | `pipeline/stages/04_certify_rank.jl` | `Generated/Rank.lean`, `Instances/A16Rank30.lean` |
| Theorem 3.5 | (not computed) | `Theory/FirstOrder.lean` … `Theory/FeasibleMain.lean` |
| Theorem 6.3, A16 is a strict local maximum | (not computed) | `Instances/A16LocalMax.lean` |
| Proposition 4.2, the square | (not computed) | `Instances/SquareLocalMax.lean` |

Lean paths are under `lean/ChiquipoliLean/`. `docs/guide/provenance-mapping.md`
goes through Section 6 of the article line by line.

## Where to start reading

1. `docs/guide/certificate-spec.md` — the canonical statement of what is certified.
2. `results/a16_certificate.toml` — the gates and values, machine-readable.
3. `docs/guide/provenance-mapping.md` — line-by-line mapping of code to the article's
   Section 6, per gate.
4. `docs/guide/scope-and-limitations.md` — the boundaries of every claim.

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
