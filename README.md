# Chiquipoli — interval and exact verification package for $A_{16}$

Supplementary computational material for the article *First Order Geometry of
Equilateral Small Polygons*, which cites this package as **[AH26]**.

The package certifies, by rigorous interval arithmetic and exact rational
algebra, the computational hypotheses that the article's first-order criterion
consumes for the Bingane–Audet hexadecagon $A_{16}$.

## Start here

```
julia --project=. chiquipoli.jl            # what is certified, read from results/ (seconds)
julia --project=. chiquipoli.jl all        # re-run the certificates and the tests
julia --project=. chiquipoli.jl help       # every task
```

The first command prints, in tables, each result of the article with its
verdict and record, the hypotheses of Theorem 3.5 for $A_{16}$ gate by gate,
the data of $A_{16}$, $A_{32}$, $A_{64}$, the Lean layer, and whether every
record still matches the sources. `chiquipoli.jl` only presents: it reads
`results/` and runs the scripts below unchanged, and never writes a record.

---

## What is certified

The article's abstract criterion (Theorem 3.5) has exactly two hypotheses. This
package establishes both for $A_{16}$ (what else it carries, which the article
does not use, is under [Beyond the article](#beyond-the-article)):

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

The certified object is identified with the one the published code builds,
exactly. `cases/upstream/optigon/cstrt_audet_ngon.jl` is Bingane's OPTIGON
constructor, byte for byte (SHA-256 checked, MIT licence alongside), and
`cases/optigon_exact.jl` runs that file **unchanged, in exact arithmetic**: at
$n=16$ its vertices are $(\sin t\,X_k(c),Y_k(c))$ with exactly the polynomials of
the certificate, and its equation is exactly $F_c(\cos t)$. The certified
perimeter agrees with the value Bingane and Audet publish, $3.1352878881$, in
all ten decimals. A separate Lean development transcribes that file statement for
statement and proves the same identification in the kernel
(`Chiquipoli.Family.A16.published_locally_maximal`).

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
- **That the published code implements the construction described in the
  Bingane–Audet paper.** That the certified polygon is the one their code
  builds is established exactly (above); that their code is their
  construction is their attribution, as for any use of published software.

`docs/guide/scope-and-limitations.md` states the full scope, and `docs/audits/referee-report.md` is our
own adversarial review of this package.

## Beyond the article

The article concerns $A_{16}$, $A_{32}$ and $A_{64}$ (its Theorem A; the
explicit radius is for $A_{16}$). The package also carries, and checks on every
`make check-all`, results that the article does not state and its proofs do not
use:

- the same first-order certificate for $A_{128},\dots,A_{1024}$
  (`pipeline/certify_family.jl`, `results/family/`);
- Lean certificates for the published constructor at $A_{128}$ and $A_{256}$
  (the article uses those of $A_{16}$, $A_{32}$, $A_{64}$), and a Lean proof that
  for **every** $n = 16k$ the polygon it builds is a strict local maximiser
  (`lean/ChiquipoliFamily/`, `AllN/Main.lean`);
- a benchmark on the known optima $n = 4, 6, 8$ and three deliberately broken
  variants of $A_{16}$ (`pipeline/certify_literature.jl`);
- $Z_{32}$ and $Z_{64}$, the polygons of larger perimeter that Bingane and Audet
  report for $n = 32$ and $64$ (perimeters $3.1403202\ldots$ and
  $3.1412752\ldots$, against $3.1402461\ldots$ and $3.1412717\ldots$ for $A_{32}$
  and $A_{64}$): the same blocks as every candidate, including the exact
  identities (`cases/family/Z32/`, `Z64/`; `make z32`, `make z64`; records in
  `results/family/Z32.toml`, `Z64.toml`, nine gates each, `pipeline/certify_z.jl`, root uniqueness on (0, π/n)
  included; in Lean too).
  Not claimed, and said in each record: a published constructor to run unchanged
  and a Lean statement. They
  are rebuilt from their Propositions 1 and 2, not from OPTIGON, which ships only
  the $A_n$ constructor, so that they are the polygons of the paper is a
  comparison with the paper that no program makes. $Z_{64}$ has two unknowns,
  $t$ and $y$; the first equation is solved for $y$ in closed form, which leaves
  one root, and its exact identities are proved in $\mathbb Q[c,s,y]$ by a ring
  of the candidate's own (the engine of `src/ExactIdentity.jl` has no square
  roots). The paper gives no angle for the pendant edges of $Z_{64}$; the ones
  used here are those that make each of them a diameter, which the identities
  prove;
- **an independent cross-check** (`pipeline/independent/verify.py`, `make
  independent`): the numerical gates computed a second time, in Python's standard
  library, with its own integer interval arithmetic and no Julia, for $A_{16}$,
  $A_{32}$, $A_{64}$, $Z_{32}$ and $Z_{64}$ (`results/independent/`). For the
  $A_n$ it ports the vendored OPTIGON file line by line and agrees with the
  Julia records to every printed digit; it rejects its own six planted defects.
  It does not prove the equalities of the sides and diameters of $A_n$ (the Julia
  pipeline does, exactly) nor the uniqueness of the root on the search interval.

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
certificate was produced with it. `Project.toml` also admits Julia 1.10 and 1.11,
but not with this Manifest (Pkg cannot instantiate a 1.12 Manifest on older Julia):
delete `Manifest.toml` first so Pkg re-resolves from `Project.toml`. Those two
versions were exercised that way (test suite, certificate, literature benchmark) by
the CI workflows, which have since been removed; nothing in this repository runs
remotely, and the recorded results come from Julia 1.12 only.

Once, after cloning, from the repository root (same command on every system):

```
julia --project=. -e "using Pkg; Pkg.instantiate()"
```

### In one command

| What it does | macOS / Linux | Windows (Git Bash or WSL) |
|---|---|---|
| Quick check: Julia only, writes nothing | `make check` | `bash tools/check_all.sh quick` |
| Everything, in order, refreshing every record in `results/` (16 GB of memory) | `make check-all` | `bash tools/check_all.sh all` |
| Both Lean layers, verified and recorded | `make check-lean` | `bash tools/check_all.sh lean` |
| One case: N = 4, 6, 8 (certifier) or 16, 32, 64 (certifier, Lean, stress) | `make check-case N=32` | `bash tools/check_all.sh case 32` |
| One candidate, every layer: A16, A32, A64 | `make A16`, `make A32`, `make A64` | `bash tools/check_all.sh candidate 16` (32, 64) |
| One of the Z polygons, every check (suite, general certifier, 9-gate certificate, Python cross-check, planted defects and the Lean certificate of the polygon), minutes (Z64 in Lean: about an hour) | `make Z32`, `make Z64` (or `z32-complete`) | `bash tools/check_all.sh zcomplete 32` (64) |
| One of the Z polygons, its certificate and the Python cross-check, in seconds | `make z32`, `make z64` | `bash tools/check_all.sh z 32` (64) |
| One polygon, its Julia certificate only, in seconds (A16 … A1024; A1024 a few minutes) | `make a16`, `make a32`, …, `make a1024` | `bash tools/check_all.sh fast 256` |
| One polygon, every layer incl. Lean (Lean for A16 … A256; A512, A1024 end `INCOMPLETE`) | `make a16-complete`, …, `make a1024-complete` | `bash tools/check_all.sh candidate 256` |

`make A16`, `make A32` and `make A64` run the same stages for each candidate:
the Julia suite, the general certifier, the family certificate (ten gates,
among them the published OPTIGON source run unchanged in exact arithmetic), the
family Lean layer (the published constructor, eleven controls with twins,
regeneration), the generator and Lean stress tests, five planted defects in the
candidate's data and sources, and fifteen sabotages of the verifier in the
candidate's own files. A16 adds the article's two dedicated layers.

Every stage runs even if an earlier one fails, and the run ends with a table
of PASS, FAIL and SKIP per stage (logs in `logs/check_all/`, not tracked). The
mutation check and the harness part of the stress test edit tracked files and
restore them from git, so on a dirty tree, or in an extracted archive without
`.git`, they are *skipped*, never counted as passed, and the verdict is then
`INCOMPLETE`, not `ALL CHECKS PASS`. Commit first for a full run.

### Every command

All commands run from the repository root. The Julia commands are the same on
every system; in Windows they run natively in PowerShell (forward slashes are
fine). Commands marked **bash** are bash scripts: on Windows run them in Git
Bash or, better, WSL.

| What it does | macOS / Linux | Windows (PowerShell unless marked bash) |
|---|---|---|
| Install the pinned dependencies (once) | `julia --project=. -e "using Pkg; Pkg.instantiate()"` | same |
| Run the test suite (820 assertions; 821 with `OPTIGON_DIR` set) | `make test` | `julia --project=. test/runtests.jl` |
| **The A16 certificate** → `results/a16_certificate.toml` | `make verify` | `julia --project=. pipeline/certify_a16.jl \| Tee-Object -FilePath logs/final_run.txt` |
| The same, without writing any record | `CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_a16.jl` | `$env:CHIQUI_NO_RECORD="1"; julia --project=. pipeline/certify_a16.jl; Remove-Item Env:CHIQUI_NO_RECORD` |
| The family certificate of one candidate (ten gates) → `results/family/A32.toml` | `julia --project=. pipeline/certify_family.jl 32` | same |
| The literature benchmark (n = 4, 6, 8, 16, 32, 64 and 3 broken controls) → `results/validation_certificate.toml` | `make literature` | `julia --project=. pipeline/certify_literature.jl` |
| One literature case only (`4`, `6`, `8`, `16`, `32`, `64`, `neg`, or a name) | `make literature-case N=8` | `julia --project=. pipeline/certify_literature.jl 8` |
| The nominal configuration, uncertified | `make nominal` | `julia --project=. pipeline/stages/01_nominal_configuration.jl` |
| Compare with your own copy of OPTIGON, byte for byte | `OPTIGON_DIR=/path/to/optigon make test` | `$env:OPTIGON_DIR="C:\path\to\optigon"; julia --project=. test/runtests.jl` |
| What is certified, in tables, from the records | `make status` | `julia --project=. chiquipoli.jl` |
| Every record against the tree, the source hashes and the Lean layer | `make check-records` | `julia --project=. pipeline/check_records.jl` |
| Download the Mathlib cache (once, about 7 GB) | `make lean-cache` | `cd lean; lake exe cache get` |
| The five Lean checks of the A16 layer | `make lean` | bash: `cd lean && ./verify.sh` |
| The same, recorded → `results/lean_certificate.toml` | `make lean-certificate` | bash: `julia --project=. pipeline/record_lean_certificate.jl` |
| The five Lean checks of the family layer (A16, A32, A64) | `make lean-family` | bash: `cd lean && ./verify_family.sh` |
| The same, recorded → `results/lean_family_certificate.toml` | `make lean-family-certificate` | bash: `julia --project=. pipeline/record_lean_family_certificate.jl` |
| Does that record still describe the tree? (hashes only, seconds) | `make lean-family-record` | `julia --project=. pipeline/record_lean_family_certificate.jl --check` |
| One case of the family in Lean (a partial run) | `make lean-family-case N=32` | bash: `cd lean && FAMILY_CASES=32 ./verify_family.sh` |
| The general Lean theorem of the family (one proof for every n = 16k), five checks on A16 … A256 | `make lean-general` | bash: `cd lean && ./verify_general.sh` |
| The same, one case | `make lean-general-case N=256` | bash: `cd lean && TRIG_CASES=256 ./verify_general.sh` |
| Plant 16 defects in the A16 layers, and 5 per candidate in the family certificates | `make mutation-check` | bash: `tools/mutation_check.sh` (needs a git clone, clean) |
| The family stress test: 63 planted defects | `make stress-family` | bash (WSL): `tools/stress_family.sh all` |
| One case of the family, planted defects | `make stress-case N=32` | bash (WSL): `STRESS_CASES=32 tools/stress_family.sh generator` |
| Archive the latest log, read-only | `make archive-log` | bash: `tools/archive_log.sh logs/final_run.txt` |
| List the targets | `make help` | — |

`make verify` also saves the full output to `logs/final_run.txt`; without
`make`, add `| tee logs/final_run.txt` on macOS or Linux (the PowerShell form is
in the table). `CHIQUI_NO_RECORD=1` works the same for
`pipeline/certify_literature.jl` and `pipeline/certify_family.jl`.

`make check-records` needs nothing outside this repository: it checks every
certificate verdict, the provenance and source hashes of every record, the
published bounds, the Lean layer and the family records against the tree.

### Notes for Windows

- **The Julia side runs natively.** Every command in the tables that starts
  with `julia` works in PowerShell or `cmd`.
- **Use PowerShell 7** (`winget install Microsoft.PowerShell`) if you save the
  log with `Tee-Object`: Windows PowerShell 5.1 writes UTF-16, which
  `tools/archive_log.sh` cannot read.
- **The bash scripts** (`lean/verify*.sh` and everything in `tools/`) need a
  bash shell. The recommended route is WSL (`wsl --install`): install Julia and
  elan inside it and follow the macOS / Linux column, where `make` works too.
  Git Bash runs the Julia-only commands and `lean/verify.sh`; the stress test
  (`tools/stress_family.sh`) uses `ps` and `pgrep` for its memory cap and needs
  WSL.
- Everything was developed and verified on macOS, and the continuous
  integration runs on Linux. **Windows has not been tested** by us; the
  Windows column is what should work, not what was run.

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
`sorry`; all 137 audited theorems depend only on Lean's three standard axioms;
32 deliberately false variants **fail** to compile, so the true statements
are not vacuous; and nine generated files reproduce byte for byte from the
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

This plants 18 known defects and requires the verification to reject each
one: thirteen that the Julia suite must reject — a transcription error in the
constructor, one in the constructor equation, a sign error in one vertex, one
digit of the root literal, one wrong active edge, a Krawczyk enclosure rebuilt
with round-to-nearest instead of outward rounding, and a derivative `Fprime`
that is wrong but keeps its sign (interval Newton still passes with it; only
the chain-rule test against `Fc` catches it), the root-uniqueness gate dropped
from the verdict, and three in the Bingane–Audet
family (a sign error in the generic constructor that only exists for n ≥ 32,
one digit of the A64 root, one wrong A32 active edge), and a flipped sign in the derivative of the defining
equation of Z32 and of Z64 (their certificate would accept it, as with `Fprime`;
only the finite-difference test catches it); and five weakenings of the Lean
layer — an admitted
goal, an unresolvable name in the axiom audit, a deleted negative control, a
wrong factor in the bridge tying the Theorem 3.5 layer to the certified
arithmetic, and one digit off in the tight root bracket — which `verify.sh`
must reject. Each is restored afterwards, and the run
asserts the working tree comes back clean.

It also plants nine further defects in Z32 and Z64 (`tools/mutation_check.sh z`: a
digit of the root, one active edge, one index of the construction, one of the
defining equation, one pendant angle of Z64), which `pipeline/certify_z.jl` must
reject, and which the figure above does not count.

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
`verify_family.sh` itself (11 ways) and the transcription of the published
constructor (4 ways), and requires the responsible check to fail.
Each case also carries eleven negative controls, each paired with a *twin* — the
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
  certify_family.jl             the family certificate of A16 ... A1024 -> results/family/A<n>.toml
  certify_radius.jl             make radius: an explicit radius for A16 -> results/radius_certificate.toml
  family_table.jl               the family table (not in the article), from results/family/
  record_lean_certificate.jl    make lean-certificate -> results/lean_certificate.toml
  record_lean_family_certificate.jl  make lean-family-certificate -> results/lean_family_certificate.toml
  check_records.jl              make check-records: every record against the tree and the Lean layer
  independent/verify.py         make independent: A16 A32 A64 Z32 Z64 by a second implementation (Python)
  stages/                       the six steps of certify_a16.jl, in order
    01_nominal_configuration.jl   the configuration, uncertified
    02_certify_root.jl            Prop 6.2(1): interval Newton, uniqueness
    03_certify_geometry.jl        Prop 6.2(3)-(4): convexity, inactive margin
    04_certify_rank.jl            Prop 6.2(6): rank D(e,d) = 30
    05_certify_multipliers.jl     Prop 6.2(5): positive multipliers
    06_prove_exact_identities.jl  Lemma 6.1: the 31 equalities, exactly

cases/                        THE INPUTS: one candidate.jl per polygon
  family/A16 ... A1024/         the Bingane-Audet family (FAMILY_N)
  literature/                   n4_regular, n6_reinhardt, n8_ahmp2004
  family/Z32, Z64/              the Bingane-Audet polygons of larger perimeter (certify_z.jl)
  negative/                     3 broken controls, which must be rejected
  upstream/optigon/             OPTIGON's cstrt_audet_ngon.jl, byte for byte (MIT)
  exact_coords.jl               exact coordinates, the family lists, the constructor for any n = 8m
  optigon_exact.jl              runs the upstream file unchanged, in exact arithmetic
test/                         make test: runtests.jl and one file per theme;
                              fixtures/ holds the vendored OPTIGON constructor
lean/                         THE VERIFIER (see lean/README.md)
  ChiquipoliLean/Theory/        Theorem 3.5 for any n
  ChiquipoliLean/Constructor/   the A16 constructor and its root
  ChiquipoliLean/Generated/     written by generators/, never by hand
  ChiquipoliLean/Instances/     the theory at A16 and at the square
  ChiquipoliFamily/             the family; the published constructor (Optigon.lean)
    Polynomial/A16 A32 A64/       per-case polynomial certificates (verify_family.sh)
    Interval/                     one theorem for every n = 16k, kernel-checked data
      T16 ... T256/                 per case (verify_general.sh)
    AllN/                         the proof for every n = 16k, no data:
                                  Main.published_all_n (see AllN/README.md)
  negative_controls/            26 false statements that must not compile
  negative_controls_family/     11 per polynomial case, each with a twin that must compile
  negative_controls_interval/   12 per interval case, each with a twin that must compile
  generators/                   Julia/Python -> Lean, the bridge between the layers
  verify.sh                     make lean: the five checks
results/                      every record (TOML; see results/README.md) and the article's tables
logs/                         final_run.txt; archive/ holds read-only copies
docs/                         guide/ (what is certified, and how), audits/ (records)
tools/                        check_all.sh, mutation_check.sh, stress_family.sh, archive_log.sh,
                              independent_check/
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
| Theorem 6.4, an explicit radius | `pipeline/certify_radius.jl` | `Instances/A16Radius.lean` (`A16_radius`, Lean's own constants); `Instances/A16RadiusPrinted.lean` (`A16_radius_printed`, the printed argument and constants) |
| Proposition 4.2, the square | (not computed) | `Instances/SquareLocalMax.lean` |

Lean paths are under `lean/ChiquipoliLean/`. `docs/guide/provenance-mapping.md`
goes through Section 6 of the article line by line.

## Where to start reading

0. `docs/article/README.md` — each row of the article's Table 3 (and Table 4 for A32, A64), mapped to its script, its record field and its Lean declaration.
1. `docs/guide/certificate-spec.md` — the canonical statement of what is certified.
2. `results/a16_certificate.toml` — the gates and values, machine-readable.
3. `docs/guide/provenance-mapping.md` — line-by-line mapping of code to the article's
   Section 6, per gate.
4. `docs/guide/scope-and-limitations.md` — the boundaries of every claim.

## Reproducibility

Every artifact records the Git commit it was produced at, whether the working
tree was clean, the language and library versions, and a SHA256 per load-bearing
source file. The archived log declares the same commit as the certificates, and
`make check-records` fails if the log and the records do not all declare one
commit from a clean tree.

Exact equalities are never inferred from an interval evaluation that contains
zero. They are proved by exact polynomial reduction with zero remainder, in
integer arithmetic.

## Citation

If you use this package, please cite the accompanying article together with this
software, giving the version you used. The version the article cites is the one
in `Project.toml` and `CITATION.cff`, and its Git tag is `v<version>`.

## License

MIT. See `LICENSE`.
