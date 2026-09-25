# Changelog

All notable changes to this project are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [1.1.1] — 2026-09-24

The version the article cites. No certified result changed; v1.1.0 is the same
certificate. This release adds what the article's revised identification
paragraph relies on, and one more consistency check.

- **The chain to the article's own objects is exact at n = 16.** The test
  *the published OPTIGON source, run unchanged, is exactly the certified A_n*
  now also requires the following. The upstream file, run in exact arithmetic
  at n = 16, gives vertices `(sin t · X_k(c), Y_k(c))` with exactly the
  polynomials `X_k`, `Y_k` of the A16 certificate. Those are the polynomials of
  Lemma 6.1 and the source of Lean's `Generated/Polynomials.lean`. Its equation
  must also be exactly the article's `F_c(cos t)`, with leading coefficient
  4096. Until now this link was numerical, to 1e-70; the article now states it
  exactly. The suite has 772 assertions.
- **`make paper-check` checks every Lean theorem the article names.** A name
  printed in `\texttt` or `\nolinkurl` must exist as a theorem, in the right
  case for `Chiquipoli.Family.A<n>.…`. The article now names
  `Chiquipoli.Family.A16.published_locally_maximal`.
- **README.** Commands for macOS/Linux and Windows side by side, in both
  tables. The identification is described as it now stands. The repository
  map now includes the family certificate, the published source and
  `check_all.sh`.

## [1.1.0] — 2026-09-24

Superseded as the cited version by 1.1.1, which certifies the same results.
Everything below landed after `v1.0.0`
(`fa7145d`, 2026-09-09), whose tag was never moved; `v1.0.0` is not the code
the article describes, and `v1.1.0` is.

- **Release 1.1.0.** `Project.toml`, `CITATION.cff` and the article's
  bibliography entry for the package now say 1.1.0, and `make paper-check`
  requires the three to agree. `make paper-check` also requires the archived
  log `logs/final_run.txt` and every record in `results/` to declare one and
  the same commit, each with a clean source tree, which is what the
  supplement states.

- **Every candidate certified the same way; the published source run exactly
  (2026-09-24).**
  * *The published source, unchanged.* `cases/upstream/optigon/` holds
    OPTIGON's `cstrt_audet_ngon.jl`, byte for byte, with its MIT licence. Its
    SHA-256 (`376e838b…d0ff`) is the one recorded in 2026-09 and was confirmed
    against an independent download (`optigon-master`).
    `cases/optigon_exact.jl` runs that file unchanged in exact arithmetic. The
    root is a symbol, angles are `q·z + r·π`, and sin/cos are exact elements of
    `Q(c,s)`. Its vertices and its equation `F` are then compared with the
    certified ones by exact equality, not by a tolerance: equal for n = 16, 32,
    64. A test plants a sign, an angle and a symmetry error in a copy of the
    source; each is caught. `OPTIGON_DIR=…` also compares against a local
    OPTIGON checkout. This replaces the numerical 1e−70 agreement as the
    evidence that the certified polygon is the published one.
  * *`pipeline/certify_family.jl <n>`: the same certificate for A16, A32, A64.*
    Ten gates, all in the verdict. They are the published source run exactly;
    exact identities; interval Newton on `Z_root`, with `F'` from the exact
    identity `F = 2^m · Fc(cos z)`; root uniqueness on the whole search
    interval by an exact Sturm count (previously a test only, now a gate);
    side length and perimeter; convexity; inactive margin; rank; multipliers;
    box nesting by endpoints. A16 goes through the generic constructor here,
    exactly like A32 and A64. All three CERTIFIED, 10 of 10. The A16 bounds
    agree with the dedicated certificate, e.g. the smallest support
    determinant 0.0074882049306989244… and the margin
    0.0080997106581357295…; the multipliers are another point of the same
    one-parameter family. Records go to `results/family/A<n>.toml`, which
    `make paper-check` checks against the tree.
  * *The same planted defects for every candidate.*
    `tools/mutation_check.sh family [n]` plants, for each of A16, A32, A64: a
    digit of its root, one of its active diameters, a sign in the published
    source, a sign in the harmonic only its own n reaches, and a changed
    constructor equation. The family certificate must print NOT CERTIFIED for
    each; it does (manually verified on A32 before the harness ran). The
    verifier harness of `tools/stress_family.sh` now runs against any case
    (`HARNESS_CASE`).
  * *`make A16`, `make A32`, `make A64` run the same stages.* The suite, the
    general certifier, the family certificate, the family Lean layer, the
    generator and Lean stress tests, the five family mutations and the fifteen
    harness sabotages in that case's files. A16 adds the article's dedicated
    certificate, Lean layer and mutation check. On a dirty tree the mutation and
    harness stages are skipped and the verdict is `INCOMPLETE`. Nothing is
    recorded: `certify_a16.jl` and `certify_family.jl` honour
    `CHIQUI_NO_RECORD=1`, and `certify_a16.jl` now exits non-zero on
    `NOT CERTIFIED`.
  * The A16 provenance guardrail now counts 33 load-bearing sources
    (`pipeline/certify_family.jl`).
  * Measured on a clean tree, run one after another: `make A32` 10 min,
    `make A16` 18 min, `make A64` 32 min and `make check-all` 34 min. Every
    stage passed, including the mutation and harness stages of each candidate.

- **A16, A32, A64: the published polygon, proved in Lean (2026-09-24).**
  Until now the family certificate was about a polygon in polynomial form, and
  only Julia tests identified it with the one Bingane and Audet published. The
  identification is now kernel-checked.
  * `lean/ChiquipoliFamily/Optigon.lean` transcribes the upstream OPTIGON
    constructor `cstrt_audet_ngon`, the code accompanying the paper, statement
    for statement and for every `n`. It keeps the array assignments in order,
    the quarter-turn shifts `sin(i(2z − π/2))`, the signs `(−1)^i` and the
    division by `cos 2z`. The general lemmas are `shift`, `sin_quarter` and
    `cos_two_pos`.
  * `lean/ChiquipoliFamily/Chebyshev.lean` gives `sin kz` and `cos kz` as
    explicit polynomials for `k ≤ 63`, generated once and shared by every case.
  * `A<n>/Published.lean` proves three things. `Q_eq_P`: all `n` vertices of
    the transcribed code equal the certified ones. `F_eq`: upstream's equation
    is `2^m · Fc(cos z)`, with `m = 12, 28, 60`, wherever `cos 2z ≠ 0`; the
    generator checks exactly that the only denominator is `cos⁴ 2z`.
    `published_locally_maximal`: upstream's `F` has exactly one zero in
    upstream's bracket, and the polygon upstream's code builds there is a
    strict local maximiser. Build cost: A64 137 s, 9.2 GB.
  * What no kernel can check is that the Lean transcription says what the Julia
    source says. It is bounded three ways. A new test requires the 32 upstream
    statements quoted in `Optigon.lean` to occur verbatim in the vendored
    source, with the same assignment counts (12 and 16). Four transcription
    slips are now planted by `tools/stress_family.sh harness` (a sign, a
    symmetry, an angle, the loop bound); each breaks the Lean identification,
    and in `A16/Published.lean`, not in `Optigon.lean`. The existing numerical
    agreement to `10⁻⁷⁰` stays.
  * Controls: an eleventh per case, `fnc11_published_bracket`. It claims
    uniqueness of the published root on `(0, π/4)`, which is false: there
    `F = 2^m · Fc(cos z)` has at least two zeros. Its twin is upstream's own
    bracket. A first candidate for this control (`F = 2^m · Fc(cos z)` at
    `z = π/4`, where `cos 2z = 0`) was refused by the generator's falsity
    check. The dropped term's numerator `sin(nπ/16)` also vanishes there, so
    the claim was true, and a control built on it would have been vacuous.
  * `verify_family.sh`: 11 controls per case, 65 audited theorems, the headline
    audited by name now includes `published_locally_maximal`, `Q_eq_P` and
    `F_eq`, and step 5 also regenerates `Chebyshev.lean`. The family record
    moves the identification from `not_formalized` to `formalized`, keeps
    transcription fidelity as the one step outside the kernel, and hashes the
    vendored upstream file. `make paper-check` checks both.
  * The first full `make check-all` after this change reported two MISSED
    harness defects. Neither was a blind spot, since the step failed each
    time, but both were wrong reports. Step 3 of `verify_family.sh` reported
    only the lowered theorem count when a headline theorem was dropped, and
    never named it; each condition is now reported on its own. The harness
    still expected the old count of 9 remaining controls. Measured afterwards
    on a clean tree: `make check-all` passes all 8 stages in 30.7 min, with
    the stress test rejecting 63 of 63 planted defects.

- **The family certificate is recorded; one command for everything
  (2026-09-24).**
  * `results/lean_family_certificate.toml` (`make lean-family-certificate`),
    the family's counterpart of `lean_certificate.toml`. It records the five
    checks per case, the certified numbers of A16, A32 and A64 (bracket,
    enclosure radius, margins, the smallest diameter stress, the `Fc`-sides,
    the derivative bound), the toolchain, the scope, and the SHA-256 of 286
    files: the Lean sources, controls and twins, the verifier, the generator,
    and its Julia inputs. `make lean-family-record` answers in seconds, without
    Lean, whether the record still describes the tree. `make paper-check` now
    fails on a stale family record.
  * `tools/check_all.sh`: `make check` (Julia only, ~5 min, writes nothing),
    `make check-all` (everything, in order, refreshing every record),
    `make check-lean`, and `make check-case N=<n>` for one case. Per-layer
    commands for one case: `literature-case`, `lean-family-case`,
    `stress-case`. Every stage runs even if one fails, and the run ends with a
    table. Stages that need a clean tree are skipped on a dirty one, and the
    verdict is then `INCOMPLETE`, not a pass. `CHIQUI_NO_RECORD=1` lets
    `certify_literature.jl` run the full benchmark without rewriting
    `results/`. Measured: `make check-all` takes 29.5 min on a clean tree
    (test 31 s, mutation check 8.5 min, family stress test 15.4 min,
    certificates and records 5 min). Its first run found a real defect that
    nothing else exercises: the A16 provenance guardrail pins the number of
    hashed sources, and the new `pipeline/record_lean_family_certificate.jl`
    made it 32. It was raised deliberately, as the guardrail asks.
  * The external audit of v1.0.0 is reviewed finding by finding in
    `docs/audits/external-audit-v1.0.0.md`. All 19 findings were already
    resolved. One had no guard against regression: D01, root uniqueness in the
    verdict. It now has a test (every gate must appear in `final_pass`) and a
    16th mutation.
  * Fixed: `docs/guide/certificate-spec.md` still said 12 planted defects,
    and `make paper-check` failed on it after the previous commit.
    `results/README.md` described files that do not exist. The README quoted
    651 test assertions (now 714).

- **Family layer: controls with twins, and a stress test in two independent
  lines (2026-09-24).** The certificates of A16, A32 and A64 are unchanged,
  byte for byte. What changed is how they are tested:
  * *Negative controls*: 10 per case, the same 10 for every `n`, generated with
    the certificate into `lean/negative_controls_family/A<n>/`. They replace the
    5 hand-written A32-only controls. Each control is a false statement,
    checked false by the generator before it is written, and attempted with the
    certificate's own proof. Each is paired with a *twin* (`twin/`): the same
    proof of the true statement, which must compile. `verify_family.sh` now
    rejects a control that fails for the wrong reason (an unresolved name, a
    timeout, a recursion limit) and a twin that compiles only by `sorry`. One
    control records a fact the certificate depends on: `Fc` has at least 5, 11 and 21
    roots in `(0, 1)` for n = 16, 32, 64, so uniqueness holds only on the
    article's search bracket.
  * *Generator pre-checks*: every inequality Lean re-proves is now also a
    named `guard` at the point of emission (enclosure `hnum`, each
    determinant, each inactive pair, each Henneberg step, the unconditional
    sides, the signs of `Fc` at the bracket ends, the derivative bound). There
    is also a new numerical check of the self-stress: the equilibrium at every
    vertex, at the centres, within a rigorous residual bound.
  * *`tools/stress_family.sh`* (`make stress-family`): eight kinds of
    generator defect (`CHIQUI_MUTATE`) planted in each case. The generator must
    refuse all 24. With the pre-checks off (`CHIQUI_MUTATE_UNGUARDED=1`), Lean
    must reject all 24, with every error inside the planted declaration and
    every upstream module byte-identical to the built certificate. Eleven
    sabotages of `verify_family.sh` must each fail the step responsible. The
    generator and Lean parts write only to scratch directories
    (`CHIQUI_OUTDIR`); a mutated run cannot write to the tracked tree. The
    generator part also runs weekly in CI (`mutation.yml`).
  * `verify_family.sh` step 5 regenerates into a scratch directory and diffs,
    instead of overwriting and restoring the tracked files. It now also covers
    the root module and the controls. `FAMILY_STEPS` and `FAMILY_CASES` run a
    subset, and label the run as partial, not a certification.
  * `tools/mutation_check.sh` gains three family mutations (15 in total): a
    sign error in the generic constructor that exists only for n ≥ 32, a digit
    of the A64 root, and an A32 active edge. The Julia suite rejects each one.

- **Lean certificate of A64; multipliers as a self-stress (2026-09-24).** The
  family layer now proves `locally_maximal_unique` for **A64** as well (A16,
  A32, A64 all pass `verify_family.sh`). Getting there replaced the multiplier
  witness: the exact solve over `Q[c]/(Fc)` took 51 min at n = 64 and one of
  its 63 degree-59 positivity certificates took 314 s / 9.7 GB in Lean. The
  multipliers are now a **self-stress built by the Henneberg order** already
  used for rigidity: the two bars outside the construction (which are exactly
  the two sides that need `Fc`, at n = 16, 32, 64) carry rational stresses,
  every other stress is Cramer's rule at the vertex that added it
  (`cramer_bal`), the pinned side is fixed last (`pin_bal`), and vertices 0, 1
  balance by the global force and moment identities. The equilibrium needs no
  `Fc`; positivity of the diameter stresses and `Σα < 0` follow by centred
  enclosure arithmetic (`add_close`, `mul_close`, `div_close`, `recenter`), and
  `mult_of_stationary'` gives the multiplier identity with `κ = −ℓΣα > 0`. The
  certified bracket for `c` narrowed from `10⁻⁹` to `10⁻¹⁷` so the enclosures
  survive the recursion. The generator now runs in seconds for every n
  (`simplest` became a continued-fraction search); `multipliers_n.jl`, the
  solver of the previous design, is removed. Measured: A64 builds in
  21 min at 13 GB peak (the degree-31 vertex enclosures dominate); A16 in
  about 1.5 min at 0.8 GB. Nothing outside `lean/ChiquipoliFamily/`,
  `lean/generators/family/`, `lean/negative_controls_family/` and
  `lean/verify_family.sh` changed apart from documentation and the A64 case
  comment (re-run `make literature` at a clean tree).

- **Lean certificate of A32, and a Lean layer that scales in n (2026-09-24).**
  New library `lean/ChiquipoliFamily/` (not a default target; `make
  lean-family` runs its own five checks in `lean/verify_family.sh`). For A32 it
  proves `locally_maximal_unique`: the constructor root is the only one in the
  article's search interval `(2 arcsin(sin(π/32)/2), π/32)`, and the polygon it
  builds is a strictly convex equilateral small 32-gon and a strict local
  maximiser of the perimeter modulo Euclidean motions, through the general
  `Feasible.thm_3_5`. Only `[propext, Classical.choice, Quot.sound]`. The same
  generator re-proves A16 independently.
  *Why a new method.* Measured before writing it: one A32 support determinant
  is a degree-29 polynomial whose Bernstein certificate costs 38 s / 2.2 GB, and
  A32 has 960 of them (a file of 300 exceeded 73 GB); the A16 rank certificate
  already costs 160 s / 13.6 GB. `ChiquipoliFamily/Basic.lean` instead proves
  once, for every n: centred-Taylor vertex enclosures (`tbound`), error
  propagation to determinants and distances (`det_lb`, `sqd_ub`), infinitesimal
  rigidity by a Henneberg construction (`pin_bar`, `henneberg_step`), and the
  multiplier identity from vertex stationarity (`mult_of_stationary`). Result:
  A16 builds in 81 s at 0.8 GB peak, A32 in about 8 min at 3.8 GB peak.
  Generator `lean/generators/family/gen_family.jl` (plus `multipliers_n.jl`, the
  n-generic copy of `multipliers.jl`) checks every margin in exact rational
  arithmetic before writing Lean. Five family negative controls
  (`lean/negative_controls_family/`). Not in Lean for the family: the
  hand-transcribed trigonometric constructor (the configuration is defined by
  its exact polynomial form; its identity with OPTIGON's is the Julia test).
  Nothing in `ChiquipoliLean/`, `verify.sh`, its pinned counts, or `paper/`
  changed; `lakefile.toml` gained the second library. `cases/A32`, `cases/A64`
  changed in comments only, so re-run `make literature` at a clean tree.

- **A32 and A64 added to the literature benchmark (2026-09-23).** The
  Bingane–Audet constructor is now written once for every `n = 2^s ≥ 16`
  (`audet_generic` in `cases/exact_coords.jl`), over an abstract angle algebra,
  and instantiated both in intervals and in `Q(c,s)`; `Fc` is derived from it
  by Proposition 1 (`audet_Fc`). New cases `cases/A32_bingane_audet` and
  `cases/A64_bingane_audet` pass every block of the general certifier. A new
  testset in `test/literature.jl` (52 assertions; the suite is now 703)
  checks the constructor against the vendored OPTIGON transcription for
  n = 16, 32, 64 and against `A16Certificate` at n = 16, proves uniqueness of
  the constructor root by a Sturm count on `Fc`, pins the observed pattern
  (`n − 1` active diameters, LICQ defect 1, `deg Fc = n − 4`, exactly two
  equalities needing `Fc`), and rejects three planted errors on A32. Nothing
  under `src/`, `lean/` or `paper/` changed; the A16 certificate's values are
  unchanged, but its provenance hashes cover `pipeline/` and `test/`, so both
  certificates must be regenerated at a clean tree. See
  `docs/guide/general-framework.md` §8a.

- **Repository reorganised (2026-09-23), no mathematics changed.** Files are
  grouped by role, so that a reader of the article can find the code behind a
  statement without opening every file. Every certified value is unchanged
  (the regenerated certificates differ from the previous ones only in
  provenance fields and file paths), the test summary is identical (651
  assertions in the same 22 testsets, in the same order), and the Lean layer
  was rebuilt from an empty build directory, so no stale compiled module could
  stand in for a renamed one. Theorem names are unchanged: they come from each
  file's `namespace`, not from its folder, so `Audit.lean` and the 32 names
  `verify.sh` requires did not move.

  Old path -> new path (the audit reports and the archived logs use the old
  ones):

  | Old | New |
  |---|---|
  | `scripts/run_all.jl` | `pipeline/certify_a16.jl` |
  | `scripts/run_literature.jl` | `pipeline/certify_literature.jl` |
  | `scripts/run_lean_certificate.jl` | `pipeline/record_lean_certificate.jl` |
  | `scripts/check_paper.jl` | `pipeline/check_paper.jl` |
  | `scripts/_bootstrap.jl` | `pipeline/stages/_bootstrap.jl` |
  | `scripts/01_nominal.jl` | `pipeline/stages/01_nominal_configuration.jl` |
  | `scripts/02_root_interval.jl` | `pipeline/stages/02_certify_root.jl` |
  | `scripts/03_geometry_interval.jl` | `pipeline/stages/03_certify_geometry.jl` |
  | `scripts/04_rank_interval.jl` | `pipeline/stages/04_certify_rank.jl` |
  | `scripts/05_multipliers_interval.jl` | `pipeline/stages/05_certify_multipliers.jl` |
  | `scripts/06_exact_identities.jl` | `pipeline/stages/06_prove_exact_identities.jl` |
  | `src/A16Certificate.jl` (one file) | `src/A16Certificate.jl` (module, exports, includes) + `src/a16/{data,guarantees,constructor,geometry,linear_algebra,exact_algebra}.jl` |
  | `examples/literature/` | `cases/` (they are inputs of a certificate, not tutorials) |
  | `test/runtests.jl` (one file) | `test/runtests.jl` + `test/{constructor,framework_guards,exact_algebra,certificate_stages,literature,regressions,optigon}.jl` |
  | `test/optigon_reference.jl`, `test/optigon_upstream_*.txt` | `test/fixtures/` |
  | `lean/scripts/verify.sh` | `lean/verify.sh` |
  | `lean/tools/` | `lean/generators/` |
  | `lean/ChiquipoliLean/{FirstOrder,Instability,Slice,SliceIFT,Feasible,FeasibleOpen,FeasibleTangent,FeasibleRigid,FeasibleMain}.lean` | `lean/ChiquipoliLean/Theory/` (same names) |
  | `lean/ChiquipoliLean/{Chebyshev,Identities,RootExists,SearchInterval,SideLength}.lean` | `lean/ChiquipoliLean/Constructor/` (same names) |
  | `lean/ChiquipoliLean/Constructor.lean` | `lean/ChiquipoliLean/Constructor/Coordinates.lean` |
  | `lean/ChiquipoliLean/Main.lean` | `lean/ChiquipoliLean/Constructor/A16Exists.lean` (it was not the main theorem) |
  | `lean/ChiquipoliLean/Generated.lean` | `lean/ChiquipoliLean/Generated/Polynomials.lean` |
  | `lean/ChiquipoliLean/{Positivity,InactiveMargin,Diameter,Convexity,Multipliers,Rank}.lean` | `lean/ChiquipoliLean/Generated/` (same names) |
  | `lean/ChiquipoliLean/FirstOrderA16.lean` | `lean/ChiquipoliLean/Instances/A16FirstOrder.lean` |
  | `lean/ChiquipoliLean/Rank30.lean` | `lean/ChiquipoliLean/Instances/A16Rank30.lean` |
  | `lean/ChiquipoliLean/FeasibleA16.lean` | `lean/ChiquipoliLean/Instances/A16LocalMax.lean` |
  | `lean/ChiquipoliLean/Examples.lean` | `lean/ChiquipoliLean/Instances/SquareAndRhombus.lean` |
  | `lean/ChiquipoliLean/FeasibleSquare.lean` | `lean/ChiquipoliLean/Instances/SquareLocalMax.lean` |
  | `docs/{certificate-spec,provenance-mapping,general-framework,literature-validation,scope-and-limitations,theorem-3.5-formalisation}.md` | `docs/guide/` |
  | `docs/{referee-report,theory-audit}.md` | `docs/audits/` (records, kept as written) |
  | `tools/independent_check*`, `tools/independent-check.md` | `tools/independent_check/` |
  | `logs/<UTC>_a16_certificate.txt` | `logs/archive/` (kept byte for byte) |
  | `main.tex`, `supplement.tex`, PDFs, `latexmkrc` (root, untracked) | `paper/` (untracked; `main_1.*` in `paper/archive/`) |

  The `make` targets did not change. Moving files into subdirectories exposed
  checks that scanned one directory level only and would have gone blind in
  silence; each is now recursive and pinned to a count, so a file that drops
  out fails loudly:
  - `verify.sh` searched for `sorry` in `ChiquipoliLean/*.lean` only. After the
    move it would have scanned 2 of 31 files and passed. Now recursive, with
    the number of scanned files pinned (and the planted-`sorry` mutation sits
    in a subdirectory, so the harness checks the recursion).
  - `verify.sh` check 5 compared a generated file against a copy of itself
    left in place, so a generator writing to a stale path would have passed.
    The committed file is now moved aside first, and the generator must
    recreate it at its path.
  - `verify.sh` counted a negative control as rejected whatever the error; one
    whose import no longer resolves fails to compile for that reason alone and
    guards nothing. That case is now a FAIL.
  - `record_lean_certificate.jl` hashed only top-level Lean files and one of the
    seven generators, and its `generated_matches_julia` field looked at one of
    the seven generated files. Both now cover all of them.
  - `check_paper.jl` read only top-level Lean files for its claims about the
    Lean layer, and checks that the article's printed paths exist for the new
    directories too (including `./verify.sh`).
  - The provenance scans of both Julia certificates are recursive, and share
    one list of directories with the git cleanliness check; the literature
    certificate now also hashes `cases/exact_coords.jl`, which supplies the
    exact coordinates of every case and was left out. Its cleanliness check
    listed `tests`, a directory that does not exist, so an uncommitted edit to
    the test suite never marked the run dirty.
  - The mutation harness counted a mutation as caught whenever the checker
    exited non-zero, and never checked that a Lean defect had actually been
    planted. During this reorganisation a one-character slip in its `cd` made
    it run from `tools/`: every Lean mutation then failed to plant, `cd lean`
    failed, and all five were reported CAUGHT. (The Julia ones reported "could
    not apply", which is why it was noticed.) Now the harness refuses to run
    outside the repository root, every mutation must be planted before the
    checker runs, and "rejected" requires the checker to have run and reported
    a failure (`LEAN CERTIFICATE FAIL` or a failed build from `verify.sh`, a
    failing test summary from the Julia suite).
  - The certificates' git cleanliness check was, for one intermediate state of
    this work, built as `` `git status -- $(SOURCE_DIRS...)` ``: inside
    backticks Julia concatenates a splatted tuple into one word
    (`srcpipelinetest`), git reports nothing for a path that does not exist, and
    a dirty tree was recorded as clean. Caught by comparing the recorded flag
    against `git status`; the command is now built from an explicit argument
    vector. No committed certificate was affected.
  - Found on the way, not caused by the move: two negative controls cited a
    "Remark 2.7" that does not exist (it is Definition 2.4, as fixed in
    `FeasibleOpen.lean` in the first external audit); `lean/README.md` said
    eighteen negative controls (there are 26), listed eighteen, and omitted
    six modules from its file list; `logs/README.md` pointed at
    `scripts/archive_log.sh` (it is in `tools/`); and `make paper` with no
    article reported "nothing to compile" and then failed.
  - The supplement's table of commands and scripts prints the new paths (an
    editorial change to `paper/supplement.tex`, which must be re-uploaded).
- **Article retitled**: "Stability of Equilateral Small Polygons" -> "First
  Order Geometry of Equilateral Small Polygons", propagated to `README.md`,
  this changelog's own past entries being the one place it was intentionally
  left as printed at the time, `docs/certificate-spec.md`,
  `scripts/run_all.jl` and `scripts/run_lean_certificate.jl`.
- **Correction to the article, supervisor round**: `Q` invertibility
  (Subsection 6.4) is now proved *exactly*, from `det Q = y_1 - 1 < 0` using
  the exact vertex map of equation (5.1), rather than from the interval sign
  `y_8 - y_1 > 0`. Table 3 restructured into three panels (exact / interval /
  exact consequences) reflecting this. `scripts/check_paper.jl` gained checks
  for the new equation (5.1) and the restructured table.
- **Article shortened** (supervisor request): operator definitions, the box
  figure, the nesting counterfactual and one proof route moved from the
  article to the supplement; Section 6 restructured 6.1-6.7; ~130 short
  displays inlined. Net: 23 -> 15 pp article, 8.7 -> 3.2 pp of that in
  Section 6, +6 pp supplement gaining the moved material.
- `scripts/check_paper.jl` hardened: verifies every number Section 6 prints
  against the certificate's own source (not a paraphrase of it), the printed
  `F_c` coefficients against `Fc_poly()`, the Figure 5 magnification and the
  supplement's precision paragraph, and the vertex map of equation (5.1)
  against `coordinates()` at several parameters.
- `docs/certificate-spec.md`: second author credited.
- CI (`.github/workflows/certificate.yml`) fix: the drift-detection step's
  field allowlist did not exclude `seconds`/`total_seconds`
  (`results/validation_certificate.toml`'s wall-clock timing fields), so it
  failed on every run since the first commit regardless of whether the
  certificate had actually drifted. Fixed; see git blame on that file for
  the reproduction.
- CI: new `compat` job (Julia 1.10 and 1.11, dependencies re-resolved because
  the pinned Manifest is 1.12's and cannot be instantiated on older Julia) that
  runs the test suite, the certificate and the literature benchmark. This backs
  the `julia = "1.10, 1.11, 1.12"` range in `Project.toml`, which until now was
  claimed but never tested. Checked locally first: 628/628 tests and `CERTIFIED`
  on 1.10.12 and 1.11.9.
- CI: new `mutation.yml` workflow runs the six Julia mutations weekly and on
  demand, so the suite's ability to fail is checked continuously. The Lean
  mutations still need `make mutation-check` by hand (Mathlib cache).
- `.zenodo.json` added, so that a Zenodo deposit made from a GitHub release
  carries the right title, authors, licence and description. No deposit exists.
- **Second external audit (2026-09, evidence-ledger report on 1.0.0).** No
  finding of severity S3 or S4; every certified bound reproduced. Findings
  M01-M04 and D07 had already been fixed by the round below. Resolved now:
  - D01: root uniqueness on the whole of `I_search` is part of the verdict; it
    was reported but not required, so a run whose monotonicity test failed
    would still have printed CERTIFIED.
  - D02: failure paths are uniform. A failed multiplier solve used to return
    only `(pass, reason)`, and run_all.jl then crashed on `r5.lambda_lower`
    after printing NOT CERTIFIED; a failed root step aborted through an
    `@assert`. Every stage now returns the same fields on failure, nothing
    aborts except a lost guarantee flag, and a failed run still writes the
    certificate with FAIL entries. Checked end to end on forced failures of both
    kinds, and by a new test that the failure and success results of stages 02
    and 05 have the same fields.
  - D03: the side-length gate is a real gate (`certify_side_length`): it fails
    if the root was not certified or the nominal ℓ lies outside its enclosure,
    and it enters the verdict. It was recorded as passed unconditionally.
  - D04: box nesting compares endpoints against the box each of stages 03-05
    actually evaluated, instead of comparing two radii.
  - D05: `regularity_test` (both tracks) sums the row bounds as intervals and
    reports the supremum, so the printed norm bounds are directed upper bounds.
    No certified value changed at 256 bits.
  - D06: the inactive margin routes its literal through `_lit` and is checked by
    `assert_guaranteed`, like every other certified quantity.
  - D08: new test `Fprime(t) = -sin t · Fc'(cos t)` from the exact coefficients
    of `Fc_poly()`, and a new mutation (a derivative that is wrong but keeps its
    sign). With that mutation interval Newton and monotonicity both still PASS,
    so before this test the certificate would have printed CERTIFIED on a wrong
    derivative; the test now rejects it. 12 planted defects, 7 in Julia.
  - D11: Track B's equilaterality block reports `:CONSISTENT`, not
    `:CERTIFIED`; the equality itself is the `:PROVEN` exact_identities block.
  - D12: `certify` sets its working precision in a scoped
    `setprecision(...) do` block instead of changing the caller's.
  - Supplement (editorial, no mathematics changed): M07, the equilateral
    benchmarks n = 4, 8 are credited to Vincze (1950) and Audet-Hansen-Messine-
    Perron (2004), not to Tamvakis (1987) and AHM (2007), whose optima are not
    equilateral; M05, the pipeline paragraph no longer says nothing is iterative
    or that a failure aborts; M06, the Krawczyk system is linear; D10, it states
    that the Jacobian steps rest on Lemma 6.1; and the steps are described in
    logical order, the scripts computing (i) last.
  - Not changed, by the report's own revision: R02 (the supplement's `y8 - y1`
    statement is accurate), R04 (the article's "re-derives those hypotheses" is
    accurate). R03 and R05 concerned the report itself.
- **External audit (2026-09, report on package 1.0.0), project-side findings
  resolved.** The report re-executed every interval gate in mpmath and found
  no error in any certified value; its findings concern the text around them.
  - F12, now formalised: new `lean/ChiquipoliLean/SearchInterval.lean` proves
    `constructor_root_existsUnique_article_search`, i.e. Proposition 6.2(1) on
    the article's own `I_search = (2 arcsin(sin(π/16)/2), π/16)`: the inclusion
    `cos(I_search) ⊆ [49/50, 491/500]` (previously a hypothesis), and the
    constructed root lying inside `I_search`. Audited, and added to the
    load-bearing list of `verify.sh`: 108 audited theorems (was 107). The
    supplement's count was updated to match.
  - F5: `scripts/run_all.jl` now *asserts* the directed-rounding self-check
    (`inf < 1//3 < sup`, compared exactly) instead of only printing it.
  - F8, F9: README counts corrected (108 audited theorems, 26 negative
    controls, 11 planted defects of which 6 in Julia), and
    `scripts/check_paper.jl` now ties all three to their sources.
  - F10, F11, F13: stale Lean comments corrected — the square instantiation
    exists (`square_strict_local_max`), root uniqueness is formalised, and
    `FeasibleOpen.lean` cited a nonexistent "Remark 2.7" (now Definition 2.4,
    the inactive margin). The supervisor's comment corrections to
    `FirstOrder.lean` and `Slice.lean` (from the ChiquipoliV2 review) ported,
    without its renumbering, which belongs to the other article.
  - F4, F7: `build_jacobian` documents that the rank and multiplier gates
    certify `D(e,d)` only together with the exact identities;
    `rigid_annihilation_identities` documents that the rank upper bound is
    argued in Julia and kernel-checked in Lean.
  - Found while fixing the above, not in the report: the recorded Lean scope
    (`run_lean_certificate.jl`) listed `rank D(e,d) = 30` as not formalised,
    though `rank_eq_thirty` is proved and audited; `docs/provenance-mapping.md`
    still gave the interval sign `y_8 - y_1 > 0` as the argument for `Q`
    invertible, superseded by the article's exact `det Q = y_1 - 1 < 0`; the
    README said the pinned Manifest works from Julia 1.10 (it needs 1.12) and
    that the run has "no search", although the root step and Krawczyk adapt
    their radius. All corrected.
- `scripts/06_exact_identities.jl`: renamed the unproved-identity sentinel
  from `"TODO"` to `"UNPROVED"` (cosmetic; the counting logic only ever
  checked for `"PROVED"`, so this changed no behaviour).

## [1.0.0] — 2026-09-09

First public release: the supplementary material for *First Order Geometry of
Equilateral Small Polygons*.

### What it establishes

- **The certificate.** Eight gates on the Bingane–Audet hexadecagon `A16`,
  by outward-rounded interval arithmetic at 256-bit precision and by exact
  rational algebra in `Q[c]`: the constructor root exists and is unique in the
  search interval, the sixteen side and fifteen active-diameter equalities hold
  exactly, the configuration is strictly convex in the labelled cyclic order,
  every inactive diameter is strictly slack, the multipliers are certified
  strictly positive, and `rank D(e,d) = 30`, hence `I_eq = R_eq`.
- **The formal layer.** Lean 4, checked against a pinned Mathlib revision, with
  no interval arithmetic and no floating point. It re-derives the computational
  hypotheses by kernel-checked rational arithmetic, and proves the article's
  Theorem 3.5 itself — the local Euclidean slice, openness of convexity and the
  inactive margin, the first-order limits, invariance under Euclidean motions,
  and the blow-up. `Feasible.A16_locally_maximal` is the article's Theorem 6.3
  and `Feasible.square_strict_local_max` its Proposition 4.2, so the passage
  from the certified data to strict local maximality is machine-checked end to
  end.
- **The general framework.** The same code path certifies the first-order
  structure at the equilateral optima known for `n = 4, 6, 8`, and refuses
  three deliberately broken variants of `A16`.

### How it guards itself

- 628 test assertions; `Pkg.test()` runs them.
- 107 Lean theorems audited, depending on `propext`, `Classical.choice` and
  `Quot.sound` only, with 32 required by name so that coverage cannot drift.
- 26 negative controls, each a deliberately false variant that must fail to
  compile — what shows the true statements are not vacuous.
- 12 planted defects, each of which the checks must reject
  (`tools/mutation_check.sh`).
- Seven generated Lean files reproduce byte for byte from the Julia source.
- SHA256 of every load-bearing source file, with the count pinned: the
  provenance scan is directory-driven and non-recursive, so a file moved out of
  `src/`, `scripts/` or `test/` would otherwise drop out of the hash chain in
  silence.
- `scripts/check_paper.jl` reconciles the article — its tables, bounds, figure
  coordinates, structural counts, claims about Lean, and the commands it prints
  — against the regenerated certificate and the Lean sources.

### Known limits

Stated in full in `docs/scope-and-limitations.md`. In short: the theorem is
local and yields no lower bound on the radius of the neighbourhood; global
optimality is not addressed; and no proof assistant establishes that the
certified configuration is the published Bingane–Audet polygon — that is an
attribution, checked by running the upstream OPTIGON constructor and comparing
coordinates.
