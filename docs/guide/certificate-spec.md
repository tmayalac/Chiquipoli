# docs/guide/certificate-spec.md — canonical specification

> **Paper numbering.** Every `Theorem/Lemma/Prop/Remark N.M` below refers to
> `main.tex` as revised on 2026-09-15, when Section 6 was reorganised into
> 6.1 scope and certificate, 6.2 exact algebra, 6.3 certification boxes, 6.4
> recovery of the omitted stationarity equations, 6.5 certified data, 6.6 strict
> local maximality and 6.7 reproducibility. Its mathematics is unchanged and
> stays in the article; only the software documentation (environment, commands,
> traceability, formal-layer detail, provenance) moved to `supplement.tex`.
> Earlier shifts are recorded here so the anchors can be traced. On 2026-08-20
> Section 3 shifted by three: what earlier revisions called Theorem 3.8 and
> Lemma 3.7 became **Theorem 3.5** and **Lemma 3.4**. On 2026-09-14 Remark 6.3
> left Section 6 for the supplement, so what was Theorem 6.4 is now
> **Theorem 6.3**; Lemma 6.1 and Proposition 6.2 keep their numbers, and
> Sections 2, 3, 4 and 5 are unaffected. Two figures were inserted before the
> existing ones, so old Figures 1 and 2 are now **Figures 3 and 4**, and the two
> multiplier tables were merged, so old Table 4 is now **Table 3**. The frozen
> previous version is `main_1.tex`. On 2026-09-15 Section 6 was shortened again:
> the definitions of the interval operators, the schematic figure of the two
> boxes and two explanatory paragraphs moved to `supplement.tex`, so the article
> now has **four figures**, and trivial displayed equations were set inline. No
> statement, bound or proof changed. On 2026-09-16, after the supervisor's
> corrections, Section 5 prints the exact vertex map as equation (5.1), Table 3
> has three panels (exact, interval, exact consequences) with the regularity of
> both M and M0, and the invertibility of Q in Subsection 6.4 is proved exactly
> from p0 = (0,0) and p8 = (0,1) rather than from the interval sign y8 - y1 > 0.
> If the article is edited again, re-check these anchors before releasing.


This is the single **authoritative** description of what this repository
certifies, how its two tracks are separated, and which document is the source
of truth for what. Everything else is either machine-readable data, source,
tests, or supplementary explanatory notes (§3). If any other document conflicts
with this one on scope or claims, **this document wins** and the other is a bug.

Paper: J. Ayala Hoffmann and T. Ayala Coppola, *"First Order Geometry of Equilateral Small Polygons"*,
which cites this package as **[AH26]**.

---

## 1. What is certified — the dedicated A16 certificate

`pipeline/certify_a16.jl` certifies, for the exact Bingane–Audet hexadecagon
\(A_{16}\) enclosed by the constructor root interval, the **hypotheses of the
paper's Theorem 3.5** as instantiated for \(A_{16}\) (Lemma 6.1 +
Proposition 6.2 (1)–(6)). By that theorem (Theorem 6.3), those hypotheses imply
\(A_{16}\) is a **strict local maximiser of perimeter modulo orientation
preserving Euclidean motions**.

**The computation certifies the hypotheses; the paper's theorem supplies the
conclusion.** The topological maximality statement is *not* proved by the
computation — it is Theorem 3.5 (proved analytically in the paper via the Local
Euclidean slice, Lemma 3.4). Global optimality is **not** claimed (§7).

Machine-readable record of every gate below: **`results/a16_certificate.toml`**
(regenerated on every `certify_a16.jl` run; one `[[gate]]` per row here).

| Gate | Paper ref | Status | Certified quantity |
|---|---|---|---|
| Unique constructor root | Prop 6.2(1) | CERTIFIED | interval Newton: \(0\notin F'(Z_{\rm root})\), \(N(Z_{\rm root})\subset\operatorname{int}Z_{\rm root}\); unique in box **and** in the full search interval |
| Side length / perimeter | Prop 6.2(2) | CERTIFIED | \(\ell=0.1959554930055385228\ldots\), \(16\ell=3.1352878880886163663\ldots\); enclosed over \(Z_{\rm root}\) with outward rounding, widths \(<2\times10^{-30}\) and \(<3.19\times10^{-29}\) |
| Strict convexity + cyclic order | Prop 6.2(3) | CERTIFIED | min support determinant \(\ge 0.0074882049306989244\) (at edge/vertex \((10,12)\)) |
| Exact active graph + inactive margin | Prop 6.2(4) | CERTIFIED | \(\delta_{\rm inact}\ge 0.0080997106581357295\) (critical pair \(\{4,12\}\)) |
| Positive multipliers + stationarity | Prop 6.2(5) | CERTIFIED | \(\min\lambda_{ij}\ge 0.0918667776833353997\) (edge \(\{6,13\}\)); omitted-eq recovery via \(\det Q=y_1-y_8<0\) |
| Rank 30 \(\Rightarrow I_{\rm eq}=R_{\rm eq}\) | Prop 6.2(6) | CERTIFIED | \(\lVert I-CM\rVert_\infty\le 1.419383643581978\times10^{-25}<1\) |
| 16 side + 15 diameter equalities | Lemma 6.1 | PROVEN | exact \(\mathbb Q[c]\) algebra, 16/16 + 15/15; 29 unconditional, 2 (\(\{3,4\},\{12,13\}\)) \(=F_c\); no interval containing zero |
| Box nesting \(Z_{\rm root}\subset\operatorname{int}Z_{\rm cert}\) | Prop 6.2 | CERTIFIED | composition gate: endpoints of \(Z_{\rm root}\) (radius \(10^{-30}\)) strictly inside each box stages 03–05 evaluated (radius \(10^{-28}\)) |

Final banner (from `certify_a16.jl`): `FINAL FIRST-ORDER CERTIFICATE: CERTIFIED`,
`ROOT UNIQUENESS ... PROVED`, `TOPOLOGICAL LOCAL MAXIMALITY: NOT ESTABLISHED BY
*THIS* RUN — PROVED IN LEAN` (the interval layer certifies the hypotheses of
Thm 3.5; the conclusion is `Chiquipoli.Feasible.A16_locally_maximal`),
`GLOBAL OPTIMALITY: NOT CLAIMED`.

Full line-by-line mapping of each gate to the exact source function and paper
sentence: **`docs/guide/provenance-mapping.md`** (the referee-grade audit; this section
is its executive summary).

### Lean 4 / Mathlib layer — Category A complete

**Every computational row of the table above** is additionally verified by the
Lean kernel in `lean/`, `sorry`-free: Lemma 6.1 with the 29-unconditional /
2-conditional split (for \(\{3,4\}\) and \(\{12,13\}\) the defect is
\(F_c(\cos z)\) exactly, quotient \(1\)); existence **and uniqueness** of
the constructor root across the paper's whole search interval, lifted to the
angle \(z\) by injectivity of \(\cos\); the inactive margin, hence diameter
exactly 1; strict convexity with the labelled cyclic order (224 determinants);
stationarity with strictly positive multipliers; and \(\mathcal I_{\rm eq}=
R_{\rm eq}\) via `kernel_is_rigid` — stated over the polygon's vertices, and
reached without `Matrix.det` or the rank API. For that layer the trust base is
Lean's kernel rather than Julia's `Rational{BigInt}` arithmetic.

The six are assembled into a single theorem, **`A16_certificate`**, exhibiting
one `z` at which all of them hold simultaneously — so the development proves an
object exists with all six properties, not merely six implications.

**`A16_certificate` by itself does not prove local maximality.** It proves the
hypotheses Theorem 3.5 consumes. Theorem 3.5 is formalised separately, in
`lean/ChiquipoliLean/Feasible*.lean`, and `Feasible.A16_locally_maximal` joins
the two: the configuration is a strict local maximiser of the perimeter modulo
orientation-preserving Euclidean motions, kernel-checked and `sorry`-free. What
remains outside the Lean layer is global optimality, and the attribution of the
certified object to the published polygon (an OPTIGON cross-check, in Julia).
Scope, the verification checks and the negative controls: **`lean/README.md`**;
the formalisation of Theorem 3.5: **`docs/guide/theorem-3.5-formalisation.md`**;
machine-readable record: `results/lean_certificate.toml`.

---

## 2. Architecture — the two tracks

The repository has **two logically distinct deliverables** that share one Julia
package (`A16Certificate`) because Julia requires a single `src/` at the package
root. They are separated by *role and dependency direction*, documented here.

### Track A — dedicated A16 certificate (the paper's supplement, [AH26])

The certified configuration is identified with the published Bingane--Audet
\(A_{16}\) by `test/fixtures/optigon_reference.jl`, a line-for-line vendored copy of the
upstream general \(n=2^s\) OPTIGON constructor: the test suite requires it to
reproduce the root, all sixteen vertices, the diameter graph, equilaterality and
the perimeter of the specialisation used here.

The flagship. Configuration-specific, exact-algebra + interval, produces the
`CERTIFIED` verdict for \(A_{16}\).

- `src/A16Certificate.jl` — the module; its parts are in `src/a16/`:
  `constructor.jl` (coordinates, F, F'), `geometry.jl` (convexity, inactive
  pairs), `linear_algebra.jl` (Jacobian, regularity test, Krawczyk),
  `exact_algebra.jl` (the rational-polynomial reduction), `data.jl`,
  `guarantees.jl`.
- `pipeline/stages/_bootstrap.jl`, `pipeline/stages/01_nominal_configuration.jl` … `pipeline/stages/06_prove_exact_identities.jl`
- `pipeline/certify_a16.jl` — the flagship driver + gate aggregation + provenance.
- `tools/archive_log.sh` — immutable dated log archival.
- outputs: `logs/final_run.txt` (latest), `logs/archive/<UTC>_a16_certificate.txt`
  (immutable), `results/a16_certificate.toml` (machine-readable, §1).
- verified by: `test/constructor.jl`, `test/exact_algebra.jl`,
  `test/certificate_stages.jl`, `test/optigon.jl` and most of
  `test/regressions.jl`.

### Track B — general small-polygon framework (research extension, not in the paper)

`n`-independent first-order structure certifier for a structured class of
candidates. **Not claimed by the article.** Broader but weaker: it certifies
*local first-order structure* for literature cases, never global optimality
(those are literature theorems it only re-certifies locally).

- `src/SmallPolygons.jl` — the general `certify(candidate)` engine.
- `src/ExactIdentity.jl` — general exact \(\mathbb Q(c,s)\) identity engine.
- `pipeline/certify_literature.jl` — benchmark driver (+ single-case CLI).
- `cases/**/candidate.jl` — data-only case definitions
  (n=4,6,8,A16 + 3 negative controls).
- outputs: `results/validation_certificate.toml`, `results/tables/table{1..4}_*.tex`.
- verified by: `test/framework_guards.jl` and `test/literature.jl`.

### Dependency direction (one-way)

Track B **uses** Track A (`SmallPolygons`/`certify_literature.jl` import
`A16Certificate` for `ACTIVE_EDGES`, `coordinates`, and the A16 benchmark row).
Track A does **not** depend on Track B: `certify_a16.jl` includes only
`_bootstrap.jl` + `01`–`06`, never `SmallPolygons.jl` or `ExactIdentity.jl`.
So the dedicated A16 certificate is self-contained and could be extracted
without Track B; the reverse is not true.

> The two tracks share `src/`, `pipeline/` and `test/`, because Julia pins one
> `src/` (and `test/runtests.jl`) at the package root. Inside them the split is
> visible: Track A is `src/A16Certificate.jl` + `src/a16/`,
> `pipeline/certify_a16.jl` + `pipeline/stages/`; Track B is
> `src/SmallPolygons.jl`, `src/ExactIdentity.jl`, `pipeline/certify_literature.jl`
> and `cases/`. The separation is enforced by the include graph above, not by
> the directories; the directories only make it easy to see (2026-09
> reorganisation, see `CHANGELOG.md`).

---

## 3. Documentation map — canonical hierarchy

To avoid "multiple authoritative narratives", each document has **one** role.
Read top-to-bottom; stop when your question is answered.

| # | Document | Role | Authoritative for |
|---|---|---|---|
| 1 | `README.md` | entry point | how to install/run; repo orientation |
| 2 | **`docs/guide/certificate-spec.md`** (this file) | **canonical spec** | **what is certified, scope, architecture, doc hierarchy** |
| 3 | `results/a16_certificate.toml` | machine-readable cert | the gates + certified values, for tooling |
| 4 | `logs/final_run.txt` + `logs/<UTC>_*.txt` | immutable execution record | provenance (commit, versions, hashes, PASS/FAIL) |
| 5 | `docs/guide/provenance-mapping.md` | referee-grade audit | line-by-line code ↔ paper mapping, per gate |
| 6 | `lean/README.md` + `results/lean_certificate.toml` | Lean layer | what the Lean kernel does and does **not** prove; its five checks |
| 7 | `src/`, `pipeline/`, `test/`, `lean/` | source + tests | ground truth (everything above describes these) |
| — | `docs/*.md` | supplementary notes | scope, limitations, theory audits, literature validation |
| — | `docs/audits/referee-report.md` | self-audit | our own adversarial review — *not* an external referee's report |

Material belonging to the authors' own writing workflow — draft manuscripts,
thesis chapters, personal study guides, supervisor correspondence — is
deliberately not part of this repository. The package ships the verification
and nothing else.

---

## 4. Reproduction & provenance

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate()'
julia --project=. test/runtests.jl                          # 651/651 assertions
julia --project=. pipeline/certify_a16.jl | tee logs/final_run.txt # -> CERTIFIED, writes results/a16_certificate.toml
tools/archive_log.sh logs/final_run.txt                     # immutable dated copy
julia --project=. pipeline/certify_literature.jl              # Track B benchmark

export PATH="$HOME/.elan/bin:$PATH"                           # Lean layer
(cd lean && lake exe cache get)                               # once; ~7 GB of Mathlib oleans
make lean                                                     # 5 checks -> LEAN CERTIFICATE PASS
make lean-certificate                                         # writes results/lean_certificate.toml

make paper                                                    # compile a16.tex, audit the LaTeX log
make paper-check                                              # reconcile the article vs certificate + Lean
tools/mutation_check.sh                                     # 12 planted defects, all must be rejected
```

Provenance is pinned by content, not just by commit: both
`logs/final_run.txt` and `results/{a16_certificate,validation_certificate}.toml`
print the git commit, `git_source_clean`, and the SHA256 of every load-bearing
source file. A release is self-consistent when all three declare the **same**
commit with `git_source_clean = true` and every printed hash matches the
archived file. `Manifest.toml` pins Julia 1.12.6 + IntervalArithmetic 0.22.36
(full resolved graph in the log's `Pkg.status()` section).
