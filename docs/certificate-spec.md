# docs/certificate-spec.md — canonical specification

> **Paper numbering.** Every `Theorem/Lemma/Prop/Remark N.M` below refers to
> `main.tex` as revised on 2026-09-14, when Section 6 was condensed and its
> technical detail moved to `supplement.tex`. Two earlier shifts are recorded
> here so the anchors can be traced. On 2026-08-20 Section 3 shifted by three:
> what earlier revisions called Theorem 3.8 and Lemma 3.7 became **Theorem 3.5**
> and **Lemma 3.4**. On 2026-09-14 Remark 6.3 left Section 6 for the supplement,
> so what was **Theorem 6.3** is now **Theorem 6.3**; Lemma 6.1 and
> Proposition 6.2 keep their numbers, and Sections 2, 3, 4 and 5 are unaffected.
> Two figures were inserted before the existing ones, so old Figures 1 and 2 are
> now **Figures 3 and 4**, and the two multiplier tables were merged, so old
> Table 4 is now **Table 3**. The frozen previous version is `main-1.tex`.
> If the article is edited again, re-check these anchors before releasing.


This is the single **authoritative** description of what this repository
certifies, how its two tracks are separated, and which document is the source
of truth for what. Everything else is either machine-readable data, source,
tests, or supplementary explanatory notes (§3). If any other document conflicts
with this one on scope or claims, **this document wins** and the other is a bug.

Paper: J. Ayala Hoffmann, *"Stability of Equilateral Small Polygons"*
which cites this package as **[AH26]**.

---

## 1. What is certified — the dedicated A16 certificate

`scripts/run_all.jl` certifies, for the exact Bingane–Audet hexadecagon
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
(regenerated on every `run_all.jl` run; one `[[gate]]` per row here).

| Gate | Paper ref | Status | Certified quantity |
|---|---|---|---|
| Unique constructor root | Prop 6.2(1) | CERTIFIED | interval Newton: \(0\notin F'(Z_{\rm root})\), \(N(Z_{\rm root})\subset\operatorname{int}Z_{\rm root}\); unique in box **and** in the full search interval |
| Side length / perimeter | Prop 6.2(2) | CERTIFIED | \(\ell=0.1959554930055385228\ldots\), \(16\ell=3.1352878880886163663\ldots\); enclosed over \(Z_{\rm root}\) with outward rounding, widths \(<2\times10^{-30}\) and \(<3.19\times10^{-29}\) |
| Strict convexity + cyclic order | Prop 6.2(3) | CERTIFIED | min support determinant \(\ge 0.0074882049306989244\) (at edge/vertex \((10,12)\)) |
| Exact active graph + inactive margin | Prop 6.2(4) | CERTIFIED | \(\delta_{\rm inact}\ge 0.0080997106581357295\) (critical pair \(\{4,12\}\)) |
| Positive multipliers + stationarity | Prop 6.2(5) | CERTIFIED | \(\min\lambda_{ij}\ge 0.0918667776833353997\) (edge \(\{6,13\}\)); omitted-eq recovery via \(\det Q=y_1-y_8<0\) |
| Rank 30 \(\Rightarrow I_{\rm eq}=R_{\rm eq}\) | Prop 6.2(6) | CERTIFIED | \(\lVert I-CM\rVert_\infty\le 1.419383643581978\times10^{-25}<1\) |
| 16 side + 15 diameter equalities | Lemma 6.1 | PROVEN | exact \(\mathbb Q[c]\) algebra, 16/16 + 15/15; 29 unconditional, 2 (\(\{3,4\},\{12,13\}\)) \(=F_c\); no interval containing zero |
| Box nesting \(Z_{\rm root}\subset\operatorname{int}Z_{\rm cert}\) | Prop 6.2 | CERTIFIED | composition gate: \(10^{-30}\subset 10^{-28}\) |

Final banner (from `run_all.jl`): `FINAL FIRST-ORDER CERTIFICATE: CERTIFIED`,
`ROOT UNIQUENESS ... PROVED`, `TOPOLOGICAL LOCAL MAXIMALITY: NOT ESTABLISHED BY
*THIS* RUN — PROVED IN LEAN` (the interval layer certifies the hypotheses of
Thm 3.5; the conclusion is `Chiquipoli.Feasible.A16_locally_maximal`),
`GLOBAL OPTIMALITY: NOT CLAIMED`.

Full line-by-line mapping of each gate to the exact source function and paper
sentence: **`docs/provenance-mapping.md`** (the referee-grade audit; this section
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
the formalisation of Theorem 3.5: **`docs/theorem-3.5-formalisation.md`**;
machine-readable record: `results/lean_certificate.toml`.

---

## 2. Architecture — the two tracks

The repository has **two logically distinct deliverables** that share one Julia
package (`A16Certificate`) because Julia requires a single `src/` at the package
root. They are separated by *role and dependency direction*, documented here.

### Track A — dedicated A16 certificate (the paper's supplement, [AH26])

The certified configuration is identified with the published Bingane--Audet
\(A_{16}\) by `test/optigon_reference.jl`, a line-for-line vendored copy of the
upstream general \(n=2^s\) OPTIGON constructor: the test suite requires it to
reproduce the root, all sixteen vertices, the diameter graph, equilaterality and
the perimeter of the specialisation used here.

The flagship. Configuration-specific, exact-algebra + interval, produces the
`CERTIFIED` verdict for \(A_{16}\).

- `src/A16Certificate.jl` — constructor coordinates, Jacobian, exact
  rational-polynomial reduction, interval multiplier solve.
- `scripts/_bootstrap.jl`, `scripts/01_nominal.jl` … `scripts/06_exact_identities.jl`
- `scripts/run_all.jl` — the flagship driver + gate aggregation + provenance.
- `tools/archive_log.sh` — immutable dated log archival.
- outputs: `logs/final_run.txt` (latest), `logs/<UTC>_a16_certificate.txt`
  (immutable), `results/a16_certificate.toml` (machine-readable, §1).
- verified by: the A16-specific testsets in `test/runtests.jl`.

### Track B — general small-polygon framework (research extension, not in the paper)

`n`-independent first-order structure certifier for a structured class of
candidates. **Not claimed by the article.** Broader but weaker: it certifies
*local first-order structure* for literature cases, never global optimality
(those are literature theorems it only re-certifies locally).

- `src/SmallPolygons.jl` — the general `certify(candidate)` engine.
- `src/ExactIdentity.jl` — general exact \(\mathbb Q(c,s)\) identity engine.
- `scripts/run_literature.jl` — benchmark driver (+ single-case CLI).
- `examples/literature/**/candidate.jl` — data-only case definitions
  (n=4,6,8,A16 + 3 negative controls).
- outputs: `results/validation_certificate.toml`, `results/tables/table{1..4}_*.tex`.
- verified by: the literature/benchmark testsets in `test/runtests.jl`.

### Dependency direction (one-way)

Track B **uses** Track A (`SmallPolygons`/`run_literature` import
`A16Certificate` for `ACTIVE_EDGES`, `coordinates`, and the A16 benchmark row).
Track A does **not** depend on Track B: `run_all.jl` includes only
`_bootstrap.jl` + `01`–`06`, never `SmallPolygons.jl` or `ExactIdentity.jl`.
So the dedicated A16 certificate is self-contained and could be extracted
without Track B; the reverse is not true.

> A physical top-level split (`dedicated/`, `general/`) was considered and
> deliberately **not** done: it would break Julia's package layout (which
> pins `src/` at the root), rewrite every `@__DIR__/..` provenance path, and
> diverge the tree from the `v1.0.0` release whose hashes are already pinned.
> The separation is by role + dependency direction, enforced by the
> include-graph above, not by directory nesting.

---

## 3. Documentation map — canonical hierarchy

To avoid "multiple authoritative narratives", each document has **one** role.
Read top-to-bottom; stop when your question is answered.

| # | Document | Role | Authoritative for |
|---|---|---|---|
| 1 | `README.md` | entry point | how to install/run; repo orientation |
| 2 | **`docs/certificate-spec.md`** (this file) | **canonical spec** | **what is certified, scope, architecture, doc hierarchy** |
| 3 | `results/a16_certificate.toml` | machine-readable cert | the gates + certified values, for tooling |
| 4 | `logs/final_run.txt` + `logs/<UTC>_*.txt` | immutable execution record | provenance (commit, versions, hashes, PASS/FAIL) |
| 5 | `docs/provenance-mapping.md` | referee-grade audit | line-by-line code ↔ paper mapping, per gate |
| 6 | `lean/README.md` + `results/lean_certificate.toml` | Lean layer | what the Lean kernel does and does **not** prove; its five checks |
| 7 | `src/`, `scripts/`, `test/`, `lean/` | source + tests | ground truth (everything above describes these) |
| — | `docs/*.md` | supplementary notes | scope, limitations, theory audits, literature validation |
| — | `docs/referee-report.md` | self-audit | our own adversarial review — *not* an external referee's report |

Material belonging to the authors' own writing workflow — draft manuscripts,
thesis chapters, personal study guides, supervisor correspondence — is
deliberately not part of this repository. The package ships the verification
and nothing else.

---

## 4. Reproduction & provenance

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate()'
julia --project=. test/runtests.jl                          # 628/628 assertions
julia --project=. scripts/run_all.jl | tee logs/final_run.txt # -> CERTIFIED, writes results/a16_certificate.toml
tools/archive_log.sh logs/final_run.txt                     # immutable dated copy
julia --project=. scripts/run_literature.jl              # Track B benchmark

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
