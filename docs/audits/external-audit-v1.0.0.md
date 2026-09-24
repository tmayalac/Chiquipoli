# External audit of v1.0.0: what became of each finding

An external audit of the v1.0.0 release (September 2026, *Audit of the
Chiquipoli v1.0.0 verification package*) found **no error that invalidates a
certified statement**. It listed 12 findings in the code (D01–D12), 7 in the
documentation and the article (M01–M07), and no finding of severity S3
(a certified statement lacks support) or S4 (a certified statement is false).

It audited the release **before** the restructuring. Paths below are the
current ones: `scripts/0*.jl` became `pipeline/stages/0*.jl`, and
`scripts/run_all.jl` became `pipeline/certify_a16.jl`. The family layer
(A32, A64) did not exist then and was not audited.

This file records, for each finding: where it was fixed, and what now fails if
the fix is undone. The *guard* column is the important one. A fix with no guard
can come back without anyone noticing.

| ID | Sev. | Finding | Resolution | Guard against regression |
|---|---|---|---|---|
| D01 | S2 | the verdict did not require root uniqueness on `I_search` | `final_pass` conjoins `r2.unique_in_search_interval` (`pipeline/certify_a16.jl`) | test *the A16 verdict conjoins every gate* (`test/regressions.jl`); mutation *root uniqueness dropped from final_pass* (`tools/mutation_check.sh`) |
| D02 | S1 | failure paths were inconsistent (abort, crash after the verdict, report) | every stage returns the same fields on failure; a failed gate is a `FAIL` entry, the certificate is still written | test *failure paths report instead of crashing* (`test/certificate_stages.jl`) |
| D03 | S1 | the side-length gate was recorded as passed unconditionally | `passed = rl.pass`, and `rl.pass` enters `final_pass` | test *the A16 verdict conjoins every gate* |
| D04 | S1 | box nesting was checked by radii | endpoints of `Z_root` checked strictly inside the box each of stages 03–05 evaluated (`strictly_inside`) | none automatic beyond the run itself |
| D05 | S1 | norm bounds summed with round-to-nearest | row sums accumulated as intervals, their supremum reported (`src/a16/linear_algebra.jl`, `src/SmallPolygons.jl`) | mutation *Krawczyk enclosure: outward rounding → round to nearest* covers the neighbouring enclosure |
| D06 | S1 | the inactive margin bypassed the guarantee-flag policy | literal routed through `_lit`, `assert_guaranteed` on the margin (`pipeline/stages/03_certify_geometry.jl`) | the NG-flag regression tests (`test/regressions.jl`) |
| D07 | S1 | the rounding self-check was printed, not enforced | `@assert inf(r) < 1//3 < sup(r)` (`pipeline/certify_a16.jl`) | the assertion itself, at every run; no test can switch the rounding mode off |
| D08 | S1 | `Fprime` was not tested against `Ffun` | chain-rule test `F'(t) = −sin t · Fc'(cos t)` (`test/certificate_stages.jl`) | mutation *derivative: Fprime loses a factor 2* |
| D09 | S0 | the rank upper bound is encoded as constants | informational; correct as an algebraic theorem | — |
| D10 | S0 | the Jacobian gates depend on the exact identities | the supplement now states that steps (iv), (v) rest on (i) | — |
| D11 | S1 | Track B labelled an equality consistency check `:CERTIFIED` | reported `:CONSISTENT`; the equality itself is `:PROVEN` by exact algebra | `test/literature.jl` asserts `:CONSISTENT` |
| D12 | S1 | Track B changed the global BigFloat precision | scoped `setprecision(...) do` | — |
| M01 | S1 | README counts of controls and audited theorems stale | corrected | `make paper-check` ties both counts to the recorded Lean certificate |
| M02 | S1 | README count of planted defects stale | corrected (now 16) | `make paper-check` ties it to `tools/mutation_check.sh` |
| M03 | S1 | lean/README said the square instantiation was not written | corrected | — |
| M04 | S1 | a Lean docstring cited a non-existent Remark 2.7 | corrected | — |
| M05 | S0 | the supplement called the pipeline non-iterative and aborting | reworded: two steps adapt within themselves; a failed step is recorded, not aborted | — |
| M06 | S0 | the supplement called the Krawczyk system nonlinear | "square linear system" | — |
| M07 | S2 | the supplement cited non-equilateral optima as equilateral benchmarks | now cites [Vin50] and [AHMP04]; [Vin50] added to its bibliography | — |

The audit's limitations still apply to it: it did not run Julia or Lean, and
its independent re-execution (mpmath, SymPy) implements the same operators, so
it rules out implementation errors, not errors in the method. Its independent
reproduction of every certified bound of A16 [V09] is a real, second-source
confirmation, and is cited as such.
