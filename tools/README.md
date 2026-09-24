# tools

Development and verification utilities. **Nothing here is part of the hashed
provenance chain** — that is `src/`, `pipeline/` and `test/` (and `cases/` for
the literature certificate), and the boundary is deliberate (see the guardrail
in `pipeline/certify_a16.jl`).

| File | What it does |
|---|---|
| `mutation_check.sh` | Plants known defects in the sources and requires the checks to reject every one. Needs a clean working tree: it edits tracked files and restores them from git. |
| `stress_family.sh` | Stress test of the family layer (A16, A32, A64). Eight kinds of generator defect per case must each be refused by the generator's exact pre-checks and, with those switched off, rejected by Lean inside the planted declaration; eleven sabotages of `verify_family.sh` must each fail the responsible step. The first two parts write only to scratch directories; the third needs a clean tree. Do not run it at the same time as `mutation_check.sh`, which edits `cases/`, one of the generator's inputs. |
| `stress_family_locate.py` | Its two exact checks: every module upstream of a planted file is byte-identical to the tracked one, and every Lean error lies inside the planted declaration. |
| `archive_log.sh` | Freezes `logs/final_run.txt` as a read-only copy in `logs/archive/`, named by its UTC timestamp. |
| `independent_check/independent_check.py` | Second-source verification of the 29-vs-2 identity finding, in SymPy rather than interval arithmetic. |
| `independent_check/independent_check_output.txt` | Its recorded output. |
| `independent_check/independent-check.md` | What "independent" means here, and what it does not mean. |

Run them through the `Makefile` rather than directly: `make mutation-check`,
`make stress-family` (or `make stress-family-generator`, Julia only),
`make archive-log`.
