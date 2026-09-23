# tools

Development and verification utilities. **Nothing here is part of the hashed
provenance chain** — that is `src/`, `pipeline/` and `test/` (and `cases/` for
the literature certificate), and the boundary is deliberate (see the guardrail
in `pipeline/certify_a16.jl`).

| File | What it does |
|---|---|
| `mutation_check.sh` | Plants known defects in the sources and requires the checks to reject every one. Needs a clean working tree: it edits tracked files and restores them from git. |
| `archive_log.sh` | Freezes `logs/final_run.txt` as a read-only copy in `logs/archive/`, named by its UTC timestamp. |
| `independent_check/independent_check.py` | Second-source verification of the 29-vs-2 identity finding, in SymPy rather than interval arithmetic. |
| `independent_check/independent_check_output.txt` | Its recorded output. |
| `independent_check/independent-check.md` | What "independent" means here, and what it does not mean. |

Run them through the `Makefile` rather than directly: `make mutation-check`,
`make archive-log`.
