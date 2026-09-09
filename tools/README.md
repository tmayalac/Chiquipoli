# tools

Development and verification utilities. **Nothing here is part of the hashed
provenance chain** — that is `src/`, `scripts/` and `test/`, and the boundary is
deliberate (see the guardrail in `scripts/run_all.jl`).

| File | What it does |
|---|---|
| `mutation_check.sh` | Plants known defects in the sources and requires the checks to reject every one. Needs a clean working tree: it edits tracked files and restores them from git. |
| `archive_log.sh` | Freezes `logs/final_run.txt` under a timestamped, read-only name. |
| `independent_check.py` | Second-source verification of the 29-vs-2 identity finding, in SymPy rather than interval arithmetic. |
| `independent_check_output.txt` | Its recorded output. |
| `independent-check.md` | What "independent" means here, and what it does not mean. |

Run them through the `Makefile` rather than directly: `make mutation-check`,
`make archive-log`.
