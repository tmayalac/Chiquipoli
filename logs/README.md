Execution logs for `pipeline/certify_a16.jl` (the dedicated A16 certificate).

- `final_run.txt` — the **latest** run. Mutable: `make verify` overwrites it
  every time. This is intentional for day-to-day development.
- `nominal_diagnostics.txt` — the nominal (floating, uncertified) configuration.
- `archive/<UTC-timestamp>_a16_certificate.txt`
  — **immutable** archived copies, one per release. Never overwritten: the
  archival script refuses if the destination already exists, and the file is
  written read-only. Create one with `make archive-log` (or
  `tools/archive_log.sh logs/final_run.txt`) whenever a run is worth
  preserving permanently (in particular, before tagging a release) — the
  filename is derived from the timestamp already printed in the log's own
  provenance header, so it always matches the content, not the moment the
  archival command happened to run.

  The archived logs are historical records and are kept byte for byte as they
  were written, so the older ones name files by the paths they had at the
  time (`scripts/run_all.jl`, and so on). `CHANGELOG.md` maps each old path to
  its current one.

Every log (latest or archived) must contain the full provenance header:
Julia version, `Pkg.status()` (both project and manifest mode), interval
precision, the directed-rounding self-check, git commit (flagged dirty if the
load-bearing source paths differ from HEAD), SHA256 of every load-bearing
source file, and every PASS/FAIL line the certificate blocks print. This is
enforced by `pipeline/certify_a16.jl`'s `print_provenance()`, not by convention
alone.
