# results

The machine-readable records of every certificate, and the article's tables.
Everything here is written by a script and never edited by hand. Each record
carries the git commit, whether the source tree was clean, and the SHA-256 of
every file its verdict depends on.

| File | Written by | What it records |
|---|---|---|
| `a16_certificate.toml` | `make verify` (`pipeline/certify_a16.jl`) | the interval certificate of A16: every gate, its bounds, the verdict |
| `validation_certificate.toml` | `make literature` (`pipeline/certify_literature.jl`) | the literature benchmark, n = 4, 6, 8, 16, 32, 64, Z32, Z64, and the three broken controls |
| `lean_certificate.toml` | `make lean-certificate` | the A16 Lean layer: its five checks, counts, scope |
| `lean_family_certificate.toml` | `make lean-family-certificate` | the family Lean layer (A16, A32, A64): its five checks, the certified numbers of each case, scope |
| `family/A16.toml`, `family/A32.toml`, `family/A64.toml` | `julia --project=. pipeline/certify_family.jl <n>` (all three in `make check-all`) | the family certificate of each candidate: the same ten gates for every n, among them the published OPTIGON source run unchanged in exact arithmetic |
| `family/Z32.toml`, `family/Z64.toml` | `julia --project=. pipeline/certify_z.jl <n>` (both in `make check-all`) | the certificate of Z32 and Z64: eight gates, the margins, and what is not claimed |
| `independent/A16.toml`, `A32`, `A64`, `Z32`, `Z64` | `make independent` (`pipeline/independent/verify.py`) | the same numerical gates, computed by a second implementation in Python: roots, convexity, inactive margin, regularity, multipliers. No timings, so a re-run is byte-identical |
| `tables/*.tex` | `make literature` | the benchmark and family tables, in LaTeX |

`make check-all` regenerates every record in one run. `make check-records`
compares them with the tree. For the family record, `make
lean-family-record` answers in seconds, without Lean, whether it still
describes the tree.

A record is evidence only while it describes the tree. After any edit to a
file it hashes, regenerate it on a clean tree and commit the result.
