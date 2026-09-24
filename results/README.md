# results

The machine-readable records of every certificate, and the article's tables.
Everything here is written by a script and never edited by hand. Each record
carries the git commit, whether the source tree was clean, and the SHA-256 of
every file its verdict depends on.

| File | Written by | What it records |
|---|---|---|
| `a16_certificate.toml` | `make verify` (`pipeline/certify_a16.jl`) | the interval certificate of A16: every gate, its bounds, the verdict |
| `validation_certificate.toml` | `make literature` (`pipeline/certify_literature.jl`) | the literature benchmark, n = 4, 6, 8, 16, 32, 64, and the three broken controls |
| `lean_certificate.toml` | `make lean-certificate` | the A16 Lean layer: its five checks, counts, scope |
| `lean_family_certificate.toml` | `make lean-family-certificate` | the family Lean layer (A16, A32, A64): its five checks, the certified numbers of each case, scope |
| `tables/*.tex` | `make literature` | the tables of the article |

`make check-all` regenerates all four records in one run. `make paper-check`
compares them with the tree and the article. For the family record, `make
lean-family-record` answers in seconds, without Lean, whether it still
describes the tree.

A record is evidence only while it describes the tree. After any edit to a
file it hashes, regenerate it on a clean tree and commit the result.
