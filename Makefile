.PHONY: help test nominal verify certificate lean lean-build lean-cache \
        lean-certificate lean-family literature mutation-check stress-family \
        stress-family-generator archive-log clean \
        check check-all check-lean check-case literature-case lean-family-case \
        stress-case lean-family-certificate lean-family-record A16 A32 A64 \
        lean-general lean-general-case \
        a16 a32 a64 a128 a256 a512 a1024 \
        a16-complete a32-complete a64-complete a128-complete a256-complete \
        a512-complete a1024-complete \
        check-records status radius

help:
	@echo "Chiquipoli — interval and exact verification package for A16"
	@echo
	@echo "  EVERYTHING, WITH A SUMMARY TABLE (tools/check_all.sh)"
	@echo "  make check             quick: Julia only, no Lean"
	@echo "  make check-all         every check and every record, in order (16 GB of memory)"
	@echo "  make check-lean        both Lean layers, verified and recorded"
	@echo "  make check-case N=32   one case (N = 4, 6, 8, 16, 32, 64): certifier, Lean, stress"
	@echo
	@echo "  ONE POLYGON, QUICKLY: its Julia certificate only (writes no record)"
	@echo "  make a16  a32  a64  a128  a256  a512  a1024"
	@echo "                         the family certificate (10 gates); a16 also the article's own"
	@echo
	@echo "  ONE POLYGON, EVERY LAYER: suite, Julia, Lean, controls, planted defects (writes no record)"
	@echo "  make a16-complete ... a1024-complete"
	@echo "                         general Lean theorem for $(shell sed -n 's/^const FAMILY_TRIG_N = (\(.*\))/\1/p' cases/exact_coords.jl);"
	@echo "                         per-case Lean also for $(shell sed -n 's/^const FAMILY_LEAN_N = (\(.*\))/\1/p' cases/exact_coords.jl);"
	@echo "                         for the others the Lean stages are SKIP and the verdict INCOMPLETE"
	@echo "  make A16 / A32 / A64   the same as a16-complete / a32-complete / a64-complete"
	@echo
	@echo "  ONE CASE, ONE LAYER"
	@echo "  make literature-case N=32   the general certifier on one case"
	@echo "  make lean-family-case N=32  the five family Lean checks on one case (partial run)"
	@echo "  make stress-case N=32       the 8+8 planted defects of one case"
	@echo
	@echo "  make test              run the Julia test suite"
	@echo "  make verify            run the full certificate, tee to logs/final_run.txt"
	@echo "  make archive-log       freeze logs/final_run.txt under a timestamped name"
	@echo "  make literature        re-certify the literature cases (n=4,6,8,16,32,64) + controls"
	@echo "  make nominal           print the nominal configuration only (no certificate)"
	@echo "  make radius            certify an explicit radius of strict local maximality of A16"
	@echo "                         -> results/radius_certificate.toml (docs/guide/radius.md)"
	@echo
	@echo "  make lean-cache        download prebuilt Mathlib oleans (~7 GB, once)"
	@echo "  make lean              full five-check verification of the Lean layer"
	@echo "  make lean-certificate  record those checks as results/lean_certificate.toml"
	@echo "  make lean-family       the same five checks for the family layer (A16, A32, A64)"
	@echo "  make lean-general      the five checks for the general Lean theorem (A16 ... A256)"
	@echo "  make lean-general-case N=256  the same, one case"
	@echo "  make lean-family-certificate  record them as results/lean_family_certificate.toml"
	@echo "  make lean-family-record       does that record still describe the tree? (seconds)"
	@echo
	@echo "  make status            what is certified, in tables, read from results/"
	@echo "  make check-records     every record against the tree, the hashes and the Lean layer"
	@echo
	@echo "  make mutation-check    break the package on purpose; the checks must catch it"
	@echo "  make stress-family     the same for A16/A32/A64: generator, Lean and harness"
	@echo "  make stress-family-generator   only the generator's pre-checks (Julia, ~2 min)"
	@echo
	@echo "  make clean             remove editor and build leftovers"

# --- the certificate -------------------------------------------------------

test:
	julia --project=. test/runtests.jl

nominal:
	julia --project=. pipeline/stages/01_nominal_configuration.jl

# The headline target. Writes results/a16_certificate.toml and the full log.
verify:
	julia --project=. pipeline/certify_a16.jl | tee logs/final_run.txt

certificate: verify

# Re-certifies the solved literature cases and the deliberately broken ones.
literature:
	julia --project=. pipeline/certify_literature.jl

# Plants known defects and requires the verification to reject each one. A
# suite that has never failed is not a tested suite; this is what shows the
# checks are capable of failing. Needs a clean tree: it edits tracked files
# and restores them from git.
mutation-check:
	tools/mutation_check.sh

# The family layer (A16, A32, A64): each of eight planted generator defects must
# be refused by the generator's exact pre-checks AND, with those switched off,
# rejected by Lean inside the planted declaration; and verify_family.sh must
# reject a sabotaged harness. The first two layers never touch tracked files;
# the third needs a clean tree. STRESS_CASES="16" restricts the first two.
stress-family:
	tools/stress_family.sh all

stress-family-generator:
	tools/stress_family.sh generator

# Freezes the current log under a timestamped, read-only name.
archive-log:
	tools/archive_log.sh logs/final_run.txt

# --- the summary -----------------------------------------------------------
# What is certified, read from results/: tables, no computation.
status:
	julia --project=. chiquipoli.jl status

# --- the records ----------------------------------------------------------
# Every certificate verdict, the provenance of every record (one commit, a clean
# tree), the SHA256 of every load-bearing source file, the published bounds,
# the Lean layer and the family records, against the tree.
check-records:
	julia --project=. pipeline/check_records.jl

# --- the Lean layer (see lean/README.md for scope) -------------------------

lean-cache:
	cd lean && lake exe cache get

lean-build:
	cd lean && lake build

# Five checks: build, no admitted goals, axiom audit, negative controls, and
# byte-identical regeneration of the generated files from the Julia source.
lean:
	cd lean && ./verify.sh

lean-certificate:
	julia --project=. pipeline/record_lean_certificate.jl

# The Bingane–Audet family A_n (lean/ChiquipoliFamily/): the same five checks,
# on a separate library, so that nothing above changes. See
# lean/ChiquipoliFamily/README.md.
lean-family:
	cd lean && ./verify_family.sh

lean-family-certificate:
	julia --project=. pipeline/record_lean_family_certificate.jl

lean-family-record:
	julia --project=. pipeline/record_lean_family_certificate.jl --check

# --- everything, and one case at a time (tools/check_all.sh) -----------------
# Every stage runs even if one fails; the run ends with a PASS/FAIL/SKIP table.
# A stage that needs a clean git tree is skipped on a dirty one, and the
# verdict is then INCOMPLETE, never PASS.
check:
	tools/check_all.sh quick

check-all:
	tools/check_all.sh all

check-lean:
	tools/check_all.sh lean

# One polygon: `make a<n>` is its Julia certificate only, in seconds; `make
# a<n>-complete` is every layer (tools/check_all.sh candidate). The members are
# FAMILY_N in cases/exact_coords.jl.
a16 a32 a64 a128 a256 a512 a1024:
	tools/check_all.sh fast $(@:a%=%)

a16-complete a32-complete a64-complete a128-complete a256-complete a512-complete a1024-complete:
	tools/check_all.sh candidate $(patsubst a%-complete,%,$@)

A16: a16-complete
A32: a32-complete
A64: a64-complete

check-case:
	@test -n "$(N)" || { echo "usage: make check-case N=<4|6|8|16|32|64>"; exit 2; }
	tools/check_all.sh case $(N)

literature-case:
	@test -n "$(N)" || { echo "usage: make literature-case N=<4|6|8|16|32|64>"; exit 2; }
	julia --project=. pipeline/certify_literature.jl $(N)

lean-family-case:
	@test -n "$(N)" || { echo "usage: make lean-family-case N=<16|32|64>"; exit 2; }
	cd lean && FAMILY_CASES=$(N) ./verify_family.sh

stress-case:
	@test -n "$(N)" || { echo "usage: make stress-case N=<16|32|64>"; exit 2; }
	STRESS_CASES=$(N) tools/stress_family.sh generator && STRESS_CASES=$(N) tools/stress_family.sh lean

# ---------------------------------------------------------------------------

clean:
	find . -name '*.aux' -o -name '*.log' -o -name '*.out' -o -name '*.toc' \
	       -o -name '*.bbl' -o -name '*.blg' -o -name '*.synctex.gz' \
	       | grep -v '^./lean/.lake/' | xargs rm -f

# The general Lean certificate of the family: ONE theorem for every n = 16k
# (lean/ChiquipoliFamily/Interval/Assemble.lean), kernel-checked data per n.
lean-general:
	cd lean && ./verify_general.sh

lean-general-case:
	cd lean && TRIG_CASES=$(N) ./verify_general.sh

# An explicit radius r of the strict local maximality of A16 (docs/guide/radius.md).
radius:
	julia --project=. pipeline/certify_radius.jl
