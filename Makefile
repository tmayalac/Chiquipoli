.PHONY: help test nominal verify certificate lean lean-build lean-cache \
        lean-certificate literature mutation-check archive-log clean \
        paper paper-check

help:
	@echo "Chiquipoli — interval and exact verification package for A16"
	@echo
	@echo "  make test              run the Julia test suite"
	@echo "  make verify            run the full certificate, tee to logs/final_run.txt"
	@echo "  make archive-log       freeze logs/final_run.txt under a timestamped name"
	@echo "  make literature        re-certify the n=4,6,8 literature cases + negative controls"
	@echo "  make nominal           print the nominal configuration only (no certificate)"
	@echo
	@echo "  make lean-cache        download prebuilt Mathlib oleans (~7 GB, once)"
	@echo "  make lean              full five-check verification of the Lean layer"
	@echo "  make lean-certificate  record those checks as results/lean_certificate.toml"
	@echo
	@echo "  make paper             compile a16.tex and audit the LaTeX log"
	@echo "  make paper-check       reconcile the article against the certificate and Lean"
	@echo
	@echo "  make mutation-check    break the package on purpose; the checks must catch it"
	@echo
	@echo "  make clean             remove editor and build leftovers"

# --- the certificate -------------------------------------------------------

test:
	julia --project=. test/runtests.jl

nominal:
	julia --project=. scripts/01_nominal.jl

# The headline target. Writes results/a16_certificate.toml and the full log.
verify:
	julia --project=. scripts/run_all.jl | tee logs/final_run.txt

certificate: verify

# Re-certifies the solved literature cases and the deliberately broken ones.
literature:
	julia --project=. scripts/run_literature.jl

# Plants known defects and requires the verification to reject each one. A
# suite that has never failed is not a tested suite; this is what shows the
# checks are capable of failing. Needs a clean tree: it edits tracked files
# and restores them from git.
mutation-check:
	tools/mutation_check.sh

# Freezes the current log under a timestamped, read-only name.
archive-log:
	tools/archive_log.sh logs/final_run.txt

# --- the article ----------------------------------------------------------
# a16.tex is a working copy at the repository root and is not tracked (see
# .gitignore), so these two targets are how it is held to the certificate.
#
# `paper` compiles it and audits the LaTeX log. The audit is deliberately
# case-insensitive and does not key on the word "Warning": LaTeX writes
# "Reference ... undefined" in lower case, and pdfTeX writes "Missing
# character" with no severity word at all, so a naive grep for "Warning" or
# "Undefined" passes a document with unresolved references and dropped glyphs.
# Both mistakes were made here before this target existed.
paper:
	@test -f a16.tex || { echo "a16.tex not present; nothing to compile"; exit 0; }
	@mkdir -p .texbuild
	@for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error \
	    -output-directory=.texbuild a16.tex >/dev/null 2>&1 || \
	    { echo "FAIL  pdflatex errored"; exit 1; }; done
	@cp .texbuild/a16.pdf a16.pdf
	@log=.texbuild/a16.log; rc=0; \
	 n=$$(grep -icE '(reference|citation)[^.]*undefined' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n unresolved reference or citation"; rc=1; }; \
	 n=$$(grep -c 'Missing character' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n missing character (glyph dropped)"; rc=1; }; \
	 n=$$(grep -c 'Font shape' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n undefined font shape"; rc=1; }; \
	 n=$$(grep -icE 'multiply.defined' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n multiply defined label"; rc=1; }; \
	 n=$$(grep -c '^!' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n TeX error"; rc=1; }; \
	 n=$$(grep -cE '^Overfull .hbox \([0-9]{2,}\.' $$log); \
	   [ "$$n" -eq 0 ] || { echo "FAIL  $$n overfull hbox over 10pt"; rc=1; }; \
	 if [ $$rc -eq 0 ]; then \
	   echo "PAPER BUILD PASS  $$(pdfinfo a16.pdf | awk '/Pages/{print $$2}') pages, log clean"; \
	 fi; exit $$rc

# Reconciles every number and claim in the article against the regenerated
# certificate and against the Lean sources. Reads the compiled PDF, since a
# mistyped table cell is invisible in the LaTeX source until it is typeset.
paper-check:
	julia --project=. scripts/check_paper.jl

# --- the Lean layer (see lean/README.md for scope) -------------------------

lean-cache:
	cd lean && lake exe cache get

lean-build:
	cd lean && lake build

# Five checks: build, no admitted goals, axiom audit, negative controls, and
# byte-identical regeneration of the generated files from the Julia source.
lean:
	cd lean && ./scripts/verify.sh

lean-certificate:
	julia --project=. scripts/run_lean_certificate.jl

# ---------------------------------------------------------------------------

clean:
	find . -name '*.aux' -o -name '*.log' -o -name '*.out' -o -name '*.toc' \
	       -o -name '*.bbl' -o -name '*.blg' -o -name '*.synctex.gz' \
	       | grep -v '^./lean/.lake/' | xargs rm -f
