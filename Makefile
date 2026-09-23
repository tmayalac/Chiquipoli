.PHONY: help test nominal verify certificate lean lean-build lean-cache \
        lean-certificate literature mutation-check archive-log clean \
        paper paper-build paper-check

PAPER := paper

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
	@echo "  make paper             compile paper/main.tex + supplement and audit the logs"
	@echo "  make paper-check       reconcile the article against the certificate and Lean"
	@echo
	@echo "  make mutation-check    break the package on purpose; the checks must catch it"
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

# Freezes the current log under a timestamped, read-only name.
archive-log:
	tools/archive_log.sh logs/final_run.txt

# --- the article ----------------------------------------------------------
# The article is paper/main.tex, with paper/supplement.tex beside it;
# paper/archive/ holds the frozen previous version. All of paper/ is a working
# copy and is not tracked (see .gitignore), so these targets are how the article
# is held to the certificate.
#
# `paper` compiles both and audits the LaTeX logs. The audit is deliberately
# case-insensitive and does not key on the word "Warning": LaTeX writes
# "Reference ... undefined" in lower case, and pdfTeX writes "Missing
# character" with no severity word at all, so a naive grep for "Warning" or
# "Undefined" passes a document with unresolved references and dropped glyphs.
# Both mistakes were made here before this target existed.
#
# Order matters. The supplement uses `xr` to cite the article's own numbering,
# so it reads main.aux; TEXINPUTS puts the build directory on the search path.
paper:
	@if [ -f $(PAPER)/main.tex ]; then $(MAKE) --no-print-directory paper-build; \
	 else echo "$(PAPER)/main.tex not present; nothing to compile"; fi

# Internal: every recipe line runs inside $(PAPER)/, where the article, its
# build directory and the Overleaf latexmkrc live.
paper-build:
	@cd $(PAPER) && mkdir -p .texbuild
	@cd $(PAPER) && for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error \
	    -output-directory=.texbuild main.tex >/dev/null 2>&1 || \
	    { echo "FAIL  pdflatex errored on main.tex"; exit 1; }; done
	@cd $(PAPER) && cp .texbuild/main.pdf main.pdf
	@cd $(PAPER) && if [ -f supplement.tex ]; then \
	   for i in 1 2 3; do TEXINPUTS=.texbuild: pdflatex -interaction=nonstopmode \
	       -halt-on-error -output-directory=.texbuild supplement.tex >/dev/null 2>&1 || \
	       { echo "FAIL  pdflatex errored on supplement.tex"; exit 1; }; done; \
	   cp .texbuild/supplement.pdf supplement.pdf; \
	 fi
	@cd $(PAPER) && rc=0; for f in main supplement; do \
	   log=.texbuild/$$f.log; [ -f "$$log" ] || continue; \
	   n=$$(LC_ALL=C grep -aicE '(reference|citation)[^.]*undefined' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n unresolved reference or citation"; rc=1; }; \
	   n=$$(LC_ALL=C grep -ac 'Missing character' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n missing character (glyph dropped)"; rc=1; }; \
	   n=$$(LC_ALL=C grep -ac 'Font shape' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n undefined font shape"; rc=1; }; \
	   n=$$(LC_ALL=C grep -aicE 'multiply.defined' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n multiply defined label"; rc=1; }; \
	   n=$$(LC_ALL=C grep -ac '^!' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n TeX error"; rc=1; }; \
	   n=$$(LC_ALL=C grep -acE '^Overfull .hbox \([0-9]{2,}\.' $$log); \
	     [ "$$n" -eq 0 ] || { echo "FAIL  $$f: $$n overfull hbox over 10pt"; rc=1; }; \
	 done; \
	 if [ $$rc -eq 0 ]; then \
	   echo "PAPER BUILD PASS  main $$(pdfinfo main.pdf | awk '/Pages/{print $$2}') pp, supplement $$(pdfinfo supplement.pdf | awk '/Pages/{print $$2}') pp, logs clean"; \
	 fi; exit $$rc

# Reconciles every number and claim in the article against the regenerated
# certificate and against the Lean sources. Reads the compiled PDFs, since a
# mistyped table cell is invisible in the LaTeX source until it is typeset.
paper-check:
	julia --project=. pipeline/check_paper.jl

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

# ---------------------------------------------------------------------------

clean:
	find . -name '*.aux' -o -name '*.log' -o -name '*.out' -o -name '*.toc' \
	       -o -name '*.bbl' -o -name '*.blg' -o -name '*.synctex.gz' \
	       | grep -v '^./lean/.lake/' | xargs rm -f
