#!/usr/bin/env bash
# Every check of the package, from one command, with a summary at the end.
#
#     tools/check_all.sh              everything (make check-all)             ~35 min, 16 GB
#     tools/check_all.sh quick        Julia only, no Lean (make check)         ~5 min
#     tools/check_all.sh lean         the two Lean layers, recorded (make check-lean)
#     tools/check_all.sh case <n>     one case: n = 4, 6, 8, 16, 32 or 64 (make check-case N=<n>)
#     tools/check_all.sh fast <n>       ONE candidate, its Julia certificate only, in seconds (make a<n>)
#     tools/check_all.sh candidate <n>  ONE candidate, every layer incl. Lean (make a<n>-complete; A16 = a16-complete)
#
# The candidates are the members of the Bingane–Audet family listed in
# cases/exact_coords.jl: FAMILY_N (Julia certificate), FAMILY_LEAN_N (the
# per-case polynomial Lean certificate) and FAMILY_TRIG_N (the general Lean
# certificate: one theorem for every n = 16k, kernel-checked data per n). A
# member in neither Lean list has its Lean stages reported SKIP, so its verdict
# is INCOMPLETE.
#
# HOW TO READ THE RESULT. Every stage runs even if an earlier one failed, and
# the run ends with a table: PASS, FAIL, or SKIP with the reason. Three verdicts:
#
#   ALL CHECKS PASS   every stage of the selected mode ran and passed
#   INCOMPLETE        nothing failed, but some stage was skipped -- typically
#                     the ones that need a clean git tree. Not a pass.
#   FAIL              at least one stage failed; its log is listed.
#
# ORDER MATTERS. The mutation check and the stress test's harness part edit
# tracked files and restore them from git, so they need a clean tree and run
# first. The stages after them regenerate the certificates in results/ and
# logs/, which dirties the tree -- that is how those records are refreshed.
# On a dirty tree the clean-tree stages are skipped, not faked.
#
# Logs of every stage: logs/check_all/<UTC timestamp>/<stage>.log (not tracked).

set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
[ -f "$ROOT/Makefile" ] && [ -f "$ROOT/src/A16Certificate.jl" ] || { echo "not the repository root: $ROOT"; exit 2; }

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; BLD=$'\033[1m'; RST=$'\033[0m'
MODE="${1:-all}"; CASE="${2:-}"
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
LOGDIR="$ROOT/logs/check_all/$STAMP"
mkdir -p "$LOGDIR"

declare -a NAMES=() RESULTS=() TIMES=() NOTES=()
record() { NAMES+=("$1"); RESULTS+=("$2"); TIMES+=("$3"); NOTES+=("$4"); }

# stage <name> <what it establishes> <command...>
stage() {
  local name="$1" what="$2"; shift 2
  local log="$LOGDIR/$name.log" t0 dt
  printf "\n${BLD}── %s${RST} — %s\n" "$name" "$what"
  t0=$(date +%s)
  if "$@" >"$log" 2>&1; then
    dt=$(( $(date +%s) - t0 )); printf "   ${GRN}PASS${RST} (%ds)\n" "$dt"; record "$name" PASS "$dt" "$what"
  else
    dt=$(( $(date +%s) - t0 )); printf "   ${RED}FAIL${RST} (%ds) — last lines of %s:\n" "$dt" "${log#$ROOT/}"
    tail -6 "$log" | sed $'s/\033\\[[0-9;]*m//g; s/^/      /'
    record "$name" FAIL "$dt" "log: ${log#$ROOT/}"
  fi
}
skip() { printf "\n${BLD}── %s${RST}\n   ${YEL}SKIP${RST} — %s\n" "$1" "$2"; record "$1" SKIP 0 "$2"; }

have() { command -v "$1" >/dev/null 2>&1; }
clean_tree() { git rev-parse --git-dir >/dev/null 2>&1 && [ -z "$(git status --porcelain)" ]; }
lean_ready() { have lake && [ -d lean/.lake/packages/mathlib ]; }

# --- preflight ----------------------------------------------------------------
printf "${BLD}Chiquipoli — check_all (%s%s)${RST}  logs: %s\n" "$MODE" "${CASE:+ $CASE}" "${LOGDIR#$ROOT/}"
have julia || { echo "julia is not on PATH; nothing can run"; exit 2; }
if [ "$(uname)" = Darwin ]; then memgb=$(( $(sysctl -n hw.memsize) / 1073741824 )); else memgb=$(( $(awk '/MemTotal/ {print $2}' /proc/meminfo) / 1048576 )); fi
case "$MODE" in
  all)   echo "   estimated ~35 min; the A64 Lean steps need ~13 GB (this machine: ${memgb} GB)" ;;
  lean)  echo "   estimated ~10 min if the Lean libraries are built, ~30 min from scratch; ~13 GB" ;;
  quick) echo "   estimated ~5 min; Julia only" ;;
  case)  echo "   estimated 1-15 min depending on the case" ;;
  fast)  echo "   estimated 10 s (n <= 256) to a few minutes (n = 1024); Julia only" ;;
  candidate) echo "   estimated on a clean tree: A16 ~18 min, A32 ~10 min, A64 ~32 min, A128/A256 a few minutes" ;;
esac
[ "$memgb" -lt 16 ] && [ "$MODE" != quick ] && echo "   ${YEL}warning${RST}: less than 16 GB of memory; the A64 Lean build may not fit"
clean_tree && echo "   git tree: clean" || echo "   git tree: ${YEL}dirty${RST} — the stages that need a clean tree will be skipped"

# The family members, read from their single source (cases/exact_coords.jl).
family_list() { sed -n "s/^const $1 = (\(.*\))/\1/p" cases/exact_coords.jl | tr -d ','; }
FAMILY_N=$(family_list FAMILY_N); FAMILY_LEAN_N=$(family_list FAMILY_LEAN_N)
FAMILY_TRIG_N=$(family_list FAMILY_TRIG_N)
in_list() { case " $2 " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
# The exact identities are proved in parallel when Julia has threads.
export JULIA_NUM_THREADS="${JULIA_NUM_THREADS:-auto}"

julia_run() { julia --project=. "$@"; }
family_case() { (cd lean && FAMILY_CASES="$1" ./verify_family.sh); }
trig_case() { (cd lean && TRIG_CASES="$1" ./verify_trig.sh); }

# --- the modes ----------------------------------------------------------------
case "$MODE" in
quick)
  stage test         "the Julia suite (A16 certificate stages, framework, literature, family)" julia_run test/runtests.jl
  stage literature   "the literature benchmark n = 4, 6, 8, 16, 32, 64 and its broken controls (nothing recorded)" \
    env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_literature.jl
  QUICK_N=$(for n in $FAMILY_N; do [ "$n" -le 512 ] && printf '%s ' "$n"; done)
  stage family-certs "the family certificates of $(echo $QUICK_N | sed 's/[0-9]*/A&/g') (10 gates each; nothing recorded)" \
    bash -c "for n in $QUICK_N; do CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_family.jl \$n || exit 1; done"
  stage stress-gen   "the family generator refuses 24 planted defects" tools/stress_family.sh generator
  stage family-record "results/lean_family_certificate.toml still describes this tree" julia_run pipeline/record_lean_family_certificate.jl --check
  stage paper-check  "the article and the docs agree with the certificates" julia_run pipeline/check_paper.jl
  ;;

lean)
  if lean_ready; then
    stage lean-a16     "A16 Lean layer: five checks, recorded in results/lean_certificate.toml" julia_run pipeline/record_lean_certificate.jl
    stage lean-family  "family Lean layer (A16, A32, A64): five checks, recorded in results/lean_family_certificate.toml" julia_run pipeline/record_lean_family_certificate.jl
    stage lean-general "the general Lean theorem ($(echo $FAMILY_TRIG_N | sed 's/[0-9]*/A&/g')): five checks, 12 tampered-data controls per case" trig_case "$FAMILY_TRIG_N"
  else
    skip lean-a16    "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-family "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-general "Lean or the Mathlib cache is missing (make lean-cache)"
  fi
  ;;

case)
  case "$CASE" in 4|6|8|16|32|64) ;; *) echo "usage: $0 case <4|6|8|16|32|64>"; exit 2 ;; esac
  stage "literature-$CASE" "the general certifier on case $CASE" julia_run pipeline/certify_literature.jl "$CASE"
  if [ "$CASE" -ge 16 ]; then
    if lean_ready; then
      stage "lean-family-A$CASE" "A$CASE in Lean: build, no sorry, axioms, 11 controls + twins, regeneration (partial run)" family_case "$CASE"
      stage "stress-A$CASE" "8 planted defects, each refused by the generator's pre-checks" env STRESS_CASES="$CASE" tools/stress_family.sh generator
      stage "stress-lean-A$CASE" "the same 8 defects with the pre-checks off: Lean alone rejects each" env STRESS_CASES="$CASE" tools/stress_family.sh lean
    else
      skip "lean-family-A$CASE" "Lean or the Mathlib cache is missing (make lean-cache)"
      stage "stress-A$CASE" "8 planted defects, refused by the generator" env STRESS_CASES="$CASE" tools/stress_family.sh generator
    fi
    [ "$CASE" = 16 ] && echo "   note: A16 also has its dedicated certificate — make verify (Julia) and make lean (Lean)"
  fi
  ;;

all)
  # 1. the stages that need a clean tree, first
  stage test "the Julia suite" julia_run test/runtests.jl
  if clean_tree; then
    if lean_ready; then
      stage mutation-check "16 planted defects in Julia and the A16 Lean layer, and 5 per candidate in the family certificates" tools/mutation_check.sh
      stage stress-family  "63 planted defects in the family layer: generator, Lean, harness, transcription" tools/stress_family.sh all
    else
      stage mutation-julia "the 11 Julia mutations (the Lean ones need the Mathlib cache)" tools/mutation_check.sh julia
      stage stress-gen     "the family generator refuses 24 planted defects" tools/stress_family.sh generator
    fi
  else
    skip mutation-check "needs a clean git tree (it edits tracked files and restores them from git)"
    if lean_ready; then
      stage stress-family-gen-lean "48 planted family defects: generator and Lean (harness part needs a clean tree)" \
        bash -c 'tools/stress_family.sh generator && tools/stress_family.sh lean'
    else
      stage stress-gen "the family generator refuses 24 planted defects" tools/stress_family.sh generator
    fi
    skip stress-harness "needs a clean git tree (it edits tracked files and restores them from git)"
  fi
  # 2. the certificates, regenerated and recorded
  stage certify-a16  "the A16 interval certificate -> results/a16_certificate.toml, logs/final_run.txt" \
    bash -c 'julia --project=. pipeline/certify_a16.jl | tee logs/final_run.txt; exit ${PIPESTATUS[0]}'
  stage literature   "the literature benchmark -> results/validation_certificate.toml" julia_run pipeline/certify_literature.jl
  stage family-certs "the family certificates of $(echo $FAMILY_N | sed 's/[0-9]*/A&/g') -> results/family/A<n>.toml" \
    bash -c "for n in $FAMILY_N; do julia --project=. pipeline/certify_family.jl \$n || exit 1; done"
  if lean_ready; then
    stage lean-a16     "A16 Lean layer -> results/lean_certificate.toml" julia_run pipeline/record_lean_certificate.jl
    stage lean-family  "family Lean layer -> results/lean_family_certificate.toml" julia_run pipeline/record_lean_family_certificate.jl
    stage lean-general "the general Lean theorem ($(echo $FAMILY_TRIG_N | sed 's/[0-9]*/A&/g')): five checks, 12 tampered-data controls per case" trig_case "$FAMILY_TRIG_N"
  else
    skip lean-a16    "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-family "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-general "Lean or the Mathlib cache is missing (make lean-cache)"
  fi
  # 3. everything against everything
  stage paper-check "the article and the docs agree with every certificate" julia_run pipeline/check_paper.jl
  ;;

fast)
  # ONE candidate, its Julia certificate only: the family certificate (ten
  # gates, the published source run exactly among them) and, for A16, the
  # article's dedicated eight-gate certificate. No suite, no Lean, no controls;
  # `make a<n>-complete` runs those. Writes no record in results/.
  in_list "$CASE" "$FAMILY_N" || { echo "usage: $0 fast <n>, n in: $FAMILY_N"; exit 2; }
  N="$CASE"
  stage "certificate-A$N" "the family certificate of A$N: 10 gates, incl. the published source run exactly, root uniqueness, side length, box nesting" \
    env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_family.jl "$N"
  # the gates themselves, one line each, so the bounds are on screen and not only in the log
  grep -E '^[a-z_]+ +(PASS|FAIL) ' "$LOGDIR/certificate-A$N.log" | cut -c1-150 | sed 's/^/      /'
  grep -E '^FAMILY CERTIFICATE A' "$LOGDIR/certificate-A$N.log" | sed 's/^/      /'
  if [ "$N" = 16 ]; then
    stage "dedicated-julia-A16" "the article's dedicated A16 interval certificate: eight gates (nothing recorded)" \
      env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_a16.jl
    grep -E '^FINAL FIRST-ORDER CERTIFICATE' "$LOGDIR/dedicated-julia-A16.log" | sed 's/^/      /'
  fi
  echo "   note: this is the Julia certificate only; make a$N-complete adds the suite, Lean, controls and planted defects"
  ;;

candidate)
  # Everything that certifies ONE candidate, in every layer, and nothing about
  # the others -- and the SAME stages for A16, A32 and A64: the standard is one
  # certificate, one Lean layer, one set of controls, one stress test and one
  # set of planted defects per candidate. A16 additionally runs its two
  # dedicated layers (the article's own certificate and Lean development),
  # which predate the family layer. Writes no record in results/.
  in_list "$CASE" "$FAMILY_N" || { echo "usage: $0 candidate <n>, n in: $FAMILY_N"; exit 2; }
  N="$CASE"
  stage test "the Julia suite (incl. A$N: published source run exactly, constructor, family pattern)" julia_run test/runtests.jl
  if in_list "$N" "16 32 64"; then
    stage "general-A$N" "the general certifier on A$N (six blocks)" julia_run pipeline/certify_literature.jl "$N"
  fi
  stage "certificate-A$N" "the family certificate of A$N: 10 gates, incl. the published source run exactly, root uniqueness, side length, box nesting" \
    env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_family.jl "$N"
  if in_list "$N" "$FAMILY_TRIG_N"; then
    if lean_ready; then
      stage "lean-general-A$N" "A$N by the general Lean theorem (one proof for every n = 16k): build, no sorry, axioms, 12 tampered-data controls + twins, regeneration" trig_case "$N"
    else
      skip "lean-general-A$N" "Lean or the Mathlib cache is missing (make lean-cache)"
    fi
  fi
  if in_list "$N" "$FAMILY_LEAN_N"; then
    if lean_ready; then
      stage "lean-A$N" "A$N in Lean, per-case certificate incl. the published constructor: build, no sorry, axioms, 11 controls + twins, regeneration" family_case "$N"
      stage "stress-gen-A$N" "8 planted generator defects, each refused by the generator's exact pre-checks" env STRESS_CASES="$N" tools/stress_family.sh generator
      stage "stress-lean-A$N" "the same 8 with the pre-checks off: Lean alone rejects each, inside the planted declaration" env STRESS_CASES="$N" tools/stress_family.sh lean
    else
      skip "lean-A$N" "Lean or the Mathlib cache is missing (make lean-cache)"
      stage "stress-gen-A$N" "8 planted generator defects, each refused by the generator's exact pre-checks" env STRESS_CASES="$N" tools/stress_family.sh generator
      skip "stress-lean-A$N" "Lean or the Mathlib cache is missing (make lean-cache)"
    fi
  elif ! in_list "$N" "$FAMILY_TRIG_N"; then
    skip "lean-A$N" "A$N has no Lean certificate yet (FAMILY_LEAN_N / FAMILY_TRIG_N in cases/exact_coords.jl)"
  fi
  if clean_tree; then
    stage "mutations-A$N" "5 planted defects in A$N's data, the published source and the constructor; the family certificate rejects each" \
      tools/mutation_check.sh family "$N"
    if ! in_list "$N" "$FAMILY_LEAN_N"; then
      in_list "$N" "$FAMILY_TRIG_N" || skip "harness-A$N" "A$N has no Lean certificate yet"
    elif lean_ready; then
      stage "harness-A$N" "15 sabotages of verify_family.sh and of the published-constructor transcription, in A$N's own files" \
        env HARNESS_CASE="$N" tools/stress_family.sh harness
    else
      skip "harness-A$N" "Lean or the Mathlib cache is missing (make lean-cache)"
    fi
  else
    skip "mutations-A$N" "needs a clean git tree (it edits tracked files and restores them from git)"
    skip "harness-A$N" "needs a clean git tree (it edits tracked files and restores them from git)"
  fi
  if [ "$N" = 16 ]; then
    stage "dedicated-julia-A16" "the article's dedicated A16 interval certificate: eight gates (nothing recorded)" \
      env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_a16.jl
    if lean_ready; then
      stage "dedicated-lean-A16" "the article's dedicated A16 Lean layer: build, no sorry, axiom audit, 26 controls, regeneration" bash -c 'cd lean && ./verify.sh'
    else
      skip "dedicated-lean-A16" "Lean or the Mathlib cache is missing (make lean-cache)"
    fi
    if clean_tree && lean_ready; then
      stage "dedicated-mutations-A16" "16 planted defects in the dedicated A16 Julia and Lean layers" \
        bash -c 'tools/mutation_check.sh julia && tools/mutation_check.sh lean'
    else
      skip "dedicated-mutations-A16" "needs a clean git tree and the Mathlib cache"
    fi
  fi
  ;;

*) echo "usage: $0 [all|quick|lean|case <n>|candidate <16|32|64>]"; exit 2 ;;
esac

# --- summary ------------------------------------------------------------------
printf "\n${BLD}%-26s %-6s %7s   %s${RST}\n" "stage" "result" "time" "notes"
nf=0; ns=0; total=0
for i in "${!NAMES[@]}"; do
  r="${RESULTS[$i]}"; c="$GRN"; [ "$r" = FAIL ] && c="$RED" && nf=$((nf + 1)); [ "$r" = SKIP ] && c="$YEL" && ns=$((ns + 1))
  total=$((total + TIMES[$i]))
  printf "%-26s ${c}%-6s${RST} %6ss   %s\n" "${NAMES[$i]}" "$r" "${TIMES[$i]}" "${NOTES[$i]}"
done
printf "total %d min %d s; logs in %s\n\n" $((total / 60)) $((total % 60)) "${LOGDIR#$ROOT/}"
if [ "$nf" -gt 0 ]; then
  printf "${RED}FAIL${RST} — %d stage(s) failed\n" "$nf"; exit 1
elif [ "$ns" -gt 0 ]; then
  printf "${YEL}INCOMPLETE${RST} — nothing failed, but %d stage(s) were skipped; this is not a full pass\n" "$ns"; exit 3
else
  printf "${GRN}ALL CHECKS PASS${RST} — every stage of '%s' ran and passed\n" "$MODE${CASE:+ $CASE}"
fi
