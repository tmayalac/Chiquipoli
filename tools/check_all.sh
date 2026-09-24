#!/usr/bin/env bash
# Every check of the package, from one command, with a summary at the end.
#
#     tools/check_all.sh              everything (make check-all)             ~30 min, 16 GB
#     tools/check_all.sh quick        Julia only, no Lean (make check)         ~5 min
#     tools/check_all.sh lean         the two Lean layers, recorded (make check-lean)
#     tools/check_all.sh case <n>     one case: n = 4, 6, 8, 16, 32 or 64 (make check-case N=<n>)
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
  all)   echo "   estimated ~30 min; the A64 Lean steps need ~13 GB (this machine: ${memgb} GB)" ;;
  lean)  echo "   estimated ~10 min if the Lean libraries are built, ~30 min from scratch; ~13 GB" ;;
  quick) echo "   estimated ~5 min; Julia only" ;;
  case)  echo "   estimated 1-15 min depending on the case" ;;
esac
[ "$memgb" -lt 16 ] && [ "$MODE" != quick ] && echo "   ${YEL}warning${RST}: less than 16 GB of memory; the A64 Lean build may not fit"
clean_tree && echo "   git tree: clean" || echo "   git tree: ${YEL}dirty${RST} — the stages that need a clean tree will be skipped"

julia_run() { julia --project=. "$@"; }
family_case() { (cd lean && FAMILY_CASES="$1" ./verify_family.sh); }

# --- the modes ----------------------------------------------------------------
case "$MODE" in
quick)
  stage test         "the Julia suite (A16 certificate stages, framework, literature, family)" julia_run test/runtests.jl
  stage literature   "the literature benchmark n = 4, 6, 8, 16, 32, 64 and its broken controls (nothing recorded)" \
    env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_literature.jl
  stage stress-gen   "the family generator refuses 24 planted defects" tools/stress_family.sh generator
  stage family-record "results/lean_family_certificate.toml still describes this tree" julia_run pipeline/record_lean_family_certificate.jl --check
  stage paper-check  "the article and the docs agree with the certificates" julia_run pipeline/check_paper.jl
  ;;

lean)
  if lean_ready; then
    stage lean-a16     "A16 Lean layer: five checks, recorded in results/lean_certificate.toml" julia_run pipeline/record_lean_certificate.jl
    stage lean-family  "family Lean layer (A16, A32, A64): five checks, recorded in results/lean_family_certificate.toml" julia_run pipeline/record_lean_family_certificate.jl
  else
    skip lean-a16    "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-family "Lean or the Mathlib cache is missing (make lean-cache)"
  fi
  ;;

case)
  case "$CASE" in 4|6|8|16|32|64) ;; *) echo "usage: $0 case <4|6|8|16|32|64>"; exit 2 ;; esac
  stage "literature-$CASE" "the general certifier on case $CASE" julia_run pipeline/certify_literature.jl "$CASE"
  if [ "$CASE" -ge 16 ]; then
    if lean_ready; then
      stage "lean-family-A$CASE" "A$CASE in Lean: build, no sorry, axioms, 10 controls + twins, regeneration (partial run)" family_case "$CASE"
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
      stage mutation-check "16 planted defects in Julia and the A16 Lean layer, each rejected" tools/mutation_check.sh
      stage stress-family  "59 planted defects in the family layer: generator, Lean, harness" tools/stress_family.sh all
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
  if lean_ready; then
    stage lean-a16     "A16 Lean layer -> results/lean_certificate.toml" julia_run pipeline/record_lean_certificate.jl
    stage lean-family  "family Lean layer -> results/lean_family_certificate.toml" julia_run pipeline/record_lean_family_certificate.jl
  else
    skip lean-a16    "Lean or the Mathlib cache is missing (make lean-cache)"
    skip lean-family "Lean or the Mathlib cache is missing (make lean-cache)"
  fi
  # 3. everything against everything
  stage paper-check "the article and the docs agree with every certificate" julia_run pipeline/check_paper.jl
  ;;

*) echo "usage: $0 [all|quick|lean|case <n>]"; exit 2 ;;
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
