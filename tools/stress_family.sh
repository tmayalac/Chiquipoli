#!/usr/bin/env bash
# Stress test of the family layer (A16, A32, A64): plant defects on purpose and
# require that something rejects every one.
#
#     tools/stress_family.sh generator   the generator's pre-checks refuse each defect   (Julia only, ~2 min)
#     tools/stress_family.sh lean        Lean alone rejects each defect                  (Lean, ~8 min for all cases)
#     tools/stress_family.sh harness     verify_family.sh rejects a sabotaged harness    (Lean, ~4 min)
#     tools/stress_family.sh all         the three, in that order
#
#     STRESS_CASES="16"   restrict the generator and lean layers to some cases (default: 16 32 64)
#     STRESS_MEM_GB=16    kill any single Lean process tree above this resident size
#
# WHAT IS BEING TESTED
#
# The family certificate has two lines of defence. The generator checks every
# margin in exact rational arithmetic before it writes a line of Lean; Lean then
# re-proves everything in the kernel. Either should be enough. This harness
# checks that EACH ONE IS enough, separately:
#
#   generator  CHIQUI_MUTATE=<kind> plants one defect; the pre-checks must stop
#              the generator ("pre-check failed") after the defect was planted.
#   lean       the same defect with CHIQUI_MUTATE_UNGUARDED=1: the pre-checks
#              are skipped and the defect is written. Lean must reject the
#              planted file, every error must lie inside the planted
#              declaration (so the rejection is about the defect and nothing
#              else), and every module the planted file imports must be
#              byte-identical to the tracked, built one (so the file was checked
#              against the true certificate).
#   harness    defects in the verification itself -- an admitted goal, an
#              unresolvable audit name, a missing, vacuous or mis-failing
#              control, a broken twin, a hand edit of a generated file -- must
#              each make the step of verify_family.sh responsible for it FAIL.
#
# The eight planted kinds (see MUTATIONS in gen_family.jl) model the failure
# modes of a generator, not typos:
#   encl    a vertex centre off by 10^4 rho              Encl1.lean     encX1
#   conv    a support line with reversed orientation     Conv1.lean     convD_0_2
#   far     an active diameter listed as inactive        Far1.lean      far_i_j
#   side    a side that needs Fc proved for every c      Sides1.lean    side_i
#   hen     a Henneberg vertex pinned twice to one vertex Hen.lean      henD_k
#   stress  Cramer's rule with one sign dropped          StressDef.lean bal_k
#   root    the signs of Fc at the bracket ends swapped  Root.lean      Fc_clo, Fc_chi
#   unique  a derivative bound above |Fc'(slo)|          Unique.lean    dFc_lb
#
# The generator and lean layers write only to scratch directories and never
# touch the tracked tree. They READ cases/ (the generator's inputs), so do not
# run this at the same time as tools/mutation_check.sh, which edits cases/:
# the generator would see that script's defects, not its own. The harness layer edits tracked files, restores them
# from git, needs a clean working tree, and ends by requiring it clean again.
#
# WHAT IT DOES NOT DO
#
# It shows the checks can fail on these defects; it cannot show there is no
# defect nobody thought of. See tools/mutation_check.sh for the same caveat.

set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
if [ ! -f "$ROOT/lean/verify_family.sh" ] || [ ! -f "$ROOT/lean/generators/family/gen_family.jl" ]; then
  printf "refusing to run: %s is not the repository root\n" "$ROOT"; exit 2
fi

RED=$'\033[31m'; GRN=$'\033[32m'; DIM=$'\033[2m'; RST=$'\033[0m'
fail=0; ncaught=0; nplanted=0
ok()   { printf "  ${GRN}CAUGHT${RST}    %s\n" "$*"; ncaught=$((ncaught + 1)); nplanted=$((nplanted + 1)); }
bad()  { printf "  ${RED}MISSED${RST}    %s\n" "$*"; fail=1; nplanted=$((nplanted + 1)); }
good() { printf "  ${GRN}OK${RST}        %s\n" "$*"; }
err()  { printf "  ${RED}ERROR${RST}     %s\n" "$*"; fail=1; }
note() { printf '%s\n' "$*"; }
dim()  { printf "${DIM}%s${RST}\n" "$*"; }

MUTATIONS="encl conv far side hen stress root unique"
CASES="${STRESS_CASES:-16 32 64}"
MEM_KB=$(( ${STRESS_MEM_GB:-16} * 1024 * 1024 ))
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/chiqui_stress.XXXXXX")
LOCATE="python3 $ROOT/tools/stress_family_locate.py"
WRONG_REASON='unknown module|unknown package|could not resolve import|object file .* does not exist|no such file|unknown (identifier|constant|namespace)|deterministic\) timeout|maximum recursion depth'

# Run a command with a ceiling on the resident memory of its whole process
# tree. Output goes to $1; exit status is the command's, or 99 if it was killed.
tree_rss() {
  local pids="$1" all="$1" kids
  while [ -n "$pids" ]; do
    kids=$(for p in $pids; do pgrep -P "$p"; done 2>/dev/null | tr '\n' ' ')
    all="$all $kids"; pids="$kids"
  done
  ps -o rss= -p $(echo $all | tr ' ' ',') 2>/dev/null | awk '{s += $1} END {print s + 0}'
}
capped() {
  local out="$1"; shift
  "$@" >"$out" 2>&1 &
  local pid=$! killed=0
  while kill -0 "$pid" 2>/dev/null; do
    if [ "$(tree_rss "$pid")" -gt "$MEM_KB" ]; then
      pkill -TERM -P "$pid" 2>/dev/null; kill -TERM "$pid" 2>/dev/null; killed=1; break
    fi
    sleep 2
  done
  wait "$pid"; local rc=$?
  [ "$killed" -eq 1 ] && return 99
  return "$rc"
}

gen() {  # gen <n> <outdir> <logfile> [ENV=... ...]
  local n="$1" out="$2" log="$3"; shift 3
  env CHIQUI_OUTDIR="$out" "$@" julia --project=. lean/generators/family/gen_family.jl "$n" >"$log" 2>&1
}

WHICH="${1:-all}"
case "$WHICH" in generator|lean|harness|all) ;; *) echo "usage: $0 generator|lean|harness|all"; exit 2 ;; esac

# ---------------------------------------------------------------------------
if [ "$WHICH" = "generator" ] || [ "$WHICH" = "all" ]; then
note "=== generator: its pre-checks must refuse every planted defect ==="
dim  "    exact rational arithmetic, before any Lean is written"
tree_sum() { find lean/ChiquipoliFamily lean/negative_controls_family -type f -name '*.lean' | sort | xargs shasum | shasum; }
before=$(tree_sum)
for n in $CASES; do
  for k in $MUTATIONS; do
    log="$SCRATCH/gen_${n}_$k.log"; out="$SCRATCH/g$n$k"
    if gen "$n" "$out" "$log" CHIQUI_MUTATE="$k"; then
      bad "A$n $k: the generator wrote the defect without complaint"
    elif ! grep -q "^MUTATED $k " "$log"; then
      err "A$n $k: the generator failed before planting the defect (see $log)"
    elif ! grep -q "pre-check failed" "$log"; then
      err "A$n $k: the generator failed, but not in a pre-check: $(grep -m1 -i error "$log")"
    else
      ok "A$n $k: $(grep -m1 -o 'pre-check failed: [^"]*' "$log" | head -1 | cut -c1-90)"
    fi
    rm -rf "$out"
  done
done
# The unguarded switch must not be usable without a planted defect, nor a
# mutated run pointed at the tracked tree.
if env CHIQUI_OUTDIR="$SCRATCH/x" CHIQUI_MUTATE_UNGUARDED=1 julia --project=. lean/generators/family/gen_family.jl 16 >/dev/null 2>&1; then
  err "unguarded run without a planted defect was allowed"
else good "unguarded run without a planted defect is refused"; fi
if env CHIQUI_MUTATE=conv julia --project=. lean/generators/family/gen_family.jl 16 >/dev/null 2>&1; then
  err "a mutated run was allowed to write into the tracked tree"
else good "a mutated run cannot write into the tracked tree"; fi
[ "$(tree_sum)" = "$before" ] || err "the generator layer changed files under lean/"
note ""
fi

# ---------------------------------------------------------------------------
if [ "$WHICH" = "lean" ] || [ "$WHICH" = "all" ]; then
note "=== lean: with the pre-checks OFF, Lean alone must reject every defect ==="
dim  "    each rejection must lie inside the planted declaration, checked against the true upstream modules"
if ! (cd lean && lake build ChiquipoliFamily >"$SCRATCH/build.log" 2>&1); then
  err "the family library does not build; the lean layer needs it built (see $SCRATCH/build.log)"
else
for n in $CASES; do
  for k in $MUTATIONS; do
    log="$SCRATCH/lgen_${n}_$k.log"; out="$SCRATCH/l$n$k"
    if ! gen "$n" "$out" "$log" CHIQUI_MUTATE="$k" CHIQUI_MUTATE_UNGUARDED=1; then
      err "A$n $k: the unguarded generator failed (see $log)"; continue
    fi
    read -r _ _ rel decls < <(grep -m1 "^MUTATED $k " "$log")
    if [ -z "${rel:-}" ]; then err "A$n $k: nothing was planted"; continue; fi
    if ! up=$($LOCATE upstream "$out" "$ROOT/lean" "$n" "$rel"); then
      err "A$n $k: $up"; continue
    fi
    if cmp -s "$out/$rel" "lean/$rel"; then
      err "A$n $k: the planted file is identical to the tracked one"; continue
    fi
    t0=$(date +%s)
    capped "$SCRATCH/lean_${n}_$k.out" bash -c "cd lean && lake env lean '$out/$rel'"
    rc=$?; dt=$(( $(date +%s) - t0 ))
    lout="$SCRATCH/lean_${n}_$k.out"
    if [ "$rc" -eq 99 ]; then
      err "A$n $k: Lean exceeded ${STRESS_MEM_GB:-16} GB and was stopped -- not counted as caught"
    elif [ "$rc" -eq 0 ]; then
      bad "A$n $k: Lean ACCEPTED the planted $decls in $rel"
    elif grep -qiE "$WRONG_REASON" "$lout"; then
      err "A$n $k: Lean failed for a reason unrelated to the defect: $(grep -m1 -iE "$WRONG_REASON" "$lout" | cut -c1-120)"
    elif where=$($LOCATE located "$out/$rel" "$decls" <"$lout"); then
      ok "A$n $k: $(basename "$rel") -- $where [${dt}s; $up]"
    else
      err "A$n $k: $where"
    fi
    rm -rf "$out"
  done
done
fi
note ""
fi

# ---------------------------------------------------------------------------
if [ "$WHICH" = "harness" ] || [ "$WHICH" = "all" ]; then
note "=== harness: verify_family.sh must reject a sabotaged verification ==="
dim  "    each defect is run against the step responsible for it (FAMILY_STEPS)"
if ! git rev-parse --git-dir >/dev/null 2>&1; then
  err "not a git checkout: the harness layer restores from git and cannot run here"
elif [ -n "$(git status --porcelain)" ]; then
  err "the working tree has uncommitted changes; the harness layer edits tracked files and restores them from git -- commit or stash first"
else
  restore() {
    git checkout -- lean/ChiquipoliFamily lean/negative_controls_family 2>/dev/null
    rm -f lean/ChiquipoliFamily/ZZ_stress_probe.lean
    git clean -fdq lean/negative_controls_family 2>/dev/null
  }
  trap restore EXIT INT TERM
  verify_rejects() {  # verify_rejects <steps> <cases> <expected message regex>
    local out
    out=$(cd lean && FAMILY_STEPS="$1" FAMILY_CASES="$2" ./verify_family.sh 2>&1) && return 1
    out=$(printf '%s' "$out" | sed $'s/\033\\[[0-9;]*m//g')
    printf '%s' "$out" | grep -q 'partial run, not a certification) FAIL' || return 1
    printf '%s' "$out" | grep -qE "$3"
  }
  harness() {  # harness <label> <steps> <cases> <regex>
    if verify_rejects "$2" "$3" "$4"; then ok "$1"; else bad "$1 -- verify_family.sh step $2 accepted it"; fi
    restore
  }
  NC=lean/negative_controls_family/A16

  printf 'import ChiquipoliFamily\ntheorem zz_probe : (1 : Nat) = 1 := by sorry\n' > lean/ChiquipoliFamily/ZZ_stress_probe.lean
  harness "an admitted goal in a file nothing imports" 2 16 'admits a goal'

  printf '\ntheorem zz : True := by\n  sorry\n' >> "$NC/twin/fnc07_bracket_nonempty.lean"
  harness "an admitted goal in a twin (a twin must not compile by sorry)" 2 16 'admits a goal'

  printf '\n#print axioms Chiquipoli.Family.A16.zz_no_such_theorem\n' >> lean/ChiquipoliFamily/Audit.lean
  harness "an unresolvable name in the axiom audit" 3 "16 32 64" 'does not compile'

  grep -v '^#print axioms Chiquipoli.Family.A64.locally_maximal_unique$' lean/ChiquipoliFamily/Audit.lean > "$SCRATCH/audit" \
    && cp "$SCRATCH/audit" lean/ChiquipoliFamily/Audit.lean
  harness "a headline theorem (A64.locally_maximal_unique) dropped from the audit" 3 "16 32 64" 'missing from the audit'

  rm "$NC/fnc05_rigidity_needs_bars.lean"
  harness "a negative control deleted" 4 16 'found 9 controls'

  sed 's/theorem good/theorem bad/' "$NC/twin/fnc06_root_sign.lean" > "$NC/fnc06_root_sign.lean"
  harness "a negative control made true (it now compiles)" 4 16 'COMPILED'

  cp "$NC/fnc06_root_sign.lean" "$NC/twin/fnc06_root_sign.lean"
  harness "a twin made false (the control's rejection would prove nothing)" 4 16 'twin does NOT compile'

  sed 's/det_lb/det_lb_no_such_lemma/' "$NC/fnc01_convexity_sign.lean" > "$SCRATCH/c" && cp "$SCRATCH/c" "$NC/fnc01_convexity_sign.lean"
  harness "a control that fails only because a name does not resolve" 4 16 'wrong reason'

  sed 's/set_option maxHeartbeats 4000000/set_option maxHeartbeats 1/' "$NC/fnc09_enclosure_tight.lean" > "$SCRATCH/c" && cp "$SCRATCH/c" "$NC/fnc09_enclosure_tight.lean"
  harness "a control that fails only by timing out" 4 16 'wrong reason'

  printf '\n-- a hand edit\n' >> lean/ChiquipoliFamily/A16/Unique.lean
  harness "a hand edit of a generated certificate file" 5 16 'differ from a fresh run'

  printf '\n-- a hand edit\n' >> "$NC/fnc02_inactive_margin.lean"
  harness "a hand edit of a generated control" 5 16 'differ from a fresh run'

  restore; trap - EXIT INT TERM
  if [ -z "$(git status --porcelain)" ]; then
    good "working tree restored, clean"
  else
    err "working tree NOT restored:"; git status --porcelain | sed 's/^/            /'
  fi
fi
note ""
fi

rm -rf "$SCRATCH"
if [ "$fail" -eq 0 ]; then
  printf "${GRN}FAMILY STRESS TEST PASS${RST} -- %d of %d planted defects rejected\n" "$ncaught" "$nplanted"
else
  printf "${RED}FAMILY STRESS TEST FAIL${RST} -- %d of %d planted defects rejected; see MISSED / ERROR above.\n" "$ncaught" "$nplanted"
  printf "  A MISSED defect means a check cannot see that failure mode: fix the check, not this script.\n"
fi
exit "$fail"
