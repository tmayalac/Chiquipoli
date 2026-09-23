#!/usr/bin/env bash
# Mutation check: break the package on purpose and require the verification to
# notice.
#
#     tools/mutation_check.sh            all mutations
#     tools/mutation_check.sh julia      only the ones the Julia suite guards
#     tools/mutation_check.sh lean       only the ones the Lean layer guards
#
# WHY THIS EXISTS
#
# A test suite that has never failed is not a tested suite. Every check in this
# repository asserts that something holds; none of them asserted that the check
# itself is capable of failing. An adversarial audit found five places where it
# was not:
#
#   * Audit.lean referenced a theorem that does not exist. Lean emitted
#     "unknown constant", verify.sh grepped only for sorryAx, and the run was
#     reported as PASS.
#   * Deleting a negative control still produced PASS: the loop iterated over
#     whatever happened to be on disk.
#   * The Julia suite threw at the end of its first failing testset, so a
#     broken constructor stopped it after two of twelve.
#   * Nothing tied the trigonometric constructor to the polynomial one, so
#     breaking one left the other proving 31 identities about a different
#     polygon.
#   * No test pinned a certified value, only a block status.
#
# All five are fixed. This script exists so they cannot come back quietly: each
# mutation below reproduces one of the failure modes that was once invisible,
# and requires the verification to reject it.
#
# WHAT IT DOES NOT DO
#
# It does not prove the harness is complete. It detects blindness to the
# mutations someone thought of. A hole nobody imagined stays invisible, exactly
# as these five did until they were looked for. What it guarantees is that
# these particular failure modes cannot regress in silence.

set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
# Every path below is relative to the repository root. If this is not the root,
# nothing gets planted and every "rejects" check fails for the wrong reason --
# which read as CAUGHT until 2026-09, when a one-character slip in the `cd`
# above made all five Lean mutations report CAUGHT without planting anything.
if [ ! -f "$ROOT/lean/verify.sh" ] || [ ! -f "$ROOT/src/A16Certificate.jl" ]; then
  printf "refusing to run: %s is not the repository root\n" "$ROOT"
  exit 2
fi

RED=$'\033[31m'; GRN=$'\033[32m'; DIM=$'\033[2m'; RST=$'\033[0m'
fail=0
ok()   { printf "  ${GRN}CAUGHT${RST}    %s\n" "$*"; }
bad()  { printf "  ${RED}MISSED${RST}    %s\n" "$*"; fail=1; }
note() { printf '%s\n' "$*"; }
dim()  { printf "${DIM}%s${RST}\n" "$*"; }

# --- state safety ----------------------------------------------------------
# This harness plants defects in tracked files and restores them with
# `git checkout`. Without a repository it can plant but cannot restore, so it
# must refuse before touching anything.
#
# The dirty-tree guard below does NOT cover that case, and reading it as though
# it did is what made this necessary: outside a checkout `git status` writes
# `fatal:` to stderr and nothing to stdout, so `-n ""` is false and the guard
# waves the run through. It then mutated the sources of an extracted archive,
# failed every restore, and left a corrupted copy reporting a screen of MISSED
# -- which reads as "the checks failed" rather than "the harness broke itself".
if ! git rev-parse --git-dir >/dev/null 2>&1; then
  printf "${RED}refusing to run: this is not a git checkout${RST}\n"
  printf "  This harness plants defects in tracked files and restores them with\n"
  printf "  'git checkout'. In the distributed archive there is nothing to restore\n"
  printf "  from, so running it would leave the sources permanently mutated.\n"
  printf "\n"
  printf "  To run it, clone the repository instead of extracting the archive.\n"
  printf "  Everything else in the supplementary material runs from the archive:\n"
  printf "    julia --project=. pipeline/certify_a16.jl\n"
  printf "    julia --project=. test/runtests.jl\n"
  printf "    julia --project=. pipeline/certify_literature.jl\n"
  exit 2
fi

# Refuse to run on a dirty tree: a mutation would be indistinguishable from
# uncommitted work, and the restore would discard it.
if [ -n "$(git status --porcelain)" ]; then
  printf "${RED}refusing to run: the working tree has uncommitted changes${RST}\n"
  printf "  this script edits tracked files and restores them from git;\n"
  printf "  commit or stash first so a restore cannot lose your work.\n"
  exit 2
fi

MOVED_NC=""
restore() {
  git checkout -- src/a16 lean/ChiquipoliLean/Audit.lean \
    lean/ChiquipoliLean/Instances/A16FirstOrder.lean lean/ChiquipoliLean/Constructor/SideLength.lean 2>/dev/null
  rm -f lean/ChiquipoliLean/Theory/ZZ_mutation_probe.lean
  if [ -n "$MOVED_NC" ] && [ -f "/tmp/$MOVED_NC" ]; then
    mv "/tmp/$MOVED_NC" "lean/negative_controls/$MOVED_NC"
  fi
}
trap restore EXIT INT TERM

# --- helpers ---------------------------------------------------------------
# A mutation is CAUGHT when the checker RAN and REPORTED a failure. A non-zero
# exit alone is not enough: a checker that could not start (wrong directory,
# missing tool, a file that failed to load) also exits non-zero, and counting
# that as "rejected" is how this harness once reported five Lean mutations as
# caught without running Lean on any of them.
julia_suite_rejects() {
  local out
  out=$(julia --project=. test/runtests.jl 2>&1) && return 1
  printf '%s' "$out" | grep -qE 'Some tests did not pass|Test Summary:.*(Fail|Error)'
}
lean_verify_rejects() {
  local out
  out=$(cd lean && ./verify.sh 2>&1) && return 1
  printf '%s' "$out" | sed $'s/\033\\[[0-9;]*m//g' \
    | grep -qE 'LEAN CERTIFICATE FAIL|^  FAIL  lake build'
}

# Replace exactly one occurrence, or abort: a mutation that did not apply would
# silently be reported as CAUGHT by whatever else is failing.
patch_once() {
  python3 - "$1" "$2" "$3" <<'PY'
import io, sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
s = io.open(path, encoding="utf-8").read()
if s.count(old) != 1:
    sys.exit("mutation target not found exactly once in %s (%d)" % (path, s.count(old)))
io.open(path, "w", encoding="utf-8").write(s.replace(old, new))
PY
}

run_julia_mutation() {
  local label="$1" file="$2" old="$3" new="$4"
  if ! patch_once "$file" "$old" "$new"; then bad "$label (could not apply)"; return; fi
  if julia_suite_rejects; then ok "$label"; else bad "$label — the suite accepted it"; fi
  git checkout -- "$file"
}

# --- the mutations ---------------------------------------------------------
WHICH="${1:-all}"

if [ "$WHICH" = "all" ] || [ "$WHICH" = "julia" ]; then
note "=== Julia: the suite must reject a broken constructor ==="
dim  "    each mutation is a realistic transcription error, not a typo"

run_julia_mutation \
  "constructor: sin(4t) -> sin(5t)" \
  src/a16/constructor.jl \
  '    return sin(t) - (two*cos(t) - one(t))*sin(four*t)' \
  '    return sin(t) - (two*cos(t) - one(t))*sin(_lit(t, 5)*t)'

run_julia_mutation \
  "constructor equation: sin(7t) -> sin(6t)" \
  src/a16/constructor.jl \
  '    return (two*x + sin(seven*t))^2 + cos(seven*t)^2 - four*sin(t/two)^2' \
  '    return (two*x + sin(_lit(t, 6)*t))^2 + cos(seven*t)^2 - four*sin(t/two)^2'

# Regression guard for the audit fix: rebuilding the Krawczyk enclosure with
# round-to-nearest BigFloat additions makes the reported box up to an ulp
# narrower than the certified set, so it is no longer guaranteed to contain the
# solution. The effect is ~1e-77 and invisible to any tolerance-based test; it
# is caught only by comparing against the outward-rounded operator directly.
run_julia_mutation \
  "Krawczyk enclosure: outward rounding -> round to nearest" \
  src/a16/linear_algebra.jl \
  '                enclosure = [x0[i] + Kcorr[i] for i in 1:n]' \
  '                enclosure = [interval(BigFloat(inf(x0[i]))+inf(Kcorr[i]), BigFloat(sup(x0[i]))+sup(Kcorr[i])) for i in 1:n]'

# A transcription error in one vertex that leaves the constructor equation F
# untouched. This is the failure mode the OPTIGON identification test exists
# for: F still has the same root, so every check that only looks at F is blind
# to it, and the certificate would be about a polygon that is not A16.
run_julia_mutation \
  "coordinates: sign of cos(6z) at vertex 5" \
  src/a16/constructor.jl \
  '    p[6,:] .= (x+sin(k6*z), y+cos(k6*z))' \
  '    p[6,:] .= (x+sin(k6*z), y-cos(k6*z))'

# A derivative that is wrong but keeps the right sign. Interval Newton and the
# monotonicity test on I_search both still PASS with it -- F'(Z) moves from
# about -3.11 to -2.92 -- so the certificate would print CERTIFIED on a root
# step whose proof uses the wrong function. Only the chain-rule test
# F'(t) = -sin t Fc'(cos t) sees it (2026-09 external audit, D08).
run_julia_mutation \
  "derivative: Fprime loses a factor 2 in its last term" \
  src/a16/constructor.jl \
  '           fourteen*cos(seven*t)*sin(seven*t) - two*sin(t)' \
  '           fourteen*cos(seven*t)*sin(seven*t) - sin(t)'

run_julia_mutation \
  "root literal: one digit altered" \
  src/a16/data.jl \
  'big"0.19627037213032280086206121185805318446"' \
  'big"0.19627037213032280096206121185805318446"'

run_julia_mutation \
  "active graph: edge (6,13) -> (6,12)" \
  src/a16/data.jl \
  '(6,13)' \
  '(6,12)'
note ""
fi

if [ "$WHICH" = "all" ] || [ "$WHICH" = "lean" ]; then
note "=== Lean: verify.sh must reject a weakened formalisation ==="
dim  "    the first three were all reported as PASS before the harness was fixed"

# L1 — an admitted goal must be found even in a file nothing imports, and even
# one level down: the sources live in subdirectories, and the scan for `sorry`
# once covered only the top level of ChiquipoliLean/.
if ! cat > lean/ChiquipoliLean/Theory/ZZ_mutation_probe.lean <<'LEAN'
import ChiquipoliLean
namespace Chiquipoli
theorem mutation_probe : (1 : ℝ) = 1 := by sorry
end Chiquipoli
LEAN
then bad "planted 'sorry' (could not apply)"
elif lean_verify_rejects; then ok "planted 'sorry' in the Lean sources"
else bad "planted 'sorry' — verify.sh accepted it"; fi
rm -f lean/ChiquipoliLean/Theory/ZZ_mutation_probe.lean

# L2 — the axiom audit must not silently skip a name it cannot resolve.
if ! printf '\n#print axioms zz_mutation_no_such_theorem\n' >> lean/ChiquipoliLean/Audit.lean
then bad "unresolvable name in Audit.lean (could not apply)"
elif lean_verify_rejects; then ok "unresolvable name in Audit.lean"
else bad "unresolvable name in Audit.lean — verify.sh accepted it"; fi
git checkout -- lean/ChiquipoliLean/Audit.lean

# L4 — the bridge from `twice` to the development's `dsq` is what ties the
# Theorem 3.5 layer to the certified A16 arithmetic. A wrong factor there would
# leave the abstract theorems true but about a different constraint system.
if ! patch_once lean/ChiquipoliLean/Instances/A16FirstOrder.lean \
  'def twice (a b : ℝ × ℝ) : ℝ × ℝ := (2 * (b.1 - a.1), 2 * (b.2 - a.2))' \
  'def twice (a b : ℝ × ℝ) : ℝ × ℝ := (2 * (b.1 - a.1), 3 * (b.2 - a.2))'
then bad "wrong factor in the dsq bridge (could not apply)"
elif lean_verify_rejects; then ok "wrong factor in the dsq bridge (Theorem 3.5 layer)"
else bad "wrong factor in the dsq bridge — verify.sh accepted it"; fi
git checkout -- lean/ChiquipoliLean/Instances/A16FirstOrder.lean

# L5 — the tight root bracket of SideLength.lean is what pins the side length
# to nineteen digits. One digit off and the exact sign check must fail.
if ! patch_once lean/ChiquipoliLean/Constructor/SideLength.lean \
  'noncomputable def cLo : ℝ := 9808007223804781715147 / 10 ^ 22' \
  'noncomputable def cLo : ℝ := 9808007223804781715148 / 10 ^ 22'
then bad "one digit off in the tight root bracket (could not apply)"
elif lean_verify_rejects; then ok "one digit off in the tight root bracket"
else bad "one digit off in the tight root bracket — verify.sh accepted it"; fi
git checkout -- lean/ChiquipoliLean/Constructor/SideLength.lean

# L3 — removing a negative control must not reduce coverage in silence.
MOVED_NC="nc1_wrong_diameter.lean"
if ! mv "lean/negative_controls/$MOVED_NC" /tmp/
then bad "a negative control removed (could not apply)"; MOVED_NC=""
elif lean_verify_rejects; then ok "a negative control removed"
else bad "a negative control removed — verify.sh accepted it"; fi
[ -n "$MOVED_NC" ] && mv "/tmp/$MOVED_NC" "lean/negative_controls/$MOVED_NC"
MOVED_NC=""
note ""
fi

# --- the tree must come back exactly as it was -----------------------------
note "=== the mutation run must leave no trace ==="
restore
if [ -z "$(git status --porcelain)" ]; then
  ok "working tree restored, clean"
else
  bad "working tree NOT restored:"
  git status --porcelain | sed 's/^/            /'
fi

note ""
if [ "$fail" -eq 0 ]; then
  printf "${GRN}MUTATION CHECK PASS${RST} — every planted defect was rejected\n"
else
  printf "${RED}MUTATION CHECK FAIL${RST} — a planted defect went undetected;\n"
  printf "  the verification cannot see that failure mode. Fix the checker,\n"
  printf "  not this script.\n"
fi
exit "$fail"
