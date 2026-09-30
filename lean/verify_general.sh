#!/usr/bin/env bash
# Verification of the general Lean certificate of the family: the interval
# method (ChiquipoliFamily/Interval/, with the generated data per case in
# ChiquipoliFamily/Interval/T<n>/) and the proof for every n = 16k with no data
# (ChiquipoliFamily/AllN/). Run from `lean/`:
#
#     ./verify_general.sh            every case in TRIG_CASES (default 16 32 64 128 256)
#     TRIG_CASES="256" ./verify_general.sh
#
# ONE theorem, `Chiquipoli.Family.Trig.published_of_checks`, proved once for every
# n = 16k, turns Boolean checks on finite data into the statement of
# A<n>/Published.lean. Per n, only the data and the kernel checks
# (`decide +kernel`) change. The same five checks as verify_family.sh:
#
#   1. the certificate builds (lake build ChiquipoliFamily.Interval.T<n>.Main);
#   2. no source admits a goal (`sorry` / `admit`), and no `native_decide`;
#   3. the headline theorem of each case and the general theorems depend only on
#      Lean's three standard axioms;
#   4. every negative control (a check on tampered data) is REFUTED by the
#      kernel, and each control's twin (the same check on the true data) compiles;
#   5. every generated file reproduces byte for byte from
#      lean/generators/family/gen_trig.py.
#
# TRIG_STEPS="1 3" runs only the listed steps. A restricted run prints
# "partial run, not a certification".

set -uo pipefail
cd "$(dirname "$0")"

ALL_CASES="16 32 64 128 256"
CASES="${TRIG_CASES:-$ALL_CASES}"
CONTROLS_PER_CASE=12
STEPS="${TRIG_STEPS:-1 2 3 4 5}"
want() { case " $STEPS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; RST=$'\033[0m'
fail=0
note() { printf '%s\n' "$*"; }
ok()   { printf "  ${GRN}PASS${RST}  %s\n" "$*"; }
bad()  { printf "  ${RED}FAIL${RST}  %s\n" "$*"; fail=1; }
skip() { printf "  ${YEL}SKIP${RST}  %s\n" "$*"; }

if want 1; then
note "=== 1. build ==="
# One module at a time: the check files of A256 peak at ~12 GB each, and lake
# would otherwise build them in parallel.
# The theorems proved once for every n (no per-case data).
t0=$(date +%s)
if lake build ChiquipoliFamily.AllN.Root ChiquipoliFamily.AllN.Strip ChiquipoliFamily.AllN.Constructor ChiquipoliFamily.AllN.Multipliers.StrictLocalMax ChiquipoliFamily.AllN.Main >"/tmp/chiqui_trig_build_all.log" 2>&1; then
  ok "every n: lake build AllN.Root, AllN.Strip, AllN.Constructor, AllN.Multipliers.StrictLocalMax, AllN.Main ($(( $(date +%s) - t0 )) s)"
else
  bad "the all-n theorems do not build (see /tmp/chiqui_trig_build_all.log)"
  grep -m5 -E 'error' /tmp/chiqui_trig_build_all.log
fi
for c in $CASES; do
  t0=$(date +%s); built=1
  : >"/tmp/chiqui_trig_build_$c.log"
  for m in Data Checks1 Checks2 Checks3 Checks4 Checks5 Checks6 Checks7 Main; do
    if ! lake build "ChiquipoliFamily.Interval.T$c.$m" >>"/tmp/chiqui_trig_build_$c.log" 2>&1; then built=0; break; fi
  done
  if [ "$built" = 1 ]; then
    ok "T$c: lake build ChiquipoliFamily.Interval.T$c.Main ($(( $(date +%s) - t0 )) s)"
  else
    bad "T$c: build failed at $m (see /tmp/chiqui_trig_build_$c.log)"
    grep -m5 -E 'error' "/tmp/chiqui_trig_build_$c.log"
  fi
done
note ""
fi

if want 2; then
note "=== 2. no admitted goals ==="
strip_lean_comments() {
  awk '
    BEGIN { depth = 0 }
    {
      line = $0; out = ""; i = 1
      while (i <= length(line)) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      print FILENAME ":" FNR ":" out
    }' "$1"
}
hits=""; nsrc=0
files=$(find ChiquipoliFamily/Interval -maxdepth 1 -name '*.lean'; find ChiquipoliFamily/AllN -name '*.lean'; for c in $CASES; do find "ChiquipoliFamily/Interval/T$c" "negative_controls_interval/T$c" -name '*.lean' 2>/dev/null; done)
while IFS= read -r f; do
  [ -n "$f" ] || continue
  nsrc=$((nsrc + 1))
  h=$(strip_lean_comments "$f" | grep -E '\bsorry\b|sorryAx|native_decide|\badmit\b' || true)
  [ -n "$h" ] && hits="${hits}${h}"$'\n'
done <<<"$(printf '%s\n' $files | sort)"
if [ -n "${hits//[$'\n' ]/}" ]; then
  bad "a source file admits a goal"; printf '%s' "$hits"
else
  ok "no 'sorry', 'admit' or 'native_decide' in any of the $nsrc source, control and twin files (comments excluded)"
fi
note ""
fi

if want 3; then
note "=== 3. axiom audit ==="
audit=$(mktemp "${TMPDIR:-/tmp}/chiqui_trig_audit.XXXXXX").lean
{
  for c in $CASES; do echo "import ChiquipoliFamily.Interval.T$c.Main"; done
  echo "import ChiquipoliFamily.Interval.Assemble"
  echo "import ChiquipoliFamily.AllN.Root"
  echo "import ChiquipoliFamily.AllN.Strip"
  echo "import ChiquipoliFamily.AllN.Constructor"
  echo "import ChiquipoliFamily.AllN.Multipliers.StrictLocalMax"
  echo "import ChiquipoliFamily.AllN.Main"
  for t in published_of_checks root_facts sides_eq diams_eq small_of stress_encl bal_zero \
           rigid_of_henneberg stationary_of_bal conv_sound far_sound encl_of_vdOK Shp.nsq_pts \
           closing "closing'" encF_sound encFd_sound root_unique tab_sound enc_sound vertex_eval root_all Strip.strip_rigid Strip.gn_rigid Strip.problem2 Layout.vertexS_eq ConstructorAll.chords_all ConstructorAll.sides_all ConstructorAll.closing_all ConstructorAll.published_rigid_all ConstructorAll.published_all RungVec.rung_vec P3.force_all P3.local_max_of_positive P3.yy_pos P3.lamR_pos P3.sigS_neg P3.strict_local_max_all P1.convex_of_angles P1.small_of_antipodal P1.side_all P1.convex_all P1.small_all P1.published_all_n; do
    echo "#print axioms Chiquipoli.Family.Trig.$t"
  done
  for c in $CASES; do echo "#print axioms Chiquipoli.Family.T$c.published_locally_maximal"; done
} >"$audit"
axout=$(lake env lean "$audit" 2>&1); axrc=$?
rm -f "$audit"
if [ "$axrc" -ne 0 ] || printf '%s' "$axout" | grep -qi 'error'; then
  bad "the axiom audit does not compile"; printf '%s\n' "$axout" | grep -i error | head -5
else
  n=$(printf '%s\n' "$axout" | grep -c 'depends on axioms')
  badl=$(printf '%s\n' "$axout" | grep 'depends on axioms' | grep -v '\[propext, Classical.choice, Quot.sound\]' || true)
  missing=""
  for c in $CASES; do
    printf '%s\n' "$axout" | grep -qF "'Chiquipoli.Family.T$c.published_locally_maximal' depends on axioms" \
      || missing="$missing T$c.published_locally_maximal"
  done
  [ -n "$badl" ] && { bad "unexpected axioms:"; printf '%s\n' "$badl"; }
  [ -n "$missing" ] && bad "headline theorems missing from the audit:$missing"
  if [ -z "$badl" ] && [ -z "$missing" ]; then
    ok "$n theorems depend only on [propext, Classical.choice, Quot.sound], incl. the headline theorem of each case ($CASES)"
  fi
fi
note ""
fi

if want 4; then
note "=== 4. negative controls: each must be REFUTED, its twin must COMPILE ==="
# A rejection counts only if the kernel refuted the check ("proved that the
# proposition ... is false"): a name that did not resolve, a timeout or a
# recursion limit is not a refutation. And only if the twin compiles.
for c in $CASES; do
  d="negative_controls_interval/T$c"; seen=0; good=0
  for f in "$d"/*.lean; do
    [ -e "$f" ] || continue
    seen=$((seen + 1)); b=$(basename "$f"); t="$d/twin/$b"
    [ -f "$t" ] || { bad "T$c $b has no twin"; continue; }
    if out=$(lake env lean "$f" 2>&1); then
      bad "T$c $b COMPILED: the check accepts tampered data"; continue
    elif ! printf '%s' "$out" | grep -q 'is false'; then
      bad "T$c $b rejected for another reason than a refutation:"; printf '%s\n' "$out" | grep -m2 error; continue
    fi
    if tout=$(lake env lean "$t" 2>&1); then good=$((good + 1))
    else bad "T$c $b: its twin does NOT compile, so the rejection proves nothing"; printf '%s\n' "$tout" | grep -m2 error; fi
  done
  ntw=$(find "$d/twin" -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')
  if [ "$seen" -ne "$CONTROLS_PER_CASE" ] || [ "$ntw" -ne "$CONTROLS_PER_CASE" ]; then
    bad "T$c: found $seen controls and $ntw twins, expected $CONTROLS_PER_CASE of each"
  elif [ "$good" -eq "$seen" ]; then
    ok "T$c: all $seen controls refuted by the kernel, all $ntw twins compile"
  fi
done
note ""
fi

if want 5; then
note "=== 5. generated files reproduce from gen_trig.py ==="
if command -v python3 >/dev/null 2>&1; then
  for c in $CASES; do
    scratch=$(mktemp -d "${TMPDIR:-/tmp}/chiqui_trig_T$c.XXXXXX")
    if CHIQUI_OUTDIR="$scratch" python3 generators/family/gen_trig.py "$c" >"$scratch.log" 2>&1; then
      d=$( { diff -rq "$scratch/ChiquipoliFamily/Interval/T$c" "ChiquipoliFamily/Interval/T$c";
             diff -rq "$scratch/negative_controls_interval/T$c" "negative_controls_interval/T$c"; } 2>&1 || true)
      if [ -z "$d" ]; then
        ok "T$c: $(ls ChiquipoliFamily/Interval/T$c/*.lean | wc -l | tr -d ' ') certificate files and $(find negative_controls_interval/T$c -name '*.lean' | wc -l | tr -d ' ') control/twin files reproduce byte for byte"
      else
        bad "T$c: tracked files differ from a fresh run of the generator"; printf '%s\n' "$d" | head -10
      fi
    else
      bad "T$c: the generator failed (see $scratch.log)"; tail -5 "$scratch.log"
    fi
    rm -rf "$scratch" "$scratch.log"
  done
else
  skip "python3 not on PATH -- cannot re-derive the generated files"
fi
note ""
fi

what="GENERAL LEAN CERTIFICATE ($CASES)"
[ "$STEPS" = "1 2 3 4 5" ] || what="GENERAL LEAN STEPS [$STEPS], CASES [$CASES] (partial run, not a certification)"
if [ "$fail" -eq 0 ]; then printf "${GRN}%s PASS${RST}\n" "$what"; else printf "${RED}%s FAIL${RST}\n" "$what"; fi
exit "$fail"
