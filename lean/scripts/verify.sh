#!/usr/bin/env bash
# Full verification of the Lean layer. Run from `lean/`:
#
#     ./scripts/verify.sh
#
# Four independent checks, in increasing order of what they rule out:
#
#   1. the development builds;
#   2. no source admits a goal (`sorry` / `sorryAx`);
#   3. every headline theorem depends only on Lean's three standard axioms;
#   4. deliberately false variants of the theorems do NOT compile — the
#      statements are not vacuous, and the two "conditional" side identities
#      genuinely need the constructor equation.
#
# Check 5 re-runs the Julia generator and requires the regenerated
# `Generated.lean` to be byte-identical to the committed one, so the Lean
# polynomial layer cannot silently drift from the certified Julia arithmetic.

set -uo pipefail
cd "$(dirname "$0")/.."

# Pinned expectations. A check that only inspects whatever happens to be on
# disk cannot notice material being removed; these two numbers make a silent
# reduction in coverage a FAIL. Update them deliberately when adding theorems
# to the audit or new negative controls.
AXIOM_AUDIT_MIN=107
NEGATIVE_CONTROLS_EXPECTED=26

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; RST=$'\033[0m'
fail=0
note() { printf '%s\n' "$*"; }
ok()   { printf "  ${GRN}PASS${RST}  %s\n" "$*"; }
bad()  { printf "  ${RED}FAIL${RST}  %s\n" "$*"; fail=1; }
skip() { printf "  ${YEL}SKIP${RST}  %s\n" "$*"; }

note "=== 1. build ==="
if lake build >/tmp/chiqui_lean_build.log 2>&1; then
  ok "lake build"
else
  bad "lake build (see /tmp/chiqui_lean_build.log)"
  tail -20 /tmp/chiqui_lean_build.log
  exit 1
fi

note ""
note "=== 2. no admitted goals ==="
# Strip Lean comments before searching, so that prose *about* `sorry` (this
# repository discusses it at length) is not mistaken for an admitted goal.
# Handles nested `/- -/` blocks and `--` line comments.
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
hits=""
for f in ChiquipoliLean.lean ChiquipoliLean/*.lean; do
  [ -e "$f" ] || continue
  h=$(strip_lean_comments "$f" | grep -E '\bsorry\b|sorryAx' || true)
  [ -n "$h" ] && hits="${hits}${h}"$'\n'
done
if [ -n "${hits//[$'\n' ]/}" ]; then
  bad "a source file admits a goal with 'sorry'"
  printf '%s' "$hits"
else
  ok "no 'sorry' in any source file (comments excluded)"
fi

note ""
note "=== 3. axiom audit ==="
axout=$(lake env lean ChiquipoliLean/Audit.lean 2>&1)
axrc=$?
# Audit.lean must COMPILE. It once carried `#print axioms` on a name that did
# not exist: Lean emitted "unknown constant", this check only grepped for
# sorryAx and for non-standard axiom lines, and the run was reported as PASS.
# An audit file that does not compile audits nothing.
if [ "$axrc" -ne 0 ] || printf '%s' "$axout" | grep -qi 'error'; then
  bad "Audit.lean does not compile — the axiom audit is not being performed"
  printf '%s\n' "$axout" | grep -i 'error' | head -5
elif printf '%s' "$axout" | grep -q 'sorryAx'; then
  bad "some theorem depends on sorryAx"
  printf '%s\n' "$axout" | grep 'sorryAx'
else
  # Count DISTINCT theorems, not output lines. Duplicated `#print axioms`
  # entries in Audit.lean silently inflated this figure once, and the number is
  # quoted in release notes — so deduplicate here rather than trusting the file.
  n=$(printf '%s\n' "$axout" | grep 'depends on axioms' \
      | sed "s/^'\([^']*\)'.*/\1/" | sort -u | wc -l | tr -d ' ')
  bad_lines=$(printf '%s\n' "$axout" \
      | grep 'depends on axioms' \
      | grep -v '\[propext, Classical.choice, Quot.sound\]' || true)
  if [ -n "$bad_lines" ]; then
    bad "unexpected axioms:"
    printf '%s\n' "$bad_lines"
  elif [ "$n" -lt "$AXIOM_AUDIT_MIN" ]; then
    bad "only $n theorems audited, expected at least $AXIOM_AUDIT_MIN — coverage silently dropped"
  else
    # A count is not coverage. Deleting a headline theorem from Audit.lean and
    # adding a trivial lemma in its place keeps the total at $AXIOM_AUDIT_MIN
    # and passes every check above. Name the results whose audit is the reason
    # this file exists, and require each of them to appear by name.
    missing=""
    nwant=0
    for want in \
      Chiquipoli.A16_certificate \
      Chiquipoli.FirstOrder.no_admissible_direction \
      Chiquipoli.FirstOrder.A16_no_admissible_direction \
      Chiquipoli.FirstOrder.A16_multiplier_identity \
      Chiquipoli.FirstOrder.A16_lam_pos \
      Chiquipoli.FirstOrder.rank_eq_thirty \
      Chiquipoli.FirstOrder.ker_jacA16 \
      Chiquipoli.FirstOrder.square_no_admissible_direction \
      Chiquipoli.FirstOrder.rhombus_not_isLocalMax \
      Chiquipoli.FirstOrder.g_hasStrictFDerivAt \
      Chiquipoli.FirstOrder.g_at_p \
      Chiquipoli.perimeter_bounds \
      Chiquipoli.constructor_root_unique_in_search \
      Chiquipoli.constructor_root_existsUnique_article_search \
      Chiquipoli.multipliers_certified \
      Chiquipoli.all_sides \
      Chiquipoli.all_active_diameters \
      Chiquipoli.Feasible.Keq_iff \
      Chiquipoli.Feasible.eD_eq_zero_of_blowup \
      Chiquipoli.Feasible.dD_nonpos_of_blowup \
      Chiquipoli.Feasible.isFeasible_move \
      Chiquipoli.Feasible.slice_of_generators \
      Chiquipoli.Feasible.no_blowup_sequence \
      Chiquipoli.Feasible.eventually_no_better \
      Chiquipoli.Feasible.eventually_congruent_of_no_worse \
      Chiquipoli.Feasible.thm_3_5 \
      Chiquipoli.Feasible.thm_3_5_le \
      Chiquipoli.Feasible.A16_bridge \
      Chiquipoli.Feasible.A16_isFeasibleConvex \
      Chiquipoli.Feasible.A16_strict_local_max \
      Chiquipoli.Feasible.A16_locally_maximal \
      Chiquipoli.Feasible.square_strict_local_max
    do
      nwant=$((nwant + 1))
      printf '%s\n' "$axout" | grep -qF "'$want' depends on axioms" || missing="$missing $want"
    done
    if [ -n "$missing" ]; then
      bad "audited count is $n, but these load-bearing theorems are NOT audited:"
      for m in $missing; do printf '           %s\n' "$m"; done
    else
      ok "$n theorems depend only on [propext, Classical.choice, Quot.sound]"
      ok "all $nwant load-bearing theorems are present by name in the audit"
    fi
  fi
fi

note ""
note "=== 4. negative controls (these MUST fail to compile) ==="
# The expected count is pinned. Without it, deleting a control — or the whole
# directory — silently reduced coverage while the run still reported PASS.
if [ -d negative_controls ]; then
  nc_seen=0
  for f in negative_controls/*.lean; do
    [ -e "$f" ] || continue
    nc_seen=$((nc_seen + 1))
    if lake env lean "$f" >/dev/null 2>&1; then
      bad "$(basename "$f") COMPILED — the corresponding theorem is vacuous"
    else
      ok "$(basename "$f") correctly rejected"
    fi
  done
  if [ "$nc_seen" -ne "$NEGATIVE_CONTROLS_EXPECTED" ]; then
    bad "found $nc_seen negative controls, expected $NEGATIVE_CONTROLS_EXPECTED"
  fi
else
  bad "no negative_controls/ directory — every theorem here is unguarded against vacuity"
fi

note ""
note "=== 5. generated layer matches the Julia source of truth ==="
if command -v julia >/dev/null 2>&1; then
  # Every generated file must reproduce byte-for-byte, or the Lean layer has
  # silently drifted from the certified Julia arithmetic.
  check_generated() {
    local file="$1" gen="$2"
    cp "ChiquipoliLean/$file" "/tmp/chiqui_before_$file"
    if (cd .. && julia --project=. "lean/tools/$gen" >"/tmp/chiqui_gen_$file.log" 2>&1); then
      if diff -q "/tmp/chiqui_before_$file" "ChiquipoliLean/$file" >/dev/null; then
        ok "$file reproduces byte-for-byte ($gen)"
      else
        bad "$file differs from a fresh run of $gen"
        diff "/tmp/chiqui_before_$file" "ChiquipoliLean/$file" | head -20
      fi
    else
      bad "$gen failed (see /tmp/chiqui_gen_$file.log)"
    fi
  }
  check_generated Generated.lean      extract_polys.jl
  check_generated Positivity.lean     gen_positivity.jl
  check_generated InactiveMargin.lean gen_inactive.jl
  check_generated Diameter.lean       gen_diameter.jl
  check_generated Convexity.lean      gen_convexity.jl
  check_generated Multipliers.lean    gen_multipliers.jl
  check_generated Rank.lean           gen_rank.jl
else
  skip "julia not on PATH — cannot re-derive the generated files"
fi

note ""
if [ "$fail" -eq 0 ]; then
  printf "${GRN}LEAN CERTIFICATE PASS${RST}\n"
else
  printf "${RED}LEAN CERTIFICATE FAIL${RST}\n"
fi
exit "$fail"
