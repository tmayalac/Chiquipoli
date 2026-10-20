#!/usr/bin/env bash
# Full verification of the Lean layer. Run from `lean/` (or `make lean`):
#
#     ./verify.sh
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
# Check 5 re-runs the nine Julia generators (generators/) and requires every
# file under ChiquipoliLean/Generated/ to be byte-identical to the committed
# one, so the Lean layer cannot silently drift from the certified Julia
# arithmetic.

set -uo pipefail
cd "$(dirname "$0")"

# Pinned expectations. A check that only inspects whatever happens to be on
# disk cannot notice material being removed; these two numbers make a silent
# reduction in coverage a FAIL. Update them deliberately when adding theorems
# to the audit, new negative controls, or new source files.
AXIOM_AUDIT_MIN=137
NEGATIVE_CONTROLS_EXPECTED=32
LEAN_SOURCES_MIN=38   # ChiquipoliLean.lean + the 37 modules under ChiquipoliLean/

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
# Recursive: the sources live in subdirectories (Theory/, Constructor/,
# Generated/, Instances/). A `ChiquipoliLean/*.lean` glob saw only the top
# level, so after the move into subdirectories it would have scanned two files
# and reported PASS. The count of scanned files is pinned for the same reason.
hits=""
nsrc=0
while IFS= read -r f; do
  nsrc=$((nsrc + 1))
  h=$(strip_lean_comments "$f" | grep -E '\bsorry\b|sorryAx' || true)
  [ -n "$h" ] && hits="${hits}${h}"$'\n'
done < <(find ChiquipoliLean.lean ChiquipoliLean -name '*.lean' | sort)
if [ -n "${hits//[$'\n' ]/}" ]; then
  bad "a source file admits a goal with 'sorry'"
  printf '%s' "$hits"
elif [ "$nsrc" -lt "$LEAN_SOURCES_MIN" ]; then
  bad "scanned only $nsrc source files for 'sorry', expected at least $LEAN_SOURCES_MIN"
else
  ok "no 'sorry' in any of the $nsrc source files (comments excluded)"
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
      Chiquipoli.Feasible.square_strict_local_max \
      Chiquipoli.Feasible.radius_of_certificate \
      Chiquipoli.Feasible.A16_coercive \
      Chiquipoli.Feasible.A16_radius \
      Chiquipoli.Feasible.radius_of_certificate_unit \
      Chiquipoli.Feasible.A16_radius_printed \
      Chiquipoli.Feasible.A16_printed_constants
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
    if ncout=$(lake env lean "$f" 2>&1); then
      bad "$(basename "$f") COMPILED — the corresponding theorem is vacuous"
    elif printf '%s' "$ncout" | grep -qiE "unknown module|unknown package|could not resolve import|object file .* does not exist|no such file"; then
      # Rejected, but for the wrong reason: a control whose import is broken
      # fails to compile whatever its statement says, so it guards nothing.
      bad "$(basename "$f") rejected only because an import did not resolve"
      printf '%s\n' "$ncout" | head -3
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
  # The committed file is moved aside BEFORE the generator runs, so the
  # generator must write it again at exactly this path. Comparing against a copy
  # left in place could not tell "reproduced" from "written somewhere else": a
  # generator pointed at a stale path would leave this file untouched, and it
  # would then match itself.
  check_generated() {
    local file="$1" gen="$2" tag
    tag=$(basename "$file" .lean)
    mv "ChiquipoliLean/$file" "/tmp/chiqui_before_$tag.lean"
    if (cd .. && julia --project=. "lean/generators/$gen" >"/tmp/chiqui_gen_$tag.log" 2>&1) \
         && [ -f "ChiquipoliLean/$file" ]; then
      if diff -q "/tmp/chiqui_before_$tag.lean" "ChiquipoliLean/$file" >/dev/null; then
        ok "$file reproduces byte-for-byte ($gen)"
      else
        bad "$file differs from a fresh run of $gen"
        diff "/tmp/chiqui_before_$tag.lean" "ChiquipoliLean/$file" | head -20
      fi
    else
      bad "$gen failed or did not write ChiquipoliLean/$file (see /tmp/chiqui_gen_$tag.log)"
      # Put the committed file back, so a failed check does not damage the tree.
      cp "/tmp/chiqui_before_$tag.lean" "ChiquipoliLean/$file"
    fi
  }
  check_generated Generated/Polynomials.lean    extract_polys.jl
  check_generated Generated/Positivity.lean     gen_positivity.jl
  check_generated Generated/InactiveMargin.lean gen_inactive.jl
  check_generated Generated/Diameter.lean       gen_diameter.jl
  check_generated Generated/Convexity.lean      gen_convexity.jl
  check_generated Generated/Multipliers.lean    gen_multipliers.jl
  check_generated Generated/Rank.lean           gen_rank.jl
  check_generated Generated/Radius.lean         gen_radius.jl
  check_generated Generated/RadiusPrinted.lean  gen_radius_printed.jl
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
