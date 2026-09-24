#!/usr/bin/env bash
# Verification of the family layer (ChiquipoliFamily/). Run from `lean/`
# (or `make lean-family`):
#
#     ./verify_family.sh
#
# The same five checks verify.sh runs on the A16 development, applied to the
# Bingane–Audet family certificates:
#
#   1. the library builds;
#   2. no source admits a goal (`sorry` / `sorryAx`), and no `native_decide`;
#   3. every audited theorem depends only on Lean's three standard axioms;
#   4. the family's negative controls do NOT compile;
#   5. every generated file under ChiquipoliFamily/A<n>/ reproduces byte for
#      byte from lean/generators/family/gen_family.jl.
#
# It is separate from verify.sh on purpose: the A16 development, its counts and
# the numbers the article quotes are untouched by anything here.

set -uo pipefail
cd "$(dirname "$0")"

CASES="16 32 64"
AXIOM_AUDIT_MIN=48
NEGATIVE_CONTROLS_EXPECTED=5

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; RST=$'\033[0m'
fail=0
note() { printf '%s\n' "$*"; }
ok()   { printf "  ${GRN}PASS${RST}  %s\n" "$*"; }
bad()  { printf "  ${RED}FAIL${RST}  %s\n" "$*"; fail=1; }
skip() { printf "  ${YEL}SKIP${RST}  %s\n" "$*"; }

note "=== 1. build ==="
if lake build ChiquipoliFamily >/tmp/chiqui_family_build.log 2>&1; then
  ok "lake build ChiquipoliFamily"
else
  bad "lake build ChiquipoliFamily (see /tmp/chiqui_family_build.log)"
  tail -20 /tmp/chiqui_family_build.log
  exit 1
fi

note ""
note "=== 2. no admitted goals ==="
# Same comment-stripping as verify.sh, so prose about `sorry` is not a hit.
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
while IFS= read -r f; do
  nsrc=$((nsrc + 1))
  h=$(strip_lean_comments "$f" | grep -E '\bsorry\b|sorryAx|native_decide|\badmit\b' || true)
  [ -n "$h" ] && hits="${hits}${h}"$'\n'
done < <(find ChiquipoliFamily.lean ChiquipoliFamily -name '*.lean' | sort)
if [ -n "${hits//[$'\n' ]/}" ]; then
  bad "a source file admits a goal"
  printf '%s' "$hits"
else
  ok "no 'sorry', 'admit' or 'native_decide' in any of the $nsrc source files (comments excluded)"
fi

note ""
note "=== 3. axiom audit ==="
axout=$(lake env lean ChiquipoliFamily/Audit.lean 2>&1)
axrc=$?
if [ "$axrc" -ne 0 ] || printf '%s' "$axout" | grep -qi 'error'; then
  bad "ChiquipoliFamily/Audit.lean does not compile — the axiom audit is not being performed"
  printf '%s\n' "$axout" | grep -i 'error' | head -5
else
  n=$(printf '%s\n' "$axout" | grep 'depends on axioms' \
      | sed "s/^'\([^']*\)'.*/\1/" | sort -u | wc -l | tr -d ' ')
  bad_lines=$(printf '%s\n' "$axout" | grep 'depends on axioms' \
      | grep -v '\[propext, Classical.choice, Quot.sound\]' || true)
  missing=""
  for c in $CASES; do
    for t in locally_maximal locally_maximal_unique Ieq_imp_R stationary; do
      printf '%s\n' "$axout" | grep -qF "'Chiquipoli.Family.A$c.$t' depends on axioms" \
        || missing="$missing A$c.$t"
    done
  done
  if [ -n "$bad_lines" ]; then
    bad "unexpected axioms:"; printf '%s\n' "$bad_lines"
  elif [ "$n" -lt "$AXIOM_AUDIT_MIN" ]; then
    bad "only $n theorems audited, expected at least $AXIOM_AUDIT_MIN"
  elif [ -n "$missing" ]; then
    bad "headline theorems missing from the audit:$missing"
  else
    ok "$n theorems depend only on [propext, Classical.choice, Quot.sound]"
    ok "every case's headline theorems are audited by name ($CASES)"
  fi
fi

note ""
note "=== 4. negative controls (these MUST fail to compile) ==="
nc_seen=0
for f in negative_controls_family/*.lean; do
  [ -e "$f" ] || continue
  nc_seen=$((nc_seen + 1))
  if ncout=$(lake env lean "$f" 2>&1); then
    bad "$(basename "$f") COMPILED — the corresponding certificate is vacuous"
  elif printf '%s' "$ncout" | grep -qiE "unknown module|unknown package|could not resolve import|object file .* does not exist|no such file|unknown (identifier|constant)"; then
    bad "$(basename "$f") rejected only because a name or import did not resolve"
    printf '%s\n' "$ncout" | head -3
  else
    ok "$(basename "$f") correctly rejected"
  fi
done
[ "$nc_seen" -eq "$NEGATIVE_CONTROLS_EXPECTED" ] \
  || bad "found $nc_seen negative controls, expected $NEGATIVE_CONTROLS_EXPECTED"

note ""
note "=== 5. generated files match the Julia source of truth ==="
if command -v julia >/dev/null 2>&1; then
  for c in $CASES; do
    before="/tmp/chiqui_family_before_A$c"
    # The root module is kept OUTSIDE the directory copy: on a case-insensitive
    # file system (macOS) a file `root.lean` next to `Root.lean` is the same file.
    beforeroot="/tmp/chiqui_family_before_A$c.root.lean"
    rm -rf "$before"; mkdir -p "$before"
    cp ChiquipoliFamily/A$c/*.lean "$before/"; cp "ChiquipoliFamily/A$c.lean" "$beforeroot"
    # The generator deletes and rewrites the whole directory, so a file it no
    # longer writes cannot survive and match itself.
    if (cd .. && julia --project=. lean/generators/family/gen_family.jl "$c" >"/tmp/chiqui_family_gen_A$c.log" 2>&1); then
      d=$(diff -rq "$before" "ChiquipoliFamily/A$c" 2>&1 || true)
      d2=$(diff -q "$beforeroot" "ChiquipoliFamily/A$c.lean" 2>&1 || true)
      if [ -z "$d$d2" ]; then
        ok "A$c: all $(ls ChiquipoliFamily/A$c/*.lean | wc -l | tr -d ' ') files reproduce byte for byte"
      else
        bad "A$c: generated files differ from a fresh run"; printf '%s\n' "$d" "$d2" | head -10
        cp "$before"/*.lean "ChiquipoliFamily/A$c/"; cp "$beforeroot" "ChiquipoliFamily/A$c.lean"
      fi
    else
      bad "A$c: the generator failed (see /tmp/chiqui_family_gen_A$c.log)"
      cp "$before"/*.lean "ChiquipoliFamily/A$c/"; cp "$beforeroot" "ChiquipoliFamily/A$c.lean"
    fi
  done
else
  skip "julia not on PATH — cannot re-derive the generated files"
fi

note ""
if [ "$fail" -eq 0 ]; then
  printf "${GRN}FAMILY LEAN CERTIFICATE PASS${RST}\n"
else
  printf "${RED}FAMILY LEAN CERTIFICATE FAIL${RST}\n"
fi
exit "$fail"
