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

# --- presentation (only presentation: the stages below are unchanged) --------
# Colours, the banner and the moving progress bar only on an interactive
# terminal; a log or `nohup` run gets plain lines.
TTY=0; [ -t 1 ] && TTY=1
if [ "$TTY" = 1 ] && [ -z "${NO_COLOR:-}" ]; then
  RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; CYN=$'\033[36m'
  DIM=$'\033[2m'; BLD=$'\033[1m'; RST=$'\033[0m'
else
  RED=""; GRN=""; YEL=""; CYN=""; DIM=""; BLD=""; RST=""
fi
COLS=$(tput cols 2>/dev/null || echo 100)
{ [ "$COLS" -gt 140 ] || [ "$COLS" -lt 60 ]; } && COLS=140
export CA_COLS="$COLS" CA_RED="$RED" CA_GRN="$GRN" CA_YEL="$YEL" CA_DIM="$DIM" CA_BLD="$BLD" CA_RST="$RST"

rule() { local s="" k; for ((k = 0; k < COLS - 2; k++)); do s+="$1"; done; printf "  ${DIM}%s${RST}\n" "$s"; }
upper() { printf '%s' "$1" | tr '[:lower:]' '[:upper:]'; }
# The heading of a stage, cut to the terminal width (characters, not bytes).
heading() {
  printf '%s · %s' "$(upper "$1")" "$2" | perl -CSD -Mutf8 -ne '
    my ($w,$B,$D,$Z) = ($ENV{CA_COLS} - 4, @ENV{qw(CA_BLD CA_DIM CA_RST)});
    $_ = substr($_,0,$w-1)."…" if length($_) > $w;
    my ($a,$b) = split / · /, $_, 2; print "  $B$a$Z $D·$Z $b\n"'
}

banner() {
  [ "$TTY" = 1 ] || return 0
  printf "\n${CYN}${BLD}"
  printf '  %s\n' \
    " ██████╗██╗  ██╗██╗ ██████╗ ██╗   ██╗██╗██████╗  ██████╗ ██╗     ██╗" \
    "██╔════╝██║  ██║██║██╔═══██╗██║   ██║██║██╔══██╗██╔═══██╗██║     ██║" \
    "██║     ███████║██║██║   ██║██║   ██║██║██████╔╝██║   ██║██║     ██║" \
    "██║     ██╔══██║██║██║▄▄ ██║██║   ██║██║██╔═══╝ ██║   ██║██║     ██║" \
    "╚██████╗██║  ██║██║╚██████╔╝╚██████╔╝██║██║     ╚██████╔╝███████╗██║" \
    " ╚═════╝╚═╝  ╚═╝╚═╝ ╚══▀▀═╝  ╚═════╝ ╚═╝╚═╝      ╚═════╝ ╚══════╝╚═╝"
  printf "${RST}\n  ${DIM}exact, interval and formal verification of equilateral small polygons${RST}\n"
}

# A box-drawn table from tab-separated rows on stdin; the first row is the
# header. Widths are counted in characters (perl), so ∈, ℓ and ⊂ align, and the
# last column is cut to the terminal width. PASS / FAIL / SKIP are coloured.
table() {
  perl -CSD -Mutf8 -e '
    my @r = map { chomp; [split /\t/, $_, -1] } <STDIN>; exit unless @r;
    my $n = @{$r[0]}; my @w = (0) x $n;
    for my $x (@r) { for my $j (0..$n-1) { my $l = length($x->[$j] // ""); $w[$j] = $l if $l > $w[$j]; } }
    my $fixed = 2 + 3*$n + 1; $fixed += $w[$_] for 0..$n-2;
    my $room = $ENV{CA_COLS} - $fixed; $room = 12 if $room < 12; $w[$n-1] = $room if $w[$n-1] > $room;
    my ($D,$B,$Z) = ($ENV{CA_DIM},$ENV{CA_BLD},$ENV{CA_RST});
    sub cell { my ($s,$w) = @_; $s //= ""; $s = substr($s,0,$w-1)."…" if length($s) > $w; $s . " " x ($w - length($s)) }
    sub col { my $s = shift; my $c = $s =~ /^\s*(PASS|CERTIFIED|PROVEN)/ ? $ENV{CA_GRN} : $s =~ /^\s*FAIL/ ? $ENV{CA_RED} : $s =~ /^\s*SKIP/ ? $ENV{CA_YEL} : ""; $c ? "$c$s$Z" : $s }
    sub line { my ($l,$m,$e) = @_; print "  $D$l", join($m, map { "─" x ($_+2) } @w), "$e$Z\n" }
    line("┌","┬","┐");
    for my $i (0..$#r) {
      my @c = map { cell($r[$i][$_], $w[$_]) } 0..$n-1;
      @c = $i == 0 ? map { "$B$_$Z" } @c : map { col($_) } @c;
      print "  $D│$Z ", join(" $D│$Z ", @c), " $D│$Z\n";
      line("├","┼","┤") if $i == 0;
    }
    line("└","┴","┘");'
}

# The checks a stage reports, one per line as [name]  PASS  detail: its own
# "X PASS = true" lines, the gates of a family certificate, the exact
# identities counted once, the test totals, the failures of the records check,
# and the verdict lines the scripts print.
details() {
  perl -CSD -Mutf8 -ne '
    BEGIN { ($G,$R,$D,$Z) = @ENV{qw(CA_GRN CA_RED CA_DIM CA_RST)}; $W = $ENV{CA_COLS} - 4;
            %ref = ("strict monotonicity on search interval" => "Prop 6.2(1) · 0 ∉ F′(I_search)", "domain" => "Prop 6.2(1) · Z_root ⊂ I_search", "derivative" => "Prop 6.2(1) · 0 ∉ F′(Z_root)", "Newton" => "Prop 6.2(1) · N(Z_root) ⊂ int Z_root", "unique root in box" => "Prop 6.2(1)", "unique root in whole search interval" => "Prop 6.2(1)", "strict convexity" => "Prop 6.2(3) · 224 support determinants > 0", "inactive" => "Prop 6.2(4) · 105 inactive pairs at distance < 1", "minor regular" => "Prop 6.2(6) · ‖I − CM‖∞ < 1", "rank 30" => "Prop 6.2(6) · rank D(e,d) = 30", "normalized matrix" => "§6.4 · the normalised system M₀ is regular", "Krawczyk" => "Prop 6.2(5) · the multipliers are enclosed", "all lambdas positive" => "Prop 6.2(5) · every λ_ij > 0", "omitted equations recovered" => "§6.4 · the three omitted equations hold", "nominal ell inside its certified enclosure" => "Prop 6.2(2)", "root box inside the interior of the boxes of 03, 04, 05" => "§6.3 · Z_root ⊂ int Z_cert"); }
    sub add { my ($n,$ok,$d) = @_; my $k = lc $n; return if $seen{$k}++; $d = $ref{$n} // "" unless defined $d && length $d; push @E, [$n, $ok, $d] }
    s/\e\[[0-9;]*m//g; chomp;
    if (/^([a-z_]+)\s{2,}(PASS|FAIL)\s+(.*)$/) { add($1, $2 eq "PASS", $3) }
    elsif (/^\s*(.+?) PASS = (true|false)\s*$/) { add($1, $2 eq "true") }
    elsif (/^(edge|diam) \(\d+,\d+\):/) { $ni++; $nok++ if /PROVED/ }
    elsif (/^Chiquipoli\s+\|\s+(\d+)\s+(\d+)/) { add("test suite", $1 == $2, "$1 of $2 assertions") }
    elsif (/^\s*(.+?)\s+\*\*\*\s*(.*?)\s*\*\*\*\s*$/) { add($1, 0, $2) }
    elsif (/^(FINAL FIRST-ORDER CERTIFICATE|FAMILY CERTIFICATE A|EXPLICIT RADIUS|RECORDS CHECK|LEAN CERTIFICATE|LEAN FAMILY CERTIFICATE)/) {
      my $c = /FAIL|NOT /i ? $R : $G; push @H, "    $D→$Z $c$_$Z" }
    END {
      if ($ni) { @E = grep { lc($_->[0]) ne "exact identities" } @E;
                 push @E, ["exact identities", $nok == $ni, "Lemma 6.1 · $nok of $ni equalities, exact in Q[c]"] }
      my $nw = 0; for (@E) { my $l = length($_->[0]) + 2; $nw = $l if $l > $nw } $nw = 44 if $nw > 44;
      for (@E) {
        my ($n,$ok,$d) = @$_; my $b = "[$n]"; $b = substr($b,0,$nw-2)."…]" if length($b) > $nw;
        my $room = $W - 4 - $nw - 2 - 4 - 2; $room = 10 if $room < 10;
        $d = substr($d,0,$room-1)."…" if length($d) > $room;
        printf "    %-*s  %s%s%s  %s\n", $nw, $b, $ok ? $G : $R, $ok ? "PASS" : "FAIL", $Z, $d;
      }
      print "$_\n" for @H }' "$1"
}

# Typical durations (seconds), for the progress bar; 0 = unknown, the bar then
# moves without promising a fraction.
est_for() {
  case "$1" in
    test) echo 42 ;;   certify-a16|dedicated-julia-A16) echo 6 ;;   radius|radius-A16) echo 5 ;;
    certificate-A16|certificate-A32|certificate-A64|certificate-A128) echo 11 ;;
    records|family-record) echo 6 ;;   literature) echo 160 ;;   family-certs) echo 420 ;;
    mutation-check) echo 900 ;;   stress-family) echo 900 ;;
    *) echo 0 ;;
  esac
}

# A moving bar while the stage runs: filled to the expected fraction (never
# 100 % before it ends) with the time left, or a block sweeping back and forth.
PROGRESS_PID=""
progress() {
  local pid="$1" name="$2" est="$3" t0 el i=0 w=26 k f p bar eta
  local spin=(⠋ ⠙ ⠹ ⠸ ⠼ ⠴ ⠦ ⠧ ⠇ ⠏)
  t0=$(date +%s)
  while kill -0 "$pid" 2>/dev/null; do
    el=$(( $(date +%s) - t0 )); bar=""
    if [ "$est" -gt 0 ]; then
      # fraction from the frame counter (one frame = 0.12 s): smooth, no subprocess
      f=$(( i * 12 * w / (est * 100) )); [ "$f" -gt $((w - 1)) ] && f=$((w - 1))
      for ((k = 0; k < w; k++)); do [ "$k" -lt "$f" ] && bar+="█" || bar+="░"; done
      [ "$el" -lt "$est" ] && eta="~$((est - el)) s left" || eta="nearly done"
    else
      p=$(( i % (2 * (w - 5)) )); [ "$p" -ge $((w - 5)) ] && p=$(( 2 * (w - 5) - p ))
      for ((k = 0; k < w; k++)); do { [ "$k" -ge "$p" ] && [ "$k" -lt $((p + 5)) ]; } && bar+="█" || bar+="░"; done
      eta=""
    fi
    printf "\r  ${CYN}%s${RST} %-24s ${CYN}%s${RST} %4ds ${DIM}%s${RST}\033[K" "${spin[$((i % 10))]}" "$name" "$bar" "$el" "$eta"
    i=$((i + 1)); sleep 0.12
  done
  printf "\r\033[K"
}
# Ctrl-C stops the running stage too (a background job ignores SIGINT), and a
# planted-defect harness receives TERM, which runs its restore.
trap '[ -n "$PROGRESS_PID" ] && kill -TERM "$PROGRESS_PID" 2>/dev/null; printf "\n"; exit 130' INT TERM
MODE="${1:-all}"; CASE="${2:-}"
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
LOGDIR="$ROOT/logs/check_all/$STAMP"
mkdir -p "$LOGDIR"

declare -a NAMES=() RESULTS=() TIMES=() NOTES=()
record() { NAMES+=("$1"); RESULTS+=("$2"); TIMES+=("$3"); NOTES+=("$4"); }

# stage <name> <what it establishes> <command...>
stage() {
  local name="$1" what="$2"; shift 2
  local log="$LOGDIR/$name.log" t0 dt rc
  printf "\n"; rule "═"; heading "$name" "$what"; rule "═"
  t0=$(date +%s)
  if [ "$TTY" = 1 ]; then
    "$@" >"$log" 2>&1 &
    PROGRESS_PID=$!
    progress "$PROGRESS_PID" "$name" "$(est_for "$name")"
    wait "$PROGRESS_PID"; rc=$?; PROGRESS_PID=""
  else
    "$@" >"$log" 2>&1; rc=$?
  fi
  dt=$(( $(date +%s) - t0 ))
  if [ "$rc" -eq 0 ]; then
    printf "  %-36s ${GRN}${BLD}PASS${RST}  ${DIM}%ds · %s${RST}\n" "[$name]" "$dt" "${log#$ROOT/}"
    details "$log"
    record "$name" PASS "$dt" "$what"
  else
    printf "  %-36s ${RED}${BLD}FAIL${RST}  ${DIM}%ds · %s${RST}\n" "[$name]" "$dt" "${log#$ROOT/}"
    details "$log"
    printf "    ${DIM}last lines of the log:${RST}\n"
    tail -6 "$log" | sed $'s/\033\\[[0-9;]*m//g; s/^/      /'
    record "$name" FAIL "$dt" "log: ${log#$ROOT/}"
  fi
}
skip() {
  printf "\n"; rule "═"; printf "  ${BLD}%s${RST}\n" "$(upper "$1")"; rule "═"
  printf "  %-36s ${YEL}${BLD}SKIP${RST}  %s\n" "[$1]" "$2"; record "$1" SKIP 0 "$2"
}

have() { command -v "$1" >/dev/null 2>&1; }
clean_tree() { git rev-parse --git-dir >/dev/null 2>&1 && [ -z "$(git status --porcelain)" ]; }
lean_ready() { have lake && [ -d lean/.lake/packages/mathlib ]; }

# --- preflight ----------------------------------------------------------------
banner
have julia || { echo "julia is not on PATH; nothing can run"; exit 2; }
if [ "$(uname)" = Darwin ]; then memgb=$(( $(sysctl -n hw.memsize) / 1073741824 )); else memgb=$(( $(awk '/MemTotal/ {print $2}' /proc/meminfo) / 1048576 )); fi
case "$MODE" in
  all)   EST="~35 min; the A64 Lean steps need ~13 GB" ;;
  lean)  EST="~10 min if the Lean libraries are built, ~30 min from scratch; ~13 GB" ;;
  quick) EST="~5 min; Julia only" ;;
  case)  EST="1-15 min depending on the case" ;;
  fast)  EST="10 s (n <= 256) to a few minutes (n = 1024); Julia only" ;;
  candidate) EST="on a clean tree: A16 ~18 min, A32 ~10 min, A64 ~32 min" ;;
  *) EST="—" ;;
esac
clean_tree && TREE="clean" || TREE="dirty: the stages that need a clean tree are skipped"
printf "\n"
{ printf 'run\t%s\n' "check_all"
  printf 'mode\t%s\n' "$MODE${CASE:+ $CASE}"
  printf 'estimated\t%s\n' "$EST"
  printf 'memory\t%s GB\n' "$memgb"
  printf 'git tree\t%s\n' "$TREE"
  printf 'commit\t%s\n' "$(git rev-parse --short HEAD 2>/dev/null || echo —)"
  printf 'logs\t%s\n' "${LOGDIR#$ROOT/}"; } | table
[ "$memgb" -lt 16 ] && [ "$MODE" != quick ] && printf "  ${YEL}warning${RST}: less than 16 GB of memory; the A64 Lean build may not fit\n"

# The family members, read from their single source (cases/exact_coords.jl).
family_list() { sed -n "s/^const $1 = (\(.*\))/\1/p" cases/exact_coords.jl | tr -d ','; }
FAMILY_N=$(family_list FAMILY_N); FAMILY_LEAN_N=$(family_list FAMILY_LEAN_N)
FAMILY_TRIG_N=$(family_list FAMILY_TRIG_N)
in_list() { case " $2 " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
# The exact identities are proved in parallel when Julia has threads.
export JULIA_NUM_THREADS="${JULIA_NUM_THREADS:-auto}"

julia_run() { julia --project=. "$@"; }
family_case() { (cd lean && FAMILY_CASES="$1" ./verify_family.sh); }
trig_case() { (cd lean && TRIG_CASES="$1" ./verify_general.sh); }

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
  stage records     "every record agrees with the tree and the Lean layer" julia_run pipeline/check_records.jl
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
    [ "$CASE" = 16 ] && printf "\n  ${DIM}note: A16 also has its dedicated certificate: make verify (Julia) and make lean (Lean)${RST}\n"
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
  stage radius       "an explicit radius of strict local maximality of A16 -> results/radius_certificate.toml" julia_run pipeline/certify_radius.jl
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
  stage records "every record agrees with the tree and the Lean layer" julia_run pipeline/check_records.jl
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
  if [ "$N" = 16 ]; then
    stage "dedicated-julia-A16" "the article's dedicated A16 interval certificate: eight gates (nothing recorded)" \
      env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_a16.jl
  fi
  printf "\n  ${DIM}note: the Julia certificate only; make a%s-complete adds the suite, Lean, controls and planted defects${RST}\n" "$N"
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
    stage "radius-A16" "an explicit radius of strict local maximality of A16 (nothing recorded)" \
      env CHIQUI_NO_RECORD=1 julia --project=. pipeline/certify_radius.jl
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
printf "\n"; rule "═"; printf "  ${BLD}SUMMARY${RST}\n"; rule "═"
nf=0; ns=0; total=0
{ printf 'stage\tresult\ttime\tnotes\n'
  for i in "${!NAMES[@]}"; do
    r="${RESULTS[$i]}"; [ "$r" = FAIL ] && nf=$((nf + 1)); [ "$r" = SKIP ] && ns=$((ns + 1))
    total=$((total + TIMES[$i]))
    printf '%s\t%s\t%ss\t%s\n' "${NAMES[$i]}" "$r" "${TIMES[$i]}" "${NOTES[$i]}"
  done; } > "$LOGDIR/summary.tsv"
table < "$LOGDIR/summary.tsv"
printf "  ${DIM}total %d min %d s · logs in %s${RST}\n\n" $((total / 60)) $((total % 60)) "${LOGDIR#$ROOT/}"
if [ "$nf" -gt 0 ]; then
  printf "  ${RED}${BLD}FAIL${RST} — %d stage(s) failed\n\n" "$nf"; exit 1
elif [ "$ns" -gt 0 ]; then
  printf "  ${YEL}${BLD}INCOMPLETE${RST} — nothing failed, but %d stage(s) were skipped; this is not a full pass\n\n" "$ns"; exit 3
else
  printf "  ${GRN}${BLD}ALL CHECKS PASS${RST} — every stage of '%s' ran and passed\n\n" "$MODE${CASE:+ $CASE}"
fi
