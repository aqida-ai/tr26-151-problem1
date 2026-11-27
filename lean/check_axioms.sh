#!/usr/bin/env bash
# AQIDA_CONSTITUTIONAL_SCOPE: gate | CLAIM_BOUNDARY: release packaging of already recorded results; states nothing new | FALSIFICATION_TESTS: lake build, check_axioms.sh, verify_certificates.py
#
# Axiom check for the Lean files of this folder. Run from the folder `lean/` after `lake exe cache get`
# (and preferably `lake build`). Not executed on the authoring machine in this form.
#
#  1. `lake env lean TheoremL.lean` and `lake env lean TheoremL_LayerRanks.lean` must exit with code 0,
#     must print the expected number of `#print axioms` lines (10 and 17), every one of which lists only
#     propext, Classical.choice, Quot.sound; no line may mention sorryAx, `sorry` or an error.
#  2. `lake env lean NegativeControl.lean` (a planted `sorry`) MUST mention sorryAx; otherwise the check
#     itself is broken and the script fails.
set -u
cd "$(dirname "$0")"

ALLOWED="propext Classical.choice Quot.sound"
status=0

check_main () {
  local file="$1" expected="$2" out rc n
  echo "== lake env lean $file"
  out="$(lake env lean "$file" 2>&1)"; rc=$?
  printf '%s\n' "$out"
  if [ "$rc" -ne 0 ]; then echo "FAIL: $file: exit code $rc"; status=1; fi
  if printf '%s\n' "$out" | grep -q 'sorryAx'; then echo "FAIL: $file: sorryAx reported"; status=1; fi
  if printf '%s\n' "$out" | grep -qi "declaration uses 'sorry'\|declaration uses \`sorry\`"; then
    echo "FAIL: $file: declaration uses sorry"; status=1; fi
  if printf '%s\n' "$out" | grep -q 'error'; then echo "FAIL: $file: an output line mentions an error"; status=1; fi
  n="$(printf '%s\n' "$out" | grep -c 'depends on axioms:')"
  if [ "$n" -ne "$expected" ]; then
    echo "FAIL: $file: $n '#print axioms' lines, expected $expected"; status=1; fi
  # every axiom named on every 'depends on axioms: [...]' line must be in the allowed list
  while IFS= read -r line; do
    list="${line#*depends on axioms: [}"; list="${list%%]*}"
    for ax in $(printf '%s' "$list" | tr ',' ' '); do
      case " $ALLOWED " in
        *" $ax "*) ;;
        *) echo "FAIL: $file: axiom '$ax' is not allowed: $line"; status=1 ;;
      esac
    done
  done < <(printf '%s\n' "$out" | grep 'depends on axioms:')
}

check_main TheoremL.lean 10
check_main TheoremL_LayerRanks.lean 17

echo "== lake env lean NegativeControl.lean (expected: sorryAx)"
neg="$(lake env lean NegativeControl.lean 2>&1)"
printf '%s\n' "$neg"
if printf '%s\n' "$neg" | grep -q 'sorryAx'; then
  echo "negative control: sorryAx reported, as expected"
else
  echo "FAIL: negative control does NOT report sorryAx; the axiom check cannot be trusted"; status=1
fi

if [ "$status" -eq 0 ]; then echo "check_axioms.sh: PASS"; else echo "check_axioms.sh: FAIL"; fi
exit "$status"
