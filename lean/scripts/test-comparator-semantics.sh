#!/usr/bin/env bash
# Real-Comparator semantic regressions for the issue #139 pilot, run directly against
# `lake comparator` (not through scripts/check-comparator.sh, whose own frozen-contract
# validation is covered by scripts/test-comparator.sh). Ported from
# uda-lab/lean-formalization-scaffold `main` (scripts/test-comparator-semantics.sh, de6fb66).
#
# Builds one temporary Lean project per run (never a tracked challenge/solution variant, so
# nothing here touches the tracked tree), hardlinking this project's already built
# `.lake/packages` so mathlib is reused rather than rebuilt. Every Lean/Lake invocation holds
# the shared build lock for the lifetime of this script.
#
# Exercises the documented outcomes of `lake comparator` (EXIT CODES in `lake help comparator`):
#   accepted (0, run cold and then repeated); a changed theorem statement, a changed definition
#   an in-scope theorem depends on, a solution using a forbidden axiom, a solution closed by
#   `sorry`, and a solution that fails to build (each 1, "rejected"); a missing, empty,
#   malformed, or required-field-missing `comparator.json` (each 2, "could not start").
#   `--paranoid` is never passed: this suite checks Lean's own kernel verdict, not the bundled
#   external checkers.
#
# Fail-closed design: `lake comparator` cannot tell a broken sandbox from an ordinary rejection
# once it starts spawning `bwrap` (both come back as exit 1), so every sandbox-dependent case
# above would misreport against a sandbox that cannot actually start. Lake validates the config
# file before it ever touches the sandbox, so the four could-not-start config cases run
# unconditionally, each asserted against its actual diagnostic text. The sandbox-dependent cases
# are gated behind a probe of the namespace capability Comparator needs, run strictly before any
# of them; if the probe fails, this script prints the diagnostic and exits 2 itself, without
# claiming any sandbox-dependent case passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

die() {
  printf 'ERROR: %s\n' "$1" >&2
  exit 2
}

command -v lake >/dev/null 2>&1 || die "lake is unavailable; install/use the repository's pinned Lean toolchain."
command -v jq >/dev/null 2>&1 || die "jq is required to generate fixture Comparator configs."
bwrap_path="$(command -v bwrap 2>/dev/null || true)"
[ -n "$bwrap_path" ] || die "bubblewrap (bwrap) is unavailable; refusing to run Comparator without its sandbox."

# Serialize with the canonical lock: fixture builds and the sandboxed Comparator below both run
# the pinned Lean toolchain.
[ -r "$ROOT/scripts/lib/build-lock.sh" ] || die "scripts/lib/build-lock.sh is missing or unreadable."
. "$ROOT/scripts/lib/build-lock.sh"

# Under $ROOT/.lake (gitignored, never written into the repository tree as a tracked path) so
# this lands on the same filesystem/device as $ROOT/.lake/packages: a plain `mktemp -d` honours
# $TMPDIR, which some harnesses point at a different device, and `cp -al` below cannot hardlink
# across devices.
mkdir -p "$ROOT/.lake"
tmp="$(mktemp -d -p "$ROOT/.lake" comparator-semantics-test.XXXXXX)"
trap 'rm -rf "$tmp"' EXIT
proj="$tmp/project"
fixtures="$tmp/fixtures"
mkdir -p "$proj" "$fixtures"

echo "==> generating fixtures in $proj (untracked; never written into the repository tree)"

cp "$ROOT/lakefile.toml" "$ROOT/lake-manifest.json" "$ROOT/lean-toolchain" "$proj/"
cp "$ROOT/IshikiConj51.lean" "$proj/"
cp -R "$ROOT/IshikiConj51" "$proj/"
cp "$ROOT/ComparatorChallenge.lean" "$proj/"
cp -R "$ROOT/ComparatorChallenge" "$proj/"
mkdir -p "$proj/.lake"
cp -al "$ROOT/.lake/packages" "$proj/.lake/packages"

# Fixture pairs live in their own tiny namespace, independent of the frozen target
# (IshikiExt.isClopen_setOf_edist_lt_top), which these fixtures never touch.
write_pair() {
  local case_name="$1" challenge_body="$2" solution_body="$3"
  printf 'import Mathlib.Data.Real.Basic\n\nnamespace ComparatorPilotFixture\n\n%s\n\nend ComparatorPilotFixture\n' \
    "$challenge_body" > "$proj/ComparatorChallenge/Case$case_name.lean"
  printf 'import Mathlib.Data.Real.Basic\n\nnamespace ComparatorPilotFixture\n\n%s\n\nend ComparatorPilotFixture\n' \
    "$solution_body" > "$proj/IshikiConj51/Case$case_name.lean"
}

write_pair Statement \
  'theorem statement_demo (x : ℝ) : x + 0 = x := add_zero x' \
  'theorem statement_demo (x : ℝ) : 0 + x = x := zero_add x'

write_pair Definition \
  'def helperConst : ℝ := 0

theorem definition_demo (x : ℝ) (_h : helperConst = helperConst) : x + 0 = x := add_zero x' \
  'def helperConst : ℝ := 1

theorem definition_demo (x : ℝ) (_h : helperConst = helperConst) : x + 0 = x := add_zero x'

write_pair Axiom \
  'theorem axiom_demo (x : ℝ) : x + 0 = x := add_zero x' \
  'axiom forbiddenAxiom : True

theorem axiom_demo (x : ℝ) : x + 0 = x := by
  have _ := forbiddenAxiom
  exact add_zero x'

write_pair Sorry \
  'theorem sorry_demo (x : ℝ) : x + 0 = x := add_zero x' \
  'theorem sorry_demo (x : ℝ) : x + 0 = x := by sorry'

write_pair BuildFail \
  'theorem build_fail_demo (x : ℝ) : x + 0 = x := add_zero x' \
  'theorem build_fail_demo (x : ℝ) : x + 0 = x := add_zero'

standard_axioms='["propext", "Classical.choice", "Quot.sound"]'
write_config() {
  local name="$1" challenge_module="$2" solution_module="$3" theorem_names="$4"
  jq -n --arg cm "$challenge_module" --arg sm "$solution_module" \
    --argjson tn "$theorem_names" --argjson pa "$standard_axioms" \
    '{challenge_module: $cm, solution_module: $sm, theorem_names: $tn, definition_names: [], permitted_axioms: $pa}' \
    > "$fixtures/$name.json"
}

write_config accepted "ComparatorChallenge.Reference" "IshikiConj51.Ext.BMetClopen" \
  '["IshikiExt.isClopen_setOf_edist_lt_top"]'
write_config statement_mismatch "ComparatorChallenge.CaseStatement" "IshikiConj51.CaseStatement" \
  '["ComparatorPilotFixture.statement_demo"]'
write_config definition_mismatch "ComparatorChallenge.CaseDefinition" "IshikiConj51.CaseDefinition" \
  '["ComparatorPilotFixture.definition_demo"]'
write_config forbidden_axiom "ComparatorChallenge.CaseAxiom" "IshikiConj51.CaseAxiom" \
  '["ComparatorPilotFixture.axiom_demo"]'
write_config sorry_closed "ComparatorChallenge.CaseSorry" "IshikiConj51.CaseSorry" \
  '["ComparatorPilotFixture.sorry_demo"]'
write_config build_failure "ComparatorChallenge.CaseBuildFail" "IshikiConj51.CaseBuildFail" \
  '["ComparatorPilotFixture.build_fail_demo"]'

: > "$fixtures/empty_config.json"
printf '{ "challenge_module": "ComparatorChallenge.Reference",\n' > "$fixtures/malformed_config.json"
jq 'del(.permitted_axioms)' "$fixtures/accepted.json" > "$fixtures/missing_field_config.json"

echo "==> plain (unsandboxed) build of every fixture under the shared lock"
failures=0
cases=0

assert_build() {
  local label="$1" module="$2" want_ok="$3" output status
  cases=$((cases + 1))
  set +e
  output="$(cd "$proj" && lake build "$module" 2>&1)"
  status=$?
  set -e
  if [ "$want_ok" = yes ] && [ "$status" -ne 0 ]; then
    printf 'FAIL [%s]: expected %s to build; got exit %s: %s\n' "$label" "$module" "$status" "$output" >&2
    failures=$((failures + 1))
  elif [ "$want_ok" = no ] && [ "$status" -eq 0 ]; then
    printf 'FAIL [%s]: expected %s to fail to build, but it built.\n' "$label" "$module" >&2
    failures=$((failures + 1))
  fi
}

for pair in \
  "statement:ComparatorChallenge.CaseStatement:IshikiConj51.CaseStatement" \
  "definition:ComparatorChallenge.CaseDefinition:IshikiConj51.CaseDefinition" \
  "axiom:ComparatorChallenge.CaseAxiom:IshikiConj51.CaseAxiom" \
  "sorry:ComparatorChallenge.CaseSorry:IshikiConj51.CaseSorry"; do
  IFS=: read -r label challenge_mod solution_mod <<< "$pair"
  assert_build "$label challenge" "$challenge_mod" yes
  assert_build "$label solution" "$solution_mod" yes
done
assert_build "build_failure challenge" "ComparatorChallenge.CaseBuildFail" yes
assert_build "build_failure solution" "IshikiConj51.CaseBuildFail" no

run_comparator() {
  local label="$1" config_path="$2" want_status="$3" want_text="${4:-}" output status
  cases=$((cases + 1))
  set +e
  output="$(cd "$proj" && env -u COMPARATOR_BWRAP lake comparator --config "$config_path" 2>&1)"
  status=$?
  set -e
  if [ "$status" -ne "$want_status" ] || { [ -n "$want_text" ] && [[ "$output" != *"$want_text"* ]]; }; then
    printf 'FAIL [%s]: expected exit %s and text %q; got exit %s: %s\n' \
      "$label" "$want_status" "$want_text" "$status" "$output" >&2
    failures=$((failures + 1))
  fi
}

echo "==> could-not-start config cases (Lake validates the config before touching the sandbox)"
run_comparator "missing config" "$fixtures/missing_config.json" 2 'could not read the configuration'
run_comparator "empty config" "$fixtures/empty_config.json" 2 'malformed configuration'
run_comparator "malformed config" "$fixtures/malformed_config.json" 2 'malformed configuration'
run_comparator "config missing required field" "$fixtures/missing_field_config.json" 2 'malformed configuration'

echo "==> probing the exact mount sequence lake comparator performs before anything else"
if ! sandbox_probe_output="$(bwrap --unshare-all --ro-bind / / \
  --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp \
  --proc /proc --dev /dev --die-with-parent --new-session true 2>&1)"; then
  echo "ERROR: bubblewrap sandbox startup probe failed; the real Comparator semantic" >&2
  echo "       regressions below cannot run in this environment (recreate the container with" >&2
  echo "       --security-opt=systempaths=unconfined / an unmasked /proc, and ensure a real" >&2
  echo "       /run/user directory exists for bwrap to mount tmpfs over)." >&2
  [ -z "$sandbox_probe_output" ] || printf '%s\n' "$sandbox_probe_output" >&2
  if [ "$failures" -eq 0 ]; then
    printf 'Fixture generation, plain build and the 4 could-not-start config cases OK (%s cases); the 7 sandbox-dependent cases NOT exercised.\n' "$cases" >&2
  else
    printf '%s of %s case(s) run so far FAILED; the 7 sandbox-dependent cases NOT exercised either.\n' "$failures" "$cases" >&2
  fi
  exit 2
fi
echo "bubblewrap namespace capability probe OK"

echo "==> real Comparator: accepted baseline (cold, then repeated)"
cases=$((cases + 1))
cold_start="$(date +%s.%N)"
set +e
cold_output="$(cd "$proj" && env -u COMPARATOR_BWRAP lake comparator --config "$fixtures/accepted.json" 2>&1)"
cold_status=$?
set -e
cold_end="$(date +%s.%N)"
if [ "$cold_status" -ne 0 ]; then
  printf 'FAIL [accepted cold]: expected exit 0; got exit %s: %s\n' "$cold_status" "$cold_output" >&2
  failures=$((failures + 1))
fi
repeat_start="$(date +%s.%N)"
set +e
repeat_output="$(cd "$proj" && env -u COMPARATOR_BWRAP lake comparator --config "$fixtures/accepted.json" 2>&1)"
repeat_status=$?
set -e
repeat_end="$(date +%s.%N)"
cases=$((cases + 1))
if [ "$repeat_status" -ne 0 ]; then
  printf 'FAIL [accepted repeated]: expected exit 0; got exit %s: %s\n' "$repeat_status" "$repeat_output" >&2
  failures=$((failures + 1))
fi
awk -v c0="$cold_start" -v c1="$cold_end" -v r0="$repeat_start" -v r1="$repeat_end" \
  'BEGIN { printf "accepted baseline wall time: cold %.3fs, repeated %.3fs\n", c1 - c0, r1 - r0 }'

run_comparator "statement mismatch" "$fixtures/statement_mismatch.json" 1 'theorem statement do not match'
run_comparator "definition mismatch" "$fixtures/definition_mismatch.json" 1 'Const does not match'
run_comparator "forbidden axiom" "$fixtures/forbidden_axiom.json" 1 "Illegal axiom detected: 'ComparatorPilotFixture.forbiddenAxiom'"
run_comparator "sorry-closed solution" "$fixtures/sorry_closed.json" 1 "Illegal axiom detected: 'sorryAx'"
run_comparator "build failure" "$fixtures/build_failure.json" 1 'build failed'

if [ "$failures" -eq 0 ]; then
  printf 'Comparator semantic regression suite OK (%s cases).\n' "$cases"
else
  printf '%s of %s case(s) FAILED.\n' "$failures" "$cases" >&2
  exit 1
fi
