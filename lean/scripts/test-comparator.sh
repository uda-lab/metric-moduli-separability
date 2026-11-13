#!/usr/bin/env bash
# Stub regression tests for the Comparator wrapper's fail-closed behavior and exit handling.
# These tests do not exercise Comparator's Lean statement/axiom semantics (see
# scripts/test-comparator-semantics.sh for that). Scoped to this repository's contract: ported
# from uda-lab/lean-formalization-scaffold `main` (scripts/test-comparator.sh, de6fb66), with the
# rename-project.sh and lakefile.toml srcDir edge cases dropped as out of scope for this pilot
# (ruling 4 on issue #139) — kept short rather than imitating every scaffold case.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

repo="$tmp/repo"
mkdir -p "$repo/scripts/lib" "$repo/IshikiConj51/Ext" "$repo/ComparatorChallenge" "$tmp/home/.elan/bin"
cp scripts/check-comparator.sh "$repo/scripts/"
cp scripts/lib/build-lock.sh "$repo/scripts/lib/"
cp scripts/lean-code-scan.awk "$repo/scripts/"
cp comparator.json lake-manifest.json lakefile.toml lean-toolchain "$repo/"
printf 'import IshikiConj51.Ext.BMetClopen\n' > "$repo/IshikiConj51.lean"
printf 'theorem stub : True := trivial\n' > "$repo/IshikiConj51/Ext/BMetClopen.lean"
cp ComparatorChallenge.lean "$repo/"
printf 'import Mathlib.Data.Real.Basic\n\ntheorem referenceStub : True := trivial\n' \
  > "$repo/ComparatorChallenge/Reference.lean"

make_bin() {
  local dir="$1" have_lake="$2" have_bwrap="$3" tool source
  mkdir -p "$dir"
  for tool in jq awk find sed head dirname readlink flock; do
    source="$(command -v "$tool" 2>/dev/null || true)"
    [ -n "$source" ] || { echo "ERROR: test prerequisite '$tool' is unavailable." >&2; exit 1; }
    ln -s "$source" "$dir/$tool"
  done
  if [ "$have_bwrap" = yes ]; then
    printf '#!/bin/bash\nexit 0\n' > "$dir/bwrap"
    chmod +x "$dir/bwrap"
  fi
  if [ "$have_lake" = yes ]; then
    cat > "$dir/lake" <<'EOF'
#!/bin/bash
printf '%s\n' "$@" > "${COMPARATOR_TEST_LOG:?}"
printf '%s\n' "${COMPARATOR_TEST_MESSAGE:-stub Comparator result}" >&2
exit "${COMPARATOR_TEST_STATUS:-0}"
EOF
    chmod +x "$dir/lake"
  fi
}

all_bin="$tmp/bin-all"
no_bwrap_bin="$tmp/bin-no-bwrap"
no_lake_bin="$tmp/bin-no-lake"
no_jq_bin="$tmp/bin-no-jq"
no_awk_bin="$tmp/bin-no-awk"
no_find_bin="$tmp/bin-no-find"
make_bin "$all_bin" yes yes
make_bin "$no_bwrap_bin" yes no
make_bin "$no_lake_bin" no yes
make_bin "$no_jq_bin" yes yes
make_bin "$no_awk_bin" yes yes
make_bin "$no_find_bin" yes yes
rm "$no_jq_bin/jq"
rm "$no_awk_bin/awk"
rm "$no_find_bin/find"

failures=0
cases=0
run_case() {
  local name="$1" want_status="$2" want_text="$3" want_call="$4" path="$5"
  local lake_status="${6:-0}" lake_message="${7:-stub Comparator result}" override="${8:-}"
  local argument="${9:-}"
  local output status
  local log="$tmp/lake-args"
  local args=()
  [ -n "$argument" ] && args=("$argument")
  rm -f "$log"
  if [ -n "$override" ]; then
    set +e
    output="$(env HOME="$tmp/home" PATH="$path" \
      COMPARATOR_TEST_LOG="$log" COMPARATOR_TEST_STATUS="$lake_status" \
      COMPARATOR_TEST_MESSAGE="$lake_message" COMPARATOR_BWRAP="$override" \
      /bin/bash "$repo/scripts/check-comparator.sh" "${args[@]}" 2>&1)"
    status=$?
    set -e
  else
    set +e
    output="$(env -u COMPARATOR_BWRAP HOME="$tmp/home" PATH="$path" \
      COMPARATOR_TEST_LOG="$log" COMPARATOR_TEST_STATUS="$lake_status" \
      COMPARATOR_TEST_MESSAGE="$lake_message" \
      /bin/bash "$repo/scripts/check-comparator.sh" "${args[@]}" 2>&1)"
    status=$?
    set -e
  fi
  cases=$((cases + 1))
  if [ "$status" -ne "$want_status" ] || [[ "$output" != *"$want_text"* ]]; then
    printf 'FAIL [%s]: expected exit %s and text %q; got exit %s: %s\n' \
      "$name" "$want_status" "$want_text" "$status" "$output" >&2
    failures=$((failures + 1))
  fi
  if [ "$want_call" = yes ]; then
    if [ ! -s "$log" ] || ! grep -Fxq 'comparator' "$log" \
      || ! grep -Fxq -- '--config' "$log" \
      || ! grep -Fxq "$repo/comparator.json" "$log" \
      || grep -Fq -- '--inadvisably-no-sandbox' "$log"; then
      printf 'FAIL [%s]: expected only the sandboxed lake comparator --config invocation; args: ' "$name" >&2
      cat "$log" >&2 2>/dev/null || true
      failures=$((failures + 1))
    fi
  elif [ -e "$log" ]; then
    printf 'FAIL [%s]: lake was invoked before the prerequisite/config check failed.\n' "$name" >&2
    failures=$((failures + 1))
  fi
}

run_case accepted 0 'stub Comparator result' yes "$all_bin" 0
run_case rejected 1 'stub Comparator rejection' yes "$all_bin" 1 'stub Comparator rejection'
run_case cannot_start 2 'stub Comparator cannot start' yes "$all_bin" 2 'stub Comparator cannot start'
run_case unexpected_status 2 'unexpected exit status 23' yes "$all_bin" 23 'stub unexpected status'
run_case missing_bwrap 2 'bubblewrap (bwrap) is unavailable' no "$no_bwrap_bin"
run_case missing_lake 2 'lake is unavailable' no "$no_lake_bin"
run_case missing_jq 2 'jq is required' no "$no_jq_bin"
run_case missing_awk 2 'awk is required' no "$no_awk_bin"
run_case missing_find 2 'find is required' no "$no_find_bin"
cp "$all_bin/bwrap" "$tmp/bwrap.success"
cat > "$all_bin/bwrap" <<'EOF'
#!/bin/bash
echo 'user namespace is unavailable' >&2
exit 1
EOF
chmod +x "$all_bin/bwrap"
run_case unsupported_bwrap_namespace 2 'bubblewrap sandbox startup probe failed' no "$all_bin"
cp "$tmp/bwrap.success" "$all_bin/bwrap"
run_case wrong_bwrap_override 2 'refusing a sandbox override' no "$all_bin" 0 'must not run' "$tmp/other-bwrap"
run_case sandbox_bypass_argument_rejected 2 'refusing sandbox bypass' no "$all_bin" 0 'must not run' '' '--inadvisably-no-sandbox'
run_case extra_argument_rejected 2 'refusing sandbox bypass' no "$all_bin" 0 'must not run' '' '--any-other-argument'

cp "$repo/IshikiConj51.lean" "$tmp/IshikiConj51.lean.saved"
printf '\nimport ComparatorChallenge.Reference\n' >> "$repo/IshikiConj51.lean"
run_case production_root_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/IshikiConj51.lean.saved" "$repo/IshikiConj51.lean"
cp "$repo/IshikiConj51/Ext/BMetClopen.lean" "$tmp/BMetClopen.lean.saved"
printf '\nimport ComparatorChallenge.Reference\n' >> "$repo/IshikiConj51/Ext/BMetClopen.lean"
run_case production_module_import_rejected 2 'must not import ComparatorChallenge' no "$all_bin"
cp "$tmp/BMetClopen.lean.saved" "$repo/IshikiConj51/Ext/BMetClopen.lean"

cp "$repo/ComparatorChallenge/Reference.lean" "$tmp/Reference.lean.saved"
printf '\nimport IshikiConj51.Ext.BMetClopen\n' >> "$repo/ComparatorChallenge/Reference.lean"
run_case challenge_reference_production_import_rejected 2 'ComparatorChallenge modules must not import IshikiConj51' no "$all_bin"
cp "$tmp/Reference.lean.saved" "$repo/ComparatorChallenge/Reference.lean"

cp "$repo/comparator.json" "$tmp/comparator.json.saved"
: > "$repo/comparator.json"
run_case empty_config 2 'comparator.json is missing or empty' no "$all_bin"
printf '{\n' > "$repo/comparator.json"
run_case malformed_config 2 'differs from the frozen pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

jq '.definition_names = ["IshikiExt.someDefinition"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case definition_hole_rejected 2 'differs from the frozen pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"
jq '.permitted_axioms += ["Fake.CustomAxiom"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case axiom_allowlist_expansion_rejected 2 'differs from the frozen pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"
jq '.theorem_names = ["IshikiExt.someOtherTheorem"]' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case theorem_name_drift_rejected 2 'differs from the frozen pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"
jq '.solution_module = "IshikiConj51.Ext.OtherModule"' "$repo/comparator.json" > "$tmp/config.json"
mv "$tmp/config.json" "$repo/comparator.json"
run_case solution_module_drift_rejected 2 'differs from the frozen pilot contract' no "$all_bin"
cp "$tmp/comparator.json.saved" "$repo/comparator.json"

mv "$repo/lake-manifest.json" "$tmp/lake-manifest.json.saved"
run_case missing_manifest 2 'lake-manifest.json is missing or empty' no "$all_bin"
mv "$tmp/lake-manifest.json.saved" "$repo/lake-manifest.json"
mv "$repo/lean-toolchain" "$tmp/lean-toolchain.saved"
run_case missing_toolchain_pin 2 'lean-toolchain is missing or empty' no "$all_bin"
mv "$tmp/lean-toolchain.saved" "$repo/lean-toolchain"
mv "$repo/scripts/lib/build-lock.sh" "$tmp/build-lock.sh.saved"
run_case missing_build_lock 2 'scripts/lib/build-lock.sh is missing or unreadable' no "$all_bin"
mv "$tmp/build-lock.sh.saved" "$repo/scripts/lib/build-lock.sh"

if [ "$failures" -eq 0 ]; then
  printf 'Comparator wrapper stub self-test OK (%s cases; semantic Comparator checks not run).\n' "$cases"
else
  exit 1
fi
