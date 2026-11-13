#!/usr/bin/env bash
# Fail-closed standalone Comparator wrapper for the issue #139 pilot contract. Optional and
# manual: this repository has no `scripts/check.sh` gate and no CI, and none is added. Ported
# from uda-lab/lean-formalization-scaffold `main` (scripts/check-comparator.sh, de6fb66), reduced
# to what this repository has: there is no pinned-theorem inventory
# (`scripts/print_axioms.lean`) here, so the scaffold wrapper's pinned-subset validation is
# dropped rather than imitated, and the frozen config is checked for an exact fixed shape
# instead. The scaffold's `solution_module` doubled as the production library name; this
# contract's `solution_module` is the *defining module* of the one frozen theorem
# (`IshikiConj51.Ext.BMetClopen`), not the library root (`IshikiConj51`), to bound export cost
# (ruling 3 on issue #139) — so the production-import boundary below is checked against the
# production library name read from `lakefile.toml`, not against `solution_module`.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

die() {
  printf 'ERROR: %s\n' "$1" >&2
  exit 2
}

[ "$#" -eq 0 ] || die "this wrapper accepts no command-line overrides; refusing sandbox bypass and externally supplied exports."

CONFIG="$ROOT/comparator.json"

# Comparator resolves dependencies inside its bubblewrap sandbox and cannot write a missing
# manifest back into the project. It also needs the repository's selected Lean toolchain.
[ -s "$ROOT/lean-toolchain" ] || die "lean-toolchain is missing or empty."
[ -s "$ROOT/lake-manifest.json" ] || die "lake-manifest.json is missing or empty; run the existing pinned build first."
[ -s "$CONFIG" ] || die "comparator.json is missing or empty."
command -v jq >/dev/null 2>&1 || die "jq is required to validate the frozen Comparator config."
command -v awk >/dev/null 2>&1 || die "awk is required to verify the production/reference import boundary."
command -v find >/dev/null 2>&1 || die "find is required to enumerate project Lean modules."

# The frozen pilot contract (issue #139 ruling 3): exact keys, exact values. Any drift — an
# unexpected field, a different module or theorem name, a non-empty definition_names, or an
# axiom-allowlist change — is a configuration error, not a request to proceed. There is no
# pinned-theorem inventory in this repository to check theorem_names against, unlike the
# scaffold's pinned-subset rule.
if ! jq -e '
  type == "object" and
  (keys | sort) == ["challenge_module", "definition_names", "permitted_axioms", "solution_module", "theorem_names"] and
  .challenge_module == "ComparatorChallenge.Reference" and
  .solution_module == "IshikiConj51.Ext.BMetClopen" and
  .theorem_names == ["IshikiExt.isClopen_setOf_edist_lt_top"] and
  .definition_names == [] and
  .permitted_axioms == ["propext", "Classical.choice", "Quot.sound"]
' "$CONFIG" >/dev/null 2>&1; then
  die "comparator.json is malformed or differs from the frozen pilot contract."
fi

# Keep the independently authored challenge and the production library on separate import
# boundaries in both directions. Challenge sources may import other challenge modules or package
# dependencies, but not another project-local module: that rule closes transitive bridges through
# auxiliary source files as well as direct imports. The production library name comes from
# lakefile.toml's package name, not from comparator.json's solution_module (see header note).
if ! production_module="$(sed -nE 's/^name[[:space:]]*=[[:space:]]*"([^"]*)"[[:space:]]*$/\1/p' "$ROOT/lakefile.toml" | head -n1)" \
  || [ -z "$production_module" ]; then
  die "could not read the production library name from lakefile.toml."
fi
solution_module="$(jq -r '.solution_module' "$CONFIG")"
solution_rel="${solution_module//./\/}"
[ -f "$ROOT/$solution_rel.lean" ] && [ ! -L "$ROOT/$solution_rel.lean" ] \
  || die "the solution module $solution_module ($solution_rel.lean) is missing, unreadable, or symlinked."
[ -f "$ROOT/$production_module.lean" ] && [ -d "$ROOT/$production_module" ] \
  || die "the production $production_module library root is missing or unreadable."
[ -f "$ROOT/ComparatorChallenge.lean" ] && [ -d "$ROOT/ComparatorChallenge" ] \
  || die "the ComparatorChallenge library root is missing or unreadable."
[ ! -L "$ROOT/$production_module.lean" ] && [ ! -L "$ROOT/$production_module" ] \
  || die "the production $production_module roots must not be symlinks."
[ ! -L "$ROOT/ComparatorChallenge.lean" ] && [ ! -L "$ROOT/ComparatorChallenge" ] \
  || die "the ComparatorChallenge roots must not be symlinks."

# Ignore only repository metadata, local build output, and local agent guidance. A symlinked
# source file or directory could otherwise hide an import from the file enumeration below.
if ! project_symlinks="$(find "$ROOT" \
  \( -path "$ROOT/.git" -o -path "$ROOT/.lake" -o -path "$ROOT/.agents" \
     -o -path "$ROOT/.claude" -o -path "$ROOT/.codex" -o -path "$ROOT/.github" \) -prune \
  -o -type l -print 2>&1)"; then
  die "could not check project Lean sources for symlinks: $project_symlinks"
fi
while IFS= read -r link; do
  [ -n "$link" ] || continue
  if [[ "$link" == *.lean ]] || [ -d "$link" ]; then
    die "project Lean sources must not be hidden behind symlinks: $link"
  fi
done <<< "$project_symlinks"

if ! project_sources="$(find "$ROOT" \
  \( -path "$ROOT/.git" -o -path "$ROOT/.lake" -o -path "$ROOT/.agents" \
     -o -path "$ROOT/.claude" -o -path "$ROOT/.codex" -o -path "$ROOT/.github" \) -prune \
  -o -type f -name '*.lean' -print 2>&1)"; then
  die "could not enumerate project Lean modules: $project_sources"
fi
[ -n "$project_sources" ] || die "the project has no Lean source files."
production_source_count=0
challenge_source_count=0
while IFS= read -r source; do
  [ -n "$source" ] || continue
  case "$source" in
    "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*)
      forbidden_target="$production_module"
      challenge_source_count=$((challenge_source_count + 1))
      boundary_description="ComparatorChallenge modules must not import $production_module"
      ;;
    *)
      forbidden_target=ComparatorChallenge
      production_source_count=$((production_source_count + 1))
      boundary_description="project production and auxiliary modules must not import ComparatorChallenge"
      ;;
  esac
  if ! boundary_output="$(LC_ALL=C awk -v mode=import -v import_target="$forbidden_target" \
    -f "$ROOT/scripts/lean-code-scan.awk" "$source")"; then
    die "could not inspect import boundary in $source."
  fi
  [ -z "$boundary_output" ] || die "$boundary_description: $boundary_output"
done <<< "$project_sources"
[ "$production_source_count" -gt 0 ] \
  || die "the production project has no Lean source files to boundary-check."
[ "$challenge_source_count" -gt 0 ] \
  || die "the ComparatorChallenge library has no Lean source files to boundary-check."

# A challenge could otherwise import a local helper that imports the production library, even
# though neither edge directly crosses the library boundary. Treat every project source outside
# ComparatorChallenge as a forbidden local dependency of challenge modules. Include configured
# source roots so modules under a Lake srcDir receive their actual import names as well as their
# repository-relative names.
declare -a project_source_roots=("$ROOT")
project_root_real="$(cd "$ROOT" && pwd -P)" \
  || die "could not resolve the project root while checking Lean source directories."
if ! configured_source_dirs="$(awk '
  BEGIN { single_quote = sprintf("%c", 39); in_table = 0 }
  {
    line = $0
    sub(/^[[:space:]]*/, "", line)
    if (line == "" || line ~ /^#/) next
    if (line ~ /^\[/) { in_table = 1; next }
    equals = index(line, "=")
    if (equals == 0) next
    key = substr(line, 1, equals - 1)
    if (key ~ /["\047]/) {
      print "quoted TOML keys are unsupported for fail-closed srcDir discovery." > "/dev/stderr"
      exit 2
    }
    if (key !~ /^srcDir[[:space:]]*$/) {
      if (key ~ /(^|[.])srcDir([.]|[[:space:]]*$)/ || index(line, "srcDir") > 0) {
        print "unsupported srcDir syntax in lakefile.toml." > "/dev/stderr"
        exit 2
      }
      next
    }
    if (in_table) {
      print "table-scoped srcDir values are unsupported for fail-closed discovery." > "/dev/stderr"
      exit 2
    }
    sub(/^srcDir[[:space:]]*=[[:space:]]*/, "", line)
    quote = substr(line, 1, 1)
    if (quote != "\"" && quote != single_quote) {
      print "unsupported srcDir value in lakefile.toml; expected a simple quoted path." > "/dev/stderr"
      exit 2
    }
    rest = substr(line, 2)
    close_at = index(rest, quote)
    if (close_at == 0) {
      print "unterminated srcDir value in lakefile.toml." > "/dev/stderr"
      exit 2
    }
    value = substr(rest, 1, close_at - 1)
    suffix = substr(rest, close_at + 1)
    if (quote == "\"" && value ~ /\\/) {
      print "escaped double-quoted srcDir paths are unsupported for fail-closed discovery." > "/dev/stderr"
      exit 2
    }
    sub(/^[[:space:]]*/, "", suffix)
    if (value == "" || (suffix != "" && suffix !~ /^#/)) {
      print "unsupported srcDir value in lakefile.toml; expected a simple quoted path." > "/dev/stderr"
      exit 2
    }
    print value
  }
' "$ROOT/lakefile.toml" 2>&1)"; then
  die "could not read configured Lean source directories from lakefile.toml: $configured_source_dirs"
fi
while IFS= read -r source_dir; do
  [ -n "$source_dir" ] || continue
  if [[ "$source_dir" == /* ]]; then
    source_root_candidate="$source_dir"
  else
    source_root_candidate="$ROOT/$source_dir"
  fi
  source_root_real="$(cd "$source_root_candidate" 2>/dev/null && pwd -P)" \
    || die "configured Lean source directory is missing or unreadable: $source_dir"
  case "$source_root_real/" in
    "$project_root_real/"*) ;;
    *) die "configured Lean source directory is outside the project tree: $source_dir" ;;
  esac
  relative_source_root="${source_root_real#"$project_root_real"/}"
  case "$relative_source_root" in
    .git|.git/*|.lake|.lake/*|.agents|.agents/*|.claude|.claude/*|.codex|.codex/*|.github|.github/*)
      die "configured Lean source directory overlaps an excluded project path: $source_dir"
      ;;
  esac
  project_source_roots+=("$source_root_real")
done <<< "$configured_source_dirs"
declare -a project_module_names=()
declare -a project_module_sources=()
while IFS= read -r source; do
  [ -n "$source" ] || continue
  for source_root in "${project_source_roots[@]}"; do
    case "$source" in
      "$source_root"/*)
        relative_source="${source#"$source_root"/}"
        [[ "$relative_source" != *[[:space:]]* ]] \
          || die "project Lean module paths with whitespace cannot be checked safely: $source"
        module_name="${relative_source%.lean}"
        module_name="${module_name//\//.}"
        if [ -n "$module_name" ]; then
          project_module_names+=("$module_name")
          project_module_sources+=("$source")
        fi
        ;;
    esac
  done
done <<< "$project_sources"
while IFS= read -r source; do
  [ -n "$source" ] || continue
  case "$source" in
    "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*) ;;
    *) continue ;;
  esac
  if ! imported_modules="$(LC_ALL=C awk -v mode=imports -f "$ROOT/scripts/lean-code-scan.awk" "$source")"; then
    die "could not enumerate imports in ComparatorChallenge source $source."
  fi
  while IFS= read -r imported_module; do
    [ -n "$imported_module" ] || continue
    for index in "${!project_module_names[@]}"; do
      [ "${project_module_names[$index]}" = "$imported_module" ] || continue
      candidate_source="${project_module_sources[$index]}"
      case "$candidate_source" in
        "$ROOT/ComparatorChallenge.lean"|"$ROOT/ComparatorChallenge/"*) continue ;;
      esac
      die "ComparatorChallenge modules must not import project-local modules outside ComparatorChallenge: $source imports $imported_module from $candidate_source"
    done
  done <<< "$imported_modules"
done <<< "$project_sources"

bwrap_path="$(command -v bwrap 2>/dev/null || true)"
[ -n "$bwrap_path" ] || die "bubblewrap (bwrap) is unavailable; refusing to run Comparator without its sandbox."
if [[ ${COMPARATOR_BWRAP+x} ]]; then
  [ -n "$COMPARATOR_BWRAP" ] || die "COMPARATOR_BWRAP is set but empty; unset it or name the default bwrap executable."
  if [[ "$COMPARATOR_BWRAP" != "bwrap" && "$COMPARATOR_BWRAP" != "$bwrap_path" ]]; then
    die "COMPARATOR_BWRAP must resolve to the default bwrap executable; refusing a sandbox override."
  fi
fi

# Probe the exact mount sequence `lake comparator` always performs before anything else
# (Lake/CLI/Check.lean's buildSandboxArgs: --unshare-all, then --ro-bind / /, then --tmpfs
# over /home, /root, /run/user and /tmp). A container can satisfy plain namespace creation and
# an unmasked /proc yet still lack a real /run/user directory: bwrap mounts tmpfs only over an
# existing mountpoint, and the preceding --ro-bind makes the whole tree read-only before it gets
# there, so a missing /run/user fails with "Can't mkdir /run/user: Read-only file system" deep
# inside Comparator's first sandboxed step. Report any such startup failure as exit 2 here,
# rather than letting Comparator's own ordinary rejection/build status (also exit 1) mask it.
if ! sandbox_probe_output="$(bwrap --unshare-all --ro-bind / / \
  --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp \
  --proc /proc --dev /dev --die-with-parent --new-session /bin/true 2>&1)"; then
  printf 'ERROR: bubblewrap sandbox startup probe failed; refusing to run Comparator without its full sandbox.\n' >&2
  [ -z "$sandbox_probe_output" ] || printf '%s\n' "$sandbox_probe_output" >&2
  exit 2
fi

command -v lake >/dev/null 2>&1 || die "lake is unavailable; install/use the repository's pinned Lean toolchain."

# Serialize Comparator builds with the same container-wide lock as every other Lean build. No
# sandbox bypass, export override, or stale-export input is accepted by this wrapper.
[ -r "$ROOT/scripts/lib/build-lock.sh" ] || die "scripts/lib/build-lock.sh is missing or unreadable."
if ! . "$ROOT/scripts/lib/build-lock.sh"; then
  die "could not acquire the shared Lean build lock."
fi

if lake comparator --config "$CONFIG"; then
  exit 0
else
  status=$?
fi

case "$status" in
  1) exit 1 ;; # Comparator rejection or build failure.
  2) exit 2 ;; # Comparator could not start (config, manifest, or sandbox prerequisite).
  *)
    printf 'ERROR: lake comparator returned unexpected exit status %s; refusing success.\n' "$status" >&2
    exit 2
    ;;
esac
