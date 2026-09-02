#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
NOTES_DIR="$SCRIPT_DIR/.."
OUTPUT_DIR="$NOTES_DIR/typeset"

if (( $# == 0 )); then
  notes=(
    borel-manuscript-20260827-audit.md
    borel-preprint-audit.md
    descriptive-set-theory-ja.md
    terminology.md
  )
else
  notes=("$@")
fi

mkdir -p -- "$OUTPUT_DIR"

TEMP_DIR=$(mktemp -d)
cleanup() {
  if [[ -n "${TEMP_DIR:-}" && -d "$TEMP_DIR" ]]; then
    rm -rf -- "$TEMP_DIR"
  fi
}
trap cleanup EXIT

default_fallback_fonts=$'STIXTwoMath-Regular:mode=node\nDejaVu Sans:mode=node\nApple Symbols:mode=node\nMenlo:mode=node'
fallback_spec="${TYPESET_FALLBACK_FONTS-$default_fallback_fonts}"

if [[ "$fallback_spec" == *';' || "$fallback_spec" == *$'\n' ]]; then
  printf '%s\n' "error: TYPESET_FALLBACK_FONTS must not have a trailing separator" >&2
  exit 1
fi

configured_fallbacks=()
while IFS= read -r entry || [[ -n "$entry" ]]; do
  if [[ -z "$entry" ]]; then
    printf '%s\n' "error: TYPESET_FALLBACK_FONTS contains an empty entry" >&2
    exit 1
  fi
  configured_fallbacks+=("$entry")
done < <(printf '%s' "$fallback_spec" | tr ';' '\n')

filtered_fallbacks=()
for entry in "${configured_fallbacks[@]}"; do
  if luaotfload-tool --find="$entry" 2>&1 | grep -q 'found!'; then
    filtered_fallbacks+=("$entry")
  fi
done

if (( ${#filtered_fallbacks[@]} == 0 )); then
  printf '%s\n' "error: no configured fallback font is available on this host; set TYPESET_FALLBACK_FONTS" >&2
  exit 1
fi

fallback_entries_lua="\"${filtered_fallbacks[0]}\""
for ((i = 1; i < ${#filtered_fallbacks[@]}; i++)); do
  fallback_entries_lua+=$',\n'
  fallback_entries_lua+="  \"${filtered_fallbacks[$i]}\""
done
math_font="${filtered_fallbacks[0]%%:*}"

render_header() {
  local header_file=$1
  local line

  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      *@@FALLBACK_ENTRIES@@*)
        printf '%s\n' "${line//@@FALLBACK_ENTRIES@@/$fallback_entries_lua}"
        ;;
      *@@MATH_FONT@@*)
        printf '%s\n' "${line//@@MATH_FONT@@/$math_font}"
        ;;
      *)
        printf '%s\n' "$line"
        ;;
    esac
  done < "$SCRIPT_DIR/glyph-fallback.tex" > "$header_file"
}

total_missing=0
failed_notes=0

process_note() {
  local note=$1
  local note_filename=${note##*/}
  local notename=${note_filename%.md}
  local source="$NOTES_DIR/$note"
  local temp_copy
  local header_file="$OUTPUT_DIR/${notename}-header.tex"
  local tex_file="$OUTPUT_DIR/${notename}.tex"
  local log_file="$OUTPUT_DIR/${notename}.log"
  local missing_count=0
  local latex_failed=0

  if [[ "$note" == */* || -z "$note" ]]; then
    printf 'error: note argument must be a bare filename relative to %s: %s\n' "$NOTES_DIR" "$note" >&2
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if [[ ! -f "$source" ]]; then
    printf 'error: note not found: %s\n' "$source" >&2
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if ! temp_copy=$(mktemp "$TEMP_DIR/source.XXXXXX"); then
    printf 'error: could not create temporary source copy: %s\n' "$source" >&2
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if ! sed 's/✅/✓/g' "$source" > "$temp_copy"; then
    printf 'error: could not prepare source note: %s\n' "$source" >&2
    if ! rm -f -- "$temp_copy"; then
      printf 'warning: could not remove temporary source copy: %s\n' "$temp_copy" >&2
    fi
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if ! render_header "$header_file"; then
    printf 'error: could not render fallback header: %s\n' "$header_file" >&2
    if ! rm -f -- "$temp_copy"; then
      printf 'warning: could not remove temporary source copy: %s\n' "$temp_copy" >&2
    fi
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if ! pandoc "$temp_copy" -s -f markdown+east_asian_line_breaks -V documentclass=ltjsarticle --include-in-header="$header_file" -o "$tex_file"; then
    printf 'error: pandoc failed for %s\n' "$note" >&2
    if ! rm -f -- "$temp_copy"; then
      printf 'warning: could not remove temporary source copy: %s\n' "$temp_copy" >&2
    fi
    failed_notes=$((failed_notes + 1))
    printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
    return
  fi

  if ! lualatex -interaction=nonstopmode -halt-on-error -output-directory="$OUTPUT_DIR" "$tex_file"; then
    printf 'error: lualatex failed for %s (pass 1)\n' "$note" >&2
    latex_failed=1
  fi
  if ! lualatex -interaction=nonstopmode -halt-on-error -output-directory="$OUTPUT_DIR" "$tex_file"; then
    printf 'error: lualatex failed for %s (pass 2)\n' "$note" >&2
    latex_failed=1
  fi

  if ! rm -f -- "$temp_copy"; then
    printf 'warning: could not remove temporary source copy: %s\n' "$temp_copy" >&2
  fi
  if [[ -f "$log_file" ]]; then
    missing_count=$(awk '/Missing character/ { count++ } END { print count + 0 }' "$log_file")
  else
    printf 'error: lualatex did not produce a log for %s\n' "$note" >&2
  fi

  total_missing=$((total_missing + missing_count))
  if (( latex_failed != 0 || missing_count != 0 )); then
    failed_notes=$((failed_notes + 1))
  fi
  printf '%s: %d missing character(s)\n' "$notename" "$missing_count"
}

for note in "${notes[@]}"; do
  process_note "$note"
done

printf 'typeset: %d note(s), %d missing character(s), %d failed note(s)\n' "${#notes[@]}" "$total_missing" "$failed_notes"
if (( failed_notes != 0 )); then
  exit 1
fi
