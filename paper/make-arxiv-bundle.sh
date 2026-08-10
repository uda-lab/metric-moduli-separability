#!/usr/bin/env bash
# Build a reproducible arXiv v1 source bundle for paper/main.tex.
#
# arXiv does not run BibTeX, so the bundle ships a pre-built main.bbl
# alongside main.tex; references.bib is intentionally excluded. The
# bundle is verified by extracting it into a clean directory and
# compiling with plain pdflatex (no latexmk, no .bib) twice.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PAPER_DIR="${SCRIPT_DIR}"
BUNDLE_NAME="arxiv-v1.tar.gz"
BUNDLE_PATH="${PAPER_DIR}/${BUNDLE_NAME}"
EXPECTED_PAGES=11

log() { printf '==> %s\n' "$1"; }

# ---------------------------------------------------------------------
# 1. Rebuild main.bbl freshly via latexmk in paper/.
# ---------------------------------------------------------------------
log "Rebuilding main.bbl with latexmk in ${PAPER_DIR}"
(
  cd "${PAPER_DIR}"
  latexmk -C main.tex
  latexmk -pdf -interaction=nonstopmode main.tex
)

if [[ ! -f "${PAPER_DIR}/main.bbl" ]]; then
  echo "ERROR: ${PAPER_DIR}/main.bbl was not produced by latexmk" >&2
  exit 1
fi

# ---------------------------------------------------------------------
# 2. Stage exactly main.tex and main.bbl into a temp dir.
# ---------------------------------------------------------------------
STAGE_DIR="$(mktemp -d)"
trap 'rm -rf "${STAGE_DIR}" "${VERIFY_DIR:-}"' EXIT

log "Staging bundle contents in ${STAGE_DIR}"
cp "${PAPER_DIR}/main.tex" "${STAGE_DIR}/main.tex"
cp "${PAPER_DIR}/main.bbl" "${STAGE_DIR}/main.bbl"

# ---------------------------------------------------------------------
# 3. Create the tarball with the two files at the archive root.
# ---------------------------------------------------------------------
log "Creating ${BUNDLE_PATH}"
rm -f "${BUNDLE_PATH}"
tar -czf "${BUNDLE_PATH}" -C "${STAGE_DIR}" main.tex main.bbl

# ---------------------------------------------------------------------
# 4. Verification: extract into a fresh dir, compile with plain
#    pdflatex twice (no latexmk, no .bib available).
# ---------------------------------------------------------------------
VERIFY_DIR="$(mktemp -d)"
log "Verifying bundle by extraction + pdflatex in ${VERIFY_DIR}"
tar -xzf "${BUNDLE_PATH}" -C "${VERIFY_DIR}"

(
  cd "${VERIFY_DIR}"
  pdflatex -interaction=nonstopmode main.tex
  pdflatex -interaction=nonstopmode main.tex
)

VERIFY_LOG="${VERIFY_DIR}/main.log"
VERIFY_PDF="${VERIFY_DIR}/main.pdf"

if [[ ! -f "${VERIFY_LOG}" ]]; then
  echo "ERROR: verification log ${VERIFY_LOG} not found" >&2
  exit 1
fi

if grep -qiE 'undefined (citations?|references?)' "${VERIFY_LOG}"; then
  echo "ERROR: verification log reports undefined citations/references:" >&2
  grep -inE 'undefined (citations?|references?)' "${VERIFY_LOG}" >&2
  exit 1
fi

if [[ ! -f "${VERIFY_PDF}" ]]; then
  echo "ERROR: verification did not produce ${VERIFY_PDF}" >&2
  exit 1
fi

PAGE_COUNT=""
if command -v pdfinfo >/dev/null 2>&1; then
  PAGE_COUNT="$(pdfinfo "${VERIFY_PDF}" | awk -F': *' '/^Pages/ {print $2}')"
else
  PAGE_COUNT="$(grep -oE "Output written on main\.pdf \([0-9]+ pages" "${VERIFY_LOG}" \
    | grep -oE '[0-9]+' || true)"
fi

if [[ -z "${PAGE_COUNT}" ]]; then
  echo "ERROR: could not determine PDF page count" >&2
  exit 1
fi

if [[ "${PAGE_COUNT}" -ne "${EXPECTED_PAGES}" ]]; then
  echo "ERROR: expected ${EXPECTED_PAGES}-page PDF, got ${PAGE_COUNT} pages" >&2
  exit 1
fi

# ---------------------------------------------------------------------
# 5. Summary.
# ---------------------------------------------------------------------
log "Bundle verification passed"
echo
echo "Bundle:      ${BUNDLE_PATH}"
echo "Contents:    $(tar -tzf "${BUNDLE_PATH}" | tr '\n' ' ')"
echo "PDF pages:   ${PAGE_COUNT}"
