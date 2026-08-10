#!/usr/bin/env bash
# Build a reproducible arXiv v1 source bundle for paper/main.tex.
#
# The bundle intentionally supplies a pre-generated main.bbl so that
# arXiv's TeX system does not need to process references.bib (which is
# deliberately excluded from the bundle). The bundle is verified by
# extracting it into a clean directory and compiling with plain
# pdflatex (no latexmk, no .bib) twice, and is only published to
# paper/arxiv-v1.tar.gz after every check passes.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PAPER_DIR="${SCRIPT_DIR}"
BUNDLE_NAME="arxiv-v1.tar.gz"
BUNDLE_PATH="${PAPER_DIR}/${BUNDLE_NAME}"
EXPECTED_PAGES=11

log() { printf '==> %s\n' "$1"; }

# ---------------------------------------------------------------------
# 0. Invalidate any pre-existing bundle up front. A failed build or a
#    failed verification below must never leave a stale or rejected
#    archive sitting at BUNDLE_PATH looking uploadable.
# ---------------------------------------------------------------------
log "Removing any pre-existing bundle at ${BUNDLE_PATH}"
rm -f "${BUNDLE_PATH}"

STAGE_DIR="$(mktemp -d)"
VERIFY_DIR="$(mktemp -d)"
CANDIDATE_PATH="$(mktemp "${PAPER_DIR}/.arxiv-v1.XXXXXX.tar.gz")"
trap 'rm -rf "${STAGE_DIR}" "${VERIFY_DIR}"; rm -f "${CANDIDATE_PATH}"' EXIT

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
log "Staging bundle contents in ${STAGE_DIR}"
cp "${PAPER_DIR}/main.tex" "${STAGE_DIR}/main.tex"
cp "${PAPER_DIR}/main.bbl" "${STAGE_DIR}/main.bbl"
chmod 644 "${STAGE_DIR}/main.tex" "${STAGE_DIR}/main.bbl"

# ---------------------------------------------------------------------
# 3. Create a candidate tarball with the two files at the archive
#    root. Tar and gzip metadata are pinned (sorted order, zeroed
#    owner/group, fixed mtime, no gzip name/mtime) so the archive is
#    byte-for-byte reproducible across runs given identical inputs.
# ---------------------------------------------------------------------
log "Creating candidate bundle ${CANDIDATE_PATH}"
tar --sort=name --owner=0 --group=0 --numeric-owner --mtime='@0' \
    --mode='u=rw,go=r' \
    -cf - -C "${STAGE_DIR}" main.tex main.bbl \
  | gzip -n -9 > "${CANDIDATE_PATH}"

# ---------------------------------------------------------------------
# 4. Verification: extract the candidate into a fresh dir, compile
#    with plain pdflatex twice (no latexmk, no .bib available).
# ---------------------------------------------------------------------
log "Verifying candidate bundle by extraction + pdflatex in ${VERIFY_DIR}"
tar -xzf "${CANDIDATE_PATH}" -C "${VERIFY_DIR}"

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
# 5. All checks passed: atomically publish the candidate as the
#    bundle. mktemp created CANDIDATE_PATH in PAPER_DIR itself, so
#    this mv is a same-filesystem rename (atomic).
# ---------------------------------------------------------------------
log "All checks passed; publishing ${BUNDLE_PATH}"
mv "${CANDIDATE_PATH}" "${BUNDLE_PATH}"
chmod 644 "${BUNDLE_PATH}"

BUNDLE_SHA256="$(sha256sum "${BUNDLE_PATH}" | awk '{print $1}')"

# ---------------------------------------------------------------------
# 6. Summary.
# ---------------------------------------------------------------------
log "Bundle verification passed"
echo
echo "Bundle:      ${BUNDLE_PATH}"
echo "Contents:    $(tar -tzf "${BUNDLE_PATH}" | tr '\n' ' ')"
echo "PDF pages:   ${PAGE_COUNT}"
echo "SHA-256:     ${BUNDLE_SHA256}"
