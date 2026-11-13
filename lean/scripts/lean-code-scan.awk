# Comment- and string-aware scanner over Lean sources, shared by scripts/check-no-sorry.sh
# (mode=sorry), scripts/check-no-custom-axiom.sh (mode=axiom),
# scripts/check-root-aggregator.sh (mode=root) and the Comparator boundary (mode=import).
# For the latter, set `-v import_target=ComparatorChallenge`. Invoke as
#     LC_ALL=C awk -v mode=sorry -f scripts/lean-code-scan.awk FILE...
# and it prints `file:line:content` for every violating line; no output means clean. Under
# LC_ALL=C every awk reads bytes, and UTF-8 is decoded here.
#
# Lexing rules (state is reset per file):
#   * block comments `/- … -/` nest and may span lines, and leave a space in the code stream (they
#     separate tokens: `import A/- -/open B` is two commands); line comments `-- …` run to end of line;
#   * string literals `"…"` (with `\"` escapes, spanning lines — Lean allows raw newlines in
#     strings) are opaque: their content is replaced by `""` in the code stream, so a `/-`,
#     `--`, `sorry` or `axiom` inside a string neither opens a comment nor trips a rule;
#   * interpolated strings (`s!"…"`, `m!"…"`, any `<ident>!"…"`) are opaque EXCEPT their
#     `{…}` holes, which are Lean terms and are lexed as code — including nested comments
#     (a `}` inside `/- … -/` does not close the hole) and nested strings, interpolated ones
#     to any depth; `\{` is a literal brace;
#   * raw string literals `r"…"`, `r#"…"#`, `r##"…"##` … are opaque: no escapes, closed only
#     by `"` followed by the same number of `#`; recognised where the `r` cannot be part of
#     an identifier;
#   * escaped identifiers `«…»` are opaque (a `--`, `/-`, `"` or `sorry` inside is part of the
#     name) and appear in the code stream as `«x»`; length() and substr() agree on `«` whether
#     the awk counts bytes or characters;
#   * character literals `'x'` / `'\n'` / `'«'` are opaque, recognised only where a `'` cannot be
#     part of an identifier (`h'` stays an identifier), and appear in the code stream as `'' `;
#   * Lean's non-ASCII identifier characters (isLetterLike, isSubScriptAlnum) appear in the code
#     stream as `_`, so `αsorry` is one identifier and `αdmit` does not become `admit`.
# `sorry`/`admit` count unless an identifier character precedes them or an isIdRest character
# (including `'`, `!`, `?`) follows them. The axiom rule fires on a line that starts a declaration
# with `axiom`/`constant`/`opaque`/`unsafe` (after attributes and modifiers), and anywhere in the
# line, so also after another command, on `axiom`/`opaque` and on `unsafe` followed by a
# declaration keyword, a modifier or the line end (`aesop (add unsafe h)` does not count), each
# not preceded by an isIdRest character or `.` (`foo?opaque` is one name). A declaration keyword
# may end its line (`axiom` ⏎ `bad : False`).
# mode=root flags every line whose code is neither blank, the `module` header nor an `import` of
# exactly ONE module name (optionally `public`/`private`/`meta`-prefixed): the root aggregator
# carries imports and comments only. It honours no marker. One name per line means no command can
# follow an import on the same line (`import A open B`, `import A declare_syntax_cat s`) without a
# keyword list. A module name is dotted components; `«…»` escapes and non-ASCII characters are
# accepted, ASCII punctuation other than `_ ' ! ?` is not (matched by an explicit character list,
# never a byte range, so mawk, nawk and gawk in any locale agree).
# mode=import reports a module import whose root matches import_target, honoring Lean's
# public/meta/all modifiers and ignoring comments and strings. mode=imports prints each direct
# imported module name, one per line, for project-local dependency checks. Both preserve escaped
# names for these checks and may be invoked on multiple source files.
# The ALLOW_ markers are honoured ONLY in the trailing line comment of the violating line
# (`… := sorry -- ALLOW_SORRY: #12 reason`), never inside a string or a block comment.
BEGIN {
  q = "\047"; G = "«"; GC = "»"; LG = length(G); LGC = length(GC)
  if (LG == 2) for (k = 128; k < 256; k++) ord[sprintf("%c", k)] = k   # byte values, for UTF-8
  if (mode == "import" && import_target == "") {
    print "lean-code-scan.awk: mode=import requires import_target" > "/dev/stderr"; exit 2
  }
}
# lvl: open interpolation holes; hb[k]: unmatched `{` inside hole k.
FNR == 1 {
  if (mode == "import" && import_file != "" && moduleHasImport(import_code, import_target))
    printf "%s: forbidden import of %s\n", import_file, import_target
  if ((mode == "import" || mode == "imports") && import_file != "") {
    if (mode == "imports") emitImports(import_code)
  }
  if (mode == "import" || mode == "imports") { import_file = FILENAME; import_code = "" }
  depth = 0; inStr = 0; rawHashes = -1; interp = 0; lvl = 0
}
{
  line = $0; code = ""; inLine = 0; trailing = ""
  n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); two = substr(line, i, 2)
    if (inStr) {
      if (rawHashes >= 0) {                        # raw string: `"` + rawHashes × `#` closes it
        if (c == "\"" && substr(line, i + 1, rawHashes) == hashes(rawHashes)) {
          i += 1 + rawHashes; inStr = 0; rawHashes = -1; code = code "\"\""; continue
        }
        i++; continue
      }
      if (c == "\\") { i += 2; continue }
      if (interp && c == "{") { lvl++; hb[lvl] = 0; inStr = 0; code = code " "; i++; continue }
      if (c == "\"") { inStr = 0; interp = 0; code = code "\"\"" }
      i++; continue
    }
    if (depth > 0) {
      if (two == "-/") { depth--; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      i++; continue
    }
    if (inLine) { i++; continue }
    if (substr(line, i, LG) == G) {
      j = skipGuillemets(line, i)
      code = code (((mode == "import" || mode == "imports") ? substr(line, i, j - i) : "«x»"))
      i = j; continue
    }
    if (two == "--") { inLine = 1; trailing = substr(line, i); i += 2; continue }
    if (two == "/-") { depth++; code = code " "; i += 2; continue }   # a comment separates tokens
    if (c == "\"") { inStr = 1; rawHashes = -1; interp = (code ~ /[A-Za-z0-9_]![[:space:]]*$/) ? 1 : 0; i++; continue }
    if (c == "r" && (code == "" || substr(code, length(code), 1) !~ /[A-Za-z0-9_.!?]/)) {
      j = i + 1; h = 0
      while (substr(line, j, 1) == "#") { h++; j++ }
      if (substr(line, j, 1) == "\"") { inStr = 1; rawHashes = h; interp = 0; i = j + 1; continue }
    }
    if (c == q) {
      prev = (code == "") ? "" : substr(code, length(code), 1)
      if (prev == "" || (prev !~ /[A-Za-z0-9_.!?]/ && prev != q)) {
        if (substr(line, i + 1, 1) == "\\" && substr(line, i + 3, 1) == q) { code = code "'' "; i += 4; continue }
        L = u8len(line, i + 1)
        if (substr(line, i + 1, 1) != q && substr(line, i + 1 + L, 1) == q) { code = code "'' "; i += 2 + L; continue }
      }
    }
    if (lvl > 0 && c == "{") hb[lvl]++
    if (lvl > 0 && c == "}") {
      if (hb[lvl] == 0) { lvl--; inStr = 1; interp = 1; code = code " "; i++; continue }   # hole closes
      hb[lvl]--
    }
    if (c in ord) { L = u8len(line, i); code = code (idRest(ucp) ? "_" : substr(line, i, L)); i += L; continue }
    code = code c; i++
  }
  if (mode == "sorry") {
    if (code ~ /(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_'!?]|$)/ && trailing !~ /ALLOW_SORRY: .*#[0-9]+/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if (mode == "axiom") {
    if ((code ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)([[:space:]]|$)/ ||
         code ~ /(^|[^A-Za-z0-9_.'!?])(axiom|opaque)([^A-Za-z0-9_'!?]|$)/ ||
         code ~ /(^|[^A-Za-z0-9_.'!?])unsafe([[:space:]]+(partial|nonrec|noncomputable|private|protected|def|theorem|lemma|abbrev|irreducible_def|instance|opaque|axiom|inductive|structure|class|example)([^A-Za-z0-9_'!?]|$)|[[:space:]]*$)/) &&
        trailing !~ /ALLOW_AXIOM: .*#[0-9]+/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if (mode == "root") {
    if (!rootLineOk(code)) printf "%s:%d:%s\n", FILENAME, FNR, line
  } else if (mode == "import" || mode == "imports") {
    import_code = import_code " " code
  } else {
    print "lean-code-scan.awk: unknown mode '" mode "'" > "/dev/stderr"; exit 2
  }
}
END {
  if (mode == "import" && import_file != "" && moduleHasImport(import_code, import_target))
    printf "%s: forbidden import of %s\n", import_file, import_target
  if (mode == "imports" && import_file != "") emitImports(import_code)
}
function hashes(k,   s) { s = ""; while (k-- > 0) s = s "#"; return s }
# Byte length of the UTF-8 character at s[i] (1 for ASCII, a malformed sequence or an awk that
# counts characters); sets ucp to its code point, or -1.
function u8len(s, i,   b, L, k, t) {
  ucp = -1; b = substr(s, i, 1)
  if (!(b in ord) || ord[b] < 194 || ord[b] > 244) return 1
  b = ord[b]; L = (b < 224) ? 2 : ((b < 240) ? 3 : 4); t = b % ((L == 2) ? 32 : ((L == 3) ? 16 : 8))
  for (k = 1; k < L; k++) {
    b = substr(s, i + k, 1)
    if (!(b in ord) || ord[b] > 191) return 1
    t = t * 64 + ord[b] - 128
  }
  ucp = t; return L
}
# Lean's non-ASCII isIdRest characters (Init/Meta/Defs.lean, isLetterLike || isSubScriptAlnum):
# U+00C0–U+017F but × ÷, U+0391–U+03A9 but Π Σ, U+03B1–U+03FB but λ, U+1D62–U+1D6A,
# U+1F00–U+1FFE, U+2080–U+2089, U+2090–U+209C, U+2100–U+214F, U+2C7C, U+1D49C–U+1D59F.
function idRest(u) {
  return (u >= 192 && u <= 383 && u != 215 && u != 247) || (u >= 913 && u <= 937 && u != 928 && u != 931) ||
    (u >= 945 && u <= 1019 && u != 955) || (u >= 7522 && u <= 7530) || (u >= 7936 && u <= 8190) ||
    (u >= 8320 && u <= 8329) || (u >= 8336 && u <= 8348) || (u >= 8448 && u <= 8527) || u == 11388 ||
    (u >= 119964 && u <= 120223)
}
# Index just past the `»` closing the `«` at position i (end of line if unterminated).
function skipGuillemets(s, i,   k) {
  k = index(substr(s, i + LG), GC)
  return (k == 0) ? length(s) + 1 : i + LG + k - 1 + LGC
}
function rootLineOk(s,   toks, nt, k, t) {
  nt = split(s, toks, /[[:space:]]+/); k = 1
  if (nt > 0 && toks[1] == "") k = 2                 # leading whitespace
  if (nt > 0 && toks[nt] == "") nt--                 # trailing whitespace
  if (k > nt) return 1                               # blank
  if (k == nt && toks[k] == "module") return 1
  while (k <= nt && (toks[k] == "public" || toks[k] == "private" || toks[k] == "meta")) k++
  if (k + 1 != nt || toks[k] != "import") return 0   # `import` and exactly one module name
  t = toks[nt]
  gsub(/«[^»]*»/, "X", t)
  if (t ~ /^[.0-9]/ || t ~ /\.$/ || t ~ /\.\./) return 0
  if (t ~ /[][(){}<>:;,=+*\/\\|&^%$#@~`"-]/) return 0
  return 1
}
function moduleHasImport(s, target,   toks, nt, i, k, module, escaped_target) {
  nt = split(s, toks, /[[:space:]]+/)
  escaped_target = G target GC
  for (i = 1; i <= nt; i++) {
    k = i
    if (toks[k] == "module") k++
    if (toks[k] == "public") k++
    if (toks[k] == "meta") k++
    if (toks[k] != "import") continue
    k++
    if (toks[k] == "all") k++
    if (k > nt) continue
    module = toks[k]
    if (module == target || substr(module, 1, length(target) + 1) == target "." ||
        module == escaped_target || substr(module, 1, length(escaped_target) + 1) == escaped_target ".")
      return 1
  }
  return 0
}
function emitImports(s,   protected, sentinel, i, n, j, escaped, toks, nt, k, module) {
  sentinel = sprintf("%c", 1); protected = ""; n = length(s); i = 1
  while (i <= n) {
    if (substr(s, i, LG) == G) {
      j = skipGuillemets(s, i)
      escaped = substr(s, i, j - i); gsub(/[[:space:]]/, sentinel, escaped)
      protected = protected escaped; i = j
    } else {
      protected = protected substr(s, i, 1); i++
    }
  }
  nt = split(protected, toks, /[[:space:]]+/)
  for (i = 1; i <= nt; i++) {
    if (toks[i] != "import") continue
    k = i + 1
    if (toks[k] == "all") k++
    if (k > nt || toks[k] == "") continue
    module = toks[k]
    # Comments can separate the components of a dotted module name. Rejoin spaces around dots.
    while (k < nt && (module ~ /\.$/ || toks[k + 1] ~ /^\./)) {
      k++; module = module toks[k]
    }
    gsub(sentinel, " ", module)
    print normalizeEscapedModule(module)
  }
}
function normalizeEscapedModule(s,   start, after_open, close_rel, close_start, close_next, body) {
  while ((start = index(s, G)) > 0) {
    after_open = start + LG
    close_rel = index(substr(s, after_open), GC)
    if (close_rel == 0) break
    close_start = after_open + close_rel - 1
    body = substr(s, after_open, close_start - after_open)
    close_next = close_start + LGC
    s = substr(s, 1, start - 1) body substr(s, close_next)
  }
  return s
}
