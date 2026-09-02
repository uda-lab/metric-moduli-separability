# Notes

このディレクトリには、プロジェクトの数学的検討、用語集、およびサーベイ文書が配置されています。

## Markdown から PDF への変換方法

これらの数学的なノートでは、単純な Pandoc のワンライナーだけでは不十分です。例えば、次のように `pandoc ... --pdf-engine=lualatex -V documentclass=ltjsarticle` を実行すると、LuaLaTeX は不足している文字ごとに `Missing character` 警告をログへ出すだけで、エラーにはしません。そのためビルドは成功したように見えますが、PDF では数百個のグリフの実体が黙って欠落し、虫食い状態になります。原因は、ノートに含まれる生の Unicode 数式文字（ℵ、𝔠、𝒟、ℝ、∈、⊆、ω₁、Σ¹₁、∖、ₙ、… など）が標準の Latin Modern フォントでカバーされていないことです。さらに、明示的な指定がないと `luatexja` はギリシャ文字や記号の範囲を日本語フォントへ回しますが、そのフォントにもこれらの文字がない場合があります。

この問題を検出可能な失敗にするため、変換には `notes/scripts/typeset.sh` を使います。このスクリプトは `notes/scripts/glyph-fallback.tex` をフォールバック用ヘッダーとして Pandoc から LuaLaTeX へ渡し、フォントフォールバックを設定します。各ノートのログに `Missing character` の行が一つでも残れば、そのノートを失敗とし、ノートごとのサマリーを表示したうえで非ゼロの終了コードでビルド全体を失敗させます。

### 必要な環境
- Pandoc と、LuaLaTeX および `luatexja` を含む TeX Live 環境。Debian/Ubuntu では `pandoc`、`texlive-luatex`、`texlive-lang-japanese`、`texlive-latex-recommended`、`texlive-fonts-recommended` が必要です。
- `STIX Two Math` と `DejaVu Sans` が kpathsea または luaotfload で解決できること。Debian/Ubuntu では `STIX Two Math` は `texlive-fonts-extra` にのみ収録されています。小さい `fonts-stix` パッケージは STIX v1 であり、ここで使う Two Math のグリフを持ちません。`DejaVu Sans` は `fonts-dejavu` で提供されます。
- `Apple Symbols` と `Menlo` は macOS で有用な追加フォールバックですが、Linux には存在しません。

### 変換コマンド
ノート名だけを引数に指定します。例えば、次のように実行します。

```bash
notes/scripts/typeset.sh terminology.md
```

引数を省略すると、数学的な記号が特に多い次の四つを処理します。

- `borel-manuscript-20260827-audit.md`
- `borel-preprint-audit.md`
- `descriptive-set-theory-ja.md`
- `terminology.md`

PDF とビルドログは `notes/typeset/` に出力されます。このディレクトリは Git の追跡対象外です。

フォールバックのリストは `TYPESET_FALLBACK_FONTS` 環境変数で変更できます。フォント名をセミコロンまたは改行で区切り、末尾に区切り文字を置かないでください。デフォルトは、次の四つをこの順序で指定したものです。

```text
STIXTwoMath-Regular:mode=node
DejaVu Sans:mode=node
Apple Symbols:mode=node
Menlo:mode=node
```

スクリプトは `luaotfload-tool --find` で実際に解決できるフォントだけを残してから LaTeX ヘッダーを生成します。したがって、Linux で利用できない `Apple Symbols` や `Menlo` は単に除外されます。手作業で `add_fallback` の表へ解決できないフォントを残すと、このエンジンでは穏当にスキップされず、Lua エラーで LuaLaTeX のビルド全体が中断します。

リストのうち最初に解決できたフォントは、`\setmathfont` によって LuaLaTeX の数式フォントにもなります。Pandoc の LuaLaTeX テンプレートは `unicode-math` を自動的に読み込み、一部の Unicode 数式クラスのコードポイントを fontspec の本文フォント用フォールバックではなく数式フォントへ送るため、順序が重要です。デフォルトで `STIX Two Math` を先頭に置いているのはそのためです。`DejaVu Sans` だけを数式フォントにすると、多くの数式グリフが欠落します。

参考（スクリプトが内部で行う処理の簡略形）は次のコマンドです。

```bash
pandoc <入力ファイル.md> -f markdown+east_asian_line_breaks -o <出力ファイル.pdf> --pdf-engine=lualatex -V documentclass=ltjsarticle
```

このコマンドをフォールバック用ヘッダーなしで直接実行すると、上記のグリフ欠落が警告だけで通過する失敗を再現します。
