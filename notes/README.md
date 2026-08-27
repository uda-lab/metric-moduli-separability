# Notes

このディレクトリには、プロジェクトの数学的検討、用語集、およびサーベイ文書が配置されています。

## Markdown から PDF への変換方法

和文の Markdown ファイル（例: `borel-preprint-corrections-ja.md`）を綺麗に PDF に変換するには、以下の環境が必要です。

### 必要な環境
- **Pandoc** (2.12 以上を推奨)
- **TeX 環境** (LuaLaTeX が動作すること。MacTeX 等)

### 変換コマンド
日本語の文章で、改行が不要な半角スペース（分かち書き）として PDF に反映されるのを防ぐため、`east_asian_line_breaks` 拡張を有効にします。

```bash
pandoc <入力ファイル.md> -f markdown+east_asian_line_breaks -o <出力ファイル.pdf> --pdf-engine=lualatex -V documentclass=ltjsarticle
```

例：
```bash
pandoc borel-preprint-corrections-ja.md -f markdown+east_asian_line_breaks -o borel-preprint-corrections-ja.pdf --pdf-engine=lualatex -V documentclass=ltjsarticle
```
