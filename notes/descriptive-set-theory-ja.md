# 記述集合論用語・学習ノート

> **Status:** evolving with Issue #46.  
> **Purpose:** 伊敷–宇田共同研究で新たに必要となる記述集合論の用語と，証明で実際に使う事実を日本語で整理する．  
> **重要:** `report/report-ja.md` は Conjecture 5.1 の v1 証明記録として保存し，本ノートで置き換えない．

## 0. このノートの読み方

本ノートでは，次の三つを区別する．

1. **用語**：本 project で採用する日本語訳．日本語の専門的使用例をできるだけ確認する．
2. **一般論**：記述集合論の標準的事実．主に Kechris の教科書を基準とする．
3. **今回の適用**：Issue #46 で監査する共同研究の証明で，その一般論をどこに使うか．

特に `analytic` / `coanalytic` は，**どの ambient space で考えるか**によって定義上の注意が必要である．共同原稿ではまず Polish ambient に対して定義した後，一般の `CPM(X)` に対して同じ語を使っているため，この部分は Issue #46 で監査中である．定義が確定するまで，このノートでも一般の `CPM(X)` に対する用法を勝手に補わない．

---

## 1. Project 標準用語

| English | 本 project の日本語 | 記号・備考 | 状態 |
|---|---|---|---|
| descriptive set theory | **記述集合論** |  | 固定 |
| Polish space | **ポーランド空間** |  | 固定 |
| Borel set | **ボレル集合** |  | 固定 |
| Borel hierarchy | **ボレル階層** |  | 固定 |
| projective hierarchy | **射影階層** |  | 固定 |
| analytic set | **解析集合** | `Σ¹₁` | 固定 |
| coanalytic set | **余解析的集合** | `Π¹₁` | 固定 |
| perfect set | **完全集合** | 閉かつ孤立点を持たない集合 | 固定 |
| perfect set theorem | **完全集合定理** |  | 固定 |
| perfect set property | **完全集合性 (perfect set property; PSP)** | 日本語は必ず英語も初出で併記する | 暫定 project 標準 |
| Bernstein set | **ベルンシュタイン集合** |  | 固定 |
| Cantor space | **カントール空間** | `2^ℕ` または `2^ω` | 固定 |
| Baire space | **ベール空間** | `ℕ^ℕ` または `ω^ω` | 固定 |
| standard Borel space | **標準ボレル空間** |  | 固定 |
| Borel isomorphism | **ボレル同型** | 位相同型とは異なる | 固定 |
| absolute Borel class | **絶対ボレル類** | Koshino の用法を監査後に定義確定 | 暫定 |

### 1.1 `analytic` は「解析集合」とする

本 project では **analytic set = 解析集合** とする．「解析的集合」は用いない．

この訳語は，名古屋大学 2026 年度「数理論理学特論1」の記述集合論シラバスで，「ポーランド空間」「ボレル集合」「解析集合」「射影集合」として実際に使われている．また，藤田博司氏の愛媛大学での講演概要でも `Σ¹₁集合（解析集合）` と明記されている．

### 1.2 `coanalytic` は「余解析的集合」とする

本 project では **coanalytic set = 余解析的集合** とする．木原貴行氏の科研費研究課題のキーワードに「余解析的集合」という実例があるため，これを標準形とする．

ただし，日本語文献では `coanalytic` を英語のまま置いたり，「解析集合の補集合」と説明したりする用法もある．したがって，初出では

> 余解析的集合 (coanalytic set, `Π¹₁`)

と英語・記号を併記する．

### 1.3 `perfect set property` は当面「完全集合性」

`perfect set property` の日本語訳には，今回確認した範囲では `解析集合` ほど強い標準化の根拠を得られていない．本 project では便宜上 **完全集合性 (perfect set property; PSP)** と呼ぶが，初出では必ず英語を併記する．

---

## 2. ポーランド空間

### 定義

位相空間 `X` が **ポーランド空間 (Polish space)** であるとは，`X` が可分であり，かつその位相を誘導する完備距離が存在することをいう．

ここで重要なのは，「現在書かれている特定の距離が完備」という意味ではなく，**位相として完全距離化可能で，しかも可分**ということである．

### 今回使う例

- `[0,1]`．
- 実数直線 `ℝ`．
- カントール空間 `2^ℕ`．
- ベール空間 `ℕ^ℕ`．

共同原稿の Proposition 2.1 では `[0,1]`，Proposition 2.2 と非 Archimedean 部分では `2^ℕ` を parameter space として使う．

---

## 3. ボレル集合，解析集合，余解析的集合

以下では，まず **ambient space `P` を Polish space とする**．これは共同原稿 §2.3 の設定と同じである．

### 3.1 ボレル集合

`P` の開集合から，可算和・可算共通部分・補集合を繰り返して得られる最小の `σ`-代数の元を **ボレル集合 (Borel set)** という．

今回の証明ではボレル階層そのものを詳しく計算する必要はない．重要なのは，ボレル集合が解析集合・余解析的集合の双方に含まれることである．

### 3.2 解析集合

`A ⊆ P` が **解析集合 (analytic set, `Σ¹₁`)** であるとは，標準的には，ある Polish space からの連続写像の像として `A` を表せることをいう．同値な定義として，Polish space のボレル集合の射影として表す定義などがある．

直観的には，「ボレル集合より一段広いが，なお強い記述可能性を持つ集合」のクラスである．

### 3.3 余解析的集合

`A ⊆ P` が **余解析的集合 (coanalytic set, `Π¹₁`)** であるとは，補集合 `P \ A` が解析集合であることをいう．

したがって，`analytic` と `coanalytic` は互いに単純な同義語ではない．

### 3.4 最低限覚える関係

Polish ambient space では，次の関係を使う．

```text
Borel  ──⇒  analytic
   │
   └────⇒  coanalytic

analytic かつ coanalytic  ──⇒  Borel
```

最後の含意は Souslin の定理であり，結局

```text
Borel = analytic ∩ coanalytic
```

となる．

**注意:**

```text
non-Borel ⇒ neither analytic nor coanalytic
```

は誤りである．非 Borel な解析集合は存在する．正しいのは，

```text
neither analytic nor coanalytic ⇒ non-Borel
```

である．この向きの取り違えは共同研究の議論で致命的になり得るので，明示的に区別する．

---

## 4. 完全集合と完全集合性

### 4.1 完全集合

距離化可能空間の部分集合 `K` が **完全集合 (perfect set)** であるとは，通常，`K` が閉であり，孤立点を持たないことをいう．

実数直線やカントール空間では，空でない完全集合は連続体濃度 `𝔠` を持つ．

### 4.2 完全集合性 (PSP)

部分集合 `A` が **完全集合性 (perfect set property; PSP)** を持つとは，

- `A` が可算であるか，
- `A` が空でない完全集合を含む

ことをいう．

Polish space の解析集合および余解析的集合は完全集合性を持つ．共同原稿は Kechris の perfect set theorems をこの形で用いている．

### 4.3 今回必要な濃度論的帰結

`A` が Polish space の非可算な解析集合または余解析的集合なら，`A` は空でない完全集合を含む．したがって

```text
|A| = 𝔠.
```

この帰結が Proposition 2.1 / 2.2 の `¬CH` case の核心である．

特に `ℵ₁ < 𝔠` のとき，

```text
|A| = ℵ₁
```

である部分集合は，解析集合にも余解析的集合にもなれない．

---

## 5. ベルンシュタイン集合

### 定義

`P` を空でない perfect Polish space とする．`B ⊆ P` が **ベルンシュタイン集合 (Bernstein set)** であるとは，すべての空でない完全集合 `K ⊆ P` に対して

```text
K ∩ B ≠ ∅,
K \ B ≠ ∅
```

が成り立つことをいう．

したがって，`B` もその補集合も，空でない完全集合を丸ごと含むことができない．

### 今回の役割

CH (`𝔠 = ℵ₁`) の場合，`[0,1]` または `2^ℕ` のベルンシュタイン集合を取ることで，濃度 `ℵ₁` で解析集合でも余解析的集合でもない集合を得る．

共同原稿 Proposition 2.1 はこの方法を `[0,1]` で用いている．

---

## 6. カントール空間 `2^ℕ`

### 6.1 定義

`2 = {0,1}` を離散空間とし，

```text
2^ℕ = { x : ℕ → {0,1} }
```

に積位相を入れたものを **カントール空間 (Cantor space)** という．

カントール空間は compact Polish space であり，孤立点を持たない．非 Archimedean な自然な距離を持つため，共同原稿の ultrametric coding の parameter space として適している．

「カントール空間」という表記は RIMS 講究録の題名「カントール空間上の非空実効的閉集合の次数構造」など，日本語の数理論理学文献で実例がある．

### 6.2 Proposition 2.2 の修正点

共同原稿の現版は，`[0,1]` と `2^ℕ` が Borel isomorphic であることから Proposition 2.2 を導いている．しかし，**ボレル同型は位相同型ではなく，一般には稠密性を保存しない**．したがって，稠密性という条件までそのまま移すことはできない．

この proposition は `2^ℕ` 上で直接構成すればよい．

- **CH の場合:** `2^ℕ` のベルンシュタイン集合 `S` を取る．`|S|=𝔠=ℵ₁` であり，解析集合でも余解析的集合でもない．また，各非空基本開集合は空でない完全集合を含むので `S` は稠密である．
- **¬CH の場合:** 可算稠密集合 `Q ⊆ 2^ℕ` を取り，`Q ⊆ S ⊆ 2^ℕ` かつ `|S|=ℵ₁` となるように `S` を拡張する．すると `S` は稠密であり，`ℵ₁<𝔠` と完全集合性から，解析集合でも余解析的集合でもない．

この修正は Issue #46 では `FIX` として扱う．

---

## 7. ボレル同型と位相同型

### ボレル同型

標準ボレル空間 `X,Y` の間の全単射 `f : X → Y` が **ボレル同型 (Borel isomorphism)** であるとは，`f` と `f⁻¹` がともに Borel measurable であることをいう．

これは Borel structure を保存する概念であり，位相そのものを保存する概念ではない．

### 位相同型との違い

位相同型ならば，開集合・閉集合・稠密性・収束などの位相的性質を保存する．一方，Borel isomorphism からそれらは一般には従わない．

したがって，今回の Proposition 2.2 のように **density が結論に含まれる場合，Borel isomorphism の存在だけでは不十分**である．

---

## 8. 今回の証明で使う pullback の考え方

共同原稿の metric coding では，parameter space 全体から

```text
Φ : [0,1] → BCPM(D)
```

という連続写像を考え，

```text
Φ⁻¹(BMet(D)) = [0,1] \ S
```

という exact pullback identity を示すのが安全である．

この形にすると，analytic / coanalytic class が連続逆像で閉じていることを直接使える．「閉部分空間として homeomorphic copy が入っている」という議論より，ambient-space convention に依存する箇所を明示しやすい．

同じ方針を finite-distance component，complete metrics，ultrametrics にも適用できるかを Issue #46 で監査する．

---

## 9. `analytic/coanalytic in CPM(X)` の ambient-space 問題

### 現在の状態: **監査中**

共同原稿 §2.3 は，`P` が Polish space である場合に analytic / coanalytic subset を定義している．一方，主定理では一般の metrizable `X` に対して

```text
Met(X) is analytic or coanalytic in CPM(X)
```

という表現を使う．しかし，一般の `CPM(X)` が Polish であるとは限らない．

したがって，ここでは以下を混同してはいけない．

1. Polish ambient space の部分集合としての classical analytic / coanalytic set．
2. 位相空間それ自体を「analytic space」と呼ぶ intrinsic な用法．
3. 非可分・非 Polish ambient に拡張された `Souslin` / absolute pointclass 型の定義．
4. 何らかの Polish coding space に埋め込んだ上での定義．

一般の非可分 metrizable spaces における analytic set には複数の拡張概念が文献上存在する．したがって，**共同原稿の主定理の意味を確定する前に，どの定義を採るかを明記する必要がある**．

Issue #46 では，ここを最優先の definition audit とする．確定するまでは，本ノートでも `Met(X) is analytic/coanalytic in CPM(X)` の日本語訳を theorem-level の確定語として扱わない．

---

## 10. Koshino の absolute Borel との関係

Koshino の論文 *On the Borel complexity and the complete metrizability of spaces of metrics*（Anal. Geom. Metr. Spaces 12 (2024), art. 20240014; DOI [10.1515/agms-2024-0014](https://doi.org/10.1515/agms-2024-0014)）は，bounded admissible metrics の空間 `AM(X)` の Borel complexity と complete metrizability を扱う．同論文の主定理・系は原文では無番号（"Theorem."／"Corollary." とのみ表記）であり，その Corollary の主張は「separable metrizable `X` について，`X` が `σ`-compact であることと `AM(X)` が completely metrizable であることは同値」というものである（`notes/literature.md` で arXiv v2 本文と DOI の Crossref レコードに対し検証済み．「Corollary 1.2」のような番号付き引用は原文と一致しないため用いない）．

**注意:** `AM(X)`（bounded admissible metrics の空間）と，本 project 全体で扱う `Met(D)`（離散位相と両立する距離の空間，`notes/terminology.md`）は同じ空間ではない．Ishiki の原稿（arXiv:2407.03030 §5）は Koshino の結果を `Met(X)` の形で引用しているが，これは Ishiki 自身による言い換えであり，Koshino の論文自体は `AM(X)` について述べている．両者を安易に同一視しない（`notes/literature.md` の記載どおり）．

今回の共同研究の一つの目標は，非可分の場合に metric moduli space の descriptive complexity（今回の `analytic/coanalytic in CPM(X)` の議論）から separability を強制し，Koshino の結果の separability hypothesis を結果として取り除くことである．

Koshino の論文における `absolute Borel class` の具体的な定義・使用箇所は，本ノート作成時点で一次資料から直接確認できていない．`absolute Borel` と今回の `analytic/coanalytic in CPM(X)` が同じ概念かどうかも含め，この関係は Issue #46 で一次資料を確認した上で正確に整理し，本節を更新する．

---

## 11. この project で当面暗記してよい最小セット

```text
Polish = separable + completely metrizable.

Borel ⇒ analytic.
Borel ⇒ coanalytic.
analytic ∩ coanalytic = Borel.          [Polish ambient]

analytic / coanalytic ⇒ perfect set property.
uncountable analytic / coanalytic ⇒ cardinality 𝔠.

Bernstein set:
  every nonempty perfect set meets both B and its complement.
  ⇒ neither side contains a nonempty perfect set.

Borel isomorphism ≠ homeomorphism.
Borel isomorphism does NOT in general preserve density.
```

そして今回最も重要な注意は，

```text
"analytic/coanalytic in CPM(X)" の意味は，general X ではまだ監査中．
```

である．

---

## 12. 参考文献・用語ソース

### 数学的基準文献

- A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer, 1995. 共同原稿では analytic/coanalytic perfect set theorem に Theorems 29.1, 32.2 を引用している．
- K. Koshino, *On the Borel complexity and the complete metrizability of spaces of metrics*, Analysis and Geometry in Metric Spaces 12 (2024), Article 20240014. https://doi.org/10.1515/agms-2024-0014

### 日本語用語の確認に使った資料

- 名古屋大学 2026 年度シラバス「数理論理学特論1」．「記述集合論」「ポーランド空間」「ベール空間」「ボレル集合」「解析集合」「射影集合」の用例．  
  https://syllabus.adm.nagoya-u.ac.jp/data/2026/25_2026_Y010602510017.html
- 愛媛大学 松山 TGSA セミナー，第12回 藤田博司「On subgroups of Polish Abelian group generated by Borel sets」．`Σ¹₁集合（解析集合）` の用例．  
  https://www.math.sci.ehime-u.ac.jp/MTGSA.ja.html
- 木原貴行，科研費「計算可能性理論，記述集合論，位相空間論における階層の究極的解析」．キーワード「余解析的集合」の用例．  
  https://kaken.nii.ac.jp/grant/KAKENHI-PROJECT-19K03602/
- 京都大学数理解析研究所 RIMS 講究録 No.1729．樋口幸治郎「カントール空間上の非空実効的閉集合の次数構造」．「カントール空間」の用例．  
  https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/1729.html
- 東京大学大学院数理科学研究科のセミナーテキスト案内．「標準ボレル空間」の用例．  
  https://www.ms.u-tokyo.ac.jp/~kida/seminartext.html

### 用語上の保留

- `perfect set property` → 「完全集合性」は本 project の暫定標準．日本語の専門文献における用例を引き続き探索する．
- `absolute Borel class` → 「絶対ボレル類」は暫定．Koshino の定義と日本語既存用法を Issue #46 で確認後に固定する．
- general `CPM(X)` における `analytic/coanalytic` → **定義自体が監査中**．訳語以前に数学的 convention を確定する．

---

## Issues

- #46 — joint extension の数学的監査．
- #47 — #46 で確定した定理の Lean 形式化．
- #48 — 本ノートの整備．
