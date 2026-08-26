# 距離のモジュライ空間のボレル性と可分性：証明の補正点に関する覚書

**対象:** Y. Ishiki and T. Uda, *Borelness of Moduli Spaces of Metrics Implies
Separability*, arXiv:2608.19618v1（以下 [IU]）．2026 年 8 月．

## 1. 要約

[IU] の全ての命題・定理・系の証明を，形式検証を併用した再検討により定理ごとに
確認した．結論は次の通りである．

**[IU] の全ての主張は ZFC の定理として正しい．** 一方，印刷された証明のうち
4 箇所（命題 2.2，系 3.7，定理 3.8，定理 3.14—系 3.17 も同じ点を継承する）には
補正が必要であり，それぞれについて標準的な議論による修正証明を確認した．また，
引用している距離の拡張定理の完備性保存の主張には，出典の証明が実際に置いている
仮定を明記する必要がある．本ノートでは各項目に次の種別を付す．

- **(A) 証明の欠陥** — 主張は真であり，書かれた証明に具体的な補正を要する．
- **(B) 外部定理の適用範囲** — 外部結果を適用できる仮定の明確化．
- **(C) 表現上の注意** — 数学的欠陥ではない記述の揺れ・省略．

| 箇所 | 種別 | 要点 |
|---|---|---|
| 命題 2.2 | A | Borel 同型は稠密性を保たない．稠密化による修正（§3.1） |
| 定理 3.3 | C | 本文は $\operatorname{BMet}(Z)$，概要・導入は $\operatorname{Met}(Z)$．同じ証明で両方成立（§3.2） |
| 系 3.7 | A | $\operatorname{BMet}$ 版のボレル性・可分性転送補題が必要（§3.3） |
| 定理 3.8 | A | 貼り合わせの基底距離を同じ成分の完備な代表に取り替える（§3.4） |
| 系 3.9 | B | 拡張定理の完備性保存は $X$ 完備距離化可能の下で読む（§3.5） |
| 定理 3.14 | A | 引用する拡張定理は擬超距離レベルの拡張を与えない．閉包を経る転送で修復（§3.6） |
| 系 3.15 | 継承 + C | 定理 3.14 の修復した経路に帰着．Alexandrov–Lavrentiev の引用を明記（§3.7） |
| 系 3.17 | A（継承）+ B | 定理 3.14 と同じ転送の補正を継承．完備性保存は (N1) の明記された仮定の下で（§3.7） |

上表以外の結果（命題 2.1，補題 3.1・3.2・3.10・3.11，定理 3.4・3.5・3.12・
3.13・3.16，系 3.6）については，印刷された証明がそのまま成立することを確認した
（系 3.6 は証明が省略されているが，意図された導出は正しい．§3.7 参照）．

最も実質的なのは定理 3.14（と系 3.17）の補正である．引用する超距離の拡張定理
[I2, Theorem 4.7] は両立する距離全体の空間の上でのみ定義されており，擬超距離
全体の空間のレベルの拡張を与えない．このため印刷された証明の最終段（全体空間
（ambient space）の間でのボレル性の引き戻し）はそのままでは従わない．
§3.6 で述べる通り，全体空間
$\operatorname{UCPM}(Y;R)$ の完備性と，パラメータ空間のコンパクトな像の閉包を
用いた転送論法によりこの段は修復され，定理の主張は成立する．

以下，§2 で記法，§3 で各論，§4 で原稿への修正提案の一覧，§5 で直接確認した
部分と外部入力の区別を述べる．

## 2. 記法と規約

### 2.1 距離のモジュライ空間

位相空間 $X$ に対し，[IU] の記法を用いる．

- $\operatorname{CPM}(X)$ — $X$ 上の連続擬距離
  $d \colon X \times X \to [0,\infty)$ 全体（各値は有限）に，上限距離
  $\mathcal{D}_X(d,e) = \sup_{(x,y) \in X^2} \lvert d(x,y) - e(x,y) \rvert$
  を入れたもの．$\mathcal{D}_X$ は $[0,\infty]$ に値をとる
  （extended-valued）が，位相は通常の距離 $\min\{\mathcal{D}_X, 1\}$ が誘導
  するものと一致する．
- $\operatorname{Met}(X) \subseteq \operatorname{CPM}(X)$ — $X$ の位相と
  両立する距離全体．$\operatorname{BMet}(X)$ — その有界なもの全体．
  $\operatorname{Comp}(X)$ — その完備なもの全体．
- 成分 (component) — $\mathcal{D}_X(d,e) < \infty$ を同値関係としたときの
  $\operatorname{Met}(X)$ の同値類 $\mathfrak{c}$．各成分は
  $\operatorname{Met}(X)$ の開かつ閉な部分集合であり，凸結合により道連結で
  ある．
- range set — $0 \in R$ を満たす $R \subseteq [0,\infty)$（確立した日本語訳が
  ないため英語のまま用いる）．$R$ が **characteristic** であるとは，$0$ が
  $R \setminus \{0\}$ の集積点であること，すなわち狭義単調減少列
  $r \colon \mathbb{N} \to R \setminus \{0\}$，$r(n) \to 0$ が存在すること
  をいう．このとき
  $h(s,t) = r(\min\{n : s(n) \neq t(n)\})$（$s \neq t$ のとき．
  $h(s,s) = 0$ とする）は
  カントール空間 $2^\omega$ 上の $R$-値超距離であり，積位相を誘導し，
  $(2^\omega, h)$ はコンパクトである．
- $\operatorname{UCPM}(Y;R)$ — 連続な $R$-値擬超距離（強三角不等式
  $d(x,z) \le \max\{d(x,y), d(y,z)\}$ を満たし値が $R$ に入る連続擬距離）
  全体に，非アルキメデス的一様距離
  $\mathcal{UD}^R_Y(d,e) = \inf\{\varepsilon \in R \cup \{\infty\} :
  d \le e \vee \varepsilon$ かつ $e \le d \vee \varepsilon$（各点で）$\}$
  を入れたもの（これも extended-valued）．
- $\operatorname{UMet}(Y;R)$ — 両立する $R$-値超距離全体．$R$-成分
  $\mathfrak{c}^R$ — $\mathcal{UD}^R_Y < \infty$ による同値類．
  $\operatorname{UComp}(Y;R)$ — $\operatorname{UMet}(Y;R)$ の完備なもの全体．

### 2.2 非可分な全体空間におけるボレル集合

$X$ が非可分ならば $\operatorname{CPM}(X)$ も一般に非可分だが，
「$\operatorname{CPM}(X)$ においてボレル」とは常に，その距離位相の開集合が
生成する $\sigma$-代数の元であることを意味する．[IU] の議論が非可分な全体空間
の中で行う操作は次の 4 つに限られ，いずれも可分性を要しない．

1. 閉集合（特にコンパクト集合）はボレル集合である．
2. ボレル集合とボレル集合（特に閉集合）の共通部分はボレル集合である．
3. トレース：$B$ が $M$ のボレル集合で $L \subseteq M$ ならば，$B \cap L$ は
   部分空間 $L$ のボレル集合である（生成系のレベルの議論で一般に成立する）．
4. 位相同型に沿った移送：ボレル $\sigma$-代数は位相不変量である．特に，閉な
   像への等長写像に沿ってボレル性が引き戻せる．

完全集合定理などの記述集合論的入力は，全て可分な完備距離空間 $[0,1]$，
$2^\omega$（またはそのコンパクトな同型像）の内部でのみ用いられる．解析集合・
余解析的集合（analytic, coanalytic）といったポイントクラスは可分性
（ポーランド性）を前提とする概念であり，[IU] の議論には現れず，必要もない．
このことが，非可分な全体空間においても主張が意味を持ち，証明が通る理由である．

## 3. 各論

### 3.1 命題 2.2 — Borel 同型は稠密性を保たない〔A〕

**主張．** $2^\omega$ に，濃度 $\aleph_1$ の稠密な非ボレル集合 $S$ が存在する
（命題 2.1 の $[0,1]$ における対応物の $2^\omega$ 版）．

**欠陥．** 印刷された証明は「$2^\omega$ と $[0,1]$ が Borel 同型であることから
従う」とする．Borel 同型はボレル構造と濃度を移すが，**稠密性を移さない**．
稠密性は位相的性質であって Borel 同型の不変量ではない．

**修正．** 次のいずれか一方で足りる．

1. 移送 + 稠密化．命題 2.1 の $S_0 \subseteq [0,1]$ を Borel 同型
   （[Ke, Theorem 15.6]）で引き戻し，非ボレルで濃度 $\aleph_1$ の
   $T \subseteq 2^\omega$ を得る．$Q_0$ を $2^\omega$ の可算稠密集合とし
   $S := T \cup Q_0$ とおく．$S$ は稠密であり，濃度は
   $\aleph_1 + \aleph_0 = \aleph_1$ である．非ボレル性：$Q_0 \setminus T$ は
   可算ゆえボレル集合であり，$T = S \setminus (Q_0 \setminus T)$ だから，
   $S$ がボレルならば $T$ もボレルとなり矛盾する．
2. 直接構成．$2^\omega$ は孤立点を持たない非空のポーランド空間だから，
   命題 2.1 の証明の場合分け（CH の場合はベルンシュタイン集合
   （存在は [Ke, Example 8.24] の証明中の構成）とボレル集合の完全集合定理
   [Ke, Theorem 13.6]，¬CH の場合は可算稠密集合を含む濃度 $\aleph_1$ の
   集合）は，そのまま $2^\omega$ の中で実行できる．

**補足（稠密性が使われる場所）．** $S$ の稠密性が本質的に使われるのは非アルキ
メデス的な側だけである．補題 3.11 の等長性の下からの評価では，
$\rho := h(s,t)$ に対し稠密性により $h(s,w_\alpha) < \rho$ なる
$w_\alpha \in S$ を選び，強三角不等式（超距離の三角形は二等辺）から
$h(t,w_\alpha) = \rho$ を得て，$r(n) < \rho$ なる添字の点対が $d_s$ と $d_t$
を距離 $\rho$ で分離する．アルキメデス的な側（補題 3.1 から系 3.9 まで）は
$S$ について「濃度 $\aleph_1$」と「非ボレル」しか使わない．

### 3.2 定理 3.3 — $\operatorname{Met}(Z)$ と $\operatorname{BMet}(Z)$ の言い分け〔C〕

本文の定理 3.3 は「$\operatorname{BMet}(Z)$ は $\operatorname{CPM}(Z)$ の
ボレル集合でない」を述べるが，概要と導入は同じ結果を
「$\operatorname{Met}(Z)$ はボレル集合でない」の形で引用している．両者はともに
真であり，同じ証明から出る．補題 3.2 は $\Phi([0,1] \setminus S)$ が
$\operatorname{Met}(Z)$ の閉集合であることを与え，構成した距離 $d_t$ は全て
有界だから，コンパクト集合 $L := \Phi([0,1])$ とのトレース恒等式

$$L \cap \operatorname{Met}(Z) = L \cap \operatorname{BMet}(Z) = \Phi([0,1] \setminus S)$$

が成り立つ．したがって $\operatorname{Met}(Z)$ と $\operatorname{BMet}(Z)$ の
どちらをボレルと仮定しても，$L \cong [0,1]$ へのトレースにより
$[0,1] \setminus S$ がボレルとなり，命題 2.1 に矛盾する．

これは数学的欠陥ではないが，$\operatorname{Met}(Z)$ 版の主張は本文のどこにも
現れない．改訂では両方を，または上のトレース恒等式から両方が同時に出る旨の
注意を，本文に明示することを勧める．

### 3.3 系 3.7 — 有界距離の空間には固有の転送補題が要る〔A・外部入力 [I1](3)，[Ko]〕

**主張．** $X$ 距離化可能：$\operatorname{BMet}(X)$ が完備距離化可能である
ことと $X$ が $\sigma$-コンパクトであることは同値．

**欠陥．** 印刷された証明は，Koshino の定理（$X$ 可分距離化可能：$X$ が
$\sigma$-コンパクト $\iff$ $AM(X)$ が完備距離化可能，ここで $AM(X)$ は有界
かつ両立する距離全体に上限距離を入れた空間，すなわち
$\operatorname{BMet}(X)$）[Ko] と系 3.6 を「組み合わせる」と述べる．
$(\Leftarrow)$ は問題ない（$\sigma$-コンパクトな距離化可能空間は可分であり，
Koshino の定理を適用すればよい）．$(\Rightarrow)$ では，Koshino の定理の可分性
の仮定に入るために「$\operatorname{BMet}(X)$ 完備距離化可能ならば $X$ 可分」
が必要だが，系 3.6 が与えるのは $\operatorname{Met}(X)$ 版であって
$\operatorname{BMet}(X)$ 版ではない．$\operatorname{BMet}(X)$ は
$\operatorname{Met}(X)$ の開かつ閉な部分集合（成分の和）だが，完備距離化可能性
はどちら向きにも自動では移らない．

**修正（[IU] 内の道具だけで足りる）．** 定理 3.5 の $\operatorname{BMet}$ 版を
補題として立てる：*$X$ 距離化可能で $\operatorname{BMet}(X)$ が
$\operatorname{CPM}(X)$ のボレル集合ならば，$X$ は可分である．* 証明は
定理 3.5 と同じ筋である．$X$ が非可分ならば閉離散部分空間 $Z \subseteq X$
（$\lvert Z \rvert = \aleph_1$）を取り，距離の等長拡張定理
[I1, Theorem 1.1] の (1)（拡張性），(2)（等長性），(3)
（$E(\operatorname{BMet}(A)) \subseteq \operatorname{BMet}(X)$）および
擬距離レベルの等長拡張 $\tilde{E} \colon \operatorname{CPM}(Z) \to
\operatorname{CPM}(X)$ を用いる．有界な距離の部分空間への制限は有界だから

$$E(\operatorname{BMet}(Z)) = \tilde{E}(\operatorname{CPM}(Z)) \cap \operatorname{BMet}(X)$$

が成り立ち，$\operatorname{CPM}(Z)$ は完備で $\tilde{E}$ は等長だから
$\tilde{E}(\operatorname{CPM}(Z))$ は $\operatorname{CPM}(X)$ の閉集合である．
$\operatorname{BMet}(X)$ がボレルならば上の共通部分は
$\operatorname{CPM}(X)$ のボレル集合であり，閉な像への位相同型 $\tilde{E}$ に
沿って引き戻すと $\operatorname{BMet}(Z)$ が $\operatorname{CPM}(Z)$ のボレル
集合となり，定理 3.3 に矛盾する．

この補題の下で $(\Rightarrow)$ は閉じる：$\operatorname{BMet}(X)$ 完備距離化
可能 $\Rightarrow$ Alexandrov–Lavrentiev（[Ke, Theorem 3.11]，全体空間の可分性
は不要）により $\operatorname{CPM}(X)$ の $G_\delta$ 集合 $\Rightarrow$ ボレル
$\Rightarrow$ 上の補題により $X$ 可分 $\Rightarrow$ Koshino の定理．

### 3.4 定理 3.8 — 貼り合わせの基底は完備な代表に取り替える〔A〕

**主張．** $Z$ 離散，$\lvert Z \rvert = \aleph_1$：$\operatorname{Met}(Z)$ の
任意の成分 $\mathfrak{c}$ に対し $\mathfrak{c} \cap \operatorname{Comp}(Z)$ は
$\operatorname{CPM}(Z)$ のボレル集合でなく，したがって
$\operatorname{Comp}(Z)$ もボレル集合でない．

**欠陥．** 印刷された証明は，定理 3.4 の構成 — 成分の代表 $d \in \mathfrak{c}$
と，濃度 $\aleph_1$ の閉球 $E$ の上に移した距離族 $e_t$ を，一点 $z$ で
貼り合わせた $m_t(x,a) = d(x,z) + e_t(z,a)$（$x \notin E$，$a \in E$）— を
そのまま用い，$t \notin S$ のとき $m_t$ が完備であると述べる．距離族の側は
正しい：$t \notin S$ のとき $e_t$ は完備である（クラスター間の距離が $4$
だから Cauchy 列は一つのクラスターに閉じ込められ，クラスター内の相異なる
2 点の距離は $\lvert t - w_\alpha \rvert > 0$ を下界に持つので，Cauchy 列は
最終的に定数になる）．しかし $E$ の外側で $m_t$ は**任意に取った代表 $d$ の
まま**であり，基底の未変更部分が完備でなければ $m_t$ も完備でない．実際，
$Z$ の可算部分集合が $\{1/n : n \ge 1\} \subseteq \mathbb{R}$ と等長になる
ような両立距離 $d$ を，この可算部分集合が閉球 $E$ の外に残るように取れば
（例えば $z$ から距離 $1$ の位置に $\aleph_1$ 個の点を置き，可算列を $z$ から
十分遠くに置けばよい），収束しない Cauchy 列がそのまま残り，どの $t$ に
ついても $m_t$ は完備でない．書かれた形の「$t \notin S$ ならば $m_t$ は完備」
は，このような成分 $\mathfrak{c}$ に対して偽である．

**修正．** 構成の前に，基底を同じ成分に属する完備な代表に取り替える．
$d'$ を対角線の外で $d' := d + 1$ と定めると，$d'$ は距離であり（三角不等式は
$d$ のものから従う），対角線外の距離が $1$ 以上だから離散位相を誘導して両立し，
Cauchy 列が最終的に定数になるので完備であり，しかも
$\mathcal{D}_Z(d, d') = 1 < \infty$ より $d' \in \mathfrak{c}$ である．基底
$d'$ で貼り合わせをやり直すと，$t \notin S$ のとき $m_t$ は完備になる：
$m_t$-Cauchy 列は，最終的に $E$ 内に留まる（$e_t$ の完備性により収束する）か，
さもなければ相異なる 2 点の距離が $1$ 以上の領域に出るので最終的に定数である．
基底の取り替え後も成分の所属は保たれる：$E^2$ 上では $e_t \le 4$ かつ $d'$ は
（$E$ が有限半径の閉球だから）有界，交差項では
$\lvert m_t(x,a) - d'(x,a) \rvert \le e_t(z,a) + d'(z,a)$ で右辺は有界，
$E$ の外では $m_t = d'$ だから，$\mathcal{D}_Z(m_t, d') < \infty$ であり，
$t \notin S$ のとき $m_t \in \mathfrak{c}$ である．証明の残りは変更なしに通る．

**「したがって」の部分．** $\operatorname{Comp}(Z)$ の非ボレル性は，非ボレル
集合 $\mathfrak{c} \cap \operatorname{Comp}(Z)$，あるいは非ボレルな
$\mathfrak{c}$（定理 3.4）との共通部分・包含関係からは従わない — 非ボレル
集合と交わること・それを含むことは，ボレル性について何も言わない．正しい
読み方は，パラメータ空間のコンパクトな像を経るトレース論法である．
$\Psi \colon [0,1] \to \operatorname{CPM}(Z)$，$\Psi(t) = m_t$ をパラメータ
写像，$L' := \Psi([0,1])$ をそのコンパクトな像とすると，$t \in S$ では $m_t$
は両立せず $\operatorname{Met}(Z)$ にすら入らず，$t \notin S$ では上で確認した
通り $m_t \in \mathfrak{c} \cap \operatorname{Comp}(Z)$ だから，

$$L' \cap \operatorname{Comp}(Z) = L' \cap (\mathfrak{c} \cap \operatorname{Comp}(Z)) = \Psi([0,1] \setminus S)$$

が成り立つ．よって $\operatorname{Comp}(Z)$（または
$\mathfrak{c} \cap \operatorname{Comp}(Z)$）がボレルならば，
$L' \cong [0,1]$ へのトレースにより $[0,1] \setminus S$ がボレルとなり矛盾する．

**定理 3.16 との対比．** 非アルキメデス版の定理 3.16 の証明は，この正規化を
最初から行っている：$c \in R \setminus \{0\}$ を固定し，基底を対角線の外で
$d \vee c$ に取り替える（完備かつ両立する $R$-値超距離であり，
$\mathcal{UD}^R_Z(d \vee c, d) \le c$ だから同じ $R$-成分に留まる）．このため
定理 3.16 に同種の欠陥は生じない．定理 3.8 の修正は，この正規化の
アルキメデス版（max を和に替えたもの）に他ならない．

### 3.5 系 3.9 — 拡張定理の完備性保存は $X$ の完備距離化可能性の下で〔B〕

**主張（系 3.9）．** $X$ **完備距離化可能**：$\operatorname{Comp}(X)$ が
$\operatorname{CPM}(X)$ のボレル集合ならば $X$ は可分．

系 3.9 の証明は，[I1, Theorem 1.1] の主張 (4)
「$E(\operatorname{Comp}(A)) \subseteq \operatorname{Comp}(X)$」を使う．この
主張は文字通りには $X$ への仮定なしに述べられているが，無条件では成立しない：
$\operatorname{Comp}(X) = \emptyset$ かつ
$\operatorname{Comp}(A) \neq \emptyset$ となる例（$X = \mathbb{Q}$，
$A = \{0\}$）があるからである．出典の証明を確認すると，完備性保存は補助的な
完備距離の選択を経ており，その選択は「$X$ が完備距離化可能」という仮定の下で
行われている．すなわち (4) は「$X$ が完備距離化可能ならば」という条件付きで
読むべきである．

系 3.9 は $X$ の完備距離化可能性を仮定しているから，条件付きの (4) で十分で
あり，系自体は（定理 3.8 の修正を前提として）正しい．確認した証明の筋：
$X$ が非可分ならば閉離散 $Z$（$\lvert Z \rvert = \aleph_1$）を取り，(4) より
$E(\operatorname{Comp}(Z)) \subseteq \operatorname{Comp}(X)$．逆向きには，
$X$ 上の完備な両立距離の閉集合 $Z$ への制限は完備かつ両立だから

$$E(\operatorname{Comp}(Z)) = E(\operatorname{Met}(Z)) \cap \operatorname{Comp}(X)$$

であり，$E(\operatorname{Met}(Z))$ は $\operatorname{Met}(X)$ の閉集合だから，
左辺は $\operatorname{Comp}(X)$ の閉集合で $\operatorname{Comp}(Z)$ と等長で
ある．同じ制限の議論を擬距離レベルで行うと，$\tilde{E}(d)|_{Z^2} = d$ から
$\tilde{E}^{-1}(\operatorname{Comp}(X)) = \operatorname{Comp}(Z)$ が従う
（$\supseteq$ は (4)，$\subseteq$ は制限の完備性・両立性による）．よって
$\operatorname{Comp}(X)$ がボレルならば，閉な像への位相同型 $\tilde{E}$ に
沿った引き戻し（§3.3 と同じ論法）により $\operatorname{Comp}(Z)$ が
$\operatorname{CPM}(Z)$ のボレル集合となり，定理 3.8 に矛盾する．

要点は二つである：外部定理の (4) を無条件には引用しないこと，および [I1] 側
にも仮定の明記を提案することである．

### 3.6 定理 3.14 — 引用定理は擬超距離レベルの拡張を与えず，閉包を経る転送で修復する〔A（原因は外部定理の適用範囲）〕

これが最も重要な補正である．

**主張．** $Y$ 超距離化可能，$R$ characteristic：$\operatorname{UMet}(Y;R)$ が
$\operatorname{UCPM}(Y;R)$ のボレル集合ならば $Y$ は可分．

**印刷された証明で成立している部分．** $Y$ が非可分ならば，分離集合の議論に
より閉離散部分空間 $Z \subseteq Y$（$\lvert Z \rvert = \aleph_1$）が取れる．
超距離の拡張定理 [I2, Theorem 4.7] は，写像
$\Sigma \colon \operatorname{Met}(Z) \to \operatorname{Met}(Y)$ であって
(1) 拡張性 $\Sigma(d)|_{Z^2} = d$，(2) $\mathcal{UD}^R$ に関する等長性，
(5) $\Sigma(\operatorname{UMet}(Z;R)) \subseteq \operatorname{UMet}(Y;R)$ を
満たすものを与える．$E$ をその $\operatorname{UMet}(Z;R)$ への制限とすると，
$E \colon \operatorname{UMet}(Z;R) \to \operatorname{UMet}(Y;R)$ は等長で，
像は $\operatorname{UMet}(Y;R)$ の閉集合であり，各 $R$-成分 $\mathfrak{c}^R$
の像 $E(\mathfrak{c}^R)$ も $\operatorname{UMet}(Y;R)$ の閉集合で
$\mathfrak{c}^R$ と等長である．ここまでは正しい．

**欠陥．** 最終段「$\operatorname{UMet}(Y;R)$ がボレルならば定理 3.13 に矛盾」
には，ボレル性を $\operatorname{UCPM}(Y;R)$ から $\operatorname{UCPM}(Z;R)$
へ引き戻す論法が要る．アルキメデス版（定理 3.5）では [I1] の拡張が擬距離
レベル $\tilde{E} \colon \operatorname{CPM}(Z) \to \operatorname{CPM}(X)$
まで伸びており，全体空間どうしの等長写像（閉な像への位相同型）に沿って
ボレル性が引き戻せた．ところが [I2, Theorem 4.7] の $\Sigma$ の定義域は
$\operatorname{Met}(Z)$ であり，**この定理は
$\operatorname{UCPM}(Z;R) \to \operatorname{UCPM}(Y;R)$ のレベルの拡張を
与えない**．$E$ は部分空間 $\operatorname{UMet}(Z;R)$ の間の等長写像に
過ぎず，「$\operatorname{UCPM}(Y;R)$ におけるボレル性」は部分集合
$E(\mathfrak{c}^R)$ に内在的な性質ではない（どんな空間も自分自身の中では閉で
ある）から，$E$ だけでは全体空間のボレル $\sigma$-代数を運べない．したがって
印刷された最終段はそのままでは従わない．

**修正（閉包とコンパクト性による転送）．** $R$-成分ではなく，パラメータ空間の
コンパクトな像で議論する．定理 3.13 の構成のパラメータ写像を
$\Psi \colon 2^\omega \to \operatorname{UCPM}(Z;R)$ とする（$\Psi$ は
$(2^\omega, h)$ からの等長写像であり，$\Psi(t) \in \operatorname{UMet}(Z;R)
\iff t \notin S$，$\Psi(2^\omega \setminus S)$ は $\operatorname{UMet}(Z;R)$
の閉集合である）．

$$F := E(\Psi(2^\omega \setminus S)), \qquad \iota := E \circ \Psi \colon (2^\omega \setminus S,\, h) \to F$$

とおく．$E$ は $\operatorname{UMet}(Z;R)$ から閉な像への位相同型だから $F$ は
$\operatorname{UMet}(Y;R)$ の閉集合であり，$\iota$ は等長写像である．

**補題（$\operatorname{UCPM}(Y;R)$ の完備性）．** $R$ が characteristic なら
ば，$\operatorname{UCPM}(Y;R)$ は $\mathcal{UD}^R_Y$（に付随する距離
$\min\{\mathcal{UD}^R_Y, 1\}$）について完備である．

*証明．* (i) $\varepsilon \in R \setminus \{0\}$ とし
$\mathcal{UD}^R_Y(d,e) < \varepsilon$ とすると，$\inf$ の定義から，各点で
$d \le e \vee \varepsilon$ かつ $e \le d \vee \varepsilon$ が成り立つ
（定義の集合に属する $\varepsilon' < \varepsilon$ が取れるから）．各点対で
$d \le e$ または $d \le \varepsilon$ だから $d - e \le \varepsilon$，対称に
$e - d \le \varepsilon$，すなわち $\lvert d - e \rvert \le \varepsilon$
（各点）．よって $\mathcal{UD}^R$-Cauchy 列 $(d_k)$ は一様 Cauchy であり，
一様極限 $d_\infty$ が存在して連続な擬距離になる．強三角不等式は各点の
max-不等式の極限として保たれる．
(ii) $d_\infty$ は $R$-値である：点対 $(x,y)$ を固定し
$v_k := d_k(x,y) \in R$，$v := \lim v_k$ とする．$v = 0$ ならば $v \in R$．
$v > 0$ ならば，$R$ が characteristic だから
$\varepsilon \in R \setminus \{0\}$，$\varepsilon < v$ が取れる．十分大きい
$j,k$ では $v_j, v_k > \varepsilon$ かつ（(i) の各点不等式から）
$v_k \le v_j \vee \varepsilon$，$v_j \le v_k \vee \varepsilon$ であり，
$v_k > \varepsilon$ から $v_k \le v_j$，対称に $v_j \le v_k$，ゆえに
$v_j = v_k$．すなわち値は最終的に一定であり $v \in R$．
(iii) $\mathcal{UD}^R_Y(d_j, d_\infty) \to 0$：
$\varepsilon \in R \setminus \{0\}$ を任意に取ると，十分大きい $j$ と全ての
$k \ge j$ で（(i) と同様に）各点 $d_j \le d_k \vee \varepsilon$ かつ
$d_k \le d_j \vee \varepsilon$．$k \to \infty$ として
$d_j \le d_\infty \vee \varepsilon$ かつ $d_\infty \le d_j \vee \varepsilon$，
すなわち $\mathcal{UD}^R_Y(d_j, d_\infty) \le \varepsilon$．$\varepsilon$ は
$R \setminus \{0\}$ の中でいくらでも $0$ に近く取れる．∎

$2^\omega \setminus S$ はコンパクト集合
$P := \operatorname{cl}_{2^\omega}(2^\omega \setminus S)$ において稠密であり，
$\iota$ は完備空間 $\operatorname{UCPM}(Y;R)$ への（一様連続な）等長写像だ
から，閉包 $P$ 上の写像

$$\bar{\iota} \colon (P, h) \to \operatorname{UCPM}(Y;R)$$

に一意に連続拡張される．等長性は二つの距離関数の連続性により閉包に伝わり，
特に $\bar{\iota}$ は単射である．$K := \bar{\iota}(P)$ はコンパクトで，
$\bar{\iota} \colon P \to K$ は位相同型である．

**主張（トレース恒等式）．** $K \cap \operatorname{UMet}(Y;R) = F$．

*証明．* $\supseteq$ は構成から従う（$2^\omega \setminus S$ 上で
$\bar{\iota} = \iota$）．$\subseteq$：$t \in P$，
$\bar{\iota}(t) \in \operatorname{UMet}(Y;R)$ とする．
$t_k \in 2^\omega \setminus S$，$t_k \to t$ を取ると
$\iota(t_k) \to \bar{\iota}(t)$ であり，この収束は
$\operatorname{UMet}(Y;R)$ の中で起きている．$F$ は
$\operatorname{UMet}(Y;R)$ の閉集合だから
$\bar{\iota}(t) \in F = \iota(2^\omega \setminus S)$ であり，$\bar{\iota}$ の
単射性より $t \in 2^\omega \setminus S$．∎

**結論．** $\operatorname{UMet}(Y;R)$ が $\operatorname{UCPM}(Y;R)$ のボレル
集合であると仮定すると，$F = K \cap \operatorname{UMet}(Y;R)$ はコンパクト
距離空間（したがってポーランド空間）$K$ のボレル集合であり（トレース，
§2.2），位相同型 $\bar{\iota}$ で引き戻すと
$P \setminus S = 2^\omega \setminus S$ が $P$ のボレル集合となる．$P$ は
$2^\omega$ の閉集合だから $2^\omega \setminus S$ は $2^\omega$ のボレル集合
となり，命題 2.2 に矛盾する．なお $S$ の補集合の稠密性は仮定していない．
閉包 $P$ に移って議論することで，この点は自動的に処理される．

**注意（誤った近道）．** 「可分距離化可能空間は，それを含むどの距離化可能空間
においてもボレルである」という形の補題を使えば転送は一行で済むように見える
が，この主張は偽である．実際 $F$ は $2^\omega \setminus S$ と等長であり，
$2^\omega \setminus S$ は $2^\omega$ のボレル集合でない．正しい転送は上の
閉包・コンパクト性の議論による．

### 3.7 系 3.15 と系 3.17 — 修復した経路の継承〔3.15: 継承 + C，3.17: A（継承）+ 外部入力 [I2](N1)〕

**系 3.15．** $Y$ 超距離化可能：$\operatorname{UMet}(Y;R)$ が完備距離化可能
ならば $Y$ は可分．証明は原稿では省略されているが，意図されている筋は明快で
ある：完備距離化可能な部分空間は距離化可能な全体空間の $G_\delta$ 集合
（Alexandrov–Lavrentiev，[Ke, Theorem 3.11]．全体空間の可分性は不要）だから
$\operatorname{UMet}(Y;R)$ は $\operatorname{UCPM}(Y;R)$ のボレル集合となり，
定理 3.14（修正済みの経路）に帰着する．改訂では引用を付して一文を追加する
ことを勧める（証明が同様に省略されている系 3.6 も同じ）．

**系 3.17．** $Y$ 超距離化可能，$\operatorname{UComp}(Y;R) \neq \emptyset$：
$\operatorname{UComp}(Y;R)$ がボレル（または完備距離化可能）ならば $Y$ は
可分．確認した筋は次の通りである．$\operatorname{UComp}(Y;R) \neq \emptyset$
から $Y$ は完備距離化可能である（その元は $Y$ 上の完備な両立距離である）．
[I2, Theorem 4.7] の追加主張 (N1) により，$Y$ が完備距離化可能ならば補助
データを選んで $\Sigma$ が完備性を保存するようにでき，本稿の記法で
$E(\operatorname{UComp}(Z;R)) \subseteq \operatorname{UComp}(Y;R)$ を得る
（(N1) は [I1] の (4) と異なり，この仮定を明記して述べられているので §3.5 の
種類の問題はない）．逆向きの包含は，完備な両立超距離の閉部分空間 $Z$ への
制限が完備かつ両立であることから

$$E(\operatorname{UComp}(Z;R)) = E(\operatorname{UMet}(Z;R)) \cap \operatorname{UComp}(Y;R)$$

であり，閉性と等長性はこれまでと同様で，定理 3.16 に帰着する．

ただし最後の帰着には定理 3.14 と同じ全体空間の転送の問題がそのまま現れるから，
**系 3.17 も §3.6 の閉包による転送を継承し，迂回はできない**．$\Psi$ を
定理 3.16 の構成のパラメータ写像に置き換えれば同じ議論が通る：$t \in S$ では
構成した距離が $\operatorname{UMet}(Z;R)$ に入らないことから，対応する
トレース恒等式 $K \cap \operatorname{UComp}(Y;R) = F$ も同様に成り立つ．

## 4. 原稿への修正・明確化の提案

1. **命題 2.2** — 証明を §3.1 の修正 1 または 2 に差し替える．Borel 同型を
   残す場合は [Ke, Theorem 15.6] を引用する．
2. **定理 3.3** — 概要・導入で引用している $\operatorname{Met}(Z)$ 版を本文
   にも明示する（トレース恒等式から $\operatorname{BMet}$ 版と同時に得られる
   旨の注意で足りる）．
3. **系 3.7** — 定理 3.5 の $\operatorname{BMet}$ 版（§3.3 の補題）を追加し，
   $(\Rightarrow)$ の導出をそれ経由に改める．また Koshino の定理の引用番号
   （"Corollary 1.2"）は出版版と照合することを勧める（確認した本文では主結果
   に番号が付されていない）．
4. **定理 3.8** — 貼り合わせの前に基底を（対角線の外で）$d + 1$ に取り替える
   正規化を追加する．「したがって $\operatorname{Comp}(Z)$ もボレルでない」の
   部分がトレース恒等式経由であることを明示する．
5. **[I1, Theorem 1.1] の主張 (4)** — 「$X$ 完備距離化可能ならば」を条件と
   して明記する（[I1] 側への報告も提案する）．系 3.9 では $X$ にこの仮定が
   あるので結論に影響しない．
6. **定理 3.14** — 最終段に §3.6 の転送論法（$\operatorname{UCPM}(Y;R)$ の
   完備性の補題，閉包への等長拡張，トレース恒等式）を追加する．
7. **系 3.6・系 3.15** — Alexandrov–Lavrentiev（[Ke, Theorem 3.11]）の引用を
   付して導出を一文で明示する．
8. **系 3.17** — 全体空間の転送が定理 3.14 の修正を継承することを明示する．

## 5. 検証の範囲と外部入力

**直接確認した部分．** [IU] 内部の全ての証明：命題 2.1・2.2（§3.1 の修正込み），
補題 3.1・3.2・3.10・3.11，定理 3.3・3.4・3.5・3.8（§3.4 の修正込み）・3.12・
3.13・3.14（§3.6 の修正込み）・3.16，系 3.6・3.7（§3.3 の修正込み）・3.9・
3.15・3.17，および §2.2 に挙げた非可分な全体空間でのボレル集合の操作．暗黙に
使われる標準的事実（非可分距離空間における $\varepsilon$-分離集合の存在と
その閉離散性，$\operatorname{CPM}(X)$ の完備性，距離の一点での貼り合わせ，
成分が開かつ閉であること，完備距離の閉部分空間への制限の完備性，$\aleph_1$
の正則性）も個別に再導出して確認した．

**外部入力として使う定理．** 以下は出典の主張を（§3.5 で述べた条件の明確化を
除き）そのまま入力として使う．

- 距離の等長拡張定理 [I1, Theorem 1.1]．定理 3.5 と系 3.7 は (1)(2)(3) と
  擬距離レベルの拡張 $\tilde{E}$ を，系 3.9 はさらに (4)（$X$ 完備距離化可能
  の下で）を使う．
- 超距離の拡張定理 [I2, Theorem 4.7]（距離空間の分解定理の帰結）．定理 3.14
  は (1)(2)(5) を，系 3.17 はさらに (N1) を使う．定義域が
  $\operatorname{Met}(F)$ であることに §3.6 の通り注意する．
- Koshino の定理 [Ko]（系 3.7）：$X$ 可分距離化可能のとき，$X$ が
  $\sigma$-コンパクトであることと $AM(X)$ が完備距離化可能であることは同値．
- 標準的な記述集合論 [Ke]：ボレル集合の完全集合定理（Theorem 13.6），
  ベルンシュタイン集合の存在（Example 8.24 の証明中の構成），Borel 同型定理
  （Theorem 15.6），Alexandrov–Lavrentiev の $G_\delta$ 特徴付け
  （Theorem 3.11．使うのは「完備距離化可能な部分空間は $G_\delta$」の向き
  のみで，全体空間の可分性は不要）．

## 参考文献

- [IU] Y. Ishiki and T. Uda, *Borelness of moduli spaces of metrics implies
  separability*, arXiv:2608.19618v1 (2026).
- [I1] Y. Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030v4.
- [I2] Y. Ishiki, *A factorization of metric spaces*, Colloq. Math. 174
  (2023), 101–120. arXiv:2212.13409.
- [Ko] K. Koshino, *On the Borel complexity and the complete metrizability of
  spaces of metrics*, Anal. Geom. Metr. Spaces 12 (2024).
- [Ke] A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in
  Mathematics 156, Springer, 1995.
