# 距離のモジュライ空間のボレル性と可分性：2026-08-27 受領原稿に関する覚書

**対象:** Y. Ishiki and T. Uda, *Borelness of Moduli Spaces of Metrics Implies
Separability*，2026 年 8 月 27 日の内部タイムスタンプをもつ受領原稿（以下
[M]）．公開されているプレプリント arXiv:2608.19618v1（以下 [IU]）の後継となる
未公開の作業稿である．arXiv に登録されているのは v1 のみであり，[M] を
「arXiv v2」と呼ぶことはできない．2026 年 9 月．

本ノートは，[M] の全ての命題・定理・系について，主張と証明を一つずつ再検討した
結果をまとめたものである．

**先行する覚書との関係．** [IU] に対する同種の覚書（以下 v1 覚書）は v1 の記録
としてそのまま有効であり，本ノートはその後継であって置き換えではない．v1 覚書
が指摘した各項目が [M] でどうなったかは §2 に整理する．

**記法とラベル．** 空間の記法 $\operatorname{CPM}$，$\operatorname{Met}$，
$\operatorname{BMet}$，$\operatorname{Comp}$，$\operatorname{UCPM}$，
$\operatorname{UMet}$，$\operatorname{UComp}$，上限距離 $\mathcal{D}_X$，
非アルキメデス的一様距離 $\mathcal{UD}^R_Y$，および有限距離の同値類としての
**成分** は [M] のものをそのまま用いる．range set と characteristic も [M] に
従い英語のまま用いる（$0 \in R \subseteq [0,\infty)$ を range set と呼び，$0$ が
$R \setminus \{0\}$ の集積点であるとき characteristic という）．[IU] から [M]
への改訂で §2 に十一個，§3 に五個の主張が挿入され，定理番号は全て移動した．
そこで本ノートは番号ではなく [M] のラベル（`thm:borel-separability` など）で
参照する．

## 1. 要約

結論は次の通りである．

**[M] に偽の主張は見つからなかった．** v1 覚書が挙げた四種類の証明の欠陥
（五箇所）は [M] で全て解消されている．そのうち二つは v1 覚書が示した修正
そのものが取り込まれ，一つは別の修正で取り込まれて妥当であり，超距離側の二つは
証明の経路ごと，より強い新しい定理に置き換えられて解消した．

実質的に加わったのは次の四点である．

- 離散空間の成分定理が $\lvert Z \rvert \ge \aleph_1$ に強化され，そのために
  **非可分な距離化可能空間 $X$ に対する $\operatorname{Met}(X)$ の非ボレル性**
  が一般の形で得られた（`cor:nonseparable-metric-nonborel`）．
- 同じことが超距離側でも，全体空間の間でボレル性を移送することなく得られた
  （`cor:nonseparable-ultrametric-nonborel`）．
- $\operatorname{BMet}(X)$ の完備距離化可能性と $X$ の $\sigma$-コンパクト性の
  同値性が，$\operatorname{Met}(X)$ と成分を含む五条件の同値性に強化された．
- カントール空間のパラメータ集合が，稠密性だけでなく補集合の稠密性まで満たす
  形に強化された．これにより超距離側の新しい経路が取れる．

一方，v1 から [M] への改訂の過程で，v1 では健全だった箇所が一つ壊れており，
**原稿側の修正を要する**．`thm:borel-separability` の仮定が
$\operatorname{Met}(X)$ のボレル性から $\operatorname{BMet}(X)$ のボレル性に
述べ直された際に，
`cor:metric-space-complete-separability` の証明が更新されず，
$\operatorname{Met}(X)$ のボレル性からこの定理を直接引く形になっている（§5）．
系の主張は正しく，直前の `cor:nonseparable-metric-nonborel` の対偶により一行で
修復できる．

このほか，導入部の相互参照，系の仮定の不一致，引用形式，引用元への注意など，
§6 に計七件の書き換えを提案する．いずれも数学的欠陥ではない．

## 2. v1 との関係と取り込まれた修正

### 2.1 受領原稿と番号の移動

[M] は [IU] の後に作成された未公開の作業稿である．本ノートでは
**2026-08-27 受領原稿**（または単に受領原稿）と呼ぶ．

番号が全て動いた理由は次の通りである．[IU] の §2 は番号付きの環境を二つ（二つの
命題）しか含まなかったのに対し，[M] の §2 は十三個を含み，二つの命題はその末尾
に移った．§3 にも五個の主張が挿入されたため，§3 の番号も全て繰り下がっている．

### 2.2 v1 覚書が挙げた欠陥とその解消

| v1 覚書 | 欠陥 | [M] における解消 |
|---|---|---|
| 命題 2.2（`prop:dense-aleph1-nonborel-cantor`） | Borel 同型に沿って稠密性を移していた | **そのまま取り込まれ，さらに強化された** |
| 系 3.7（`cor:bounded-metric-complete-sigma-compact`） | $(\Rightarrow)$ に $\operatorname{BMet}$ 版のボレル性・可分性の移送が必要だった | **そのまま取り込まれた** |
| 定理 3.8（`thm:complete-metric-nonborel`） | 完備とは限らない基底距離の上で貼り合わせを完備と主張していた | **別の修正で取り込まれ，妥当である** |
| 定理 3.14（`thm:ultrametric-borel-separability`） | $\operatorname{UCPM}$ 版の拡張子が無く，全体空間の間でボレル性を引き戻せなかった | **より強い結果に置き換えられ，解消した** |
| 系 3.17（`cor:complete-ultrametric-borel-separability`） | 同じ全体空間の間の移送の欠陥 | **同上** |

**`prop:dense-aleph1-nonborel-cantor`．** [M] の証明は Borel 同型を Borel 構造
と濃度にのみ使い，稠密性は $S$ に含ませた可算稠密集合から別途供給する．これは
v1 覚書が示した修正そのものである．さらに，互いに素な第二の可算稠密集合を
Borel 同型の像の外に置くことで補集合の稠密性まで得ており，これは v1 覚書の要求
を超える強化である（§3.4）．v1 覚書が要望した引用も付いた．

**`cor:bounded-metric-complete-sigma-compact`．** v1 覚書の修正案は「移送定理の
$\operatorname{BMet}$ 版を補題として立て，成分を経由せずに
`thm:bounded-discrete-nonborel` に直接矛盾させる」ことであった．[M] はまさに
それを行い，しかも $\operatorname{BMet}$ 版を `thm:borel-separability` そのもの
に昇格させている．その代償が §5 の名称の齟齬である．

**`thm:complete-metric-nonborel`．** v1 覚書の修正案は基底距離を対角線の外で
$d + 1$ に取り替えることであった．[M] は対角線の外で $d \vee 1$ に取り替える．
どちらも両立し，完備で，一様離散であり，$\mathcal{D}_Z \le 1$ の範囲にあるから
同じ成分に留まる．「したがって $\operatorname{Comp}(Z)$ もボレルでない」の段も
v1 覚書の処方（コンパクトな像を経るトレース論法）とは異なり，[M] は
$\operatorname{CPM}(Z)$ における $d$ の有限距離類との共通部分を取る．この類は
$\operatorname{CPM}(Z)$ で開かつ閉だから，ボレル集合の相対的に開な部分集合が
ボレルであることがそのまま使える．どちらも妥当である．

**`thm:ultrametric-borel-separability` と
`cor:complete-ultrametric-borel-separability`．** v1 の欠陥は，超距離の拡張定理
が擬超距離全体の空間の上の拡張を与えないため，全体空間の Borel $\sigma$-代数を
拡張子の像に沿って運べない，という点にあった．[M] はこの証明を修理するのでは
なく，経路ごと `cor:nonseparable-ultrametric-nonborel` に置き換える（§3.5）．
新しい経路では拡張はコンパクトなカントール空間の**全体**の上で作られ，引き戻し
は拡張子の像ではなく成分に対して取られるので，全体空間の間の移送が現れない．
二つの主張はその帰結として従う．v1 覚書が構成した修正は，あくまで v1 の本文に
対して検証された記録として残る．

### 2.3 欠陥に至らない指摘について

v1 覚書が付した明確化・補足の要望も，ほとんどが [M] に反映されている．距離の
等長 extensor 定理の完備性保存の主張には「$X$ が完備距離化可能ならば」という
条件が明記され（§4），$2^\omega$ と $[0,1]$ の Borel 同型には引用が付き，
Alexandrov–Lavrentiev の $G_\delta$ 特徴付けは番号付きの定理として明示的に
引用されるようになった．v1 では概要と導入だけにあって本文に無かった
$\operatorname{Met}(Z)$ 版の非ボレル性も，`cor:discrete-metric-nonborel` の
(2) として本文に置かれた（ただし導入部の引用先は §6(b) の通り依然として成分
定理である）．移送定理の証明で暗黙だった引き戻しの段については，[M] は拡張子に
沿った四つの引き戻し等式と，連続写像による引き戻しの障害を，それぞれ独立した
補題として立てている．v1 で暗黙に使われていた標準的事実（分離集合の抽出，
全体空間の完備性，one-point amalgamation）も明示された．とくに v1 覚書が自前で
証明しなければならなかった $\operatorname{UCPM}(Y;R)$ の完備性は，[M] では引用
付きの補題になっている．

残っているのは二点である．一つは成分定理の証明の暗黙のステップで，貼り合わせた
距離の両立性の同値性と，符号化の中心を含む部分集合の取り方が，依然として明示
されていない．どちらも直ちに埋まる記述上の要望である（§6(g)）．もう一つは
Koshino の定理の引用番号であり，出版版との照合が残っている（§6(f)）．[M] に
残る数学的な欠陥は §5 の一件のみである．

## 3. 強化された定理群

### 3.1 離散空間の成分定理：$\lvert Z \rvert \ge \aleph_1$

**主張（`thm:metric-component-nonborel`）．** $Z$ を離散空間，
$\lvert Z \rvert \ge \aleph_1$ とする．$\operatorname{Met}(Z)$ の任意の成分
$\mathfrak{c}$ は $\operatorname{CPM}(Z)$ のボレル集合でない．

v1 では $\lvert Z \rvert = \aleph_1$ が仮定されていた．弱めるために変更を要する
のは一箇所だけである．$d \in \mathfrak{c}$ と $z \in Z$ を固定すると
$Z = \bigcup_{h \ge 0} B(z, 2^h; d)$ は可算和だから，$Z$ が非可算ならばある閉球
$L$ が非可算であり，$\aleph_1$ の極小性からその濃度は $\aleph_1$ 以上である．
そこで $z \in H \subseteq L$ を $\lvert H \rvert = \aleph_1$ となるように取る
（$z \in L$ は常に成り立ち，$z$ を付け加えても濃度は変わらない）．以降は v1 の
議論を，閉球そのものではなく $H$ の上で行えばよい．符号化した距離を $H$ に
移し，$(Z \setminus H) \cup \{z\}$ 上の $d$ と $z$ で one-point amalgamation
した $m_t$ について，成分の評価と双 Lipschitz 評価，および引き戻し等式が
そのまま再現する．

**この形が必要な理由．** 非可分な $(X,d)$ に対する
`cor:nonseparable-metric-nonborel` は，この定理を極大 $\varepsilon$-分離集合に
適用する．極大 $\varepsilon$-分離集合として得られるのは「非可算」であって
「濃度がちょうど $\aleph_1$」ではなく，濃度 $\aleph_1$ の部分集合に取り替えると
成分の評価が要求する $\varepsilon$-ネット性が壊れる．$\ge \aleph_1$ の形は，
次節の証明が実際に用いる形である．

**系（`cor:discrete-metric-nonborel`）．** $\lvert Z \rvert = \aleph_1$ の下で，
成分の非ボレル性に加えて $\operatorname{Met}(Z)$ 自身も
$\operatorname{CPM}(Z)$ のボレル集合でない．成分は $\operatorname{Met}(Z)$ で
開だから，$\operatorname{Met}(Z)$ がボレルならば各成分もボレルとなる．これが，
v1 では概要と導入だけに現れて本文に無かった $\operatorname{Met}(Z)$ 版である．

### 3.2 非可分な距離化可能空間：$\operatorname{Met}(X)$ の非ボレル性

**主張（`cor:nonseparable-metric-nonborel`）．** $X$ を非可分な距離化可能空間と
する．(1) $\operatorname{Met}(X)$ の任意の成分は $\operatorname{CPM}(X)$ の
ボレル集合でない．(2) $\operatorname{Met}(X)$ 自身もボレル集合でない．

これが [M] の第一の新しい主結果である．非可分性から取り出せるのは $X$ の閉離散
部分集合 $Z$ の上の情報であり，§3.1 はその $Z$ の上で成分の非ボレル性を与える．
問題は，それを $X$ の側の指定された成分 $\mathfrak{c}_X$ に運ぶことである．等長
extensor 定理は，閉部分集合の上の距離を $X$ 上の距離に等長に拡張するが，その
拡張が $\operatorname{Met}(X)$ のどの成分に属するかについては何も述べない．
成分ごとの主張を得るには，定理の主張だけでは足りない．

[M] の解決は，定理が与える任意の拡張子を用いるのではなく，その証明の中の構成に戻り，
$d|_{Z^2}$ とその拡張 $d$ を基底距離に取ってその構成を改めて行うことである．
こうして得られる拡張子は，定理として述べられている性質に加えて点評価
$r(x,a) \le 4\,d(x,a) + 1$（$x \in X$，$a \in Z$，$r = E(d|_{Z^2})$）を満たす
（§4）．そして $Z$ を単なる閉離散集合ではなく $\varepsilon$-ネットに取っておけば，
この点評価が拡張を $\mathfrak{c}_X$ の中に留める．

詳細は次の通りである．成分 $\mathfrak{c}_X$ と $d \in \mathfrak{c}_X$ を固定し，
$(X,d)$ が可算な $\varepsilon$-ネットを持たないような $\varepsilon > 0$ を取って，
極大 $\varepsilon$-分離集合 $Z$ を取る．$Z$ は非可算，閉，離散であり，かつ
$\varepsilon$-ネットである．$d|_{Z^2}$ は離散空間 $Z$ 上の両立距離であり，その
成分 $\mathfrak{c}_Z$ は §3.1 の $\ge \aleph_1$ 版により $\operatorname{CPM}(Z)$
で非ボレルである．上の構成から得た $r = E(d|_{Z^2})$ について，$Z$ が
$\varepsilon$-ネットであることから各 $x$ に $d(x,a_x) < \varepsilon$ なる
$a_x \in Z$ が取れ，$r = d$ が $Z^2$ 上で成り立つので，三角不等式を両向きに
使って各点で $\lvert r - d \rvert < 10\varepsilon + 2$ を得る．よって
$\mathcal{D}_X(r,d) < \infty$，すなわち $r \in \mathfrak{c}_X$ である．
$\mathfrak{c}_X$ が $E(d|_{Z^2})$ の成分に他ならないから，擬距離版の拡張子
$\tilde{E}$ に沿った**厳密な引き戻し等式**
$\tilde{E}^{-1}(\mathfrak{c}_X) = \mathfrak{c}_Z$ が成り立ち，連続写像による
引き戻しの障害から (1) が従う．(2) は，成分が $\operatorname{Met}(X)$ で開である
ことから (1) に帰着する．

### 3.3 五条件の同値性

**主張（`cor:bounded-metric-complete-sigma-compact`）．** $X$ を距離化可能空間
とする．次の五つは同値である．

1. $\operatorname{Met}(X)$ が完備距離化可能．
2. $\operatorname{BMet}(X)$ が完備距離化可能．
3. $\operatorname{Met}(X)$ の全ての成分が完備距離化可能．
4. $\operatorname{Met}(X)$ のある成分が完備距離化可能．
5. $X$ が $\sigma$-コンパクト．

v1 では (2) と (5) の同値性であった．初等的な含意は次の通りである．成分は
開かつ閉だから，完備距離化可能な空間の閉部分空間として (1) $\Rightarrow$ (3)．
$\operatorname{Met}(X)$ はその成分の位相和であり，完備距離化可能空間の位相和は
完備距離化可能だから (3) $\Rightarrow$ (1)．有界な両立距離はちょうど一つの成分
をなし，$\min\{d,1\}$ によりそれは空でないから (3) $\Rightarrow$ (2)．全ての成分が
完備距離化可能なら，とりわけ固定した $d$ を含む成分がそうだから (3) $\Rightarrow$ (4)．
(2) $\Rightarrow$ (5) は，完備距離化可能性から $G_\delta$，したがってボレル性を
得て，$\operatorname{BMet}$ 版の `thm:borel-separability` で可分性を出し，
Koshino の定理を適用する．これが v1 の系 3.7 の欠陥の解消である．

残る二方向が新しい．以下の順に述べる．

**方向 A：(5) $\Rightarrow$ (3)．** $d$ を固定し，
$P_d = \{p \in \operatorname{CPM}(X) : \mathcal{D}_X(p,d) < \infty\}$ とおく．
$\mathcal{D}_X$-Cauchy 列は切り詰めた距離についても Cauchy だから
$\operatorname{CPM}(X)$ の中で収束し，極限は $d$ から有限距離に留まる．よって
$P_d$ は完備距離化可能である．$o \in X$ を固定して
$A_n = B(o, 2^n; d)$ とおくと，$A_n$ は閉であり，$X$ が $\sigma$-コンパクトなら
$A_n$ も $\sigma$-コンパクト，したがって可分である．Koshino の定理により
$\operatorname{BMet}(A_n)$ は完備距離化可能であり，$\operatorname{BCPM}(A_n)$ の
$G_\delta$ 集合である．制限写像
$r_n \colon P_d \to \operatorname{BCPM}(A_n)$ は 1-Lipschitz ゆえ連続であり，
$d$ が $A_n^2$ 上で有界で $p$ が $d$ から有限距離にあるから well-defined である．
そして $P_d$ の中で

$$\mathfrak{c} = \bigcap_{n} r_n^{-1}\bigl(\operatorname{BMet}(A_n)\bigr)$$

が成り立つ．$\subseteq$ は，両立する距離を $A_n^2$ に制限すれば
$\operatorname{BMet}(A_n)$ の元になることによる．$\supseteq$ は二段である．
相異なる 2 点はどれかの $A_n$ に入るから $p$ は定値でなく距離である．両立性は
次のようにして分かる．
$x \in X$ と $K = \mathcal{D}_X(p,d)$ に対し $2^N > d(o,x) + K + 1$ なる $N$ を
取ると，$y \notin A_N$ に対し $d(x,y) > K + 1$ ゆえ $p(x,y) > 1$ である．よって
$x$ の中心，半径 $< 1$ の $p$-球は $A_N$ に含まれ，そこでは $p|_{A_N^2}$ が既に
両立している．一方 $p$ の連続性から $p$-球は元の位相で開である．したがって二つの
位相は一致する．こうして $\mathfrak{c}$ は完備距離化可能な $P_d$ の $G_\delta$
集合であり，Alexandrov–Lavrentiev の逆向き（完備距離化可能空間の $G_\delta$
部分空間は完備距離化可能）が適用できる．[M] がこの向きを使うのはここが初めて
である．

**方向 B：(4) $\Rightarrow$ (5)．** $\mathfrak{c}$ を完備距離化可能な成分，
$d \in \mathfrak{c}$ とし，$A_n$ を上と同様に取る．制限写像
$R_n \colon \mathfrak{c} \to \operatorname{BMet}(A_n)$ は 1-Lipschitz である．
ここで距離の補間定理（metric interpolation）を用いる．$m \in \mathfrak{c}$ と
$e \in \operatorname{BMet}(A_n)$ に対し，$M|_{A_n^2} = e$ かつ

$$\mathcal{D}_X(M, m) = \mathcal{D}_{A_n}\bigl(e,\, m|_{A_n^2}\bigr)$$

を満たす $M \in \operatorname{Met}(X)$ が存在する（閉集合の一元族に適用する）．
右辺が有限だから $M \in \mathfrak{c}$ であり，$R_n$ は全射である．さらに，この
**等式**（不等式ではなく）により，$R_n$ による球の像が像の側の球にちょうど
一致する．すなわち $R_n$ は開写像である．したがって $\operatorname{BMet}(A_n)$
は，完備距離空間の連続開写像による距離化可能な像として，Hausdorff の定理により
完備距離化可能である．そこから，完備距離化可能ならば $G_\delta$，したがって
ボレルであることを経て `thm:borel-separability` により可分性を得て，Koshino
の定理を適用すると $A_n$ は $\sigma$-コンパクトであり，
$X = \bigcup_n A_n$ も $\sigma$-コンパクトである．

方向 B の途中で「$\operatorname{BMet}(A_n)$ が完備距離化可能」から可分性の
移送定理に移る段は，$G_\delta$ からボレルへの一歩を圧縮している．
直ちに埋まるが，(2) $\Rightarrow$ (5) の枝が同じ一歩を明示的に書いている
ので，対称性のために明示することを勧める．

### 3.4 補集合も稠密な非ボレルのパラメータ集合

**主張（`prop:dense-aleph1-nonborel-cantor`，強化）．** カントール空間
$2^\omega$ に，濃度 $\aleph_1$ で，$S$ と $2^\omega \setminus S$ が**ともに**
稠密であり，かつ $S$ が非ボレルであるような部分集合 $S$ が存在する．

v1 の証明は「$2^\omega$ と $[0,1]$ が Borel 同型であることから従う」であり，
Borel 同型が稠密性を保たない点が欠陥であった．[M] は互いに素な可算稠密集合
$P, Q \subseteq 2^\omega$ を取り，非可算な標準 Borel 空間 $2^\omega \setminus P$
への Borel 同型 $f \colon [0,1] \to 2^\omega \setminus P$ を引用し，$[0,1]$ 側の
非ボレル集合 $S_0$ から $S = f(S_0) \cup Q$ とおく．Borel 同型は Borel 構造と
濃度にのみ使われ，稠密性は $Q \subseteq S$ から，補集合の稠密性は
$P \subseteq 2^\omega \setminus S$ から来る．

非ボレル性の最後の段には一つ注意が要る．$Q$ は $P$ を避けるが
$2^\omega \setminus P$（すなわち $f$ の像）の中にあるので，$f(S_0)$ と $Q$ は
交わり得る．したがって $S \setminus Q$ は $f(S_0)$ そのものではなく
$f(S_0) \setminus Q$ である．正しくは，$S$ がボレルならば $S \setminus Q$ も
ボレルであり，$f(S_0) = (S \setminus Q) \cup (f(S_0) \cap Q)$ はボレル集合と
可算集合の和としてボレルとなって矛盾する，と読む．原稿の「可算集合はボレル」と
いう一言は正しい示唆であるが，必要なのは上の可算集合による補正であって，集合の
等式ではない．

補集合の稠密性は §3.5 で使われる．そこでは $G = 2^\omega \setminus S$ を**稠密な**
パラメータ域とし，その上で定義された等長写像をコンパクトな $2^\omega$ 全体に
一意に連続拡張する．v1 の経路ではこれができなかった．

### 3.5 非可分な超距離化可能空間：$\operatorname{UMet}(Y;R)$ の非ボレル性

**主張（`cor:nonseparable-ultrametric-nonborel`）．** $Y$ を非可分な超距離化
可能空間，$R$ を characteristic な range set とする．(1)
$\operatorname{UMet}(Y;R)$ の任意の $R$-成分は $\operatorname{UCPM}(Y;R)$ の
ボレル集合でない．(2) $\operatorname{UMet}(Y;R)$ 自身もボレル集合でない．

これが [M] の第二の新しい主結果である．v1 の超距離側の議論は，引用する拡張定理
が擬超距離全体の空間の上の拡張を与えないために，全体空間 $\operatorname{UCPM}$
の間で Borel $\sigma$-代数を運ぶ段で止まっていた（§2.2）．[M] はその段を修理
するのではなく，そこを通らない別の経路を取る．要点は二つである．第一に，拡張
は完備な全体空間 $\operatorname{UCPM}(Y;R)$ の内部で，稠密なパラメータ域
$G = 2^\omega \setminus S$ から作る（§3.4 の補集合の稠密性はここで用いられる）．
第二に，引き戻しは拡張子の像ではなく $R$-成分に対して取る．この二点により，
全体空間の間の移送が最初から現れず，$\operatorname{UCPM}$ 版の拡張子は不要に
なる．

構成は次の四つの部分からなる．

**分離集合と中心写像．** $R$-成分 $\mathfrak{c}^R$ と $d \in \mathfrak{c}^R$ を
固定し，$(Y,d)$ が可算な $\varepsilon$-ネットを持たない $\varepsilon > 0$ と，
$a \in R \setminus \{0\}$，$a \le \varepsilon$ を取る（$R$ が characteristic だ
から取れる）．極大 $a$-分離集合 $A$ を取ると，$A$ を中心とする開 $a$-球は $Y$ の
開かつ閉な集合からなる分割をなし，中心写像 $\pi$ は $d(x,\pi(x)) < a$ を満たす
連続なレトラクションである．$a \le \varepsilon$ と $A$ の $a$-ネット性から $A$
は非可算であり，閉かつ離散である．

**成分を制御する拡張子．** $A$ を潰した商は零次元の距離化可能空間であり，$R$ が
characteristic だから両立する $R$-値超距離 $v_0$ を持つ．$b \in R \setminus \{0\}$
による切り詰め $v = \min\{v_0, b\}$ も両立する $R$-値超距離であり $v \le b$ を
満たす．因子化の定理が要求する二条件は，その定理が構成するレトラクションでは
なく，上の $\pi$ に対して確かめられる．一方は $A$ が離散だから，他方は
$\inf_{u \in A} d(x,u) < a$ が $\pi(x)$ で達成されることによる（$d(x,u) < a$
ならば $\pi(x) = u$ であり，他の $u' \in A$ には強三角不等式と
$d(u,u') \ge a$ から $d(x,u') \ge a$ が出る）．これにより，因子化定理の証明中の
位相埋め込み $\Theta(x) = (\pi(x), p(x))$（零次元部分への埋め込み．§4）の第二
成分である射影 $p$ を用いて，max 形の拡張子
$E(w)(x,y) = w(\pi x, \pi y) \vee v(px, py)$ が使える．ここで $w$ は $A$ 上の
両立する $R$-値超距離を走る変数であり，これは拡張子 $E$ を定める式であって，
後に $w = d|_{A^2}$ および符号化した超距離 $m_t$ に適用する．

**基底の拡張と符号化．** 基底の拡張 $\hat{d} = E(d|_{A^2})$ は $d$ から有限距離
にある：$\tau = a \vee b$ とおくと，$\pi$ を経由した強三角不等式から
$\mathcal{UD}^R_Y(\hat{d}, d) \le \tau$ が出る．符号化は $A$ の内部で行う．
$z \in A$ を固定し，$R$ の可算共終部分集合により $A$ を $z$ を中心とする閉球の
可算和として書くと，そのうち一つ $B$ は非可算である．$z \in H \subseteq B$，
$\lvert H \rvert = \aleph_1$ を取り，超距離の符号化を $H$ に移して $e_t$ と
書き，$(A \setminus H) \cup \{z\}$ 上の $d|_{A^2}$ と $z$ で max 形の
one-point amalgamation を行って $m_t$ を得る．両立性の同値性と成分の評価，および等長性の下からの評価が
いずれも再現する．両立性は $A$ が $a$-分離であることから来る：$t \notin S$ の
とき $A \setminus H$ の各点は半径 $a$ で孤立し，$H$ の中心以外の点は符号化の
半径で孤立し，交差項は $e_t(z,u) > 0$ または $d(x,z) \ge a$ で下から押さえ
られる．$t \in S$ のときは $H$ の中の符号化の中心が孤立点でなくなる．

**稠密な域からの拡張と引き戻し．** $G = 2^\omega \setminus S$ は §3.4 により
稠密であり，$F(t) = E(m_t)$ は $G$ 上で等長である．$\operatorname{UCPM}(Y;R)$
は完備距離化可能だから，$F$ は $2^\omega$ 全体への連続写像 $\bar{F}$ に一意に
拡張される．$A^2$ への制限は 1-Lipschitz で $t \mapsto m_t$ は連続だから，
Hausdorff 空間へ向かう二つの連続写像が稠密集合 $G$ 上で一致することにより，
**全ての** $t \in 2^\omega$ で $\bar{F}(t)|_{A^2} = m_t$ が成り立つ．これと，
基底の拡張および貼り合わせた符号化についての上の二つの成分の評価から，
$\bar{F}^{-1}(\mathfrak{c}^R) = G$ が従う．$G$ は非ボレル
だから，連続写像による引き戻しの障害により $\mathfrak{c}^R$ も非ボレルである．
(2) は $R$-成分が開であることから従う．

**帰結．** `thm:ultrametric-borel-separability`（$\operatorname{UMet}(Y;R)$ が
ボレルならば $Y$ は可分）は，いまや上の (2) の対偶として一行で従う．
`cor:ultrametric-space-complete-separability` は，完備距離化可能な部分空間が
$G_\delta$ であるという Alexandrov–Lavrentiev の順方向を引用して，そこに帰着
する．`cor:complete-ultrametric-borel-separability` は，$\operatorname{UComp}$
版の完備性保存を持つ拡張子に取り替えて同じ構成を繰り返す（後述 §6(g) の通り，
再利用されるのは分離集合・符号化の族・稠密な域からの拡張だけであり，成分の
評価は用いられない）．いずれの証明にも，全体空間の間でボレル性を移送する段は
現れない．

## 4. 用いられた外部の数学的結果

以下は，[M] が定理として引用する外部の結果と，出典の**証明**の中の構成に依存
するデータとを区別して並べたものである．後者は，定理の主張から得られる情報より
真に強く，定理の主張の一部として扱ってはならない．各項目に添えた E1 などの記号
は，本ノートの中で外部に由来する各項目を指し分けるための呼称である．

**定理として引用されるもの．**

- **距離の等長 extensor 定理**（[I1, Theorem 1.1]．E1）．距離化可能
  空間 $X$ とその閉部分集合 $A$ に対し，$E \colon \operatorname{Met}(A) \to
  \operatorname{Met}(X)$ で (1) $E(d)|_{A^2} = d$，(2)
  $\mathcal{D}_A(d,e) = \mathcal{D}_X(E(d),E(e))$，(3)
  $E(\operatorname{BMet}(A)) \subseteq \operatorname{BMet}(X)$，(4)
  $E(\operatorname{Comp}(A)) \subseteq \operatorname{Comp}(X)$ を満たすものが
  存在し，さらに擬距離全体の空間の上の等長拡張
  $\tilde{E} \colon \operatorname{CPM}(A) \to \operatorname{CPM}(X)$ で
  $\tilde{E}|_{\operatorname{Met}(A)} = E$ となるものが存在する．[M] は (4) を
  「$X$ が完備距離化可能ならば」という条件付きで述べており，これは [I1] の
  文字通りの主張よりも [I1] 自身の証明に忠実である（§6(e)）．用いる箇所は
  拡張子の引き戻し補題，`thm:borel-separability`，
  `cor:nonseparable-metric-nonborel`，`cor:complete-metric-borel-separability`
  である．
- **超距離の因子化・拡張定理**（[I2, Theorem 4.7]．E2）．$X$ 超距離
  化可能，$A$ を空でない閉部分集合，$R$ を characteristic とすると，等長埋め込み
  $E \colon \operatorname{UMet}(A;R) \to \operatorname{UMet}(X;R)$ で (1)
  $E(u)|_{A^2} = u$，(2) $\mathcal{UD}^R_X(E(u),E(v)) = \mathcal{UD}^R_A(u,v)$，
  (3) $X$ が完備距離化可能ならば $E$ は
  $E(\operatorname{UComp}(A;R)) \subseteq \operatorname{UComp}(X;R)$ を満たす
  ように選べる，となるものが存在する．この $\operatorname{UMet}$ 版の主張は，
  出典が与えるより一般の $\Sigma \colon \operatorname{Met}(F) \to
  \operatorname{Met}(X)$ を，その条件 (1)，(2)，(5) と (N1) に沿って
  $\operatorname{UMet}$ に特殊化したものである．**擬超距離全体の空間の上の
  拡張子は与えない．** [M] はもはやそれを必要としない（§3.5）．
- **Koshino の定理**（[Ko]．E3）．$X$ が可分距離化可能のとき，$X$ が
  $\sigma$-コンパクトであることと，有界な両立距離の空間 $AM(X) =
  \operatorname{BMet}(X)$ が完備距離化可能であることは同値である．
  `cor:bounded-metric-complete-sigma-compact` の二つの枝（全体に一度，各
  $A_n$ に一度）で用いられる．
- **距離の補間定理**（metric interpolation．[I3, Theorem 1.1]．E5）．
  距離化可能空間 $X$，閉集合の離散族 $\{A_i\}_{i \in I}$，$d \in
  \operatorname{Met}(X)$，$e_i \in \operatorname{Met}(A_i)$ に対し，
  $m|_{A_i^2} = e_i$ かつ $\mathcal{D}_X(m,d) =
  \sup_i \mathcal{D}_{A_i}(e_i, d|_{A_i^2})$ を満たす
  $m \in \operatorname{Met}(X)$ が存在する．[M] は一元族に適用し，第二の条件を
  **等式として**使う：制限写像の開性は，指定された距離ちょうどの位置に原像を
  作ることで示されるからで，$\le$ では足りない．
- **Hausdorff の開写像定理**（E6）．完備距離空間の連続開写像による
  距離化可能な像は完備距離化可能である．像に可分性の制限は付かない．
  `cor:bounded-metric-complete-sigma-compact` の方向 B で用いられる．[M] は
  これを [MS, §3.4] により引用しているが，その節自身の番号付き主張は無理数
  空間の**可分な**像に関するものであり，[M] が必要とする形は同節の "only if"
  の論証の中に Hausdorff に帰して記されている（§6(d)）．
- **Alexandrov–Lavrentiev の $G_\delta$ 特徴付け**（[Ke, Theorem 3.11]）．
  順方向（距離化可能空間の完備距離化可能な部分空間は $G_\delta$ であり，全体
  空間の可分性は不要）と逆方向（完備距離化可能空間の $G_\delta$ 部分空間は完備距離化
  可能）の双方が [M] では番号付きの定理として引用されている．逆方向が使われる
  のは `cor:bounded-metric-complete-sigma-compact` の方向 A が初めてである．
- **標準的な記述集合論**（[Ke]，[Sr]）．ボレル集合の完全集合定理とベルンシュタ
  イン集合の存在が `prop:dense-aleph1-nonborel-interval` の二つの分岐で，
  $2^\omega \setminus P$ と $[0,1]$ の Borel 同型（[Sr, Theorem 3.3.13]）が
  `prop:dense-aleph1-nonborel-cantor` で用いられる．

**出典の証明の中の構成に依存するデータ．**

- **[I1] の証明の中の点評価**（[I1, Lemma 4.4]．E1c）．函数空間への
  埋め込み $J$ が $y \in A$ に対し $L(J(x),J(y)) \le 4\,w(x,y) + 1$ を満たす，
  という評価であり，[M] では $r(x,a) \le 4\,d(x,a) + 1$ として現れる．これは
  [I1, Theorem 1.1] の主張から得られる情報より真に強い：定理は任意の閉部分集合
  について述べており，特定の拡張が $\operatorname{Met}(X)$ のどの成分に属するか
  は何も言わないからである．`cor:nonseparable-metric-nonborel` のみが用い，
  そこでは「用いる拡張子はこの構成そのものであって，定理が与える任意の拡張子
  ではない」ことを記す必要がある．
- **[I2] の証明の中の構成データ**（E2c）．次の五つである．零次元の
  商に関する命題（Proposition 2.8）と，characteristic な $R$ に対し
  $\operatorname{UMet}(X;R) \neq \emptyset$ と $\dim_T X = 0$ が同値であること
  （Proposition 2.3）．Theorem 2.11 の二条件 (D), (SR)．ただし [M] はこの定理が
  構成するレトラクションではなく，自分で取った中心写像に対してこれらを確かめる．
  Theorem 3.1 の証明が用いるのは二条件だけなので，この差し替えは正当である．
  さらに Theorem 3.1 の証明の中の埋め込み $\Theta(x) = (\pi(x), p(x))$ と，
  Theorem 4.7 の証明の中の max 形の拡張子
  $E(w)(x,y) = w(\pi x, \pi y) \vee v(px, py)$．
  `cor:nonseparable-ultrametric-nonborel` のみが用いる．ここから得られる成分の
  制御は，レトラクションが $a$-ネットの中心写像であることと，商の超距離を $b$
  で切り詰めたことに依存しており，どちらも [I2, Theorem 4.7] の主張からは得ら
  れない．

**標準的事実として引用されるもの．** $\operatorname{CPM}(X)$ の完備距離化可能性
と，characteristic な $R$ に対する $\operatorname{UCPM}(Y;R)$ の完備距離化可能性
は，いずれも [I5, Lemma 2.4] による．one-point amalgamation が距離
（超距離）を与えることも引用付きで述べられており，距離の場合は [I3, Proposition 3.2]，超距離
の場合は [I4, Lemma 2.15] にそれぞれよる．一方，両片が完備なら結果も完備である
という完備性の半分は外部引用ではなく，[M] 自身の中で証明されている．なお，分離集合が閉
かつ離散であること，成分が開かつ閉であること，完備距離の閉部分空間への制限が
完備であること，可算集合の可算和が可算であること（球の選択に必要なのはこれだけ
で，$\aleph_1$ の正則性は使われない），超距離を定数で切り詰めても超距離であり
位相が変わらないこと，完備距離化可能空間の位相和が完備距離化可能であることは，
[M] でも明示されないまま用いられており，いずれも初等的である．

## 5. 残された原稿側の修正点

**対象．** `cor:metric-space-complete-separability`（$X$ 距離化可能：
$\operatorname{Met}(X)$ が完備距離化可能ならば $X$ は可分）．主張は正しく，
問題は書かれている証明の一段にある．

**欠陥．** 証明は $\operatorname{Met}(X)$ の完備距離化可能性から
$\operatorname{Met}(X)$ が $\operatorname{CPM}(X)$ の $G_\delta$ 集合，
したがってボレル集合であることを導き，そこで `thm:borel-separability` を引いて
可分性を結論する．しかし [M] におけるこの定理の仮定は
$\operatorname{BMet}(X)$ のボレル性であって $\operatorname{Met}(X)$ のそれでは
ない．したがってこの段は，引用された定理の主張からはそのままでは従わない．
[IU] では同定理が $\operatorname{Met}(X)$ について述べられており，この系
（v1 では証明が省略されていた）の引用は健全であった．欠陥は，定理を
$\operatorname{BMet}$ 版に述べ直した際に系の証明が更新されなかったことから
生じた．v1 と [M] の間で新たに入ったものであり，長く残っていた誤りでは
ない．

**修正（推奨）．** 直前の `cor:nonseparable-metric-nonborel` の (2) は，$X$ が
非可分ならば $\operatorname{Met}(X)$ が $\operatorname{CPM}(X)$ のボレル集合で
ないことを与える．$\operatorname{Met}(X)$ が完備距離化可能ならばボレルだから，
その対偶で可分性が一行で出る．[M] 自身の新しい定理群だけで閉じる修正である．

**修正（代替）．** 有界な両立距離は $\operatorname{Met}(X)$ のただ一つの成分を
なし，成分は $\operatorname{Met}(X)$ で開かつ閉である．したがって
$\operatorname{Met}(X)$ がボレルならば $\operatorname{BMet}(X)$ も
$\operatorname{CPM}(X)$ のボレル集合であり，`thm:borel-separability`
がそのまま適用できる．

**名称．** 概要と導入はいずれも「$\operatorname{Met}(X)$ がボレルならば
$X$ は可分」を述べ，導入はこれに同定理を引いている．この主張は真である
（`cor:nonseparable-metric-nonborel` の (2) の対偶）が，引用された定理が
述べていることではない．書き換えの案は §6(a) に挙げる．

## 6. 原稿への提案

以下はおおむね原稿の記述に関する提案であり，数学的な欠陥は (a) の第一項のみで
ある（ただし (e) は原稿 [M] ではなく引用元 [I1] の著者へ向けた注意である）．

**(a) `cor:metric-space-complete-separability` と，概要・導入の言い分け．**
系の証明中の `thm:borel-separability` への参照を，
`cor:nonseparable-metric-nonborel` の (2) の対偶に差し替える（§5）．併せて，
概要と導入が述べる「$\operatorname{Met}(X)$ がボレルならば $X$ は可分」に，
文字通り対応する番号付きの主張を与える．二つの選択肢がある：
`thm:borel-separability` を v1 と同様に $\operatorname{Met}(X)$ について
述べ直すか，この対偶に独立したラベルを与えてそちらを引用する．なお `cor:bounded-metric-complete-sigma-compact` の
(2) $\Rightarrow$ (5) は $\operatorname{BMet}$ 版を必要とするので，どちらを
選ぶ場合でも両方の形が本文のどこかに必要である．

**(b) 導入部の相互参照（$\operatorname{Met}(Z)$ の非ボレル性）．** 導入は，
濃度 $\aleph_1$ の離散空間 $Z$ について $\operatorname{Met}(Z)$ がボレルでない
と述べ，`thm:metric-component-nonborel` を引用している．その定理が述べるのは
各**成分**の非ボレル性であり，$\operatorname{Met}(Z)$ に関する主張は
`cor:discrete-metric-nonborel` の (2) である．引用先を系に（または両方に）
改めることを勧める．概要は同じ主張をラベルなしで述べているので影響しない．

**(c) 定理と系の濃度の仮定の不一致．** `thm:metric-component-nonborel` は
$\lvert Z \rvert \ge \aleph_1$ で成立するが，`cor:discrete-metric-nonborel` は
$\lvert Z \rvert = \aleph_1$ の下で述べられており，しかもその証明は (1) が定理
「そのもの」であると書いている．系は真であるが，定理の一般性を捨てている．系の
仮定を $\ge \aleph_1$ に揃えるか，「そのもの」という表現を外すことを勧める．

**(d) Michael–Stone の引用形式．** 原稿は「完備距離空間の連続開写像による
距離化可能な像は完備距離化可能」に [MS, §3.4] を引いている．同節自身の番号付き
主張は無理数空間の**可分な**像に関するものであり，実際に使われている定理
（Hausdorff のもの，像に可分性の制限がない形）は同節の論証の中に，Hausdorff に
帰する形で現れる．Hausdorff の定理を直接引用し，[MS, §3.4] を副次的な出典と
して添える形に改めることを勧める．

**(e) 引用元の側への注意（本原稿の欠陥ではない）．** [I1] は完備性保存の主張を
$X$ への仮定なしに述べているが，その証明は $X$ が完備距離化可能であることを
使っている．無条件では成り立たない（$\operatorname{Comp}(X) = \emptyset$ かつ
$\operatorname{Comp}(A) \neq \emptyset$ となる例がある）．**[M] はこの主張を
条件付きで正しく述べている**ので，本原稿に修正は要らない．これは引用元である
[I1] の著者への注意であり，扱いは著者の判断に委ねる．

**(f) Koshino の定理の引用番号．** 原稿は "Corollary 1.2" を引いているが，
確認した本文では主定理と系に番号が付いていない．出版版と照合することを勧める．
$AM(X)$ を $\operatorname{BMet}(X)$ と同一視する点は正しい．

**(g) 記述上の要望（数学的欠陥ではない）．** 三点ある．第一に，
`thm:metric-component-nonborel` の証明で，貼り合わせた距離の両立性の同値性が
証明なしに述べられ，符号化の中心が部分集合に属することが暗黙に置かれている．
どちらも直ちに埋まるが，明示することを勧める．第二に，
`cor:nonseparable-ultrametric-nonborel` の対応する両立性の議論では，離散の
成分定理が用いる「部分集合の外では中心からの距離が大きい」という理由は使えない
（そこでの部分集合は球の真部分集合であり得るため）．主張は真であるが，根拠は
分離集合の $a$-分離性である旨を書き添えることを勧める．第三に，
`cor:complete-ultrametric-borel-separability` の「構成を繰り返す」の範囲を明示
することを勧める．実際に再利用されるのは分離集合，その上の符号化の族，および
稠密な域からの拡張だけであり，成分に関する三つの評価は用いられない．引用元の
完備性保存の節は自前の補助データを選ぶので，成分を制御するデータと**同時に**
選べるという主張は要らないし，本文にもない．

## 7. 参考文献

- [M] Y. Ishiki and T. Uda, *Borelness of moduli spaces of metrics implies
  separability*，2026 年 8 月 27 日の内部タイムスタンプをもつ未公開の受領原稿
  （arXiv:2608.19618v1 の後継の作業稿．arXiv には登録されていない）．
- [IU] Y. Ishiki and T. Uda, *Borelness of moduli spaces of metrics implies
  separability*, arXiv:2608.19618v1 (2026).
- [I1] Y. Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030v4.
- [I2] Y. Ishiki, *A factorization of metric spaces*, Colloq. Math. 174
  (2023), 101–119. arXiv:2212.13409.
- [I3] Y. Ishiki, *An interpolation of metrics and spaces of metrics*, Topol.
  Appl. 388 (2026), 109856. arXiv:2003.13227v3.
- [I4] Y. Ishiki, *Fractal dimensions in the Gromov–Hausdorff space*, Bull.
  Pol. Acad. Sci. Math. 71 (2023), 147–168.
- [I5] Y. Ishiki, *Spaces of metrics are Baire*, Topol. Appl. 369 (2025),
  109408.
- [Ko] K. Koshino, *On the Borel complexity and the complete metrizability of
  spaces of metrics*, Anal. Geom. Metr. Spaces 12 (2024).
- [MS] E. Michael and A. H. Stone, *Quotients of the space of irrationals*,
  Pacific J. Math. 28 (1969), 629–633.
- [Ke] A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in
  Mathematics 156, Springer, 1995.
- [Sr] S. M. Srivastava, *A Course on Borel Sets*, Graduate Texts in
  Mathematics 180, Springer, 1998.
