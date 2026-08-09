# 証明報告書：石木予想 5.1

**出典:** Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 (2024)  
**状態:** 証明（Gate A–C 通過．証明候補ラベルは owner 裁定により解除 — PR #29, 2026-08-09．Lean 形式化は sorry-free）  
**更新:** 2026-08-09

---

## 1. 記号と設定

- $D$：濃度 $\aleph_1$ の離散位相空間
- $\operatorname{Met}(D)$：$D$ の離散位相に**適合する**距離の全体，上限距離位相を装備する  
  （注意：$d \in \operatorname{Met}(D)$ とは，$d$ が $D$ 上の距離であり，$d$ が誘導する位相が $D$ の離散位相に一致することを意味する．集合 $D$ 上の全ての距離の全体とは異なる．）
- $\rho(d_1, d_2) := \sup_{x,y\in D} |d_1(x,y) - d_2(x,y)|$：$\operatorname{Met}(D)$ 上の上限距離
- $[0,1]$：実数の閉単位区間
- $\omega_1$：最小の非可算順序数
- $\mathbb{N}_{\ge 1}$：$1$ 以上の自然数全体

**背景定理 1（Alexandrov–Lavrentiev 型の $G_\delta$ 特徴づけ，可分な場合に使用）.**  
$X$ を可分距離化可能空間（特に Polish 空間）とする．部分空間 $S \subseteq X$ が完全距離化可能ならば，$S$ は $X$ の $G_\delta$ 集合である．  
（出典: Kechris, *Classical Descriptive Set Theory*, GTM 156, Thm. 3.11，$X$ が Polish の場合．一般の——可分性を仮定しない——完全距離化可能空間についても同型の特徴づけが成り立つ．Engelking, *General Topology*, Thm. 4.3.23–4.3.24，および Willard, *General Topology*, Thm. 24.12, p. 179 を参照．）  
本報告書では，この定理を対偶の形（$S$ が $X$ の $G_\delta$ でなければ $S$ は完全距離化可能でない）で，$X=[0,1]$（可分，実際 Polish）という可分な設定に限って用いる（主定理の証明，手順 3）．

**背景定理 2（閉部分空間の遺伝性，可分性を用いない初等的議論）.**  
$Z$ を完全距離化可能な空間とし，$C \subseteq Z$ をその閉部分集合とする．このとき $C$ は（相対位相に関して）完全距離化可能である．

*証明.* $Z$ の位相を与える完備距離 $d$ を一つとる．$d|_{C\times C}$ は $C$ の相対位相を与える距離だから，これが完備であることを示せばよい．$(c_n)_n$ を $(C, d|_C)$ における Cauchy 列とする．$(c_n)_n$ は $(Z,d)$ における Cauchy 列でもあるから，$d$ の完備性より，ある $z \in Z$ に収束する．距離空間においては閉集合は点列に関して閉じている（$C$ の点列の極限は $Z$ の中で取っても $C$ に属する）から，$C$ が $Z$ の閉集合であることより $z \in C$．よって $(c_n)_n$ は $(C,d|_C)$ の中で $z$ に収束し，$(C,d|_C)$ は完備である．したがって $C$ は完全距離化可能である．∎

この証明は $Z$（したがって $C$）の可分性を一切用いない．本報告書では，$\operatorname{Met}(D)$（$|D|=\aleph_1$）が可分でないため，背景定理 1 を $\operatorname{Met}(D)$ に対して直接使うことは避け，$\operatorname{Met}(D)$ の閉部分空間の完全距離化可能性の議論には，可分性を要求しないこの背景定理 2 のみを用いる（主定理の証明，手順 5）．

**注意（$\operatorname{Met}(D)$ の上限距離の値域について）.** 上限距離 $\rho(d_1,d_2)=\sup_{x,y\in D}|d_1(x,y)-d_2(x,y)|$ は，$d_1,d_2 \in \operatorname{Met}(D)$ が非有界かつ差が非有界であるとき $+\infty$ をとりうる（extended 値．出典検証の詳細は Issue #2 の記録として `notes/literature.md` を参照）．しかし $\min(\rho,1)$ は $\rho$ と同一の位相を定める通常の（有限値の）距離だから，$\operatorname{Met}(D)$ 自体は通常の意味で距離化可能である．「完全距離化可能」は位相のみに依存する性質であって，それを証明するのにどの具体的な距離を用いるかには依存しないから，$\rho$ が extended 値をとりうるという事実自体は，背景定理 2 を含む本報告書の議論に一切影響しない．なお §3 で構成する距離族はすべて値域が $[0,2]$ に含まれるから，そこで現れる $\rho$ の値はすべて有限である．

---

## 2. 主定理

**THM-CONJ51.**  
$|D| = \aleph_1$ のとき，$\operatorname{Met}(D)$ は上限距離位相に関して完全距離化可能でない．

*状態: 証明（§3–§4 に完全に記述済み．Gate A–C 通過，証明候補ラベル解除済み — 2026-08-09．Lean: `thm_conj51`, sorry-free）*

---

## 3. 補題

### LEM-A-EXISTS

**主張.**  
ZFC において，$A \subseteq [0,1]$，$|A| = \aleph_1$，かつ $A$ が $F_\sigma$ でない集合が存在する．

**記法.** $\mathfrak{c} := 2^{\aleph_0}$（連続体濃度）とおく．Cantor の定理より $\aleph_0 < \mathfrak{c}$．また $\aleph_1$ は最小の非可算基数だから，常に $\aleph_1 \le \mathfrak{c}$（ZFC の定理）．

**証明（監査済み，2026-08-09）.**

命題 $\mathsf{CH}$（$\aleph_1 = \mathfrak{c}$）の真偽によって場合分けする．排中律により，ZFC の任意のモデルでこのいずれか一方が成立するから，これは正当な場合分けである．

**場合 1：$\mathsf{CH}$ が成立する場合（$\aleph_1 = \mathfrak{c}$）.**

$A := [0,1] \setminus \mathbb{Q}$（$[0,1]$ 内の無理数全体）とおく．

- *濃度.* $|[0,1]| = \mathfrak{c}$ であり $\mathbb{Q} \cap [0,1]$ は可算．無限濃度 $\kappa$ を持つ集合から可算集合を除いても濃度は変わらない（$\aleph_0 < \kappa$ のとき $\kappa = |A| + \aleph_0$ から $|A| = \kappa$ が従う，標準的な基数演算）から，$|A| = \mathfrak{c} = \aleph_1$（最後の等号は $\mathsf{CH}$ による）．

- *$A$ が $F_\sigma$ でないこと（Baire のカテゴリ定理．この議論は $\mathsf{CH}$ に依存しない）.*  
  $A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は $[0,1]$ の閉集合）と仮定して矛盾を導く．$\mathbb{Q} \cap [0,1]$ は $[0,1]$ で稠密であり，$F_n \subseteq A$ より $F_n \cap \mathbb{Q} = \emptyset$．ゆえに $F_n$ は内点を持たない：もし $F_n$ が空でない開区間を含めば，その区間内の有理点が $F_n \subseteq A$ に属することになり $A \cap \mathbb{Q} = \emptyset$ に反する．内点を持たない閉集合は疎（nowhere dense）だから，$A$ は可算個の疎な閉集合の合併，すなわち $[0,1]$ における痩集合（meager set）である．一方 $\mathbb{Q} \cap [0,1] = \bigcup_{q \in \mathbb{Q}\cap[0,1]} \{q\}$ も可算個の疎な閉集合（一点集合）の合併だから痩集合．したがって $[0,1] = A \cup (\mathbb{Q}\cap[0,1])$ は二つの痩集合の合併，すなわち痩集合．しかし $[0,1]$ は完備距離空間であり，Baire のカテゴリ定理（例えば Kelley, *General Topology*, Theorem 34, p. 200，あるいは Willard, *General Topology*, Corollary 25.4）より，完備距離空間はそれ自身の中で痩集合になり得ない．これは矛盾．よって $A$ は $F_\sigma$ でない．

**場合 2：$\mathsf{CH}$ が成立しない場合（$\aleph_1 < \mathfrak{c}$）.**

次の補題を用いる．

> **補題（完全集合定理の系）.** $F \subseteq [0,1]$ が非可算な閉集合ならば $|F| = \mathfrak{c}$．
>
> *証明.* $F$ は $[0,1]$ の閉部分集合だから，それ自身 Polish 空間である．Cantor–Bendixson の定理（Kechris, *Classical Descriptive Set Theory*, GTM 156, 1995, §6，完全集合の性質は同書 p. 150 付近）より，$F$ は完全集合（perfect set）$P$ と可算集合 $C$ の非交和 $F = P \sqcup C$ に分解できる．$F$ が非可算で $C$ が可算だから $P \ne \emptyset$．空でない完全 Polish 空間は連続体濃度を持つ（標準的な Cantor 図式による埋め込み，同書 §6）から $|P| = \mathfrak{c}$．よって $|F| \ge |P| = \mathfrak{c}$．また $F \subseteq [0,1]$ より $|F| \le \mathfrak{c}$．ゆえに $|F| = \mathfrak{c}$．∎

$\aleph_1 \le \mathfrak{c} = |[0,1]|$ だから，$[0,1]$ の部分集合で濃度がちょうど $\aleph_1$ のものが存在する．そのような集合を一つ取り $A$ とする．$A$ が $F_\sigma$ であると仮定し，$A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は $[0,1]$ の閉集合）とする．各 $n$ について $F_n \subseteq A$ だから $|F_n| \le |A| = \aleph_1 < \mathfrak{c}$．したがって上の補題の対偶より，各 $F_n$ は可算．ゆえに $A = \bigcup_n F_n$ は可算個の可算集合の合併だから可算（可算選択公理．ZFC で常に利用可能）．これは $|A| = \aleph_1$（非可算）に矛盾．よって $A$ は $F_\sigma$ でない．

**結論.** 場合 1・場合 2 のいずれでも，$A \subseteq [0,1]$，$|A| = \aleph_1$，$A \notin F_\sigma$ を満たす集合が構成できる．両場合は排他的かつ網羅的（$\mathsf{CH}$ の真偽による分岐）だから，ZFC において LEM-A-EXISTS が成立する．∎

**別証（remark）：場合分けを回避する一様な構成.**  
場合分けを避けたい場合は，Bernstein 集合を用いた次の一様な構成もある．$[0,1]$ の Bernstein 集合 $B$（$B$ とその補集合がともに $[0,1]$ のすべての完全集合と交わるように，濃度 $\mathfrak{c}$ の超限帰納法で構成される集合．Oxtoby, *Measure and Category*, 2nd ed., p. 24）を一つ固定し，$B$ の部分集合で濃度 $\aleph_1$ のものを $A$ とする（$\aleph_1 \le \mathfrak{c} = |B|$ より存在する）．$A \subseteq B$ ゆえ $A$ は完全集合を部分集合として持たない：もし完全集合 $P \subseteq A \subseteq B$ ならば，$B$ の補集合は $P$ と交わるという Bernstein 集合の性質に反する．いま $A$ が $F_\sigma$，すなわち $A = \bigcup_n F_n$（$F_n$ 閉）であったとする．$A$ は非可算（$|A|=\aleph_1$）だから，ある $F_n$ は非可算閉集合．Cantor–Bendixson の定理より，非可算閉集合は空でない完全集合を含む．よってその完全集合は $F_n \subseteq A$ の部分集合，すなわち $A$ の完全部分集合となり，$A$ が完全集合を持たないことに反する．よって $A$ は $F_\sigma$ でない．この議論は $\mathsf{CH}$ の成否によらず一様に成立する．

*状態: **監査済み・独立レビュー通過（Issue #10, 2026-08-09）**．参考文献は `notes/literature.md`，監査記録は `notes/proof-audit.md` を参照．*

---

### LEM-STAR-METRIC

**主張.**  
$D$ 上に，パラメータ $t \in Y$（$Y = [0,1] \setminus A$）によってパラメトライズされた星型族の距離 $d_t \in \operatorname{Met}(D)$ が構成できる．

#### 3.1 設定の正規化

主張は濃度 $\aleph_1$ の離散空間 $D$ を一つ固定して述べられているが，$D$ を以下で定める具体的な集合にとってよい．実際，離散位相空間の同相型はその濃度のみで定まる．さらに，離散空間 $D, D'$ の間の全単射 $f : D \to D'$ は同相写像だから，対応 $d \mapsto d \circ (f\times f)$ は $D'$ 上の距離を $D$ 上の距離に移し，離散位相への適合性を保つ．すなわちこの対応は $\operatorname{Met}(D')$ から $\operatorname{Met}(D)$ への全単射を与える（逆写像は $f^{-1}$ による同じ対応）．さらに $\sup$ をとる添字集合が $f\times f$ によって全単射に移り合うから，この対応は上限距離 $\rho$ を保つ．すなわち等距離同型である．したがって $\operatorname{Met}(D)$ の（距離空間としての，特に位相空間としての）同型類は $|D|$ のみで定まり，濃度 $\aleph_1$ を持つ任意の具体的な集合を $D$ として取って一般性を失わない．

#### 3.2 構成

LEM-A-EXISTS の与える $A \subseteq [0,1]$（$|A| = \aleph_1$，$A$ は $F_\sigma$ でない）を固定する．$|A| = \aleph_1$ だから単射な列挙
$$A = \{a_\alpha : \alpha < \omega_1\}, \qquad \alpha \ne \beta \implies a_\alpha \ne a_\beta$$
を一つ取る．$Y := [0,1] \setminus A$ とおく．

台集合を
$$D := \{p, q\} \ \sqcup\ \{y_\alpha : \alpha < \omega_1\} \ \sqcup\ \{x_{\alpha,n} : \alpha < \omega_1,\ n \in \mathbb{N}_{\ge 1}\}$$
（三つの部分は互いに交わらず，各添字は相異なる元を与える）で定め，離散位相を与える．濃度は
$$|D| = 2 + \aleph_1 + \aleph_1 \cdot \aleph_0 = \aleph_1$$
である．$\alpha < \omega_1$ に対して
$$C_\alpha := \{y_\alpha\} \cup \{x_{\alpha,n} : n \in \mathbb{N}_{\ge 1}\}$$
とおき，$C_\alpha$ を第 $\alpha$ 星，$y_\alpha$ をその中心，$x_{\alpha,n}$ をその端点と呼ぶ．また $\{p,q\}$ を基準対と呼ぶ（$d_t(p,q)$ からパラメータ $t$ を復元するために用いる）．
$$D = \{p,q\} \ \sqcup \bigsqcup_{\alpha<\omega_1} C_\alpha$$
は $D$ の分割である．以下ではこの分割の要素をブロックと呼ぶ．

$t \in [0,1]$，$\alpha < \omega_1$，$n \in \mathbb{N}_{\ge 1}$ に対して
$$s_n(\alpha, t) := \min\bigl(1,\ |t - a_\alpha| + 1/n\bigr)$$
とおく．$|t-a_\alpha| \ge 0$ と $1/n > 0$ より $0 < s_n(\alpha,t) \le 1$ である．

$t \in [0,1]$ に対し，写像 $d_t : D \times D \to [0,2]$ を，$d_t(u,u) := 0$ と，相異なる 2 点に対する次の表とで定める（表は無順序対に対して値を与えるから，$d_t$ は定義により対称である）．

| 相異なる 2 点 $\{u,v\}$ | $d_t(u,v)$ |
|---|---|
| 基準対 $\{p,\ q\}$ | $1 + t$ |
| 同一の星の中心と端点 $\{y_\alpha,\ x_{\alpha,n}\}$ | $s_n(\alpha,t)$ |
| 同一の星の相異なる端点 $\{x_{\alpha,n},\ x_{\alpha,m}\}$（$n \ne m$） | $s_n(\alpha,t) + s_m(\alpha,t)$ |
| 上記以外のすべての対（相異なるブロックに属する 2 点） | $1$ |

表の 4 つの場合は相異なる 2 点の全体を過不足なく尽くす：同一ブロックに属する相異なる 2 点は，そのブロックが $\{p,q\}$ ならば第 1 行，星 $C_\alpha$ ならば第 2 行または第 3 行に該当し，相異なるブロックに属する 2 点は第 4 行に該当する．値域が $[0,2]$ に含まれることは $0 < s_n \le 1$ と $0 \le t \le 1$ から従う．

以下，構成の性質を (C1)–(C3) として示す．

#### 3.3 (C1) $d_t$ は距離である（すべての $t \in [0,1]$）

**主張.** 任意の $t \in [0,1]$ に対し，$d_t$ は $D$ 上の距離である．

*証明.* 対称性と $d_t(u,u)=0$ は定義による．相異なる $u,v$ に対し，表の各行の値は正である（$1+t \ge 1 > 0$，$s_n > 0$，$s_n + s_m > 0$，$1 > 0$）から，$d_t(u,v) = 0$ と $u = v$ は同値である．

三角不等式 $d_t(u,w) \le d_t(u,v) + d_t(v,w)$ を示す．$u = v$，$v = w$，$u = w$ のいずれかが成り立つ場合は，それぞれ等号または $0 \le d_t(u,v)+d_t(v,u)$ に帰着して自明だから，$u, v, w$ が相異なる場合を考える．以下，$t$ と $\alpha$ を固定したときは $s_n := s_n(\alpha,t)$ と略記する．次の 2 つの観察を用いる．

- (i) 相異なる 2 点の距離は $2$ 以下である（値域が $[0,2]$）．
- (ii) 相異なるブロックに属する 2 点の距離は $1$ である（表第 4 行）．

3 点 $u,v,w$ がブロックの分割に対してどのように分布するかで場合を分ける．

**場合 (a)：3 点が同一のブロックに属する.**  
$\{p,q\}$ は 2 元集合だから，そのブロックはある星 $C_\alpha$ である．

- 3 点のうち 1 点が中心 $y_\alpha$ で，残り 2 点が端点 $x_{\alpha,n}, x_{\alpha,m}$（$n \ne m$）である場合：中心を経由する経路について
  $$d_t(x_{\alpha,n}, x_{\alpha,m}) = s_n + s_m = d_t(x_{\alpha,n}, y_\alpha) + d_t(y_\alpha, x_{\alpha,m})$$
  が等号で成り立つ．また端点を経由する経路については
  $$d_t(x_{\alpha,n}, y_\alpha) = s_n \le s_n + 2 s_m = d_t(x_{\alpha,n}, x_{\alpha,m}) + d_t(x_{\alpha,m}, y_\alpha)$$
  が成り立つ．3 点の順序を入れ替えた残りの場合もこの 2 つの不等式の対称なコピーである．
- 3 点がすべて端点 $x_{\alpha,n}, x_{\alpha,m}, x_{\alpha,k}$（$n,m,k$ は相異なる）である場合：
  $$d_t(x_{\alpha,n}, x_{\alpha,m}) = s_n + s_m \le (s_n + s_k) + (s_k + s_m) = d_t(x_{\alpha,n}, x_{\alpha,k}) + d_t(x_{\alpha,k}, x_{\alpha,m}).$$

**場合 (b)：2 点が一つの星 $C_\alpha$ に属し，残る 1 点 $z$ が $C_\alpha$ の外にある.**  
$u,v \in C_\alpha$，$z \notin C_\alpha$ とすると，(ii) より $d_t(u,z) = d_t(v,z) = 1$．よって

- $d_t(u,v) \le 2 = d_t(u,z) + d_t(z,v)$（(i) による），
- $d_t(u,z) = 1 \le d_t(u,v) + 1 = d_t(u,v) + d_t(v,z)$．

**場合 (c)：2 点が基準対 $\{p,q\}$ で，残る 1 点 $z$ がある星に属する.**  
(ii) より $d_t(p,z) = d_t(q,z) = 1$．$t \le 1$ より

- $d_t(p,q) = 1 + t \le 2 = d_t(p,z) + d_t(z,q)$，
- $d_t(p,z) = 1 \le (1+t) + 1 = d_t(p,q) + d_t(q,z)$．

**場合 (d)：3 点が互いに異なるブロックに属する.**  
このとき $p$ と $q$ が同時に現れることはないから，3 つの対はいずれも相異なるブロックに属する 2 点の対であり，(ii) よりその距離はすべて $1$．$1 \le 1 + 1$ が成り立つ．

場合 (a)–(d) は 3 点の分布を尽くすから，三角不等式が成り立つ．よって $d_t$ は距離である．∎

#### 3.4 (C2) $t \in Y$ ならば $d_t \in \operatorname{Met}(D)$

**主張.** $t \in Y$ ならば，$d_t$ の誘導する位相は $D$ の離散位相であり，$d_t \in \operatorname{Met}(D)$ が成り立つ．

*証明.* 距離 $d$ の誘導する位相が離散位相であることは，すべての一点集合が開であること，すなわち各 $u \in D$ に対して
$$\delta(u) := \inf_{v \in D,\ v \ne u} d(u,v) > 0$$
が成り立つことと同値である（$\delta(u) > 0$ ならば半径 $\delta(u)$ の球は $\{u\}$ に一致し，逆に $\{u\}$ が開ならばある半径 $\varepsilon>0$ の球が $\{u\}$ に一致するので $\delta(u) \ge \varepsilon$）．$t \in Y$ を固定し，$D$ の各点についてこれを確かめる．

- $u = p$：$d_t(p,q) = 1+t \ge 1$ であり，$p$ から他のすべての点への距離は $1$．よって $\delta(p) = 1 > 0$．$u = q$ も同様に $\delta(q) = 1 > 0$．
- $u = x_{\alpha,n}$（端点）：$x_{\alpha,n}$ から出る距離の値は，中心 $y_\alpha$ への $s_n(\alpha,t)$，同じ星の他の端点への $s_n(\alpha,t) + s_m(\alpha,t) \ge s_n(\alpha,t)$，および星の外への $1$ である．$s_n(\alpha,t) \le 1$ だから
  $$\delta(x_{\alpha,n}) = s_n(\alpha,t) = \min\bigl(1, |t-a_\alpha| + 1/n\bigr) \ge \min(1, 1/n) = 1/n > 0 .$$
  この評価は $t$ の位置によらない．
- $u = y_\alpha$（中心）：$y_\alpha$ から出る距離の値は，端点への $s_n(\alpha,t)$（$n \in \mathbb{N}_{\ge 1}$）と，星の外への $1$ である．関数 $r \mapsto \min(1,r)$ は単調非減少かつ連続であり，$n \to \infty$ のとき $|t-a_\alpha| + 1/n \downarrow |t-a_\alpha|$ だから
  $$\inf_{n \in \mathbb{N}_{\ge 1}} s_n(\alpha,t) = \min\bigl(1, |t - a_\alpha|\bigr).$$
  よって $\delta(y_\alpha) = \min(1, |t-a_\alpha|)$．$t \in Y = [0,1]\setminus A$ かつ $a_\alpha \in A$ より $t \ne a_\alpha$，すなわち $|t - a_\alpha| > 0$．ゆえに $\delta(y_\alpha) > 0$．

すべての点が孤立点だから，$d_t$ の誘導する位相は離散位相に一致する．(C1) より $d_t$ は距離だから，$d_t \in \operatorname{Met}(D)$．∎

#### 3.5 (C3) $t \in A$ における適合性の喪失

**主張.** $\beta < \omega_1$ とし $t = a_\beta \in A$ とする．このとき $d_{a_\beta}$ は $D$ 上の距離であるが，その誘導する位相は離散位相と異なる．すなわち $d_{a_\beta} \notin \operatorname{Met}(D)$ である．

*証明.* (C1) は $t \in [0,1]$ のすべてに対して成り立つから，$d_{a_\beta}$ は $D$ 上の距離である．一方
$$s_n(\beta, a_\beta) = \min\bigl(1,\ |a_\beta - a_\beta| + 1/n\bigr) = \min(1, 1/n) = 1/n$$
だから，$d_{a_\beta}(y_\beta, x_{\beta,n}) = 1/n$．任意の $\varepsilon > 0$ に対し $1/n < \varepsilon$ となる $n \in \mathbb{N}_{\ge 1}$ を取れば，中心 $y_\beta$ を中心とする半径 $\varepsilon$ の球は端点 $x_{\beta,n} \ne y_\beta$ を含む．よって $\{y_\beta\}$ は $d_{a_\beta}$ に関して開でなく，$d_{a_\beta}$ の誘導する位相は離散位相と異なる．∎

**系（適合性の特徴づけ）.** $t \in [0,1]$ に対し，$d_t \in \operatorname{Met}(D)$ であることと $t \in Y$ であることは同値である．（(C2) が一方の含意を，(C3) が他方の対偶を与える．）

(C1)–(C3) より，$t \in Y$ でパラメトライズされた距離の族 $(d_t)_{t\in Y} \subseteq \operatorname{Met}(D)$ が構成された．各 $d_t$ は各星 $C_\alpha$ の上で中心 $y_\alpha$ を経由する星型の距離であり（場合 (a) の等号），LEM-STAR-METRIC の主張が示された．∎

*状態: 執筆完了・独立レビュー通過（Issue #10, 2026-08-09）．依存関係: LEM-A-EXISTS．*

---

### LEM-CLOSED-IMAGE

**主張.**  
写像 $\varphi: Y \to \operatorname{Met}(D)$，$t \mapsto d_t$ は双リプシッツ埋め込みであり，その像 $\varphi(Y)$ は $\operatorname{Met}(D)$ において閉である．

以下，LEM-STAR-METRIC の §3.2 で固定した $A$，$Y$，$D$，$(d_t)_{t \in [0,1]}$ をそのまま用いる．$Y$ には $[0,1]$ からの相対位相（すなわち通常の距離 $|t-s|$）を与える．また $D$ 上の距離 $d, e$ に対し $\rho(d,e) := \sup_{u,v \in D}|d(u,v)-e(u,v)|$ と書く（$d_t$ たちの値域は $[0,2]$ に含まれるから，以下に現れる $\rho$ の値はすべて有限である）．

#### 3.6 (C4) 双リプシッツ評価

**主張.** 任意の $s, t \in [0,1]$ に対して
$$|t - s| \ \le\ \rho(d_t, d_s) \ \le\ 2\,|t - s| .$$

*証明.* **下界.** 基準対における値を比べると
$$|d_t(p,q) - d_s(p,q)| = |(1+t)-(1+s)| = |t-s|$$
であり，$\rho(d_t,d_s)$ はこの値以上だから $\rho(d_t,d_s) \ge |t-s|$．

**上界.** 各対 $\{u,v\}$ について $|d_t(u,v) - d_s(u,v)| \le 2|t-s|$ を示せば，上限をとって結論が従う．表の各行で確かめる．

- $u = v$：両辺 $0$．
- 基準対：$|(1+t)-(1+s)| = |t-s| \le 2|t-s|$．
- 中心と端点 $\{y_\alpha, x_{\alpha,n}\}$：実数値関数 $r \mapsto \min(1,r)$ は $1$-Lipschitz であり，$r \mapsto |r - a_\alpha| + 1/n$ も（逆三角不等式 $\bigl||r-a_\alpha| - |r'-a_\alpha|\bigr| \le |r-r'|$ より）$1$-Lipschitz だから，その合成 $r \mapsto s_n(\alpha, r)$ は $1$-Lipschitz である．よって
  $$|s_n(\alpha,t) - s_n(\alpha,s)| \le |t-s| \le 2|t-s| .$$
- 同一の星の相異なる端点 $\{x_{\alpha,n}, x_{\alpha,m}\}$：上の評価を 2 回用いて
  $$\bigl|(s_n(\alpha,t)+s_m(\alpha,t)) - (s_n(\alpha,s)+s_m(\alpha,s))\bigr| \le |t-s| + |t-s| = 2|t-s| .$$
- 上記以外の対：値は $t$ によらず $1$ だから差は $0$．

以上より $\rho(d_t,d_s) \le 2|t-s|$．∎

**系（埋め込み）.** (C2) より $\varphi(t) := d_t$ は $Y$ から $\operatorname{Met}(D)$ への写像として定義される．(C4) の下界より $\varphi$ は単射であり，(C4) の両側評価より $\varphi$ は $Y$ から像 $\varphi(Y)$（$\operatorname{Met}(D)$ の相対位相を与える）への双リプシッツ全単射，特に同相写像である．すなわち $\varphi$ は双リプシッツ埋め込みである．

#### 3.7 (C5) 像の閉性

**主張.** $\varphi(Y)$ は $\operatorname{Met}(D)$ の閉集合である．

*証明.* $\operatorname{Met}(D)$ の位相は距離 $\min(\rho,1)$ が定めるものだから，閉包の点は点列の極限として得られる．そこで $e \in \operatorname{Met}(D)$ を $\varphi(Y)$ の $\operatorname{Met}(D)$ における閉包の点とし，$t_k \in Y$（$k \in \mathbb{N}$）を $\rho(d_{t_k}, e) \to 0$ となるように取る．$e \in \varphi(Y)$ を示す．

**手順 1（パラメータの回収）.** 基準対における値を比べると
$$|d_{t_k}(p,q) - e(p,q)| \le \rho(d_{t_k}, e) \longrightarrow 0$$
だから $1 + t_k \to e(p,q)$，すなわち $t_k \to t$（ここで $t := e(p,q) - 1$）．各 $t_k$ は $[0,1]$ に属し $[0,1]$ は $\mathbb{R}$ の閉集合だから $t \in [0,1]$．よって (C1) により $d_t$ は $D$ 上の距離として定まる（この段階では $d_t \in \operatorname{Met}(D)$ はまだ主張しない）．

**手順 2（極限の同定）.** (C4) の上界より
$$\rho(d_{t_k}, d_t) \le 2|t_k - t| \longrightarrow 0 .$$
したがって任意の $u,v \in D$ と任意の $k$ に対し
$$|e(u,v) - d_t(u,v)| \le |e(u,v) - d_{t_k}(u,v)| + |d_{t_k}(u,v) - d_t(u,v)| \le \rho(e, d_{t_k}) + \rho(d_{t_k}, d_t) .$$
右辺は $k \to \infty$ で $0$ に収束し，左辺は $k$ によらないから $|e(u,v) - d_t(u,v)| = 0$．$u,v$ は任意だから $e = d_t$．

**手順 3（境界の場合の排除）.** 仮定より $e \in \operatorname{Met}(D)$ であり，手順 2 より $d_t = e \in \operatorname{Met}(D)$ である．もし $t \in A$，すなわち $t = a_\beta$ となる $\beta < \omega_1$ が存在すれば，(C3) より $d_t \notin \operatorname{Met}(D)$ となって矛盾する．よって $t \notin A$，すなわち $t \in Y$．

以上より $e = d_t = \varphi(t) \in \varphi(Y)$．ゆえに $\varphi(Y)$ はその閉包を含み，$\operatorname{Met}(D)$ の閉集合である．∎

手順 3 が，パラメータの極限 $t$ が $A$ に落ちる境界の場合を扱う箇所である．そこでは $d_t$ が距離であり続けながら離散位相への適合性のみを失う（(C3)）ため，$e \in \operatorname{Met}(D)$ という仮定がその場合を排除する．この点が，$\varphi(Y)$ が閉である理由の核心である．

*状態: 執筆完了・独立レビュー通過（Issue #10, 2026-08-09）．依存関係: LEM-STAR-METRIC．*

#### 3.8 濃度条件 $|A| = \aleph_1$ の使用箇所

LEM-A-EXISTS が与える 2 つの条件は，以下のように役割が分かれる．

- **$A$ が $F_\sigma$ でないこと**は，主定理の証明の手順 2–3（$Y$ が $G_\delta$ でなく，したがって完全距離化可能でない）でのみ使う．
- **$|A| = \aleph_1$ という濃度条件**は，§3.2 の次の 2 箇所で使う．
  1. **添字付けの成立**．$A$ の単射列挙を $\{a_\alpha : \alpha < \omega_1\}$ の形，すなわち添字が $\omega_1$ の全体を走る形で取れるのは $|A| = \aleph_1$ のときに限る．星 $C_\alpha$ と距離 $s_n(\alpha,t)$ はこの列挙に沿って各 $\alpha < \omega_1$ に対して定義されているから，構成そのものがこの条件に依存する．
  2. **濃度計算**．$|D| = 2 + \aleph_1 + \aleph_1\cdot\aleph_0 = \aleph_1$ であること．THM-CONJ51 が要求する「濃度 $\aleph_1$ の離散空間」という指定と構成を整合させるために必要である．

一方，§3.2 の構成がひとたび与えられた後は，(C1)–(C5) の検証は添字集合 $\omega_1$ の濃度をまったく用いない．いずれの証明も，高々 3 点（(C1)），1 点とその補集合（(C2)），ただ 1 つの中心 $y_\beta$（(C3)），あるいは点対ごとの評価（(C4), (C5)）という局所的な議論であり，$a_\alpha \in A \subseteq [0,1]$ であることと，$t \in Y$ か $t \in A$ かという条件のみを使う．したがって濃度条件が効くのは構成の段階であって，検証の段階ではない．

なお，濃度が $\aleph_1$ でない $A$ に対して同型の構成を行うには，星を $\omega_1$ ではなく $A$ 自身で添字付け直し，$|D| = \aleph_1$ を保つための補充点を別に加える必要がある．本報告書ではその一般化を用いず，$|A| = \aleph_1$ を仮定したままとする．そもそも $A$ が $F_\sigma$ でないためには $A$ は非可算でなければならず（可算集合は一点集合の可算合併として $F_\sigma$ である），$|A| = \aleph_1$ は LEM-A-EXISTS が与える条件そのものである．

---

## 4. 主定理の証明

$|D| = \aleph_1$ の離散空間 $D$ に対して $\operatorname{Met}(D)$ が完全距離化可能でないことを示す．§3.1 より，$D$ としては LEM-STAR-METRIC の §3.2 で構成した具体的な集合を取ってよい．

1. **LEM-A-EXISTS** より，$A \subseteq [0,1]$，$|A| = \aleph_1$，$A \notin F_\sigma$ をとる．
2. $Y := [0,1] \setminus A$ とおく．一般に，全体集合 $X$ の部分集合 $S$ について，「$S$ が $F_\sigma$（可算個の閉集合の合併）」であることと「$X$ における補集合 $X \setminus S$ が $G_\delta$（可算個の開集合の共通部分）」であることは同値である：$S = \bigcup_n F_n$（$F_n$ は $X$ の閉集合）は，De Morgan の法則により $X\setminus S = \bigcap_n (X\setminus F_n)$（各 $X\setminus F_n$ は $X$ の開集合）と同値である．ここで $A$ と $Y=[0,1]\setminus A$ は，ともに全体集合を $[0,1]$ として扱っている（$[0,1]$ は $\mathbb{R}$ の閉集合だから，$[0,1]$ の部分集合に対しては「$[0,1]$ における閉性」と「$\mathbb{R}$ における閉性」が一致し，$F_\sigma$/$G_\delta$ の判定に曖昧さは生じない）．よって，$A$ が $[0,1]$ において $F_\sigma$ でないこと（LEM-A-EXISTS）から，$Y$ は $[0,1]$ において $G_\delta$ でない．
3. $[0,1]$ は可分距離化可能（実際 Polish 空間）だから，背景定理 1（Alexandrov–Lavrentiev 型の特徴づけ）の対偶が適用できる：$Y$ が $[0,1]$ の $G_\delta$ でないことから，$Y$ は（$[0,1]$ の部分空間として）完全距離化可能でない．
4. **LEM-STAR-METRIC** より，$Y$ でパラメトライズされた距離の族 $(d_t)_{t\in Y} \subseteq \operatorname{Met}(D)$ を取る．**LEM-CLOSED-IMAGE** より，写像 $\varphi: Y \to \operatorname{Met}(D)$，$t \mapsto d_t$ は $Y$ から像 $\varphi(Y)$ への同相写像であり，$\varphi(Y)$ は $\operatorname{Met}(D)$ の閉部分集合である．
5. $\operatorname{Met}(D)$ が完全距離化可能であると仮定する．背景定理 2（閉部分空間の遺伝性．可分性を用いない）より，閉部分集合 $\varphi(Y)$ も完全距離化可能である．完全距離化可能性は同相写像で保たれる位相的性質だから，手順 4 の同相 $Y \cong \varphi(Y)$ より $Y$ も完全距離化可能となる．これは手順 3 に矛盾する．
6. 従って $\operatorname{Met}(D)$ は完全距離化可能でない．∎

**位置づけ.** 手順 1–6 の各ステップには証明が付いており（手順 1 は §3 の LEM-A-EXISTS，手順 2–3 は §1 の背景定理 1 と De Morgan の法則，手順 4 は §3 の LEM-STAR-METRIC・LEM-CLOSED-IMAGE，手順 5 は §1 の背景定理 2），数学的に未記述のステップは残っていない．プロジェクト計画の Gate A–C（独立エンドツーエンド数学レビュー，Lean による形式化，形式化と報告書の言明の一致確認）はいずれも 2026-08-09 に通過し，証明候補ラベルは owner 裁定（PR #29 のコメント）により解除された．よって本報告書はこの議論を証明として提示する．ただし，ここでの検証はプロジェクト内部の独立監査と Lean による機械検証であり，外部の査読を経たことを示唆する表現は引き続き用いない．

---

## 5. 開問題・未解決事項

数学的な議論としては，主定理の証明を構成する全ステップが本報告書に記述されており，検証（独立レビューと Lean 形式化）も完了している．

- **独立エンドツーエンド数学レビュー**（Issue #10）：**完了（2026-08-09）**．Issue #2–#9 に関与していない監査者が §3–§4 の全議論を一次資料から独立に再構成し，数学的ギャップは見つからなかった．反例構成の試みとその失敗の記録，Lean 定理文との突き合わせ，監査者自身による `#print axioms` の再実行結果は `notes/proof-audit.md` の Issue #10 の項にある．この結果を受け，証明候補ラベルは owner 裁定（PR #29 のコメント，2026-08-09）により解除された．
- **Lean 4 による形式化**（Issue #6–#9, #23）：**完了（2026-08-09）**．$\operatorname{Met}(D)$ 型の構成（#6），LEM-STAR-METRIC（#7），LEM-A-EXISTS を含む集合論・記述集合論の前提（#8），LEM-CLOSED-IMAGE と最終的な組み立て（#9），Alexandrov–Lavrentiev 方向（#23）．リポジトリに `sorry` は残っておらず，`#print axioms thm_conj51` は標準の 3 公理のみを報告する．
- **英語論文の作成**（Issue #11）：**完了（2026-08-09）**．`paper/main.tex` は本報告書の監査済みの内容から書き起こされ，Issue #10 の指摘 F1（Polish 空間版の $G_\delta$ 特徴づけから閉部分空間の遺伝性を導く誤り，LEM-STAR-METRIC の主張文の不一致，付録の陳腐化）はすべて修正された．claim ID 単位の三者一致（paper・report・Lean）は E9（Issue #26）の突き合わせ表で確認済み．
- **形式化に向けた確認事項**：$\operatorname{Met}(D)$ が可分でないこと（§1 で用いた事実）は，4 つの安定 ID のいずれにも含まれない．Issue #10 の監査で明示的な非可分族（互いに素な対 $\{u_\alpha, v_\alpha\}$ の上で値を $1$ と $1/2$ に振り分けて得られる $2^{\aleph_1}$ 個の互いに距離 $1/2$ の元）が構成され，事実として確認された（`notes/proof-audit.md` の Issue #10 の項 A2）．本報告書の議論はこの事実に論理的には依存していない（$\operatorname{Met}(D)$ に対しては可分性を用いない背景定理 2 のみを使う）．

失敗した証明の試みと監査の記録は `notes/proof-audit.md` に，参考文献の検証記録は `notes/literature.md` に置く．

---

## 6. 参考文献

`notes/literature.md` を参照．一次資料: Ishiki, arXiv:2407.03030 (2024)．
