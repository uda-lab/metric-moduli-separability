# 石木予想 5.1 の証明

本報告書では，Ishiki [1] の Conjecture 5.1，すなわち濃度 $\aleph_1$ の離散位相空間 $D$ に対して $\operatorname{Met}(D)$ が完全距離化可能でないことを，ZFC の定理として証明する．

## 1. 記号と設定

| 記号 | 意味 |
|---|---|
| $D$ | 濃度 $\aleph_1$ の離散位相空間 |
| $\operatorname{Met}(D)$ | $D$ の離散位相と**両立する**距離の全体．上限距離位相を備える |
| $\rho(d_1, d_2)$ | $\sup_{x,y\in D} \lvert d_1(x,y) - d_2(x,y)\rvert$（$\operatorname{Met}(D)$ 上の上限距離） |
| $[0,1]$ | 実数の閉単位区間 |
| $\omega_1$ | 最小の非可算順序数 |
| $\aleph_1$ | 最小の非可算基数 |
| $\mathfrak{c}$ | 連続体濃度 $2^{\aleph_0}$ |
| $S^\complement$ | 部分集合 $S \subseteq [0,1]$ の補集合 $[0,1] \setminus S$．本報告書で補集合は常に全体集合 $[0,1]$ でとる |

$D$ 上の距離 $d$ が $D$ の離散位相と**両立する**とは，$d$ の誘導する位相が $D$ の離散位相に一致することをいう．したがって $\operatorname{Met}(D)$ は集合 $D$ 上の距離すべての集合ではない．離散でない位相を誘導する距離は $\operatorname{Met}(D)$ に属さない．

基数については，Cantor の定理より $\aleph_0 < \mathfrak{c}$ であり，$\aleph_1$ は最小の非可算基数だから $\aleph_1 \le \mathfrak{c}$ が ZFC で成り立つ．

**定理 1.1（完全距離化可能部分空間の $G_\delta$ 性 [2, Theorem 3.11]）.**
$X$ を距離化可能空間，$S \subseteq X$ を相対位相に関して完全距離化可能な部分空間とする．このとき $S$ は $X$ の $G_\delta$ 集合である．

本報告書では，この定理を対偶の形で $X = [0,1]$ に対してのみ用いる（§4 手順 3）．同じ一般形は [3, Theorems 4.3.23–4.3.24] および [4, Theorem 24.12] にもある．

**定理 1.2（閉部分空間の完全距離化可能性）.**
$X$ を完全距離化可能な空間，$Y \subseteq X$ を閉部分集合とする．このとき $Y$ は相対位相に関して完全距離化可能である．

*証明.* $X$ の位相を与える完備距離 $d$ を一つとる．$d|_{Y \times Y}$ は $Y$ の相対位相を与える距離だから，これが完備であることを示せばよい．$(x_n)_n$ を $(Y, d|_Y)$ の Cauchy 列とすると，$(x_n)_n$ は $(X, d)$ の Cauchy 列でもあるから，ある $x \in X$ に収束する．距離空間の閉集合は点列の極限で閉じているから $x \in Y$ である．よって $(x_n)_n$ は $(Y, d|_Y)$ において $x$ に収束し，$d|_Y$ は完備である．∎

この証明は $X$ の可分性を用いない．本報告書で $\operatorname{Met}(D)$ に適用する完全距離化可能性についての事実は定理 1.2 のみである（§4 手順 5）．

**Remark（上限距離の値域）.** 上限距離 $\rho(d_1, d_2)$ は，$d_1, d_2$ が非有界で差が非有界のとき $+\infty$ をとりうる．しかし $\min(\rho, 1)$ は $\rho$ と同一の位相を定める有限値の距離だから，$\operatorname{Met}(D)$ は通常の意味で距離化可能であり，完全距離化可能性は位相のみで定まる性質だから，このことは以下の議論に影響しない．なお §3 で構成する距離族の値域はすべて $[0,2]$ に含まれ，そこで現れる $\rho$ の値はすべて有限である．

## 2. 主定理

**定理 2.1（石木予想 5.1）.**
$\lvert D\rvert = \aleph_1$ ならば，$\operatorname{Met}(D)$ は上限距離位相に関して完全距離化可能でない．

証明は §4 で与える．§3 で必要な補題を準備する．

## 3. 補題

### 3.1 $F_\sigma$ でない濃度 $\aleph_1$ の集合

**補題 3.1（閉集合の濃度）.**
$F \subseteq [0,1]$ を閉集合とする．$\lvert F\rvert < \mathfrak{c}$ ならば $F$ は可算である．

*証明.* 対偶を示す．$F$ を非可算な閉集合とする．$F$ は $[0,1]$ の閉部分集合だからそれ自身 Polish 空間であり，Cantor–Bendixson の定理 [2, Theorem 6.4] より完全集合 $P$ と可算集合 $C$ の非交和 $F = P \sqcup C$ に分解できる．$F$ が非可算で $C$ が可算だから $P \ne \emptyset$ であり，空でない完全 Polish 空間は濃度 $\mathfrak{c}$ を持つ [2, Theorem 6.2, Corollary 6.3]．よって $\lvert F\rvert \ge \lvert P\rvert = \mathfrak{c}$ である．∎

**補題 3.2（$F_\sigma$ でない集合の存在）.**
$F_\sigma$ でない濃度 $\aleph_1$ の集合 $A \subseteq [0,1]$ が存在する．

*証明.* 連続体仮説 $\mathsf{CH}$（$\aleph_1 = \mathfrak{c}$）の成否で場合を分ける．

**場合 1（$\mathsf{CH}$ が成立するとき）.** $A := [0,1] \setminus \mathbb{Q}$（$[0,1]$ 内の無理数全体）とおく．$\lvert[0,1]\rvert = \mathfrak{c}$ で $\mathbb{Q} \cap [0,1]$ は可算だから $\lvert A\rvert = \mathfrak{c}$ であり，$\mathsf{CH}$ より $\lvert A\rvert = \aleph_1$．

$A$ が $F_\sigma$ でないことを示す（この部分は $\mathsf{CH}$ を用いない）．$A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は $[0,1]$ の閉集合）と仮定する．$\mathbb{Q} \cap [0,1]$ は $[0,1]$ で稠密で $F_n \cap \mathbb{Q} = \emptyset$ だから，各 $F_n$ は内点を持たない閉集合，したがって疎（nowhere dense）である．$\mathbb{Q} \cap [0,1]$ も可算個の一点集合の合併として痩集合（meager set）だから，$[0,1] = A \cup (\mathbb{Q} \cap [0,1])$ は $[0,1]$ の痩集合となり，完備距離空間は自身の中で痩せていないという Baire のカテゴリ定理 [4, Corollary 25.4] に反する．よって $A$ は $F_\sigma$ でない．

**場合 2（$\mathsf{CH}$ が成立しないとき，$\aleph_1 < \mathfrak{c}$）.** $\aleph_1 \le \mathfrak{c} = \lvert[0,1]\rvert$ だから，濃度 $\aleph_1$ の部分集合 $A \subseteq [0,1]$ が存在する．$A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は閉集合）と仮定すると，各 $n$ について $\lvert F_n\rvert \le \lvert A\rvert = \aleph_1 < \mathfrak{c}$ だから，補題 3.1 より $F_n$ は可算である．よって $A$ は可算個の可算集合の合併として可算となり，$\lvert A\rvert = \aleph_1$ に矛盾する．ゆえに $A$ は $F_\sigma$ でない．∎

**Remark（場合分けを避ける構成）.** $\mathsf{CH}$ による場合分けを避けるなら，Bernstein 集合による一様な構成もある．$B$ と $B^\complement$ がともに $[0,1]$ のすべての非可算閉集合と交わるような集合 $B \subseteq [0,1]$（Bernstein 集合，$\lvert B\rvert = \mathfrak{c}$）が超限帰納法で構成できる [5, p. 24]．濃度 $\aleph_1$ の部分集合 $A \subseteq B$ をとる．$A = \bigcup_n F_n$（各 $F_n$ は閉集合）と書ければ，$A$ は非可算だからある $F_n$ は非可算閉集合であり，$F_n \subseteq B$ は $B^\complement$ がすべての非可算閉集合と交わることに反する．よってこの $A$ も $F_\sigma$ でなく，この議論は $\mathsf{CH}$ の成否によらない．

### 3.2 設定の正規化

補題 3.3 以降では，$D$ を §3.3 で定める具体的な集合にとる．これで一般性を失わないことを先に確認する．離散位相空間の位相型はその濃度のみで定まり，離散空間の間の全単射 $f : D \to D'$ は同相写像である．対応 $d \mapsto d \circ (f \times f)$ は $D'$ 上の距離を $D$ 上の距離に移し，誘導する位相を保つから，$\operatorname{Met}(D')$ から $\operatorname{Met}(D)$ への全単射を与える（逆写像は $f^{-1}$ による同じ対応）．さらに $\sup$ をとる添字集合が $f \times f$ で全単射に移り合うから，この対応は上限距離 $\rho$ を保つ．すなわち等長同型である．したがって $\operatorname{Met}(D)$ の距離空間としての（特に位相空間としての）同型類は $\lvert D\rvert$ のみで定まる．

### 3.3 距離族の構成

補題 3.2 の与える $A \subseteq [0,1]$（$\lvert A\rvert = \aleph_1$，$A$ は $F_\sigma$ でない）と，単射な列挙
$$A = \{a_\alpha : \alpha < \omega_1\}, \qquad \alpha \ne \beta \implies a_\alpha \ne a_\beta$$
を固定する．

**補題 3.3（距離族の構成）.**
濃度 $\aleph_1$ の離散空間 $D$ と，$D$ 上の距離の族 $(d_t)_{t \in [0,1]}$ であって
$$d_t \in \operatorname{Met}(D) \iff t \in A^\complement$$
を満たすものが存在する．

**構成.** 台集合を
$$D := \{p, q\} \ \sqcup\ \{y_\alpha : \alpha < \omega_1\} \ \sqcup\ \{x_{\alpha,n} : \alpha < \omega_1,\ n \in \mathbb{N}\}$$
（三つの部分は互いに交わらず，各添字は相異なる元を与える）で定め，離散位相を与える．濃度は
$$\lvert D\rvert = 2 + \aleph_1 + \aleph_1 \cdot \aleph_0 = \aleph_1$$
である．$\alpha < \omega_1$ に対して
$$C_\alpha := \{y_\alpha\} \cup \{x_{\alpha,n} : n \in \mathbb{N}\}$$
とおくと，
$$D = \{p,q\} \ \sqcup \bigsqcup_{\alpha<\omega_1} C_\alpha$$
は $D$ の分割である．

$t \in [0,1]$，$\alpha < \omega_1$，$n \in \mathbb{N}$ に対して
$$s_n(\alpha, t) := \min\bigl(1,\ \lvert t - a_\alpha\rvert + 1/(n+1)\bigr)$$
とおく．$0 < s_n(\alpha,t) \le 1$ である．

$t \in [0,1]$ に対し，写像 $d_t : D \times D \to [0,2]$ を，$d_t(u,u) := 0$ と，相異なる 2 点の非順序対に対する次の表とで定める（表は非順序対に値を与えるから，$d_t$ は対称である）．

| 非順序対 $\{u,v\}$ | $d_t(u,v)$ |
|---|---|
| $\{p,\ q\}$ | $1 + t$ |
| $\{y_\alpha,\ x_{\alpha,n}\}$ | $s_n(\alpha,t)$ |
| $\{x_{\alpha,n},\ x_{\alpha,m}\}$（$n \ne m$） | $s_n(\alpha,t) + s_m(\alpha,t)$ |
| 上記以外（分割の相異なる要素に属する 2 点） | $1$ |

補題 3.3 の主張を，(C1) $d_t$ は距離である，(C2) $t \in A^\complement$ ならば $d_t \in \operatorname{Met}(D)$，(C3) $t \in A$ ならば $d_t \notin \operatorname{Met}(D)$，の三つに分けて示す．

**(C1) 任意の $t \in [0,1]$ に対し，$d_t$ は $D$ 上の距離である．**

*証明.* 対称性と $d_t(u,u) = 0$ は定義による．表の各値は正だから，$d_t(u,v) = 0$ と $u = v$ は同値である．

三角不等式 $d_t(u,w) \le d_t(u,v) + d_t(v,w)$ は，$u,v,w$ のうちに一致する 2 点があれば自明だから，相異なる 3 点について示す．$\alpha$ を固定した文脈では $s_n := s_n(\alpha,t)$ と略記する．表より，相異なる 2 点の距離は常に $2$ 以下であり，分割の相異なる要素に属する 2 点の距離は $1$ である．3 点が分割とどう交わるかで場合を分ける．

**場合 (a)　3 点が分割の同一要素に属する.** $\{p,q\}$ は 2 元集合だから，その要素はある $C_\alpha$ である．3 点が $y_\alpha,\ x_{\alpha,n},\ x_{\alpha,m}$（$n \ne m$）のとき，検証すべき不等式は
$$s_n + s_m \le s_n + s_m \quad (y_\alpha \text{ 経由}), \qquad s_n \le (s_n + s_m) + s_m \quad (x_{\alpha,m} \text{ 経由})$$
の 2 つ（残りはその対称形）であり，いずれも成り立つ．3 点が $x_{\alpha,n},\ x_{\alpha,m},\ x_{\alpha,k}$（添字は相異なる）のときは
$$s_n + s_m \le (s_n + s_k) + (s_k + s_m).$$

**場合 (b)　ちょうど 2 点が分割の同一要素 $E$ に属する.** $u, v \in E$，$z \notin E$ とすると $d_t(u,z) = d_t(v,z) = 1$ だから
$$d_t(u,v) \le 2 = d_t(u,z) + d_t(z,v), \qquad d_t(u,z) = 1 \le d_t(u,v) + d_t(v,z).$$

**場合 (c)　3 点が分割の相異なる 3 要素に属する.** 3 つの対の距離はすべて $1$ であり，$1 \le 1 + 1$．

場合 (a)–(c) は 3 点の配置を尽くすから，三角不等式が成り立つ．∎

**(C2) $t \in A^\complement$ ならば $d_t \in \operatorname{Met}(D)$ である．**

*証明.* 距離 $d$ の誘導する位相が離散位相であることは，各 $u \in D$ に対して
$$\delta(u) := \inf_{v \in D,\ v \ne u} d(u,v) > 0$$
が成り立つことと同値である．$t \in A^\complement$ を固定し，各点でこれを確かめる．

- $u = p$ のとき，$d_t(p,q) = 1+t \ge 1$ で他のすべての点への距離は $1$ だから $\delta(p) = 1$．$u = q$ も同様に $\delta(q) = 1$．
- $u = x_{\alpha,n}$ のとき，$u$ から出る距離の値は $s_n(\alpha,t)$（$y_\alpha$ へ），$s_n(\alpha,t) + s_m(\alpha,t)$（$x_{\alpha,m}$，$m \ne n$ へ），$1$（$C_\alpha$ の外へ）だから，$s_n(\alpha,t) \le 1$ より
  $$\delta(x_{\alpha,n}) = s_n(\alpha,t) \ge 1/(n+1) > 0.$$
- $u = y_\alpha$ のとき，値は $s_n(\alpha,t)$（$n \in \mathbb{N}$）と $1$ である．$n \to \infty$ のとき $\lvert t-a_\alpha\rvert + 1/(n+1) \downarrow \lvert t-a_\alpha\rvert$ であり，$r \mapsto \min(1,r)$ は連続かつ単調非減少だから
  $$\delta(y_\alpha) = \min\bigl(1, \lvert t - a_\alpha\rvert\bigr).$$
  $t \in A^\complement$ かつ $a_\alpha \in A$ より $t \ne a_\alpha$ だから $\delta(y_\alpha) > 0$．

よって $d_t$ の誘導する位相は離散位相であり，(C1) と合わせて $d_t \in \operatorname{Met}(D)$．∎

**(C3) $t \in A$ ならば $d_t \notin \operatorname{Met}(D)$ である．**

*証明.* $t = a_\beta$（$\beta < \omega_1$）とする．(C1) より $d_{a_\beta}$ は $D$ 上の距離である．一方
$$s_n(\beta, a_\beta) = \min\bigl(1,\ 1/(n+1)\bigr) = 1/(n+1)$$
だから $d_{a_\beta}(y_\beta, x_{\beta,n}) = 1/(n+1)$ であり，任意の $\varepsilon > 0$ に対し $1/(n+1) < \varepsilon$ となる $n \in \mathbb{N}$ をとれば，$y_\beta$ の $\varepsilon$-近傍は $x_{\beta,n} \ne y_\beta$ を含む．よって $\{y_\beta\}$ は開でなく，$d_{a_\beta}$ の誘導する位相は離散位相と異なる．∎

(C2) と (C3) より $d_t \in \operatorname{Met}(D) \iff t \in A^\complement$ が成り立ち，補題 3.3 が示された．∎

### 3.4 閉埋め込み

**補題 3.4（閉埋め込み）.**
$A^\complement$ に $[0,1]$ からの相対位相を与える．写像 $\varphi : A^\complement \to \operatorname{Met}(D)$，$t \mapsto d_t$ は双リプシッツ埋め込みであり，像 $\varphi(A^\complement)$ は $\operatorname{Met}(D)$ の閉集合である．

補題 3.3 の $A$，$D$，$(d_t)_{t \in [0,1]}$ をそのまま用いる．距離族の値域が $[0,2]$ に含まれるから，以下に現れる $\rho$ の値はすべて有限である．主張を (C4)（双リプシッツ評価）と (C5)（像の閉性）に分けて示す．

**(C4) 任意の $s, t \in [0,1]$ に対して $\lvert t - s\rvert \le \rho(d_t, d_s) \le 2\,\lvert t - s\rvert$．**

*証明.* 下界は $\lvert d_t(p,q) - d_s(p,q)\rvert = \lvert(1+t)-(1+s)\rvert = \lvert t-s\rvert$ による．上界は，各非順序対で $\lvert d_t(u,v) - d_s(u,v)\rvert \le 2\lvert t-s\rvert$ を確かめて上限をとればよい．$\{p,q\}$ では差は $\lvert t-s\rvert$．$r \mapsto \min(1,r)$ と $r \mapsto \lvert r - a_\alpha\rvert + 1/(n+1)$ はともに $1$-Lipschitz だから合成 $r \mapsto s_n(\alpha,r)$ も $1$-Lipschitz であり，$\{y_\alpha, x_{\alpha,n}\}$ では差は高々 $\lvert t-s\rvert$，$\{x_{\alpha,n}, x_{\alpha,m}\}$ では高々 $2\lvert t-s\rvert$．その他の対では値は $t$ によらず $1$ で，差は $0$．∎

**系.** (C2) より $\varphi(t) := d_t$ は $A^\complement$ から $\operatorname{Met}(D)$ への写像を定める．(C4) の下界より $\varphi$ は単射であり，両側評価より $\varphi$ は $A^\complement$ から像 $\varphi(A^\complement)$（$\operatorname{Met}(D)$ の相対位相を与える）への双リプシッツ同相，すなわち双リプシッツ埋め込みである．

**(C5) $\varphi(A^\complement)$ は $\operatorname{Met}(D)$ の閉集合である．**

*証明.* $\operatorname{Met}(D)$ の位相は距離 $\min(\rho,1)$ が定めるから，閉包の点は点列の極限として得られる．$e \in \operatorname{Met}(D)$ を $\varphi(A^\complement)$ の閉包の点とし，$t_k \in A^\complement$（$k \in \mathbb{N}$）を $\rho(d_{t_k}, e) \to 0$ となるように取る．$e \in \varphi(A^\complement)$ を示す．

**手順 1（パラメータの回収）.** $\lvert d_{t_k}(p,q) - e(p,q)\rvert \le \rho(d_{t_k}, e) \to 0$ より $1 + t_k \to e(p,q)$，すなわち $t_k \to t := e(p,q) - 1$ である．各 $t_k \in [0,1]$ で $[0,1]$ は閉だから $t \in [0,1]$ であり，(C1) より $d_t$ は $D$ 上の距離として定まる（$d_t \in \operatorname{Met}(D)$ はまだ主張しない）．

**手順 2（極限の同定）.** $u, v \in D$ を任意に固定する．(C4) より $\rho(d_{t_k}, d_t) \le 2\lvert t_k - t\rvert \to 0$ だから
$$\lvert e(u,v) - d_t(u,v)\rvert \le \rho(e, d_{t_k}) + \rho(d_{t_k}, d_t) \longrightarrow 0 \quad (k \to \infty)$$
であり，左辺は $k$ によらないから $e(u,v) = d_t(u,v)$．よって $e = d_t$．

**手順 3（$t \in A$ の排除）.** 仮定より $e \in \operatorname{Met}(D)$ だから，手順 2 より $d_t = e \in \operatorname{Met}(D)$ である．$t \in A$ ならば (C3) より $d_t \notin \operatorname{Met}(D)$ となって矛盾するから，$t \in A^\complement$ である．

以上より $e = d_t = \varphi(t) \in \varphi(A^\complement)$ となり，$\varphi(A^\complement)$ は閉である．∎

パラメータの極限が $A$ に落ちる場合を排除できることが閉性の本質であり，それを与えるのが (C3) である．(C4) の系と (C5) より補題 3.4 が示された．∎

## 4. 主定理の証明

**定理 2.1 の証明.** §3.2 より，$D$ としては §3.3 で構成した具体的な集合を取ってよい．

1. 補題 3.2 の $A \subseteq [0,1]$（$\lvert A\rvert = \aleph_1$，$A$ は $F_\sigma$ でない）をとる．
2. $F_\sigma$ と $G_\delta$ の補集合双対により，$A$ が $[0,1]$ で $F_\sigma$ でないことから，$A^\complement$ は $[0,1]$ で $G_\delta$ でない．
3. 定理 1.1 の対偶を距離化可能空間 $X = [0,1]$ に適用して，$A^\complement$ は $[0,1]$ の部分空間として完全距離化可能でない．
4. 補題 3.3・補題 3.4 より，$\varphi : A^\complement \to \operatorname{Met}(D)$，$t \mapsto d_t$ は像 $\varphi(A^\complement)$ への同相写像であり，$\varphi(A^\complement)$ は $\operatorname{Met}(D)$ の閉部分集合である．
5. $\operatorname{Met}(D)$ が完全距離化可能であると仮定すると，定理 1.2 より閉部分集合 $\varphi(A^\complement)$ も完全距離化可能であり，完全距離化可能性は同相で保たれるから，手順 4 の同相より $A^\complement$ も完全距離化可能となる．これは手順 3 に矛盾する．
6. よって $\operatorname{Met}(D)$ は完全距離化可能でない．∎

**Remark（濃度条件 $\lvert A\rvert = \aleph_1$ の使用箇所）.** 補題 3.2 の与える 2 条件の役割は分かれている．$A$ が $F_\sigma$ でないことは手順 2–3 でのみ用いる．濃度条件 $\lvert A\rvert = \aleph_1$ は §3.3 の構成の 2 箇所，すなわち $A$ の $\omega_1$ による単射列挙と，濃度計算 $\lvert D\rvert = 2 + \aleph_1 + \aleph_1 \cdot \aleph_0 = \aleph_1$ とで用いる．構成がひとたび与えられた後は，(C1)–(C5) の検証は濃度を用いない．

## 5. 参考文献

1. Y. Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 (2024).
2. A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer-Verlag, 1995.
3. R. Engelking, *General Topology*, revised ed., Sigma Series in Pure Mathematics 6, Heldermann Verlag, 1989.
4. S. Willard, *General Topology*, Addison-Wesley, 1970（Dover 版 2004）.
5. J. C. Oxtoby, *Measure and Category*, 2nd ed., Graduate Texts in Mathematics 2, Springer-Verlag, 1980.
