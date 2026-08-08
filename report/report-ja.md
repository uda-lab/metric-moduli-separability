# 証明報告書：石木予想 5.1

**出典:** Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 (2024)  
**状態:** 証明候補（未検証）  
**更新:** 2026-08-09

---

## 1. 記号と設定

- $D$：濃度 $\aleph_1$ の離散位相空間
- $\operatorname{Met}(D)$：$D$ の離散位相に**適合する**距離の全体，上限距離位相を装備する  
  （注意：$d \in \operatorname{Met}(D)$ とは，$d$ が $D$ 上の距離であり，$d$ が誘導する位相が $D$ の離散位相に一致することを意味する．集合 $D$ 上の全ての距離の全体とは異なる．）
- $\rho(d_1, d_2) := \sup_{x,y\in D} |d_1(x,y) - d_2(x,y)|$：$\operatorname{Met}(D)$ 上の上限距離
- $[0,1]$：実数の閉単位区間
- $\omega_1$：最小の非可算順序数

**背景定理 (Alexandrov).**  
完全距離化可能な空間（Polish 空間）の部分空間が完全距離化可能であることと，それが $G_\delta$ 集合であることは同値である．

**系（閉部分空間の遺伝性）.**  
完全距離化可能な空間の閉部分空間は完全距離化可能である．  
（Alexandrov の定理の系：閉集合は $G_\delta$ だから．）

---

## 2. 主定理

**THM-CONJ51.**  
$|D| = \aleph_1$ のとき，$\operatorname{Met}(D)$ は上限距離位相に関して完全距離化可能でない．

*状態: 証明候補，未検証*

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

- *$A$ が $F_\sigma$ でないこと（Baire のカテゴリ定理；$\mathsf{CH}$ に依存しない）.*  
  $A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は $[0,1]$ の閉集合）と仮定して矛盾を導く．$\mathbb{Q} \cap [0,1]$ は $[0,1]$ で稠密であり，$F_n \subseteq A$ より $F_n \cap \mathbb{Q} = \emptyset$．ゆえに $F_n$ は内点を持たない：もし $F_n$ が空でない開区間を含めば，その区間内の有理点が $F_n \subseteq A$ に属することになり $A \cap \mathbb{Q} = \emptyset$ に反する．内点を持たない閉集合は疎（nowhere dense）だから，$A$ は可算個の疎な閉集合の合併，すなわち $[0,1]$ における痩集合（meager set）である．一方 $\mathbb{Q} \cap [0,1] = \bigcup_{q \in \mathbb{Q}\cap[0,1]} \{q\}$ も可算個の疎な閉集合（一点集合）の合併だから痩集合．したがって $[0,1] = A \cup (\mathbb{Q}\cap[0,1])$ は二つの痩集合の合併，すなわち痩集合．しかし $[0,1]$ は完備距離空間であり，Baire のカテゴリ定理（例えば Kelley, *General Topology*, Theorem 34, p. 200，あるいは Willard, *General Topology*, Corollary 25.4）より，完備距離空間はそれ自身の中で痩集合になり得ない．これは矛盾．よって $A$ は $F_\sigma$ でない．

**場合 2：$\mathsf{CH}$ が成立しない場合（$\aleph_1 < \mathfrak{c}$）.**

次の補題を用いる．

> **補題（完全集合定理の系）.** $F \subseteq [0,1]$ が非可算な閉集合ならば $|F| = \mathfrak{c}$．
>
> *証明.* $F$ は $[0,1]$ の閉部分集合だから，それ自身 Polish 空間である．Cantor–Bendixson の定理（Kechris, *Classical Descriptive Set Theory*, GTM 156, 1995, §6，完全集合の性質は同書 p. 150 付近）より，$F$ は完全集合（perfect set）$P$ と可算集合 $C$ の非交和 $F = P \sqcup C$ に分解できる．$F$ が非可算で $C$ が可算だから $P \ne \emptyset$．空でない完全 Polish 空間は連続体濃度を持つ（標準的な Cantor 図式による埋め込み，同書 §6）から $|P| = \mathfrak{c}$．よって $|F| \ge |P| = \mathfrak{c}$．また $F \subseteq [0,1]$ より $|F| \le \mathfrak{c}$．ゆえに $|F| = \mathfrak{c}$．∎

$\aleph_1 \le \mathfrak{c} = |[0,1]|$ だから，$[0,1]$ の部分集合で濃度がちょうど $\aleph_1$ のものが存在する．そのような集合を一つ取り $A$ とする．$A$ が $F_\sigma$ であると仮定し，$A = \bigcup_{n\in\mathbb{N}} F_n$（各 $F_n$ は $[0,1]$ の閉集合）とする．各 $n$ について $F_n \subseteq A$ だから $|F_n| \le |A| = \aleph_1 < \mathfrak{c}$．したがって上の補題の対偶より，各 $F_n$ は可算．ゆえに $A = \bigcup_n F_n$ は可算個の可算集合の合併だから可算（可算選択公理；ZFC で常に利用可能）．これは $|A| = \aleph_1$（非可算）に矛盾．よって $A$ は $F_\sigma$ でない．

**結論.** 場合 1・場合 2 のいずれでも，$A \subseteq [0,1]$，$|A| = \aleph_1$，$A \notin F_\sigma$ を満たす集合が構成できる．両場合は排他的かつ網羅的（$\mathsf{CH}$ の真偽による分岐）だから，ZFC において LEM-A-EXISTS が成立する．∎

**別証（remark）：場合分けを回避する一様な構成.**  
場合分けを避けたい場合は，Bernstein 集合を用いた次の一様な構成もある．$[0,1]$ の Bernstein 集合 $B$（$B$ とその補集合がともに $[0,1]$ のすべての完全集合と交わるように，濃度 $\mathfrak{c}$ の超限帰納法で構成される集合；Oxtoby, *Measure and Category*, 2nd ed., p. 24）を一つ固定し，$B$ の部分集合で濃度 $\aleph_1$ のものを $A$ とする（$\aleph_1 \le \mathfrak{c} = |B|$ より存在する）．$A \subseteq B$ ゆえ $A$ は完全集合を部分集合として持たない：もし完全集合 $P \subseteq A \subseteq B$ ならば，$B$ の補集合は $P$ と交わるという Bernstein 集合の性質に反する．いま $A$ が $F_\sigma$，すなわち $A = \bigcup_n F_n$（$F_n$ 閉）であったとする．$A$ は非可算（$|A|=\aleph_1$）だから，ある $F_n$ は非可算閉集合．Cantor–Bendixson の定理より，非可算閉集合は空でない完全集合を含む．よってその完全集合は $F_n \subseteq A$ の部分集合，すなわち $A$ の完全部分集合となり，$A$ が完全集合を持たないことに反する．よって $A$ は $F_\sigma$ でない．この議論は $\mathsf{CH}$ の成否によらず一様に成立する．

*状態: **監査済み（独立レビュー前）**．場合 2 の議論は，以前の報告書で「$F_\sigma$ 集合としての構造から直接矛盾を導くことはより微妙で要検証」として未完成のまま残されていた部分を，完全集合定理（Cantor–Bendixson の定理の系）を用いた数え上げ論法に置き換えて完成させたものである．場合 1（Baire のカテゴリ定理）は $\mathsf{CH}$ の真偽に依存しない独立した議論であり，変更していない．旧スケッチの記録は `notes/proof-audit.md`（Failed / abandoned attempts）を参照．参考文献の詳細は `notes/literature.md` を参照．*

---

### LEM-STAR-METRIC

**主張.**  
$D$ 上に，パラメータ $t \in Y$（$Y = [0,1] \setminus A$）によってパラメトライズされた星型族の距離 $d_t \in \operatorname{Met}(D)$ が構成できる．

*状態: 未検証；依存関係: LEM-A-EXISTS*

---

### LEM-CLOSED-IMAGE

**主張.**  
写像 $\varphi: Y \to \operatorname{Met}(D)$，$t \mapsto d_t$ は双リプシッツ埋め込みであり，その像 $\varphi(Y)$ は $\operatorname{Met}(D)$ において閉である．

*状態: 未検証；依存関係: LEM-STAR-METRIC*

---

## 4. 主定理の証明（候補）

1. **LEM-A-EXISTS** より，$A \subset [0,1]$，$|A| = \aleph_1$，$A \notin F_\sigma$ をとる．
2. $Y := [0,1] \setminus A$ とおく．$A$ が $F_\sigma$ でないことより，$Y$ は $G_\delta$ でない．
3. Alexandrov の定理より，（Polish 空間 $[0,1]$ の部分空間として）$Y$ は完全距離化可能でない．
4. **LEM-CLOSED-IMAGE** より，$Y$ は $\operatorname{Met}(D)$ の閉部分空間に同相埋め込まれる．
5. $\operatorname{Met}(D)$ が完全距離化可能であれば，その閉部分空間も完全距離化可能（閉集合は $G_\delta$ だから Alexandrov の定理より）．これは 3 に矛盾する．
6. 従って $\operatorname{Met}(D)$ は完全距離化可能でない．∎（候補）

---

## 5. 開問題・未解決事項

- $\operatorname{Met}(D)$ が完全距離化可能な空間であるかどうかの先行知識の確認
- 星型距離族の具体的構成（LEM-STAR-METRIC）
- 像の閉性の証明（LEM-CLOSED-IMAGE）

詳細は `notes/proof-audit.md` を参照．

---

## 6. 参考文献

`notes/literature.md` を参照．一次資料: Ishiki, arXiv:2407.03030 (2024)．
