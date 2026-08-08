# 証明報告書：石木予想 5.1

**出典:** Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 (2024)  
**状態:** 証明候補（未検証）  
**更新:** 2026-08-08

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
ZFC において，$A \subset [0,1]$，$|A| = \aleph_1$，かつ $A$ が $F_\sigma$ でない集合が存在する．

**証明の方針（候補，要検証）.**

次の場合分けを用いる：

- **$\mathsf{CH}$ が成立する場合**（$\aleph_1 = 2^{\aleph_0}$）:  
  $[0,1]$ の無理数全体の集合 $\mathbb{P} \cap [0,1]$ を考える．$|\mathbb{P} \cap [0,1]| = 2^{\aleph_0} = \aleph_1$．また $\mathbb{P} \cap [0,1]$ は $G_\delta$ だが $F_\sigma$ ではない（Baire カテゴリ論より）．よって $A := \mathbb{P} \cap [0,1]$ が求める集合の候補となる．

- **$\mathsf{CH}$ が成立しない場合**（$\aleph_1 < 2^{\aleph_0}$）:  
  任意の可算個の閉集合の合併は閉集合の可算族を成す．$[0,1]$ の閉集合で非可算なものの濃度は連続体濃度 $2^{\aleph_0}$ である（完全集合定理）．従って，$[0,1]$ の濃度 $\aleph_1$ の部分集合 $A$ が $F_\sigma$ であれば，$A$ はある閉集合 $F \subset [0,1]$ に含まれ $|F| \geq \aleph_1$ となるが，そのような $F$ の濃度は $2^{\aleph_0} > \aleph_1$ となる矛盾は生じない——しかし $F_\sigma$ 集合としての構造から直接矛盾を導くことはより微妙で，要検証である．

*状態: 未検証；この証明スケッチはいずれの場合も独立した検証が必要*

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

- LEM-A-EXISTS の両ケース（CH あり・なし）の詳細な検証
- $\operatorname{Met}(D)$ が完全距離化可能な空間であるかどうかの先行知識の確認
- 星型距離族の具体的構成（LEM-STAR-METRIC）
- 像の閉性の証明（LEM-CLOSED-IMAGE）

詳細は `notes/proof-audit.md` を参照．

---

## 6. 参考文献

`notes/literature.md` を参照．一次資料: Ishiki, arXiv:2407.03030 (2024)．
