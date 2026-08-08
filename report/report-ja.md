# 証明報告書：石木予想 5.1

**状態:** 証明候補（未検証）  
**更新:** 2026-08-08

---

## 1. 記号と設定

- $D$：濃度 $\aleph_1$ の離散空間
- $\operatorname{Met}(D)$：$D$ 上の距離の全体，上限距離位相を装備する
- $[0,1]$：実数の閉単位区間
- $\omega_1$：最小の非可算順序数

完全距離空間の閉部分空間は完全距離化可能である（Alexandrov の定理）。  
完全距離化可能でない空間を完全距離化可能な空間に閉埋め込めるならば矛盾が生じる。

---

## 2. 主定理

**THM-CONJ51.**  
$|D| = \aleph_1$ のとき，$\operatorname{Met}(D)$ は上限距離位相に関して完全距離化可能でない。

*状態: 証明候補，未検証*

---

## 3. 補題

### LEM-A-EXISTS

**主張.**  
ZFC において，$A \subset [0,1]$，$|A| = \aleph_1$，かつ $A$ が $F_\sigma$ でない集合が存在する。

**証明の方針（候補）.**  
- 連続体仮説を仮定しない場合（$\aleph_1 < 2^{\aleph_0}$），$[0,1]$ の実数からオメガ 1 個を選ぶ．Bernstein 集合の構成などを用いる（要検証）．
- 連続体仮説を仮定する場合，別の構成が必要な可能性がある（要検証）．

*状態: 未検証；依存関係: ZFC の基本公理*

---

### LEM-STAR-METRIC

**主張.**  
$D$ 上に，あるパラメータ $t \in Y$（$Y = [0,1] \setminus A$）によってパラメトライズされた星型族の距離 $d_t \in \operatorname{Met}(D)$ が構成できる．

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
3. Alexandrov の定理（$G_\delta$ の特徴付け）より，$Y$ は完全距離化可能でない．
4. **LEM-CLOSED-IMAGE** より，$Y$ は $\operatorname{Met}(D)$ の閉部分空間に同相埋め込まれる．
5. $\operatorname{Met}(D)$ が完全距離化可能であれば，その閉部分空間も完全距離化可能（Alexandrov の定理）．これは 3 に矛盾する．
6. 従って $\operatorname{Met}(D)$ は完全距離化可能でない．∎（候補）

---

## 5. 開問題・未解決事項

- LEM-A-EXISTS の ZFC 的根拠の厳密化（CH 非仮定の場合）
- $Y$ の $G_\delta$ でないことから完全距離化不可能を導く補題の詳細
- 星型距離族の具体的構成
- 像の閉性の証明

詳細は `notes/proof-audit.md` を参照。

---

## 6. 参考文献

`notes/literature.md` を参照。
