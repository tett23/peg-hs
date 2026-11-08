# ADR 0088: [ADR 0087](0087-other-labels-do-not-change-the-label-check.md) の二つめの例とテスト設計を直す

ステータス: 採択

## 文脈

[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) は、ほかのラベルが検査の判定を変える経路として、展開の深さと既知の文字列の二つを挙げた。
既知の文字列の例には、次の変更を使った。

```text
R <- 'a' 'b' { () }
```

を

```text
R <- ('a' ^m) 'b' { () }
```

に変えると、`l` に警告が出る、というものである。

実装の途中で、この例が誤りだと分かった。
`m` を外した文法は `R <- 'a' 'b'` ではなく、括弧の残った `R <- ('a') 'b' { () }` である。
括弧はグループ（`EGroup`）になり、検査は、グループを文字列と認めない。
この文法を main（6aa281b）をビルドした `peg-hs gen` にかけると、`m` がなくても `3:9: warning: the label l may reject valid input: where it fails, the alternative at 3:26 can match` が出た。
ほかのラベルを外した文法の上でも同じ警告が出るので、[ADR 0029](0029-label-safety-implementation-deviations.md) の定義どおりの判定である。
この例の警告は、`m` ではなく括弧によるものだった。

既知の文字列の経路そのものはある。
ラベルは後置で、括弧なしに一つの要素に付けられる。
`R` を次のように変えると、同じ `peg-hs gen` で、`l` と `m` の両方に警告が出た。

```text
R <- 'a' 'b' ^m { () }
```

`m` を外した文法は `R <- 'a' 'b' { () }` で、`l` には警告が出ない。
`m` の警告は、`'b'` で失敗したときに後の選択肢 `'a' 'x'` が一致しうるからで、ほかのラベルによらない。

[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) のテスト設計の一つめの項は、「文脈の節の二つの文法（`S_any` と `S_group`、`l` と `m`）で、ほかのラベルを足しても、もとのラベルの警告が変わらないこと」を確かめるとした。
括弧の例でこれを「`l` に警告が出ない」と確かめると、定義に反する判定を期待するテストになる。

## 実装すること

[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) のテスト設計の一つめの項のうち、`l` と `m` の文法の項を、次の二つのテストに置き換える。

- `R <- 'a' 'b' ^m { () }` の文法で、警告が `m` の一つだけであることを確かめる。今は `l` にも警告が出るので落ちる
- `R <- ('a' ^m) 'b' { () }` の文法の警告が、`m` を外した `R <- ('a') 'b' { () }` の文法の警告と同じであることを確かめる。今も通る

[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) のほかの決定（各ラベルをほかのラベルを外した文法と枠の上で判定すること、文書の更新、ほかのテスト）は変えない。
[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) のステータスを採択にするときは、ステータスの行に、二つめの例とテスト設計の該当の項はこの ADR で直したことを書く。

## 実装しないこと

- 括弧だけのグループを、検査が中身と同じに扱うようにすること。`('a')` と `'a'` は同じ言語を受け付けるので、扱えば精度は上がる。ただし、ほかのラベルの有無とは関係のない、検査の近似の問題である。必要になったら別の ADR にする

## テスト設計

実装することの節の二つのテストを、`packages/peg-grammar/test/Labels.hs` の「other labels do not change the verdict ([ADR 0087](0087-other-labels-do-not-change-the-label-check.md))」の群に足す。
一つめは、[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) の修正の前に落ち、修正の後に通ることを確かめる。

## トレードオフ

なし。

## 参考文献

なし。
