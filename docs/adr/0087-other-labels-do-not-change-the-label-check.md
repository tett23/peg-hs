# ADR 0087: ほかのラベルがラベルの検査の判定を変えないようにする

ステータス: 採択（未実装）

## 文脈

[ADR 0029](0029-label-safety-implementation-deviations.md) は、各ラベルを、ほかのラベルをすべて外した文法の上で判定すると定めた。
[ADR 0056](0056-label-insertion-and-template-deviations.md) は、選択肢の共通の部分を比べるときにほかのラベルを除くことで、比べ方をこの定義に合わせた。
`docs/syntax.md` も「ほかのラベルの有無で判定は変わらない」と書いている。

ところが、[ADR 0086](0086-inserted-labels-pass-the-label-check.md) の原因を調べると、検査（`Peg.Grammar.Labels.labelWarnings`）はこの定義から外れていた。
ほかのラベルが判定を変える経路は、コードを読んだ限りで二つある。

一つめは、後の選択肢の展開の深さである。
検査は、後の選択肢を一致した要素と比べるとき、先頭の規則の呼び出し、グループ、繰り返しを展開する（[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md)）。
展開は 8 段で打ち切り、それより深い区別は粗い比べ方に戻る。
この展開（`expansions`）が、ラベルの付いた要素を中身に置き換えることも一段に数えている。
そのため、ほかのラベルが段を使い、上限に早く達して警告することがある。

次の文法を、main（6aa281b）をビルドした `peg-hs gen` にかけた。

```text
%module M
S :: ()
S <- ((&(!.) &('a')) 'a' ('a' &(S 'b') . ^S_any)) (((S 'b') ('b' 'b') / (S) S)) { () }
```

この文法には警告が出ない。
二つめのグループに `^S_group` を付けると、`3:40: warning: the label S_any may reject valid input: where it fails, the alternative at 3:73 can match` が出た。
`S_any` の判定は、ほかのラベルをすべて外した文法の上では同じはずなので、定義どおりなら警告は変わらない。

二つめは、既知の文字列である。
検査は、一致した要素が文字列や、文字列だけからなる規則の呼び出しで始まるとき、入力の先頭の文字列を求め、後の選択肢がその文字列で必ず失敗するかを確かめる（`knownStrings`、[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md)）。
呼び出した規則の選択肢が文字列だけからなるかを確かめるところ（`sequenceLiterals`）が、ラベルの付いた文字列を文字列と認めない。

次の文法を、同じ `peg-hs gen` にかけた。

```text
%module M
S :: ()
S <- R ('c' ^l) { () } / 'a' 'x' { () }
R :: ()
R <- 'a' 'b' { () }
```

この文法には警告が出ない。
`R` を `R <- ('a' ^m) 'b' { () }` に変えると、`3:9: warning: the label l may reject valid input: where it fails, the alternative at 3:26 can match` が出た。
`m` は `R` の中のラベルで、`l` の判定とは関係がないはずである。

ほかの箇所（共通の部分の比較の `plainExpr`、文字列の上の評価の `simExpr`、先頭の文字の集合の `exprAbs`）は、ラベルを中身と同じに扱っている。
外れているのは、ラベルを外す処理を一つずつの箇所に書いてきたからである。
新しく比べ方を足すたびに、同じ外れが入りうる。

[ADR 0086](0086-inserted-labels-pass-the-label-check.md) は、挿入したラベルを検査にかけ直すことで、`peg-hs label` の結果に警告が出ないようにした。
その代わり、安全なのに挿入されないラベルが残り、もとからあったラベルの判定が挿入で変わる可能性も残った。
直すと検査の判定が変わるので、別の ADR にすると決めていた。

## 実装すること

### ほかのラベルを外した文法の上での判定

検査は、各ラベルを、ほかのラベルを外した文法と枠の上で判定する。
ラベルを外す処理を、比べ方の箇所ごとではなく、検査の入口の一か所に置く。

- 検査の文脈（`Ctx`）を、すべてのラベルを外した文法から作る。規則の選択肢（`ctxRules`）にラベルがなくなるので、呼び出しの展開と既知の文字列は、ほかのラベルに影響されない
- 各ラベルの位置の枠（`Frame`）からも、そのラベル以外のラベルを外す。外側のラベルの枠（`FLabel`）を除き、枠の持つ要素の列（`FSeq` の要素、`FAlts` の選択肢）の中のラベルを外す
- ラベルを外す処理は、ラベル（`ELabel`）を中身に置き換えるだけにする。`%recover` の宣言は残し、検査が回復の規則を知る方法（`ctxRecovery`）は変えない。`--strip-labels` の文法（`stripLabels`）とは違い、回復の規則を入口に足すことはしない。入口が変わると、規則の呼び出し元が変わり、判定が変わるからである
- `labelSafeAt`（ラベルの挿入の候補の判定）も、同じ文脈と枠で判定する

展開の深さの上限（8）と、展開の数の上限（64）は変えない。
ほかのラベルがなくなるので、ラベルの展開に段を使うことがなくなる。

[ADR 0086](0086-inserted-labels-pass-the-label-check.md) の、挿入の結果の検査は残す。
この ADR の後は、候補の判定と挿入した後の検査が同じ文法の上で行われるので、外れるラベルはないはずである。
ただし、この ADR が見落とした経路があったときに、`peg-hs label` の結果に警告が出ないことを保証する役が残る。

### 文書

- `docs/specifications.md` の既知の制限から「ほかのラベルによる検査の判定の変化」の項を除き、ラベルの安全性の項に、各ラベルをほかのラベルを外した文法の上で判定することがこの ADR で実装どおりになったと書く
- `docs/syntax.md` と `docs/syntax.en.md` の「ほかのラベルの有無で判定は変わらない」の文に、この ADR へのリンクを足す。冒頭の「反映している ADR」にこの ADR を足す
- peg-grammar の CHANGELOG に、判定が変わりうることを書く

## 実装しないこと

- 展開の深さと数の上限の変更
- キャプチャ（`ECapture`）と値の破棄（`EDiscard`）の扱いの変更。`sequenceLiterals` はこれらも文字列と認めないが、これらは判定する文法そのものの要素なので、ほかのラベルの有無とは関係がない。精度を上げるなら別の ADR にする
- [ADR 0086](0086-inserted-labels-pass-the-label-check.md) の、挿入の結果の検査の削除
- `%safe` の扱いの変更。`%safe` はこれまでどおり、名前の一致したラベルの警告を止める

## テスト設計

先に書いて失敗させてから実装する。
テストは `packages/peg-grammar/test/Labels.hs` に足す。

- 文脈の節の二つの文法（`S_any` と `S_group`、`l` と `m`）で、ほかのラベルを足しても、もとのラベルの警告が変わらないことを確かめる。今はどちらも落ちる
- プロパティ「ほかのラベルは判定を変えない」を足す。無作為な文法に無作為にラベルを付け、各ラベルの警告の有無が、そのラベルだけを残した文法での警告の有無と一致することを確かめる。文法の生成器は、[ADR 0054](0054-automatic-label-insertion.md) のプロパティの生成器（`packages/peg-grammar/test/LabelInsertion.hs`）を使う。今は落ちる見込みである
- `packages/peg-grammar/test/LabelInsertion.hs` に、文脈の節の一つめの文法で、`insertLabels` が `^S_any` も挿入することを確かめるテストを足す。今は [ADR 0086](0086-inserted-labels-pass-the-label-check.md) の検査が外すので落ちる
- [ADR 0086](0086-inserted-labels-pass-the-label-check.md) の二つめの反例で、`insertLabels` の挿入の結果の検査が外すラベルの数を、プルリクエストに書く。0 にならなければ、残った経路を調べてプルリクエストに書く
- 既存のプロパティ「the warnings of the labels already there stay」と「the labelled grammar accepts the same language, and has no new warnings」を、ふだんの 10 倍の件数で一度実行して、落ちないことを確かめる。結果をプルリクエストに書く
- 既存のラベルの警告の golden と、リポジトリの文法（conformance、フィクスチャ、`docs/syntax.md` と `docs/syntax.en.md` の例）の警告と `peg-hs label` の結果が変わらないことを確かめる。変わった場合は、変わった文法とラベルと警告をプルリクエストに書き、警告が増えたものは、ほかのラベルを外した文法で定義どおりの判定であることを確かめる

## トレードオフ

- 判定が変わる。この ADR で警告が消えるラベルのほかに、ほかのラベルが展開を打ち切らせていたおかげで警告されなかったラベルがあれば、警告が出るようになりうる。深く展開すると比べる組み合わせが増え、展開の数の上限に達して粗い比べ方に戻ることもあるからである。利用者の文法で警告が増えた場合は、`%safe` を付けるか文法を直す必要がある
- ラベルの位置ごとに枠からほかのラベルを外すので、検査が少し遅くなる。外すのは枠の持つ要素の列だけで、文脈は一度だけ作る
- 文脈をラベルのない文法から作ると、規則の中のラベルの位置は文脈から失われる。検査がラベルの位置を使うのは、判定するラベル自身の枠だけなので、判定には影響しない

## 参考文献

- Medeiros, S. Q., Alvez Junior, G. A., Mascarenhas, F. 2020. Automatic Syntax Error Reporting and Recovery in Parsing Expression Grammars. Science of Computer Programming 187.
