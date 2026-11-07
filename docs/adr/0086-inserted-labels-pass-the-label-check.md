# ADR 0086: 挿入したラベルが、ラベルの検査で警告されないようにする

ステータス: 採択（未実装）

## 文脈

`peg-hs label` は、ラベルの検査が安全と判定する位置にだけラベルを挿入する（[ADR 0054](0054-automatic-label-insertion.md)）。
挿入したラベルは文法の言語を変えず、`peg-hs gen` の検査も警告を出さない、というのが [ADR 0054](0054-automatic-label-insertion.md) の約束である。
テストのプロパティ「the labelled grammar accepts the same language, and has no new warnings」が、この約束を確かめている（`packages/peg-grammar/test/LabelInsertion.hs`）。

このプロパティが、無作為の文法によってまれに落ちる。
[ADR 0081](0081-missing-tests.md) の実装の途中で一度落ち、[ADR 0085](0085-generate-modules-in-the-build-with-setup-hooks.md) の実装の PR の CI（sdist-2 のジョブ）でも一度落ちた。
どちらも、流し直すと通った。
関係のないプルリクエストの CI が、ときどき落ちることになる。

二つの反例は、どちらもコマンドで再現した。
一つめは、CI で落ちた反例のラベルを外した文法である。

```text
%module M
S :: ()
S <- ((&(!.) &('a')) 'a' ('a' &(S 'b') .)) (((S 'b') ('b' 'b') / (S) S)) { () }
```

この文法を `peg-hs gen` にかけても、警告は出ない。
`peg-hs label --write` は、`^S_any`、`^S_group`、`^S_b`、`^S_S` の四つを挿入する。
挿入した後の文法を `peg-hs gen` にかけると、`3:40: warning: the label S_any may reject valid input: where it fails, the alternative at 3:78 can match` が出た。

二つめは、[ADR 0081](0081-missing-tests.md) の実装で落ちた反例である。

```text
%module M
S :: ()
S <- (!. (('a' 'b' 'c') ('b' 'c') S)* 'b') ((('a' S 'c') !('a' 'a') / ('b' 'a' 'a' / 'c') ('c' S 'b')) !.) &((('b' 'c')?)? ((S . / 'b' 'b' S) &('a' 'b' [ab]) ('c') / S 'a')) { () }
```

挿入の前は、`peg-hs gen` は警告を出さない。
`peg-hs label --write` は 10 個のラベルを挿入し、その後の `peg-hs gen` は、10 個のすべてに「may reject valid input」の警告を出した。
どの警告も、同じ選択肢（`/ S 'a'`）を指している。

二つの反例には、共通する形がある。
規則 `S` が自分を呼び、`S` の呼び出しで始まる選択肢の後ろに、別の選択肢がある。
警告は、その後ろの選択肢を指している。

挿入の候補は、ラベルのない文法の上で、候補ごとに `labelSafeAt` で判定している（`Peg.Grammar.LabelInsertion.safeCandidates`）。
`peg-hs gen` の検査は、ラベルを挿入した後の文法の上で判定する。
[ADR 0056](0056-label-insertion-and-template-deviations.md) は、ほかのラベルを外して比べることで、あるラベルがほかのラベルの判定を変えないようにした。
それでも、二つの判定がこの形で食い違っている。
ラベルが規則の中から呼び出し元へ送出され、呼び出し元の選択肢の後ろの選択肢が試されなくなる場合を、候補の判定が見落としている可能性がある。
原因はまだ特定していない。

## 実装すること

### 原因の特定

二つの反例で、`labelSafeAt` がラベルのない文法で「安全」と判定し、`labelWarnings` がラベルを挿入した文法で警告する理由を特定する。
特定した原因を、実装のプルリクエストと、この ADR のステータスを採択にするときの仕様書の記述に書く。

原因が候補の判定の誤りであり、[ADR 0054](0054-automatic-label-insertion.md) と [ADR 0056](0056-label-insertion-and-template-deviations.md) の決めた判定の範囲で直せるなら、`labelSafeAt` を直す。
直すと検査の判定（`labelWarnings`）まで変わる場合や、[ADR 0056](0056-label-insertion-and-template-deviations.md) の決定を変える必要がある場合は、その部分は直さず、別の ADR にする。

### 挿入の結果の検査

原因の修正とは別に、挿入の結果を、`peg-hs gen` と同じ検査で確かめる。

- `insertLabels` は、候補を選んで挿入した文法に `labelWarnings` をかける。
- 警告された挿入のラベルがあれば、それを候補から外して、挿入をやり直す。
- 挿入のラベルが一つも警告されなくなるまで繰り返す。外すたびに候補は減るので、繰り返しは終わる。
- もとからあったラベルの警告は、今までどおり残す。外すのは、挿入したラベルだけである。

これで、`peg-hs label` が挿入したラベルについて、`peg-hs gen` が警告を出さないことは、判定の食い違いの有無によらず保証される。
言語サーバーも、ラベルの挿入に `insertLabels` を使っているので、同じ結果になる。

`Peg.Grammar.LabelInsertion` の Haddock の「Every label inserted therefore keeps the language of the grammar」の説明に、挿入の結果を検査で確かめることを書き足す。
`docs/specifications.md` のラベルの挿入の項と、peg-grammar の CHANGELOG にも書く。

## 実装しないこと

- ラベルの検査（`labelWarnings`）の判定の変更。この ADR が変えるのは、挿入する候補の選び方だけである。
- 候補の選び方の変更のうち、[ADR 0054](0054-automatic-label-insertion.md) と [ADR 0056](0056-label-insertion-and-template-deviations.md) の範囲を超えるもの。必要になったら別の ADR にする。
- テストの無作為の文法の生成器の変更。反例を作れる生成器なので、そのまま残す。

## テスト設計

先に書いて失敗させてから実装する。

- `packages/peg-grammar/test/LabelInsertion.hs` に、上の二つの反例を固定したテストを足す。`insertLabels` の結果に `labelWarnings` をかけると、挿入したラベルの警告が出ないことを確かめる。今は落ちる。
- 同じ二つの文法で、挿入した後の文法が、挿入の前と同じ言語を受け付けることを、既存のプロパティと同じ解釈器で確かめる。
- 原因を `labelSafeAt` で直した場合は、二つの反例のうち警告されたラベルの位置で、`labelSafeAt` が安全と判定しないことを確かめるテストを足す。
- 既存のプロパティ「the labelled grammar accepts the same language, and has no new warnings」を、CI で落ちたシード `(SMGen 11749201546952811152 9099341262703249443,22)` を `--quickcheck-replay` に渡して実行し、通ることを確かめる。[ADR 0081](0081-missing-tests.md) の実装で落ちたシード `(SMGen 11978778289461465274 2562149824260837101,62)` でも同じことをする。
- 修正の後、このプロパティを、ふだんの件数の 10 倍の件数で一度実行して、落ちないことを確かめる。結果をプルリクエストに書く。
- リポジトリの文法（conformance、フィクスチャ）に `peg-hs label` をかけた結果が変わらないことを確かめる。変わった場合は、変わった文法とラベルをプルリクエストに書く。

## トレードオフ

- 挿入のたびに検査をかけ直すので、`peg-hs label` と言語サーバーのラベルの挿入が遅くなる。外すラベルがなければ、検査は一度だけ増える。
- 原因を直さずに、挿入の結果の検査だけで警告を防ぐと、安全なのに挿入されないラベルが残る場合がある。挿入しないことは、文法の言語を変えないので、安全な側の誤りである。

## 参考文献

- Medeiros, S. Q., Alvez Junior, G. A., Mascarenhas, F. 2020. Automatic Syntax Error Reporting and Recovery in Parsing Expression Grammars. Science of Computer Programming 187.
