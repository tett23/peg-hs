# peg-hs への貢献

この文書は peg-hs の開発の進め方を定める。
日本語版（この文書）を正とする。
英語版（[CONTRIBUTING.md](CONTRIBUTING.md)）は翻訳であり、内容が食い違う場合は日本語版に従う。

## 変更の進め方

peg-hs の変更は、設計の決定を記録した ADR（Architecture Decision Record）から始める。
ADR は `docs/adr/` に置く。

### ADR を書く

- 実装に入る前に ADR を書く。ADR のない機能の追加や仕様の変更は受け付けない
- ファイル名は `NNNN-kebab-case.md` とする。`NNNN` は既存の ADR に続く連番、その後ろは内容が分かる英語の名前である
- ステータスは「提案」とする
- 次の節を含める。データ構造やアルゴリズムを変える場合はその節を、検討の経緯として残すべきことがあればその節を加える

```
# ADR NNNN: タイトル

ステータス: 提案

## 文脈

## 実装すること

## 実装しないこと

## テスト設計

## トレードオフ
```

- 既存の ADR の実装の順序（[ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)）のどこに入るかを「実装の段階」の節に書く

### レビューと採択

- 書いた ADR はコミットせず、レビューを受ける
- 採択されたら、ステータスを「採択」にしてコミットする
- 記法を変える ADR を採択するときは、同じコミットで `docs/syntax.md` を更新し、冒頭の「反映している ADR」の一覧に加える
- ADR で仕様が変わったら、`docs/specifications.md` と README（英語版と日本語版）も同時に更新する。この三つは main で常に最新でなければならない

### コミットした ADR は変えない

- コミットした ADR は、ステータスの行を除いて変更できない。pre-commit のフックと CI で [adr-guard](https://github.com/tett23/adr-guard) が検査する
- 決定を変えたいときは、変更する内容の新しい ADR を書く。元の ADR のステータスの行を「採択→（変更した部分）は ADR NNNN」のように書き換える
- ADR を破棄するときは、ステータスを「破棄」にし、理由を `docs/specifications.md` に書く
- 実装の過程で ADR のとおりにできなかった点や、ADR と違う形にした点は、それを記録する ADR を書く（例：[ADR 0015](docs/adr/0015-implementation-deviations.md)、[ADR 0025](docs/adr/0025-lua-toml-implementation-deviations.md)、[ADR 0029](docs/adr/0029-label-safety-implementation-deviations.md)）

## 実装

### テストを先に書く

- ADR のテスト設計に書いたテストを先に書き、失敗することを確かめてから実装する
- 自動テストを書けない変更（設定の値など）は、ADR のテスト設計に確かめ方を書き、実装の後に実際に動かして確かめる
- 実行時間に上限のないテストを書かない。計算量の検査は、退行したときに数秒で失敗する大きさの入力で書く。指数の時間がかかる入力は、テストではなく失敗として現れるようにする

### 生成物

- 生成したモジュール（codegen の fixture、適合性テストの文法、自己記述のパーサー、ラベルを外した変種）はコミットする。テストが、コミットした生成物と生成器の現在の出力の一致を検査する
- 生成器か文法を変えたら、`scripts/regen-fixtures.sh` で生成し直す
- 文法は `peg-hs fmt` で整形してからコミットする。CI が `peg-hs fmt --check` を実行する（[ADR 0032](docs/adr/0032-grammar-formatter.md)）
- 文法に `peg-hs lint` の警告を残さない。CI が `peg-hs lint` を実行する（[ADR 0033](docs/adr/0033-grammar-linter.md)）
- `docs/` と Markdown のファイルだけの変更では、CI はビルドとテストを行わない。adr-guard の検査は行う。pull request に続けて push すると、前の push の CI は止まる（[ADR 0039](docs/adr/0039-faster-ci.md)）
- テストスイートは、中のテストを並列に動かす。テストは、ほかのテストと共有しないファイルとディレクトリを使う（[ADR 0039](docs/adr/0039-faster-ci.md)）
- 記法に構文を加えて、その構文を自己記述の文法（`packages/peg-grammar/grammar/Peg.peg`）自身で使う場合は、二回に分けて生成し直す（[ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)）。まず構文を受理する規則を、その構文を使わずに加えて生成し直す。次に `Peg.peg` でその構文を使い、新しい生成器で生成し直す

### 性能

- peg-runtime か peg-codegen に触れる変更では、変更の前後のベンチマークを同じ機械で比べる（[ADR 0007](docs/adr/0007-performance-discipline.md)）
- 性能に関わる決定の計測は、`docs/benchmarks/` にスナップショットとして置く

### 依存

- ライセンスに問題がなく、再実装が容易なものは、依存に加えず再実装する。必要な機能が限られている場合は、その機能だけを実装してよい
- 再実装したものには、元の実装のテストを参考にして十分なテストを書く

### 適合性テストのデータ

- 外部から取り込んだテストデータ（`conformance/data/`）は変更しない。取り込んだ版と取得元を `SOURCE` に、ライセンスを `LICENSE` に書く
- 適合率や計測のスナップショット（`docs/conformance/`、`docs/benchmarks/`）は、コミットした後に変更しない。新しい結果は新しいスナップショットとして加える

## 開発環境

ツールチェーン、テストとベンチマークの実行、生成物の再生成のコマンドは、README の開発の節（[README.ja.md](README.ja.md)）にある。
次の点に注意する。

- コンパイラとビルドツールは、ghcup が recommended とする版を使う（[ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)）。ghcup の既定の `cabal` が新しい版に切り替わっていることがあるので、コマンドでは `cabal-3.16.1.0` のように版を明示するとよい
- clone した後に `git config core.hooksPath .githooks` を実行し、adr-guard のフックを有効にする

## 文書の言語

- ADR、仕様書（`docs/specifications.md`）、記法の解説（`docs/syntax.md`）は日本語で書く
- 公開するモジュールの Haddock は英語で書く
- README は英語版と日本語版の両方を更新する
- 日本語の文書は、[README.ja.md](README.ja.md) と既存の ADR の書き方に合わせる

## コミットとブランチ

- コミットは、内容のまとまりごとに分ける。ADR、実装、テスト、文書の更新を、それぞれ独立したコミットにすることが多い
- コミットの件名は `種類(範囲): 内容` の形で、日本語で書く。種類は `feat`、`fix`、`test`、`docs`、`refactor` など、範囲はパッケージの名前（`peg-runtime`、`peg-grammar` など）である。件名には関係する ADR の番号を添える
- main に対する rebase はしない。API キーなどの秘密を誤ってコミットした場合だけを例外とする
- ブランチは、マージするまでは rebase してよい。マージは常に `--no-ff` で行う

## リリース

- `v` から始まるタグをリリースとする。`v0.0.1-rc` のような形のタグはプレリリースとして扱う
- リリースノートは GitHub の Releases に書く。変更点を「追加」「変更」「削除」「修正」などの項目に分け、可能であれば各変更のコミットか PR を添える
- Hackage への公開は、まだ行っていない（[ADR 0009](docs/adr/0009-hackage-publication.md)）

## ライセンス

peg-hs は MIT ライセンスである。
貢献した内容も MIT ライセンスで公開される。
