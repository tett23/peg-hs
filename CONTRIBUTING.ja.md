# peg-hs への貢献

この文書は peg-hs の開発の進め方を定める。
日本語版（この文書）を正とする。
英語版（[CONTRIBUTING.md](CONTRIBUTING.md)）は翻訳であり、内容が食い違う場合は日本語版に従う。

peg-hs の最初のリリース候補 `v0.1.0-rc1` は、GitHub の Release で配布している。
Hackage にはまだ公開していない。
Hackage への公開は `v0.1.0` で行う（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）。

## 開発の環境

コンパイラとビルドツールは、ghcup が recommended とする版を使う（[ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)）。
いまは GHC 9.10.3 と cabal-install 3.16.1.0 である。
`cabal.project` が `with-compiler: ghc-9.10.3` で GHC の版を固定している。

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

ghcup の既定の `cabal` は、新しい版に切り替わっていることがある。
ghcup は版ごとの実行ファイル（`cabal-3.16.1.0`）も置くので、既定が切り替わっている場合は、この文書のコマンドの `cabal` を `cabal-3.16.1.0` に読みかえる。
[mise](https://mise.jdx.dev/) を使う場合は、リポジトリの `mise.toml` が ghcup の `~/.ghcup/bin` をプロジェクトの `PATH` に加える。

パッケージが対応する GHC は 9.10、9.12、9.14 である（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）。
各 `.cabal` の `tested-with` に、確かめた版（9.10.3、9.12.4、9.14.1）を並べている。
開発で使うのは 9.10.3 だけでよい。
9.12 と 9.14 でのビルドは CI が確かめる。
手元で確かめるときは、その版の GHC を入れて `cabal build -w ghc-9.14.1 all` のように版を指定する。

clone した後に、[adr-guard](https://github.com/tett23/adr-guard) を入れ、git のフックを有効にする。
adr-guard は、コミットした ADR とベンチマークの記録が変わっていないことを検査する道具である（「ADR と adr-guard」の節）。

```sh
cargo install --git https://github.com/tett23/adr-guard --tag v0.8.1
git config core.hooksPath .githooks
```

`git config core.hooksPath .githooks` は clone ごとに要る。
adr-guard の版は、CI（`.github/workflows/adr.yml`）の版にそろえる（[ADR 0047](docs/adr/0047-adr-guard-v0.8.1.md)）。

エディタの文法のテスト（「エディタの文法のテスト」の節）には Node の LTS が要る。

## ビルドとテスト

すべてのパッケージをビルドし、すべてのテストを動かすには、リポジトリの直下で次を実行する。

```sh
cabal build all
cabal test all
```

テストスイートは、中のテストを並列に動かす。
そのため、テストはほかのテストと共有しないファイルとディレクトリを使う（[ADR 0039](docs/adr/0039-faster-ci.md)）。

最も時間のかかる peg-grammar-test は、オプション `--shard i/n` で n 個に分けたうちの i 番めだけを動かせる（[ADR 0042](docs/adr/0042-shard-peg-grammar-test.md)）。
CI はこれで三つのジョブに分けている。

```sh
cabal test peg-grammar --test-options='--shard 1/3'
```

分けた各部分の時間をそろえるため、事例が 300 件以上で、CI で 10 秒以上かかるプロパティテストは、`packages/peg-grammar/test/Shard.hs` の `chunkedProperty` で複数のテストに分ける。
一つのプロパティが一つのテストのままだと、それを含む部分だけが長くなるためである。

テストの一部は、パッケージの外のファイル（ほかのパッケージの文法、`editors/test` など）を読む。
ソースのアーカイブ（sdist）から展開したパッケージには、それらのファイルがない。
そのとき、これらのテストは失敗せずに飛ばし、`skipped:` で始まる行で理由を報告する（[ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。
CI の `sdist` のジョブは、この行の数を数えて表示する。
パッケージの外を読むテストを加えるときは、同じ形で飛ばすようにする。

公開する四つのライブラリ（peg-runtime、peg-grammar、peg-codegen、peg-lsp）は、公開モジュールのすべてを Haddock で文書化する（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）。
CI と同じ検査を手元で動かすには、次を実行する。
網羅率が 100% でないモジュールがあれば失敗する。

```sh
cabal haddock peg-runtime peg-grammar peg-codegen peg-lsp 2>&1 | scripts/haddock-coverage.sh
```

CommonMark の適合性テストは、結果を調べるためのオプションを取る。
`--show N` は例 N の入力、期待する出力、実際の出力を表示し、`--report FILE` は節ごとの結果を Markdown で書き出し、`--accept` はいま通る例の一覧を記録し直す。

```sh
cd conformance && $(cabal list-bin peg-conformance:test:commonmark-conformance) --show 5
```

## 生成物の再生成

生成したモジュールは、リポジトリにコミットする。
対象は、codegen の fixture、適合性テストの文法から生成したパーサー、記法の自己記述のパーサー、ラベルを外した変種である。
テストが、コミットした生成物と生成器の現在の出力が一致することを検査する。
生成器か文法を変えたら、次で生成し直す。

```sh
scripts/regen-fixtures.sh
```

既定の `cabal` が切り替わっている場合は、`CABAL=cabal-3.16.1.0 scripts/regen-fixtures.sh` のように使う `cabal` を指定する。
このスクリプトは最後に `scripts/embed-runtime.py` を動かし、`peg-hs parse` が使う peg-runtime のソース（`packages/peg-cli/app/Embedded.hs`）を書き直す（[ADR 0036](docs/adr/0036-parse-command.md)）。
peg-runtime のソースを変えたときも、このスクリプトを動かす。
`Embedded.hs` が古いと、peg-cli のテストが失敗する。

記法の構文解析器は、記法自身の文法（`packages/peg-grammar/grammar/Peg.peg`）から生成している（[ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)）。
記法に構文を加え、その構文を `Peg.peg` 自身で使う場合は、二回に分けて生成し直す。
いまの生成器はその構文を読めないので、一度に変えると `Peg.peg` を生成できないためである。

1. 構文を受理する規則を、その構文を使わずに `Peg.peg` に加え、`scripts/regen-fixtures.sh` で生成し直す
2. `Peg.peg` でその構文を使い、新しい生成器でもう一度 `scripts/regen-fixtures.sh` を動かす

リポジトリの文法は `peg-hs fmt` で整形してからコミットする（[ADR 0032](docs/adr/0032-grammar-formatter.md)）。
`peg-hs lint` の警告も残さない（[ADR 0033](docs/adr/0033-grammar-linter.md)）。
引数を付けないと、どちらも現在のディレクトリの下のすべての `.peg` を対象にする。
CI は、リポジトリの直下で次の二つを動かす。

```sh
$(cabal list-bin exe:peg-hs) fmt --check
$(cabal list-bin exe:peg-hs) lint
```

Lua の適合性テストの期待する出力は、参照実装の Lua 5.5.1 で作っている。
作り直すときだけ Lua 5.5.1 が要る。

```sh
conformance/lua/golden/regen.sh
```

## ADR と adr-guard

peg-hs の変更は、設計の決定を記録した ADR（Architecture Decision Record）から始める。
ADR は `docs/adr/` に置く。

### ADR を書く

- 実装に入る前に ADR を書く。ADR のない機能の追加や仕様の変更は受け付けない
- ファイル名は `NNNN-kebab-case.md` とする。`NNNN` は既存の ADR に続く連番、その後ろは内容の分かる英語の名前である
- ADR は日本語で書く。ステータスは「提案」とする
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

### レビューと採択

- 書いた ADR はコミットせず、レビューを受ける
- 採択されたら、ステータスを「採択」にしてコミットする
- 記法を変える ADR を採択するときは、同じコミットで `docs/syntax.md` を更新し、冒頭の「反映している ADR」の一覧に加える
- ADR で仕様が変わったら、`docs/specifications.md` と README（英語版と日本語版）も同時に更新する。この三つは main で常に最新でなければならない
- 開発の進め方が変わったら、この文書（日本語版と英語版）も同時に更新する

### コミットした ADR は変えない

- コミットした ADR は、ステータスの行と、ADR の参照に付けるリンクを除いて変更できない。pre-commit のフックと CI の `adr` のジョブで adr-guard が検査する
- ADR は、行頭が `ステータス:` のステータスの行をちょうど一つ持つ。ステータスの行が無い ADR と二つ以上ある ADR は、adr-guard が拒否する（[ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md)）
- 決定を変えたいときは、変更する内容の新しい ADR を書く。元の ADR のステータスの行を「採択→（変更した部分）は ADR NNNN」のように書き換える
- ADR を破棄するときは、ステータスを「破棄」にし、理由を `docs/specifications.md` に書く
- 実装の過程で ADR のとおりにできなかった点や、ADR と違う形にした点は、それを記録する ADR を書く（例：[ADR 0015](docs/adr/0015-implementation-deviations.md)、[ADR 0025](docs/adr/0025-lua-toml-implementation-deviations.md)、[ADR 0029](docs/adr/0029-label-safety-implementation-deviations.md)）

### ADR へのリンク

文書（`.md`）の中の ADR の参照（`ADR 0001` の形）には、ADR のファイルへのリンクを付ける。
adr-guard がリンクの有無を検査する。
ADR を書いた後と文書を更新した後は、リポジトリの直下で次を実行し、リンクの無い参照をリンクに置きかえる。

```sh
adr-guard links --fix
adr-guard links
```

`adr-guard links` が終了コード 0 で終われば、すべての参照にリンクがある。

### 変えない記録

ベンチマークの記録（`docs/benchmarks/`）、適合率のスナップショット（`docs/conformance/`）、言語サーバーの手での確認の記録（`docs/editors/`）は、コミットした後に変更しない。
新しい結果は、新しいファイルとして加える。
このうち adr-guard が変更を拒否するのは `docs/benchmarks/` だけで、リンクの付与も拒否する（[ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md)）。
`docs/conformance/` と `docs/editors/` は検査しないので、レビューで確かめる。

## 実装の決まり

### テストを先に書く

- ADR のテスト設計に書いたテストを先に書き、失敗することを確かめてから実装する
- 自動テストを書けない変更（設定の値など）は、ADR のテスト設計に確かめ方を書き、実装の後に実際に動かして確かめる
- 実行時間に上限のないテストを書かない。計算量の検査は、退行したときに数秒で失敗する大きさの入力で書く。指数の時間がかかる入力は、終わらないテストではなく失敗として現れるようにする

### peg-runtime の互換と PVP

パッケージの版は PVP に従う。
生成したモジュールは peg-runtime の内部のモジュール `Peg.Runtime.Internal` を import する。
`Peg.Runtime.Internal` は利用者が直接使うものではないが、その変更は生成済みのモジュールを壊しうるので、PVP の上でメジャーの変更として扱う（[ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

生成したモジュールの先頭のコメントには、そのモジュールが要る peg-runtime の版の範囲（`peg-runtime >=0.1 && <0.2` の形）が入る。
範囲は peg-codegen の `Peg.Codegen` の定数 `runtimeVersions` が持つ。
`Peg.Runtime.Internal` を変えて生成したモジュールとの互換が崩れるときは、この範囲を上げ、`scripts/regen-fixtures.sh` で生成物を作り直す。
peg-codegen のテストは、この範囲が `peg-codegen.cabal` の peg-runtime の依存の範囲と一致することを検査する。

### 依存

- ライセンスに問題がなく、再実装が容易なものは、依存に加えず再実装する。必要な機能が限られている場合は、その機能だけを実装してよい
- 再実装したものには、元の実装のテストを参考にして十分なテストを書く

### 適合性テストのデータ

外部から取り込んだテストデータ（`conformance/data/`）は変更しない。
取り込んだ版と取得元を `SOURCE` に、ライセンスを `LICENSE` に書く。

### 文書の言語

- ADR、仕様書（`docs/specifications.md`）、記法の解説（`docs/syntax.md`）は日本語で書く
- 公開するモジュールの Haddock は英語で書く
- 各パッケージの `CHANGELOG.md` とリリースノートは英語で書く
- README とこの文書は、英語版と日本語版の両方を同じ内容で更新する

## コミットの書き方

- コミットは、内容のまとまりごとに分ける。ADR、実装、テスト、文書の更新を、それぞれ独立したコミットにすることが多い
- コミットの件名と本文は英語で書く（[ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)）
- 件名は `type(scope): description` の形にする。`type` は `feat`、`fix`、`test`、`docs`、`refactor`、`ci` など、`scope` は変更した場所（パッケージの名前か、`editors`、`conformance`、`adr`、`benchmarks` など）で、複数の場所にまたがるときは省いてよい
- 件名の末尾に、関係する ADR の番号を `(ADR 0046)` の形で添える

```
feat(cli): take --name=value in every option that takes a value (ADR 0046)
```

- main に対する rebase はしない。API キーなどの秘密を誤ってコミットした場合だけを例外とする
- ブランチは、マージするまでは rebase してよい。マージは常に `--no-ff` で行う

## CI のジョブ

CI は三つのワークフローからなる。

`.github/workflows/ci.yml` は、main への push と pull request で動く。
`docs/` と Markdown のファイルだけの変更では動かない（[ADR 0039](docs/adr/0039-faster-ci.md)）。
pull request に続けて push すると、前の push の実行は止まる。

- **haskell**：すべてのパッケージをビルドし、リポジトリの文法の `peg-hs fmt --check` と `peg-hs lint`、五つのパッケージの版の一致（`python3 scripts/versions.py check`）、各パッケージの `cabal check` を検査する
- **test-grammar-1、test-grammar-2、test-grammar-3**：peg-grammar-test を `--shard 1/3` から `--shard 3/3` に分けて動かす（[ADR 0042](docs/adr/0042-shard-peg-grammar-test.md)）
- **test-conformance**：適合性テスト（Lua、TOML、JSON、CommonMark）と計算量のテストを動かす
- **test-packages**：peg-cli、peg-lsp、peg-codegen、peg-runtime のテストを動かす
- **haddock**：公開する四つのライブラリの Haddock を生成し、公開モジュールがすべて文書化されていることを `scripts/haddock-coverage.sh` で検査する（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）
- **sdist**：公開する五つのパッケージの sdist を作り、展開したものだけでビルドとテストを行う。飛ばしたテストの数と理由を表示する（[ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)）
- **ghc-9.12.4、ghc-9.14.1**：新しい GHC で全パッケージをビルドし、peg-runtime と peg-codegen のテストを動かす。peg-codegen のテストは、生成したモジュールが警告なしでコンパイルできることを確かめる（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）
- **editors**：エディタの文法のテストを動かし、コミットした tree-sitter のパーサーが最新であることを確かめる（[ADR 0034](docs/adr/0034-syntax-highlighting.md)）

テストのジョブ（`test-*`）の中では、スイートを一つずつ動かす。
各スイートが実行環境のすべてのコアを使えるようにするためである（[ADR 0041](docs/adr/0041-split-test-jobs-and-cores.md)）。
新しいテストスイートは、`docs/benchmarks/` の最新の CI の時間をもとに、ジョブの時間がそろうジョブに加える。

`.github/workflows/adr.yml` の **adr** のジョブは、文書だけの変更も含むすべての変更で動き、adr-guard で ADR とベンチマークの記録を検査する（[ADR 0047](docs/adr/0047-adr-guard-v0.8.1.md)）。

`.github/workflows/release.yml` は、`v` で始まるタグの push で動き、Release を作る。
内容は「リリースの手順」の節に書く。

## ベンチマークと性能

peg-hs は性能に絶対値の目標を置かない（[ADR 0007](docs/adr/0007-performance-discipline.md)）。
計測値は機械に依存するためである。
退行は、変更の前と後を同じ機械で計測して比べることで見つける。
共有の実行環境では計測のばらつきが大きいので、CI では性能を検査しない。

peg-runtime か peg-codegen に触れる変更では、変更の前後で次のベンチマークを動かして比べる。

```sh
cabal bench peg-conformance
```

規則のメモ化を `%nomemo` で外す前には、メモの項目がどこに溜まるかを調べ、最大のメモリ使用量を別々のプロセスで比べる（[ADR 0017](docs/adr/0017-nomemo-implementation.md)）。

```sh
cd conformance && $(cabal list-bin peg-conformance:bench:peg-bench) --memo-report
```

性能に関わる決定の根拠にした計測と、CI の時間の計測は、`docs/benchmarks/` に日付を付けたスナップショットとして置く。
置いた後は変更しない（「変えない記録」の節）。

## エディタの文法のテスト

`editors/` には、TextMate の文法、tree-sitter の文法、VS Code の拡張機能がある（[ADR 0034](docs/adr/0034-syntax-highlighting.md)）。
テストは Node と tree-sitter の CLI（`npm ci` で入る）で動かす。

```sh
cd editors && npm ci && npm test
```

テストは、エディタの文法が記法自身の文法と同じ範囲（コメント、リテラル、文字クラス、アクション、規則名、ラベル）を見つけることを確かめる。
比べる相手の範囲は、peg-grammar のテストが `editors/test/ranges.txt` に書き出す golden である。
記法を変えたら、`editors/` の文法を直し、次で `ranges.txt` を書き直してから、エディタの文法のテストを動かす。

```sh
cabal test peg-grammar --test-options=--accept
```

TextMate の文法のトークンごとのスコープは、`editors/test/textmate.golden.txt` と比べる。
意図してスコープを変えたときは、`UPDATE=1 npm test` で書き直す。

tree-sitter の文法を変えたら、`npm test` が生成し直した `editors/tree-sitter-peg/src` もコミットする。
CI の `editors` のジョブは、生成し直した結果とコミットしたものに差がないことを確かめる。

## リリースの手順

リリースの範囲と手順は [ADR 0044](docs/adr/0044-release-v0-1-0.md) で決めている。

### 版とタグ

- 公開するパッケージは peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli の五つで、すべて同じ版で出す
- タグは `v` に cabal の版の上の三つの桁を付けたもの（`v0.1.0`）とする。cabal の版の四つめの桁は、タグを伴わない出し直しに使う
- プレリリースのタグは `v0.1.0-rc1` のように `-` の後に印を付ける。対応する cabal の版は、`-` の前の三つの桁（`0.1.0.0`）である。PVP の版は rc を表せないためである
- `v` で始まるタグをリリースとし、`-` を含むタグはプレリリースとして扱う

### 1. 版を上げる

五つの `.cabal` の `version` と、パッケージ間の依存の範囲（`peg-runtime >=0.1 && <0.2` など）を、同じコミットで変える。
変えた後に、版がそろっていることを確かめる。

```sh
python3 scripts/versions.py check
```

`Peg.Runtime.Internal` の互換が崩れている場合は、`runtimeVersions` も上げて生成物を作り直す（「peg-runtime の互換と PVP」の節）。

### 2. CHANGELOG を書く

各パッケージの `CHANGELOG.md` に、版の見出し（`## 0.1.0.0` の形）を加える。
見出しの下は「Added」「Changed」「Removed」「Fixed」の項目に分け、英語で書く。
各変更に、それを決めた ADR への絶対リンク（`https://github.com/tett23/peg-hs/blob/main/docs/adr/...`）を添える。
プレリリースは見出しにしない。
`v0.1.0-rc1` の変更は `## 0.1.0.0` の下に書き、rc の間の修正も同じ見出しの下に足す。

### 3. タグを打つ

版の更新と CHANGELOG を main にマージし、main の CI が通っていることを確かめる。
タグの版が `.cabal` の版と一致することを手元で確かめてから、main のコミットにタグを打って push する。

```sh
python3 scripts/versions.py tag v0.1.0-rc1
git tag v0.1.0-rc1
git push origin v0.1.0-rc1
```

### 4. Release のワークフローを確かめる

タグの push で `.github/workflows/release.yml` が動き、次を行う。

- タグの版と五つの `.cabal` の版が一致することを確かめる。一致しなければ失敗し、Release を作らない
- 五つのパッケージの sdist と、四つのライブラリの Haddock の tarball（Hackage にそのまま上げられる形）を作る
- `peg-hs` の実行ファイルを、Linux（x86-64）と macOS（arm64）で作る
- GitHub の Release を作り、tarball、実行ファイル、`SHA256SUMS` を添付して公開する。`-` を含むタグでは、プレリリースとして公開する
- Release の本文には、仮の本文として GitHub が自動で作るリリースノート（前のタグからマージした pull request の一覧）を入れる

同じタグでワークフローを再実行すると、既存の Release の添付を置き換える。
実行の様子と添付は、次で確かめる。

```sh
gh run list --workflow release.yml
gh run watch
gh release view v0.1.0-rc1
```

### 5. リリースノートを書く

リリースノートは、Release ができた後に、手元の Claude Code で書く。
CI の中では書かない（API の資格情報を CI に置かないため）。
Claude Code には、次の指示を、`TAG`（今回のタグ）と `PREV`（前のタグ）を置きかえて渡す。
`PREV` は、プレリリースでは直前のタグ（rc を含む）、正式な版では直前の正式な版のタグとする。

```
Write the release notes of peg-hs TAG and save them to release-notes.md
(outside the repository, or delete it afterwards; do not commit it).

Sources:
- the commits in `git log PREV..TAG`
- the pull requests merged in that range (`git log --merges PREV..TAG`,
  `gh pr list --state merged --base main`)
- the ADRs adopted in that range: `git diff --name-status PREV..TAG -- docs/adr/`,
  and the status lines that changed to 採択
- the CHANGELOG.md of each of the five packages (packages/*/CHANGELOG.md)

Format:
- English.
- Sections "Added", "Changed", "Removed" and "Fixed"; add other sections
  (for example "Documentation" or "CI") only when needed, and omit empty ones.
- Each item: one sentence on what changed for a user, then a link to its
  commit or pull request, and an absolute link to its ADR,
  https://github.com/tett23/peg-hs/blob/main/docs/adr/NNNN-name.md.
  Check that every ADR link points to an existing file.
- A section "Known limitations" with one line that links to
  https://github.com/tett23/peg-hs/blob/main/README.md#known-limitations
- A section "Assets" that names the attached files: the sdists and Haddock
  tarballs of the packages, the peg-hs executables for x86_64-linux and
  aarch64-macos, and SHA256SUMS.

If there is no previous tag (the first release), do not list changes; write
the features of each package, each with absolute links to the ADRs that
decided it, following the CHANGELOGs.
```

書かれたリリースノートを人が読み、誤りを直してから、Release の本文を置き換える。

```sh
gh release edit v0.1.0-rc1 --notes-file release-notes.md
```

人が確かめることは、変更の分け方、各項目のコミットか pull request のリンク、ADR の絶対リンクが開けること、既知の制限へのリンクである。

### 6. Hackage に上げる

Hackage へのアップロードは、ワークフローでは行わない。
Hackage の資格情報を CI に置かないためである。
Release の添付を手元に落とし、チェックサムを確かめてから、人が `cabal upload` で上げる。

```sh
gh release download v0.1.0-rc1 --dir release
cd release
shasum -a 256 -c SHA256SUMS
```

`cabal upload` は、`--publish` を付けなければ候補（candidate）として上げる。
候補は Hackage 上で表示を確かめるためのもので、公開した版とは別に扱われる。
上げる順は、依存される側からとする（peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli）。

```sh
cabal upload peg-runtime-0.1.0.0.tar.gz peg-grammar-0.1.0.0.tar.gz peg-codegen-0.1.0.0.tar.gz peg-lsp-0.1.0.0.tar.gz peg-cli-0.1.0.0.tar.gz
cabal upload --documentation peg-runtime-0.1.0.0-docs.tar.gz peg-grammar-0.1.0.0-docs.tar.gz peg-codegen-0.1.0.0-docs.tar.gz peg-lsp-0.1.0.0-docs.tar.gz
```

候補のページで、モジュールの文書、各モジュールの先頭の説明と例、CHANGELOG、依存の表示を確かめる。

- **プレリリース（`v0.1.0-rc1` など）**：候補として上げて確かめるだけにし、公開しない。Hackage の版は rc を表せず、`0.1.0.0` を一度公開すると取り消せないためである
- **正式な版（`v0.1.0` など）**：候補として上げて確かめた後に、同じファイルを `--publish` を付けて上げ、公開する

```sh
cabal upload --publish peg-runtime-0.1.0.0.tar.gz peg-grammar-0.1.0.0.tar.gz peg-codegen-0.1.0.0.tar.gz peg-lsp-0.1.0.0.tar.gz peg-cli-0.1.0.0.tar.gz
cabal upload --publish --documentation peg-runtime-0.1.0.0-docs.tar.gz peg-grammar-0.1.0.0-docs.tar.gz peg-codegen-0.1.0.0-docs.tar.gz peg-lsp-0.1.0.0-docs.tar.gz
```

正式な版を公開したら、README とこの文書の冒頭の状態の表示を、Hackage に公開した状態に合わせる。

### 言語サーバーの手での確認

VS Code、Neovim、Helix で、言語サーバーの診断、整形、定義への移動、ホバー、文書の記号、semantic tokens を手で確かめる。
確かめるのはリポジトリの持ち主で、都合のよいときに行う。
リリース（rc も含む）の条件にはしない。
確かめた結果（エディタとその版、確かめた機能、問題）は `docs/editors/` に記録として置き、コミットした後は変えない。
記録を置くコミットで、README のそのエディタの設定の例から「未確認」の表示を外す。

## ライセンス

peg-hs は MIT ライセンスである。
貢献した内容も MIT ライセンスで公開される。
