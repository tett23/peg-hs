# ADR 0044: v0.1.0 のリリースの範囲と手順

ステータス: 採択→プレリリースの Hackage への候補のアップロードは [ADR 0058](0058-no-hackage-candidates-for-pre-releases.md)

## 文脈

peg-hs は、まだ一度もリリースしていない。
タグも GitHub の Release もなく、Hackage にも上げていない。

[ADR 0009](0009-hackage-publication.md) は、Hackage への公開を前提にした。
パッケージ名、PVP、公開モジュール全体の Haddock、cabal のメタデータを最初から整えることを決め、最初のアップロードの目安を「非左再帰の生成器が end-to-end で実働した時点」とした。
その時点はとうに過ぎている。
生成器、実行時のライブラリ、整形、lint、言語サーバー、解析の表示のコマンドがそろい、適合性のテスト（JSON、TOML、Lua、CommonMark）も通っている。

リリースに向けてリポジトリを調べると、決まっていないことと、足りないものが見つかった。

- **範囲**：[ADR 0009](0009-hackage-publication.md) が公開するパッケージは peg-runtime、peg-grammar、peg-codegen、peg-cli の四つである。後から加わった peg-lsp（[ADR 0035](0035-language-server.md)）は入っていない
- **版**：cabal の版は PVP の四つの桁（`0.1.0.0`）で、リリースのタグは `v` で始まる（CONTRIBUTING）。二つの対応が決まっていない。プレリリースのタグ（`v0.1.0-rc1`）と cabal の版の対応も決まっていない
- **変更の記録**：どのパッケージにも CHANGELOG がない。Hackage はパッケージの CHANGELOG を表示する
- **Haddock**：[ADR 0009](0009-hackage-publication.md) は公開モジュール全体の Haddock を義務にしたが、後から加えたモジュールで欠けている。`Peg.Grammar.Outline` の `Outline`、`DeclarationKind`、`Reference`、`Peg.Lsp.Server` の `State`、`initialState`、`Severity`、`Peg.Lsp.Json` の `asText`、`asBool`、`asArray`、`int`、`object` である。コメントのある関数も、書いた後の ADR で振る舞いが変わったものがある。CI は Haddock を生成するが、網羅しているかは見ていない
- **手での確認**：[ADR 0035](0035-language-server.md) は、言語サーバーを VS Code で手で確かめることを定めたが、まだ確かめていない。それなのに README は VS Code、Neovim、Helix の設定を載せている
- **状態の表示**：README と CONTRIBUTING は「pre-release、Hackage に未公開」と書いている
- **成果物**：タグを push しても、CI は何もしない。sdist の tarball も `peg-hs` の実行ファイルも作らず、Release も作らない
- **リリースノート**：リポジトリの持ち主の方針では、リリースノートを GitHub の Release に書き、変更を「追加」「変更」「削除」「修正」などに分け、コミット（または pull request）と ADR を添える。ADR の数が多く、手で書くと手間がかかる

一つずつ直すことはできるが、範囲と手順が決まっていないと、何をそろえればリリースできるかが決まらない。
本 ADR は v0.1.0 の範囲と手順を決め、リリースの作業を繰り返せる形にする。

## 実装すること

### 範囲

- 公開するパッケージは、peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli の五つとする。[ADR 0009](0009-hackage-publication.md) の四つに peg-lsp を加える。peg-cli が peg-lsp に依存するので、peg-cli を Hackage から入れるには peg-lsp も Hackage にある必要がある
- peg-conformance（適合性のテスト）は公開しない
- エディタの文法（`editors/`）は、リポジトリの中で配布する。nvim-treesitter と GitHub Linguist への登録は、これまでどおり行わない（[ADR 0034](0034-syntax-highlighting.md)）
- VS Code の拡張機能の vsix の作成と Marketplace への公開は、本 ADR では行わない。docs/specifications.md の未決事項に残課題として加える

### 版

- 五つのパッケージは同じ版で出す。v0.1.0 では `0.1.0.0` とする
- タグは `v` に、cabal の版の上の三つの桁を付けたもの（`v0.1.0`）とする。四つめの桁は、Hackage の改訂のない修正の再アップロードなど、タグを伴わない出し直しに使う
- プレリリースのタグは、`v0.1.0-rc1` のように、`-` の後に印を付ける。プレリリースのタグも、対応する cabal の版は `-` の前の三つの桁（`0.1.0.0`）とする。PVP の版は `rc` を表せないためである
- 最初のリリースは `v0.1.0-rc1` とする。ADR 0044 から [ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md) を実装した後に打つ。rc で問題がなければ、同じコミットか修正を加えたコミットに `v0.1.0` を打つ
- 版を上げるときは、五つの `.cabal` の `version` と、パッケージ間の依存の範囲（`peg-runtime >=0.1 && <0.2` など）を同じコミットで変える。CI で、五つの版が一致することを検査する

### CHANGELOG

- 各パッケージの直下に `CHANGELOG.md` を置き、`.cabal` の `extra-doc-files` に加える
- 書式は版ごとの見出しの下に「Added」「Changed」「Removed」「Fixed」の項目を置くものとし、英語で書く。各変更には ADR への絶対リンクを添える。GitHub の Release のリリースノートと同じ分け方である
- v0.1.0 の CHANGELOG は「初めてのリリース」として、そのパッケージが提供するものを機能ごとに書く。機能ごとに、それを定めた ADR への絶対リンクを添える
- プレリリースは CHANGELOG の見出しにしない。`v0.1.0-rc1` の CHANGELOG の見出しは `0.1.0.0` とし、rc の間の修正は同じ見出しの下に足す

### Haddock

- 公開する五つのパッケージの公開モジュールすべての Haddock を見直す。上に挙げた欠けているコメントを足すだけでなく、次を行う
  - 各モジュールの先頭に、そのモジュールの役割と、主な型と関数の使い方を書く
  - 書いた後の ADR で振る舞いが変わった関数のコメントを、いまの振る舞いに合わせる
  - 使い方の分かりにくい関数（生成したモジュールが呼ぶ `Peg.Runtime` の関数、`Peg.Grammar` の検査の入口、`Peg.Codegen` の生成の入口、`Peg.Lsp.Server` の入口）に、短い使い方の例を付ける
  - 関連する型と関数への参照（`'Name'`）と、モジュールへの参照（`"Module"`）を付け、Hackage の文書の中で移動できるようにする
  - `Peg.Runtime.Internal` の先頭に、生成したモジュールのためのモジュールであり、利用者が直接使うものではないことを書く
- Haddock は英語で書く（CLAUDE.md）
- CI の Haddock の生成で、公開するパッケージの公開モジュールが 100% 文書化されていることを検査する。`cabal haddock` が出力するモジュールごとの網羅率を読み、100% でないモジュールがあれば失敗する

### 言語サーバーの手での確認

- VS Code、Neovim、Helix で、診断、整形、定義への移動、ホバー、文書の記号、semantic tokens を手で確かめる。確かめるのはリポジトリの持ち主で、都合のよいときに行う。リリース（rc も含む）の条件にはしない
- 確かめるまでは、README のそのエディタの設定の例に「未確認」と書く
- 確かめた結果（エディタとその版、確かめた機能、問題）を `docs/editors/` に記録として置く。記録はコミットした後は変えない。記録を置くコミットで、そのエディタの「未確認」の表示を外す

### リリースを作る CI

- `v` で始まるタグの push で動くワークフロー（`release.yml`）を加える。`-` を含むタグ（`v0.1.0-rc1`）はプレリリースとする
- ワークフローは次を行う
  - タグの版（`-` の前）が五つの `.cabal` の版の上の三つの桁と一致することを確かめる。一致しなければ失敗する
  - 五つのパッケージの sdist の tarball と、Haddock の tarball（Hackage にそのまま上げられる形）を作る
  - `peg-hs` の実行ファイルを、Linux（x86-64）と macOS（arm64）で作る
  - GitHub の Release を作り、tarball と実行ファイルと `SHA256SUMS` を添付して公開する。プレリリースのタグでは、Release をプレリリースとして公開する
  - Release の本文には、仮の本文として、前のタグからのマージした pull request の一覧（GitHub の自動のリリースノート）を入れる
- 同じタグでワークフローを再実行したときは、既存の Release の添付を置き換える

### リリースノート

- リリースノートは AI（Claude Code）で作る。ワークフローが Release を作った後、前のタグからのコミット、pull request、ADR、CHANGELOG をもとに書き、`gh release edit` で Release の本文を置き換える。問題があれば人が手で直す
- 書式はリポジトリの持ち主の方針に従う。変更を「追加」「変更」「削除」「修正」などの項目に分け、必要ならほかの項目を足す。各変更に、コミット（または pull request）と ADR への絶対リンクを添える
- 最初のリリース（`v0.1.0-rc1`）には前のタグがないので、リリースノートは機能ごとの一覧とし、各機能に ADR への絶対リンクを添える
- 既知の制限は、README の「既知の制限」の節（[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md)）へリンクする
- AI に渡す手順（参照する範囲、書式、リンクの形）を CONTRIBUTING のリリースの節に書き、毎回同じ手順で作れるようにする

### Hackage

- Hackage へのアップロードは、ワークフローでは行わない。Release の tarball を確かめた後、人が `cabal upload` で行う。Hackage の資格情報を CI に置かないためである
- プレリリースのタグでは、Hackage に公開しない。候補（`--candidate`）として上げて表示を確かめるだけにする。Hackage の版は rc を表せず、`0.1.0.0` を一度公開すると取り消せないためである
- `v0.1.0` では、候補として上げて表示を確かめた後に公開する

### 状態の表示と手順の文書

- `v0.1.0-rc1` を打つ前のコミットで、README（日本語と英語）と CONTRIBUTING の「pre-release、Hackage に未公開」の表示を、リリースの状態に合わせて更新する。rc の間は「rc を GitHub の Release で配布し、Hackage には未公開」とし、`v0.1.0` で Hackage の表示に変える
- README に、GitHub の Release から実行ファイルを入れる手順と、ソースから `cabal install` する手順を書く
- CONTRIBUTING のリリースの節に、手順（版の更新、CHANGELOG、タグ、ワークフローの確認、AI によるリリースノート、Hackage の候補と公開）を書く

## 実装しないこと

- Hackage への自動のアップロード
- Windows の実行ファイルと、x86-64 の macOS の実行ファイル
- Stackage への登録（[ADR 0009](0009-hackage-publication.md) と同じく 1.0 の後）
- VS Code の拡張機能の vsix の作成と Marketplace への公開（docs/specifications.md の未決事項に加える）
- リリースノートを CI の中で AI に書かせること。API の資格情報を CI に置くことになるので、Release を作った後に手元の Claude Code で書く
- 言語サーバーの手での確認をリリースの条件にすること

## テスト設計

自動テストを書けるもの：

- **版の一致**：CI で、五つの `.cabal` の `version` が一致し、パッケージ間の依存の範囲がその版を含むことを検査する。版を一つだけ変えると失敗することを、手で一度確かめる
- **タグの版の判定**：タグの文字列から cabal の版を求める処理（`v0.1.0` と `v0.1.0-rc1` から `0.1.0`、`0.1.0` や `v0.1` は誤り）を、シェルの関数として持ち、CI でいくつかの例を確かめる
- **Haddock の網羅**：CI の検査が、コメントを一つ外したモジュールで失敗することを、手で一度確かめる
- **CHANGELOG**：`cabal check` が通り、sdist の tarball に `CHANGELOG.md` が入ること

実際に動かして確かめるもの：

- **リリースのワークフロー**：`v0.1.0-rc1` を push し、プレリリースの Release に、五つの sdist、五つの Haddock の tarball、二つの実行ファイル、`SHA256SUMS` が添付されることを確かめる。実行ファイルが `peg-hs --version` で `0.1.0.0` を出し、`peg-hs gen` で文法を生成できることを確かめる。`SHA256SUMS` が添付と一致することを確かめる
- **版の食い違い**：タグの版と `.cabal` の版を食い違わせたタグを fork か一時的なタグで push し、ワークフローが失敗して Release を作らないことを確かめる。確かめた後にタグを消す
- **リリースノート**：AI が書いたリリースノートが書式に従い、ADR のリンクが絶対リンクで、リンク先が開けることを確かめる
- **Hackage**：sdist と Haddock の tarball を候補として上げ、モジュールの文書、CHANGELOG、依存が正しく表示されることを確かめる
- **Haddock の見直し**：Hackage の候補の表示で、各モジュールの先頭の説明と例が読めることを確かめる
- **言語サーバー**：持ち主の手での確認と記録

## トレードオフ

- peg-lsp を公開するので、言語サーバーの API（`Peg.Lsp.Server` など）も PVP の対象になる。言語サーバーは peg-hs の内部の部品に近いが、peg-cli の依存として Hackage に要る
- 五つのパッケージを同じ版で出すので、変更のないパッケージの版も上がる。版の対応を考える手間がなくなるかわりに、Hackage に中身の同じ版が増える
- rc と正式な版が同じ cabal の版（`0.1.0.0`）を持つので、rc の実行ファイルと正式な版の実行ファイルは `--version` で区別できない。rc は GitHub の Release でしか配らないので、Release の名前で区別する
- Hackage へのアップロードを人の作業にするので、手順を忘れると GitHub の Release と Hackage の版がずれる。CONTRIBUTING の手順で防ぐ
- Release をワークフローが直接公開するので、リリースノートを AI が書くまでの間、仮の本文が見える。下書きにすると公開の操作が一つ増えるので、仮の本文が短い間見えることを受け入れる
- リリースノートを AI で作るので、誤りが入りうる。手順を CONTRIBUTING に書いて入力をそろえ、人が読んで直す
- 言語サーバーの手での確認をリリースの条件にしないので、確かめていないエディタの設定の例が rc に含まれる。README に「未確認」と書いて、確かめていないことを明示する
