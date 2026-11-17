# ADR 0101: テストとビルドが読む文書の変更では CI を省かない

Status: accepted

## 文脈

[ADR 0039](0039-faster-ci.md) は、文書だけの変更では Haskell と Node のジョブを動かさないと決めた。
文書だけの変更とは、`docs/` の下のファイルと `.md` のファイルだけを変えることである。
[ADR 0039](0039-faster-ci.md) は、その理由を「テストは `docs/` と `*.md` のファイルを読まないので、これらだけの変更では結果が変わらない」とした。
[ADR 0072](0072-required-checks-for-auto-merge.md) は、プルリクエストでの判定を `changes` のジョブに移したが、同じ条件を引き継いだ。

しかし、いまのテストは文書を読む。
[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md) のテストは記法の解説と README の完全な文法の例を、[ADR 0084](0084-english-version-of-the-syntax-guide.md) のテストは記法の解説の日本語版と英語版の対応を、[ADR 0045](0045-fixes-before-v0-1-0.md) のテストは README の例の生成と実行を確かめる。
[ADR 0018](0018-tab-partial-consumption.md) の CommonMark の検査と、[ADR 0073](0073-editor-grammars-in-releases.md) のエディタの文法の写しの検査も、`.md` のファイルを読む。
そのため、これらの文書だけを変えたプルリクエストでは、その文書を確かめるテストが動かずにマージされる。

リポジトリの持ち主が全リポジトリに置いた決まり（dotfiles ADR 0129）は、標準の `docs/` の構成のパスの中だけの変更では CI のビルドとテストを省き、ビルドやテストの入力になるファイルの変更では省かないとしている。
この ADR は、このリポジトリの判定を、その決まりに合わせる。

## 調査した事項

- `.github/workflows/ci.yml:12` は、main への `push` に `paths-ignore: ['docs/**', '**.md']` を付けている。
- `.github/workflows/ci.yml:52` の `changes` のジョブは、プルリクエストの `git diff --name-only "$BASE...$HEAD"` に `docs/` の下と `.md` のほかのパスがあれば `code=true` を出す。`push` では常に `code=true` を出す。`setup-node` の段は判定の後にあり、プルリクエストで `code` が `true` のときだけ動く（`ci.yml:58-64`）。
- ビルドとテストのジョブ（`haskell`、`test`、`haddock`、`sdist`、`hooks`、`editors`、`wasm`）は、`code` が `true` のときだけ動く。
- `docs/` の下と `.md` のファイルのうち、テストが読むものは次のとおりである。
  - `packages/peg-grammar/test/Main.hs:696` は、`docs/syntax.md`、`docs/syntax.en.md`、`README.md`、`README.ja.md` の完全な文法の例を解析して検査する（[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md)）。
  - `packages/peg-grammar/test/Main.hs:725-726` は、`docs/syntax.md` と `docs/syntax.en.md` を読み、二つが対応することを検査する（[ADR 0084](0084-english-version-of-the-syntax-guide.md)）。
  - `packages/peg-codegen/test/Main.hs:1442` は、`README.md` と `README.ja.md` の例を生成し、動かす（[ADR 0045](0045-fixes-before-v0-1-0.md)）。
  - `conformance/test/CommonMarkMain.hs:245` は、`conformance/commonmark/tabs/` の直下の `.md` のファイルを `listDirectory` で読み、参照実装の出力と比べる（[ADR 0018](0018-tab-partial-consumption.md)）。
  - `editors/test/pack.test.js:13` は `scripts/pack-editors.sh` を動かし、`:27-31` で写しと `editors/README.md` のバイト列が一致することを確かめる（[ADR 0073](0073-editor-grammars-in-releases.md)）。
  - `packages/peg-cli/test/Main.hs:1036-1037` は、`docs/audits/2026-11-07-inj-module.hpeg.txt` を読む（[ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md)）。
- 六つのパッケージの `.cabal` は、どれも `extra-doc-files: CHANGELOG.md` を持つ（たとえば `packages/peg-runtime/peg-runtime.cabal:20`）。`packages/*/CHANGELOG.md` は、`sdist` のジョブが作るソースのアーカイブに入る。
- そのほかの `.md` のファイルと `docs/` の下のファイル（`docs/specifications.md`、`docs/conformance/`、`CONTRIBUTING.md`、`verification/README.md` など）は、`packages/*/test`、`conformance/test`、`editors/test`、`scripts`、`verification` のどれからも読まれない（`rg -n 'docs/|\.md\b|README|CHANGELOG|CONTRIBUTING'` で探した）。
- `.github/workflows/adr.yml` は、`push` の main とすべての `pull_request` で、文書だけの変更も含めて adr-guard を動かす。
- `docs/specifications.md:14` は、文書（`docs/` の下と `.md` のファイル）だけの変更では、`ci` がほかのジョブを飛ばして成功すると書いている。

## 実装すること

### 判定の関数

- ビルドとテストが要るかの判定を、`scripts/ci-changes.mjs` の関数 `needsBuild(paths)` にまとめる。
- パスは、リポジトリの根からの相対パスとし、大文字と小文字を区別して比べる。
- **文書のパス**を、`docs/` で始まるか、`.md` で終わるパスとする。`docs/` は根の `docs/` だけで、`packages/x/docs/` は含まない。
- **入力の一覧**を、文書のパスのうち、ビルドかテストが読むものとする。いまの一覧は次のとおりである。`*` は `/` を含まない一つの名前に合う。
  - `docs/syntax.md`
  - `docs/syntax.en.md`
  - `README.md`
  - `README.ja.md`
  - `editors/README.md`
  - `conformance/commonmark/tabs/*.md`
  - `docs/audits/2026-11-07-inj-module.hpeg.txt`
  - `packages/*/CHANGELOG.md`
- `needsBuild(paths)` は、`paths` のどれかが文書のパスでないか、入力の一覧に合うときに真を返し、それ以外では偽を返す。

### 判定のコマンド

- `node scripts/ci-changes.mjs <前のコミット> <後のコミット>` は、二つのコミットの差分のパスを `git diff --no-renames --name-only -z` で取り、`needsBuild` の結果を `true` か `false` で出す。`--no-renames` は、コードのファイルを文書のパスへ移す変更で、消えたコードのパスも差分に出すためである。
- 前のコミットが `0` をちょうど 40 個並べた文字列のとき（ブランチの最初の push）は、`git` を動かさずに `true` を出す。
- 引数がちょうど二つでないとき、どちらかが空の文字列のとき、`git diff` が失敗したときは、0 でない終了コードで終わり、何も出さない。`changes` のジョブは失敗し、`ci` も失敗する。

### ワークフロー

- `changes` のジョブで、`setup-node` の段を判定の段の前に置き、プルリクエストと push の両方で動かす。
- 判定の前に、`scripts/ci-changes.test.mjs` を `node --test` で動かす段を置く。
- 判定の段は、プルリクエストでは `node scripts/ci-changes.mjs "$(git merge-base "$BASE" "$HEAD")" "$HEAD"` の結果を、main への `push` では `node scripts/ci-changes.mjs "$BEFORE" "$GITHUB_SHA"` の結果を `code` に出す。
- 既存の `node --test scripts/lsp-median*.test.mjs scripts/lsp-monitor-changes.test.mjs` の段は、これまでどおり `code` が `true` のときだけ動かす。
- `ci.yml` の `push` から `paths-ignore` を外す。main への文書だけの push でもワークフローは起動し、`changes` と `ci` のジョブだけが動く。
- `.github/workflows/adr.yml` の検査は、これまでどおり、文書だけの変更でも動かす。

### 一覧を保つ決まり

- テストかビルドに文書のパスを読ませる変更では、同じ変更で、そのパスを入力の一覧に足す。
- 一覧のパスを読むテストかビルドを消す変更では、同じ変更で、そのパスを一覧から除く。

### 前の ADR と文書

- この ADR を採択したら、[ADR 0039](0039-faster-ci.md) のステータスを、`part` を「文書だけの変更では Haskell と Node のジョブを動かさない」とした `superseded` にする。
- [ADR 0072](0072-required-checks-for-auto-merge.md) のステータスを、`part` を「変更の判定」とした `superseded` にする。
- `docs/specifications.md:14` と、CONTRIBUTING（日本語と英語）の CI の説明を、入力の一覧を含めて書き直す。
- `ci.yml` の冒頭の注釈を、この ADR に合わせて書き直す。

## 実装しないこと

- 変更のあったパッケージだけを試験すること。判定は、ビルドとテストが要るかどうかの二つに限る（[ADR 0072](0072-required-checks-for-auto-merge.md) と同じ）。
- テストが読む文書を、テストのソースから自動で見つけること。一覧は手で保つ。
- 文書の中のコード例のうち、いまテストしていないものをテストすること。
- `scripts/lsp-monitor-changes.mjs` の `shouldMeasure` の判定を変えること。言語サーバーの計測の要否は、別の ADR で扱う。

## 不変条件

- `I1`: `needsBuild(paths)` は、`paths` のどれかが文書のパスでないか、入力の一覧に合うとき、そしてそのときに限り真を返す。
- `I2`: `scripts/ci-changes.mjs` は、前のコミットが `0` をちょうど 40 個並べた文字列のとき、`git` を動かさずに `true` を出す。引数がちょうど二つでないとき、どちらかが空のとき、`git diff` が失敗したときは、0 でない終了コードで終わり、何も出さない。
- `I3`: 一時の git のリポジトリで、`scripts/ci-changes.mjs` は、改名を含むコミットの差分で、改名の前と後の両方のパスを `needsBuild` に渡す。
- `I4`: `.github/workflows/ci.yml` に `paths-ignore` が無く、`changes` のジョブに `scripts/ci-changes.mjs` の呼び出しがちょうど二つ（プルリクエストと push）あり、`changes` のジョブが `git diff` を直接動かさない。

| 入力 | 期待 | 不変条件 |
| --- | --- | --- |
| パスが 0 件 | 偽 | I1 |
| `docs/adr/0101-run-ci-for-documents-that-tests-read.md` だけ | 偽 | I1 |
| `docs/specifications.md` と `CONTRIBUTING.md` | 偽 | I1 |
| `docs/benchmarks/` の下の `.md` と `.svg` | 偽 | I1 |
| `docs/audits/` の下の `2026-11-07-inj-module.hpeg.txt` のほかのファイルだけ | 偽 | I1 |
| `conformance/README.md` だけ | 偽 | I1 |
| `docs/syntax.md` だけ | 真 | I1 |
| `docs/syntax.en.md` だけ | 真 | I1 |
| `README.md` だけ | 真 | I1 |
| `README.ja.md` だけ | 真 | I1 |
| `editors/README.md` だけ | 真 | I1 |
| `conformance/commonmark/tabs/item-quote.md` だけ | 真 | I1 |
| `conformance/commonmark/tabs/sub/a.md` だけ | 偽 | I1 |
| `conformance/commonmark/tabs/item-quote.html` だけ | 真（文書のパスでない） | I1 |
| `docs/audits/2026-11-07-inj-module.hpeg.txt` だけ | 真 | I1 |
| `packages/peg-grammar/CHANGELOG.md` だけ | 真 | I1 |
| `packages/peg-grammar/sub/CHANGELOG.md` だけ | 偽 | I1 |
| `packages/x/README.md` だけ | 偽 | I1 |
| `packages/peg-grammar/docs/x.txt` だけ | 真（文書のパスでない） | I1 |
| `docs/X.MD` だけ | 偽（`docs/` で始まる） | I1 |
| `docs/adr/` の一つと `packages/peg-grammar/src/` の一つ | 真 | I1 |
| `.github/workflows/ci.yml` だけ | 真 | I1 |
| 前のコミットが `0` を 40 個 | `true`、`git` を動かさない | I2 |
| 前のコミットが `0` を 39 個で、そのコミットが無い | 0 でない終了コード、何も出さない | I2 |
| 引数なし、引数が一つ、引数の一つが空の文字列 | 0 でない終了コード、何も出さない | I2 |
| `src/A.hs` を `docs/A.md` に移したコミット | `true` | I3 |
| `docs/syntax.md` を `docs/old.md` に移したコミット | `true` | I3 |
| `docs/old.md` を `docs/new.md` に移したコミット | `false` | I3 |
| `ci.yml` に `paths-ignore` が残る | 失敗 | I4 |

## 受けいれ条件

- `A1`: 実装の後に、`docs/adr/` だけを変えるプルリクエストの CI で、ビルドとテストのジョブが飛ばされ、`ci` と `adr` が成功する。
- `A2`: 実装の後に、`docs/syntax.md` だけを変えるプルリクエストの CI で、ビルドとテストのジョブが動く。
- `A3`: 実装の後に、文書だけを変えたコミットを main に push すると、CI のワークフローが起動し、`changes` が `code=false` を出し、ビルドとテストのジョブが飛ばされる。

## テスト設計

- `I1` から `I4` は、`scripts/ci-changes.test.mjs` に `node:test` で書き、表の入力を与える。テストの名前は `ADR 0101 I1: …` の形にする。
- `I2` の `git` を動かさないことは、`node` を `process.execPath` の絶対パスで起動し、環境の `PATH` を空にして確かめる。
- `I3` は、`git init` した一時のディレクトリでコミットを作り、`node scripts/ci-changes.mjs <前> <後>` を動かして確かめる。
- `I4` は、`.github/workflows/ci.yml` を文字列として読んで確かめる。
- `A1` と `A2` は、実装のプルリクエストをマージした後に、それぞれの変更だけのプルリクエストを作り、CI のジョブの状態を見て確かめる。`A2` のプルリクエストは、`docs/syntax.md` の誤字の直しなど、マージしてよい変更にする。
- `A3` は、`A1` のプルリクエストをマージしたときの main の CI の実行で確かめる。

## トレードオフ

- 入力の一覧は手で保つので、テストに文書を読ませたのに一覧に足し忘れると、その文書だけの変更でテストが飛ばされる。いまと同じ種類の見落としが残るが、一覧が一か所にまとまるので、レビューで見つけやすくなる。
- main への文書だけの push でも、ワークフローが起動する。`changes` と `ci` のジョブは checkout と Node だけで、数十秒で終わる（[ADR 0072](0072-required-checks-for-auto-merge.md) のトレードオフと同じ見込みで、測っていない）。
- `packages/*/CHANGELOG.md` と `editors/README.md` だけの変更でも、ビルドとテストが動く。どちらもソースのアーカイブかエディタの文法の写しに入るファイルで、内容を変えても結果はまず変わらないが、消したときや名前を変えたときに `sdist` か `editors` のジョブが失敗するので、省かない。
- 判定のコマンドが失敗すると `ci` が失敗する。判定できないときにテストを省くより、止めるほうを選ぶ。

## 参考文献

- [ADR 0018](0018-tab-partial-consumption.md)：CommonMark のタブの検査
- [ADR 0039](0039-faster-ci.md)：文書だけの変更で Haskell と Node のジョブを動かさない
- [ADR 0045](0045-fixes-before-v0-1-0.md)：README の例の生成と実行の検査
- [ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md)：文書の完全な文法の例の検査
- [ADR 0072](0072-required-checks-for-auto-merge.md)：プルリクエストでの変更の判定と `ci` のジョブ
- [ADR 0073](0073-editor-grammars-in-releases.md)：エディタの文法の写しの検査
- [ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md)：監査の記録の文法を読むテスト
- [ADR 0084](0084-english-version-of-the-syntax-guide.md)：記法の解説の日本語版と英語版の検査
