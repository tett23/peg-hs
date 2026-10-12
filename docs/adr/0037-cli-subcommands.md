# ADR 0037: peg-hs のコマンドをサブコマンドに分ける

ステータス: 採択

## 文脈

`peg-hs` は、いまは文法からモジュールを生成するだけのコマンドであり、`peg-hs Grammar.peg -o Grammar.hs` の形で使う。
採択済みの ADR が、ほかに四つのコマンドを加える。

- `peg-hs fmt`：文法の整形（[ADR 0032](0032-grammar-formatter.md)）
- `peg-hs lint`：文法の lint（[ADR 0033](0033-grammar-linter.md)）
- `peg-hs lsp`：言語サーバー（[ADR 0035](0035-language-server.md)）
- `peg-hs parse`：文法で入力を解析して AST と CST を表示する（[ADR 0036](0036-parse-command.md)、提案）

これらの ADR はそれぞれのコマンドの振る舞いを定めたが、コマンドの全体の形は定めていない。
引数の最初がファイル名なら生成、`fmt` なら整形、という区別は、`fmt` という名前の文法ファイルと衝突する。
オプションの解析、ヘルプ、終了状態、出力の先も、コマンドごとに決めるとばらつく。

コマンドの全体の形をここで決め、生成もサブコマンドの一つにする。

## 実装すること

### コマンドの形

```sh
peg-hs <command> [options] [arguments]
```

| コマンド | 内容 | ADR |
|---|---|---|
| `gen` | 文法から Haskell のモジュールを生成する。いまの `peg-hs FILE.peg` の動作 | [ADR 0002](0002-standalone-code-generator.md) |
| `fmt` | 文法を整形する | [ADR 0032](0032-grammar-formatter.md) |
| `lint` | 文法を lint する | [ADR 0033](0033-grammar-linter.md) |
| `lsp` | 言語サーバーを標準入出力で起動する | [ADR 0035](0035-language-server.md) |
| `parse` | 文法で入力を解析し、AST と CST を表示する | [ADR 0036](0036-parse-command.md) |
| `help` | コマンドの一覧、または `help <command>` でコマンドの説明を表示する | |

- `peg-hs` を引数なしで実行すると、コマンドの一覧を表示して失敗する
- `peg-hs --version` は版を表示する。`peg-hs <command> --help`（`-h`）は、そのコマンドの説明を表示する
- サブコマンドのない形（`peg-hs Grammar.peg`）は受け付けない。最初の引数がコマンドでなく、`.peg` で終わる場合は、`peg-hs gen Grammar.peg` を使うよう示して失敗する。peg-hs は公開前であり、いまの形を使うのはこのリポジトリだけなので、互換のための別名は設けない

### `gen` の引数

いまのオプションを引き継ぐ。

```sh
peg-hs gen GRAMMAR.peg [-o OUTPUT.hs] [--debug-entry] [--Werror] [--strip-labels MODULE]
```

### 共通の約束

- **出力の先**：結果（生成したモジュールの書き込みの報告、`parse` の表示、`help` の表示）は標準出力に、誤りと警告は標準エラー出力に書く。`lsp` は標準出力をプロトコルに使うので、記録は標準エラー出力に書く
- **診断の形**：誤りと警告は `ファイル:行:桁: error: 文言` と `ファイル:行:桁: warning: 文言` の形で書く（いまの `renderDiagnostic` の形）
- **終了状態**：成功は 0、検査で問題が見つかった場合（文法の誤り、`--Werror` の警告、lint の警告、`fmt --check` の差、`parse` の解析の失敗）は 1、コマンドの使い方の誤り（未知のコマンドとオプション、引数の不足）は 2 とする
- **ファイルの探索**：ファイルの指定を省ける `fmt` と `lint` は、[ADR 0032](0032-grammar-formatter.md) の探索の規則に従う
- **引数の解析**：オプションの解析は手で書く。optparse-applicative などに依存しない（再実装の方針）。各コマンドのオプションは、コマンドごとの表で定義し、ヘルプの文言もその表から作る

### 既存の利用の更新

- 再生成のスクリプト（`scripts/regen-fixtures.sh`）、README、CONTRIBUTING、peg-cli のテストを `peg-hs gen` の形に直す

## 実装しないこと

- サブコマンドのない形の別名
- 設定ファイル（コマンドの既定のオプションを書くもの）。fmt と lint は設定を持たない（[ADR 0032](0032-grammar-formatter.md)、[ADR 0033](0033-grammar-linter.md)）
- シェルの補完の定義
- 出力の色付け

## テスト設計

- **ヘルプ**：`peg-hs`、`peg-hs help`、`peg-hs help <command>`、`peg-hs <command> --help` の出力の golden
- **終了状態**：各コマンドの成功（0）、検査の問題（1）、使い方の誤り（2）。未知のコマンドとオプション、引数の不足
- **古い形**：`peg-hs Grammar.peg` が、`peg-hs gen Grammar.peg` を示して失敗すること
- **`gen`**：これまでの peg-cli のテスト（警告、`--Werror`、`%safe`、`--strip-labels`）が `gen` の形で通ること
- **出力の先**：結果が標準出力に、診断が標準エラー出力に出ること
- **再生成**：`scripts/regen-fixtures.sh` が `gen` の形で動き、生成物が変わらないこと

## 実装の段階

[ADR 0031](0031-rule-templates.md) の後、[ADR 0032](0032-grammar-formatter.md) の前に行う。
`fmt`、`lint`、`lsp`、`parse` は、この形の上にコマンドを加える。

## トレードオフ

- いまの `peg-hs Grammar.peg` の形を使うスクリプトは動かなくなる。公開前で、利用者はこのリポジトリだけなので、互換の別名を持たずに形を一つにする
- オプションの解析を手で書くので、オプションの組み合わせが増えると保守の手間が増える。コマンドごとのオプションは少なく、表で定義すれば十分と見込む
