# ADR 0069: ハイライトを細かくし、保存時に整形する

ステータス: 採択

## 文脈

いまの言語の道具は、言語サーバー、lint、整形、シンタックスハイライトがそろっていることを前提にしている。
peg-hs は四つとも持つ（[ADR 0032](0032-grammar-formatter.md)、[ADR 0033](0033-grammar-linter.md)、[ADR 0034](0034-syntax-highlighting.md)、[ADR 0035](0035-language-server.md)）が、エディタでの使い勝手には二つの不足がある。

一つは、ハイライトの粒度である。
tree-sitter の問い合わせ（`editors/tree-sitter-hpeg/queries/highlights.scm`）は、次のものに色を付けていない。

- 括弧（`(` `)`）、アクションの波括弧（`{` `}`）、verbatim ブロックの区切り（`%{` `}%`）、束縛の `:`、ラベルの `^`、雛形の引数の `,`
- 指示の引数の中身。`%entry Expr` の `Expr` は規則の名前、`%recover l R` の `l` はラベル、`R` は規則の名前だが、どれも `@string.special` の一色になる
- 折り畳み、字下げ、名前の定義と参照の問い合わせ（`folds.scm`、`indents.scm`、`locals.scm`）がない

言語サーバーの semantic tokens も、指示の引数を区別しない。
Haskell の断片（アクション、意味述語、引数、型、verbatim ブロック）は、エディタの Haskell の文法に任せている（[ADR 0034](0034-syntax-highlighting.md)）。

もう一つは、保存時の整形である。
整形は言語サーバーの整形（`textDocument/formatting`）で行えるが、エディタの既定では保存時に動かない。
VS Code の拡張機能は保存時の整形を既定にしておらず、README の Neovim と Helix の設定も、保存時の整形を任意の設定として載せているだけである。
整形の流儀は一つに固定しており（[ADR 0032](0032-grammar-formatter.md)）、整形しない理由は少ないので、保存時に整形するのを既定にする。

## 実装すること

### tree-sitter の問い合わせ

`highlights.scm` に次の capture を加える。
capture の名前は、nvim-treesitter と Helix の慣用の名前に合わせる。

| 対象 | capture |
|---|---|
| `(` `)` `[` `]`（文字クラスの括弧を除く） | `@punctuation.bracket` |
| アクションの `{` `}`、verbatim ブロックの `%{` `}%` | `@punctuation.special` |
| 束縛の `:`、雛形の引数の `,` | `@punctuation.delimiter` |
| ラベルの `^` | `@operator` |
| `%start`、`%entry`、`%nomemo`、`%token`、`%trivia`、`%inline` の引数の規則の名前、`%recover` の二つめの引数 | `@function.call` |
| `%recover` と `%safe` の一つめの引数のラベル | `@label` |
| `%module` の引数 | `@module` |
| `%language` の引数 | `@constant` |

指示の引数を区別するには、tree-sitter の文法で、指示ごとに引数の節を分ける必要がある。
`directive` の規則を、引数の種類ごとの節（`module_name`、`rule_name_argument`、`label_argument`、`extension_name`）を持つ形にする。
文法の範囲の一致のテスト（[ADR 0034](0034-syntax-highlighting.md)）は、規則の名前とラベルの範囲を比べるので、指示の引数の規則の名前とラベルも比べる対象に加える。

次の問い合わせを加える。

- `folds.scm`：規則の定義（型注釈と定義をまとめて）、verbatim ブロック、複数行のアクション
- `indents.scm`：`/` で始まる続きの選択肢の行を字下げする。整形の流儀（[ADR 0032](0032-grammar-formatter.md)、`/` を `<-` の桁に揃える）に合わせる
- `locals.scm`：規則の定義を `@local.definition.function`、規則の参照を `@local.reference`、束縛を `@local.definition.var` とする

### 言語サーバーの semantic tokens

- 指示の引数の規則の名前を `function`、ラベルを `decorator`（いまのラベルと同じ）、`%module` の引数を `namespace` とする。`tokenTypes` に `namespace` を加える
- 括弧や区切りには token を付けない。エディタの文法のハイライトに任せる

### TextMate の文法

- 上の表と同じ区別を TextMate の文法にも加え、スナップショットの golden を作り直す。VS Code では semantic tokens が TextMate の色を上書きするが、言語サーバーを動かさない環境のために合わせる

### 保存時の整形

- VS Code の拡張機能の `package.json` の `configurationDefaults` に、`"[hpeg]": { "editor.formatOnSave": true }` を加える。利用者は自分の設定で上書きできる
- README の Neovim の節の言語サーバーの設定に、保存時に `vim.lsp.buf.format()` を呼ぶ自動コマンドを、任意の設定ではなく推奨の設定として含める
- README の Helix の節の `[[language]]` に `auto-format = true` を書く。Helix は言語サーバーの整形で保存時に整形する

### 文書

- README のエディタの節に、言語サーバー、lint、整形、ハイライトの四つがそろうことと、保存時に整形することを書く
- docs/specifications.md のエディタの支援の節を合わせる

## 実装しないこと

- Haskell の断片の中身のハイライト。これまでどおり、エディタの Haskell の文法に任せる
- 言語サーバーでの範囲の整形（`textDocument/rangeFormatting`）と入力中の整形（`onTypeFormatting`）
- tree-sitter の textobjects の問い合わせ
- VS Code の拡張機能の Marketplace への公開（[ADR 0044](0044-release-v0-1-0.md) の残課題）

## テスト設計

先に書き、いまの実装で失敗させる。

- **tree-sitter のハイライト**：`test/highlight/notation.hpeg` に、上の表の対象ごとの断言（`^ punctuation.bracket` など）を加え、`tree-sitter test` で通ること
- **tree-sitter の文法**：指示の引数の節を分けた後も、コーパスのテストと、リポジトリのすべての文法を `ERROR` なく読むテストが通ること
- **範囲の一致**：指示の引数の規則の名前とラベルを範囲の一致のテストに加え、自己記述の文法、tree-sitter、TextMate の三つで一致すること
- **folds、indents、locals**：`tree-sitter query` で問い合わせが文法に対して正しいこと（節の名前の誤りがないこと）を確かめるテストを、editors のテストに加える。Neovim で、規則の定義が畳め、続きの選択肢が字下げされることを、画面なしで動かして確かめる
- **semantic tokens**：`%entry Expr`、`%recover l R`、`%module M` の引数の token の種類が上のとおりであること（peg-lsp のテスト）
- **TextMate**：スナップショットの golden に、新しい scope が現れること
- **保存時の整形**：VS Code の拡張機能の `package.json` に `configurationDefaults` があることをテストで確かめる。Neovim の設定で、整形されていない文法を保存すると整形されることを、画面なしで動かして確かめる。Helix は手で確かめる項目（[ADR 0044](0044-release-v0-1-0.md)）に加える

## トレードオフ

- 指示ごとに tree-sitter の節を分けるので、tree-sitter の文法と、範囲の一致のテストが大きくなる。指示の種類は少なく、増える頻度も低い
- 保存時の整形を既定にすると、整形の流儀に従わない書き方は保存のたびに直される。流儀は一つに固定しており、利用者は VS Code の設定で無効にできる
- capture の名前はエディタの慣用に合わせるので、テーマによって色の付き方が変わる。名前を慣用に合わせることで、多くのテーマで色が付く

## 参考文献

- nvim-treesitter, CONTRIBUTING.md（capture の名前の一覧）. https://github.com/nvim-treesitter/nvim-treesitter/blob/main/CONTRIBUTING.md
- Helix, Themes（scope の名前）. https://docs.helix-editor.com/themes.html
- Language Server Protocol Specification 3.17, Semantic Tokens. https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens
