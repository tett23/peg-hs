# ADR 0034: 文法ファイルのシンタックスハイライト

ステータス: 採択

## 文脈

`.peg` ファイルは、PEG の記法と Haskell の断片（verbatim ブロック、型注釈、アクション、意味述語、引数）が混ざる。
ハイライトがないと、アクションの閉じ括弧の位置や、リテラルと Haskell の文字リテラルの区別が目で追いにくい。
文法を書く量が増える（Golem の文法）前に、エディタでのハイライトを用意する。

ハイライトの方式は三つあり、対応するエディタが異なる。

- **TextMate の文法**：正規表現の規則で字句に名前（スコープ）を付ける。VS Code、Sublime Text、GitHub のコードの表示（Linguist）、多くのエディタのプラグインが読む
- **tree-sitter の文法**：JavaScript で書いた文法から増分のパーサーを生成する。Neovim、Helix、Zed が読む
- **LSP の semantic tokens**：言語サーバーが構文木から字句の種類を返す。LSP に対応するエディタのすべてで働き、解析の誤りがない

三つとも用意する。
TextMate と tree-sitter の文法は、言語サーバーなしで、ファイルを開いた直後から働く。
semantic tokens は、peg-hs 自身の構文木に基づく正確な区別（規則の定義と参照、雛形の引数など）を加える。
semantic tokens は LSP の ADR（[ADR 0035](0035-language-server.md)）で定める。
本 ADR は TextMate と tree-sitter の文法を定める。

記法の文法を、自己記述の文法（[ADR 0027](0027-switch-to-self-hosted-parser.md)）のほかに TextMate と tree-sitter の文法の二つで持つことになる。
三つのずれは、自己記述の文法の構文木（[ADR 0032](0032-grammar-formatter.md) の構文木の変種）との一致をテストで確かめて防ぐ。

## 実装すること

### 置き場所と配布

- TextMate の文法を `editors/textmate/peg.tmLanguage.json` に置く。スコープ名は `source.peg`、拡張子は `.peg` とする
- tree-sitter の文法を `editors/tree-sitter-peg/` に置く。`grammar.js`、ハイライトの問い合わせ（`queries/highlights.scm`）、Haskell の断片の埋め込みの問い合わせ（`queries/injections.scm`）を含める。生成した C のパーサー（`src/parser.c`）もコミットする（tree-sitter の文法の慣習に合わせる）
- VS Code の拡張機能の雛形（`editors/vscode/`）を置き、TextMate の文法、言語の設定（コメントの記号、括弧の対応）、言語サーバーの起動（[ADR 0035](0035-language-server.md)）を含める
- README に、VS Code、Neovim、Helix での使い方を書く
- VS Code のマーケットプレイス、nvim-treesitter、GitHub Linguist への登録は行わない

### 字句の分類

両方の文法で、次の字句を区別する。
TextMate のスコープ名と、tree-sitter のハイライトの捕捉名を対応させる。

| 字句 | TextMate のスコープ | tree-sitter の捕捉 |
|---|---|---|
| コメント（`#` から行末） | `comment.line.number-sign.peg` | `@comment` |
| ディレクティブの名前（`%module` など） | `keyword.other.directive.peg` | `@keyword.directive` |
| ディレクティブの引数 | `string.unquoted.directive.peg` | `@string.special` |
| 規則名（定義と型注釈の行頭） | `entity.name.function.rule.peg` | `@function` |
| 規則の参照 | `variable.other.rule.peg` | `@function.call` |
| 雛形の引数の山括弧（[ADR 0031](0031-rule-templates.md)） | `punctuation.definition.template.peg` | `@punctuation.bracket` |
| 束縛の名前と `:` | `variable.parameter.binding.peg` | `@variable.parameter` |
| リテラル | `string.quoted.single.peg`、`string.quoted.double.peg` | `@string` |
| リテラルと文字クラスのエスケープ | `constant.character.escape.peg` | `@string.escape` |
| 文字クラス | `string.regexp.class.peg` | `@string.regexp` |
| `.` | `constant.language.any.peg` | `@constant.builtin` |
| `<-`、`::` | `keyword.operator.definition.peg` | `@keyword.operator` |
| `/` | `keyword.operator.choice.peg` | `@operator` |
| `*`、`+`、`?`、`&`、`!`、`$` | `keyword.operator.peg` | `@operator` |
| 失敗ラベル（`^label`） | `entity.name.tag.label.peg` | `@label` |
| 予約束縛（`_span`、`_env`、`_col`） | `variable.language.peg` | `@variable.builtin` |

### Haskell の断片

次の範囲は Haskell として扱い、既存の Haskell の文法に任せる。
TextMate では `source.haskell` を埋め込み、tree-sitter では injections で `haskell` の言語を指定する。

- verbatim ブロック（`%{` から `}%` まで）
- 型注釈の `::` から行末まで
- アクション（`{` から対応する `}` まで）と意味述語（`&{`、`!{` から対応する `}` まで）
- 規則の引数（`Name(` から対応する `)` まで）

アクションの終わりは、Haskell の断片の中の括弧の深さと、文字列と文字リテラルを考慮して決める。
TextMate の文法は、begin と end の規則の再帰で括弧の入れ子を数える。
tree-sitter の文法は、自己記述の文法と同じ規則（[ADR 0027](0027-switch-to-self-hosted-parser.md) の `ActionCode` と `HsPart`）を写す。

## 実装しないこと

- 上記のマーケットプレイスと登録先への公開
- Haskell の断片のハイライトの独自実装
- tree-sitter の文法による折り畳み、字下げ、テキストオブジェクトの問い合わせ（ハイライトと埋め込みだけを用意する）

## テスト設計

- **TextMate のスナップショット**：vscode-textmate で、上の表の各字句を含む `.peg` ファイルを字句に分け、スコープの列の golden と比べる
- **tree-sitter のテスト**：`tree-sitter test` のコーパスのテスト（入力と構文木の S 式の組）と、ハイライトのテスト（`tree-sitter test` のハイライトの注釈）
- **構文木との一致**：リポジトリのすべての `.peg` ファイルを、TextMate の文法、tree-sitter の文法、自己記述の文法の構文木の変種（[ADR 0032](0032-grammar-formatter.md)）の三つで字句に分ける。リテラル、文字クラス、コメント、アクション、規則名、ラベルの範囲が三つで一致すること。記法を変えて TextMate か tree-sitter の文法を直し忘れると、このテストが失敗する
- **tree-sitter の誤りのない解析**：リポジトリのすべての `.peg` ファイルで、tree-sitter の構文木に ERROR の節がないこと
- **埋め込み**：アクションの中の `}` を含む文字列（`{ "}" }`）や、入れ子の括弧（`{ f {x = 1} }`）で、アクションの終わりを正しく決めること
- テストは Node の最新の LTS と tree-sitter の CLI で動かし、CI に Node のジョブを加える

## 実装の段階

[ADR 0032](0032-grammar-formatter.md) の後に行う。
構文木との一致のテストに、[ADR 0032](0032-grammar-formatter.md) の構文木の変種を使うためである。
[ADR 0031](0031-rule-templates.md)（雛形）が先に実装されていれば、雛形の記法も含める。
[ADR 0035](0035-language-server.md)（LSP）の VS Code の拡張機能は、本 ADR の雛形に加える。

## トレードオフ

- 記法の文法を三つ（自己記述、TextMate、tree-sitter）で持つことになる。ずれは構文木との一致のテストで検出するが、記法を変えるたびに三つを直す手間は残る
- TextMate の文法は正規表現の規則なので、文脈に依存する区別（`A(x)` の呼び出しと `A (x)` の逐次など）は近似になる。空白の有無で区別できるものは区別し、できないものは構文木との一致のテストで許容する範囲を記録する
- tree-sitter の生成した C のパーサーをコミットするので、リポジトリに大きな生成物が加わる
- CI に Node のジョブが加わり、Haskell のツールチェーンとは別の依存を持つ
