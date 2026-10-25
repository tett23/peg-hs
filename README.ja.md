# peg-hs

peg-hs は、PEG（Parsing Expression Grammar）で書いた文法から、Haskell のパーサーを生成するツールチェーンである。

[English README](README.md)

## 概要

文法は `.hpeg` ファイルに書く。
各規則には結果の型とセマンティックアクション（規則が成功したときに値を作る Haskell の式）を付ける。
`peg-hs gen` が文法から Haskell のモジュールを生成し、利用者のプログラムはそのモジュールの `parse` を呼んで、自分の AST を直接受け取る。

ほかのパーサー生成器と比べたときの特徴は、次のとおりである。

- **左再帰をそのまま書ける**：`Expr <- Expr '+' Term / Term` のような直接と間接の左再帰を受理する。意味論は bounded left recursion（Medeiros et al. 2014）である（[ADR 0001](docs/adr/0001-bounded-left-recursion.md)）
- **生成したモジュールの依存が小さい**：生成したモジュールが依存するのは実行時のライブラリ peg-runtime だけである。同じ文法からはバイト単位で同じモジュールを生成するので、生成物をリポジトリにコミットできる（[ADR 0002](docs/adr/0002-standalone-code-generator.md)）
- **型の誤りを文法の行で報告する**：アクションの型の誤りは、GHC が `.hpeg` ファイルの行と桁で報告する（[ADR 0014](docs/adr/0014-generated-module-api.md)）
- **文脈に依存する構文を書ける**：意味述語、引数付き規則、読み取り専用の解析環境、桁の参照で、字下げに依存する構文や前方参照を書ける。パックラットのメモ化と左再帰の正しさを保つように設計している（[ADR 0012](docs/adr/0012-context-sensitive-extensions.md)）
- **空白とコメントを失わない構文木**：`%syntax` を書くと、rust-analyzer に倣ったロスレスな構文木も作る。整形や lint のような道具のためである（[ADR 0019](docs/adr/0019-lossless-syntax-tree.md)）
- **構文エラーから回復する**：ラベル付きの失敗（`e ^label` と `%recover`）で、一度の解析で複数の誤りを報告できる。回復するモードは、誤りのノードを含むロスレスな構文木を必ず返す。言語サーバーのためである（[ADR 0021](docs/adr/0021-error-recovery.md)）

実在する言語の文法で、適合性を確かめている。

- **JSON**（[JSONTestSuite](https://github.com/nst/JSONTestSuite)）：受理すべき 95 件と拒否すべき 188 件のすべてに合格する
- **CommonMark 0.31.2**：仕様の例 652 件すべてに適合する
- **Lua 5.5**（Lua 5.5.1 の公式のテストスイート）：マニュアルの構文を間接の左再帰のまま書いた文法で、34 ファイルすべてを受理する。優先順位、結合性、拒否は、参照実装から作った正解と一致する
- **TOML 1.1.0**（[toml-test](https://github.com/toml-lang/toml-test) v2.2.0）：受理すべき 214 件のすべてで期待する JSON と一致し、拒否すべき 467 件をすべて拒否する。回復するモードでは、全件でロスレスな構文木を返す

**状態**：リリース候補（最新は v0.1.0-rc2）を、GitHub の [Releases](https://github.com/tett23/peg-hs/releases) で配布している。
Hackage にはまだ上げていない（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）。

## 導入

### 実行ファイル

GitHub の [Releases](https://github.com/tett23/peg-hs/releases) に、Linux（x86-64）と macOS（arm64）の `peg-hs` を置いている。
アーカイブを展開し、`peg-hs` を `PATH` の通ったディレクトリに置く。
アーカイブが壊れていないことは、同じ Release の `SHA256SUMS` で確かめられる。

```sh
tar xzf peg-hs-0.1.0-rc2-x86_64-linux.tar.gz
install peg-hs-0.1.0-rc2-x86_64-linux/peg-hs ~/.local/bin/
peg-hs --version
```

### ソースから

ほかの環境では、ソースからビルドする。
GHC 9.10、9.12、9.14 のどれかと、cabal-install が要る（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）。

```sh
git clone https://github.com/tett23/peg-hs.git
cd peg-hs
cabal install exe:peg-hs --installdir="$HOME/.local/bin" --install-method=copy --overwrite-policy=always
```

## 最初の文法

足し算と掛け算と括弧の式を読む文法を例に、生成して使うまでを示す。
次の文法を `grammar/Calc.hpeg` に置く。

<!-- readme-example: grammar/Calc.hpeg -->
```hpeg
%module Calc.Parser
%{
import qualified Data.Text as T

data Expr = Num Int | Add Expr Expr | Mul Expr Expr
  deriving (Show)
}%

# 足し算は掛け算より弱く、どちらも左に結合する。左再帰でそのまま書ける。
Expr :: Expr
Expr <- l:Expr '+' Sp r:Term { Add l r }
     / Term

Term :: Expr
Term <- l:Term '*' Sp r:Atom { Mul l r }
     / Atom

Atom :: Expr
Atom <- d:$[0-9]+ Sp { Num (read (T.unpack d)) }
     / '(' Sp e:Expr ')' Sp { e }

Sp :: ()
Sp <- ' '* { () }
```

`%module` は生成するモジュールの名前である。
`%{` と `}%` の間（verbatim ブロック）には、生成したモジュールにそのまま入る Haskell を書く。
`Expr :: Expr` は規則 `Expr` の結果の型で、`Expr <- ...` が規則の定義である。
`l:Expr` は結果に名前を付け（束縛）、`{ Add l r }` はアクションである。
`$[0-9]+` は、読んだ範囲の文字列（`Text`）を値にする。
記法の詳しい解説は [docs/syntax.md](docs/syntax.md) にある。

`peg-hs gen` でモジュールを生成する。

```sh
peg-hs gen grammar/Calc.hpeg -o src/Calc/Parser.hs
```

生成したモジュールは、渡したパスを記録する。
先頭のコメントと、GHC の誤りを文法の行に向ける `LINE` プラグマである。
パスは、モジュールをコンパイルするパッケージのディレクトリからの相対パスで渡す。
cabal はそのディレクトリで GHC を動かすので、エディタが誤りの位置から文法を開ける。
また、どの機械で生成しても同じモジュールになる（[ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

文法を確かめるだけなら、生成したモジュールをプロジェクトに組み込む前に `peg-hs parse` で入力を解析できる。

```sh
echo -n '1 + 2 * (3 + 4)' > input.txt
peg-hs parse grammar/Calc.hpeg input.txt
```

```text
Add (Num 1) (Mul (Num 2) (Add (Num 3) (Num 4)))
```

## 生成したモジュールを使う

生成したモジュールは、開始規則の入口 `parse :: Text -> Either ParseError a` を公開する。
`a` は開始規則（最初に定義した規則、または `%start` で指定した規則）の型である。
解析に失敗すると、最も遠くまで読めた位置と、そこで期待した字句の集合を `ParseError` で返す。
`Peg.Runtime` の `renderParseError` は、それを `1:4: expected ' ', '(' or [0-9]` のような一行にする。

次のプログラムは、標準入力の一行を解析して、AST か誤りを表示する。

<!-- readme-example: src/Main.hs -->
```haskell
module Main (main) where

import Calc.Parser (parse)
import qualified Data.Text.IO as TIO
import Peg.Runtime (renderParseError)

main :: IO ()
main = do
  input <- TIO.getLine
  case parse input of
    Right expr -> print expr
    Left err -> TIO.putStrLn (renderParseError err)
```

利用者のパッケージの `.cabal` には、peg-runtime と text を `build-depends` に加える。
生成したモジュールの先頭のコメントに、要る peg-runtime の版の範囲が書いてある（`-- It needs peg-runtime >=0.1 && <0.2.`）。

```cabal
executable calc
  main-is:          Main.hs
  hs-source-dirs:   src
  other-modules:    Calc.Parser
  build-depends:
    , base
    , peg-runtime  >=0.1 && <0.2
    , text
  default-language: GHC2021
```

peg-runtime はまだ Hackage にない。
それまでは、`cabal.project` で GitHub のリポジトリを指す。
`tag` には、使う peg-hs のリリースのタグを書く。

```cabal
packages: .

source-repository-package
  type:     git
  location: https://github.com/tett23/peg-hs
  tag:      v0.1.0-rc2
  subdir:   packages/peg-runtime
```

文法を変えたら、`peg-hs gen` で生成し直し、生成したモジュールもコミットする。
生成したモジュールは文法から決まるので、CI で生成し直して差分がないことを確かめると、生成し忘れを防げる。

このほか、生成したモジュールは次のものを公開する。

- `%entry` で指定した規則の入口（`parseExpr` など）
- `%syntax` を書いた文法では、ロスレスな構文木を返す `parseSyntax`（[ADR 0019](docs/adr/0019-lossless-syntax-tree.md)）
- `%recover` を書いた文法では、誤りから回復して複数の誤りを返す `parseRecover`。`%syntax` も書くと、誤りのノードを含む構文木を返す `parseSyntaxRecover` も公開する（[ADR 0021](docs/adr/0021-error-recovery.md)）
- `%env` を書いた文法では、どの入口も最初の引数に解析環境の値を取る（[ADR 0012](docs/adr/0012-context-sensitive-extensions.md)）

詳しい一覧は、Hackage の文書（peg-codegen の `Peg.Codegen` と peg-runtime の `Peg.Runtime`）にある。
入口と `%syntax` の名前は、`gen --export` でプログラムが使うものだけに狭められる（[ADR 0061](docs/adr/0061-select-generated-exports.md)）。

## コマンド

`peg-hs` は、目的ごとのサブコマンドを持つ（[ADR 0037](docs/adr/0037-cli-subcommands.md)）。
オプションと例は `peg-hs help COMMAND` で表示できる。
値を取るオプションは、`--output FILE` と `--output=FILE` のどちらの形でも書ける。
ファイルは、ロケールによらず UTF-8 で読み書きする（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）。

| コマンド | 目的 |
|---|---|
| `peg-hs gen GRAMMAR.hpeg [-o FILE]` | 文法から Haskell のモジュールを生成する |
| `peg-hs fmt [FILE\|DIR...]` | 文法を一つの流儀で整形する |
| `peg-hs lint [FILE\|DIR...]` | 誤りである書き方を警告する |
| `peg-hs label GRAMMAR.hpeg [--write]` | 安全と示せる位置にラベルを挿入する |
| `peg-hs parse GRAMMAR.hpeg INPUT` | 入力を解析して、AST か構文木を表示する |
| `peg-hs lsp` | 言語サーバーを標準入出力で動かす |

終了状態は、成功で 0、コマンドの使い方の誤りで 2 である。
文法の誤り、読み書きできないファイル、`lint` の警告、`fmt --check` で見つかった整形されていないファイル、`gen --Werror` での警告では 1 になる。

### gen

`gen` は文法を検査し、モジュールを書き出す。
出力のパスを省くと、文法のパスの拡張子を `.hs` にしたものになる。

生成器は、正しい入力を拒否するかもしれないラベルを警告する（[ADR 0028](docs/adr/0028-label-safety-check.md)）。
`--Werror` を付けると、警告があればモジュールを書かずに失敗する。
作者が確かめたラベルは、文法に `%safe label` と書くと警告されない。

`--export NAME` を付けると、モジュールは指定した名前と `%export` の名前だけを公開する（[ADR 0061](docs/adr/0061-select-generated-exports.md)）。
`NAME` には、入口（`parse`、`parseExpr`、`parseSyntaxRecover` など）か `%syntax` の名前（`nameOfSyntaxKind`、種類の定数、`(..)` を除いたラッパーの型、`cast…Syntax`、取り出し関数）を書き、何度でも指定できる。
ほかの名前からしか使われない規則などの宣言は出力しない。
`%{ }%` のブロックは常に出力するので、そこから生成器の名前を参照するなら、その名前も `--export` に加える。
生成器が定義しない名前は文法の誤りとし、1 行 1 桁の誤りとして報告する。

```sh
peg-hs gen grammar/Doc.hpeg --export parseSyntaxRecover --export nameOfSyntaxKind -o src/Doc/Parser.hs
```

### fmt

`fmt` は、文法を一つに固定した流儀で整形して上書きする（[ADR 0032](docs/adr/0032-grammar-formatter.md)）。
流儀を選ぶオプションはない。コメントは残る。
`--check` はファイルを書き換えず、整形されていないファイルの名前を表示し、一つでもあれば失敗する。CI での検査に使う。

引数にディレクトリを渡すと、その下の `.hpeg` ファイルを対象にする。
以前の拡張子 `.peg` は、ほかの PEG の道具と重なるので探さない。ファイルを直接渡せば、拡張子によらず扱う（[ADR 0050](docs/adr/0050-hpeg-extension.md)）。
引数を省くと、現在のディレクトリの下の `.hpeg` ファイルをすべて対象にする。
どちらの場合も、名前が `.` で始まるディレクトリと `dist-newstyle` はたどらない。

### lint

`lint` は、静的検査を通った文法のうち、誤りである書き方を警告する（[ADR 0033](docs/adr/0033-grammar-linter.md)）。
対象は、試されない選択肢と成功しない選択肢、前の選択肢と同じ選択肢、先読みの中の効果のないラベル、使われない束縛である。
規則は固定で、警告を抑える手段はない。どの警告も文法を直せば消え、警告が一つでもあれば失敗する。
対象のファイルの選び方は `fmt` と同じである。

### label

`label` は、正しい入力を拒否しないと検査で示せる位置を探し、そこに付けるラベルを `ファイル:行:桁: ^名前` の形で一行ずつ表示する（[ADR 0054](docs/adr/0054-automatic-label-insertion.md)）。
`--write` を付けると、文法のファイルにも書き込む。コメントや空白はそのまま残る。
挿入したラベルは受理する言語を変えないが、回復はしない。回復させたいラベルには、作者が `%recover` と回復の規則を書く（言語サーバーのコードアクションで雛形を加えられる）。

- 名前は `規則名_対象` であり、対象は参照した規則の名前、識別子の文字だけのリテラルの文字列、記号一文字のリテラルの名前（`rparen` など）である。表は `peg-hs help label` にある
- `--rule RULE` は、その規則の中だけに挿入する。何度でも指定できる
- 回復の規則を持つラベルの内側と、そこから呼ぶ規則には挿入しない
- 意味述語で文字を判定する規則の近くや左再帰の中は、安全でも検査が示せないので挿入しない。たとえば Lua の文法には一つも挿入されない

### parse

`parse` は、入力を解析して、開始規則の値（AST、既定）かロスレスな構文木（CST、`--format cst`）を表示する（[ADR 0036](docs/adr/0036-parse-command.md)）。
生成したパーサーを `PATH` の `ghc` でコンパイルし、実行ファイルを `$XDG_CACHE_HOME/peg-hs/parse` にキャッシュする。
GHC を待つのは、文法ごとに最初の一回だけである。

- AST の表示には、開始規則の型の `Show` のインスタンスが要る。ない場合は `--format cst` を使う
- `--entry RULE` は、`%entry` の規則で解析する
- 文法の Haskell の断片が利用者のモジュールを import する場合は、`--ghc-arg -isrc` のように探索のパスを渡す。cabal のプロジェクトのパッケージを使う場合は、`cabal exec -- peg-hs parse ...` で実行する
- 文字列の中の ASCII 以外の文字は、エスケープせずにそのまま表示する

### lsp

`lsp` は、標準入出力で Language Server Protocol を話す言語サーバーである（[ADR 0035](docs/adr/0035-language-server.md)）。
エディタが起動するもので、手で動かすことはない。設定は次の節にある。

## エディタ

`editors/` に、シンタックスハイライトの文法と VS Code の拡張機能を置いている（[ADR 0034](docs/adr/0034-syntax-highlighting.md)）。
Haskell の断片（verbatim ブロック、型、アクション、意味述語、引数）は、エディタの Haskell の文法がハイライトする。

言語サーバー `peg-hs lsp` は、編集のたびに `gen` と `lint` の誤りと警告を報告し、`fmt` で整形する。
semantic tokens、定義への移動、参照の検索、ホバー、文書の記号も提供する。
コードアクションとして、`label` と同じラベルを付ける「ラベルを付ける」と、回復の規則を持たないラベルに `%recover` と回復の規則の雛形を加える「`%recover` を加える」がある（[ADR 0054](docs/adr/0054-automatic-label-insertion.md)）。
雛形の値は型の穴 `{ _ }` なので、GHC が示す型を見て作者が書き入れる。

下の設定は、どれもまだエディタで手で確かめていない（**未確認**）。
確かめた結果は `docs/editors/` に記録し、記録したエディタからこの表示を外す（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）。

### VS Code（未確認）

`editors/vscode` は、TextMate の文法（`editors/textmate/hpeg.tmLanguage.json`）を含み、言語サーバーを起動する拡張機能である。
Marketplace にはまだ公開していないので、リポジトリから入れる。
依存を入れ、拡張機能のディレクトリにリンクを張り、VS Code を再起動する。
`peg-hs` が `PATH` にない場合は、設定 `peg-hs.path` で実行ファイルを指す。

```sh
(cd editors/vscode && npm ci)
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/peg-hs
```

### Neovim（未確認）

ハイライトには、`editors/tree-sitter-hpeg` の tree-sitter の文法を nvim-treesitter（main ブランチ）に登録する。
`User TSUpdate` の自動コマンドで文法の場所と問い合わせのディレクトリを渡し、Neovim で `:TSInstall hpeg` を実行する。
文法のビルドには tree-sitter の CLI が要る。
nvim-treesitter は、ハイライトを自動では有効にしないので、`FileType` の自動コマンドで `vim.treesitter.start()` を呼ぶ。

```lua
vim.filetype.add({ extension = { hpeg = 'hpeg' } })
vim.api.nvim_create_autocmd('User', { pattern = 'TSUpdate', callback = function()
  require('nvim-treesitter.parsers').hpeg = {
    install_info = { path = '/path/to/peg-hs/editors/tree-sitter-hpeg', queries = 'queries' },
  }
end })
vim.api.nvim_create_autocmd('FileType', { pattern = 'hpeg', callback = function() vim.treesitter.start() end })
```

nvim-treesitter の旧版（master ブランチ）では、`get_parser_configs()` に登録する。
文法は外部のスキャナー（`src/scanner.c`）を持つので、`files` に二つのファイルを書き、問い合わせをランタイムパスの `queries/hpeg/` に写す。

```lua
require('nvim-treesitter.parsers').get_parser_configs().hpeg = {
  install_info = { url = '/path/to/peg-hs/editors/tree-sitter-hpeg', files = { 'src/parser.c', 'src/scanner.c' } },
  filetype = 'hpeg',
}
```

言語サーバーは、Neovim 0.11 以降の `vim.lsp.config` で設定する。

```lua
vim.lsp.config('peg_hs', { cmd = { 'peg-hs', 'lsp' }, filetypes = { 'hpeg' }, root_markers = { '.git' } })
vim.lsp.enable('peg_hs')
```

### Helix（未確認）

`languages.toml` に言語、文法、言語サーバーを加え、`hx --grammar build` を実行する。
問い合わせは `runtime/queries/hpeg/` に写す。

```toml
[[language]]
name = "hpeg"
scope = "source.hpeg"
file-types = ["hpeg"]
comment-token = "#"
language-servers = ["peg-hs"]

[[grammar]]
name = "hpeg"
source = { path = "/path/to/peg-hs/editors/tree-sitter-hpeg" }

[language-server.hpeg-hs]
command = "peg-hs"
args = ["lsp"]
```

## 拡張子 .peg からの移行

文法ファイルの拡張子は、v0.1.0-rc1 までは `.peg` で、いまは `.hpeg` である。エディタの言語の名前も `hpeg` になった（[ADR 0050](docs/adr/0050-hpeg-extension.md)）。

1. 文法の名前を改める（`git mv Grammar.peg Grammar.hpeg`）
2. 新しいパスでモジュールを生成し直す。生成したモジュールは文法のパスを記録するためである
3. エディタの設定を改める。言語とファイルの種類の `peg` は `hpeg` に、tree-sitter の文法は `editors/tree-sitter-hpeg` に、問い合わせの置き場所は `queries/hpeg/` になる

## 既知の制限

- **配布**：実行ファイルは Linux（x86-64）と macOS（arm64）だけである。Windows では、ソースからビルドする。Hackage にはまだない（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）
- **GHC の版**：パッケージと生成したモジュールは GHC 9.10、9.12、9.14 に対応する。CI で確かめるのは ghcup の recommended の版（9.10）だけで、9.12 と 9.14 は v0.1.0-rc2 まで確かめた（[ADR 0057](docs/adr/0057-recommended-ghc-only.md)）。9.8 以前には対応しない（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）
- **文字コード**：文法と入力のファイルは UTF-8 でなければならない。ほかの文字コードは、変換してから渡す（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）
- **`peg-hs parse` と `%env`**：`parse` は `%env`（読み取り専用の解析環境）を使う文法を扱えない。環境の値を与える手段がないためである。そうした文法は、生成したモジュールを自分のプログラムから呼んで確かめる（[ADR 0036](docs/adr/0036-parse-command.md)）
- **`peg-hs parse` の GHC**：`parse` は `PATH` の `ghc` でパーサーをコンパイルするので、GHC 9.10、9.12、9.14 のどれかが要る（[ADR 0036](docs/adr/0036-parse-command.md)、[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）
- **型名の重なる規則**：`%syntax` の文法では規則ごとに型を作るので、`expr` と `Expr` のように同じ型名になる二つの規則は誤りになる。`peg-hs parse` は常に構文木も生成するので、`%syntax` を書いていない文法でも、そうした規則があれば扱えない（[ADR 0053](docs/adr/0053-type-names-of-rules-without-case.md)）
- **ラベルの安全性の検査は保守的である**：検査は、正しい入力を拒否しうるラベルを見逃さない代わりに、実際には安全なラベルも警告することがある。作者が確かめたラベルは `%safe` で警告を止める。記法自身の文法は 21 個の `%safe` を持つ（[ADR 0028](docs/adr/0028-label-safety-check.md)、[ADR 0038](docs/adr/0038-label-check-precision-and-strip-labels-entries.md)）
- **規則の雛形**：雛形の引数は呼び出し元の引数を使えるが、呼び出し元の束縛は使えない。束縛の値は値の引数で渡す。雛形は `%entry`、`%start`、`%recover` の規則にできない（[ADR 0031](docs/adr/0031-rule-templates.md)、[ADR 0055](docs/adr/0055-templates-and-parameterized-rules-in-stages.md)）
- **tree-sitter の文法**：アクションも要素もない選択肢（`S <- 'a' /`）を誤りにする。この選択肢は値を持たないので、`peg-hs gen` も必ず誤りにする。そのため、正しい文法を誤りと表示することはない（[ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)）
- **TextMate の文法**：正規表現の規則なので、文脈に依存する区別（`A(x)` の呼び出しと `A (x)` の並び）は近似である。言語サーバーの semantic tokens は正確に区別する（[ADR 0034](docs/adr/0034-syntax-highlighting.md)）
- **エディタの設定**：上の三つのエディタの設定は、まだ手で確かめていない（[ADR 0044](docs/adr/0044-release-v0-1-0.md)）。VS Code の拡張機能は Marketplace にない

## 文書

- [docs/syntax.md](docs/syntax.md)：`.hpeg` 記法の解説とサンプル
- [docs/specifications.md](docs/specifications.md)：製品の仕様
- [docs/adr/](docs/adr/)：設計の決定の記録（ADR）。仕様の各項目がどの決定によるかをたどれる
- [CONTRIBUTING.ja.md](CONTRIBUTING.ja.md)：開発の環境、テスト、生成物の再生成、ADR の書き方、コミット、リリースの手順
- 各パッケージの `CHANGELOG.md`：版ごとの変更

## ライセンス

[MIT](LICENSE)。
`conformance/data/` に取り込んだテストデータは、それぞれのディレクトリの LICENSE に従う。
