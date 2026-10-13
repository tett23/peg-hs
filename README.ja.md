# peg-hs

PEG（Parsing Expression Grammar）の定義から Haskell のパーサーを生成するツールチェーン。

[English README](README.md)

- 標準 PEG の全構文と、直接と間接の左再帰を受理する（bounded left recursion, Medeiros et al. 2014）
- happy / alex 方式のスタンドアロン生成器。`.peg` から決定的に `.hs` を生成する（同一入力からバイト単位で同一の出力）
- 各規則が結果型とセマンティックアクションを持ち、生成されたパーサーは利用者の AST を直接返す
- 字下げに依存する構文や前方参照を書くための文脈依存の拡張（意味述語、引数付き規則、読み取り専用の解析環境、桁の参照）。パックラットのメモ化と左再帰の正しさを保つように設計している
- アクションの型の誤りは、`.peg` ファイルの行と桁で報告される
- rust-analyzer に倣った、空白とコメントを失わない構文木（`%syntax`）。lint や formatter のため
- ラベル付きの失敗による構文エラーからの回復（`e ^label` と `%recover`）。回復するモードは、誤りのノードを含むロスレスな構文木を必ず返す。LSP のため

**ステータス：公開前（0.1）。** 生成器、実行時ライブラリ、適合性テストは実装済み。Hackage には未公開。

- JSON（[JSONTestSuite](https://github.com/nst/JSONTestSuite)）：受理すべき 95 件と拒否すべき 188 件のすべてに合格
- CommonMark 0.31.2：仕様の例 652 件すべてに適合
- Lua 5.5（Lua 5.5.1 の公式のテストスイート）：マニュアルの構文を間接の左再帰のまま書いた文法で、34 ファイルすべてを受理。優先順位、結合性、拒否は、参照実装から作った正解と一致
- TOML 1.1.0（[toml-test](https://github.com/toml-lang/toml-test) v2.2.0）：受理すべき 214 件のすべてで期待する JSON と一致し、拒否すべき 467 件をすべて拒否。回復するモードでは全件でロスレスな構文木を返す

仕様は [docs/specifications.md](docs/specifications.md)、`.peg` 記法の解説とサンプルは [docs/syntax.md](docs/syntax.md)、設計決定は [docs/adr/](docs/adr/) を参照。

## 使い方

### CLI のビルド

コマンドラインのツール `peg-hs` は、[開発](#開発)の節のツールチェーン（GHC 9.10.3 と cabal-install 3.16.1.0）で、リポジトリからビルドする。

```sh
git clone https://github.com/tett23/peg-hs.git
cd peg-hs
cabal build exe:peg-hs
```

ビルドした実行ファイルのパスは `cabal list-bin exe:peg-hs` で表示できる。
`PATH` の通ったディレクトリ（たとえば `~/.local/bin`）にインストールするには、次のようにする。

```sh
cabal install exe:peg-hs --installdir="$HOME/.local/bin" --install-method=copy --overwrite-policy=always
```

### パーサーの生成

```sh
peg-hs gen Grammar.peg -o Grammar.hs
```

インストールせずに使う場合は、cabal を通して実行する。

```sh
cabal run peg-hs -- gen Grammar.peg -o Grammar.hs
```

生成されたモジュールは `peg-runtime` パッケージだけに依存し、開始規則の入口 `parse :: Text -> Either ParseError a` を公開する。

生成器は、正しい入力を拒否するかもしれないラベルを警告する（[ADR 0028](docs/adr/0028-label-safety-check.md)）。
`--Werror` を付けると警告で生成を止め、文法に `%safe label` を書くと、作者が確かめたラベルの警告を止められる。

### 入力を解析して確かめる

```sh
peg-hs parse Grammar.peg input.txt [--format ast|cst|all] [--entry RULE] [--ghc-arg ARG]...
```

`parse` は、入力を解析して、開始規則の値（AST、既定）かロスレスな構文木（CST）を表示する（[ADR 0036](docs/adr/0036-parse-command.md)）。
生成したパーサーを `PATH` の `ghc`（GHC 9.10）でコンパイルし、実行ファイルを `$XDG_CACHE_HOME/peg-hs/parse` にキャッシュする。GHC を待つのは、文法ごとに最初の一回だけである。
AST の表示には、開始規則の型の `Show` のインスタンスが要る。
文法の Haskell の断片が利用者のモジュールを import する場合は、`--ghc-arg -isrc` のように探索のパスを渡す。cabal のプロジェクトのパッケージを使う場合は、`cabal exec -- peg-hs parse ...` で実行する。

### 文法の整形

```sh
peg-hs fmt [FILE...]
peg-hs fmt --check [FILE...]
```

`fmt` は、文法を一つに固定した流儀で整形して上書きする。オプションはない（[ADR 0032](docs/adr/0032-grammar-formatter.md)）。
ファイルを指定しなければ、現在のディレクトリから再帰的にたどった `.peg` ファイルをすべて整形する。名前が `.` で始まるディレクトリと `dist-newstyle` はたどらない。
`--check` はファイルを書き換えず、整形されていないファイルの名前を表示し、一つでもあれば失敗する。

### 文法の lint

```sh
peg-hs lint [FILE...]
```

`lint` は、静的検査を通った文法のうち、確実に誤りである書き方を警告する（[ADR 0033](docs/adr/0033-grammar-linter.md)）。
対象は、試されない選択肢と成功しない選択肢、先読みの中の効果のないラベル、使われない束縛である。
規則は固定で、警告を抑制する手段はない。どの警告も文法を直せば消え、警告が一つでもあればコマンドは失敗する。
ファイルを指定しない場合の対象は `fmt` と同じである。

### エディタ

`editors/` に、シンタックスハイライトのための文法を置いている（[ADR 0034](docs/adr/0034-syntax-highlighting.md)）。
Haskell の断片（verbatim ブロック、型、アクション、意味述語、引数）は、エディタの Haskell の文法がハイライトする。

- **VS Code**：`editors/vscode` は、TextMate の文法（`editors/textmate/peg.tmLanguage.json`）を含み、言語サーバーを起動する拡張機能である。依存を入れ、拡張機能のディレクトリにリンクを張り、VS Code を再起動する。`peg-hs` の実行ファイルは設定 `peg-hs.path` で指定する

  ```sh
  (cd editors/vscode && npm ci)
  ln -s "$PWD/editors/vscode" ~/.vscode/extensions/peg-hs
  ```

- **Neovim**（nvim-treesitter）：`editors/tree-sitter-peg` の tree-sitter の文法を登録し、問い合わせをランタイムパスの `queries/peg/` に写す

  ```lua
  vim.filetype.add({ extension = { peg = 'peg' } })
  require('nvim-treesitter.parsers').get_parser_configs().peg = {
    install_info = { url = '/path/to/peg-hs/editors/tree-sitter-peg', files = { 'src/parser.c' } },
    filetype = 'peg',
  }
  ```

- **Helix**：`languages.toml` に言語と文法を加え、`hx --grammar build` を実行し、問い合わせを `runtime/queries/peg/` に写す

  ```toml
  [[language]]
  name = "peg"
  scope = "source.peg"
  file-types = ["peg"]
  comment-token = "#"

  [[grammar]]
  name = "peg"
  source = { path = "/path/to/peg-hs/editors/tree-sitter-peg" }
  ```

### 言語サーバー

`peg-hs lsp` は、標準入出力で動く言語サーバーである（[ADR 0035](docs/adr/0035-language-server.md)）。
編集のたびに `gen` と `lint` の誤りと警告を報告し、`fmt` で整形する。semantic tokens、定義への移動、参照の検索、ホバー、文書の記号も提供する。
上の VS Code の拡張機能のほか、Neovim では次のように設定する。

```lua
vim.lsp.config('peg_hs', { cmd = { 'peg-hs', 'lsp' }, filetypes = { 'peg' }, root_markers = { '.git' } })
vim.lsp.enable('peg_hs')
```

Helix では `languages.toml` に書く。

```toml
[language-server.peg-hs]
command = "peg-hs"
args = ["lsp"]

[[language]]
name = "peg"
language-servers = ["peg-hs"]
```

## 開発

変更の進め方（ADR、テストを先に書くこと、コミットとリリース）は [CONTRIBUTING.ja.md](CONTRIBUTING.ja.md) に定める。

ツールチェーンは ghcup が recommended とする版を使う（GHC 9.10.3、cabal-install 3.16.1.0、HLS 2.14.0.0）。
コンパイラの版は `cabal.project` で固定する。
[mise](https://mise.jdx.dev/) を使う場合は、同梱の `mise.toml` が ghcup のバイナリをプロジェクトの PATH に加える。

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

クローン後、[adr-guard](https://github.com/tett23/adr-guard) を導入し、git の hook を有効化する。
コミット済みの ADR と計測の記録（`docs/benchmarks/`）は変更不可であり、adr-guard が pre-commit hook と CI で変更を拒否する。ADR のステータスの行と、ADR の参照に付けるリンクの変更だけは許される。
ADR は、行頭が `ステータス:` のステータスの行をちょうど一つ持つ（[ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md)）。

```sh
cargo install --git https://github.com/tett23/adr-guard --tag v0.8.1
git config core.hooksPath .githooks
```

すべてのテストを実行する。

```sh
cabal test all
```

生成したモジュールはリポジトリにコミットしており、テストが生成器の現在の出力との一致を検査する。
生成器か文法を変えたら、次のコマンドで生成し直す。

```sh
scripts/regen-fixtures.sh
```

`.peg` 記法のパーサーは、記法自身の文法 `packages/peg-grammar/grammar/Peg.peg` から生成している（[ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)）。
記法に構文を加え、その構文を `Peg.peg` 自身で使う場合は、二回に分けて生成し直す。
まず、その構文を受理する規則を、その構文を使わずに加えて生成し直す。
次に、`Peg.peg` でその構文を使い、新しい生成器で生成し直す。

性能の退行は手元のベンチマークで検出する。
peg-runtime や peg-codegen に触れる変更では、変更前後で同一マシンのベンチマークを比較すること（[ADR 0007](docs/adr/0007-performance-discipline.md)）。

```sh
cabal bench peg-conformance
```

`%nomemo` で規則のメモ化を外す前に、メモ表の項目がどの規則に集まっているかを調べ、外す前後の最大の常駐メモリを別々のプロセスで比べる（[ADR 0017](docs/adr/0017-nomemo-implementation.md)）。

```sh
cd conformance && $(cabal list-bin peg-conformance:bench:peg-bench) --memo-report
```

CommonMark のテストは、結果を調べるためのオプションを受け付ける。
`--show N` は一つの例を表示し、`--report FILE` は節ごとの結果を書き出し、`--accept` は現在適合している例を記録する。

```sh
cd conformance && $(cabal list-bin peg-conformance:test:commonmark-conformance) --show 5
```

エディタの文法は、Node と tree-sitter の CLI でテストする。
記法を変えたら、`editors/` の文法も直す。テストは、エディタの文法の字句の範囲を、自己記述の文法の範囲と比べる。後者は、`cabal test peg-grammar` に `--accept` を付けると `editors/test/ranges.txt` に書き出される。

```sh
cd editors && npm ci && npm test
```

Lua のテストの正解は、参照実装の Lua 5.5.1 で作る。参照実装が要るのは、正解を作り直すときだけである。

```sh
conformance/lua/golden/regen.sh
```

## ライセンス

[MIT](LICENSE)
