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
peg-hs Grammar.peg -o Grammar.hs
```

インストールせずに使う場合は、cabal を通して実行する。

```sh
cabal run peg-hs -- Grammar.peg -o Grammar.hs
```

生成されたモジュールは `peg-runtime` パッケージだけに依存し、開始規則の入口 `parse :: Text -> Either ParseError a` を公開する。

生成器は、正しい入力を拒否するかもしれないラベルを警告する（ADR 0028）。
`--Werror` を付けると警告で生成を止め、文法に `%safe label` を書くと、作者が確かめたラベルの警告を止められる。

## 開発

変更の進め方（ADR、テストを先に書くこと、コミットとリリース）は [CONTRIBUTING.ja.md](CONTRIBUTING.ja.md) に定める。

ツールチェーンは ghcup が recommended とする版を使う（GHC 9.10.3、cabal-install 3.16.1.0、HLS 2.14.0.0）。
コンパイラの版は `cabal.project` で固定する。
[mise](https://mise.jdx.dev/) を使う場合は、同梱の `mise.toml` が ghcup のバイナリをプロジェクトの PATH に加える。

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

クローン後、git の hook を有効化する。
コミット済みの ADR は変更不可であり、[adr-guard](https://github.com/tett23/adr-guard) が pre-commit hook と CI で変更を拒否する。

```sh
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

`.peg` 記法のパーサーは、記法自身の文法 `packages/peg-grammar/grammar/Peg.peg` から生成している（ADR 0027）。
記法に構文を加え、その構文を `Peg.peg` 自身で使う場合は、二回に分けて生成し直す。
まず、その構文を受理する規則を、その構文を使わずに加えて生成し直す。
次に、`Peg.peg` でその構文を使い、新しい生成器で生成し直す。

性能の退行は手元のベンチマークで検出する。
peg-runtime や peg-codegen に触れる変更では、変更前後で同一マシンのベンチマークを比較すること（ADR 0007）。

```sh
cabal bench peg-conformance
```

`%nomemo` で規則のメモ化を外す前に、メモ表の項目がどの規則に集まっているかを調べ、外す前後の最大の常駐メモリを別々のプロセスで比べる（ADR 0017）。

```sh
cd conformance && $(cabal list-bin peg-conformance:bench:peg-bench) --memo-report
```

CommonMark のテストは、結果を調べるためのオプションを受け付ける。
`--show N` は一つの例を表示し、`--report FILE` は節ごとの結果を書き出し、`--accept` は現在適合している例を記録する。

```sh
cd conformance && $(cabal list-bin peg-conformance:test:commonmark-conformance) --show 5
```

Lua のテストの正解は、参照実装の Lua 5.5.1 で作る。参照実装が要るのは、正解を作り直すときだけである。

```sh
conformance/lua/golden/regen.sh
```

## ライセンス

[MIT](LICENSE)
