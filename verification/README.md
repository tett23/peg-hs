# Lean による peg-hs の検証

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) に基づき、hpeg の構文解析、拒否条件、生成する Haskell の一部を Lean で検証する。
各定理の対象と公開入口までの未証明部分を次の表に示す。

| 不変条件 | Lean が検査する性質 | 実装との対応と残る課題 |
| --- | --- | --- |
| 1 | [Parsing.lean](Parsing.lean) は有限の式の実行と帰納的な判定関係の同値、深さ 256 の境界を証明する。[Lexical.lean](Lexical.lean) は空白とコメントのモデルを検査する。 | [check-core.sh](check-core.sh) は非回復時のランタイムの一部とモデルを比較し、[check-lexical.sh](check-lexical.sh) は実メタ文法の該当規則を照合する。任意のテキストに対する公開入口 `parseTops` とメタ文法全体の導出の同値は未証明。意味述語の Haskell 式は、モデルへ真偽値を渡す前に評価されると仮定する。 |
| 2 | [Guard.lean](Guard.lean) は二つのファイル名に制御文字がある場合の診断との同値を証明する。[Nullable.lean](Nullable.lean) は有限の正の式に対する空文字受理集合の最小不動点と停止性を証明する。[Reachable.lean](Reachable.lean) は有限の参照グラフにおける到達集合の正確性と停止性を証明する。[Signatures.lean](Signatures.lean) は規則の重複、参照の存在、引数個数を判定する。 | [check-guard.sh](check-guard.sh) は生成器の文字比較を翻訳して照合し、[check-nullable.sh](check-nullable.sh) と [check-reachable.sh](check-reachable.sh) は Haskell の該当処理を固定の定義と照合する。[ExtractSignatures.hs](ExtractSignatures.hs) は二つのメタ文法と `Templates.hpeg` の定義と参照を抽出し、Lean が三件とも検査する。空文字受理判定と署名抽出から公開入口の全診断までの同値、全段階の停止性は未証明。 |
| 3 | [Header.lean](Header.lean) はモジュール名と `module` 行の構文を検査する。[Literal.lean](Literal.lean) は文字列リテラルの引用とエスケープを検査する。 | [check-header.sh](check-header.sh) は対応する Haskell の定義を照合し、[check-literal.sh](check-literal.sh) は GHC の `Show` と 97 個の一文字および 9,409 個の二文字を比較する。生成モジュール全体の Haskell 構文導出は未証明。実際に再生成した二つのメタ文法は GHC に渡して検査する。 |

ソースの照合スクリプトと、そこで使う Haskell の構文の読み取り方は信頼する前提である。
[Audit.lean](Audit.lean) は八つの証明モジュールの定理ごとに依存する公理を列挙し、Lean 標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理を使うと失敗する。

## 実行方法

リポジトリのルートで次のコマンドを実行する。
GHC と Cabal はプロジェクト指定の版を使う。
elan が [lean-toolchain](lean-toolchain) の Lean を選ぶ。

```sh
cabal build exe:peg-hs
verification/check.sh
```

対応テストでは、深さ 256 の前後で `parseTops` と Lean の結果を比較する。
空ファイル、末尾の余分な文字、未定義参照については実際の診断を確認する。
実ファイルから抽出した規則の署名は三件とも Lean で証明し、未定義参照を加えた負例の証明は Lean が拒否することを確認する。
二つのメタ文法は実ファイルから再生成し、出力を GHC で検査する。
区切りが閉じたアクションに不完全な Haskell 式を入れたケースでは、GHC が構文エラーを返すことを確認する。
