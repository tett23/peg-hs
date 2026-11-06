# 型を推論し生成する JSON の文法の費用と、言語サーバーの編集の時間（2026-11-06）

[ADR 0075](../adr/0075-generated-types-for-rules-without-actions.md) の実装の後に、JSON の文法の三つの変種で、時間と最大の常駐メモリを測った。
型注釈もアクションも書かずに型の推論と生成に任せた文法（`JsonGenerated.hpeg`）は、型注釈とアクションを書いた文法に比べて、時間が約 0.97 倍、最大の常駐メモリが約 1.18 倍だった。
ただし、二つの文法は同じ値を作らない（後述）。
あわせて、言語サーバーの 1 回の編集の時間を実装の前と後で測り、分類の計算を加えても 16 ms の目安に届いていることを確かめた。

この値は下記の環境での計測であり、他の環境の値とは比べられない。
退行の判定には使わない（[ADR 0007](../adr/0007-performance-discipline.md)）。

## 計測の環境

- 機械：Apple M1 Max、メモリ 64GB
- OS：macOS 27.0
- コンパイラ：GHC 9.10.3（`-O1`、cabal の既定）
- 入力：ベンチマークが生成する合成の JSON 文書（`conformance/bench-main/BenchMain.hs` の `syntheticJson`）、801,683 文字
- 文法：`conformance/json/Json.hpeg`（型注釈とアクション）、`conformance/bench/JsonUntyped.hpeg`（`%syntax`、型注釈とアクションなし、構文木）、`conformance/bench/JsonGenerated.hpeg`（`%syntax` なし、型注釈とアクションなし、型の推論と生成）
- 言語サーバーの文法：`conformance/bench/Memo.hpeg`（712 行）と、Golem の文法（`modules/golem-parser/grammar/Golem.hpeg`、749 行、Golem のコミット a5e7bae3）
- 計測の間、同じ機械で別の作業が動いていた。ロードアベレージは、JSON の計測の始めに 9.8、言語サーバーの計測の間に 3 から 5 だった

## 解析時間

criterion の計測（`peg-bench --time-limit 15 json`、`conformance` のディレクトリで実行）。
括弧の中は criterion の時間の信頼区間である。

| 文法と入口 | 時間 | 型付きの文法との比 |
|---|---:|---:|
| `Json.hpeg`、型注釈とアクション、`parse` | 639.6 ms（609.8 ms から 666.9 ms） | 1.00 |
| `JsonUntyped.hpeg`、構文木、`parseSyntax` | 765.1 ms（650.4 ms から 894.2 ms） | 1.20 |
| `JsonGenerated.hpeg`、型の推論と生成、`parse` | 620.2 ms（583.3 ms から 663.2 ms） | 0.97 |

`JsonGenerated.hpeg` と `Json.hpeg` の時間の差は、二つの信頼区間の重なりに収まる。

二つの文法は同じ値を作らない。
`Json.hpeg` のアクションは、文字列の要素を符号単位の整数にし、`T.pack` で `Text` に組み立てる。
`JsonGenerated.hpeg` は、文字列を `Unit` の値のリストのまま返し、`Text` に組み立てない。
計測はどちらも値の全体を評価するが（`size` と `generatedSize`）、`JsonGenerated.hpeg` の値を `Json.hpeg` の値の型に写す処理（`conformance/test/JsonMain.hs` の `fromGenerated`）は含まない。
写す処理を含めた時間は測っていない。

`JsonUntyped.hpeg` の時間は、[docs/benchmarks/2026-11-06-json-untyped-syntax.md](2026-11-06-json-untyped-syntax.md) の値（1,032 ms）より短く、信頼区間も広い。
この差の原因は確かめていない。

## 最大の常駐メモリ

変種ごとに別のプロセスで計測した（`peg-bench --memory VARIANT 10000`、VARIANT は `typed`、`untyped-tree`、`generated`）。

| 文法と入口 | 最大の常駐メモリ | 型付きの文法との比 |
|---|---:|---:|
| `Json.hpeg`、型注釈とアクション、`parse` | 156,517,032 バイト | 1.00 |
| `JsonUntyped.hpeg`、構文木、`parseSyntax` | 191,893,008 バイト | 1.23 |
| `JsonGenerated.hpeg`、型の推論と生成、`parse` | 184,708,016 バイト | 1.18 |

生成した型の値は、文字列を `Unit` のリストとして持ち、`Value5`、`Array1`、`Elements` のような構築子を重ねるので、`Text` と `[Value]` を直接持つ型付きの値より大きい。

`Json.hpeg` と `JsonUntyped.hpeg` の値は、[docs/benchmarks/2026-11-06-json-untyped-syntax.md](2026-11-06-json-untyped-syntax.md) の値（264,740,432 バイトと 296,625,104 バイト）より小さい。
その計測の後に入った変更のどれが差を生んだかは確かめていない。
この記録の三つの値は、同じ版の同じ実行ファイルで続けて測った。

## 言語サーバーの 1 回の編集

criterion の計測（`peg-bench --match prefix lsp +RTS -A64m -RTS`、`conformance` のディレクトリで実行）。
Golem の文法は `PEG_BENCH_LSP_GRAMMAR` で与えた。
「前」は [ADR 0075](../adr/0075-generated-types-for-rules-without-actions.md) の文書だけを加えたコミット（ade2e4c）、「後」は実装の後である。
編集の作りは [docs/benchmarks/2026-11-06-lsp-incremental.md](2026-11-06-lsp-incremental.md) と同じで、規則の定義の行の前に `#` だけの行を挿入する。
「範囲」は `didChange` が挿入の位置と文字列だけを持つ同期である。

Memo.hpeg（712 行）：

| 段 | 場所 | 前 | 後 |
|---|---|---:|---:|
| 編集の診断（解読、検査、符号化、範囲） | 先頭 | 2.323 ms | 2.412 ms |
| 編集の診断（解読、検査、符号化、範囲） | 中ほど | 2.385 ms | 2.437 ms |
| 編集の診断（解読、検査、符号化、範囲） | 末尾 | 2.421 ms | 2.526 ms |
| 編集の診断と semantic tokens（範囲） | 先頭 | 9.766 ms | 9.848 ms |
| 編集の診断と semantic tokens（範囲） | 中ほど | 9.895 ms | 9.826 ms |
| 編集の診断と semantic tokens（範囲） | 末尾 | 9.740 ms | 10.00 ms |
| 静的検査（`check`） | | 0.901 ms | 1.076 ms |
| lint | | 0.471 ms | 0.482 ms |

Golem の文法（749 行）：

| 段 | 場所 | 前 | 後 |
|---|---|---:|---:|
| 編集の診断（解読、検査、符号化、範囲） | 先頭 | 3.719 ms | 3.826 ms |
| 編集の診断（解読、検査、符号化、範囲） | 中ほど | 3.779 ms | 3.892 ms |
| 編集の診断（解読、検査、符号化、範囲） | 末尾 | 3.925 ms | 3.901 ms |
| 編集の診断と semantic tokens（範囲） | 先頭 | 10.68 ms | 10.69 ms |
| 編集の診断と semantic tokens（範囲） | 中ほど | 10.77 ms | 10.71 ms |
| 編集の診断と semantic tokens（範囲） | 末尾 | 10.65 ms | 10.83 ms |
| 静的検査（`check`） | | 0.635 ms | 0.804 ms |
| lint | | 1.611 ms | 1.625 ms |

静的検査は、分類の計算の分だけ、Memo.hpeg で約 0.18 ms、Golem の文法で約 0.17 ms 長くなった。
編集の診断の差は 0.1 ms ほどで、計測の揺れと区別できない。
二つの文法は、どちらも型注釈とアクションのない値を持つ規則をほとんど持たないので、この計測は分類で型を生成する規則の多い文法の時間を表さない。

ホバーとコードアクションのための分類と構築子の名前の編集は、要求されたときに初めて計算するので、編集の診断の時間に入らない。
その時間は測っていない。

| 目安（16 ms 以内） | Memo.hpeg | Golem.hpeg |
|---|---|---|
| 1 回の編集の診断（範囲の同期） | 2.41 ms から 2.53 ms | 3.83 ms から 3.90 ms |
| 編集の後の semantic tokens の要求（概要を含む、診断との合計） | 9.83 ms から 10.00 ms | 10.69 ms から 10.83 ms |

どちらの目安にも、三つの場所のすべてで届いた。
[docs/benchmarks/2026-11-06-lsp-incremental.md](2026-11-06-lsp-incremental.md) の 51 回の編集のセッション（`peg-hs lsp` のプロセスの CPU 時間）は、この記録では測っていない。

## 判断

型の推論と生成に任せた JSON の文法は、この計測では型注釈とアクションを書いた文法と同じほどの時間で、最大の常駐メモリが約 1.18 倍だった。
ただし、値を利用者の型に写す処理を含めていないので、生成した型の値をそのまま使う場合の費用である。
[ADR 0075](../adr/0075-generated-types-for-rules-without-actions.md) の「速さが要る規則は型注釈とアクションを手で書く」という判断を変える結果ではない。
言語サーバーの編集の時間は、分類を加えても目安の 16 ms に余裕を持って収まった。
