# 言語サーバーの検査の段ごとの時間、速くする前（2026-11-06）

[ADR 0070](../adr/0070-faster-checks-in-the-language-server.md) の実装の前に、言語サーバーが編集のたびに行う検査を段ごとに測った。
1 回の編集（`didChange` の受信から診断の送信まで）は、リポジトリの文法で 36.7 ms、Golem の文法で 47.8 ms かかった。
どちらの文法でも、時間の大半は二つの構文解析が占める。
`.hpeg` の構文解析（`parseTops`）が約 25 ms、`didChange` の JSON の解読が約 12 ms で、静的検査、ラベルの安全性の検査、lint を合わせても 2 ms に満たない。

この値は下記の環境での計測であり、他の環境の値とは比べられない。
退行の判定には使わない（[ADR 0007](../adr/0007-performance-discipline.md)）。

## 計測の環境

- 機械：Apple M1 Max
- OS：macOS 27.0
- コンパイラ：GHC 9.10.3（`-O1`、cabal の既定）
- 文法：Golem の文法の形を写した `conformance/bench/Memo.hpeg`（712 行）。参考として、Golem の文法（`modules/golem-parser/grammar/Golem.hpeg`、723 行）も測った
- 計測の間、同じ機械で別の作業（GHC のビルドとテスト）が動いており、ロードアベレージは 4.5 から 9 だった

`Memo.hpeg` は、Golem の文法と同じく、`%syntax`、`%token`、`%inline`、字下げの深さを引数に取る規則、ラベルと `%recover`、検査が安全を示せないラベルの `%safe` を持つ。
違いは、型注釈とアクションを書かない（[ADR 0068](../adr/0068-untyped-rules-in-syntax-grammars.md)）ことである。
Golem の文法はどの規則にも `:: ()` と `{ () }` を書くので、lint の情報（severity が Hint の診断）が多く出る。

## 段ごとの時間

criterion の計測（`peg-bench --match prefix lsp`、`conformance` のディレクトリで実行）。
Golem の文法は環境変数 `PEG_BENCH_LSP_GRAMMAR` でパスを与えて測った。

| 段 | Memo.hpeg | Golem.hpeg |
|---|---:|---:|
| 概要（回復する構文解析と構文木） | 56.43 ms | 59.49 ms |
| 構文解析（`parseTops`） | 25.29 ms | 25.38 ms |
| 構文解析と雛形の展開 | 25.57 ms | 26.18 ms |
| 静的検査（`check`） | 0.863 ms | 0.590 ms |
| ラベルの安全性の検査 | 0.034 ms | 0.028 ms |
| lint | 0.435 ms | 1.237 ms |
| semantic tokens（概要は計算済み） | 7.197 ms | 6.701 ms |
| semantic tokens（概要の計算を含む） | 61.20 ms | 58.54 ms |
| コードアクションのラベルと回復の規則 | 180.7 ms | 168.3 ms |
| 診断（`diagnose`） | 25.88 ms | 26.02 ms |
| `didChange` の JSON の解読 | 12.36 ms | 11.95 ms |
| 1 回の編集（解読、検査、診断の符号化） | 36.74 ms | 47.83 ms |
| 1 回の編集（解読した通知から） | 25.85 ms | 33.93 ms |
| 1 回の編集と semantic tokens | 86.21 ms | 85.72 ms |

ラベルの安全性の検査が短いのは、二つの文法のラベルがどれも `%safe` で、検査を省くからである。
Golem の文法では、診断の計算（26.02 ms）と解読した通知からの編集（33.93 ms）の差の約 8 ms が、診断を JSON にする部分にかかっている。
Memo.hpeg ではこの差がない。
Golem の文法には lint の情報が 325 個あり、言語サーバーは診断の一つずつについて、文書の行の連結リストを先頭からたどって範囲を計算する。
差の原因はこのたどり方にあると考えられるが、この計測では確かめていない。

コードアクションの計算（`peg-hs label` と同じラベルの候補と、回復の規則の提案）は 170 ms 前後と最も長い。
ただし、言語サーバーはこれをコードアクションの要求のときにだけ計算し、編集のたびには計算しない。

## 51 回の編集のセッション

`peg-bench --lsp-session GRAMMAR FILE` で、`initialize`、文法の `didOpen`、全文を送る 50 回の `didChange`（版ごとに末尾にコメントの行を一つ足す）、`shutdown`、`exit` を並べた入力を作った。
これを `peg-hs lsp` の標準入力に与え、`/usr/bin/time -p` で 5 回測った。

| 文法 | 5 回の時間（秒） | 1 回の編集あたり |
|---|---|---:|
| Memo.hpeg | 2.42、1.70、1.73、1.71、1.73 | 約 34 ms |
| Golem.hpeg | 2.17、2.18、2.20、2.22、2.19 | 約 43 ms |

1 回の編集あたりの時間は、最初の 1 回を除いた中央値を 51 で割った値である。
Golem の文法の値は、[ADR 0070](../adr/0070-faster-checks-in-the-language-server.md) を書いたときの 2.33 秒（約 46 ms）に近い。

## 時間の内訳

ベンチマークとは別に、`.hpeg` の構文解析を `+RTS -s` で走らせると、時間の約 6 割がガベージコレクションだった。
構文解析は 1 回に約 40 MB を割り当て、メモ表が生きているあいだに世代 1 の収集が繰り返される。
`+RTS -A64m` で割り当て領域を広げると、構文解析の時間はほぼ半分になった。

目安の 16 ms（[ADR 0070](../adr/0070-faster-checks-in-the-language-server.md) の 20 ms を、所有者が実装の前に改めた値）に対して、構文解析と JSON の解読だけで 37 ms ある。
検査（静的検査、ラベル、lint）を速くしても、目安には届かない。
