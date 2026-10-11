# JSON の文法の %nomemo の効果（2026-10-11）

ADR 0017 の判断材料として、JSON の文法の字句の規則からメモ化を外した場合のメモリと時間を測った。
字句の規則 6 つ（`Ws`、`Unit`、`Hex`、`IntPart`、`Frac`、`Exp`）に `%nomemo` を付けると、80 万文字の文書で、最大の常駐メモリは 54% 減り、解析時間は 40% 短くなった。

この値は下記の環境での計測であり、他の環境の値とは比べられない。
退行の判定には使わない（ADR 0007）。

## 計測の環境

- 機械：Apple M1 Max、メモリ 64GB
- OS：macOS 27.0
- コンパイラ：GHC 9.10.3（`-O1`、cabal の既定）
- 入力：ベンチマークが生成する合成の JSON 文書（`conformance/bench-main/BenchMain.hs` の `syntheticJson`）

## メモ表の項目の内訳

7 万 7 千文字の文書を解析し終えた時点の、規則ごとのメモ表の項目数である（`--memo-report`）。
`Unit`（文字列の一文字）と `Ws`（空白）の二つで、全項目の約半数を占める。

| 規則 | 項目数 |
|---|---:|
| Unit | 35893 |
| Ws | 26002 |
| String | 9001 |
| Value | 9001 |
| IntPart | 7001 |
| Number | 7001 |
| Element | 5000 |
| MoreElement | 5000 |
| Member | 4000 |
| MoreMember | 4000 |
| Array | 2001 |
| Exp | 2000 |
| Frac | 2000 |
| Elements | 1001 |
| Members | 1000 |
| Object | 1000 |
| Json | 1 |

## 最大の常駐メモリ

変種ごとに別のプロセスで計測した（`--memory memoised N` と `--memory nomemo N`）。
最大の常駐メモリはプロセス全体での最大値なので、同じプロセスで続けて測ると後の計測が前の値に引きずられる。

| 入力 | すべてメモ化 | 字句の規則に %nomemo |
|---|---:|---:|
| 77,180 文字 | 15,398,984 バイト | 9,692,144 バイト |
| 801,683 文字 | 248,736,888 バイト | 114,358,344 バイト |

## 解析時間

criterion の計測（`cabal bench peg-conformance --benchmark-options='--time-limit 3 json'`）。

| 入力 | すべてメモ化 | 字句の規則に %nomemo |
|---|---:|---:|
| 801,683 文字 | 667.2 ms | 399.5 ms |

## 判断

字句の規則は、同じ位置で二度評価されることがほとんどないため、メモ化を外しても評価回数はほとんど増えず、メモ表への書き込みの分だけ時間とメモリが減った。
JSON の文法はこの計測の目的のために変種（`conformance/bench/JsonNomemo.peg`）を作ったもので、適合性テストに使う文法（`conformance/json/Json.peg`）は変えていない。
