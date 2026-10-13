# peg-grammar-test を分けた後の CI の時間（2026-10-13）

[ADR 0042](../adr/0042-shard-peg-grammar-test.md) のテスト設計に従い、peg-grammar-test の重いプロパティテストを分け、スイートを三つのジョブ（`test-grammar-1` から `test-grammar-3`）で動かすようにした後の、GitHub Actions の段ごとの時間を計測した。
比べる相手は、[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後の計測（[2026-10-13-ci-split-tests.md](2026-10-13-ci-split-tests.md)）である。

すべてのキャッシュが当たる実行で、ワークフロー全体は 2 分 33 秒から 2 分 4 秒になった。
peg-grammar-test を動かすジョブは、148 秒の一つから、85 秒、52 秒、98 秒の三つになった。
[ADR 0042](../adr/0042-shard-peg-grammar-test.md) の二つの目安（各シャードのジョブが test-conformance のジョブより短く終わること、ワークフロー全体が 2 分 33 秒より短くなること）は、どちらも満たした。

ワークフローの時間を決めるジョブは、test-grammar から package（121 秒）と test-conformance（116 秒）に移った。
[ADR 0042](../adr/0042-shard-peg-grammar-test.md) のトレードオフに書いた頭打ちである。
三つのシャードの間の偏りは大きく、テストの段は 46 秒、16 秒、55 秒だった。

この値は GitHub のホストするランナー（`ubuntu-latest`、x86-64、4 コア）での一回の計測であり、ばらつきがある。
同じ test-conformance のテストの段は、前回の計測では 54 秒、今回は 77 秒だった。
退行の判定には使わない（[ADR 0007](../adr/0007-performance-discipline.md)）。

## 計測した実行

| 列 | 実行 | コミット | キャッシュ |
|---|---|---|---|
| [ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後 | run 38333158193、二回目 | be54d87 | すべて |
| [ADR 0042](../adr/0042-shard-peg-grammar-test.md) の後 | run 38343187943 | e3c0ab5（main） | すべて |

e3c0ab5 は、[ADR 0042](../adr/0042-shard-peg-grammar-test.md) のマージ（2ea7312）の後に、adr-guard を v0.8.0 に上げた変更（pull request #6）をマージしたコミットである。
変更は ADR の検査のワークフローだけなので、テストのジョブの比較には影響しない。
[ADR 0042](../adr/0042-shard-peg-grammar-test.md) のマージの直後の実行（run 38342790561）は、テストのコードを変えたためにビルドの成果物のキャッシュが部分的にしか当たらなかったので、計測に使わなかった。

## ジョブの時間

| ジョブ | [ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後 | [ADR 0042](../adr/0042-shard-peg-grammar-test.md) の後 |
|---|---:|---:|
| haskell | 41 秒 | 47 秒 |
| test-grammar | 148 秒 | （三つに分けた） |
| test-grammar-1 | | 85 秒 |
| test-grammar-2 | | 52 秒 |
| test-grammar-3 | | 98 秒 |
| test-conformance | 97 秒 | 116 秒 |
| test-packages | 56 秒 | 68 秒 |
| package | 118 秒 | 121 秒 |
| editors | 9 秒 | 9 秒 |
| ワークフロー全体 | 2 分 33 秒 | 2 分 4 秒 |

各ジョブのテストの前の準備（キャッシュの復元、GHC の導入、依存の解決）は、30 秒から 45 秒だった。

## peg-grammar-test の時間

| 部分 | テストの数 | スイートの報告した時間 | テストの段 |
|---|---:|---:|---:|
| 分ける前（[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後） | 279 | 105 秒 | 106 秒 |
| `--shard 1/3` | 100 | 44 秒 | 46 秒 |
| `--shard 2/3` | 99 | 14 秒 | 16 秒 |
| `--shard 3/3` | 99 | 53 秒 | 55 秒 |

プロパティテストを四つずつに分けたので、テストの数は 279 から 298 になった。
三つの部分のテストの一覧を合わせると、`--shard` を付けない一覧と一致することは、手元で確かめた。

テストの数はそろっているが、時間はそろっていない。
順番の余りによる分け方は、テストの時間を見ないためである（[ADR 0042](../adr/0042-shard-peg-grammar-test.md) のトレードオフ）。
最も長い部分（53 秒）は、test-conformance のテストの段（77 秒）より短いので、ワークフローの時間には効いていない。

## ADR のテスト設計の結果

| 項目 | 結果 |
|---|---|
| 三つの部分のテストの一覧を合わせると、全体の一覧と一致すること | 一致した（298 件） |
| 各シャードのジョブが test-conformance のジョブより短いこと | 85 秒、52 秒、98 秒で、どれも test-conformance の 116 秒より短い |
| ワークフロー全体が 2 分 33 秒より短いこと | 2 分 4 秒 |

## 残った課題

ワークフローの時間は、package のジョブ（Haddock 43 秒、ソースのアーカイブからのビルド 41 秒）と test-conformance のジョブで決まっている。
これ以上縮めるには、package のジョブの二つの段を別のジョブに分けるか、test-conformance のスイートを分ける必要がある。
三つのシャードの偏りを直しても、ワークフローは縮まない。
