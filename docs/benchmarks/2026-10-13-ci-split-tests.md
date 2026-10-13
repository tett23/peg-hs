# テストのジョブを分けた後の CI の時間（2026-10-13）

[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) のテスト設計に従い、テストスイートを三つのジョブに分け、各ジョブの中でスイートを一つずつ動かすようにした後の、GitHub Actions の段ごとの時間を計測した。
比べる相手は、[ADR 0039](../adr/0039-faster-ci.md) の実装の後の計測（[2026-10-13-ci-duration.md](2026-10-13-ci-duration.md) の「すべて」の列）である。

すべてのキャッシュが当たる実行で、ワークフロー全体は約 3 分 45 秒から 2 分 33 秒になった。
テストのスイートは、コアを取り合わなくなったことで大きく縮んだ。
適合性のスイートは 2 倍から 5 倍速くなり、peg-grammar-test は 150 秒から 105 秒になった。

ただし、[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の三つの目安は、どれも満たさなかった。
ワークフロー全体は目安の 2 分 30 秒を 3 秒超え、peg-grammar-test は目安の 100 秒を 5 秒超えた。
三つのテストのジョブの時間は、最も長い test-grammar（148 秒）と最も短い test-packages（56 秒）の差が、最も長いジョブの半分（74 秒）を超えた。
ワークフローの時間を決めているのは、peg-grammar-test だけを動かす test-grammar のジョブである。

この値は GitHub のホストするランナー（`ubuntu-latest`、x86-64、4 コア）での一回の計測であり、ばらつきがある。
退行の判定には使わない（[ADR 0007](../adr/0007-performance-discipline.md)）。

## 計測した実行

| 列 | 実行 | コミット | キャッシュ |
|---|---|---|---|
| [ADR 0039](../adr/0039-faster-ci.md) の後 | run 38330942328、二回目 | 60b9472 | すべて |
| [ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後 | run 38333158193、二回目（再実行） | be54d87（main） | すべて |

run 38333158193 の一回目は、main のキャッシュが保存される数秒前に始まり、GHC のキャッシュが外れたので取り消した。
再実行では、すべてのジョブが GHC、依存のストア、ビルドの成果物のキャッシュを復元した。

## ジョブの時間

| ジョブ | [ADR 0039](../adr/0039-faster-ci.md) の後 | [ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後 |
|---|---:|---:|
| haskell | 220 秒（テストを含む） | 41 秒（ビルドと検査だけ） |
| test-grammar | | 148 秒 |
| test-conformance | | 97 秒 |
| test-packages | | 56 秒 |
| package | 92 秒 | 118 秒 |
| editors | 13 秒 | 9 秒 |
| ワークフロー全体 | 約 3 分 45 秒 | 2 分 33 秒 |

テストのジョブの段の内訳は次のとおりである。

| 段 | test-grammar | test-conformance | test-packages |
|---|---:|---:|---:|
| キャッシュの復元と GHC の導入 | 17 秒 | 17 秒 | 13 秒 |
| 依存の解決 | 17 秒 | 19 秒 | 17 秒 |
| ビルド | 2 秒 | 2 秒 | 2 秒 |
| テスト | 106 秒 | 54 秒 | 20 秒 |

各ジョブに、テストの前の準備（キャッシュの復元、GHC の導入、依存の解決）が約 30 秒かかる。
[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の見込みのとおりである。

## テストスイートの時間

| スイート | ジョブ | [ADR 0039](../adr/0039-faster-ci.md) の後（同時に 10 個） | [ADR 0041](../adr/0041-split-test-jobs-and-cores.md) の後（ジョブの中で一つずつ） |
|---|---|---:|---:|
| peg-grammar-test | test-grammar | 150 秒 | 105 秒 |
| lua-conformance | test-conformance | 85 秒 | 25 秒 |
| toml-conformance | test-conformance | 54 秒 | 16 秒 |
| json-conformance | test-conformance | 49 秒 | 9 秒 |
| peg-cli-test | test-packages | 23 秒 | 11 秒 |
| peg-lsp-test | test-packages | 7 秒 | 4 秒 |
| peg-codegen-test | test-packages | 2 秒 | 1 秒 |
| commonmark-conformance、complexity、peg-runtime-test | | 1 秒未満 | 1 秒未満 |

適合性のスイートは、単独で 4 コアを使えるようになって大きく縮んだ。
[ADR 0039](../adr/0039-faster-ci.md) の後の時間の大半は、ほかのスイートとのコアの取り合いだったことになる。
peg-grammar-test の縮み方は小さい。
4 コアを独占しても、最も長いテスト（文法ファイルごとに分けた変異のテストと、無作為な文法のプロパティテスト）の時間がスイートの時間の下限になっているためと見られる。

## ADR のテスト設計の結果

| 項目 | 結果 |
|---|---|
| すべてのスイートが動くこと | 10 個のスイートが、三つのジョブのどれかで一度ずつ動いた |
| キャッシュのある実行の時間 | 2 分 33 秒。[ADR 0039](../adr/0039-faster-ci.md) の後の約 3 分 45 秒より短いが、目安の 2 分 30 秒を 3 秒超えた |
| peg-grammar-test の時間 | 105 秒。目安の 100 秒を 5 秒超えた |
| ジョブの時間のそろい方 | 148 秒、97 秒、56 秒。差（92 秒）が最も長いジョブの半分（74 秒）を超え、目安を満たさなかった |
| キャッシュの保存 | main の `dist-newstyle` のキャッシュは、`haskell` のジョブが保存した一つだけだった。テストのジョブは設定のとおり復元だけを行った |

## 残った課題

ワークフローの時間は、peg-grammar-test 一つで決まっている。
ジョブの分け方をそろえても、test-grammar のジョブが縮まない限り、ワークフローは縮まない。
縮めるには、peg-grammar-test の中の重いテストを複数のジョブに分ける（シャーディング）か、重いテストそのものの費用を下げる必要がある。
どちらも、[ADR 0041](../adr/0041-split-test-jobs-and-cores.md) が別の ADR に回したものである。
