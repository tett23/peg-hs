# 予算の一覧

この文書は、peg-hs の性能の予算を一覧にする。
予算を決めるのは ADR であり、この一覧と ADR が食い違うときは ADR が正しい。
予算を置くか変える ADR は、同じ変更でこの一覧も変える。

予算の合否は、GitHub Actions の `ubuntu-latest` のランナーでの計測で決める（[ADR 0102](adr/0102-judge-performance-budgets-in-ci.md)）。
「計測のコマンド」の列のコマンドは、リポジトリのルートで動かすと、計測した値を一つの数として標準出力の最後の行に出す。
手元でこのコマンドを動かした値は参考の値であり、合否には使わない。

| 名前 | 指標と単位 | 比較 | 値 | 計測のコマンド | ADR |
| --- | --- | --- | --- | --- | --- |
| 言語サーバーの編集の診断 | 6 ケースの中央値の最大（ms） | `<=` | 16 | `scripts/lsp-budget.sh diagnostics` | [ADR 0102 A3](adr/0102-judge-performance-budgets-in-ci.md) |
| 言語サーバーの編集の semantic tokens | 6 ケースの中央値の最大（ms） | `<=` | 16 | `scripts/lsp-budget.sh semantic-tokens` | [ADR 0102 A3](adr/0102-judge-performance-budgets-in-ci.md) |

ケースは、Memo と Golem の 2 文法で、文書の先頭、中ほど、末尾を編集する 6 件である。
中央値は、Criterion の標本ごとに経過時間を反復数で割った値の中央値である（[ADR 0099](adr/0099-open-an-issue-for-lsp-median-latency.md)）。
