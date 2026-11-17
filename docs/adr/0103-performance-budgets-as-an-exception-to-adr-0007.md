# ADR 0103: 性能の予算を [ADR 0007](0007-performance-discipline.md) の例外とする

Status: accepted-pending

## 文脈

[ADR 0007](0007-performance-discipline.md) は、「絶対値の性能目標は置かない」と「CI での自動性能ゲートは設けない」の二つを、実装しないこととして決めた。
後者の理由は、共有ランナーの計測は分散が大きく、閾値が誤検出と見逃しの両方を生むことである。

しかし、その後の ADR は、この二つと食い違う決定をした。
[ADR 0071](0071-incremental-parsing-in-the-language-server.md) は言語サーバーの目安を 16 ms とし、[ADR 0102](0102-judge-performance-budgets-in-ci.md) はその目安を予算として、すべてのプルリクエストの CI で判定する。
それでも [ADR 0007](0007-performance-discipline.md) のステータスは accepted のままで、`CONTRIBUTING.md` の性能の節も、[ADR 0007](0007-performance-discipline.md) を引いて絶対値の目標を置かないと書いている。

16 ms は、60 FPS の 1 フレーム（1000 / 60 ≒ 16.7 ms）を近似した値である。
編集の応答を、画面の 1 フレームのうちに返すことを狙う。
この根拠は、リポジトリの持ち主がこの ADR を書くときに示したもので、[ADR 0071](0071-incremental-parsing-in-the-language-server.md) には書かれていない。

[ADR 0007](0007-performance-discipline.md) が心配した分散は、実際に観測された。
同じコードを同じ条件で測っても、CI の中央値は大きく変わった（「調査した事項」）。
リポジトリの持ち主は、測り直しなどで分散を吸収することはせず、16 ms を超えたら [ADR 0102](0102-judge-performance-budgets-in-ci.md) のとおり失敗させ、いまの値が予算に近いことは高速化で解くと決めた。
この ADR は、[ADR 0007](0007-performance-discipline.md) の二つの決定を予算に限って改め、文書を合わせる。

## 調査した事項

- `docs/adr/0007-performance-discipline.md:31` は「絶対値の性能目標は置かない」、`:33` は「CI での自動性能ゲートは設けない。共有ランナーの計測は分散が大きく、閾値が誤検出と見逃しの両方を生むためである」と書いている。ステータスは `accepted` である。
- `CONTRIBUTING.md:296` は「peg-hs sets no absolute performance targets ([ADR 0007](docs/adr/0007-performance-discipline.md)).」、`CONTRIBUTING.ja.md:297` は「peg-hs は性能に絶対値の目標を置かない（[ADR 0007](docs/adr/0007-performance-discipline.md)）。」と書いている。同じ節の後の行は、CI が `docs/budgets.md` の予算を検査すると書いている。
- `git diff --stat d0771af 35a32ab -- packages conformance cabal.project cabal.project.freeze` の出力は空である。二つのコミットのあいだで、`peg-bench` のビルドと入力に関わるファイルは変わっていない。
- main の d0771af を測った実行 44060701947 では、semantic tokens の 6 ケースの中央値は 9.26 ms から 10.18 ms、診断の 6 ケースは 3.22 ms から 4.52 ms だった。
- main の 35a32ab を測った実行 44134458784 では、semantic tokens の 6 ケースの中央値は 14.14 ms から 15.45 ms、診断の 6 ケースは 4.68 ms から 6.81 ms だった。
- 二つのジョブのログは、どちらもランナーのイメージを `ubuntu-26.04` の `20261103.629` と記録している。どちらも `peg-bench` を `--enable-optimization=1` でビルドし、`--match pattern range` と RTS の `-A64m` で動かした。
- 12 件の中央値は、二つの実行のあいだで、どれも 1.4 倍から 1.6 倍になった。ケースごとに揺れたのではなく、割り当てられたランナー全体が遅かったと推測する。同じジョブの中で二回測ったときの差は測っていない。

## 実装すること

- 絶対値の性能目標は、ADR で決めて `docs/budgets.md` に書いた予算に限って置く。予算のほかの性能には、これまでどおり絶対値の目標を置かない。
- CI での自動性能ゲートは、`docs/budgets.md` の予算に限って設ける。判定は [ADR 0102](0102-judge-performance-budgets-in-ci.md) のとおりで、この ADR は変えない。
- この ADR を採択したら、[ADR 0007](0007-performance-discipline.md) のステータスを、`part` を「実装しないこと（絶対値の性能目標は置かない）」と「実装しないこと（CI での自動性能ゲートは設けない）」とした二つの変更を持つ `superseded` にする。
- `CONTRIBUTING.md:296` と `CONTRIBUTING.ja.md:297` を、`docs/budgets.md` の予算のほかは絶対値の目標を置かない、という形に書き直す。

## 実装しないこと

- 予算を超えたヘッドを測り直すこと。上の二つの実行の差はランナー全体の速さの差と推測され、同じランナーで測り直しても防げない見込みが高い。別のランナーで測り直すことも、リポジトリの持ち主は選ばなかった。
- 16 ms の値を変えること。
- 言語サーバーを速くすること。予算に近いいまの値は、別の ADR で高速化して解く。
- [ADR 0102](0102-judge-performance-budgets-in-ci.md) の判定と、[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の main の計測を変えること。

## 不変条件

なし。
この ADR は、前の ADR のステータスと文書の記述だけを変え、振る舞いを変えない。

## 受けいれ条件

- `A1`: [ADR 0007](0007-performance-discipline.md) のステータスが、上の二つの `part` を持ち、`by` をこの ADR とする `superseded` になっていて、`adr-guard check-status` が通る。
- `A2`: `CONTRIBUTING.md` と `CONTRIBUTING.ja.md` の性能の節が、`docs/budgets.md` の予算のほかは絶対値の目標を置かないと書き、[ADR 0007](0007-performance-discipline.md) とこの ADR へのリンクを持つ。

## テスト設計

- `A1` は、実装のプルリクエストで `adr-guard check-status` と `adr-guard trace` を動かし、[ADR 0007](0007-performance-discipline.md) の二つの変更がこの ADR を指すことを確かめる。
- `A2` は、実装のプルリクエストで二つの文書の性能の節を読んで確かめる。

## トレードオフ

- 予算に分散を吸収する仕組みを持たせないので、遅いランナーに当たると、コードが変わらなくてもプルリクエストが失敗する。いまの値（実行 44134458784 で 15.45 ms）は 16 ms に近く、高速化で余裕を作るまでは、この失敗が起こりうる。失敗したときは CI を再実行し、ジョブサマリーのベースの値と比べる。
- [ADR 0007](0007-performance-discipline.md) の、共有ランナーの計測は分散が大きいという判断は、上の実行の差のとおり正しい。この ADR は、その分散を知ったうえで、予算に限ってゲートを置く。

## 参考文献

- [ADR 0007](0007-performance-discipline.md)：計算量の保証と性能規律
- [ADR 0071](0071-incremental-parsing-in-the-language-server.md)：言語サーバーの目安（16 ms）
- [ADR 0099](0099-open-an-issue-for-lsp-median-latency.md)：main の計測と issue の通知
- [ADR 0102](0102-judge-performance-budgets-in-ci.md)：性能の予算を CI の計測で判定する
- [実行 44060701947](https://github.com/tett23/peg-hs/actions/runs/44060701947)：main の d0771af の計測
- [実行 44134458784](https://github.com/tett23/peg-hs/actions/runs/44134458784)：main の 35a32ab の計測
