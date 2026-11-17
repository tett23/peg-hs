# ADR 0102: 性能の予算を CI の計測で判定する

Status: proposed

## 文脈

[ADR 0071](0071-incremental-parsing-in-the-language-server.md) は、言語サーバーの目安を、Golem の大きさの文法で 1 回の編集の診断と、編集の後の semantic tokens の要求が、それぞれ 16 ms 以内と定めた。
[ADR 0071](0071-incremental-parsing-in-the-language-server.md) のテスト設計は、この目安を「自動テストにはしない。実装の後の計測で、目安に届いたかを書く」とした。
[ADR 0094](0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md) も、修正の前と後を同じ方法で測り、結果をプルリクエストに書くと定めた。
どちらも、計測する場所を決めていない。

PR #86 では、この計測を開発者の手元で行い、手元の負荷が高く、変更後の同じバイナリでも 13.5 ms から 30.3 ms の値が出た（[ADR 0098](0098-measure-pr-86-lsp-latency-in-ci.md) の文脈）。
そのため、PR #86 の判定は保留になり、[ADR 0098](0098-measure-pr-86-lsp-latency-in-ci.md) で GitHub Actions のランナーに移した。
ただし、[ADR 0098](0098-measure-pr-86-lsp-latency-in-ci.md) は PR #86 だけに限った決定である。
[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) は、計測に影響する変更を含む main への push ごとに測るが、16 ms を超えても issue を立てるだけで、プルリクエストのマージを止めない。

リポジトリの持ち主は、負荷のかかる計測の予算は CI で測るほうが、開発者ごとのばらつきが減ってよいと判断した。
この ADR は、予算の合否を決める場所を CI に定め、言語サーバーの予算をプルリクエストで判定する。
この ADR は、[ADR 0101](0101-run-ci-for-documents-that-tests-read.md) の `scripts/ci-changes.mjs` を使うので、[ADR 0101](0101-run-ci-for-documents-that-tests-read.md) の実装の後に実装する。

## 用語

- **ベース**と**ヘッド**：プルリクエストの `base.sha` と `head.sha` のコミット。
- **操作**：言語サーバーの計測の二つの操作。「診断」は範囲の編集を受け取って診断を返すまで、「semantic tokens」は同じ編集の後に semantic tokens を返すまでである（診断を含む）。
  ケースの名前の末尾が `range: decode, check, encode` のものが「診断」、`range, and the semantic tokens` のものが「semantic tokens」である。
  `scripts/lsp-budget.sh` と `scripts/lsp-median.mjs --max` は、それぞれを `diagnostics` と `semantic-tokens` の名前で受ける。
- **ケース**：計測の一つの組み合わせ。Memo と Golem の 2 文法、文書の先頭、中ほど、末尾の 3 か所、2 操作で、一つの版につき 12 件ある。
- **標本**と**反復数**：Criterion 1.6 の JSON の `reportMeasured` の一行が一つの標本で、その `time` の列が経過秒数、`iters` の列が反復数である。
- **中央値**：ケースごとに、各標本の経過秒数をその反復数で割った値を昇順に並べ、標本数が奇数なら中央の一つ、偶数なら中央の二つの算術平均を取った値（[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の定義）。

## 調査した事項

- `.github/workflows/lsp-latency.yml` は、`push` の `main` だけで起動する。`changes` のジョブが `scripts/lsp-monitor-changes.mjs` の `shouldMeasure` で計測の要否を決め、`benchmark` のジョブが `scripts/lsp-median.mjs` で 12 件の中央値を出し、`notify` のジョブが issue を立てる。
- `scripts/lsp-median.mjs:2` は、ケースの名前の一覧 `cases` を `scripts/lsp-latency.mjs` から読み込む。上限は `scripts/lsp-median.mjs:4` の `limitSeconds = 0.016` である。入力が欠けるか不正なときは例外を投げ、0 でない終了コードで終わる。
- `.github/workflows/ci.yml:444-445` の `lsp-latency` のジョブは、`github.event.pull_request.number == 86` のときだけ動く。このジョブは、ベースとヘッドを同じランナーで測り、`scripts/lsp-latency.mjs` で Criterion の平均を判定する。Memo の文法は、ベースの `conformance/bench/Memo.hpeg` を両版に使う。
- `.github/workflows/ci.yml:501-515` の `ci` のジョブは、`lsp-latency` を含む全ジョブの結果を `needs` で集め、`success` と `skipped` のほかがあれば失敗する。
- main のブランチ保護が必須にしている検査は `adr` と `ci` の二つである（`gh api repos/tett23/peg-hs/branches/main/protection/required_status_checks --jq '.contexts'` の出力は `["adr","ci"]`）。
- `.github/workflows/ci.yml` の `changes` のジョブは、`git diff --name-only "$BASE...$HEAD"` の差分が `docs/` と `.md` だけなら、ビルドとテストのジョブを飛ばす。
- `shouldMeasure`（`scripts/lsp-monitor-changes.mjs:6-15`）は、`conformance/`（`conformance/test/` と `conformance/README.md` を除く）、`packages/*/src/` と `packages/*/grammar/`、`.cabal`、`cabal.project` と `cabal.project.freeze`、`.github/workflows/lsp-latency.yml`、`scripts/lsp-latency.mjs`、正規表現 `^scripts/lsp-(median|monitor-changes)(?:-issue)?(?:\.test)?\.mjs$` に合うパスのどれかを含む差分で真になる。
- `lsp-latency.yml` が main の d0771af で測った実行 44060701947 では、12 件の中央値は 3.22 ms から 10.18 ms だった。最大は Golem の文法の末尾の編集の semantic tokens の 10.18 ms である。
- 同じ実行で、ビルドと計測の段は 10:00:36 に始まり、中央値の段は 10:07:40 に始まった。一つの版のビルドと計測に約 7 分かかった。
- PR #86 のヘッドを CI で測ったときの 12 件の平均時間の最大は 14.2744 ms だった（[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の文脈）。平均と中央値は別の指標なので、10.18 ms と直接は比べられない。
- `docs/budgets.md` は main に無い。

## 実装すること

### 予算の合否を決める場所（方針）

- 性能の予算の合否は、GitHub Actions の `ubuntu-latest` のランナーでの計測で決める。
- 開発の途中で、手元で簡易に測って目安にしてよい。ただし、手元の計測は参考の値であり、合否に使わない。手元で予算を満たしても、CI の計測で満たすまでは、予算を満たしたとはしない。
- これ以後の ADR が予算を置くときは、その予算を CI で測る方法と、どのイベントで測るかを、同じ ADR で決める。
- 予算は、決めた ADR の受けいれ条件と `docs/budgets.md` の両方に書く。
- この節は方針であり、テストで確かめない。この ADR で予算にするのは、受けいれ条件 `A3` の言語サーバーの二つだけである。

### 計測の手順の共有

- 計測の手順を `scripts/lsp-measure.sh <Memo の文法のパス> <出力のディレクトリ>` にまとめる。このスクリプトは、動かしたディレクトリの `peg-bench` を `-O1` でビルドし、Golem の文法（コミット `89ae4b41` の `modules/golem-parser/grammar/Golem.hpeg`）を取得して SHA-256 を確かめ、2 文法を RTS の `-A64m` で測り、出力のディレクトリに `Memo.json` と `Golem.json` を書く。
- main の計測（`lsp-latency.yml`）、プルリクエストの判定、予算のコマンド（`scripts/lsp-budget.sh`）は、どれもこのスクリプトで測る。
- ケースの名前の一覧 `cases` を `scripts/lsp-median.mjs` に移し、`scripts/lsp-latency.mjs` とそのテスト `scripts/lsp-latency.test.mjs` を消す。`scripts/lsp-median.test.mjs` の `cases` の読み込み元も `scripts/lsp-median.mjs` に直す。`ci.yml` の `lsp-latency` のジョブから、`lsp-latency.test.mjs` を動かす段を消す。
- `scripts/lsp-median.mjs` は、上限 `limitSeconds` を export する。

### プルリクエストでの判定

- `.github/workflows/ci.yml` の `lsp-latency` のジョブを、PR #86 に限らず、すべての `pull_request` で動かす。
- このジョブは、まず `node scripts/lsp-monitor-changes.mjs "$(git merge-base "$BASE" "$HEAD")" "$HEAD"` で計測の要否を決める。このコマンドは、マージベースからヘッドまでの差分のパスを `--no-renames` で取り、`shouldMeasure` に渡す。偽なら、ビルドと計測の段を飛ばして成功する。
- 真なら、ベースとヘッドの作業ツリーで、ヘッドの `scripts/lsp-measure.sh` を順に動かす。Memo の文法は、同じ入力で比べるため、両版ともベースの `conformance/bench/Memo.hpeg` を使う。
- ヘッドの判定は `node scripts/lsp-median.mjs --fail-on-exceed <Memo.json> <Golem.json>` で行う。12 件の入力の条件（不変条件 `I1`）を満たさないとき、またはどれかの中央値が 0.016 秒を超えたとき、0 でない終了コードで終わり、ジョブを失敗させる。判定には表示用に丸める前の秒数を使う。
- ベースの値は比較のためだけに使う。ベースのビルドと計測と集計の段には `continue-on-error: true` を付け、どれかが失敗したときは、ジョブサマリーに「ベースは測れなかった」と出す。ジョブの結果はヘッドの判定だけで決める。
- ジョブサマリーには、ベースとヘッドのコミット、Memo と Golem の入力の版、ランナー、GHC、計測の設定と、両版の 12 件の中央値を出す。
- `lsp-latency` は `ci` のジョブの `needs` に入っているので、このジョブの失敗は必須の検査 `ci` を失敗させ、マージを止める。

### 計測の要否の対象

- `shouldMeasure` が真になるパスに、`docs/budgets.md`、`.github/workflows/ci.yml`、`scripts/lsp-measure.sh`、`scripts/lsp-budget.sh` を足し、消した `scripts/lsp-latency.mjs` を除く。
- `shouldMeasure` は main の計測（[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md)）とプルリクエストの判定の両方が使う。そのため、main でも、この四つのパスを変えた push を測る。

### 予算の一覧

- `docs/budgets.md` を置き、受けいれ条件 `A3` の二つの予算を、次の列で書く。

  | 名前 | 指標と単位 | 比較 | 値 | 計測のコマンド | ADR |
  | --- | --- | --- | --- | --- | --- |
  | 言語サーバーの編集の診断 | 6 ケースの中央値の最大（ms） | `<=` | 16 | `scripts/lsp-budget.sh diagnostics` | ADR 0102 A3 |
  | 言語サーバーの編集の semantic tokens | 6 ケースの中央値の最大（ms） | `<=` | 16 | `scripts/lsp-budget.sh semantic-tokens` | ADR 0102 A3 |

- `scripts/lsp-budget.sh <操作>` は、まず引数を確かめる。引数がちょうど一つで、`diagnostics` か `semantic-tokens` のときだけ先に進む。
- 先に進むと、`mktemp -d` で作った一時のディレクトリを出力のディレクトリにして、リポジトリのルートで `scripts/lsp-measure.sh` を `conformance/bench/Memo.hpeg` で動かす。続いて `node scripts/lsp-median.mjs --max <操作> <Memo.json> <Golem.json>` で、その操作の 6 ケースの中央値の最大を、ms で小数第 3 位まで（`toFixed(3)`）の一つの数として、標準出力の最後の行に出す。
- このコマンドは、手元で動かすと参考の値を出す。合否は、プルリクエストの判定と main の計測で決める。
- `I7` のテストが `docs/budgets.md` を読むので、`docs/budgets.md` を [ADR 0101](0101-run-ci-for-documents-that-tests-read.md) の入力の一覧に足す。`docs/budgets.md` だけを変えるプルリクエストでも、テストと計測が動く。

### 前の ADR の扱い

- この ADR を採択したら、[ADR 0071](0071-incremental-parsing-in-the-language-server.md) のステータスを、`part` を「テスト設計の計測」とした `superseded` にする。[ADR 0071](0071-incremental-parsing-in-the-language-server.md) の「計測の記録」（`docs/benchmarks/` への記録）は変えない。
- [ADR 0098](0098-measure-pr-86-lsp-latency-in-ci.md) のステータスを、`part` を `null` とした `superseded` にする。PR #86 に限った判定と、Criterion の平均による判定を、この ADR の判定で置き換える。
- [ADR 0094](0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md) の「言語サーバーの速さ」は実装を終えており、変えない。これからの実装での計測は、この ADR の判定による。
- 仕様書と README の、編集応答時間の計測の記述を、プルリクエストでの判定を含めて書き直す。

## 実装しないこと

- [ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の main の計測の中央値と、issue の通知は変えない。main に入った後の揺れの観測として残す。変えるのは、計測の手順を `scripts/lsp-measure.sh` に移すことと、`shouldMeasure` の対象だけである。
- dotfiles の `bin/budget-check` を CI に入れること。main で予算を超えたときの issue は [ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の仕組みが立てるので、二つの仕組みが同じ超過に issue を立てることになる。入れるなら、[ADR 0099](0099-open-an-issue-for-lsp-median-latency.md) の通知を置き換える別の ADR で決める。
- 16 ms の値を変えること。
- 言語サーバーのほかの性能（`peg-hs gen` などのコマンドの時間、CI の所要時間の目安）を予算にすること。
- 超過したときに、自動で計測をやり直すこと。

## 不変条件

- `I1`: ヘッドの判定の入力の条件は、二つの JSON がどちらも Criterion 1.6 の形式で、各報告に `time` と `iters` の列がちょうど一つずつあり、12 件の各ケースがちょうど一つずつあり、各ケースに一つ以上の標本があり、各経過時間が有限の正の数で、各反復数が正の整数であることである。条件を満たさなければ、判定は失敗する。
- `I2`: 判定は、`I1` の条件を満たし、ヘッドの 12 件のすべての中央値が 0.016 秒以下のときに限って成功する。
- `I3`: 判定の結果は、ベースの値と、ベースの計測が成功したかどうかによらない。
- `I4`: プルリクエストの差分のパスを `shouldMeasure` に渡して偽なら、ジョブは計測せずに成功する。真なら、ヘッドを測り、`I1` と `I2` で判定する。
- `I5`: `scripts/lsp-budget.sh` の引数がちょうど一つで、`diagnostics` か `semantic-tokens` でなければ、ビルドの前に終了コード 2 で終わり、数を出さない。
- `I6`: `scripts/lsp-budget.sh` は、`I1` の条件を満たすとき、指定した操作の 6 ケースの中央値の最大を、ms で小数第 3 位までの数として標準出力の最後の行に出し、終了コード 0 で終わる。16 ms を超えていても同じである。条件を満たさないときは、0 でない終了コードで終わり、数を出さない。
- `I7`: `docs/budgets.md` の二つの予算の行の値は、`scripts/lsp-median.mjs` の上限を ms にした値と等しい。
- `I8`: [ADR 0101](0101-run-ci-for-documents-that-tests-read.md) の `needsBuild` は、`docs/budgets.md` だけの差分で真を返す。

| 入力（記載したほかのケースは 16 ms 以内で、条件を満たす） | 期待 | 不変条件 |
| --- | --- | --- |
| ヘッドの最大の中央値が 16 ms ちょうど | 成功 | I2 |
| ヘッドの一件の中央値が 16.001 ms | 失敗 | I2 |
| ヘッドの一件の標本が 15 ms と 17.002 ms の二つ（中央値 16.001 ms） | 失敗 | I2 |
| ヘッドの一件の標本が、経過時間 0.032 秒、反復数 2 の一つだけ（中央値 16 ms） | 成功 | I2 |
| ヘッドの一件が欠測、標本が空、反復数が 0 | 失敗 | I1 |
| ヘッドに同じケースが二つ | 失敗 | I1 |
| ベースの一件だけが 40 ms | 成功 | I2, I3 |
| ベースのビルドが失敗 | 成功（サマリーに「ベースは測れなかった」） | I3 |
| 差分のパスが 0 件 | 計測せずに成功 | I4 |
| 差分が `docs/adr/` と `conformance/test/` だけ | 計測せずに成功 | I4 |
| 差分が `docs/budgets.md` だけ | 計測して判定 | I4 |
| 差分が `.github/workflows/ci.yml` だけ | 計測して判定 | I4 |
| 差分が `packages/peg-grammar/src/` の一つのファイル | 計測して判定 | I4 |
| `lsp-budget.sh`（引数なし）、`lsp-budget.sh latency`、`lsp-budget.sh diagnostics semantic-tokens` | ビルドせずに終了コード 2、数を出さない | I5 |
| `lsp-budget.sh semantic-tokens` で、その 6 ケースが 9.2、9.5、9.6、10.0、9.9、10.2 ms | 最後の行が `10.200`、終了コード 0 | I6 |
| `lsp-budget.sh diagnostics` で、その 6 ケースの一件が 20 ms | 最後の行が `20.000`、終了コード 0 | I6 |
| `lsp-budget.sh diagnostics` で、診断の 6 ケースの一件が欠測 | 0 でない終了コード、数を出さない | I6 |
| `docs/budgets.md` の値が 16、上限が 0.016 秒 | 一致 | I7 |
| `needsBuild` に `docs/budgets.md` だけ | 真 | I8 |

## 受けいれ条件

- `A1`: この ADR を実装するプルリクエストは、`shouldMeasure` が真になるパス（`scripts/lsp-monitor-changes.mjs` と `scripts/lsp-median.mjs`）を変える。そのプルリクエストの CI で、`lsp-latency` のジョブが両版を測り、ジョブサマリーに両版の 12 件の中央値が出る。
- `A2`: 実装の後に、`docs/adr/` だけを変えるプルリクエストの CI で、`lsp-latency` のジョブが成功し、ビルドと計測の段が飛ばされる。
- `A4`: 実装のプルリクエストの `ci.yml` で、ベースのビルドと計測と集計の段に `continue-on-error: true` が付き、ヘッドの判定の段がヘッドの JSON だけを読む。
- `A3`: 言語サーバーの予算は、診断の 6 ケースの中央値の最大が 16 ms 以下、semantic tokens の 6 ケースの中央値の最大が 16 ms 以下である。`docs/budgets.md` に、「予算の一覧」の節の表の二行が、その列の値のとおりにある。

## テスト設計

- `I1`、`I2`、`I3` の判定と、`I6` の集計と書式は、`scripts/lsp-median.test.mjs` に `node:test` で書き、Criterion の JSON の小さな見本を入力に、表の境界例を与える。テストの名前は `ADR 0102 I1: …` の形にする。
- `I4` の `shouldMeasure` の真偽は、`scripts/lsp-monitor-changes.test.mjs` に同じ形で書く。表の「計測せずに成功」と「計測して判定」のジョブの結果は、単体のテストでは確かめられないので、`A1` と `A2` で確かめる。
- `I5` は、`scripts/lsp-budget.test.mjs` から `node:child_process` で `scripts/lsp-budget.sh` を動かし、終了コードと標準出力を確かめる。ビルドが始まらないことは、呼ばれたら印のファイルを書く偽の `cabal` を `PATH` の先頭に置き、印が無いことで確かめる。
- `I7` は、`scripts/lsp-median.test.mjs` で `docs/budgets.md` の二つの行を読み、上限と比べる。
- `I8` は、`scripts/ci-changes.test.mjs` に `ADR 0102 I8: …` の名前で書く。
- これらのテストは、`ci.yml` の `changes` のジョブの `node --test scripts/lsp-median*.test.mjs scripts/lsp-monitor-changes.test.mjs` に `scripts/lsp-budget.test.mjs` を足して動かす。
- `scripts/lsp-measure.sh` のビルドと計測は、`A1` の CI の実行で確かめる。
- `A1` と `A2` は、それぞれのプルリクエストの CI の実行で、ジョブの終了状態、段の状態、ジョブサマリーを見て確かめる。
- `A4` は、実装のプルリクエストのレビューで `ci.yml` を読んで確かめる。ベースだけが失敗するプルリクエストを意図して作るのは難しいためである。
- `A3` は、`I7` のテストと、`docs/budgets.md` の表を目で読むことで確かめる。

## トレードオフ

- GitHub が割り当てるランナーの性能にはばらつきがあり、コードの変化が無くても 16 ms を超えて失敗することがある。実行 44060701947 の中央値の最大は 10.18 ms だった。ランナーによる揺れの幅は測っておらず、一回の実行の値しかない。失敗したときは、ジョブサマリーのベースの値と比べ、ベースも同じく遅ければランナーの揺れを疑う。
- 計測の要るプルリクエストでは、二つの版のビルドと計測の分だけ、`ci` の検査が終わるのが遅れる。一つの版に約 7 分かかったので、二つの版で約 14 分かかると見込む（見込みであり、測っていない）。`ci.yml` は新しい push で前の実行を取り消すので、計測の途中で push すると、計測はやり直しになる。
- 手元の計測を合否に使わないので、ランナーと手元の機械の差は判定に入らない。その代わり、手元で速いことを確かめても、CI の判定を待たないとマージできない。
- `shouldMeasure` に `ci.yml` を足すので、計測に関係しない `ci.yml` の変更でも、プルリクエストと main で計測が動く。判定のジョブ自体を変える変更が、計測されずにマージされることを防ぐためである。

## 参考文献

- [ADR 0071](0071-incremental-parsing-in-the-language-server.md)：言語サーバーの目安（16 ms）
- [ADR 0072](0072-required-checks-for-auto-merge.md)：必須の検査 `ci` のジョブで結果を一つにまとめる
- [ADR 0094](0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md)：修正の前後の言語サーバーの計測
- [ADR 0098](0098-measure-pr-86-lsp-latency-in-ci.md)：PR #86 の CI での判定
- [ADR 0099](0099-open-an-issue-for-lsp-median-latency.md)：main の計測と中央値の定義
- [ADR 0101](0101-run-ci-for-documents-that-tests-read.md)：テストとビルドが読む文書の入力の一覧
- [実行 44060701947](https://github.com/tett23/peg-hs/actions/runs/44060701947)：main の d0771af の 12 件の中央値
