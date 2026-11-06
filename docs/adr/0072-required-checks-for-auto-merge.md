# ADR 0072: 自動マージのために、必須のチェックを一つにまとめる

ステータス: 採択

## 文脈

リポジトリの持ち主は、プルリクエストを自動マージにすると決めた。
そのために、リポジトリの設定で自動マージを有効にし、main のブランチ保護で、CI の 12 のジョブ（`adr`、`editors`、`haddock`、`haskell`、`sdist-1` から `sdist-3`、`test-conformance`、`test-grammar-1` から `test-grammar-3`、`test-packages`）を必須のチェックにした（2026-11-06）。
自動マージは、必須のチェックがすべて通った時点でマージする。

ところが、CI のワークフロー（`.github/workflows/ci.yml`）は、文書だけの変更では動かない。
`pull_request` に `paths-ignore: ['docs/**', '**.md']` があるためである（[ADR 0039](0039-faster-ci.md)）。
ADR だけのプルリクエストでは `adr` のジョブしか動かず、残りの 11 の必須のチェックは結果を返さない。
GitHub は、結果を返さない必須のチェックを待ち続けるので、自動マージはいつまでもマージしない。

必須のチェックをジョブごとに並べる形には、もう一つ弱みがある。
ジョブを足したり、名前や行列を変えたりするたびに、ブランチ保護の設定も直す必要があり、直し忘れると、新しいジョブが落ちてもマージされる。

## 実装すること

### 変更の判定

- `ci.yml` の `pull_request` から `paths-ignore` を外し、プルリクエストでは常にワークフローを動かす
- 最初のジョブ `changes` で、プルリクエストの基点と先端の差分を `git diff --name-only` で求め、`docs/` の下と `.md` のファイル以外の変更があるかを出力する。外部のアクションは使わず、シェルで書く
- これまでのジョブ（`haskell`、`test`、`haddock`、`sdist`、`editors`）は `changes` に依存し、文書以外の変更がないときは `if` で飛ばす
- `push`（main）の `paths-ignore` は変えない

### まとめのジョブ

- ジョブ `ci` を加える。`ci` はこれまでのすべてのジョブと `changes` に依存し、`if: always()` で常に動く
- `ci` は、依存するジョブの結果に `failure` か `cancelled` が一つでもあれば失敗し、それ以外（`success` と `skipped`）なら成功する

### ブランチ保護

- main の必須のチェックを、`adr` と `ci` の二つにする。ジョブを足しても、`ci` の依存に加えるだけで、ブランチ保護の設定は変えない
- 文書の [ADR 0039](0039-faster-ci.md) に関わる記述（docs/specifications.md の CI の節、README の開発の節）に、必須のチェックと自動マージを書く

## 実装しないこと

- 変更のあったパッケージだけを試験すること。判定は、文書だけかどうかの二つに限る
- `adr` のワークフローを `ci.yml` にまとめること。`adr` は文書の変更でも動く別のワークフローで、いまのままで必須のチェックにできる
- レビューの承認を必須にすること

## テスト設計

ワークフローの設定なので、自動テストにはしない。
実装の後に、次のプルリクエストで実際に動かして確かめる。

- 文書だけを変えるプルリクエスト：`changes` が文書だけと判定し、ほかのジョブが飛ばされ、`ci` が成功し、自動マージでマージされること
- Haskell のコードを変えるプルリクエスト：すべてのジョブが動き、`ci` がその結果を待ってから成功すること
- ジョブの一つを意図して落としたプルリクエスト（確かめた後に閉じる）：`ci` が失敗し、自動マージがマージしないこと

## トレードオフ

- 文書だけの変更でも、ワークフローが起動し、`changes` と `ci` の二つのジョブが動く。どちらも checkout とシェルだけで、数十秒で終わる
- 判定のシェルは、[ADR 0039](0039-faster-ci.md) の `paths-ignore` と同じ条件を、別の書き方で持つことになる。`push` の `paths-ignore` と食い違わないように、同じ条件をワークフローの注釈に書く
- `if` で飛ばしたジョブは、GitHub の画面では skipped と表示される。GitHub は skipped を成功として扱うので、マージは止まらない

## 参考文献

- GitHub Docs, About protected branches, Require status checks before merging. https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches#require-status-checks-before-merging
- GitHub Docs, Troubleshooting required status checks（パスの絞り込みで飛ばしたワークフローと、条件で飛ばしたジョブの扱い）. https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/collaborating-on-repositories-with-code-quality-features/troubleshooting-required-status-checks
- GitHub Docs, Automatically merging a pull request. https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/incorporating-changes-from-a-pull-request/automatically-merging-a-pull-request
