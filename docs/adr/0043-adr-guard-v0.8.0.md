# ADR 0043: adr-guard を v0.8.0 に上げ、ステータスの行と計測の記録を検査する

ステータス: 採択→adr-guard の版（v0.8.1）は [ADR 0047](0047-adr-guard-v0.8.1.md)

## 文脈

コミット済みの ADR は、[adr-guard](https://github.com/tett23/adr-guard) が pre-commit のフックと CI で変更を拒否している。
CI の `adr` のジョブは [ADR 0039](0039-faster-ci.md) で、文書だけの変更でも動くようにした。
CI の action は v0.5.0 で、ステータスの行の変更（`allow-status`）と ADR の参照のリンクだけの変更（`allow-links`）を許可している。
v0.5.0 への更新には ADR を書かなかった。

v0.5.0 の後、adr-guard には次の変更が入った。

- v0.6.0：どの深さの `docs/adr/` と `docs/<モジュール>/adr/` も ADR として扱う（[adr-guard の ADR 0011](https://github.com/tett23/adr-guard/blob/main/docs/adr/0011-nested-adr-directories.md)）。peg-hs の ADR は `docs/adr/` だけなので、対象は変わらない
- v0.7.0：ADR は、行頭が `ステータス:` か `Status:` のステータスの行をちょうど一つ持たねばならない。無い ADR と二つ以上ある ADR は違反になる。検査のサブコマンド `adr-guard check-status` が加わり、action は既定でこれも実行する（[adr-guard の ADR 0012](https://github.com/tett23/adr-guard/blob/main/docs/adr/0012-status-line-and-status-adt.md)）
- v0.8.0：監査と計測の記録（どの深さの `docs/` の下の `docs/audit/` と `docs/benchmarks/`）も、コミット済みのものは変更・削除・移動できない。`--allow-status` と `--allow-links` は記録には効かない（[adr-guard の ADR 0013](https://github.com/tett23/adr-guard/blob/main/docs/adr/0013-protect-audit-and-benchmark-records.md)）

peg-hs の CONTRIBUTING は、`docs/benchmarks/` のスナップショットをコミットした後に変更しないと定めている。
これまでは決まりだけで、検査はなかった。
v0.8.0 にすると、この決まりを adr-guard が検査する。

v0.8.0 の手元の adr-guard で、`main` の作業ツリーの `adr-guard check-status` は違反なしで終わる。
すべての ADR が、行頭が `ステータス:` の行をちょうど一つ持つ。

## 実装すること

- CI の action を `tett23/adr-guard@v0.8.0` にする。`allow-status: true` と `allow-links: true` は残す。`check-status: false` は付けず、ステータスの行の検査も CI で行う
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする（v0.8.0 の pre-commit は、ステータスの行の数と記録の変更も検査する）
- README（英語と日本語）の開発の節に、adr-guard の導入のコマンド（`cargo install --git https://github.com/tett23/adr-guard --tag v0.8.0`）と、adr-guard が `docs/benchmarks/` の変更も拒否することを書く
- CONTRIBUTING（英語と日本語）に、ADR はステータスの行をちょうど一つ持つこと、`docs/benchmarks/` の記録の変更を adr-guard が拒否することを書く
- `docs/specifications.md` に、コミット済みの ADR と `docs/benchmarks/` の記録が変更不可であり、adr-guard が検査することを書く
- CLAUDE.md のディレクトリ構成に `docs/benchmarks/` を加え、コミット後は変更不可で adr-guard が変更を拒否することを書く

## 実装しないこと

- `docs/conformance/` の保護。adr-guard v0.8.0 が保護するのは `docs/audit/` と `docs/benchmarks/` だけである。`docs/conformance/` のスナップショットを変更しない決まりは CONTRIBUTING に残し、検査はしない
- 記録の置き場所の移動。`docs/conformance/` を `docs/benchmarks/` の下に移すと、既存の記録の移動になり、記録とそれを参照する ADR を書きかえることになる
- 過去のコミットの扱い。CI の `check-range` は push と pull request の範囲だけを検査する。v0.8.0 の規則を過去のコミットに当てはめると、ADR の参照をリンクにしたコミット（`docs/benchmarks/` の三つの記録を書きかえた）が違反になるが、検査の範囲に入らないので何もしない
- Claude Code の PreToolUse のフック。全体の設定で有効なので、リポジトリには置かない

## テスト設計

設定の変更なので、自動テストは書かない。
実装の後に、次のことを確かめる。

- `adr-guard check-status` と `adr-guard links` が終了コード 0 で終わる
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- コミット済みの ADR の本文を一時的に変えてステージすると、`.githooks/pre-commit` が拒否する
- コミット済みの `docs/benchmarks/` の記録を一時的に変えてステージすると、`.githooks/pre-commit` が拒否する
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが通る

## トレードオフ

- `docs/benchmarks/` の記録は、誤記を直すことも ADR の参照にリンクを付けることも、検査を迂回しないとできなくなる。記録を直すときは新しい記録を作る。迂回が要るときは、`ADR_GUARD_ALLOW` の環境変数かコミットのトレーラー `ADR-Guard-Allow:` を、書きかえだけのコミットに付ける
- ステータスの行を `- Status:` などの形で書いた ADR は違反になる。peg-hs の ADR はすべて `ステータス:` で書いているので、この制約は既存の書き方と同じである
