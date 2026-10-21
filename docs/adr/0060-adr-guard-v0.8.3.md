# ADR 0060: adr-guard を v0.8.3 に上げる

ステータス: 採択

## 文脈

[ADR 0059](0059-adr-guard-v0.8.2.md) で、[adr-guard](https://github.com/tett23/adr-guard) を v0.8.2 に上げた。

adr-guard の v0.8.3 は、ADR のステータスに `採択（未実装）`（英語は `Accepted (not implemented)`、括弧は全角でも半角でもよい）を加えた（[adr-guard の ADR 0016「ステータス `採択（未実装）` を加え、未実装のADRを一覧する `unimplemented` サブコマンド」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0016-accepted-not-implemented-status.md)）。
採択したがまだ実装していない ADR を表すステータスである。
あわせて、ステータスが `採択（未実装）` の ADR を一覧するサブコマンド `adr-guard unimplemented [--status]` を加えた。

peg-hs では、ADR を採択してから、複数の pull request に分けて実装することがある（[ADR 0055](0055-templates-and-parameterized-rules-in-stages.md) など）。
これまでは、採択した ADR が実装済みかどうかをステータスから区別できなかった。
`採択（未実装）` を使えば、実装の残っている ADR を `adr-guard unimplemented` で一覧できる。
CI と手元の版をそろえるため、版を上げる。

## 実装すること

- CI の action を `tett23/adr-guard@v0.8.3` にする。`allow-status: true` と `allow-links: true` は残す
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする
- CONTRIBUTING（英語と日本語）の adr-guard の導入のコマンドを `cargo install --git https://github.com/tett23/adr-guard --tag v0.8.3` にし、版の決まりと `adr` のジョブの説明の参照をこの ADR にする
- CONTRIBUTING（英語と日本語）の「レビューと採択」に、採択したがまだ実装していない ADR はステータスを「採択（未実装）」にし、実装を終えたら「採択」にすること、`adr-guard unimplemented` で一覧できることを書く
- `docs/specifications.md` の adr-guard の版を v0.8.3 にし、この ADR へリンクする
- CI の YAML のコメントの ADR の並びにこの ADR を加える
- [ADR 0059](0059-adr-guard-v0.8.2.md) のステータスの行を、版の更新がこの ADR に移ったことを示す形に変える

## 実装しないこと

- 既存の ADR のステータスを `採択（未実装）` に書きかえること。どの ADR が未実装かの判断は、それぞれの実装の作業で行う
- `採択（未実装）` の使用を必須にすること。実装まで一つの pull request で済む ADR は、これまでどおり「採択」でコミットしてよい
- README の変更。README は adr-guard の版にも ADR のステータスにも触れていない
- `docs/benchmarks/` と `docs/conformance/`、`docs/editors/` の扱いの変更。[ADR 0059](0059-adr-guard-v0.8.2.md) のとおりとする

## テスト設計

設定の変更なので、自動テストは書かない。
peg-hs には ADR のステータスの書式を検査するテストは無い。
実装の後に、次のことを確かめる。

- v0.8.3 の手元の adr-guard で、`adr-guard links --fix --include-committed` の後に `adr-guard check-status` と `adr-guard links` が終了コード 0 で終わる
- `adr-guard unimplemented` が終了コード 0 で終わる
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- `adr-guard check-range origin/main HEAD --allow-status --allow-links` が終了コード 0 で終わる
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが通る

## トレードオフ

- ステータスの候補が一つ増え、採択から実装の完了までにステータスの行を二度変えることになる。代わりに、実装の残っている ADR を道具で一覧できる
- 実装を終えたときにステータスを「採択」に戻し忘れると、`adr-guard unimplemented` の一覧が実態と食い違う。レビューで確かめる
- 版の更新ごとに ADR を書く手間がかかる。使えるステータスが変わる更新なので、変更の理由を残す

## 参考文献

- [adr-guard の ADR 0016「ステータス `採択（未実装）` を加え、未実装のADRを一覧する `unimplemented` サブコマンド」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0016-accepted-not-implemented-status.md)
- [adr-guard v0.8.3 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.8.3)
