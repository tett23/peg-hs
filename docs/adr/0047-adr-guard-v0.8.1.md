# ADR 0047: adr-guard を v0.8.1 に上げる

ステータス: 採択

## 文脈

[ADR 0043](0043-adr-guard-v0.8.0.md) で、[adr-guard](https://github.com/tett23/adr-guard) を v0.8.0 に上げ、ステータスの行とコミット済みの `docs/benchmarks/` の記録を検査するようにした。

adr-guard の v0.8.1 は、保護するディレクトリの名前の別名を加えた（[adr-guard の ADR 0014](https://github.com/tett23/adr-guard/blob/main/docs/adr/0014-directory-name-variants.md)）。

- ADR のディレクトリとして、`adr` のほか `adrs`、`decisions`、`decision` も扱う
- 記録のディレクトリとして、`docs/audit/` と `docs/benchmarks/` のほか `docs/audits/` と `docs/benchmark/` も保護する

peg-hs の ADR は `docs/adr/` だけにあり、記録は `docs/benchmarks/` だけにある。
追跡しているファイルにも、追跡していないディレクトリにも、`adrs`、`decisions`、`decision`、`audits`、`benchmark` の名前のディレクトリは無い。
v0.8.1 にしても、検査の対象は変わらない。
別名のディレクトリを誤って作ったときも保護されるように、版をそろえる。

## 実装すること

- CI の action を `tett23/adr-guard@v0.8.1` にする。`allow-status: true` と `allow-links: true` は残す
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする
- README（英語と日本語）の adr-guard の導入のコマンドを `cargo install --git https://github.com/tett23/adr-guard --tag v0.8.1` にする
- `docs/specifications.md` の adr-guard の版を v0.8.1 にし、この ADR へリンクする
- [ADR 0043](0043-adr-guard-v0.8.0.md) のステータスの行を、版の更新がこの ADR に移ったことを示す形に変える

## 実装しないこと

- 記録や ADR のディレクトリの名前の変更。peg-hs は `docs/adr/` と `docs/benchmarks/` だけを使い、別名のディレクトリは無い
- 文書への別名の列挙。peg-hs の文書は、記録の置き場所として `docs/benchmarks/` だけを定めている。別名を使う予定は無いので、README、CONTRIBUTING、CLAUDE.md には書き足さない
- `docs/conformance/` の保護。v0.8.1 でも adr-guard の保護の対象ではない。扱いは [ADR 0043](0043-adr-guard-v0.8.0.md) のとおりとする

## テスト設計

設定の変更なので、自動テストは書かない。
実装の後に、次のことを確かめる。

- v0.8.1 の手元の adr-guard で、`adr-guard check-status` と `adr-guard links` が終了コード 0 で終わる
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが通る

## トレードオフ

- `docs/benchmark/` や `docs/audits/` を、記録のつもりでなく作ると、コミットした後に変更できなくなる。peg-hs ではこれらの名前を使わない
- 版の更新ごとに ADR を書く手間がかかる。検査の規則が変わる更新なので、変更の理由を残す
