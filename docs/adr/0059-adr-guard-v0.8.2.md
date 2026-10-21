# ADR 0059: adr-guard を v0.8.2 に上げる

ステータス: 採択→adr-guard の版（v0.8.3）は [ADR 0060](0060-adr-guard-v0.8.3.md)

## 文脈

[ADR 0047](0047-adr-guard-v0.8.1.md) で、[adr-guard](https://github.com/tett23/adr-guard) を v0.8.1 に上げた。

v0.8.1 までの `--allow-links` は、コミットした ADR の変更のうち、ADR の参照（`ADR 0001` の形）にリンクを付ける変更だけを許していた。
adr-guard の v0.8.2 は、`--allow-links` が許す変更を、コミットした ADR の「リンクだけの変更」全般に広げた（[adr-guard の ADR 0015](https://github.com/tett23/adr-guard/blob/main/docs/adr/0015-allow-link-changes.md)）。

- インラインのリンクと参照形式のリンクの追加、削除、リンク先の変更
- 画像のリンク先の変更
- リンクの参照定義の行（`[1]: url`）の変更

リンクのテキストの変更、画像の追加と削除、自動リンク（`<url>`）と本文の URL の変更は、引き続き拒否する。
記録（`docs/benchmarks/`）は、引き続き完全に保護し、リンクの付与も拒否する。

peg-hs の ADR は、外部の文献や他の ADR へのリンクを多く含む。
v0.8.2 にすれば、移動したページへのリンク先の付けかえのような、決定の中身を変えない修正をステータスの行の変更と同じく許せる。
CI と手元の版をそろえるため、版を上げる。

## 実装すること

- CI の action を `tett23/adr-guard@v0.8.2` にする。`allow-status: true` と `allow-links: true` は残す
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする
- CONTRIBUTING（英語と日本語）の adr-guard の導入のコマンドを `cargo install --git https://github.com/tett23/adr-guard --tag v0.8.2` にし、版の決まりの参照をこの ADR にする
- CONTRIBUTING（英語と日本語）と `docs/specifications.md` の、コミットした ADR で変えてよいものの説明を「ステータスの行と ADR の参照に付けるリンク」から「ステータスの行とリンクだけの変更」にする
- `docs/specifications.md` の adr-guard の版を v0.8.2 にし、この ADR へリンクする
- CI の YAML のコメントの ADR の並びにこの ADR を加える
- [ADR 0047](0047-adr-guard-v0.8.1.md) のステータスの行を、版の更新がこの ADR に移ったことを示す形に変える

## 実装しないこと

- リンクのテキストの変更や本文の URL の変更を許すこと。v0.8.2 でも拒否され、決定の中身に関わりうるので、変えたいときは新しい ADR を書く
- `docs/benchmarks/` のリンクの変更の許可。v0.8.2 でも記録は完全に保護される
- `docs/conformance/` と `docs/editors/` の保護。v0.8.2 でも adr-guard の保護の対象ではない。扱いは [ADR 0043](0043-adr-guard-v0.8.0.md) のとおりとする
- README の変更。README は adr-guard の版に触れていない

## テスト設計

設定の変更なので、自動テストは書かない。
実装の後に、次のことを確かめる。

- v0.8.2 の手元の adr-guard で、`adr-guard links --fix --include-committed` の後に `adr-guard check-status` と `adr-guard links` が終了コード 0 で終わる
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- `adr-guard check-range origin/main HEAD --allow-status --allow-links` が終了コード 0 で終わる
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが通る

## トレードオフ

- コミットした ADR のリンク先を変えられるので、参照した文献を別の文献に差しかえる変更も検査を通る。リンクのテキストは変えられないので、差しかえはレビューで確かめる
- 版の更新ごとに ADR を書く手間がかかる。検査の規則が変わる更新なので、変更の理由を残す

## 参考文献

- [adr-guard の ADR 0015「allow link changes」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0015-allow-link-changes.md)
- [adr-guard v0.8.2 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.8.2)
