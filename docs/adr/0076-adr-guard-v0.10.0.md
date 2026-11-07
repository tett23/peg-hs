# ADR 0076: adr-guard を v0.10.0 に上げる

ステータス: 採択

## 文脈

[ADR 0060](0060-adr-guard-v0.8.3.md) で、[adr-guard](https://github.com/tett23/adr-guard) を v0.8.3 に上げた。

adr-guard の v0.9.0 は、同じディレクトリで番号が重複した ADR を報告する `adr-guard check-numbers` を加え、CI の action が既定でこれを実行するようにした（[adr-guard の ADR 0018「重複したADRの番号の修復」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0018-repair-duplicate-adr-numbers.md)）。
重複を直す `adr-guard renumber` と、番号の付けかえを許す `--allow-renumber` もあわせて加えた。
v0.9.1 は `renumber` の誤報を直した。

v0.10.0 は、修飾子の付いた ADR の参照を解釈するようにした（[adr-guard の ADR 0019「モジュールで修飾したADRの参照」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0019-module-qualified-adr-references.md)）。
`ADR NNNN` の直前の語（空白一つで区切ったもの）が `-` を含めばモジュール（`golem-parser ADR 0002` は `docs/golem-parser/adr/` の ADR）、`/` を含めばディレクトリとみなし、修飾子をリンクのテキストに含める。
`links` と pre-commit のフックは、ディレクトリや ADR が存在しない修飾子付きの参照と、リンクの外に出た修飾子（`golem-parser [ADR 0002](...)`）を報告する。
シンボリックリンクの `.md` は検査しなくなった（[adr-guard の ADR 0020「シンボリックリンクの文書を飛ばす」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0020-skip-symlinked-documents.md)）。

peg-hs の ADR は Golem の ADR を `golem-parser ADR 0002` の形で参照している（[ADR 0021](0021-error-recovery.md)）。
これまでの adr-guard は修飾子を見ないので、これらの参照に peg-hs 自身の ADR へのリンク（`golem-parser [ADR 0002](0002-standalone-code-generator.md)`）を付けていた。
リンク先は Golem の ADR ではなく、誤りである。
v0.10.0 の `adr-guard links` は、main のままでこれらを報告して失敗する。
手元の adr-guard が v0.10.0 になったので、CI と手元の版をそろえるため、版を上げ、誤ったリンクを直す。

## 実装すること

- CI の action を `tett23/adr-guard@v0.10.0` にする。`allow-status: true` と `allow-links: true` は残し、`check-numbers` は既定（実行する）のままとする
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする
- [ADR 0021](0021-error-recovery.md) の Golem の ADR への参照を、修飾子をリンクのテキストに含めた、Golem のリポジトリの ADR への外部リンク（`[golem-parser ADR 0002](https://github.com/tett23/golem/blob/main/docs/golem-parser/adr/0002-parser-on-peg-hs.md)`）にする。リンクだけの変更なので、`--allow-links` でコミットする
- CONTRIBUTING（英語と日本語）の adr-guard の導入のコマンドを `cargo install --git https://github.com/tett23/adr-guard --tag v0.10.0` にし、版の決まりと `adr` のジョブの説明の参照をこの ADR にする
- CONTRIBUTING（英語と日本語）の `adr` のジョブの説明に、ADR の番号の重複も検査することを書く
- CONTRIBUTING（英語と日本語）の「ADR へのリンク」に、ほかのリポジトリの ADR への参照は修飾子をリンクのテキストに含めた外部リンクにすることを書く
- `docs/specifications.md` の adr-guard の版を v0.10.0 にし、この ADR へリンクする
- CI の YAML のコメントの ADR の並びにこの ADR を加える
- [ADR 0060](0060-adr-guard-v0.8.3.md) のステータスの行を、版の更新がこの ADR に移ったことを示す形に変える

## 実装しないこと

- peg-hs にモジュールごとの ADR のディレクトリを作ること。peg-hs の ADR は `docs/adr/` だけに置く
- `--allow-renumber` を pre-commit のフックや CI に付けること。番号の付けかえが要るときに、その作業の中で判断する
- README の変更。README は adr-guard の版にも ADR の検査にも触れていない
- `docs/benchmarks/` と `docs/conformance/`、`docs/editors/` の扱いの変更。[ADR 0059](0059-adr-guard-v0.8.2.md) のとおりとする

## テスト設計

設定の変更なので、自動テストは書かない。
実装の後に、次のことを確かめる。

- v0.10.0 の手元の adr-guard で、`adr-guard links --fix --include-committed` の後に `adr-guard links`、`adr-guard check-status`、`adr-guard check-numbers` が終了コード 0 で終わる
- `docs/benchmarks/` が書きかわっていない
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- `adr-guard check-range origin/main HEAD --allow-status --allow-links` が終了コード 0 で終わる
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが通る

## トレードオフ

- Golem の ADR への外部リンクは `main` を指すので、Golem の側で ADR のファイル名が変わるとリンクが切れる。adr-guard は外部リンクの先を検査しない。代わりに、peg-hs の ADR から誤った自分の ADR へのリンクが無くなる
- CI が ADR の番号の重複で失敗するようになる。並行する pull request が同じ番号の ADR を足したときは、後からマージする側が番号を付けかえる必要がある
- 版の更新ごとに ADR を書く手間がかかる。リンクの検査の規則が変わる更新なので、変更の理由を残す

## 参考文献

- [adr-guard の ADR 0018「重複したADRの番号の修復」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0018-repair-duplicate-adr-numbers.md)
- [adr-guard の ADR 0019「モジュールで修飾したADRの参照」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0019-module-qualified-adr-references.md)
- [adr-guard の ADR 0020「シンボリックリンクの文書を飛ばす」](https://github.com/tett23/adr-guard/blob/main/docs/adr/0020-skip-symlinked-documents.md)
- [adr-guard v0.9.0 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.9.0)
- [adr-guard v0.9.1 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.9.1)
- [adr-guard v0.10.0 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.10.0)
