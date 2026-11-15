# ADR 0100: adr-guard を v0.13.1 に上げ、ADR のステータスの行を新形式に移す

Status: accepted

## 文脈

[ADR 0076](0076-adr-guard-v0.10.0.md) で、[adr-guard](https://github.com/tett23/adr-guard) を v0.10.0 に上げた。
CI（`.github/workflows/adr.yml`）の action は `tett23/adr-guard@v0.10.0` で、`.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` である。
ADR のステータスの行は、すべて `ステータス: 採択` のような日本語の形（以下、旧形式）で書いてある。

adr-guard の v0.11.0 は、Codex の PreToolUse のフックとして `adr-guard codex-hook` を加えた（[adr-guard の ADR 0021「Codex の PreToolUse hook で、コミット済みのADRと記録の編集を拒否する」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0021-codex-hook.md)）。

v0.12.0 は、ステータスの行の新しい形（以下、新形式）と、状態遷移の検査を加えた（[adr-guard の ADR 0022「状態と遷移を別々の代数的データ型で表す」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0022-status-transitions.md)）。
新形式は `Status: <トークン>` で、トークンは `proposed`、`accepted`、`accepted-pending`、`rejected`、`discarded`、`deprecated`、または `superseded [<変更の JSON 配列>]` である。
変更は `{"part":<変更した部分の名前か null>,"by":[<修正した ADR のリポジトリのルートからのパス>]}` の形で書く。
新しい ADR は、最初に `Status: proposed` でコミットしなければならない。
追加した ADR と、ステータスの行を変えた ADR には、新形式が要る。
旧形式の行は、変えなければそのまま読める。
pre-commit のフックと `check-range` は、ステータスの行の状態遷移（`proposed` から `accepted` へ、`accepted` から `superseded` へ、など）を検査する。
この検査は、`--allow-status`、環境変数 `ADR_GUARD_ALLOW`、コミットのトレーラーでは免除されない。
旧形式を新形式に書き換える移行スクリプト `scripts/migrate-adr-status` は adr-guard のソースにあり、リリースのアーカイブには入っていない。
元の決定から修正した ADR をたどる `adr-guard trace` も加わった（[adr-guard の ADR 0023「trace で元の決定から修正ADRをたどる」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0023-trace-amendments.md)）。

v0.13.0 は、移行スクリプトに、書き換えずに差分だけを示す `--dry-run` を加えた（[adr-guard の ADR 0024「移行スクリプトに --dry-run を設け、失敗を最後まで数える」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0024-migration-dry-run-and-error-count.md)）。
移行スクリプトは移行できない ADR を最後まで数え、`移行できる: N件、移行済み: K件、移行できない: M件` を標準エラーに表示する。
新形式には `superseded-pending`、変更の `kind` と `note`、`https://` で始まる修正先、`trace --list` の6列が加わった（[adr-guard の ADR 0025「新形式のステータス行に、実装待ちの修正、補足、注記、別のリポジトリの修正先を加える」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0025-extend-canonical-status-amendments.md)）。
旧形式の修正先の読み方も広がった（[adr-guard の ADR 0026「旧形式のステータス行の修正先を、リンク先と裸の番号からも読む」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0026-read-more-legacy-references.md)、[adr-guard の ADR 0027「旧形式の `置換（…）` を、修正を受けた状態として読む」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0027-read-legacy-replaced-status.md)）。

v0.13.1 は、移行スクリプトが作る部分名の不具合を直した（[adr-guard の ADR 0028「旧形式の部分名から修飾子と区切りの記号を除き、決められない部分名を移行しない」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0028-fix-legacy-part-names.md)）。
v0.13.0 の移行スクリプトは、部分名に修飾子（`ADR NNNN` の直前の語）、先頭の「。」、末尾の「→」を残すことがあった。
v0.13.1 はこれらを除き、部分名を決められない行は「部分名を決められません」と報告して書かない。

手元の adr-guard は v0.13.1 になっている。
手元の pre-commit のフックは、新しい ADR を旧形式で書くと拒否し、コミットした ADR のステータスの行を旧形式のまま書き換えても拒否する（「調査した事項」）。
そのため、ADR を足すたびに、またステータスの行を変えるたびに、新形式と旧形式が混ざっていく。
CI と手元の版をそろえるため版を上げ、すべての ADR のステータスの行を一度に新形式に移す。

## 調査した事項

次のことを、手元で実行して確かめた。

- `adr-guard -V` は `adr-guard 0.13.1` を表示した。
- 移行スクリプトは、adr-guard の v0.13.1 のソースの `scripts/migrate-adr-status` を使った。このスクリプトは、`cargo run --example migrate_adr_status` で example の `migrate_adr_status` をビルドして実行する。以下では、ビルドした `migrate_adr_status` を直接実行した。
- このリポジトリのルート（origin/main の b57bcd5）で `migrate_adr_status --dry-run` を実行すると、終了コード 0 で終わり、標準エラーの最後の行は `移行できる: 99件、移行済み: 0件、移行できない: 0件` だった。作業ツリーは書きかわらなかった。
  - この ADR の草稿を置いた作業ツリーでは、最後の行は `移行できる: 99件、移行済み: 1件、移行できない: 0件` だった。この ADR は新形式なので、移行済みに数えられる。
  - 差分の行は、v0.13.0（`0096636`）の移行スクリプトを同じコミットで実行したときと同じだった。このリポジトリの部分名は、[adr-guard の ADR 0028](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0028-fix-legacy-part-names.md) の修正の影響を受けない。
  - 99 件のうち、`accepted` が 63 件、`accepted-pending` が 2 件（[ADR 0096](0096-file-names-of-positions-in-messages.md)、[ADR 0097](0097-verify-hpeg-and-generated-haskell-in-lean.md)）、`rejected` が 1 件（[ADR 0040](0040-templates-with-parameterized-rules.md)）、`superseded` が 33 件に移る。
  - [ADR 0076](0076-adr-guard-v0.10.0.md) の行は `Status: accepted` に、[ADR 0060](0060-adr-guard-v0.8.3.md) の `ステータス: 採択→adr-guard の版（v0.10.0）は [ADR 0076](...)` は `Status: superseded [{"by":["docs/adr/0076-adr-guard-v0.10.0.md"],"part":"adr-guard の版（v0.10.0）"}]` に移る。
- 同じコミットの複製で `migrate_adr_status --write` を実行すると、99 件の ADR のステータスの行だけが書きかわった（`99 files changed, 99 insertions(+), 99 deletions(-)`）。その後の `--dry-run` は `移行できる: 0件、移行済み: 99件、移行できない: 0件` を表示した。
  - 書き換えた後の複製で、`adr-guard links`、`adr-guard check-status`、`adr-guard check-numbers` は終了コード 0 で終わった。`adr-guard unimplemented` は [ADR 0096](0096-file-names-of-positions-in-messages.md) と [ADR 0097](0097-verify-hpeg-and-generated-haskell-in-lean.md) を表示した。
  - 書き換えをステージして `adr-guard pre-commit --allow-status --allow-links` は終了コード 0 で終わった。コミットした後、`adr-guard check-range HEAD~1 HEAD --allow-status --allow-links` も終了コード 0 で終わった。
- 移行していない複製（別のリポジトリ shorten-path で試した）で、手元の adr-guard（v0.13.1）の pre-commit は次を拒否した。
  - `ステータス: 提案` の新しい ADR。診断は `` 新形式のステータス行は `Status: ` で始めてください `` だった。
  - `Status: accepted` の新しい ADR。診断は `許可されていない状態遷移: Absent -> accepted` だった。
  - コミットした ADR の `ステータス: 採択` を、旧形式のまま `ステータス: 採択→…` に書き換えた変更。診断は `` 新形式のステータス行は `Status: ` で始めてください `` で、終了コードは 1 だった。
  - `Status: proposed` の新しい ADR は許可した。
- 実装の手順を、origin/main の複製で次のとおりに試した。どの段階でも pre-commit（`--allow-status --allow-links`）は終了コード 0 で終わった。
  1. この ADR を `Status: proposed` のまま足してコミットした。
  2. 移行スクリプトの `--write` を実行した。最後の行は `移行できる: 99件、移行済み: 1件、移行できない: 0件` で、この ADR は移行済みに数えられた。
  3. この ADR を `Status: accepted` に、[ADR 0076](0076-adr-guard-v0.10.0.md) を「実装すること」に書いた `superseded` の行にして、移行とあわせて一つのコミットにした。
  - その後、`adr-guard check-range <origin/main> HEAD --allow-status --allow-links`、`adr-guard links`、`adr-guard check-status`、`adr-guard check-numbers` は終了コード 0 で終わった。
  - 移行を一つのコミットにし、この ADR の採択と [ADR 0076](0076-adr-guard-v0.10.0.md) の変更を次のコミットに分けた場合も、同じ結果だった。
- v0.13.1 の `action.yml` の入力は `base`、`head`、`version`、`allow-status`、`allow-links`、`links`、`check-status`、`check-numbers`、`allow-renumber` で、v0.10.0 から名前は変わっていない。

## 実装すること

- CI の action を `tett23/adr-guard@v0.13.1` にする。`allow-status: true` と `allow-links: true` は残し、ほかの入力は付けない
- CI の YAML のコメントの ADR の並びにこの ADR を加える
- このリポジトリのルートで、adr-guard の v0.13.1 の移行スクリプトを `--dry-run` で実行し、`移行できない: 0件` で終わることを確かめてから、`--write` で全 ADR のステータスの行を新形式に書き換える。adr-guard のソースから実行するときは `scripts/migrate-adr-status --dry-run` と `scripts/migrate-adr-status --write` である。書き換えの結果は手で直さない
- [ADR 0076](0076-adr-guard-v0.10.0.md) のステータスの行を `Status: superseded [{"by":["docs/adr/0100-adr-guard-v0.13.1.md"],"part":"adr-guard の版（v0.13.1）"}]` にする。部分の名前は、移行した後の [ADR 0043](0043-adr-guard-v0.8.0.md)、[ADR 0047](0047-adr-guard-v0.8.1.md)、[ADR 0059](0059-adr-guard-v0.8.2.md)、[ADR 0060](0060-adr-guard-v0.8.3.md) のステータスの行の「adr-guard の版（修正した ADR の版）」に倣う
- `.githooks/pre-commit` は `exec adr-guard pre-commit --allow-status --allow-links` のままとする
- CONTRIBUTING（英語と日本語）を次のとおりに直す
  - adr-guard の導入のコマンドを `cargo install --git https://github.com/tett23/adr-guard --tag v0.13.1` にし、版の決まりの参照をこの ADR にする
  - ADR の雛形のステータスの行を `Status: proposed` にし、ステータスのトークン（`proposed`、`accepted`、`accepted-pending`、`rejected`、`discarded`、`superseded`）を説明する
  - 新しい ADR は最初に `Status: proposed` でコミットし、採択は後のコミットで `accepted`（まだ実装していなければ `accepted-pending`）にすることを書く
  - ステータスの行を行頭が `Status:` の行にし、決定を変えたときの元の ADR のステータスの行を `superseded` の形で書くことを書く
  - pre-commit のフックと CI が状態遷移を検査し、その検査は `ADR_GUARD_ALLOW` とトレーラーでは免除されないことを書き、この ADR へリンクする
- `docs/specifications.md` の adr-guard の版を v0.13.1 にし、この ADR へリンクする

## 実装しないこと

- Codex のフック（`adr-guard codex-hook`）の導入。peg-hs は Claude Code のフックもリポジトリに置いていない
- 移行スクリプトの結果を超えた、ステータスの行の書き直し（`kind` や `note` を足すことなど）
- ADR の本文と、ステータスの行以外の行の変更
- README の変更。README は adr-guard の版にも ADR の検査にも触れていない
- CLAUDE.md の変更。CLAUDE.md の「ステータスを採択にしたとき」は状態の名前を指し、ステータスの行の書き方には触れていない
- `docs/benchmarks/` と `docs/conformance/`、`docs/editors/` の扱いの変更。[ADR 0059](0059-adr-guard-v0.8.2.md) のとおりとする

## 不変条件

なし。設定の値と移行の手順を決める ADR で、入力によって変わる振る舞いを足さない。

## テスト設計

設定と文書の変更なので、自動テストは書かない。
実装の後に、次のことを確かめる。

- 書き換える前に移行スクリプトの `--dry-run` が終了コード 0 で終わり、`移行できない: 0件` を表示する。この ADR は新形式なので「移行済み」に数えられる。書き換えた後の `--dry-run` は `移行できる: 0件` を表示する
- v0.13.1 の手元の adr-guard で、`adr-guard links --fix` の後に `adr-guard links`、`adr-guard check-status`、`adr-guard check-numbers` が終了コード 0 で終わる
- `adr-guard unimplemented` の出力が、書き換える前と同じである（いまは [ADR 0096](0096-file-names-of-positions-in-messages.md) と [ADR 0097](0097-verify-hpeg-and-generated-haskell-in-lean.md)）
- `adr-guard trace docs/adr/0076-adr-guard-v0.10.0.md` が、この ADR への部分「adr-guard の版（v0.13.1）」の辺を表示する
- `docs/benchmarks/` が書きかわっていない
- 変更をステージして `.githooks/pre-commit` が終了コード 0 で終わる
- `adr-guard check-range origin/main HEAD --allow-status --allow-links` が終了コード 0 で終わる
- `.github/workflows/adr.yml` が YAML として読める
- pull request の CI で `adr` のジョブが v0.13.1 の action で通る

## トレードオフ

- ADR のステータスの行が英語のトークンと JSON になり、日本語の形より読みにくい。代わりに、状態遷移の検査と `adr-guard trace` が使え、旧形式と新形式が混ざらない
- 一度に 99 件の ADR のステータスの行を書き換えるので、差分が大きい。書き換えは移行スクリプトの結果だけで、手で直さないので、`--dry-run` の差分と比べて確かめられる
- 並行するブランチが ADR のステータスの行を変えていると、移行とぶつかる。[ADR 0097](0097-verify-hpeg-and-generated-haskell-in-lean.md) のように実装中の ADR は、後からマージする側が新形式で直す
- 状態遷移の検査は `ADR_GUARD_ALLOW` とトレーラーで免除されないので、誤ったステータスを緊急に戻す手段が減る
- 版の更新ごとに ADR を書く手間がかかる。ステータスの行の書き方と、コミットの手順が変わる更新なので、変更の理由を残す

## 参考文献

- [adr-guard の ADR 0021「Codex の PreToolUse hook で、コミット済みのADRと記録の編集を拒否する」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0021-codex-hook.md)
- [adr-guard の ADR 0022「状態と遷移を別々の代数的データ型で表す」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0022-status-transitions.md)
- [adr-guard の ADR 0023「trace で元の決定から修正ADRをたどる」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0023-trace-amendments.md)
- [adr-guard の ADR 0024「移行スクリプトに --dry-run を設け、失敗を最後まで数える」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0024-migration-dry-run-and-error-count.md)
- [adr-guard の ADR 0025「新形式のステータス行に、実装待ちの修正、補足、注記、別のリポジトリの修正先を加える」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0025-extend-canonical-status-amendments.md)
- [adr-guard の ADR 0026「旧形式のステータス行の修正先を、リンク先と裸の番号からも読む」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0026-read-more-legacy-references.md)
- [adr-guard の ADR 0027「旧形式の `置換（…）` を、修正を受けた状態として読む」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0027-read-legacy-replaced-status.md)
- [adr-guard の ADR 0028「旧形式の部分名から修飾子と区切りの記号を除き、決められない部分名を移行しない」](https://github.com/tett23/adr-guard/blob/v0.13.1/docs/adr/0028-fix-legacy-part-names.md)
- [adr-guard v0.11.0 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.11.0)
- [adr-guard v0.12.0 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.12.0)
- [adr-guard v0.13.0 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.13.0)
- [adr-guard v0.13.1 のリリース](https://github.com/tett23/adr-guard/releases/tag/v0.13.1)
