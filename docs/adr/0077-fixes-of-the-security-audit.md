# ADR 0077: 2026-11-06 のセキュリティ監査の指摘を直す

ステータス: 採択（未実装）

## 文脈

2026-11-06 に、コミット 8441ad7 を対象とするセキュリティ監査を行った（[docs/audits/2026-11-06-security-audit.md](../audits/2026-11-06-security-audit.md)）。
監査は四つの指摘を記録した。

| ID | 重大度 | 指摘 |
|---|---|---|
| SEC-01 | 中 | 再帰的な `fmt` がシンボリックリンクを辿り、対象のディレクトリの外の文法を書き換える |
| SEC-02 | 中 | VS Code の拡張機能が依存する minimatch に、既知の DoS（[GHSA-g3hv-75wg-m249](https://github.com/advisories/GHSA-g3hv-75wg-m249)）がある |
| SEC-03 | 中・条件付き | `parse` の作業ディレクトリを、排他的に、所有者だけが読める形で作っていない |
| SEC-04 | 低 | 言語サーバーが、届ききらないメッセージを上限なく溜める |

リポジトリの持ち主は、四つをすべて直すと決めた。
監査の「防御として確認できた点と追加改善」の節の項目（Actions のコミットの固定、`parse` の説明、Workspace Trust など）は、脆弱性として数えていないので、この ADR では扱わない。

### SEC-01 を確かめたこと

`peg-hs fmt` と `peg-hs lint` は、ディレクトリを渡されるか引数がないと、`packages/peg-cli/app/Files.hs` の `walk` で `.hpeg` を探す。
`walk` は `doesDirectoryExist` でディレクトリかを判定するが、この関数はシンボリックリンクの先を見る。
そのため、探索はリンクを辿ってディレクトリの外に出る。
監査は、一時ディレクトリに `repo/linked -> ../outside` を作り、`repo` で `peg-hs fmt` を実行して、`outside/Victim.hpeg` が整形されたことを記録した（[2026-11-06-symlink-result.json](../audits/2026-11-06-symlink-result.json)）。
循環するリンクでは、探索が終わらないおそれもある。

### SEC-02 を確かめたこと

依存の経路は `vscode-languageclient@10.1.1 -> minimatch@10.2.6` である。
アドバイザリは `>=7.0.0 <11.0.1` を対象とし、修正版を 11.0.1 としている。
2026-11-07 の時点で、vscode-languageclient の最新版（11.0.0）と、GitHub の main の `client/package.json` も、`minimatch: ^10.2.6` を求める。
vscode-languageclient を上げても、修正版にはならない。

npm の `overrides` で minimatch を 11 系に上書きすると、`npm audit` は 0 件になる（2026-11-07 に一時ディレクトリで確かめた）。
ただし、minimatch 11.0 は `makeRe()` を削った（minimatch の changelog）。
vscode-languageclient は、`lib/common/utils/globPattern.js` と `lib/common/fileOperations.js` で `new Minimatch(…)` の後に `makeRe()` を呼ぶ。
この二つは、言語サーバーが glob のパターンを送ってきたときにだけ通る。
具体的には、診断のフィルターやノートブックの文書の選択子のパターン（`diagnostic.js`、`notebook.js`）と、ファイル操作の登録（`fileOperations.js`）である。
拡張機能自身の文書の選択子は `{ language: 'hpeg' }` で、パターンを持たない。
peg-hs の言語サーバーは、これらの機能を宣言せず、パターンを送らない。
同じ理由で、DoS の対象となる glob のパターンも、peg-hs の言語サーバーからは届かない。

## 実装すること

### SEC-01: 自動の探索でシンボリックリンクを辿らない

- `walk` は、シンボリックリンクであるファイルとディレクトリを、探索の対象から外す。判定には `pathIsSymbolicLink` を使う。リンクを辿らないので、探索は探索の始まりのディレクトリの中だけを見て、循環するリンクでも終わる
- 外したリンクは黙って飛ばす。`lint` と `fmt` の出力は変えない
- 利用者が引数でファイルを名指しした場合は、それがリンクでも、これまでどおりリンクの先を読み書きする。名指しは利用者の意図である
- 引数で名指ししたディレクトリがリンクの場合は、そのディレクトリを探索の始まりとしてリンクの先を探索する。その中のリンクは辿らない
- README の `fmt` と `lint` の節、docs/specifications.md に、自動の探索がリンクを辿らないことを書く

### SEC-02: minimatch を修正版に上書きする

- `editors/vscode/package.json` に `"overrides": { "minimatch": "^11.0.1" }` を書き、`package-lock.json` を作り直す
- `makeRe()` を呼ぶ経路は、peg-hs の言語サーバーがパターンを送らない限り通らない。この前提をテストで固定する。言語サーバーの初期化の応答が、`workspace.fileOperations`、`diagnosticProvider`、`notebookDocumentSync` を宣言しないことを、peg-lsp のテストで確かめる。前提が崩れる変更は、このテストが落として知らせる
- `editors/vscode/package.json` の上書きの横に置ける注釈はないので、上書きの理由はこの ADR と `editors/vscode` の README の節に書く
- vscode-languageclient が minimatch の修正版を許すようになったら、上書きを外す。それまでは、上書きを保つ

### SEC-03: `parse` の作業ディレクトリを、所有者だけのものとして排他的に作る

- 作業ディレクトリは、一時ディレクトリの下に、乱数の名前で作る。作るのは `mkdir` 一回で、すでにある名前（リンクを含む）なら失敗させ、別の名前で作り直す。作り直しは 100 回までとし、それでも作れなければ誤りで終わる
- ディレクトリの権限は、作るときに 0700 とする。`directory` パッケージは作るときの権限を指定できず、`setPermissions` は所有者以外の権限を外せないので、POSIX の環境では `unix` パッケージの `createDirectory`（権限を指定する `mkdir`）を使う。`unix` は GHC に同梱のパッケージで、`process` と `directory` がすでに依存しているので、ビルドの計画に新しいパッケージは加わらない
- Windows では `unix` を使わず、これまでどおり `createDirectory` で作る。Windows の一時ディレクトリは利用者ごとにある
- 乱数は、時刻とプロセスの番号から作る。名前の予測を難しくするためのもので、排他性は `mkdir` の失敗で保つ
- 作業ディレクトリは、成功、失敗、例外のどの場合も消す（`bracket` で囲む）
- コンパイルしたパーサーのキャッシュのディレクトリ（[ADR 0036](0036-parse-command.md)）は、利用者のキャッシュのディレクトリの下にあり、所有者だけが書けることを前提とする。この前提を docs/specifications.md に書く

### SEC-04: 言語サーバーのメッセージの大きさに上限を設ける

- ヘッダーの長さの上限を 64 KiB、本文の長さ（`Content-Length`）の上限を 64 MiB とする。届ききらない分を溜める大きさは、この二つの和を超えない
- ヘッダーの終わり（空行）が見つからないまま溜まった分が 64 KiB を超えたとき、または `Content-Length` が 64 MiB を超えたとき、言語サーバーは標準エラーに理由を書き、終了コード 1 で終わる。本文を読み飛ばして続ける形にはしない。どこから次のメッセージが始まるかがわからないからである
- 上限は `Peg.Lsp.Rpc` の公開の定数とし、Haddock に値と理由を書く
- docs/specifications.md の言語サーバーの節に、上限を書く

### 監査の記録

- 監査の記録（`docs/audits/` の文書と証跡）をコミットする。CLAUDE.md の決まりに従い、コミットした後は変えない
- 証跡の再現用のスクリプト `reproduce-symlink.py` は、リポジトリに Python のスクリプトを置かない決まりに合わないので、同じ手順のシェルスクリプト `reproduce-symlink.sh` に書き直し、監査の文書のリンクをそれに合わせてからコミットする。監査の文書の内容は、このリンクのほかは変えない
- この ADR の実装の後に、監査の文書と同じ手順で四つを確かめ直し、結果を `docs/audits/` に新しい記録として置く

## 実装しないこと

- 監査の「追加改善」の項目（GitHub Actions のコミットの SHA への固定、ghcup の bootstrap の検証、`parse` の説明に文法が利用者の権限で動くコードであると書くこと、VS Code の Workspace Trust の方針）
- 自動の探索でリンクを辿る選択肢（`--follow-symlinks` など）
- 名指ししたファイルの書き込みで、リンクを辿らないこと。名指しは利用者の意図である
- CI での `npm audit` の実行。新しいアドバイザリが出るたびに、関係のないプルリクエストの CI が落ちるからである
- vscode-languageclient の置き換えや、minimatch を使わない版への差し替え
- Haskell の依存の、アドバイザリとの網羅的な照合

## テスト設計

先に書き、いまの実装で失敗させる。

### SEC-01（peg-cli のテスト）

一時ディレクトリに次のものを作り、`repo` を作業ディレクトリとして `peg-hs fmt` と `peg-hs lint` を引数なしで実行する。

- 外のディレクトリへのリンク（`repo/linked -> ../outside`、`outside/Victim.hpeg` は整形されていない）：`outside/Victim.hpeg` が変わらないこと。`lint` がそのファイルを報告しないこと
- 外のファイルへのリンク（`repo/Link.hpeg -> ../outside/Victim.hpeg`）：同じく変わらないこと
- 循環するリンク（`repo/loop -> .`）：`fmt` と `lint` が時間内（10 秒）に終わること
- リンクでない `repo/Own.hpeg` は、これまでどおり整形されること
- 名指ししたリンク（`peg-hs fmt Link.hpeg`）は、リンクの先を整形すること

### SEC-02（editors と peg-lsp のテスト）

- `editors/vscode/package-lock.json` で、minimatch が 11.0.1 以上に解決されていることを、editors のテスト（`npm test`）で確かめる
- 言語サーバーの初期化の応答の capabilities が、`workspace.fileOperations`、`diagnosticProvider`、`notebookDocumentSync` を持たないこと（peg-lsp のテスト）
- VS Code での起動、診断、整形、ホバー、semantic tokens は、自動テストにしない。実装の後に、`editors/vscode` の拡張機能を VS Code に入れて手で確かめ、結果を `docs/editors/` に記録する。手で確かめられなかった場合は、確かめていないと記録に書く

### SEC-03（peg-cli のテスト）

- 作業ディレクトリを作る関数を、`parse` から切り出してテストする。umask 022 の下で作ったディレクトリの権限が 0700 であること（POSIX のみ）
- 作ろうとした名前に、すでにディレクトリ、ファイル、リンクがある場合、それを使わずに別の名前で作ること。名前を作る関数を差し替えられる形にして、最初の名前が埋まっている場合を作る
- コンパイルが失敗した場合と、例外が起きた場合にも、作業ディレクトリが消えること

### SEC-04（peg-lsp のテスト）

- ヘッダーや本文が複数の塊に分かれて届く正常な場合が、これまでどおり読めること
- ちょうど上限の大きさのヘッダーと本文は受け付けること
- 空行のないヘッダーが 64 KiB を超えた場合、`Content-Length` が 64 MiB を超えた場合に、言語サーバーが標準エラーに理由を書いて終了コード 1 で終わること

### 監査の確かめ直し

- 自動テストにはしない。実装の後に、監査の文書の「修正後の確認」の手順で四つを確かめ、`docs/audits/` に記録する

## トレードオフ

- 自動の探索でリンクを辿らないので、リンクで置いた文法（別の場所の文法をリンクでまとめる構成）は、`fmt` と `lint` が引数なしでは見つけない。その構成の利用者は、ファイルを名指しする
- minimatch の上書きは、vscode-languageclient が求める版の範囲（`^10.2.6`）の外の版を使う。peg-hs の言語サーバーが glob のパターンを送らない限り、上書きした minimatch の、`makeRe()` を削った変更に当たらない。言語サーバーにファイル操作などの機能を足す変更は、上のテストが落として知らせるので、そのときに上書きを見直す
- `unix` を peg-cli の直接の依存に加える。GHC の同梱のパッケージで、ビルドの計画は変わらないが、cabal ファイルに OS の条件が入る
- 言語サーバーの上限を超える文書（64 MiB を超える文法）は扱えなくなる。そのような文法は現実的でない
- 上限を超えたときに言語サーバーが終わるので、エディタは言語サーバーを起動し直す。壊れたクライアントが送り続ける場合は、起動と終了を繰り返す

## 参考文献

- [docs/audits/2026-11-06-security-audit.md](../audits/2026-11-06-security-audit.md)（監査の記録）
- GitHub Advisory Database, GHSA-g3hv-75wg-m249（minimatch の DoS）. https://github.com/advisories/GHSA-g3hv-75wg-m249
- minimatch, changelog.md（11.0 で `makeRe()` を削ったこと）. https://github.com/isaacs/minimatch/blob/main/changelog.md
- vscode-languageserver-node, `client/package.json` と `client/src/common/utils/globPattern.ts`（minimatch の版の範囲と `makeRe()` の呼び出し）. https://github.com/microsoft/vscode-languageserver-node
- Language Server Protocol Specification 3.17, Base Protocol（ヘッダーと `Content-Length`）. https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#baseProtocol
