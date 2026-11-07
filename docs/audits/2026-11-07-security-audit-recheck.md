# セキュリティ監査の確かめ直し（2026-11-07）

[2026-11-06 のセキュリティ監査](2026-11-06-security-audit.md)の四つの指摘を、[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) の実装の後に、監査の「修正後の確認」の手順で確かめ直した。
対象は、ブランチ `impl-0077-security` のコミット `c28a036` と同じ内容の作業ツリーである（[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) を加えたコミット `224f9ee` に、その実装を加えたもの）。
ローカルの macOS / arm64、GHC 9.10.3、cabal 3.16.1.0、Node v26.11.1、npm 11.20.0 で実施した。

## 結果

| ID | 重大度 | 指摘 | 確かめ直しの結果 |
| --- | --- | --- | --- |
| SEC-01 | 中 | 再帰的な `fmt` がシンボリックリンクを辿り、対象ディレクトリ外を書き換える | 解消。外へのディレクトリのリンク、ファイルのリンク、循環するリンクのどれでも、外のファイルは変わらず、探索は終わった |
| SEC-02 | 中 | VS Code 拡張の依存する minimatch に既知の DoS | 解消。ロックファイルは minimatch 11.0.5 に解決し、`npm audit` は 0 件。VS Code での手の確認は未実施 |
| SEC-03 | 中・条件付き | `parse` の作業ディレクトリを排他的・非公開に作成していない | 解消。umask 022 の下で作業ディレクトリの権限は 0700 で、既存の名前は使わず、失敗の後に一時ディレクトリに何も残らなかった |
| SEC-04 | 低 | LSP の未完了フレームを無制限に保持する | 解消。上限を超える入力で、言語サーバーは理由を標準エラー出力に書いて終了コード 1 で終わった。ちょうど上限のヘッダーは受け付けた |

以下の節に、実行したコマンドと出力を記録する。
`peg-hs` は、この作業ツリーで `cabal-3.16.1.0 build` した実行ファイル（`cabal-3.16.1.0 list-bin exe:peg-hs` の示すもの）である。
以下では、その絶対パスを `$EXE` と書く。

## SEC-01: 自動探索がシンボリックリンクを辿る

### 外へのディレクトリのリンク

監査の再現用スクリプトをそのまま実行した。

```sh
sh docs/audits/reproduce-symlink.sh "$EXE"
```

```text
case: directory symlink escape
exit: 0
outside_changed: false
--- before
%module M
S :: ()
S <-   'a'    { () }
--- after
%module M
S :: ()
S <-   'a'    { () }
--- stderr
```

監査では `outside_changed: true` だった（[2026-11-06-symlink-result.json](2026-11-06-symlink-result.json)）。
実装の後は `false` で、`repo/linked -> <一時ディレクトリ>/outside` の先の `Victim.hpeg` は整形されなかった。

### 外へのファイルのリンクと、循環するリンク

一時ディレクトリに次の三つを置き、`repo` で `fmt --check`、`lint`、`fmt` を引数なしで実行した。
その後、ファイルを名指しした `fmt Link.hpeg` も実行した。

- `repo/Own.hpeg`：リンクでない、整形されていない文法
- `repo/Link.hpeg -> ../outside/Victim.hpeg`：外のファイルへのリンク。`Victim.hpeg` は整形されていない
- `repo/loop -> .`：循環するリンク

実行したスクリプト（コミットしていない）は次のとおりである。

```sh
#!/bin/sh
set -eu
exe=$1
root=$(mktemp -d "${TMPDIR:-/tmp}/peg-recheck-XXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir "$root/repo" "$root/outside"
printf "%%module M\nS :: ()\nS <-   'a'    { () }\n" > "$root/outside/Victim.hpeg"
cp "$root/outside/Victim.hpeg" "$root/before.hpeg"
printf "%%module M\nS :: ()\nS <-   'b'    { () }\n" > "$root/repo/Own.hpeg"
ln -s ../outside/Victim.hpeg "$root/repo/Link.hpeg"
ln -s . "$root/repo/loop"
ls -l "$root/repo" | sed "s|$root|<root>|g" | tail -n +2 | awk '{print $1, $9, $10, $11}'
echo "--- fmt --check"
set +e
(cd "$root/repo" && "$exe" fmt --check); echo "exit: $?"
echo "--- lint"
(cd "$root/repo" && time -p "$exe" lint) 2>&1; echo "exit: $?"
echo "--- fmt"
(cd "$root/repo" && time -p "$exe" fmt) 2>&1; echo "exit: $?"
set -e
if cmp -s "$root/before.hpeg" "$root/outside/Victim.hpeg"; then echo "outside_changed: false"; else echo "outside_changed: true"; fi
echo "--- repo/Own.hpeg after"; cat "$root/repo/Own.hpeg"
echo "--- fmt Link.hpeg (named)"
(cd "$root/repo" && "$exe" fmt Link.hpeg); echo "exit: $?"
if cmp -s "$root/before.hpeg" "$root/outside/Victim.hpeg"; then echo "outside_changed: false"; else echo "outside_changed: true"; fi
```

```text
lrwxr-xr-x@ Link.hpeg -> ../outside/Victim.hpeg
lrwxr-xr-x@ loop -> .
-rw-r--r--@ Own.hpeg  
--- fmt --check
Own.hpeg
exit: 1
--- lint
real 0.02
user 0.00
sys 0.00
exit: 0
--- fmt
real 0.02
user 0.00
sys 0.00
exit: 0
outside_changed: false
--- repo/Own.hpeg after
%module M

S :: ()
S <- 'b' { () }
--- fmt Link.hpeg (named)
exit: 0
outside_changed: true
```

引数なしの探索は `Own.hpeg` だけを一度見つけ、`Link.hpeg` と `loop` の先を見なかった。
`lint` と `fmt` は、循環するリンクがあっても 0.02 秒で終わった。
外の `Victim.hpeg` は変わらず、リンクでない `Own.hpeg` は整形された。
最後の `outside_changed: true` は、名指ししたリンクの先を整形した結果であり、[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) の決めたとおりの動作である。

実装の前のコードでは、同じ構成の `fmt --check` が `loop/Own.hpeg`、`loop/loop/Own.hpeg` のように同じファイルを 33 回列挙した（peg-cli のテストを実装の前に動かして失敗させたときの出力）。
監査が測っていなかった循環するリンクの影響は、macOS ではリンクの解決の回数の上限で止まる重複の列挙だった。

## SEC-02: minimatch の既知 DoS

### ロックファイルと監査

`editors/vscode/package.json` に `"overrides": { "minimatch": "^11.0.1" }` を加え、`npm install --package-lock-only --ignore-scripts` でロックファイルを作り直した。
監査と同じコマンドで、二つのディレクトリの依存を確かめた。

```sh
(cd editors && npm audit --package-lock-only --ignore-scripts --json)
(cd editors/vscode && npm audit --package-lock-only --ignore-scripts --json)
```

どちらも終了コード 0 で、`metadata.vulnerabilities.total` は 0 だった。
出力は [2026-11-07-npm-editors.json](2026-11-07-npm-editors.json) と [2026-11-07-npm-vscode.json](2026-11-07-npm-vscode.json) に置いた。
`npm ci` で入れた後の `npm audit`（ロックファイルだけでなく `node_modules` を見るもの）も、二つのディレクトリで `found 0 vulnerabilities` だった。

`editors/vscode` で `npm ci --ignore-scripts` の後に解決した版は次のとおりである。

```text
$ npm ls minimatch
peg-hs@0.1.0 /private/tmp/claude-501/impl-0077/editors/vscode
└─┬ vscode-languageclient@10.1.1
  └── minimatch@11.0.5
```

### makeRe() の経路

入れた minimatch 11.0.5 で、`Minimatch` の `makeRe` がないことを確かめた。

```text
$ node -e "const m=require('minimatch'); console.log(require('minimatch/package.json').version, typeof m.Minimatch, typeof new m.Minimatch('*.x').makeRe)"
11.0.5 function undefined
```

vscode-languageclient 10.1.1 が `makeRe()` を呼ぶのは、`lib/common/fileOperations.js:111` と `lib/common/utils/globPattern.js:58` の二か所である（`grep -rn makeRe node_modules/vscode-languageclient/lib`）。
[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) のとおり、この二つは言語サーバーが glob のパターンを送る機能でだけ通る。
言語サーバーの初期化の応答が `workspace.fileOperations`、`diagnosticProvider`、`notebookDocumentSync` を持たないことは、peg-lsp のテスト「the server declares no capability that makes the client match glob patterns (SEC-02)」で確かめている（下の「自動テスト」の節）。

### VS Code での確認

VS Code に拡張機能を入れての確認（起動、診断、整形、ホバー、semantic tokens、ファイル監視）は、**まだ行っていない**。
リポジトリの持ち主が行い、結果を `docs/editors/` に記録する。
それまで、上書きした minimatch で拡張機能が VS Code で動くことは未確認である。

## SEC-03: コンパイル用一時ディレクトリの保護不足

### 権限と後始末

`PATH` の先頭に偽の `ghc` を置いて `peg-hs parse` を実行し、作業ディレクトリの権限と所有者を `ghc` の中から調べた。
偽の `ghc` は、`--numeric-version` に `9.10.3` と答え、コンパイルの呼び出しでは `-i` の引数から作業ディレクトリを求めて `stat` し、終了コード 1 で失敗する。
`TMPDIR` と `XDG_CACHE_HOME` は空の一時ディレクトリにし、umask は 022 にした。

```sh
#!/bin/sh
set -eu
exe=$1
root=$(mktemp -d "${TMPDIR:-/tmp}/peg-recheck-XXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir "$root/bin" "$root/tmp" "$root/cache" "$root/work"
cat > "$root/bin/ghc" <<'GHC'
#!/bin/sh
if [ "$1" = "--numeric-version" ]; then echo 9.10.3; exit 0; fi
for a in "$@"; do
  case $a in -i*) src=${a#-i};; esac
done
work=$(dirname "$src")
echo "fake ghc: working directory $(basename "$work"), mode $(stat -f '%Lp' "$work"), owner $(stat -f '%Su' "$work")" >&2
exit 1
GHC
chmod +x "$root/bin/ghc"
printf "%%module M\nS :: ()\nS <- 'a'\n" > "$root/work/G.hpeg"
printf "a" > "$root/work/in.txt"
umask 022
echo "umask: $(umask)"
set +e
(cd "$root/work" && PATH="$root/bin:$PATH" TMPDIR="$root/tmp/" XDG_CACHE_HOME="$root/cache" "$exe" parse G.hpeg in.txt)
echo "exit: $?"
set -e
echo "left in TMPDIR: $(ls -A "$root/tmp" | wc -l | tr -d ' ')"
```

```text
umask: 0022
fake ghc: working directory peg-hs-parse-80a0c50d3df0f3d9, mode 700, owner tett23
exit: 1
left in TMPDIR: 0
```

作業ディレクトリは、乱数の名前、権限 0700 で作られ、コンパイルが失敗した後に消えた。
監査が指摘した、umask 022 で 0755 になる経路は塞がった。

### 既存のパスを使わないこと

作業ディレクトリの名前は乱数なので、実行ファイルの外から次の名前を予測して先に置くことはできない。
そのため、既存のパスを使わないことは、名前を作る関数を差し替えられる peg-cli のテストで確かめた。
テスト「a name taken by a directory, a file or a link is not used, and another is made」は、最初の四つの名前にディレクトリ、ファイル、ディレクトリへのリンク、先のないリンクを置き、五つ目の名前で作られることと、置いた四つが変わらないこと（先のないリンクの先も作られないこと）を確かめる。
テスト「when 100 names are taken, it fails」は、すべての名前が埋まっている場合に 100 回試して誤りで終わることを確かめる。
テスト「it is removed after a success, a failure and an exception」は、成功、失敗、例外のどの場合も作業ディレクトリが消えることを確かめる。
いずれも下の「自動テスト」の節の実行で成功した。

共有の一時ディレクトリで別の利用者が競合する攻撃は、監査と同じく再現していない。
Linux での確認もしていない。

## SEC-04: LSP フレームのサイズ制限がない

`peg-hs lsp` の標準入力に作ったバイト列を送り、入力を閉じずに 5 秒開けたまま、終了コードと標準エラー出力を見た。
入力を閉じないのは、入力の終わりで終わる通常の終了（これも終了コード 1）と区別するためである。

```sh
( printf 'Content-Length: 2\r\nX-Padding: '; head -c 70000 /dev/zero | tr '\0' x; sleep 5 ) | "$EXE" lsp; echo "exit: $?"
( printf 'Content-Length: 67108865\r\n\r\n'; sleep 5 ) | "$EXE" lsp; echo "exit: $?"
( printf 'Content-Length: 99999999999999999999999\r\n\r\n'; sleep 5 ) | "$EXE" lsp; echo "exit: $?"
```

```text
peg-hs lsp: a message header longer than 65536 bytes
exit: 1
peg-hs lsp: a message body of 67108865 bytes, longer than 67108864 bytes
exit: 1
peg-hs lsp: a message body of 99999999999999999999999 bytes, longer than 67108864 bytes
exit: 1
```

三つ目は、`Int` に収まらない `Content-Length` が桁あふれで小さな数として読まれないことを確かめたものである。

ちょうど上限の大きさのヘッダー（終わりの空行を含めて 65536 バイト）に `initialize` の要求を続けたファイルを送ると、言語サーバーは応答を返した。

```sh
body='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}'
start="Content-Length: ${#body}\r\nX-Padding: "
pad=$((65536 - 4 - $(printf "$start" | wc -c)))
{ printf "$start"; head -c $pad /dev/zero | tr '\0' x; printf '\r\n\r\n%s' "$body"; } > limit.in
echo "header bytes: $(( $(wc -c < limit.in) - ${#body} ))"
"$EXE" lsp < limit.in > limit.out 2> limit.err; echo "exit: $?"
head -c 60 limit.out; echo; echo "stderr bytes: $(wc -c < limit.err)"
```

```text
header bytes: 65536
exit: 1
Content-Length: 586

{"jsonrpc":"2.0","id":1,"result":{"ca
stderr bytes:        0
```

ここでの終了コード 1 は、`shutdown` なしに入力が終わった通常の終了であり、標準エラー出力は空である。
ちょうど 64 MiB の本文を受け付けることと、分かれて届くヘッダーと本文を読めることは、peg-lsp のテストで確かめた。

## 自動テスト

実装の後に、次のコマンドですべてのテストを実行し、すべて成功した。

```sh
cabal-3.16.1.0 test all
(cd editors && npm ci && npm test)
```

| テストスイート | 結果 |
| --- | --- |
| peg-runtime-test | 56 件成功 |
| peg-grammar-test | 656 件成功 |
| peg-codegen-test | 198 件成功 |
| peg-cli-test | 114 件成功（[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) の 12 件を含む） |
| peg-lsp-test | 151 件成功（[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) の 11 件を含む） |
| complexity | 7 件成功 |
| json-conformance | 308 件成功 |
| lua-conformance | 93 件成功 |
| toml-conformance | 696 件成功 |
| commonmark-conformance | 成功（652 例中 652 例） |
| editors（`npm test`） | tree-sitter のテストと、node のテスト 21 件が成功（[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) の 2 件を含む） |

[ADR 0077](../adr/0077-fixes-of-the-security-audit.md) のテストは、実装の前に書いた。
peg-cli のテストのうち、SEC-01 の 4 件（名指ししたリンクの 1 件を除く）と SEC-04 の 2 件は、実装の前の `Files.hs` と言語サーバーで失敗した。
SEC-04 の 2 件は、入力を開けたまま 10 秒待っても言語サーバーが終わらなかった。
peg-lsp の SEC-04 のテストは、テストする定数と型がまだなかったので、コンパイルできずに失敗した。
SEC-03 のテストは、作業ディレクトリを作る関数の新しいモジュールを先に加えてから動かしたので、実装の前の失敗は確かめていない。このモジュールを `parse` から使う変更は、その後に加えた。
editors のテストは、ロックファイルの minimatch 10.2.6 で失敗した。
SEC-02 の capabilities のテストと、名指ししたリンクのテスト、`parse` がコンパイルの失敗の後に何も残さないテストは、いまの動作を固定するもので、実装の前から成功する。

## 実施した検証と限界

| 検証 | 結果 |
| --- | --- |
| 外へのディレクトリのリンク（`reproduce-symlink.sh`） | `outside_changed: false` |
| 外へのファイルのリンク、循環するリンク | 外のファイルは不変、探索は 0.02 秒で終了 |
| `editors` の npm audit | 0 件 |
| `editors/vscode` の npm audit | 0 件（minimatch 11.0.5） |
| `parse` の作業ディレクトリ（umask 022） | 権限 0700、失敗の後に残らない |
| 既存のパスを使わないこと | peg-cli のテストで確認。実行ファイルでの競合は未再現 |
| LSP の上限 | 超過で終了コード 1 と理由。上限ちょうどは受理 |
| VS Code での手の確認 | 未実施 |

確かめていないことは次のとおりである。
VS Code の実機での拡張機能の動作、Linux での確認、共有の一時ディレクトリでの競合攻撃、Windows での作業ディレクトリの作成（`unix` を使わない経路）は、今回の範囲外である。
