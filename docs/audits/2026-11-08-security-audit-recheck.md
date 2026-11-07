# セキュリティ監査の確かめ直し（2026-11-08）

[2026-11-07 のセキュリティ監査](2026-11-07-security-audit.md)の四つの指摘を、[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の実装の後に、監査の「修正後の確認」と ADR の「実装の後に測って記録すること」の手順で確かめ直した。
対象は、ブランチ `impl-0080` の作業ツリーである（main の `e166337` に [ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の実装を加え、その後の main を取り込んだもの）。
ローカルの macOS / arm64、GHC 9.10.3、cabal 3.16.1.0、Node v26.11.1、Deno 2.9.7 で実施した。
wasm は、CI と同じ ghc-wasm-meta のコミット（`8079eb96`）の `nix shell` で `scripts/build-wasm.sh` を動かしてビルドした。

## 結果

| ID | 重大度 | 指摘 | 確かめ直しの結果 |
| --- | --- | --- | --- |
| SEC-05 | 中（条件付き） | `%module`、`%export`、ファイル名の値が生成物にそのまま出る | 解消。監査の文法は終了状態 1 の誤りになり、ファイルを書かなかった。監査の wasm の要求は診断を返し、`module` は `null` だった |
| SEC-06 | 中 | 入れ子の深い文法と JSON が超線形の時間とメモリを使う | 解消。監査の入力は、`gen`、`fmt --check`、`lint`、言語サーバー、wasm のどれでも 0.1 秒前後で誤りになった |
| SEC-07 | 低（情報） | 範囲外の長さで reactor が終了する | 解消。監査の harness の `neg` と `huge` は JSON の誤りを返し、その後の呼び出しも応えた |
| SEC-08 | 低〜中 | `peg-hs.path` をワークスペースの設定で上書きできる | `package.json` の宣言を直し、テストで固定した。VS Code の実機での確認は未実施 |

以下の節に、実行したコマンドと出力を記録する。
`peg-hs` は、この作業ツリーで `cabal-3.16.1.0 build` した実行ファイル（`cabal-3.16.1.0 list-bin exe:peg-hs` の示すもの）である。
以下では、その絶対パスを `$EXE` と書く。
時間は、コマンドの前後の時刻の差で測った一回の値である。

## SEC-05: 生成物に出る値

監査の証跡の文法（[2026-11-07-inj-module.hpeg.txt](2026-11-07-inj-module.hpeg.txt)）を `inj-module.hpeg` という名前で写し、`gen` にかけた。

```text
$ "$EXE" gen inj-module.hpeg -o inj-module.hs; echo "exit: $?"; ls inj-module.hs
inj-module.hpeg:1:9: error: %module expects a module name, but got M (parse) where evil = 1 {-
inj-module.hpeg:2:9: error: %export expects export items, but got evil2) where evil2 = 2 {-
exit: 1
ls: inj-module.hs: No such file or directory
```

監査では、この二つの値が生成物の見出しとエクスポートの一覧にそのまま出た（[生成物](2026-11-07-inj-module.hs)）。
実装の後は、どちらも値の位置の誤りになり、`inj-module.hs` は書かれなかった。

改行を含むファイル名は、peg-cli のテスト「a file name with a newline is an error, and gen writes nothing (SEC-05)」で確かめた。
名前 `x.hpeg\nimport Evil\n--` の文法を `gen` にかけると、`the file name contains a control character` の誤りで終了状態 1 になり、出力のファイルはできなかった。

監査の証跡の wasm の要求（[2026-11-07-srcname-req.json](2026-11-07-srcname-req.json)）を、監査の harness（[reproduce-wasm-length.ts](reproduce-wasm-length.ts)）の `file` で、ビルドした wasm の `analyze` に渡した。

```text
$ PEG_HS_WASM=peg-hs.wasm deno run --allow-read --allow-env docs/audits/reproduce-wasm-length.ts file docs/audits/2026-11-07-srcname-req.json analyze
ms 138.6 len 602 {"diagnostics":[{"severity":"error","line":1,"column":1,"message":"the file name contains a control character"}],"ast":{"kind":"Grammar", ...
```

harness は応答の先頭の 300 文字だけを表示するので、`module` が `null` であることは peg-wasm のテスト「the request of the audit with a newline in sourceName gets a diagnostic and no module (SEC-05)」で確かめた。
制御文字を含まない名前では、すべての生成物の golden と、wasm の `module` と `peg-hs gen` の出力の一致のテストが、実装の前と同じバイト列で通った。

## SEC-06: 入れ子の深い入力

### 監査の入力

監査の証跡のスクリプト（[reproduce-deep-nesting.sh](reproduce-deep-nesting.sh)）が書く `p<N>.hpeg` と、同じ形で N を 256 にした `p256.hpeg` を使った。

```sh
sh docs/audits/reproduce-deep-nesting.sh "$dir"
awk -v n=256 'BEGIN { printf "%%module M\nS <- "; for (i = 0; i < n; i++) printf "("; printf "%c%s%c", 39, "a", 39; for (i = 0; i < n; i++) printf ")"; printf "\n" }' > "$dir/p256.hpeg"
```

| 入力 | `gen` | `fmt --check` | `lint` | 監査の `gen` | 監査の `fmt --check` |
| --- | --- | --- | --- | --- | --- |
| p256（256 段、上限の内側） | 0.07 秒、生成した | 0.09 秒 | 0.05 秒 | （未計測） | （未計測） |
| p1000 | 0.05 秒、誤り | 0.05 秒、誤り | 0.05 秒、誤り | 0.24 秒 | 1.05 秒 |
| p2000 | 0.05 秒、誤り | 0.06 秒、誤り | 0.05 秒、誤り | 0.53 秒 | 4.78 秒 |
| p4000 | 0.05 秒、誤り | 0.04 秒、誤り | 0.05 秒、誤り | 1.49 秒 | 10.21 秒 |
| p8000 | 0.06 秒、誤り | 0.04 秒、誤り | 0.05 秒、誤り | 6.03 秒 | 30 秒で終わらず |

誤りは、どの入力でも 257 段目の括弧の位置の `p<N>.hpeg:2:262: error: the expression nests deeper than 256` だった。
p256 の `fmt --check` の終了状態 1 は、文法が整形されていないためで、誤りではない。
入れ子 100,000 段の文法を `gen`、`fmt --check`、`lint` にかけるテスト（peg-cli）も、10 秒の制限の中で同じ誤りを返した。

### 言語サーバー

`peg-hs lsp` に、`initialize`、`initialized`、`didOpen`、`formatting`、`shutdown`、`exit` のフレームを流し、終わるまでの時間を測った。
フレームは、文法を `jq -Rs .` で JSON の文字列にしてシェルで組み立てた（スクリプトはコミットしていない）。

| 入力 | 時間 | 診断 | 整形の応答 |
| --- | --- | --- | --- |
| p256 | 0.16 秒 | なし | 整形の編集が一つ |
| p4000 | 0.08 秒 | `the expression nests deeper than 256` | `[]` |

監査では、p4000 の `initialize`、`didOpen`、`formatting` に 3.98 秒かかった。

### wasm

監査の harness の `file` で、文法を `{"grammar": ...}` に包んだ要求（`jq -Rs '{grammar: .}'`）と、監査のスクリプトが書く `dj<N>.json` を渡した。
表の時間は、harness が表示する一回の呼び出しの時間で、呼び出しごとに Deno を起動し直した。

| 要求 | `analyze` | `format` | 監査の `analyze` | 監査の `format` |
| --- | --- | --- | --- | --- |
| p256 | 177 ms、診断なし | 353 ms、整形した | （未計測） | （未計測） |
| p4000 | 154 ms、誤り | 113 ms、誤り | 14.6 秒 | 15.6 秒 |
| p8000 | 181 ms、誤り | 104 ms、誤り | （未計測） | （未計測） |
| dj10000 | 7.9 ms、JSON でない | （未計測） | （未計測） | （未計測） |
| dj100000 | 3.6 ms、JSON でない | （未計測） | 2.8 秒 | （未計測） |
| dj1000000 | 6.0 ms、JSON でない | （未計測） | 30 秒で終わらず | （未計測） |

誤りは、どれも 2 行 262 桁の `the expression nests deeper than 256` だった。
`dj<N>.json` の応答は `{"error":"the request is not JSON"}` だった。

### 評価の回数

conformance の計算量のテスト（complexity）に、記法のパーサーを評価の回数を数える形で生成したもの（`Conformance.Bench.PegCounted`）を加えた。
入れ子 50,000 段と 100,000 段の文法で、パーサーはラベル `nest` で止まり、100,000 段の評価の回数は 50,000 段の 2.5 倍以内、かつ入力の長さの 10 倍以内だった。
パーサーは 257 段目で止まるので、回数は入力の長さによらずほぼ一定である。

## SEC-07: 範囲外の長さ

監査の harness の `neg`、`huge`、`ok` を、ビルドした wasm と、監査が使った v0.1.0-rc5 の wasm で動かした。

```text
$ PEG_HS_WASM=peg-hs.wasm deno run --allow-read --allow-env docs/audits/reproduce-wasm-length.ts neg
{"error":"the request is outside the memory"}
after: alive? {"error":"the request is not JSON"}
$ PEG_HS_WASM=peg-hs.wasm deno run --allow-read --allow-env docs/audits/reproduce-wasm-length.ts huge
{"error":"the request is outside the memory"}
after: alive? {"error":"the request is not JSON"}
$ PEG_HS_WASM=rc5/peg-hs.wasm deno run --allow-read --allow-env docs/audits/reproduce-wasm-length.ts neg
dead: Error: proc_exit 1
```

実装の後は、`neg` と `huge` のどちらも `proc_exit` に至らず、JSON の誤りを返し、その後の `format` も応えた。
rc5 の wasm では、監査のとおり `neg` で reactor が終了した。

`after: alive?` の応答と `ok` の応答が `the request is not JSON` なのは、harness が渡す長さ 36 が要求の長さ（35 バイト）より 1 だけ長く、要求の後ろの 1 バイトまで読むためである。
rc5 の wasm でも、`ok` は同じ応答だった。
監査の記録は `ok` が通常の応答を返したと書くが、この作業の環境では再現しなかった。
reactor が動き続けていることは、この応答が返ること自体で確かめられる。

peg-wasm の Deno のテスト「a length outside the memory gets only an error, and the wasm still works (SEC-07)」は、`analyze` と `format` のそれぞれに、長さ `-1`、`0x7fffffff`、線形メモリの大きさを 1 だけ超える値を渡し、どれも `{"error": "the request is outside the memory"}` が返り、その後の `analyze` と `format` が正しく応えることを確かめる。
このテストは、ビルドした wasm で成功し、rc5 の wasm では `proc_exit(1)` で失敗した。

## SEC-08: VS Code の拡張の設定

`editors/vscode/package.json` の `peg-hs.path` に `"scope": "machine"` を付け、`capabilities.untrustedWorkspaces` を `{"supported": "limited", "restrictedConfigurations": ["peg-hs.path"], ...}` と宣言した。
`editors/test/vscode-trust.test.js` の二つのテストがこれを確かめ、実装の前の `package.json` では二つとも失敗した。

ワークスペースの `.vscode/settings.json` に書いた `peg-hs.path` が使われないことの、VS Code の実機での確認は**行っていない**。
この確認は手で VS Code を操作する必要があり、この作業の環境ではできなかった。
リポジトリの持ち主が行い、結果を `docs/editors/` に記録する。
それまで、`scope` と `untrustedWorkspaces` の効果は、VS Code の文書（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の参考文献）にもとづく推定である。

## 自動テスト

実装の後に、次のコマンドですべてのテストを実行し、すべて成功した。
wasm は上の節のとおりビルドし、`PEG_HS` には `$EXE` を渡した。

```sh
cabal-3.16.1.0 test all
(cd editors && npm ci && npm test)
PEG_HS_WASM=peg-hs.wasm PEG_HS_WASM_RAW=raw.wasm PEG_HS="$EXE" deno test --allow-read --allow-write --allow-env --allow-run wasm/test
```

| テストスイート | 結果 |
| --- | --- |
| peg-runtime-test | 56 件成功 |
| peg-grammar-test | 773 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 60 件を含む） |
| peg-codegen-test | 222 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 13 件を含む） |
| peg-cli-test | 117 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 3 件を含む） |
| peg-lsp-test | 159 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 7 件を含む） |
| peg-wasm-test | 183 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 4 件を含む） |
| complexity | 9 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 2 件を含む） |
| json-conformance | 308 件成功 |
| lua-conformance | 93 件成功 |
| toml-conformance | 696 件成功 |
| commonmark-conformance | 成功 |
| editors（`npm test`） | tree-sitter のテストと、node のテスト 23 件が成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 2 件を含む） |
| wasm（Deno） | 185 件成功（[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) の 2 件を含む） |

[ADR 0080](../adr/0080-fixes-of-the-security-audit-of-2026-11-07.md) のテストは、実装の前に書いて動かした。
次のテストは、実装の前のコードで失敗した。

- peg-grammar：`%module` を拒む 7 件、`%export` を拒む 11 件、改行を含む項目と二つめの項目の位置の 2 件、入れ子 257 段の 10 件、`parseTops` と整形と 100,000 段の 3 件
- peg-codegen：制御文字を含むファイル名の 12 件
- peg-cli：三つのすべて（監査の文法、改行を含むファイル名、100,000 段の文法）。100,000 段の文法は 10 秒で終わらなかった
- peg-lsp：257 段の JSON を拒む件、1,000,000 段の JSON を 1 秒以内に拒む件、言語サーバーの -32700 の件、257 段の文法の診断と整形の件
- peg-wasm：監査の要求、制御文字を含む `outputName`、257 段の文法の 3 件
- complexity：100,000 段の文法を拒む件
- editors：`vscode-trust.test.js` の 2 件
- wasm（Deno）：SEC-07 と SEC-06 の 2 件。実装の前の wasm は作らず、rc5 の wasm で動かした。SEC-07 の件が `proc_exit(1)` で reactor を終了させ、続く件も失敗した

`%module` と `%export` と入れ子のそれぞれで受け付ける側の件、文字列の中の括弧を数えない件、並べた式や JSON の段を足さない件、制御文字のない名前の生成物が変わらない件は、いまの動作を固定するもので、実装の前から成功する。
peg-wasm の「`grammar` が 257 段の配列の要求」の件は、最初は応答が誤りであることだけを確かめていて実装の前から成功したので、誤りの文言が `the request is not JSON` であることを確かめる形に強めた。強めた後の形は、実装の前のコードでは動かしていない。

言語サーバーの診断の golden（`packages/peg-lsp/test/golden/diagnostics/`）は、27 個のファイルが変わった。
記法の文法（`Peg.hpeg`、`PegSyntax.hpeg`）の二つは、文法の本文が変わったので、変異の文法がすべて変わった。
ほかの 25 個で変わった変異の文法は 38 個で、どれも新しい検査で誤りになるものだった。
変異の文法を作り直し、`gen` の誤りを実装の前後の `peg-hs` で比べたところ、実装の後だけ `%module expects a module name, but got Fixture..Sum` や `%export expects export items, but got Node(..` の誤りが出た。
どのファイルでも、変異させない文法の診断（golden の 1 行目）は変わらなかった。
`editors/test/ranges.txt` は、記法の文法の行と字句が変わったことだけを反映した。
エディタの文法のテストは、この新しい `ranges.txt` で成功した。

## 実施した検証と限界

| 検証 | 結果 |
| --- | --- |
| 監査の文法の `gen`（SEC-05） | 終了状態 1、ファイルを書かない |
| 監査の wasm の要求（SEC-05） | 診断を返し、`module` は `null` |
| 監査の入力の `gen`、`fmt --check`、`lint`（SEC-06） | 0.1 秒以内に誤り |
| 言語サーバーの p4000（SEC-06） | 0.08 秒、診断と空の編集 |
| wasm の深い文法と深い JSON（SEC-06） | 0.2 秒以内に誤り |
| harness の `neg` と `huge`（SEC-07） | JSON の誤り、reactor は動き続ける |
| VS Code での手の確認（SEC-08） | 未実施 |

確かめていないことは次のとおりである。
VS Code の実機での `peg-hs.path` の解決、Linux での確認、注入した宣言を GHC でコンパイルして動かすことは、今回の範囲外である。
上限の内側の費用は、入れ子 256 段の一つの形（群の括弧）でだけ測った。
