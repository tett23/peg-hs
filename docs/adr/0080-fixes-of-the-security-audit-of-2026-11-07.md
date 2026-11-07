# ADR 0080: 2026-11-07 のセキュリティ監査の指摘を直す

ステータス: 採択

## 文脈

v0.1.0-rc5（コミット `a429a19`）を対象に、二度目のセキュリティ監査を行った（[監査の記録](../audits/2026-11-07-security-audit.md)）。
前回の監査（[2026-11-06](../audits/2026-11-06-security-audit.md)）の指摘は、[ADR 0077](0077-fixes-of-the-security-audit.md) で直した。
今回は、その後に入った wasm（[ADR 0078](0078-grammar-analysis-in-wasm.md)、[ADR 0079](0079-stub-wasi-imports-outside-the-contract.md)）と、前回が範囲外とした領域を見た。
指摘は四つある。

- **SEC-05**（中・条件付き）：`%module` の値と `%export` の項目が、生成したモジュールの見出しとエクスポートの一覧にそのまま出る。`gen` のファイル名と wasm の `sourceName` も、生成物の先頭のコメントにそのまま出る。アクションも述語も `%{ }%` も `%env` も持たない文法でも、生成したモジュールにトップレベルの宣言を仕込める。
- **SEC-06**（中）：入れ子の深い文法と、入れ子の深い JSON が、小さな入力で超線形の時間とメモリを使う。
- **SEC-07**（低）：wasm の reactor が、要求の長さが範囲外のときに、JSON の誤りを返さずに終了する。
- **SEC-08**（低〜中）：VS Code の拡張の `peg-hs.path` を、ワークスペースの設定で上書きできる。

SEC-05 と SEC-06 は、監査の後にこの ADR を書く前に手元で再現した。
SEC-05 では、`%module M (parse) where evil = 1 {-` を持つ文法を `peg-hs gen` にかけると、生成物に `module M (parse) where evil = 1 {-` の行が出た。
このモジュールを GHC でコンパイルして、仕込んだ宣言が動くところまでは確かめていない。
SEC-06 では、入れ子の群を 2,000 段から 4,000 段に倍にすると、`gen` は 1.1 秒から 11.8 秒に、`fmt --check` は 5.7 秒から 18.1 秒になった。

SEC-06 の費用は、パーサーにもある。
解析と lint だけを行う `peg-hs lint` は、入れ子 256 段と 1,000 段では 0.1 秒以内で終わるが、20,000 段で 1.4 秒、100,000 段（約 200 KB）で 14.3 秒かかった。
したがって、解析した後に深さを検査するのでは、深い入力を拒むまでに時間がかかる。
上限を超えた入れ子に入る前に、パーサーが止まる必要がある。

リポジトリの文法の入れ子の深さは、群の括弧を数えると、深いものでも 7 段だった（`Peg.hpeg`、`PegSyntax.hpeg`）。
言語サーバーが受け取る JSON の入れ子は、LSP のメッセージでは 10 段に満たない。

## 実装すること

### SEC-05：生成物に出る値を検査する

`Peg.Grammar.Assemble` の検査に、次の二つを加える。
どちらも、文法の誤りとして値の位置で報告する。

- **`%module` の値**：ドットで区切った Haskell のモジュール名でなければならない。各部分は大文字で始まり、その後は文字、数字、`_`、`'` だけからなる。違えば `%module expects a module name, but got X` とする。
- **`%export` の項目**：Haskell のエクスポート項目の書式でなければならない（[ADR 0014](0014-generated-module-api.md)）。受け付けるのは、次の形だけである。
  - 修飾してもよい変数名か型の名前（`evalExpr`、`Expr`、`M.f`）
  - 型の名前に `(..)` か、名前と括弧で囲んだ演算子をカンマで区切った `( ... )` を続けたもの（`Expr(..)`、`Expr(Add, Mul)`）
  - 括弧で囲んだ演算子（`(+++)`）
  - `type` か `pattern` を前に付けたもの（`type (:+)`、`pattern P`）
  - `module` とモジュール名（`module Data.Text`）

  項目と項目のあいだと、括弧の内側の空白は許す。
  改行、`--`、`{-`、`where` などを含む項目は、どの形にも当たらないので誤りになる。
  違えば `%export expects export items, but got X` とする。

`Peg.Codegen.generate` は、`optSourceName` と `optOutputName` が制御文字（U+0000 から U+001F と U+007F）を含むとき、1 行 1 桁の誤り `the file name contains a control character` を返す。
`peg-hs gen` も wasm の `analyze` も、この誤りを出して生成しない。
制御文字を含まない名前では、生成物は今と同じバイト列のままである。

README と `docs/specifications.md` の信頼境界の記述に、次のことを書く。
`%module`、`%export`、ファイル名のような埋め込みのブロックの外の値も、生成したモジュールに入る。
peg-hs はそれらを検査して、Haskell の宣言として読める値を拒む。

### SEC-06：入れ子の深さに上限を設ける

文法の式の入れ子の深さを、256 段までとする。
深さは、群の括弧、前置と後置の演算子（`&`、`!`、`$`、`*`、`+`、`?`）、ラベル（`^`）、テンプレートの呼び出しの引数が、それぞれ一段ずつ数える。
上限を超えた文法は、超えた位置で `the expression nests deeper than 256` の誤りになる。

検査は自己記述の文法（`packages/peg-grammar/grammar/Peg.hpeg` と `PegSyntax.hpeg`）のパーサーで行い、上限を超えた入れ子にパーサーが入らないようにする。
解析が深さの上限で止まるので、拒むまでの時間は入力の長さに対して線形に抑えられる。
規則の引数で深さを渡すか、別の方法にするかは、実装で決める。

`parseTops` を通るすべての経路（`gen`、`fmt`、`lint`、`parse`、言語サーバー、wasm）が、この上限で入力を拒む。
言語サーバーは、この誤りを診断として返し、整形の要求には応えない。

JSON の入れ子の深さも、256 段までとする。
`Peg.Lsp.Json.parseJson` は、文字列の外の `[` と `{` の入れ子が 256 段を超える JSON を、解析する前に線形の走査で拒み、`Nothing` を返す。
言語サーバーは、ほかの JSON でない本文と同じく `-32700` の誤りで応える。
wasm は、ほかの JSON でない要求と同じく `{"error": ...}` を返す。

`docs/syntax.md` に入れ子の深さの上限を書き、冒頭の「反映している ADR」の一覧にこの ADR を足す。

### SEC-07：reactor が範囲外の長さで終了しないようにする

`wasm/reactor/` の `serve` は、要求を写す前に長さを検査する。
長さが負のとき、または `ptr + len` が線形メモリの大きさを超えるときは、`{"error": "the request is outside the memory"}` を返す。
線形メモリの大きさは、reactor に加える小さな C の関数（`__builtin_wasm_memory_size(0)` に 65536 を掛ける）で得る。
要求を写す処理も、例外を捕まえる範囲の内側に移す。

### SEC-08：VS Code の拡張の実行ファイルの設定

`editors/vscode/package.json` を次のように変える。

- `peg-hs.path` に `"scope": "machine"` を付ける。ワークスペースの設定では上書きできず、利用者の設定でだけ決まる。
- `capabilities.untrustedWorkspaces` を `{"supported": "limited", "restrictedConfigurations": ["peg-hs.path"], "description": ...}` と宣言する。言語サーバーは文法を読むだけで、文法の Haskell を動かさない。そのため、信頼していないワークスペースでも、利用者の設定の `peg-hs.path` で言語サーバーを起動してよい。

README の VS Code の節に、`peg-hs.path` は利用者の設定にだけ書けることを書く。

### 文書と CHANGELOG

- `docs/specifications.md`：入れ子の深さの上限、`%module` と `%export` の検査、ファイル名の制御文字、wasm の範囲外の長さ、VS Code の設定の scope。
- `packages/peg-grammar`、`peg-codegen`、`peg-lsp` の CHANGELOG の Security に、変わったことを書く。
- 監査の確かめ直しの記録を `docs/audits/` に置く（[ADR 0077](0077-fixes-of-the-security-audit.md) と同じ形）。

## 実装しないこと

- フォーマッター、検査、生成の走査そのものを、入れ子の深さに対して線形にすること。上限があれば費用は抑えられる。上限の内側の費用は、下のテスト設計のとおり測って記録する。
- 文法の長さや規則の数の上限。今回の監査で超線形を確かめたのは、入れ子の深さだけである。
- 生成したモジュールを、生成器の側で Haskell として解析すること。生成器は Haskell の構文を理解しない方針である（[ADR 0014](0014-generated-module-api.md)）。`%export` の検査は、エクスポート項目の字句の形だけを見る。
- VS Code の拡張の、`peg-hs.path` 以外の設定の見直し。
- 前回と今回の監査が範囲外とした項目（Actions のコミットの SHA への固定、ghcup の bootstrap の検証、git の履歴の秘密情報、Linux の共有一時領域の競合、継続的な fuzzing）。

## テスト設計

先に書いて失敗させてから実装する。

- SEC-05（`peg-grammar`、`peg-codegen`、`peg-cli`、`peg-wasm`）
  - `%module` に `M (parse) where evil = 1 {-`、`m`、`M.`、`.M`、`M..N`、空白を含む名前を書いた文法が、それぞれ値の位置の誤りになる。`M`、`A.B.C`、`A1.B_c'` は通る。
  - `%export` に `evil2) where evil2 = 2 {-`、改行を含む項目、`--` を含む項目が誤りになる。`Expr(..)`、`Expr(Add, Mul)`、`evalExpr`、`M.f`、`(+++)`、`type (:+)`、`pattern P`、`module Data.Text` は通る。リポジトリのすべての文法が今までどおり通る。
  - 監査の証跡の文法（`docs/audits/2026-11-07-inj-module.hpeg.txt`）を `peg-hs gen` にかけると、終了状態 1 で誤りを出し、ファイルを書かない。
  - 改行を含む `optSourceName` と `optOutputName` で `generate` が誤りを返す。wasm の `analyze` に、監査の証跡の要求（`docs/audits/2026-11-07-srcname-req.json`）を渡すと、診断が返り、`module` が `null` になる。
  - 制御文字を含まない名前では、すべての生成物の golden が変わらない。
- SEC-06（`peg-grammar`、`peg-lsp`、`peg-wasm`、`conformance` の計算量のテスト）
  - 入れ子 256 段の文法は通り、257 段の文法は 257 段目の位置で誤りになる。群、前置の演算子、後置の演算子、ラベル、テンプレートの引数のそれぞれで確かめる。
  - 入れ子 100,000 段の文法を拒むまでのパーサーの評価の回数が、入力の長さに比例する。[ADR 0007](0007-performance-discipline.md) の計算量のテストと同じく、評価の回数を数えて確かめる。
  - JSON の入れ子 256 段は解析でき、257 段は `parseJson` が `Nothing` を返す。文字列の中の `[` と `{` は数えない。入れ子 1,000,000 段の JSON でも、`parseJson` が 1 秒以内に `Nothing` を返す。
  - 言語サーバーに入れ子 257 段の JSON の本文を送ると `-32700` の誤りが返り、サーバーは次のメッセージに応える。入れ子 257 段の文法を開くと診断が返り、整形の要求には空の編集で応える。
  - wasm で、入れ子 257 段の文法の `analyze` が診断を返し、`grammar` が入れ子 257 段の配列の要求が `{"error": ...}` を返す。
- SEC-07（`peg-wasm` の Deno のテスト）
  - 長さに `-1`、`0x7fffffff`、線形メモリの大きさを 1 だけ超える値を渡すと、`{"error": ...}` が返る。その後の `analyze` と `format` も正しく応える。監査の証跡の harness（`docs/audits/reproduce-wasm-length.ts`）の `neg` と `huge` で、`proc_exit` に至らない。
- SEC-08（`editors/test`）
  - `package.json` の `peg-hs.path` の `scope` が `machine` である。
  - `capabilities.untrustedWorkspaces` の `supported` が `limited` で、`restrictedConfigurations` が `peg-hs.path` を含む。

### 実装の後に測って記録すること

- 入れ子 256 段の文法での `gen`、`fmt`、`lint`、言語サーバーの `didOpen` と整形、wasm の `analyze` と `format` の時間。
- 監査の証跡のスクリプト（`docs/audits/reproduce-deep-nesting.sh`）の入力で、`gen`、`fmt --check`、wasm が誤りを返すまでの時間。
- VS Code で、ワークスペースの `.vscode/settings.json` に書いた `peg-hs.path` が使われないこと。手で確かめ、確かめ直しの記録に書く。手で確かめられない場合は、そのことを記録に書く。

## トレードオフ

- 入れ子の深さの上限は、記法の新しい制限である。256 段はリポジトリの文法の深さ（7 段）よりずっと大きいが、機械で生成した文法が超える可能性はある。上限を設定で変えられるようにはしない。
- `%export` の検査は、Haskell のエクスポート項目の書式の一部だけを受け付ける。書式に当てはまる項目でも、受け付けないものがありうる（たとえば、演算子の型の名前を修飾したもの）。その場合は、項目を verbatim ブロックの側に寄せて書き直す必要がある。
- ファイル名の制御文字を拒むので、改行を含むファイル名の文法は生成できなくなる。こうしたファイル名は普通は使わないので、拒むほうを選んだ。
- `untrustedWorkspaces` を `limited` にすると、信頼していないワークスペースでも言語サーバーが起動する。言語サーバーは文法を読むだけで、文法の Haskell を動かさない。ただし、言語サーバーの資源の消費（SEC-06）は信頼していない文法にも及ぶ。上限がそれを抑える。

## 参考文献

- [セキュリティ監査（2026-11-07）](../audits/2026-11-07-security-audit.md)
- [セキュリティ監査（2026-11-06）](../audits/2026-11-06-security-audit.md)
- Visual Studio Code, "Workspace Trust Extension Guide". https://code.visualstudio.com/api/extension-guides/workspace-trust
- Visual Studio Code, "Contribution Points: contributes.configuration". https://code.visualstudio.com/api/references/contribution-points#contributes.configuration
