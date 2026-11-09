# ADR 0078: 文法の解析と生成を wasm にしてリリースに添付する

ステータス: 採択→約束の外の import の扱いは [ADR 0079](0079-stub-wasi-imports-outside-the-contract.md)、入力の解析は [ADR 0090](0090-grammar-interpreter-without-ghc.md)

## 文脈

tett23/tett23 の GitHub Pages に、peg-hs のページを作る（[tett23/tett23 の ADR 0004](https://github.com/tett23/tett23/blob/main/.github/docs/adr/0004-peg-hs-page.md)）。
ページにはプレイグラウンドを置く。
ブラウザの中で文法を書きかえると、文法の AST、生成した Haskell のモジュール、生成した型の宣言がすぐに出る。
入力のテキストは解析しない。
peg-hs には文法を直接解釈する仕組みがなく（[ADR 0036](0036-parse-command.md)）、入力を解析するには生成したモジュールを GHC でコンパイルする必要があるからだ。

ブラウザで動かすのは、文法を読んで生成するところまでである。
この部分は純粋な関数でできていて、GHC のブートパッケージだけに依存する。

- `Peg.Grammar.Parser.parseGrammar :: Text -> Either [Diagnostic] Grammar`
- `Peg.Grammar.Templates.expandTemplates` と `Peg.Grammar.Check.check`
- `Peg.Grammar.Format.formatGrammar :: Text -> Either [Diagnostic] Text`
- `Peg.Codegen.generate :: Options -> Grammar -> Either [Diagnostic] Text`
- `Peg.Grammar.Types.classify` と `dataTypeText`（生成した型の宣言を、利用者が読む形で書く。言語サーバーのホバーが使っている）

JSON の読み書きも、すでにある。
`peg-lsp` の `Peg.Lsp.Json` は、peg-hs が JSON の文法から生成したパーサーで JSON を読み、`renderJson` で書く（[ADR 0035](0035-language-server.md)）。
`peg-lsp` のライブラリの依存は、ブートパッケージと `peg-grammar`、`peg-runtime` だけである。

GHC の wasm バックエンドは、ghc-wasm-meta がバイナリを配っている。
その README（2026-10-12 のコミット `8079eb96bbc63823d99ad8acaff0765532625474` で読んだ）から、次のことを確かめた。

- `wasm32-wasi-ghc` と `wasm32-wasi-cabal` を、nix の flake か `setup.sh` で入れる。flavour `9.10` は、GHC の `ghc-9.10` の release branch を追う fork をビルドしたものである。flake の出力 `all_9_10` に、この flavour の道具がそろっている。flake は `x86_64-linux`、`aarch64-darwin` などに対応する。
- `-no-hs-main -optl-mexec-model=reactor` で、WASI の **reactor** モジュールを作る。reactor は一度初期化すると、エクスポートした関数を何度でも呼べる。
- `-optl-Wl,--export=名前` を付けた関数だけが残る。付けないと、リンカーが消す。
- `foreign export ccall` の関数をエクスポートできる。`malloc` と `free` もエクスポートでき、線形メモリ（エクスポートの `memory`）を介して大きな値を受け渡せる。
- 呼ぶ側は、`_initialize` を一度呼び、次に `hs_init(0, 0)` を一度呼んでから、ほかの関数を呼ぶ。

ページ側との約束は、次のとおりである（[tett23/tett23 の ADR 0002](https://github.com/tett23/tett23/blob/main/.github/docs/adr/0002-product-pages-on-github-pages.md)）。

- wasm はこのリポジトリの CI でビルドし、GitHub Releases に添付する。ページ側は wasm をビルドしない。
- ページ側は `wasm.lock` に名前、URL、SHA-256 を書いて取り込む。添付するファイルの名前は、版をまたいで変えない。
- ページ側が実装する WASI preview1 の関数は、引数、環境変数、時計、乱数、標準出力と標準エラーへの書き込み、`proc_exit` だけである。ファイルシステムは実装しない。
- Safari と Chrome の最新版の Web Worker と、Deno で動く。

wasm がどの WASI の関数を import するかは、まだ測っていない。
この ADR を書いた時点では、手元にも CI にも wasm のツールチェーンがなく、ビルドして import の一覧を読むことができなかった。
そこで、許す import の一覧をこの ADR で決め、実装でそれを超えないことをテストで確かめる。

## 実装すること

### パッケージ

非公開のパッケージ `peg-wasm` を `wasm/` に置く。
Hackage には出さない（`conformance/` の `peg-conformance` と同じ扱い）。

- **ライブラリ** `Peg.Wasm`：純粋な関数 `analyzeJson :: Text -> Text` と `formatJson :: Text -> Text` を持つ。要求の JSON を受け取り、応答の JSON を返す。ネイティブでもビルドし、テストする。依存は `peg-grammar`、`peg-codegen`、`peg-lsp`（`Peg.Lsp.Json` だけを使う）、`base`、`text`、`containers`、`filepath`。
- **実行ファイル** `peg-hs-wasm`：`foreign export ccall` で `analyze` と `format` をエクスポートする reactor である。cabal の flag `reactor`（既定は無効）を付けたときだけビルドする。ネイティブの `cabal build all` には入らない。
- **`cabal.project.wasm`**：wasm のビルドに使う。パッケージは `peg-runtime`、`peg-grammar`、`peg-codegen`、`peg-lsp`、`peg-wasm` で、`peg-wasm` の flag `reactor` を有効にする。
- ルートの `cabal.project` に `wasm` を足す。ライブラリとテストは、ほかのパッケージと同じくネイティブでビルドされる。

`peg-cli` は含めない。
`peg-hs gen` と同じ出力を作るため、`Peg.Wasm` は `gen` と同じ順で関数を呼ぶ。

1. `parseGrammar`
2. `expandTemplates` と `check`。誤りは `templateNotes` でテンプレートの呼び出しを添える
3. 誤りがなければ、`labelWarnings` を警告にする（`templateNotes` を添える）
4. `generate`

`gen` の `--strip-labels`、`--export`、`-Werror` は扱わない。

### エクスポートと呼び方

wasm がエクスポートするものは、次のとおりである。

| 名前 | 型 | 働き |
| --- | --- | --- |
| `memory` | メモリ | 線形メモリ |
| `_initialize` | `() -> ()` | reactor の初期化。最初に一度だけ呼ぶ |
| `hs_init` | `(i32, i32) -> ()` | Haskell のランタイムの初期化。`_initialize` の次に `hs_init(0, 0)` を一度だけ呼ぶ |
| `malloc` | `(i32) -> i32` | 線形メモリを確保する |
| `free` | `(i32) -> ()` | `malloc` で確保した領域と、`analyze` と `format` の返した領域を解放する |
| `analyze` | `(i32, i32) -> i32` | 文法を解析して生成する |
| `format` | `(i32, i32) -> i32` | 文法を整形する |

`analyze` と `format` は、要求の JSON を UTF-8 で書いた領域の先頭と長さ（バイト）を受け取る。
返すのは、新しく確保した領域の先頭である。
その領域は、先頭の 4 バイトが応答の長さ（バイト、リトルエンディアンの符号なし整数）で、その後に応答の JSON が UTF-8 で続く。
呼んだ側は、応答を読んだら返された領域を `free` で解放する。
要求の領域は、関数が戻る前に Haskell の側で写し終えるので、戻った後に呼んだ側が解放してよい。

関数の中で Haskell の例外が起きても、wasm を止めない。
例外を捕まえ、`{"error": "internal error: ..."}` を返す。

### 要求と応答の JSON

`analyze` の要求は、次の形である。

```json
{"grammar": "%module Calc\n...", "sourceName": "Calc.hpeg", "outputName": "Calc.hs", "debugEntry": false}
```

- `grammar`（必須）：文法のテキスト。
- `sourceName`（省略可、既定は `Grammar.hpeg`）：`LINE` プラグマに書く文法のファイル名。`peg-hs gen` に渡すパスにあたる。
- `outputName`（省略可、既定は `sourceName` の拡張子を `.hs` にしたもの）：生成するファイルの名前。`gen` の `-o` にあたる。
- `debugEntry`（省略可、既定は `false`）：`gen` の `--debug-entry` にあたる。

`analyze` の応答は、次の形である。

```json
{
  "diagnostics": [{"severity": "error", "line": 3, "column": 7, "message": "undefined rule Term"}],
  "ast": {"kind": "Grammar", "line": 1, "column": 1, "text": null, "children": []},
  "types": "data Expr = Add Expr Term | Expr2 Term\n  deriving (Eq, Show)",
  "module": null
}
```

- `diagnostics`：誤りと警告の配列。`severity` は `"error"` か `"warning"` である。`line` と `column` は 1 から数え、`column` は Unicode のコードポイントで数える（タブも 1 桁、`peg-hs` の表示と同じ）。`message` は `peg-hs gen` の表示から `ファイル名:行:桁: error: ` を除いたものである。
- `ast`：`parseGrammar` が通ったときの文法の AST。テンプレートを展開する前の、書いたとおりの形である。通らなければ `null`。
- `types`：テンプレートの展開が通ったときの、生成した型の宣言。`classify` の生成した型を、規則の順に `dataTypeText` で書き、空行でつなぐ。生成した型がなければ空の文字列。`check` に誤りがあっても出す。未定義の規則に依存する型は、言語サーバーと同じく分類から外れる（[ADR 0075](0075-generated-types-for-rules-without-actions.md)）。展開が通らなければ `null`。
- `module`：誤りがないときの生成したモジュール。同じ要求の `peg-hs gen` が書くファイルと、バイト単位で一致する。誤りがあれば `null`。

`format` の要求は `{"grammar": "..."}` で、応答は `{"text": "...", "diagnostics": [...]}` である。
`text` は `formatGrammar` の結果で、`peg-hs fmt` が書くものと同じである。
整形できなければ `text` は `null` で、`diagnostics` に誤りがある。

要求が JSON でない、`grammar` がない、型が違う、UTF-8 でない、のどれかのときは、`{"error": "..."}` だけを返す。

### 文法の AST の JSON

ページは AST を、たためる木として表示する。
木の表示に要るのは、ノードの種類、位置、短い文字列、子の並びだけである。
そこで、すべてのノードを同じ形にする。

```json
{"kind": "Rule", "line": 5, "column": 1, "text": "Expr", "children": [...]}
```

- `kind`：ノードの種類（下の表）。
- `line`、`column`：文法の中の位置。AST が位置を持たないノードは `null` で、ページは近い祖先の位置を使う。
- `text`：ノードの短い文字列。ないノードは `null`。
- `children`：子のノード。

| `kind` | 元の型 | `text` | 位置 | `children` |
| --- | --- | --- | --- | --- |
| `Grammar` | `Grammar` | `null` | 1 行 1 桁 | 指示、`Verbatim`、規則を、位置の順に並べたもの |
| `Directive` | `Grammar` の各欄 | `%module` などの指示の名前 | 指示の位置 | `Value` |
| `Verbatim` | `%{ ... }%` のブロック | 中の Haskell のコード | ブロックの位置 | なし |
| `Value` | 指示の値 | 値（名前、数、Haskell のコード） | 値の位置 | なし |
| `Rule` | `Rule` | 規則の名前 | 規則の位置 | `Parameter`、`TemplateParameter`、`Type`、`Alternative` |
| `Parameter` | `Param` | `名前 :: 型` | 型の位置 | なし |
| `TemplateParameter` | `TemplateParam` | 名前、型があれば `名前 :: 型` | `null` | なし |
| `Type` | 型注釈 | 型 | 型の位置 | なし（型注釈を書いた規則だけに置く） |
| `Alternative` | `Alt` | `null` | 選択肢の位置 | `Item`、`Action`、`Constructor` |
| `Action` | アクション | Haskell のコード | コードの位置 | なし |
| `Constructor` | `@名前` | 構築子の名前 | 名前の位置 | なし |
| `Item` | `Item` | 束縛の名前、なければ `null` | 要素の位置 | 式のノード一つ |
| `Literal` | `ELit` | 書いたとおりのリテラル | `null` | なし |
| `Class` | `EClass` | 書いたとおりの文字クラス | `null` | なし |
| `Any` | `EAny` | `.` | `null` | なし |
| `Reference` | `ERef` | 規則の名前 | 参照の位置 | `Argument` |
| `Argument` | 規則やテンプレートへの引数 | Haskell のコード | 引数の位置 | なし |
| `Group` | `EGroup` | `null` | `null` | `Sequence` |
| `Sequence` | `EGroup` の選択肢 | `null` | `null` | `Item` |
| `Star`、`Plus`、`Optional`、`And`、`Not`、`Capture`、`Discard` | `EStar` など | `null` | `null` | 式のノード一つ |
| `Label` | `ELabel` | ラベル | ラベルの位置 | 式のノード一つ |
| `AndPredicate`、`NotPredicate` | `EPred` | Haskell のコード | コードの位置 | なし |
| `Template` | `ETemplate` | テンプレートの名前 | 呼び出しの位置 | 式の引数のノードの後に `Argument` |

`Grammar` の欄と指示の名前の対応は、`%module`、`%start`、`%entry`、`%export`、`%env`、`%tabstop`、`%nomemo`、`%language`、`%syntax`、`%token`、`%trivia`、`%inline`、`%recover`、`%safe`、`%deriving` で、記法の文書（[syntax.md](../syntax.md)）の書き方に合わせる。
欄が複数の値を持つ指示（`%recover` の二つの名前など）は、`Value` を複数持つ。
`%syntax` は値を持たない。
`Discard` は記法に現れず、テンプレートの展開が作るものなので、展開する前の AST には出てこない。表に入れておくのは、`Expr` の構成子をすべて覆うためである。

### ビルドとリリース

ツールチェーンは、ghc-wasm-meta の flake を、コミット `8079eb96bbc63823d99ad8acaff0765532625474` に固定して使う。
出力は `all_9_10` である。
nix は、flake.lock と、各成果物に書かれたハッシュでダウンロードを検証する。
`setup.sh` はダウンロードしたものを検証しないので、使わない。

- **CI**：`ci.yml` に `wasm` のジョブを足し、集約の `ci` ジョブの `needs` に加える。nix を入れ、`nix shell` で固定した flake の `wasm32-wasi-cabal` を使って `cabal.project.wasm` で `peg-hs-wasm` をビルドする。同じジョブでネイティブの `peg-hs` もビルドし、Deno で wasm のテストを動かす。ドキュメントだけの変更では、ほかのジョブと同じく飛ばす（[ADR 0072](0072-required-checks-for-auto-merge.md)）。
- **リリース**：`release.yml` に `wasm` のジョブを足す。ビルドした wasm を `peg-hs.wasm` という名前でリリースに添付し、`SHA256SUMS` に加える。名前に版を入れない。版はタグで区別する。リリースノートの添付物の一覧にも書く。

使うアクションは、Node 24 以降で動く最新のメジャー版にする。

### import の約束

wasm が import してよいのは、`wasi_snapshot_preview1` の次の関数だけである。

- `args_get`、`args_sizes_get`
- `environ_get`、`environ_sizes_get`
- `clock_time_get`、`clock_res_get`
- `random_get`
- `fd_write`（標準出力と標準エラーだけ）
- `proc_exit`

ほかのモジュールからの import はしない。
実装でこの一覧を超える import が見つかったら、実装を止めて報告する。
ページ側に関数を足してもらうか（たとえば `EBADF` を返すだけの `fd_close`）、wasm の側で import をなくすかは、そのとき別の ADR で決める。

### 文書

- README（英語と日本語）に、wasm の節を足す。添付物の名前、エクスポートの表、呼び方の手順、要求と応答の JSON、import の一覧を書く。
- `docs/specifications.md` に、wasm の項を足す。
- 実装が終わったら、tett23/tett23 のセッションに、タグ、添付したファイルの URL と SHA-256、エクスポートの一覧、JSON の形を伝える。

## 実装しないこと

- 入力のテキストの解析（文法のインタプリタ、ブラウザでの GHC）。
- 言語サーバーの機能（補完、ホバー、意味トークン、コードアクション）。`peg-lsp` から使うのは JSON のモジュールだけである。
- `peg-hs lint` の警告。`analyze` の警告は、`gen` が出すラベルの警告だけである。
- `gen` の `--strip-labels`、`--export`、`-Werror`。
- 規則ごとの推論した型の一覧。`types` は生成した型の宣言だけを返す。
- wasm を読み込むための JavaScript のライブラリと、npm のパッケージ。呼び方は README に書く。
- JavaScript の FFI（`foreign export javascript`）。`post-link.mjs` の生成する JavaScript を要しない `ccall` だけで作る。
- wizer による事前の初期化と、wasm-opt による縮小。大きさと読み込みの時間を測ってから、必要なら別の ADR で決める。
- Safari での確認。ページ側の [tett23/tett23 の ADR 0004](https://github.com/tett23/tett23/blob/main/.github/docs/adr/0004-peg-hs-page.md) が、実装後に Safari と Chrome で確かめる。

## テスト設計

先に書いて失敗させてから実装する。

### ネイティブのテスト（`peg-wasm-test`、tasty）

`Peg.Wasm` の純粋な関数を試す。

- `analyzeJson`
  - `conformance/bench/JsonGenerated.hpeg` で、`diagnostics` が空で、`types` が `data Value` を含む。
  - README の電卓の文法（型を生成する書き方）で、`diagnostics` が空で、`types` が `data Expr = Add Expr Term | Expr2 Term` を含む。
  - 未定義の規則を参照する文法で、`severity` が `error`、`line` と `column` が参照の位置、`message` が `undefined rule 名前` の診断が返る。`ast` と `types` は `null` でなく、`module` は `null` である。
  - 構文の誤りのある文法で、`ast`、`types`、`module` が `null` で、位置つきの診断が返る。
  - ラベルの警告が出る文法で、`severity` が `warning` の診断と、`null` でない `module` が返る。
  - 生成したモジュールが、`peg-hs gen` の書くファイルとバイト単位で一致する。テストは `build-tool-depends` で `peg-hs` を使い、一時ディレクトリで `gen` を動かして比べる。文法は conformance の全文法と、peg-codegen のフィクスチャの全文法で、`--debug-entry` の有無の両方を含める。
  - `sourceName` と `outputName` を省くと、`Grammar.hpeg` と `Grammar.hs` として生成する。`sourceName` だけを渡すと、拡張子を `.hs` にした名前を `outputName` にする。
  - 非 ASCII の規則名とコメント（日本語）を含む文法で、応答の文字列が元の文字列と一致する。
- AST の JSON
  - 小さな文法の AST を、期待する JSON と比べる（golden）。指示、引数、テンプレート、述語、ラベル、構築子、グループを一つずつ含める。
  - 子が位置の順に並ぶ。指示と規則を交互に書いた文法で確かめる。
  - conformance の全文法で、ノードの数が `Grammar` の値の構成子の数と一致する。
- `formatJson`
  - 結果が `formatGrammar` と一致する。
  - 整形した文法をもう一度整形しても変わらない。conformance の全文法で確かめる。
  - 構文の誤りのある文法で、`text` が `null` で、位置つきの診断が返る。
- 要求の誤り
  - JSON でない要求、`grammar` のない要求、`grammar` が文字列でない要求で、`error` だけの応答が返る。

### wasm のテスト（Deno、CI の `wasm` ジョブ）

ビルドした wasm を読み込んで試す。
WASI は、テストのために書く最小の実装で与える。
その実装は、「import の約束」の関数だけを持つ。
ページ側の実装と同じ範囲で動くことを確かめるためである。

- import と export
  - `WebAssembly.Module.imports` が、「import の約束」の一覧に含まれる関数だけである。
  - `WebAssembly.Module.exports` が、エクスポートの表の名前をすべて含む。
- 呼び方
  - `_initialize`、`hs_init(0, 0)` の順に呼んだ後、`analyze` と `format` を交互に 100 回呼んでも、毎回同じ応答が返る。
  - 応答の領域を `free` で解放できる。
- ネイティブとの一致
  - ネイティブのテストの `analyze` の項目を、wasm でも同じ文法で確かめる。
  - 生成したモジュールが、同じジョブでビルドしたネイティブの `peg-hs gen` の出力とバイト単位で一致する。文法はネイティブのテストと同じである。
  - `format` の結果が、ネイティブの `peg-hs fmt` の出力と一致する。
- 不正な入力
  - UTF-8 でない要求で、`error` だけの応答が返り、wasm がその後も動く。

### 実装の後に測って記録すること

自動のテストにしない数値は、実装のプルリクエストに書く。

- wasm の大きさ。
- Deno で、読み込みから `hs_init` の終わりまでの時間と、`JsonGenerated.hpeg` の `analyze` の時間。
- 組み込みのブラウザ（Chromium）の Web Worker で、`JsonGenerated.hpeg` の `analyze` が動くこと。

## トレードオフ

- `gen` の手順を `Peg.Wasm` にも書くので、手順が二か所になる。手順を一つのライブラリ関数にまとめれば重複はなくなるが、`peg-codegen` の公開の API が増える。ここでは重複を選び、バイト単位の一致のテストでずれを検出する。
- AST の JSON をすべて同じ形のノードにしたので、ページの木の表示は簡単になるが、欄の名前がなくなる。たとえば、選択肢の子のうちどれが構築子かは `kind` で区別し、欄の名前では区別しない。木を表示する以外の用途には向かない。
- 位置を持たない式のノードがある。AST が式の位置を持たないためで、位置を足すには `peg-grammar` の型を変える必要がある。ページは近い祖先の位置で代える。
- 応答の長さを領域の先頭に書く形にしたので、呼んだ側は 4 バイトを読む手間が増える。代わりに、長さを返す関数を別に用意する必要がなく、呼び出しの間に状態が残らない。
- import の一覧を測らずに約束した。測った結果が約束を超えれば、実装が止まり、ページ側との調整が要る。
- ツールチェーンを nix で入れるので、CI に nix のインストールが加わる。代わりに、ダウンロードしたものを検証できる。

## 参考文献

- [tett23/tett23 の ADR 0002「Product pages on GitHub Pages」](https://github.com/tett23/tett23/blob/main/.github/docs/adr/0002-product-pages-on-github-pages.md)
- [tett23/tett23 の ADR 0004「peg-hs のページとプレイグラウンド」](https://github.com/tett23/tett23/blob/main/.github/docs/adr/0004-peg-hs-page.md)
- ghc-wasm-meta, README（コミット `8079eb96bbc63823d99ad8acaff0765532625474`、2026-10-12）. https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta
- GHC User's Guide, "Using the GHC WebAssembly backend". https://ghc.gitlab.haskell.org/ghc/doc/users_guide/wasm.html
