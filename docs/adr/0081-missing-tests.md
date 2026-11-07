# ADR 0081: 欠けているテストを足す

ステータス: 採択（未実装）

## 文脈

採択した ADR の「テスト設計」と、実際のテストを突き合わせた（main、コミット `a429a19`）。
照合したのは、採択した 78 の ADR のテスト設計の各項目、四つの公開ライブラリの公開の API、CLI の誤りの経路である。
ADR が設計したのに、テストがないか、設計より弱いものが見つかった。
ADR は決めていないが、Haddock や仕様書が約束している振る舞いで、テストのないものもあった。

設計より弱いものの例を挙げる。
[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md) は、ラベルの安全性の検査の偽陰性を、引数つきの規則と意味述語を含む無作為の文法で確かめると決めた。
テスト（`packages/peg-grammar/test/Labels.hs`）は、そうした文法を作る。
しかし、テストの中の解釈器は規則の引数を捨て、`True` と `False` 以外の述語を常に成功させる。
そのため、検査が引数の置き換えを誤っても、このテストは落ちない。

テストのない約束の例も挙げる。
`Peg.Runtime.Syntax`（ロスレスな構文木、[ADR 0019](0019-lossless-syntax-tree.md)）の Haddock は、根の親が `Nothing` であること、範囲がバイトのオフセットであること、`syntaxText (concatSyntax k [a, b]) == syntaxText a <> syntaxText b` であることを約束している。
`syntaxParent`、`tokenParent`、`concatSyntax` などの名前は、どのテストにも現れない。
Golem が使う層なので、退行は Golem の側で初めて見つかることになる。

回復の全域性のテスト（`packages/peg-grammar/test/Recovery.hs`）は、[ADR 0035](0035-language-server.md) が「すべての位置」と決めた変異を、文法ごとに長さの 50 分の 1 の間隔で約 100 か所に間引いている。
間引いたことは、どの ADR にも書かれていない。

照合では、文書の食い違いも一つ見つかった。
CONTRIBUTING（英語と日本語）は最新の rc を `v0.1.0-rc2` と書き、README は `v0.1.0-rc4` と書いている。
実際の最新は `v0.1.0-rc5` である。

## 実装すること

テストを足す。
製品のコードは、テストが見つけた誤りを直す場合を除いて変えない。
テストが誤りを見つけたら、その修正は同じプルリクエストに入れ、プルリクエストに書く。

### 設計より弱いテストを、設計どおりにする

- **ラベルの検査の偽陰性**（[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md)、`packages/peg-grammar/test/Labels.hs`）：テストの解釈器が、整数の引数を規則に渡し、引数と整数の比較の述語（`&{ n == 0 }`、`&{ n > 0 }` など）を評価できるようにする。束縛による引数の遮蔽も扱う。
- **回復の全域性の変異**（[ADR 0035](0035-language-server.md)、`packages/peg-grammar/test/Recovery.hs`）：いまの間引いた変異を残し、無作為の位置の変異を 100 件加える。QuickCheck のシードは失敗したときに表示されるので、落ちた変異を再現できる。
- **回復のフィクスチャの健全性**（[ADR 0028](0028-label-safety-check.md)、`packages/peg-codegen/test/Main.hs`）：Recover のフィクスチャで、正しい入力の一文字の削除と重複のすべてを確かめる。JSON と TOML の適合性のテストと同じ形にする。
- **`%recover` を持つ文法へのラベルの挿入**（[ADR 0054](0054-automatic-label-insertion.md)、`packages/peg-codegen`）：`%recover` のラベルと、その外側の挿入の候補の両方を持つフィクスチャを足す。挿入した後の `parseRecover` と `parseSyntaxRecover` が、挿入する前と同じ結果を返すことを確かめる。
- **先読みと `_span`**（[ADR 0008](0008-source-positions.md)、`packages/peg-runtime/test/Main.hs`）：`&` と `!` が `_span` を動かさないこと、マルチバイト文字をまたぐ範囲がバイトのオフセットで正しいことを確かめる。
- **`#` がコメントにならない場所**（[ADR 0004](0004-peg-notation.md)、`packages/peg-grammar/test/Main.hs`）：文字クラス `[#]` とアクション `{ "#" }` の中の `#` が、コメントにならない。
- **`%tabstop` と診断の桁**（[ADR 0012](0012-context-sensitive-extensions.md)、`packages/peg-codegen/test/Main.hs`）：`%tabstop` が `_col` だけを変え、誤りの位置の桁（`Pos`）を変えない。
- **wasm の Deno のテスト**（[ADR 0078](0078-grammar-analysis-in-wasm.md)、`wasm/test/wasm_test.ts`）：ネイティブのテストにある三つの項目を、wasm でも確かめる。テンプレートの本体の誤りに呼び出しが添えられること、生成した型がないときに `types` が空の文字列になること、桁がコードポイントで数えられタブも 1 桁であること、の三つである。
- **`%nomemo` の未定義の規則**（[ADR 0017](0017-nomemo-implementation.md)、`packages/peg-grammar/test/Main.hs`）：未定義の規則を `%nomemo` に書くと誤りになる。
- **整形の golden**（[ADR 0032](0032-grammar-formatter.md)、`packages/peg-grammar/test/golden/format/input.txt`）：CRLF、行末の空白、末尾の連続した空行を入力に足し、LF への統一、行末の空白の除去、末尾の空行の除去を golden で固定する。
- **CLI の書き込みの失敗**（[ADR 0045](0045-fixes-before-v0-1-0.md)、`packages/peg-cli/test/Main.hs`）：次の場合の終了状態と表示を確かめる。
  - `gen -o` にディレクトリを渡す
  - `gen -o` に書き込めない場所を渡す
  - `fmt` に読み取り専用のファイルを渡す。報告して、残りのファイルの整形を続ける
  - `label --write` に読み取り専用のファイルを渡す
  - `fmt`、`lint`、`parse` に UTF-8 でない文法を渡す
  - `parse` に UTF-8 でない入力を渡す
- **CLI の使い方の誤り**（[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md)、[ADR 0050](0050-hpeg-extension.md)、`packages/peg-cli/test/Main.hs`）：`peg-hs help a b` が終了状態 2 の使い方の誤りになる。`parse` に拡張子 `.peg` の文法を渡すと、ほかのコマンドと同じく扱われる。

### ADR に設計がなく、仕様が約束していることのテスト

- **ロスレスな構文木の不変条件**（[ADR 0019](0019-lossless-syntax-tree.md)、`conformance/test/JsonMain.hs` と `TomlMain.hs`）：JSON と TOML の適合性のデータのすべてと、無作為の入力の構文木のすべてのノードについて、次を確かめる。
  - 子の範囲が、親の範囲を順に隙間なく分ける
  - 子の `syntaxParent` とトークンの `tokenParent` が、その親を指す。根の親は `Nothing` である
  - `syntaxText` が、トークンのテキストをつないだものに等しい
  - `labeledTokens` と `labeledNodes` が、`syntaxChildrenWithTokens` をラベルで選んだものに等しい
  - `syntaxText (concatSyntax k [a, b]) == syntaxText a <> syntaxText b`
- **言語サーバーの全域性**（[ADR 0035](0035-language-server.md)、`packages/peg-lsp/test/Main.hs`）：任意のバイト列に対して、`parseJson` と `decodeFrames` が例外を投げずに評価を終える。JSON の生成器に、小数、指数、`-0` の数を加える。
- **UTF-16 の位置の往復**（[ADR 0071](0071-incremental-parsing-in-the-language-server.md)、`packages/peg-lsp/test/Main.hs`）：基本多言語面の外の文字を含む無作為のテキストで、オフセットから行と UTF-16 の桁に変え、オフセットに戻すと元に戻る。
- **文法のパーサーの全域性**（[ADR 0035](0035-language-server.md)、`packages/peg-grammar/test/Recovery.hs`）：任意の Unicode のテキストに対して、`parseGrammar` と回復つきの解析が例外を投げない。回復つきの解析の構文木のテキストが、入力に等しい。

### 文書

- CONTRIBUTING（英語と日本語）の最新の rc の記述から、版の番号を外す。最新の版は Releases を見るように書く。README と食い違わないようにするためである。

## 実装しないこと

- アクションの中の未定義の束縛名と、意味述語の右側の束縛の参照の静的な検査。テストだけでなく検査そのものを足すので、[ADR 0082](0082-static-check-of-binding-references.md) で扱う。
- wasm の `diagnostics`、`ast`、`types` を、ネイティブの出力とバイト単位で比べること。[ADR 0078](0078-grammar-analysis-in-wasm.md) は、生成したモジュールと整形の結果だけをネイティブと比べると決めている。
- テストにも製品のコードにも現れない公開の名前（`isValidIdent`、`nameCandidates`、`safeCandidates`、`generatedTypeName`、`stripLabels`、`receiveMessage` など）を、消すか残すかの判断。消すと公開の API が変わるので、別の ADR で決める。
- 手での確かめのうち、まだ記録のないもの（エディタでの言語サーバーと整形、Neovim と Helix の設定の例、意図して落とすプルリクエストで `ci` が失敗すること、sdist を分けた後の CI の計測）。この ADR はテストを足すだけで、手での確かめは行わない。
- 優先度の低い項目（結合文字と基本多言語面の外の文字の文字クラス、`%safe` を一つずつ外した結果の golden、環境の値を変えた入力、選択肢の順を入れ替えた文法の誤りの一致、左再帰を含むフィクスチャの新旧の一致、長い入力での疎なメモ表、sdist の CHANGELOG と数の検査、`%inline` だけの静的な誤り）。必要になったら別の ADR で足す。

## テスト設計

この ADR はテストそのものを足すので、足したテストが意味を持つことを次のように確かめる。

- 足したテストのうち、製品のコードの振る舞いを確かめるものは、その振る舞いをわざと壊すと落ちることを一度確かめる。壊し方は、テストごとにプルリクエストに書く。たとえば、ラベルの検査の偽陰性のテストは、検査が引数を置き換えないように壊すと落ちる。壊した変更はコミットしない。
- すでに正しく動いている振る舞いを固定するテストは、先に書いて失敗させることができない。わざと壊して落ちることを確かめれば、先に失敗させたことに代えられる。
- テストが製品のコードの誤りを見つけたら、修正の前に落ち、修正の後に通ることを確かめる。
- `cabal test all` の時間が、足す前と比べてどれだけ延びたかを、プルリクエストに書く。CI の三つのテストのジョブの長さの釣り合い（[ADR 0039](0039-faster-ci.md)）が崩れたら、ジョブへの振り分けを直す。

## トレードオフ

- 無作為の位置の変異と無作為の入力のプロパティは、実行のたびに違う入力を試す。めったに起きない誤りが、関係のないプルリクエストの CI で初めて落ちることがある。そのときは、表示されたシードで再現して直す。
- テストが増えるので、CI の時間が延びる。延びた分は測って記録する。
- 優先度の低い項目を外したので、それらの退行は見つけられないままである。

## 参考文献

なし
