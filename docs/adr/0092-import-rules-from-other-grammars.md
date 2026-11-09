# ADR 0092: ほかのファイルの規則を取り込む

ステータス: 採択

## 文脈

文法は、いまは一つのファイルで完結する。
記法の解説（[docs/syntax.md](../syntax.md)）にも、仕様書（[docs/specifications.md](../specifications.md)）にも、README にも、別のファイルの規則を使う手段はない。
`%import` と書くと、`peg-hs gen` は `error: unknown directive %import` で止まる（`~/.local/bin/peg-hs` の 0.1.0.0 で確かめた）。
verbatim ブロックに書く `import` は Haskell のモジュールの import であり、規則を取り込むものではない。

識別子、数、空白、文字列のエスケープのような字句の規則は、文法をまたいで同じ形になりやすい。
このリポジトリにも、写しで済ませている例がある。
`packages/peg-grammar/grammar/PegSyntax.hpeg` は、`scripts/regen-fixtures.sh` が `Peg.hpeg` を `sed` で書き換え、`SyntaxVariant.txt` を末尾に足して作る。
二つのファイルは 59 個の規則名を共有し、違うのは `%module`、`TopItem` の一行、末尾の `%syntax` と `%token` などの指示だけである。
`conformance/bench/JsonSyntax.hpeg` も、`json/Json.hpeg` から同じ形の `sed` で作る。
`conformance/commonmark/` の `Block.hpeg` と `Inline.hpeg` は、`Attr`、`Dest`、`Title` など 7 個の規則名を共有している。

規則を共有したくなる理由ははっきりしている。
迷うのは、どこまでを一度に入れるかである。
名前空間、選んだ規則だけの取り込み、取り込んだファイルからの取り込み、取り込んだファイルの verbatim ブロックと指示は、どれも欲しくなりうる。
ただ、それぞれが生成するモジュール、診断の位置、言語サーバー、ビルドのフック、wasm に別々の影響を持ち、互いに絡む。
この ADR は、絡みの少ない最小の形を決め、残りを後の ADR に回す。

考えるうえで外せない前提は四つある。

- 生成器は文法から単一の Haskell モジュールを出力する（仕様書の「生成するコード」）。生成器は Haskell を解析せず、verbatim ブロックを出現順に連結して写す（[ADR 0062](0062-warnings-of-pruned-generated-modules.md)、syntax.md の「verbatim ブロック」）。
- 診断の位置 `Loc` は行と桁だけを持つ（`Peg.Grammar` の `Loc`、`Diagnostic`）。ファイル名は `renderDiagnostic` に外から渡す。
- 言語サーバーは URI からファイルを読み書きしない。2026-11-07 の監査は、これをパストラバーサルの経路がない根拠として記録した（[監査の記録](../audits/2026-11-07-security-audit.md)の「防御として確認できた点」）。`Peg.Lsp.Server` は純粋な状態機械であり、`didOpen` と `didChange` が送ったテキストだけを扱う。
- `peg-hs.wasm` はファイルを読めない。ファイルの WASI の関数は誤りの番号を返す関数で置きかえてある（[ADR 0079](0079-stub-wasi-imports-outside-the-contract.md)）。`analyze` は文法をテキストで受け取る（[ADR 0078](0078-grammar-analysis-in-wasm.md)）。

ファイルの名前は、これまでの監査で二度扱った。
自動の探索はシンボリックリンクを辿らない（[ADR 0077](0077-fixes-of-the-security-audit.md)）。
ファイルの名前は生成したモジュールに入るので、制御文字を含む名前は拒む（[ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md)）。

## 実装すること

### 記法

規則を取り込むファイルを **ライブラリ** と呼ぶ。
ライブラリは、先頭近くに引数のない指示 `%library` を書いた `.hpeg` ファイルである。
取り込む側は、これまでどおり `%module` を書いた文法であり、以下では **根の文法** と呼ぶ。

```hpeg
# grammar/lex/Ident.hpeg
%library

Ident :: Text
Ident <- $(IdentStart IdentChar*) Sp

IdentStart <- [a-zA-Z_]

IdentChar <- [a-zA-Z0-9_]

Sp <- [ \t]*
```

```hpeg
# grammar/Calc.hpeg
%module Calc.Parser
%import lex/Ident.hpeg

%{
import Data.Text (Text)
}%

Assign :: (Text, Text)
Assign <- n:Ident '=' Sp v:Ident { (n, v) }
```

- `%import パス` は一行に一つのライブラリを書き、何度でも書ける。根の文法にだけ書ける。
- `%library` は一度だけ書け、`%module` と同じファイルには書けない。
- 記法の文法（`packages/peg-grammar/grammar/Peg.hpeg`）は変えない。指示はすでに `'%' 名前 行末までの引数` の一般の形で読んでおり（`Directive` の規則）、二つの指示はその上で組み立て（`Peg.Grammar.Assemble`）が解釈する。引数の後ろの `#` からはコメントになる（`directiveArg`）。

### パスと解決

パスは、それを書いた根の文法のディレクトリからの相対パスである。
検索パスは持たない。
パスの字句は次のとおりとし、外れるものは `%import` の引数の位置の誤りにする。

- `/` で区切った一つ以上の部分からなり、`/` で始まらない。
- 各部分は空でなく、ASCII の英字、数字、`_`、`-`、`.` だけからなり、`.` と `..` ではない。
- 最後の部分は `.hpeg` で終わる。

`..` を許さないので、取り込めるのは根の文法のディレクトリとその下のファイルだけになる。
この制約のおかげで、パスを書いたとおりに比べれば同じファイルかどうかが決まり、正規化は要らない。
字句を ASCII に絞るのは、制御文字を含む名前を拒む [ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md) の検査を、パスの形の検査に含めるためでもある。

ファイルを読む側（`peg-hs` のコマンド、peg-hooks、言語サーバー）は、パスの各部分がシンボリックリンクでないことを `pathIsSymbolicLink` で確かめてから読む。
リンクは辿らず、`cannot import lex/Ident.hpeg: it is a symbolic link` の誤りにする。
自動の探索がリンクを辿らない [ADR 0077](0077-fixes-of-the-security-audit.md) と同じ扱いである。
`%import` のパスは利用者がコマンドで名指ししたものではなく、文法が名指ししたものなので、名指ししたファイルの扱い（リンクの先を読む）には揃えない。

読めないファイルは `cannot import lex/Ident.hpeg: no such file` のように、`%import` の位置の誤りにする。
`%library` のないファイルを取り込んだときは、`lex/Ident.hpeg is not a library: it has no %library directive` とする。
同じパスを二度書いたときは、二つめの位置で `lex/Ident.hpeg is imported twice` とする。

ライブラリは `%import` を書けない。
取り込みは一段だけなので、循環も、同じライブラリを二つの道から取り込む形も起こらない。

### 名前

根の文法とライブラリの規則は、一つの名前の集まりに合わせる。
修飾名も、選んだ規則だけの取り込みも持たない。

- 同じ名前の規則が二つのファイルにあれば、これまでと同じ `duplicate definition of Ident` の誤りにする。位置は後に読んだほうの定義で、読む順は根の文法、ライブラリを `%import` の順である。
- ライブラリの規則が呼べるのは、同じライブラリの規則だけである。根の文法やほかのライブラリの規則を呼ぶと、ライブラリの中の位置で `undefined rule Ws` の誤りにする。こうしておくと、ライブラリは単独で検査でき、意味が取り込む側によって変わらない。
- 根の文法は、取り込んだ規則を自分の規則と同じに呼べる。雛形（[ADR 0031](0031-rule-templates.md)、[ADR 0055](0055-templates-and-parameterized-rules-in-stages.md)）も呼べ、根の文法の規則を引数に渡せる。
- 根の文法の指示（`%start`、`%entry`、`%nomemo`、`%token`、`%trivia`、`%inline`、`%recover`）は、取り込んだ規則を名指しできる。`PegSyntax.hpeg` が `%token Ident` を足す形がこれに当たる。
- 開始規則、`%entry` の規則、回復の規則から到達しないライブラリの規則は、誤りにせず、生成もしない。根の文法の規則が到達しないときは、これまでどおり誤りである。字句のライブラリは、根の文法が一部の規則しか使わなくても取り込めなければ役に立たないからである。

### ライブラリに書けるもの

ライブラリに書けるのは、`%library`、コメント、規則（型注釈、定義、雛形、引数付き規則）だけである。
ほかの指示と verbatim ブロックは、`a library cannot have %syntax; write it in the grammar that imports the library` のように、その位置の誤りにする（verbatim ブロックでは `%{ ... }%` と書く）。

生成するモジュールについての決定（モジュール名、言語拡張、`%env`、`%syntax`、`%deriving`、`%export`、`%safe`、`%recover`）は、根の文法だけが下す。
ライブラリのアクション、意味述語、型注釈に書いた Haskell の名前は、根の文法のモジュールの中で解決される。
`Text` を型に使うライブラリを取り込むなら、根の文法の verbatim ブロックが `Data.Text` を import する。
補助関数は、普通の Haskell のモジュールに置き、根の文法の verbatim ブロックから import するのを勧める。
Haskell のコードの共有には Haskell のモジュールがすでにあり、peg-hs の取り込みは規則だけを受け持つ。

ライブラリの規則の値の型も、根の文法の指示に従う。
型注釈のない規則は、`%syntax` の根の文法では `()` を返し（[ADR 0068](0068-untyped-rules-in-syntax-grammars.md)）、ほかの根の文法では型を推論する。
生成する型が導出するクラスは根の文法の `%deriving` で決まる（[ADR 0075](0075-generated-types-for-rules-without-actions.md)）。

ラベルの安全性は、規則を呼ぶ側の選択肢によって変わる。
`A <- B / "xy"` と `B <- "x" ("z" ^lab)` の文法で、`peg-hs gen` は `the label lab may reject valid input: where it fails, the alternative at 2:10 can match` と警告した（`B` の側だけを見ても判定できない）。
そのため `%safe` も根の文法に書く。

### 生成

出力は、これまでどおり単一の Haskell モジュールである。
規則は、根の文法の規則、ライブラリの規則を `%import` の順に並べてから、これまでと同じ検査と生成にかける。
並べる順を固定するので、同じ入力から同じ出力を生成する決定性は保たれる。

ライブラリのアクションと意味述語の `{-# LINE #-}` は、ライブラリのファイルを指す。
パスは、`optSourceName`（`peg-hs gen` に渡したパス、peg-hooks の `Grammar` のパス、wasm の `sourceName`）のディレクトリに `%import` のパスを `/` でつないだものである。
GHC は、アクションの型の誤りをライブラリの行と桁で報告する。

生成したモジュールの先頭のコメントは、これまでどおり根の文法だけを名指しする。

### 診断の位置

誤りと警告は、それが起きたファイルで報告する。
`peg-hs gen grammar/Calc.hpeg` は、ライブラリの誤りを `grammar/lex/Ident.hpeg:3:5: error: ...` と書く。
雛形を展開した規則の誤りは、これまでどおり雛形の定義の位置で報告するので、ライブラリの雛形ならライブラリの位置になる。

### 道具

- **`peg-hs gen`**：根の文法の `%import` を読み、上の解決をしてから生成する。ライブラリを `gen` に渡すと、これまでどおり `missing %module directive` になる。
- **`peg-hs parse`**：`gen` と同じに解決する。コンパイルしたパーサーのキャッシュの鍵（`Command.Parse` の `cacheDir`）は、いまは根の文法のテキストだけを含む。鍵に、取り込んだライブラリのパスとテキストを `%import` の順に加える。加えないと、ライブラリを変えても古いパーサーを実行する。
- **`peg-hs lint`**：根の文法は、取り込みを解決した上で検査し、根の文法の中の警告と info だけを報告する。ライブラリは単独で検査し、その中の警告と info を報告する。`lint` はディレクトリを再帰的に探すので、ライブラリの警告が根の文法の分と二重に出ないよう、この分け方にする。ライブラリを単独で検査するときは、根の文法がないと決まらない検査（開始規則と到達、`_env` と `%env` の対応、`%syntax` による値の扱い）をしない。
- **`peg-hs fmt`**：ファイルごとに整形し、取り込みは解決しない。整形の前後の比較も解析だけで行うので、ライブラリも根の文法と同じに整形できる。`%library` と規則だけのファイルの `fmt --check` は、いまも `%module` を求めずに成功する（0.1.0.0 で確かめた）。
- **`peg-hs label`**：取り込みを解決した文法の上で候補を判定し、根の文法の規則にだけラベルを挿入する。ライブラリのラベルの安全性は根の文法ごとに違いうるので、ライブラリのファイルは書き換えない。
- **`peg-hs parse --interpret` と `peg-hs test`**：[ADR 0090](0090-grammar-interpreter-without-ghc.md) のインタプリタと [ADR 0091](0091-grammar-test-command.md) の `peg-hs test` も、`gen` と同じに取り込みを解決した文法を使う。コンパイルする道のキャッシュの鍵は `peg-hs parse` と同じに扱う。wasm の `parse`（[ADR 0090](0090-grammar-interpreter-without-ghc.md)）の要求にも、`analyze` と同じ `"imports"` を足す。この ADR の実装がそれらより先になったときは、それらの実装でこの扱いを加える。
- **言語サーバー**：次の節に書く。
- **peg-hooks**：規則を登録するとき（`RulesM` の中、いま `moduleName` を `liftIO` で呼んでいるところ）に根の文法を読み、ライブラリのファイルも規則の `FileDependency` に加える。README には、ライブラリも `extra-source-files` に書くことを足す。[ADR 0085](0085-generate-modules-in-the-build-with-setup-hooks.md) の試作で、文法を `extra-source-files` に書かないと cabal は変更を見なかったので、ライブラリも同じだと見込む。
- **wasm**：`analyze` の要求に、パスからテキストへの対応 `"imports": {"lex/Ident.hpeg": "..."}` を足す。省略は空の対応とする。パスの字句の検査は `peg-hs gen` と同じで、対応にないパスは `cannot import lex/Ident.hpeg: no such file` とする。wasm は対応のテキストだけを使い、ファイルを読まない。`analyze` の結果のモジュールが同じ要求の `peg-hs gen` の出力とバイト単位で一致する約束は保つ。`format` は変えない。
- **エディタの文法**：tree-sitter と TextMate の文法に `%import` と `%library` を加え、`%import` の引数をパスとして区別する。`editors/test/` の一致のテストのサンプルに二つの指示を足す。capture と scope の名前は [ADR 0069](0069-richer-highlighting-and-format-on-save.md) の方針で実装のときに選ぶ。`editors/` に足すファイルはないので、`scripts/pack-editors.sh` と `editors/test/pack.txt` は変えない見込みである。

### 言語サーバー

言語サーバーは、`file://` の URI の文書についてだけ、取り込みを解決する。
ほかの URI（`untitled:` など）の根の文法の `%import` は、`imports need a file: save the grammar first` の誤りにする。

ライブラリのテキストは、開いている文書にあればそれを使い、なければディスクから読む。
読むのは純粋な `Peg.Lsp.Server` ではなく、入出力を受け持つ `Peg.Lsp` である。
`Step` に読んでほしいパスの並びを加え、`Peg.Lsp` が読んだ結果を内部のメッセージとしてサーバーに返す。
読むファイルは、上の字句とリンクの検査を通ったパスに限る。
これで「URI からファイルを読まない」は「根の文法のディレクトリの下の `.hpeg` のライブラリだけを、リンクを辿らずに読む」に変わるので、仕様書のその記述を直す。

- **診断**：根の文法の診断のうち、位置がライブラリにあるものは、根の文法の `%import` の行に `lex/Ident.hpeg:3:5: 文言` の形で出す。ライブラリを開いていれば、ライブラリ自身には単独の検査の診断を出す。開いているライブラリが変わると、それを取り込む開いている根の文法も検査し直す。
- **定義への移動**：取り込んだ規則の参照から、ライブラリの定義の位置へ移る。返す URI は、根の文法の URI のディレクトリに `%import` のパスをつないだものである。
- **ホバー**：取り込んだ規則にも、推論した型と生成した型を示す。
- 開いていないライブラリがディスクの上で変わったことは、根の文法を開き直すか編集するまで反映しない。

## データ構造

`Peg.Grammar` の型を次のように変える。
peg-grammar の公開の API を壊すので、版の付け方は [ADR 0009](0009-hackage-publication.md) と仕様書の「配布と版」に従う。

- `Loc` に、どのファイルの位置かを示す `locFile :: !Int` を加える。`0` は根の文法（または単独で検査するライブラリ）で、`i` は `i` 番目の `%import` のライブラリである。記法のパーサーは `0` で位置を作り、解決が取り込んだライブラリの位置の番号を付け替える。比較の順は、ファイル、行、桁の順になる。
- `Grammar` に `grammarImports :: [Located FilePath]`（`%import` のパス、書いた順）と `grammarLibrary :: Maybe Loc`（`%library` の位置）を加える。
- `renderDiagnostic` は、根の文法のパスと `grammarImports` から、`locFile` に当たるファイルの名前を決める。

取り込みの解決は peg-grammar の純粋な関数にする。

- 根の文法から、検査したパスの並びを取り出す関数。
- 根の文法と、パスとテキストの組の並びから、規則を合わせた `Grammar` を作る関数。テキストの解析、`%library` の検査、ライブラリの単独の検査、名前の合わせ、位置の付け替えを行う。

ファイルを読む部分（字句とリンクの検査、読めないときの誤り）は、`peg-hs` のコマンド、peg-hooks、言語サーバーが共有する一つの関数にし、peg-grammar の新しいモジュールに置く。
peg-grammar の依存に `directory` と `filepath` を加える。
どちらも GHC に付属するパッケージである。
wasm はこの関数を使わず、要求の対応を純粋な関数に渡す。

## 実装しないこと

- **修飾名と名前空間**（`Lex.Ident` の形）。記法の識別子に `.` を加えると、規則名、束縛名、`%export` の名前、生成する Haskell の名前のすべてに波及する。名前が衝突したら規則名を変えて避ける。
- **選んだ規則だけの取り込み**（`%import lex/Ident.hpeg (Ident, Sp)` の形）。到達しないライブラリの規則を生成しないので、選ぶ利点は名前の衝突を避けることだけになる。衝突が実際に困るとわかってから、別の ADR で決める。
- **ライブラリからの取り込み**。取り込みを一段に限ると、循環と、同じライブラリへの二つの道を考えずに済む。字句のライブラリが別のライブラリを要する例が出てきたら、別の ADR で循環の扱いとあわせて決める。
- **ライブラリの verbatim ブロック**。生成器は Haskell を解析しないので、ライブラリの `import` の行を根の文法の宣言より前に移せない。連結すると、宣言の後ろに `import` が来るモジュールになる。
- **ライブラリの指示**（`%safe`、`%nomemo`、`%token` など）。生成するモジュールと構文木についての決定は根の文法ごとに違いうる。`Peg.hpeg` と `PegSyntax.hpeg` は同じ規則に対して `%token` の有無が違う。
- **規則の上書き**。根の文法がライブラリの規則を同じ名前で定義し直す形は持たない。`PegSyntax.hpeg` の `TopItem` のように一つの規則だけが違うなら、その規則を根の文法の側に置き、残りをライブラリにする。
- **検索パス、絶対パス、`..`**。パッケージの外の文法を取り込む用途は、パッケージの中に写しを置いて代える。
- **ASCII の外の文字を含むパス**。必要になったら、制御文字の検査（[ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md)）とあわせて別の ADR で広げる。
- **言語サーバーの、ディスクの上のライブラリの変更の監視**（`workspace/didChangeWatchedFiles`）と、ライブラリの規則の参照を根の文法から探す、ワークスペースをまたぐ参照の検索。
- **ライブラリへのラベルの挿入**。`peg-hs label` と言語サーバーのコードアクションは、ライブラリのファイルを書き換えない。
- **このリポジトリの文法の書き換え**。`Peg.hpeg` と `PegSyntax.hpeg`、`Json.hpeg` の変種をライブラリに分けるのは、この ADR の実装が入った後に別に判断する。自己ホストの記法のパーサーを生成する手順に関わるためである。

## テスト設計

先に書いて失敗させてから実装する。

### peg-grammar

- 記法：`%import lex/Ident.hpeg` と `%library` を読み、`grammarImports` と `grammarLibrary` に入る。引数の後ろの `# コメント` は除かれる。
- パスの字句：`../x.hpeg`、`/abs.hpeg`、`a//b.hpeg`、`./a.hpeg`、`a.peg`、`a b.hpeg`、制御文字を含むパス、ASCII の外の文字を含むパスを、それぞれ `%import` の引数の位置の誤りにする。`lex/Ident.hpeg`、`a-b_c.d.hpeg` は通る。
- `%library` の検査：`%module` と `%library` の両方を書いたファイル、`%library` を二度書いたファイル、ライブラリの `%import`、ライブラリの各指示（`%start` から `%deriving` まで、この ADR の時点の指示のすべて）と verbatim ブロックを、それぞれその位置の誤りにする。
- 解決：二つのライブラリを取り込んだ文法の規則が、根の文法、ライブラリの `%import` の順に並ぶ。
- 名前：根の文法とライブラリの同名の規則、二つのライブラリの同名の規則を `duplicate definition` にし、位置が後に読んだほうのファイルと行を指す。ライブラリが根の文法の規則を呼ぶと、ライブラリの位置で `undefined rule` になる。
- 到達：根の文法から到達しないライブラリの規則は誤りにならず、根の文法の到達しない規則は誤りになる。
- 雛形：ライブラリの雛形を根の文法から根の文法の規則を引数にして呼べる。展開した規則の誤りがライブラリの雛形の定義の位置（`locFile` が `1`）で報告される。
- 指示：根の文法の `%token`、`%recover`、`%entry` がライブラリの規則を名指しできる。
- 位置：`renderDiagnostic` が `locFile` に応じて `grammar/Calc.hpeg` と `grammar/lex/Ident.hpeg` を書き分ける。
- 同じパスの二度の `%import`、`%library` のないファイルの取り込み、対応にないパスを、それぞれ文言どおりの誤りにする。
- ライブラリの単独の検査：到達、`_env`、`%syntax` に関わる検査をせず、ライブラリの中の `undefined rule` と `duplicate definition` は報告する。

### ファイルを読む関数

- 一時ディレクトリに、ライブラリへのシンボリックリンク、ライブラリのあるディレクトリへのシンボリックリンクを作り、どちらも `it is a symbolic link` の誤りにする（`docs/audits/reproduce-symlink.sh` の作り方に倣う）。
- ないファイルを `no such file` の誤りにする。

### peg-codegen と peg-cli

- golden：`packages/peg-codegen/test/fixtures/` にライブラリを取り込む文法とライブラリを置き、生成したモジュールの golden を `scripts/regen-fixtures.sh` で作る。ライブラリのアクションの `LINE` プラグマがライブラリのパスを指す。
- 生成したモジュールをコンパイルして入力を解析し、ライブラリの規則で読んだ値が返る。
- ライブラリのアクションに型の誤りを入れ、GHC の誤りがライブラリの行を指す。
- 決定性：同じ根の文法とライブラリから二度生成し、出力が一致する。
- `peg-hs parse`：ライブラリだけを書き換えた後の `parse` が、書き換えた後の文法で解析する（キャッシュの鍵の確かめ）。
- `peg-hs lint`：ライブラリにだけ `unused-binding` がある構成で、ディレクトリを `lint` すると警告が一度だけ出る。
- `peg-hs label --write`：ライブラリのファイルが書き換わらない。
- `peg-hs fmt`：ライブラリを整形でき、`fmt --check` が通る。

### 言語サーバー

`Peg.Lsp.Server` の純粋なテストで、ディスクの代わりにテキストを内部のメッセージで渡して確かめる。

- 根の文法を開くと、`Step` がライブラリのパスを読む要求を含む。テキストを返すと診断が出る。
- ライブラリの中の誤りが、根の文法の `%import` の行に `lex/Ident.hpeg:行:桁:` の形で出る。
- 取り込んだ規則の参照からの定義への移動が、ライブラリの URI と位置を返す。
- 開いているライブラリを変えると、それを取り込む根の文法の診断が更新される。
- `untitled:` の URI の根の文法の `%import` が誤りになる。

`Peg.Lsp` の入出力のテストで、一時ディレクトリのライブラリを実際に読み、シンボリックリンクを読まないことを確かめる。

### peg-hooks と wasm

- `examples/hooks/` の文法の一部をライブラリに分け、CI のジョブで次を確かめる。ビルドが通る。ライブラリの意味を変えるとモジュールが生成し直され、解析の結果が変わる。ライブラリに誤りを入れると、ビルドが `grammar/lex/....hpeg:行:桁: error:` で止まる。
- wasm：`imports` の対応を渡した `analyze` のモジュールが、同じ文法とライブラリの `peg-hs gen` の出力とバイト単位で一致する。対応にないパスの誤りと、`imports` を省いた要求の後方互換を確かめる。

### エディタの文法

- `editors/test/` の一致のテストのサンプルに、`%import` と `%library` を含むファイルを足し、tree-sitter と TextMate が記法の構文木と同じ範囲を返すこと、tree-sitter が `ERROR` を出さないことを確かめる。

## トレードオフ

- 名前の衝突を避ける手段が規則名の変更しかない。字句のライブラリの `Sp` と根の文法の `Sp` のように、短い名前ほど衝突しやすい。
- ライブラリは verbatim ブロックを持てないので、ライブラリのアクションが使う import と補助関数を、取り込む根の文法ごとに書く。補助関数を Haskell のモジュールに置けば、根の文法に書くのは import の行だけになる。
- ライブラリの Haskell の名前は根の文法のモジュールで解決されるので、根の文法が import を忘れたときの誤りは GHC が出す。peg-hs はそれを生成の前に知らせない。これは規則の中で束縛していない名前の扱い（syntax.md の「束縛」）と同じである。
- `..` を許さないので、`grammar/a/A.hpeg` と `grammar/b/B.hpeg` が共有するライブラリは、両方の下に置けない。根の文法を同じディレクトリかその上に置く必要がある。
- `Loc` に欄を加えるので、`Loc` を作るコードと、peg-grammar を使う利用者のコードを直す。
- 言語サーバーがディスクを読むようになり、2026-11-07 の監査の「URI からファイルを読まない」は成り立たなくなる。読む範囲は根の文法のディレクトリの下の、リンクでない `.hpeg` に限る。VS Code の拡張は、信頼していないワークスペースでも言語サーバーを動かす（`capabilities.untrustedWorkspaces` が `limited`）ので、そのワークスペースのライブラリも読む。読むだけで Haskell は動かさないので、`limited` の説明は保てる見込みである。
- `peg-hs lint` は、根の文法の中の警告とライブラリの中の警告を別々のファイルで報告する。ライブラリを根の文法と別の場所に置き、`lint` にライブラリを渡さないと、ライブラリの警告は出ない。

## 未決事項

- `%library` という名前と、引数を持たない形。後で修飾名を入れるなら、ライブラリの名前の引数を足せる形にしておく。
- パスの起点を、根の文法のディレクトリにするか、`peg-hs gen` が動くディレクトリやパッケージの根にするか。この ADR は根の文法のディレクトリにした。
- 言語サーバーで、ライブラリを開いたときに、それを取り込む根の文法の文脈で検査する方法（どの根の文法かを決める手段がない）。

## 参考文献

- Rich Hickey, "Simple Made Easy", Strange Loop 2011. https://www.infoq.com/presentations/Simple-Made-Easy/
- Cabal 3.16.1.0 のソース `Distribution/Simple/SetupHooks/Rule.hs`（`staticRule` と `FileDependency`）。
- [2026-11-07 のセキュリティ監査の記録](../audits/2026-11-07-security-audit.md)
