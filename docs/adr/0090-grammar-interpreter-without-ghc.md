# ADR 0090: GHC を使わずに文法を解釈して入力を解析する

ステータス: 採択

## 文脈

文法で入力がどう読まれるかを確かめる道具は、いま `peg-hs parse` だけである（[ADR 0036](0036-parse-command.md)）。
`parse` は生成したパーサーを `PATH` の `ghc` でコンパイルし、実行ファイルをキャッシュする。
そのため、`ghc` のない環境では入力を一つも試せない。
`PATH` に `ghc` のない環境で `~/.local/bin/peg-hs parse` を動かすと、`peg-hs parse needs ghc on PATH` を出して終了状態 1 で終わる。

コンパイルの待ち時間もある。
二つの規則の左再帰の文法（`E <- l:E '+' r:T / T`、`T <- [0-9]+`）と入力 `1+2+3` で、`--format cst` の初回はこの機械で約 4.3 秒かかり、キャッシュの効く二回目は約 0.16 秒だった。
文法を一文字書きかえるたびに、初回の待ち時間に戻る。

wasm（[ADR 0078](0078-grammar-analysis-in-wasm.md)）と言語サーバー（[ADR 0035](0035-language-server.md)）は、GHC を呼べない。
README の WebAssembly の節は、`peg-hs.wasm` が入力のテキストを解析しないと書いている。
[ADR 0036](0036-parse-command.md) は、文法の解釈による解析を「アクション、意味述語、引数を評価できないため」実装しないとした。
アクションの値（AST）は、たしかに解釈では得られない。
しかし、受理か拒否か、失敗の位置と期待集合（[ADR 0005](0005-error-reporting.md)）、ロスレスな構文木（CST、[ADR 0019](0019-lossless-syntax-tree.md)）は、アクションの値に依存しない。
[ADR 0091](0091-grammar-test-command.md) の `peg-hs test` が求めるのも、この三つである。

文法を解釈する仕組みは、peg-grammar のテストの中にすでにある。
`packages/peg-grammar/test/Labels.hs` の `run` は、ラベルの安全性の検査（[ADR 0028](0028-label-safety-check.md)、[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md)、[ADR 0081](0081-missing-tests.md)）が、ラベルを外した文法と同じ言語を受理するかを確かめるために使う。
読んで確かめた範囲では、`run` は次のものを持たない。

- 左再帰。規則の呼び出しの深さが 200 を超えると `Nothing` を返す
- メモ化と `%nomemo` の区別
- 期待集合と最遠到達位置。結果は全体に一致したかの真偽だけである
- 回復（[ADR 0021](0021-error-recovery.md)）と CST
- テンプレート。`ETemplate` で `Nothing` を返す

述語の扱いも、検査の目的に合わせた近似である。
整数との比較と `True`、`False` だけを評価し、ほかのコードの述語は成功したとみなす。
束縛の値は、その要素が読んだ文字数とみなす。
この近似は、検査が述語の値に頼らないことを確かめるためのもので、生成したパーサーと同じ結果を返すためのものではない。
`run` はテストの中にしかなく、公開の API でもない。

一方で、生成したパーサーの実行時の振る舞いは、peg-runtime の `Peg.Runtime.Internal` の関数がすべて決めている。
生成コードは、規則の本体を `choice`、`lit`、`many` などのコンビネータで組み、規則を `memo`、`memoLR`、`memoArg`、`nomemo` のどれかで包み、`runParser` か `runSyntaxRecover` で走らせる。
左再帰の成長と、種に依存するメモの項目の破棄（[ADR 0001](0001-bounded-left-recursion.md)、[ADR 0024](0024-discard-seed-dependents-only.md)）、期待集合の併合、ラベルの送出と回復、構文木の子の記録は、どれもこの関数群の中にある。
生成器が決めるのは、文法のどの部分にどの関数を当てるかだけである。
この関数群は `Text` と文法から独立した型 `P r s a` の上に書かれ、`P` の値は実行時に組み立てられる。
peg-grammar はすでに peg-runtime に依存している（[ADR 0015](0015-implementation-deviations.md)）。

## 実装すること

### インタプリタ

peg-grammar に公開のモジュール `Peg.Grammar.Interpret` を加える。
このモジュールは、文法の AST から `Peg.Runtime.Internal` のコンビネータで `P` の値を組み立て、生成コードと同じ実行関数で走らせる。
左再帰、メモ化、ラベル、回復、期待集合を自前で実装しない。
生成コードと同じ関数を呼ぶので、生成コードとの違いは「どの関数を当てるか」の対応の誤りだけに限られる。

インタプリタは、次のものを返す。

- **受理か拒否か**：`Either ParseError SyntaxNode`。拒否のときの `ParseError` は、生成したパーサーの `parse` が返すものと同じ値である（最遠到達位置、期待集合、送出されたラベル）
- **CST**：受理したときの構文木。生成したパーサーの `parseSyntax` が返す木と同じ形である
- **回復した構文エラー**：回復するモードの関数が、`runSyntaxRecover` の結果（どの入力にも返る木と `SyntaxError` の列）を返す

アクションの値（AST）は返さない。
アクションは読まずに捨てる。
verbatim ブロックも読まない。

文法に `%syntax` がなくても、`%syntax` を加えた文法として構文木を作る。
`%token`、`%trivia`、`%inline` は文法に書いたとおりとする。
`peg-hs parse --format cst` が `%syntax` を加えた文法から生成するのと同じ扱いである（[ADR 0036](0036-parse-command.md)）。

[ADR 0089](0089-rule-names-and-label-messages-in-errors.md) の `%expect` と `%message` も、生成コードと同じ実行時の関数（`expecting`、`labeledMessage`、`labeledMessageS`）を当てて扱う。
そのため、拒否のときの期待集合の表示名と、ラベルの文言も、生成したパーサーと同じになる。
この ADR の実装が [ADR 0089](0089-rule-names-and-label-messages-in-errors.md) より先になったときは、その実装で二つの指示を加える。

### 公開する関数

```haskell
-- | A grammar prepared for interpretation.
data Interpreter

-- | Prepare a grammar whose templates are expanded and which passed 'check'.
-- The diagnostics point at the predicates and arguments that the
-- interpreter cannot evaluate.
interpreter :: Grammar -> Analysis -> Either [Diagnostic] Interpreter

-- | Parse the input from a rule, the start rule when 'Nothing'.
interpret :: Interpreter -> Maybe Text -> Text -> Either ParseError SyntaxNode

-- | Parse with recovery (ADR 0021).
interpretRecover :: Interpreter -> Maybe Text -> Text -> (SyntaxNode, [SyntaxError])

-- | The name of a syntax kind: the rule name, or that of the text and error kinds.
interpreterKindName :: Interpreter -> SyntaxKind -> Text

-- | 'interpret' with a configuration, returning the counters (for tests).
interpretWith :: Config -> Interpreter -> Maybe Text -> Text -> (Either ParseError SyntaxNode, Stats)
```

呼ぶ側は、`peg-hs gen` と同じ順で `parseGrammar`、`expandTemplates`、`check` を通してから `interpreter` を呼ぶ。
`interpreter` の誤りには、`gen` と同じく `templateNotes` でテンプレートの呼び出しを添える。
規則の名前を渡す引数は、文法のどの規則も受け付ける。
`%entry` に限るかどうかは、呼ぶ側（CLI と wasm）が決める。

`interpreterKindName` が返す名前は、生成モジュールの `nameOfSyntaxKind` と同じである。
`SyntaxKind` の番号も、生成モジュールと同じ順で振る。

### 生成器と共有する判断

生成器が文法のどの部分にどの関数を当てるかのうち、次の二つは、いま peg-codegen の中に書かれている。

- 規則を包む関数の選択：`%nomemo` なら `nomemo`、引数がなく左再帰に関わるなら `memoLR`、引数がなければ `memo`、引数があれば `memoArg`（`Peg.Codegen` の `ruleDecl`）
- 構文木の子に束縛の名前を付ける要素の選択：規則の選択肢の最上位の要素のうち、束縛があり、値を持つ要素か、選択肢が値をそのまま返す要素（`itemStmtS` と `passThroughS`）。括弧の中の要素には付けない

この二つを、純粋な関数として peg-grammar に移す。
peg-codegen はその関数を呼んでコードを書き、インタプリタは同じ関数を呼んで `P` の値を組み立てる。
生成するコードは変わらない。
二つの実装が別々に判断すると、片方だけを直したときにずれるからである。
ほかの判断（終端、繰り返し、先読み、捕獲、ラベルと回復の規則の対応）は、式の構成子と実行時の関数が一対一に対応するので移さない。

### 解釈できる述語と引数

意味述語、規則の引数、`%env` の値は Haskell の式であり、インタプリタは Haskell を評価しない。
そこで、評価できる式の小さな集合を決め、文法がその外の式に頼るときは、文法ごと受け付けない。

**解釈できる式**は、前後の空白を除いたコードが次の形のものである。

- 述語：`True`、`False`、または `項 比較 項`。比較は `==`、`/=`、`<`、`<=`、`>`、`>=` のどれか
- 項：`原子`、`原子 + 原子`、`原子 - 原子`
- 原子：10 進の非負の整数、規則の引数の名前、`_col`

字句の間には空白を置いても置かなくてもよい。
括弧、`&&`、`||`、関数の呼び出しは含めない。
`True` と `False` は、ラベルの安全性の検査が解釈する定数の述語（[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md) の `constantPred`）と同じ扱いである。
`_col` は、生成コードと同じく `predicate` と `withCol` が渡す 0 から数える桁で、`%tabstop` に従う。

引数の名前は、同じ名前の束縛が見えない位置でだけ引数を指す。
束縛が引数を隠す位置（[ADR 0081](0081-missing-tests.md) の `shadowGrammar` の形）では、その名前は束縛の値、つまりアクションの値を指すので、解釈できない。
束縛が見えるかどうかは、静的検査（[ADR 0082](0082-static-check-of-binding-references.md)、[ADR 0083](0083-bindings-inside-a-group-are-not-visible.md)）と同じ規則で決める。

規則の引数のうち、解析の結果に関わるものだけを評価する。
引数が**読まれる**とは、その規則の述語に名前が現れるか、読まれる引数への実引数に名前が現れることとする（規則をまたいだ不動点で求める）。
読まれない引数は、アクションの中でしか使われないので、値がどうであっても受理と構文木は変わらない。
インタプリタは、読まれない引数の実引数を評価せず、メモの鍵にも入れない。

`interpreter` は、次のすべてが成り立つときに限り成功する。

1. すべての意味述語（`&{ … }` と `!{ … }`）が解釈できる式である
2. 読まれる引数へのすべての実引数が、解釈できる項である
3. 読まれる引数の型が `Int` と書かれている

成り立たないときは、解釈できない述語と実引数をすべて、コードの位置で報告する。
文言は `the interpreter cannot evaluate the predicate &{ isKeyword n }` のように、述語か実引数かと、書いたとおりのコードを示す。

`%env` は、この規則から帰結する扱いになる。
`_env` は原子に含まれないので、述語か読まれる引数への実引数が `_env` を読む文法は受け付けない。
`_env` をアクションの中でしか読まない文法は、環境の値なしで解釈する。

テンプレートは、展開した後の文法を解釈する（[ADR 0031](0031-rule-templates.md)、[ADR 0040](0040-templates-with-parameterized-rules.md)）。

### 解釈できない述語を成功とみなさない理由

テストの `run` のように、解釈できない述語を成功とみなす選択もある。
採らないのは、結果の誤りに向きがないからである。
順序付き選択の中で述語の値が変わると、生成したパーサーが採らない選択肢を採る。
すると、受理する入力が増えることも減ることもあり、構文木の形も変わる。
たとえば Lua の文法（`conformance/lua/Lua.hpeg`）の `Name <- n:$(...) !{ isKeyword n }` を成功とみなすと、`Name` が予約語にも一致する。
その結果を生成したパーサーの結果として示すと、文法の作者は誤った読み方を確かめたことになる。
失敗とみなす選択も、同じ理由で採らない。

### `peg-hs parse`

`peg-hs parse` に `--interpret` を加える。

```sh
peg-hs parse --interpret GRAMMAR.hpeg INPUT [--entry RULE]
```

- `--interpret` は、生成したパーサーをコンパイルせずに、インタプリタで解析して CST を表示する。`ghc` を探さず、キャッシュのディレクトリも作らない
- 出力は、同じ文法と入力での `--format cst` と、標準出力、標準エラー出力、終了状態のすべてで一致する。受理すれば `debugTree` の形の木を標準出力に書き、拒否すれば `renderParseError` の文言を標準エラー出力に書いて終了状態 1 で終わる
- `--format` の既定は `cst` になる。`--format ast` と `--format all` は、AST がアクションの値なので使い方の誤り（終了状態 2）とし、`--interpret` を外せば表示できることを伝える
- `--ghc-arg` は使い方の誤り（終了状態 2）とする
- `--entry` は、`--interpret` がないときと同じく `%entry` の規則に限る
- 文法が解釈できないときは、`interpreter` の誤りを `ファイル:行:桁: error: 文言` の形で報告し、`--interpret` を外せばコンパイルして解析できることを添えて、終了状態 1 で終わる
- `%env` を宣言した文法は、`--interpret` があり、上の規則で解釈できるときに限り扱う。`--interpret` がないときは、これまでどおり誤りとする

`--interpret` のないときの振る舞いは変えない。
文法が解釈できるときに自動でインタプリタを使う形は採らない（「トレードオフ」の節）。

### wasm

`peg-hs.wasm` に、エクスポート `parse`（`(i32, i32) -> i32`）を加える。
受け渡しは `analyze` と `format` と同じで、要求と応答は JSON である。

要求：

```json
{"grammar": "%module Calc\n...", "input": "1+2", "entry": null}
```

- `grammar`（必須）：文法のテキスト
- `input`（必須）：解析する入力のテキスト
- `entry`（省略可、既定は `null`）：`%entry` の規則の名前。`null` なら開始規則

応答：

```json
{
  "diagnostics": [],
  "accepted": true,
  "parseError": null,
  "tree": {"kind": "E", "start": 0, "end": 3, "label": null, "text": null, "children": []}
}
```

- `diagnostics`：文法の誤りと、`interpreter` の誤り。形は `analyze` の `diagnostics` と同じである。`entry` が `%entry` にない規則のときも、ここに誤りを入れる
- `accepted`：受理すれば `true`、拒否すれば `false`。`diagnostics` に誤りがあれば `null`
- `parseError`：拒否したときの `{"line", "column", "offset", "expected", "label", "message"}`。`line` と `column` は `Pos` の行と桁（1 から数え、桁はコードポイントで数える）、`offset` は UTF-8 のバイトの位置である。`expected` は期待集合の各要素を `renderParseError` と同じ文字列にした配列で、`label` は送出されたラベルか `null`、`message` は `renderParseError` の文言である。受理したときと誤りのあるときは `null`
- `tree`：受理したときの CST。ノードとトークンを同じ形のオブジェクトにする。`kind` は `interpreterKindName` の名前、`start` と `end` は UTF-8 のバイトの位置、`label` は束縛の名前か `null`、`text` はトークンの文字列（ノードでは `null`）、`children` は子の並び（トークンでは空）である。受理しなかったときは `null`

応答のキーを `error` でなく `parseError` とするのは、`{"error": ...}` が要求の誤りを表す既存の約束（[ADR 0078](0078-grammar-analysis-in-wasm.md)）と重ならないようにするためである。
要求の誤り（JSON でない、`grammar` か `input` がない、型が違う）は、`analyze` と同じく `{"error": "..."}` だけを返す。

`wasm/exports.json` と、`scripts/build-wasm.sh` が残すエクスポートに `parse` を加える。
import の約束（[ADR 0078](0078-grammar-analysis-in-wasm.md)、[ADR 0079](0079-stub-wasi-imports-outside-the-contract.md)）は変えない。

### 文書

- `docs/specifications.md` の「解析の表示」の項に `--interpret` を、「wasm」の節に `parse` を書く。「能力」に、GHC を使わない解析の範囲（解釈できる式）を書く
- README（英語と日本語）の `parse` の節と WebAssembly の節に、同じことを書く
- `peg-hs help parse` に `--interpret` と例を加える
- 実装のプルリクエストで、[ADR 0036](0036-parse-command.md) のステータスを「採択→文法の解釈による解析は ADR 0090」に、[ADR 0078](0078-grammar-analysis-in-wasm.md) のステータスに「入力の解析は ADR 0090」を加える

## データ構造とアルゴリズム

### 組み立て

インタプリタの値の型は、生成コードの構文木のモードと同じ `((), [Child])` である。
アクションの値を持たないので、値はすべて `()` になる。
式の構成子は、生成コードの構文木のモード（`Peg.Codegen` の `exprCodeSU`）と同じ関数に対応させる。

| 式 | 実行時の関数 |
| --- | --- |
| `ELit t orig` | `plain (lit t orig)` |
| `EClass rs orig` | `plain (cls rs orig)` |
| `EAny` | `plain anyChar` |
| `ERef` | 規則の表から引いた `P`。読まれる引数があれば `withCol` の中で実引数を評価して渡す |
| `EGroup` | `choice` |
| `EStar`、`EPlus`、`EOpt` | `manyS`、`many1S`、`optionalS` |
| `EAnd`、`ENot` | `plain . andP`、`plain . notP` |
| `ECapture` | `captureS` |
| `ELabel` | `labeledS`。回復の規則は `%recover` の最初の対応である |
| `EPred b c` | `plain (predicate f)`。`f` は解釈した式（`b` が偽なら否定） |
| `EDiscard` | `voidS` |

規則は、共有する判断の関数が選んだ `memo`、`memoLR`、`memoArg`、`nomemo` で包み、`%inline` でなければ `node`（`%token` なら `token`）で包む。
規則の名前の文字列は、生成コードと同じものを渡す。
`Stats` の鍵が規則の名前なので、評価の回数を生成コードと比べられる。

### メモ表の置き場

生成コードは、規則ごとのメモ表を、生成したレコード（`Peg'Store`）の欄に持つ。
インタプリタは、規則の名前からメモ表への `Map` を持つレコードを置き場とし、`runParser` などに渡す `ST s (store s)` で、すべての規則のメモ表を作る。
`memo` と `memoLR` には `Table s ((), [Child])` を、`memoArg` には読まれる引数の値の列を鍵とする `ArgTable s [Int] ((), [Child])` を与える。

規則の `P` の値は、規則の名前から `P` への表として一度だけ組み立て、規則の参照はこの表を引く。
表は遅延評価で自分自身を参照する。

## 実装しないこと

- AST（アクションの値）。Haskell を評価しない限り得られない。AST は `peg-hs parse` の GHC の道で表示する
- 解釈できる式の拡張（括弧、`&&`、`||`、`not`、捕獲した文字列の `T.length` など）。Lua の長括弧の `LongClose(T.length e)` のように、拡張で扱える文法が増える形はある。どこまで広げるかは、実際の文法の述語を集めてから別の ADR で決める
- 解釈できない述語を成功か失敗とみなすオプション（「解釈できない述語を成功とみなさない理由」の節）
- `%env` の値の受け渡し
- `peg-hs parse` と wasm での回復するモードの表示。ライブラリは `interpretRecover` を持つが、CLI と wasm に出すかは別の ADR で決める
- 言語サーバーの機能（入力を試すコマンド、カスタムの要求、エディタの UI）。インタプリタは peg-grammar にあるので、peg-lsp からそのまま呼べる。何を出すかは別の ADR で決める
- 文法が解釈できるかを lint や言語サーバーの診断として出すこと
- `peg-hs parse` で、文法が解釈できるときに自動でインタプリタを使うこと
- インタプリタの速さの目標。下の計測の結果を見てから決める

## テスト設計

先に書いて失敗させてから実装する。

### インタプリタの単体テスト（peg-grammar のテスト）

- **左再帰**：[ADR 0001](0001-bounded-left-recursion.md) のテストの文法で、生成したパーサーのテストと同じ結果になる。`E <- E '+' n / n` が `n+n+n` を左結合の木にする。Medeiros らの間接左再帰の例（`L <- P '.x' / 'x'`、`P <- P '(n)' / L`）。nullable な式を前置した左再帰
- **ラベル**：送出したラベルが順序付き選択の後戻りを止め、`ParseError` の `parseErrorLabel` に入る
- **回復**：`%recover` のある文法で、`interpretRecover` の木が誤りのノードを含み、`SyntaxError` の列が回復した範囲を持つ
- **ロスレス性**：回復するモードで、ランダムな入力に対し、木のトークンを連結すると入力に戻る（プロパティテスト）
- **解釈できる述語**：`Labels.hs` の `countGrammar`（空白がちょうど二つ）を、`""`、`" "`、`"  "`、`"   "` のうち `"  "` だけ受理する。`_col` を読む述語が `%tabstop` に従う
- **解釈できない文法**：次の文法を `interpreter` が拒み、解釈できない述語と実引数をすべて、コードの位置で報告する
  - `!{ isKeyword n }` のように関数を呼ぶ述語
  - `Labels.hs` の `shadowGrammar`（束縛が引数を隠す）
  - 述語で `_env` を読む文法
  - 読まれる引数に `T.length e` を渡す文法
  - 読まれる引数の型が `Int` でない文法
  - テンプレートの中の解釈できない述語。誤りにテンプレートの呼び出しが添えられる
- **読まれない引数**：アクションでしか使わない引数に `T.length e` を渡す文法と、`_env` をアクションでしか読まない `%env` の文法を、解釈できる
- **テストの `run` との一致**：`genGrammar` のランダムな文法のうち左再帰とラベルのないものについて、`run False` が `Just` を返す入力では、`interpret` の受理と `run` の結果が一致する（プロパティテスト）

### 生成したパーサーとの一致（peg-codegen のテスト）

peg-codegen のテストは、コミットした生成モジュールをコンパイルして使う。
同じ文法をインタプリタでも解析し、次のものが一致することを確かめる。

- 拒否したときの `ParseError`（位置、期待集合、ラベル）と、受理か拒否か。生成モジュールの `parse` と比べる
- 受理したときの CST。`%syntax` の文法は `parseSyntax` と比べる。`%syntax` のない文法は、`%syntax` を加えて生成したモジュールがないので比べない
- 回復するモードの木と `SyntaxError` の列。`%recover` と `%syntax` のある文法は `parseSyntaxRecover` と比べる

木は `debugTree` の文字列で比べる。

対象の文法と入力は次のとおりである。

- **フィクスチャ**：`packages/peg-codegen/test/fixtures` の文法のうち、`interpreter` が受け付けるものすべて。受け付ける文法の一覧をテストに書き、一覧が変わったら気付けるようにする。入力は、フィクスチャのテストが使っている入力と、文法のリテラルと文字クラスの端の文字からなる長さ 3 以下のすべての文字列
- **ランダムな文法**：固定したシードで作った 50 個の小さな文法を、規則の名前の接頭辞で分けて一つの文法にまとめ、各文法の開始規則を `%entry` に挙げたフィクスチャ（`Differential.hpeg`）を加える。生成モジュールは、ほかのフィクスチャと同じく `scripts/regen-fixtures.sh` で作ってコミットする。文法の生成器は `Labels.hs` の `genGrammar` を基に、左再帰、`%recover` のあるラベル、`%nomemo`、`%token`、`%inline`、束縛を加えたものとし、生成器とシードから作った文法がコミットした `.hpeg` と一致することもテストする。入力は `abc` からなる長さ 4 以下のすべての文字列

共有する判断の関数を peg-grammar に移した後も、生成モジュールがバイト単位で変わらないことは、フィクスチャの再生成の一致の検査（既存）で確かめる。

### 適合性テストのデータでの一致（peg-conformance のテスト）

- **JSON**：`conformance/json/Json.hpeg` と JSONTestSuite の `test_parsing` の 318 ファイルで、受理か拒否かと `ParseError` が、生成したパーサーと一致する
- **構文木と回復**：`conformance/bench/JsonSyntax.hpeg` と `JsonRecover.hpeg` で、同じ 318 ファイルの CST と、回復するモードの木と `SyntaxError` の列が一致する
- **評価の回数**：`NestedLR2.hpeg`、`NestedLR4.hpeg`、`NestedLR8.hpeg`、`Pathological.hpeg` で、`ComplexityMain.hs` が使う入力について、`interpretWith defaultConfig {cfgCount = True}` の `statsEvaluations` が、生成モジュールの `peg'parseWith` のものと一致する。メモ化と左再帰の成長（[ADR 0024](0024-discard-seed-dependents-only.md)）が同じ順で同じ回数だけ評価されることを確かめるためである

Lua、TOML、CommonMark の文法は、解釈できない述語を含むので対象にしない。
三つの文法を `interpreter` が拒むこともテストする。

### CLI のテスト（peg-cli のテスト）

- `parse --interpret` の出力を golden ファイルと比べる。受理する入力と拒否する入力の両方
- 同じ文法と入力で、`parse --interpret` と `parse --format cst` の標準出力、標準エラー出力、終了状態が一致する。`ghc` の要るテストとして、CI の Haskell のジョブで動かす
- `PATH` を `ghc` のないディレクトリだけにしても、`parse --interpret` が動く
- `--interpret` と `--format ast`、`--format all`、`--ghc-arg` を組み合わせると、終了状態 2 になる
- 解釈できない文法で、位置つきの誤りを出して終了状態 1 になる
- `_env` をアクションでしか読まない `%env` の文法を、`--interpret` で解析できる。`--interpret` がなければ、これまでどおり誤りになる

### wasm のテスト

- ネイティブのテスト（`peg-wasm-test`）：`parse` の応答を、`interpret` の結果から期待する JSON と比べる。受理、拒否、文法の誤り、解釈できない文法、`%entry` にない `entry`、要求の誤りを一つずつ含める。非 ASCII の入力で `offset` がバイトの位置、`column` がコードポイントの桁になる
- Deno のテスト：エクスポートに `parse` があり、import が約束の一覧の中にある。ネイティブのテストの `parse` の項目が、wasm でも同じ応答になる

### 実装の後に測って記録すること

インタプリタの速さは、まだ測っていない。
実装の後に、`conformance/bench` の JSON の入力で、インタプリタと生成したパーサーの解析の時間を測り、`docs/benchmarks/` に記録する。
この ADR では速さの目標を置かない。

## トレードオフ

- インタプリタを peg-runtime のコンビネータの上に作るので、左再帰、メモ化、ラベル、回復、期待集合の実装は一つで済み、生成コードとの違いは関数の当て方の誤りに限られる。代わりに、`Peg.Runtime.Internal` の関数を変えると、生成コードだけでなくインタプリタも影響を受ける。同じリポジトリで版を揃えて出すので、二つは一緒に直せる
- テストの `run` のように独立したインタプリタを書けば、peg-runtime を経由しない分だけ単純になる。しかし、[ADR 0024](0024-discard-seed-dependents-only.md) の種に依存する項目の破棄や、失敗の記録の併合を、もう一度書くことになる。一致のテストでずれは見つかるが、直す場所が二つになるので採らない
- インタプリタを peg-runtime に置くことはできない。文法の AST は peg-grammar にあり、peg-runtime は他のどのパッケージにも依存しない（仕様書の「モジュール構成」）。新しいパッケージを作ることもしない。peg-grammar はすでに peg-runtime に依存し、peg-cli、peg-lsp、peg-wasm はすでに peg-grammar に依存しているので、依存の向きは変わらない。代わりに、peg-grammar の公開の API が増える
- 解釈できる式を小さく決めたので、この ADR の時点で解釈できない文法が多い。このリポジトリの文法では、Lua、TOML、CommonMark、`.hpeg` 記法の文法（`packages/peg-grammar/grammar/Peg.hpeg`）が、関数を呼ぶ述語を含むので解釈できない。解釈できる文法の結果は生成したパーサーと一致し、解釈できない文法は理由とともに拒む。範囲の広さより、結果を信じられることを優先した
- `--interpret` を明示のオプションにしたので、利用者は二つの道を選ぶ必要がある。自動で選ぶと、文法に述語を一つ足しただけで、黙ってコンパイルの道に変わり、待ち時間と `ghc` の要否が変わる。インタプリタに誤りがあったときに、どちらの道の結果かがわかることも、明示を選んだ理由である。`peg-hs test`（[ADR 0091](0091-grammar-test-command.md)）は文法で道を選ぶので、二つのコマンドで選び方が異なる
- `--interpret` はコンパイルした実行ファイルを動かさず、キャッシュのディレクトリも使わない。キャッシュのディレクトリをほかの利用者が書ける環境の問題（[ADR 0077](0077-fixes-of-the-security-audit.md)）は、この道にはない
- 読まれない引数をメモの鍵から外すので、そういう引数を持つ文法では、`Stats` の評価の回数が生成コードより少なくなりうる。受理と構文木は変わらない。評価の回数の一致は、引数のない文法でだけ確かめる
- 解釈できる式の整数は Haskell の `Int` で計算する。読まれる引数の型を `Int` と書いたものに限るので、生成コードと同じ型の演算になり、桁あふれも同じ規則に従う

## 参考文献

- Ford, B. 2004. Parsing Expression Grammars: A Recognition-Based Syntactic Foundation. POPL 2004.
- Medeiros, S., Mascarenhas, F., Ierusalimschy, R. 2014. Left Recursion in Parsing Expression Grammars. Science of Computer Programming 96.
