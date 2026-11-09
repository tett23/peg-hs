# ADR 0089: 規則の表示名とラベルの文言を誤りの報告に使う

ステータス: 採択

## 文脈

peg-hs で作った言語の利用者が目にする誤りは、`renderParseError` の一行である。
その一行が、文法の作者でない人にとって読みにくい。

次の文法で確かめた。

```hpeg
%module Calc

Sum :: Int
Sum <- a:Expr '+' b:Expr { a + b }
     / Expr

Expr :: Int
Expr <- '(' e:Sum (')' ^close) { e }
      / n:$[0-9]+ { read (T.unpack n) }
      / '-' e:Expr { negate e }

%{
import qualified Data.Text as T
}%
```

いまの main から作った `peg-hs parse`（`renderParseError` で誤りを表示する）に入力を与えると、次のように表示された。

| 入力 | 表示 |
|---|---|
| `1+` | `1:3: expected '(', '-' or [0-9]` |
| `x` | `1:1: expected '(', '-' or [0-9]` |
| `(x` | `1:2: expected '(', '-' or [0-9]` |
| `1+2x` | `1:4: expected [0-9] or end of input` |
| `(1+2` | `1:5: expected ')' or [0-9]` |
| `1+(2` | `1:5: expected ')', '+' or [0-9]` |

一つめの問題は、式が来るべき位置で、式を始められる終端がすべて並ぶことである。
`1+` の利用者に要る情報は「式が要る」であって、`(` と `-` と数字の列挙ではない。
式の始まりの終端は、言語が大きくなるほど増える。
[ADR 0005](0005-error-reporting.md) は期待集合を終端の単位に決め、規則を人間向けの名前で表示する仕組み（PEG.js の human-readable name に相当）を、将来の検討に回した。

二つめの問題は、ラベルを送出しても、表示が変わらないことである。
`(1+2` と `1+(2` は `^close` を送出して失敗するが、表示は期待集合の列挙のままだった。
`ParseError` はラベルの名前を `parseErrorLabel` に持つが、`renderParseError` はそれを使わない。
[ADR 0021](0021-error-recovery.md) は、peg-hs はラベルに文言を付けず、ラベルから利用者向けの文言への対応を利用者の責任とした。
その結果、文言の対応表は文法の外の Haskell のコードに置かれる。
peg-hs 自身もそうしている。
記法のパーサーの文言は、`packages/peg-grammar/src/Peg/Grammar/Parser.hs` の `labelMessage` に、ラベルの名前ごとに書いた表から作る（[ADR 0027](0027-switch-to-self-hosted-parser.md)）。
ラベルを足すたびに、文法と別のファイルの表を揃える手間がかかる。

二つの問題は、どちらも「文法の作者が知っている名前を、誤りの表示に届ける手段がない」ことから来ている。
そのため、一つの ADR で扱う。

いまの実装を読んで、次のことを確かめた。

- 期待集合の要素（`Expected`）は、リテラル、文字クラス、任意の一文字、入力の終わりの四つで、構築子の順が表示の順を決める（`packages/peg-runtime/src/Peg/Runtime/Internal.hs`）
- 規則の評価（`memo`、`memoArg`、`nomemo`、`memoLR`）は、規則の中の失敗を規則ごとの記録に分けてメモ表の項目に保存し、メモ表から結果を返すときに記録を合わせ直す
- ラベル付きの式（`labeled`）も、式の中の失敗を局所の記録に分けてから外の記録に合わせる
- 回復しないモードの `ParseError` の位置は、ラベルを送出したときも最遠の失敗の位置である
- `peg-hs gen` は、`%expect` と `%message` を `unknown directive` の誤りにする。規則名の後に文字列を置く `B "b" <- "c"` は、`expected a rule, a directive or %{ ... }%` の誤りになる。どちらの書き方も、いま受理される文法の意味を変えない

## 実装すること

### 記法

二つのディレクティブを加える。

| ディレクティブ | 意味 |
|---|---|
| `%expect Name "文字列"` | 規則 `Name` の**表示名**。誤りの期待の一覧で、規則の終端の代わりに表示する |
| `%message label "文字列"` | ラベル `label` の**文言**。ラベルで失敗したときの誤りの表示に使う |

- 文字列は、規則の中の `"..."` のリテラルと同じ書き方とし、同じエスケープ（`\n`、`\t`、`\r`、`\\`、`\'`、`\"`、`\[`、`\]`、`\-`、`\u{...}`）を使える
- 閉じた `"` の後の `#` から行末までは、ほかのディレクティブと同じくコメントである。文字列の中の `#` はコメントの始まりにならない
- 一つの規則に `%expect` は一つまで、一つのラベルに `%message` は一つまでとする
- 誤りにするもの
  - 形が違う：`%expect expects a rule name and a string`、`%message expects a label and a string`
  - 文字列が閉じていない、未知のエスケープ：規則の中のリテラルと同じ文言
  - 空の文字列、または改行などの制御文字（U+0000 から U+001F と U+007F）を含む文字列：`the description is empty`、`the message contains a control character` の形。`renderParseError` の一行を保つためである
  - 二つめの `%expect` と `%message`：`duplicate %expect for rule Name`、`duplicate %message for label l`
  - 定義していない規則：`undefined rule Name`（`%nomemo` などと同じ）
  - 雛形の名前：`the template Name cannot be named in %expect`（`%nomemo` などと同じ）
  - 文法に現れないラベル：`the label l does not appear in the grammar`（`%recover` と `%safe` と同じ）

### 表示名の意味論

規則 `R` に表示名 `n` があるとき、`R` を位置 `i` で評価した結果の失敗の記録を、次のように変える。

- 規則の中で最も遠い失敗の位置が `i` なら、その位置の期待集合を `{n}` だけに置き換える
- 規則の中で最も遠い失敗の位置が `i` より先なら、記録を変えない
- 規則の中に失敗がなければ、何もしない

規則が成功したか失敗したかは問わない。
規則が入力を消費せずに失敗したときだけ表示名にする、という megaparsec の `label` の条件を、最遠の失敗で報告する peg-hs に移したものである。
規則の中で最も遠い失敗が始まりの位置にあるのは、規則のどの選択肢もその位置より先に進めなかったときである。
そのとき利用者に伝えるべきことは「ここに `R` が来るべきだった」であり、表示名がそれを表す。
規則がいくらか読んだ後で失敗したときは、規則の内側の具体的な終端のほうが役に立つので、置き換えない。
すべての失敗を表示名に置き換える方式では、`1+2x` の `[0-9]` のような規則の内側の誤りまで「expected expression」と報告することになり、位置と内容が合わなくなる。

表示名を持つ規則が入れ子になったときは、外側の規則の置き換えが最後に働くので、外側の表示名が残る。
置き換えは失敗の記録の集合だけを変え、位置を変えない。
解析が受理する入力と、`ParseError` の位置は、表示名の有無で変わらない。

`Calc` の文法に `%expect Expr "expression"` を加えると、文脈の表の入力は次のように表示されるはずである（この ADR の時点の実行の結果ではなく、上の規則から求めた期待値である）。

| 入力 | 表示 |
|---|---|
| `1+` | `1:3: expected expression` |
| `x` | `1:1: expected expression` |
| `(x` | `1:2: expected expression` |
| `1+2x` | `1:4: expected [0-9] or end of input`（変わらない） |

`1+2x` の `[0-9]` は、位置 2 から始めた `Expr` の中の位置 3 の失敗なので、置き換わらない。

### 文言の意味論

ラベル `l` に文言 `m` があるとき、次のように使う。

- 回復しないモード：送出されたラベルが `l` なら、`ParseError` の新しい欄 `parseErrorMessage` に `m` が入る。`renderParseError` は、文言があれば期待の一覧の代わりに `行:桁: m` を表示する
- 回復するモード：ラベル `l` から回復して記録する `SyntaxError` の新しい欄 `syntaxErrorMessage` に `m` が入る
- 文言のないラベルの表示は、いまと変わらない（期待の一覧）

`Calc` の文法に `%message close "missing ')'"` を加えると、`(1+2` と `1+(2` は `1:5: missing ')'` と表示されるはずである。

`parseErrorLabel` と `syntaxErrorLabel` は残す。
文言を多言語にしたい利用者や、Golem のように診断コードに写す利用者は、これまでどおりラベルの名前から自分の表を引ける。

### peg-runtime のデータ構造

`Peg.Runtime` が公開する型を次のように変える。

```haskell
data Expected
  = ExpectedName !Text      -- 新設。%expect の表示名
  | ExpectedLiteral !Text
  | ExpectedClass !Text
  | ExpectedAny
  | ExpectedEnd

data ParseError = ParseError
  { parseErrorPos :: !Pos
  , parseErrorExpected :: !(Set Expected)
  , parseErrorLabel :: !(Maybe Text)
  , parseErrorMessage :: !(Maybe Text)   -- 新設。送出されたラベルの文言
  }

data SyntaxError = SyntaxError
  { syntaxErrorLabel :: !(Maybe Text)
  , syntaxErrorRange :: !(Int, Int)
  , syntaxErrorPos :: Pos
  , syntaxErrorExpected :: !(Set Expected)
  , syntaxErrorMessage :: !(Maybe Text)  -- 新設。ラベルの文言
  }
```

- `ExpectedName` を構築子の先頭に置き、期待の一覧で表示名を終端より先に並べる。表示名は終端より大きな単位を表すので、利用者が先に読むべきものだからである。表示は引用符を付けない（`expected expression or 'return'`）。リテラルは引用符付きで表示されるので、表示名と取り違えない
- `renderParseError` は、`parseErrorMessage` があれば `行:桁: 文言` を、なければいまと同じ形を返す
- `renderSyntaxError :: SyntaxError -> Text` を加える。`syntaxErrorPos` の位置に、文言があれば文言を、なければ `renderParseError` と同じ期待の一覧を付ける。回復した誤りを表示するために、利用者がいまは自分で書いている処理（`Peg.Runtime.Internal` の Haddock の例）を置き換える

内部の `Res` の送出は、位置とラベルに加えて文言を持つ（`Throw !Int !Text !(Maybe Text)`）。
メモ表の項目は `Res` を保存するので、メモ表から返した送出も文言を持つ。

### アルゴリズム

表示名は、`Peg.Runtime.Internal` の新しい関数 `expecting` で実装する。
`labeled` が局所の失敗の記録を分けるのと同じ手順で、規則の本体の失敗の記録を分け、置き換えてから外の記録に合わせる。

```haskell
expecting :: String -> P r s a -> P r s a
expecting rawName p = P $ \c i -> do
  saved <- readSTRef (ctxFail c)
  writeSTRef (ctxFail c) NoFailure
  r <- unP p c i
  local <- readSTRef (ctxFail c)
  let renamed = case local of
        Failure j _ | j == i -> Failure i (S.singleton (ExpectedName name))
        f -> f
  writeSTRef (ctxFail c) (mergeFailure saved renamed)
  pure r
  where
    name = T.pack rawName
```

- 生成器は `expecting` を、メモ化の関数（`memo`、`memoArg`、`nomemo`、`memoLR`）の内側、規則の本体の外側に置く。こうすると、メモ表の項目に置き換えた後の記録が入り、メモ表へのヒットの有無で報告が変わらない（[ADR 0005](0005-error-reporting.md) の要件）
- 左再帰の規則では、成長の反復ごとに置き換える。どの反復も同じ位置 `i` から始まるので、条件は反復によらない
- 期待集合は遅延したまま扱い、置き換えのために集合を作らない（[ADR 0070](0070-faster-checks-in-the-language-server.md)）
- 文言は、新しい関数 `labeledMessage` と `labeledMessageS` で扱う。`labeled` と `labeledS` に文言の引数を足さず、別の関数にするのは、`%message` を使わない文法の生成コードを変えないためである

### 生成器

- 表示名のある規則の本体を `PegRt.expecting "表示名"` で包む
- 文言のあるラベルには `PegRt.labeledMessage`（`%syntax` では `PegRt.labeledMessageS`）を生成し、文言を渡す
- 表示名と文言は、ほかの文字列と同じく `hsString` で Haskell の文字列リテラルにする。`%expect` と `%message` の値は埋め込みのブロックの外の値なので、Haskell の宣言として読める値が生成モジュールに入らないことを、テストで確かめる（[ADR 0080](0080-fixes-of-the-security-audit-of-2026-11-07.md)）
- `%expect` と `%message` を使わない文法の生成コードは変わらない
- `peg-hs parse` が生成したパーサーと一緒にコンパイルする peg-runtime のソース（`packages/peg-cli/app/Embedded.hs`）は、`scripts/regen-fixtures.sh` が呼ぶ `scripts/embed-runtime.py` で作り直す（[ADR 0036](0036-parse-command.md)）。`peg-hs parse` は `renderParseError` で誤りを表示するので、表示名と文言がそのまま表示に出る
- `peg-hs gen --strip-labels` で作るラベルのない文法（`stripLabels`）は、`%message` を除き、`%expect` を残す。`%expect` は受理する言語を変えないので、ラベルの安全性を確かめる比較（[ADR 0029](0029-label-safety-implementation-deviations.md)）に影響しない

### 記法を読む道具

文字列の中の `#` をコメントとしないために、ディレクティブの引数とコメントを分ける処理を、`%expect` と `%message` で文字列を知るものにする。
いまこの処理は三か所にあり、どれも最初の `#` で分ける。

- `Peg.Grammar.Assemble` の `directiveArg`：引数を読む。`Grammar` に `grammarExpects :: [(Located Text, Located Text)]` と `grammarMessages :: [(Located Text, Located Text)]` を加え、静的検査を `Assemble` と `Check` に加える
- `Peg.Grammar.Format` の `directiveParts`：`peg-hs fmt` が文字列の中の空白を変えないようにする
- `Peg.Grammar.Highlight` の `directive`：`%expect` の規則名を `HDirectiveRule`、`%message` のラベルを `HDirectiveLabel`、文字列を `HLiteral` にする

三か所は、`Assemble` に置く一つの関数を使う。

言語サーバーは、ハイライトの種類から規則名の参照を作るので（[ADR 0069](0069-richer-highlighting-and-format-on-save.md)）、`%expect` の規則名にも定義への移動、参照の検索が働く。
診断は `Assemble` と `Check` の誤りがそのまま出る。

wasm の `analyze` は、`%expect` と `%message` の `Directive` のノードに、`%recover` と同じく二つの `Value` を付ける。
一つめは規則名かラベル、二つめは書いたとおりの文字列（引用符を含む）である。
JSON のノードの種類は増やさない。
README（日本語と英語）の WebAssembly の節の `Directive` の行を直す。

エディタの文法も、ハイライトに合わせる。

- tree-sitter（`editors/tree-sitter-hpeg/grammar.js`）：`%expect` は `rule_name_argument` と文字列、`%message` は `label_argument` と文字列を持つ選択肢を `directive` に加える。文字列の中の `#` をコメントにしない。生成済みのパーサー（`src/`）と問い合わせ、コーパスとハイライトのテストを更新する
- TextMate（`editors/textmate/hpeg.tmLanguage.json` と `editors/vscode/syntaxes/hpeg.tmLanguage.json`）：二つのディレクティブの型を加える
- `editors/test` の例とゴールデンに二つのディレクティブを加える。`editors/` にファイルを足さないので、`scripts/pack-editors.sh` と `editors/test/pack.txt` は変えない

### 記法のパーサー

`packages/peg-grammar/grammar/Peg.hpeg` のラベルの文言を、`labelMessage` の表から `%message` に移す。
規則の文法は変えないので、記法のパーサーの規則は変わらない。
`Assemble` が `%message` を受理した後に `scripts/regen-fixtures.sh` で生成し直せばよく、二段の生成は要らない。

ただし、次のラベルの文言は誤りの位置の文字で変わるので、`labelMessage` に残す。

- `escape`：`unknown escape \x` か `unexpected end of file`
- `action` と `argcode`：`unbalanced bracket in Haskell code` か `unterminated Haskell code`

`parseTops` と `Outline` は、文字で変わる三つのラベルなら `labelMessage` を、そうでなければ生成モジュールの文言を使う。
文言のないラベル（構文木の変種の `topitem` など）は、いまと同じくラベルの名前を文言とする。
`Peg.hpeg` の冒頭の「誤りの文言は Peg.Grammar.Parser の対応表で作る」のコメントを直す。
記法のパーサーに `%expect` は付けない。

### 版と互換

`Expected` に構築子を足し、`ParseError` と `SyntaxError` に欄を足すのは、`Peg.Runtime` の公開の API の互換を崩す変更である。
`Expected` を網羅して照合するコードと、構築子を位置で使うコードが壊れる。
`Peg.Grammar` の `Grammar` の欄の追加も、peg-grammar の互換を崩す。
`Peg.Runtime.Internal` の `Res` の変更は、[ADR 0046](0046-docs-cli-and-ci-before-v0-1-0.md) によって PVP のメジャーの変更である。

版の扱いは、実装の時点で v0.1.0（rc でない版）を出したかで分ける。

- v0.1.0 を出す前なら、版は 0.1.0.0 のまま変えず、生成モジュールの peg-runtime の範囲（`peg-runtime >=0.1 && <0.2`）も変えない。rc は Hackage に上げておらず（[ADR 0058](0058-no-hackage-candidates-for-pre-releases.md)）、PVP の版として公開していないためである
- v0.1.0 を出した後なら、六つのパッケージの版を 0.2.0.0 に上げ（[ADR 0044](0044-release-v0-1-0.md)）、生成器の範囲の定数（`runtimeVersions`）を `peg-runtime >=0.2 && <0.3` にし、生成物を作り直す

どちらの場合も、`%expect` と `%message` を使わない生成モジュールは、新しい peg-runtime で、生成し直さずにコンパイルできる。
`expecting` と `labeledMessage` は追加であり、既存の生成コードが使う関数の型は変えないためである。
各パッケージの `CHANGELOG.md` に変更を書く。

### 文書

- docs/syntax.md と docs/syntax.en.md：ディレクティブの表に二つの行を加える。「解析の失敗」の節に表示名と文言の説明と例（上の `Calc` の文法と表）を加える。ラベルの節の「送出したラベルは `parseErrorLabel` に入る」に文言を加える。採択のときに、冒頭の「反映している ADR」の一覧に本 ADR を加える（[ADR 0084](0084-english-version-of-the-syntax-guide.md)）
- docs/specifications.md：エラー報告の節に表示名と文言を加え、`renderParseError` の形の説明を直す。構文エラーからの回復の節に文言を加える
- README（日本語と英語）：生成したモジュールを使う節の `renderParseError` の説明に文言と `renderSyntaxError` を加え、WebAssembly の節の表を直す
- `Peg.Runtime` と `Peg.Runtime.Internal` の Haddock（英語）：`Expected`、`ParseError`、`SyntaxError`、`renderParseError`、`renderSyntaxError` を直す

### ADR のステータス

採択のとき、次の ADR のステータスの行を変える。

- [ADR 0005](0005-error-reporting.md)：「採択→ラベルの意味論は [ADR 0021](0021-error-recovery.md)、規則の表示名は ADR 0089」
- [ADR 0021](0021-error-recovery.md)：「採択→ラベルの文言（実装すること、実装しないこと）は ADR 0089」

## 実装しないこと

- 規則の定義の行に表示名を書く記法（`Expr "expression" <- ...`）。理由は「検討した記法」の節に書く
- 雛形への表示名。雛形を展開した規則の名前は生成器が作るので、ほかの規則名を取るディレクティブと同じく、雛形の名前を `%expect` に書けない
- 文言の多言語化と、文言への値の埋め込み（`missing ')' for '(' at 1:1` のように、位置や入力の文字を文言に入れること）。記法のパーサーの `escape` のような文字で変わる文言は、これまでどおり利用者の Haskell のコードで作る
- 規則の期待をまったく表示しない仕組み（megaparsec の `hidden` に当たるもの）。空白の規則の終端が一覧に出る問題はあるが、本 ADR の二つの問題と別に検討する
- 回復しないモードの `ParseError` の位置を、ラベルを送出した位置に変えること。いまは最遠の失敗の位置であり、本 ADR は位置を変えない
- 言語サーバーのホバーに表示名を出すこと、`%message` を加えるコードアクション。表示名と文言はディレクティブの一行に書いてあり、参照の検索でたどれる
- 記法のパーサーへの `%expect`。記法の誤りの文言はラベルで足りている
- 期待の一覧の中の終端を、表示名と同じ形で言い換えること（`'('` を `opening parenthesis` と表示するなど）

## テスト設計

先に書き、失敗させてから実装する。
peg-runtime と生成器のテストは、`expecting`、`labeledMessage`、新しい欄、`%expect`、`%message` が無いので、いまはコンパイルか検査で失敗する。

### peg-runtime（`packages/peg-runtime/test/Main.hs`）

- **始まりでの置き換え**：`expecting "number" (cls [('0','9')] "[0-9]")` に `x` を与えると、`renderParseError` が `1:1: expected number` を返すこと
- **内側の失敗は残す**：`expecting "sum" (lit "1" "'1'" >> lit "+" "'+'")` に `1*` を与えると、`1:2: expected '+'` のままであること
- **成功した規則**：始まりの位置で失敗を記録して成功した規則の、その位置の記録が表示名になること
- **入れ子**：表示名を持つ規則の中で、表示名を持つ規則を同じ位置で呼んだとき、外側の表示名が残ること
- **ほかの選択肢との合併**：`choice [lit "return" "'return'", expecting "expression" e]` で、`expected expression or 'return'` の順に並ぶこと
- **メモ化との整合**：メモ化を無効にした評価器と、表示名を含む失敗の報告が一致すること。`nomemo`、`memoArg`、`memoLR` の規則のそれぞれで確かめる
- **位置と受理の不変**：表示名の有無で、成功と失敗、`parseErrorPos` が変わらないこと（無作為な入力によるプロパティテスト）
- **回復**：回復した `SyntaxError` の `syntaxErrorExpected` に `ExpectedName` が入ること
- **文言**：`labeledMessage` で送出したとき、`parseErrorLabel` と `parseErrorMessage` の両方が入り、`renderParseError` が `行:桁: 文言` を返すこと。文言のない `labeled` では、表示がいまと同じであること
- **メモ表からの送出**：文言のあるラベルを持つメモ化した規則を同じ位置で二度評価し、二度めの送出も文言を持つこと
- **`renderSyntaxError`**：文言のある誤り、文言のない誤り、期待の一覧が空の誤りの表示

### peg-grammar

- **ディレクティブの受理**：`%expect` と `%message` の値が `Grammar` に入ること。エスケープの復号、文字列の中の `#`、閉じた `"` の後のコメント
- **静的検査**：「記法」の節の誤りのそれぞれの文言と位置
- **整形**：`%message l "a  # b"   # c` を `peg-hs fmt` が `%message l "a  # b" # c` にし、文字列の中を変えないこと。いまは最初の `#` で分けるので失敗する
- **ハイライト**：二つのディレクティブの規則名、ラベル、文字列の範囲と種類
- **ラベルを外した文法**：`stripLabels` が `%message` を除き、`%expect` を残すこと
- **記法のパーサーの文言**：記法の誤りの文言の既存のテストが、`%message` への移行の前後で変わらずに通ること。文字で変わる三つのラベルの文言も含む

### 生成器と適合性テスト

- **生成コードのゴールデン**：`%expect` と `%message` を使う fixture（`packages/peg-codegen/test/fixtures/Expect.hpeg` と、その `%syntax` の版）を加え、生成コードのゴールデンと、生成したモジュールの動作を確かめる。動作は、本 ADR の二つの表の入力と表示である
- **既存の生成物の不変**：`scripts/regen-fixtures.sh` で既存の fixture を生成し直しても、差分が出ないこと（版を上げた場合は、先頭のコメントの範囲の行を除く）
- **生成モジュールに入る値**：引用符、バックスラッシュ、`\u{...}` を含む表示名と文言から生成したモジュールがコンパイルでき、文字列が書いたとおりに復号されること
- **適合性**：JSON の文法の値の規則に `%expect` を付けた版が、JSONTestSuite の全件で付けない版と同じに受理と拒否をし、拒否した入力の `parseErrorPos` が一致すること

### エディタと wasm

- **エディタの文法**：`editors/test` の例に二つのディレクティブ（文字列の中に `#` を含むもの）を加え、TextMate と tree-sitter のハイライトが記法の構文木と一致すること（`consistency.test.js`）。tree-sitter のコーパスとハイライトのテストを加える
- **wasm**：`analyze` の応答の `Directive` のノードが、`%expect` と `%message` に二つの `Value` を持つこと

### 手で確かめること

実装の後に、`Calc` の文法に `%expect Expr "expression"` と `%message close "missing ')'"` を加え、`peg-hs parse` で本 ADR の表の入力を与え、表のとおりに表示されることを確かめる。
VS Code の拡張機能で、二つのディレクティブの色付けを目で確かめる。

## トレードオフ

- 表示名は、規則の始まりで失敗したときにしか働かない。規則がいくらか読んでから失敗した誤りは、これまでどおり終端の列挙になる。内側の規則にも表示名を付ければ、その規則の始まりで失敗した誤りは表示名になる
- 規則の始まりの位置の失敗を一律に置き換えるので、その規則の中の、始まりの位置での具体的な終端の情報は消える。たとえば `Expr` の始まりで `'-'` だけが期待されていたとしても、表示は `expression` になる。具体的な終端を見たい作者は、表示名を付けない
- 表示名を持つ規則の評価ごとに、失敗の記録の参照を二度書きかえる。メモ表にヒットした評価では起きない。表示名を持たない規則の生成コードは変わらないので、表示名を使わない文法の速さは変わらない
- 文言は文法の中に一つの言語で書く。多言語の文言が要る利用者は、文言を使わずにラベルの名前から自分の表を引く
- 公開の型の互換が崩れる。v0.1.0 の前に入れれば、版を上げずに済む

## 検討した記法

### 規則の定義の行に表示名を書く

Peggy（PEG.js の後継）は、規則名と `=` の間に文字列を書いて表示名とする（`integer "simple number" = ...`）。
peg-hs で同じ形にすると `Expr "expression" <- ...` になり、表示名が規則の定義の隣に来る。

この形を採らず、ディレクティブにする。
理由は二つある。

一つめに、規則の頭の文法が変わる。
記法のパーサーは、選択肢の要素を読むたびに、次の規則の宣言が始まっていないかを先読み（`DeclStart`）で確かめる。
`Expr "expression" <-` を宣言の始まりとして認めるには、この先読みと `Declaration` の規則を変え、記法のパーサーを生成し直し、tree-sitter と TextMate の定義の型、ハイライトの宣言の処理、整形、言語サーバーの宣言の範囲を、すべて変えることになる。
ディレクティブなら、変わるのは引数の読み方だけで、どの道具もディレクティブごとの分岐をすでに持っている。

二つめに、受理する言語を変えない規則の属性は、すでにディレクティブで書いている。
`%nomemo`、`%token`、`%trivia`、`%inline`、`%entry` がそうである。
表示名も、受理する言語を変えず、誤りの表示だけを変える属性なので、同じ置き場所にする。

代わりに、表示名が規則の定義から離れた場所に書ける。
言語サーバーの参照の検索で、規則から `%expect` の行をたどれる。

### ディレクティブの名前

`%name` は `%module` の名前や規則名と紛らわしい。
`%expect` は、表示が「expected 表示名」になることと対応し、「この規則を期待するところでは、この名前で表示する」と読める。
文字列を `expected` の後に置くので、表示名は名詞句（`expression`、`an identifier`）で書く。

## 参考文献

- megaparsec 9.8.3 の `Text.Megaparsec` の Haddock（`label` と `hidden`）。https://hackage.haskell.org/package/megaparsec-9.8.3/docs/Text-Megaparsec.html
- Peggy の文書（規則の human-readable name）。https://peggyjs.org/documentation.html
- Leijen, D., Meijer, E. 2001. Parsec: Direct Style Monadic Parser Combinators for the Real World. Technical Report UU-CS-2001-27. https://www.microsoft.com/en-us/research/publication/parsec-direct-style-monadic-parser-combinators-for-the-real-world/
