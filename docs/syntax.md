# .hpeg 記法

[English version](syntax.en.md)

peg-hs の文法定義ファイル（`.hpeg`）の書き方を、例を中心に解説する。
記法の各要素について、何をするものか、どう書くか、書き誤ったときに peg-hs が何を報告するかを順に述べる。
規範は各 ADR にあり、この文書はそれを利用者の側から読める形にまとめたものである。
記述が ADR と食い違う場合は ADR が優先する。

この文書は、採択済みの ADR の内容だけを反映する。
反映している ADR は [ADR 0001](adr/0001-bounded-left-recursion.md)、[ADR 0003](adr/0003-typed-semantic-actions.md)、[ADR 0004](adr/0004-peg-notation.md)、[ADR 0005](adr/0005-error-reporting.md)、[ADR 0006](adr/0006-memoization-control.md)、[ADR 0008](adr/0008-source-positions.md)、[ADR 0012](adr/0012-context-sensitive-extensions.md)、[ADR 0014](adr/0014-generated-module-api.md)、[ADR 0015](adr/0015-implementation-deviations.md)、[ADR 0016](adr/0016-language-extensions.md)、[ADR 0017](adr/0017-nomemo-implementation.md)、[ADR 0018](adr/0018-tab-partial-consumption.md)、[ADR 0019](adr/0019-lossless-syntax-tree.md)、[ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)、[ADR 0021](adr/0021-error-recovery.md)、[ADR 0026](adr/0026-discard-unused-values.md)、[ADR 0027](adr/0027-switch-to-self-hosted-parser.md)、[ADR 0028](adr/0028-label-safety-check.md)、[ADR 0029](adr/0029-label-safety-implementation-deviations.md)、[ADR 0030](adr/0030-unit-values-are-not-counted.md)、[ADR 0031](adr/0031-rule-templates.md)、[ADR 0033](adr/0033-grammar-linter.md)、[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)、[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)、[ADR 0050](adr/0050-hpeg-extension.md)、[ADR 0053](adr/0053-type-names-of-rules-without-case.md)、[ADR 0054](adr/0054-automatic-label-insertion.md)、[ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)、[ADR 0056](adr/0056-label-insertion-and-template-deviations.md)、[ADR 0061](adr/0061-select-generated-exports.md)、[ADR 0062](adr/0062-warnings-of-pruned-generated-modules.md)、[ADR 0063](adr/0063-omit-unit-actions.md)、[ADR 0064](adr/0064-unit-rules-always-return-unit.md)、[ADR 0065](adr/0065-omittable-identity-actions.md)、[ADR 0066](adr/0066-omit-unit-type-annotations.md)、[ADR 0067](adr/0067-lint-info-with-verbose.md)、[ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)、[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)、[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)、[ADR 0082](adr/0082-static-check-of-binding-references.md)、[ADR 0083](adr/0083-bindings-inside-a-group-are-not-visible.md) である。

この文書のコードブロックのうち、`%module` で始まるものは完全な文法であり、そのまま `peg-hs gen` で生成できる。
それ以外は文法の一部を抜き出した断片である。

## 最小の例

加算だけを持つ式の文法から始める。

```hpeg
%module Example.Sum

%{
import Data.Text (unpack)
}%

# 左結合の加算
Sum :: Int
Sum <- l:Sum '+' r:Num { l + r }
     / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

`peg-hs gen Sum.hpeg` は、この文法から Haskell のモジュール `Example.Sum` を生成する。
モジュールは入口 `parse :: Text -> Either ParseError Int` を公開し、`parse "1+2+3"` は `Right 6` を返す。
`Sum` は自分自身を左端で呼ぶ左再帰の規則であり、`1+2+3` は `(1+2)+3` の順に組み立てられる。

この短い文法に、記法の要素の大半が現れている。
`%module` はディレクティブ、`%{ ... }%` は Haskell のコードの丸写し、`Sum :: Int` は規則の型注釈、`Sum <- ...` は規則の定義である。
`l:Sum` は値に名前を付ける束縛、`$[0-9]+` は読んだ文字列を取るテキストキャプチャ、`{ l + r }` は選択肢の値を作るアクションである。
以下の節で、それぞれを説明する。

## 誤りと警告の読み方

peg-hs は、文法の誤りを次の形で標準エラー出力に書く。

```
Sum.hpeg:3:6: error: undefined rule Num
```

ファイル名、行、桁に続けて、誤りの文言が来る。
誤りが一つでもあれば、`peg-hs gen` は何も生成せずに終了状態 1 で終わる。

誤りのほかに、生成はできるが意図と違うかもしれない書き方への警告がある。
警告には二つの出どころがある。

- **ラベルの安全性の警告**：`peg-hs gen` が出す。生成は続ける。`--Werror` を付けると、警告があれば失敗する（[ラベルの安全性の検査](#ラベルの安全性の検査)）
- **lint の警告**：`peg-hs lint` が出す。警告が一つでもあれば終了状態 1 で終わる（[lint](#lint)）

`peg-hs lint` は、警告とは別に info も出す。
info は、直せば文法が簡潔になるが、直さなくても誤りではない書き方を知らせる。
`--verbose` を付けたときだけ、`warning:` の代わりに `info:` と書いて表示し、終了状態は変えない。

以下の各節の「よくある誤り」の表は、書き方と、そのとき peg-hs が出す文言の組である。
文言はファイル名と位置を除いて示す。

## ファイルの構造

ファイルは、ディレクティブ、verbatim ブロック、規則の並びである。
並びの順は自由だが、ディレクティブと verbatim ブロックを先頭にまとめ、規則を後ろに並べるのが読みやすい。

### コメント

`#` から行末までがコメントになる。
リテラル、文字クラス、アクションの内側の `#` はコメントにならない。

```hpeg
%module Example.Hash

# この行はコメント
Hash <- '#' # リテラルの '#' はコメントではない
```

ディレクティブの引数の後ろにもコメントを書ける。
ただし `%env` の引数は行末までがそのまま型になるので、`%env` の行にはコメントを書かない。

### ディレクティブ

ディレクティブは `%` で始まる一行で、文法全体に関わる指定をする。

| ディレクティブ | 意味 | ADR |
|---|---|---|
| `%module A.B.C` | 生成するモジュールの名前。必須 | [ADR 0004](adr/0004-peg-notation.md) |
| `%start Name` | 開始規則。省略すると、最初に定義した規則が開始規則になる | [ADR 0004](adr/0004-peg-notation.md) |
| `%entry Name` | 開始規則以外の規則にも入口を生成する | [ADR 0014](adr/0014-generated-module-api.md) |
| `%export 項目, ...` | verbatim ブロックで定義した名前を生成モジュールから公開する | [ADR 0014](adr/0014-generated-module-api.md) |
| `%language 拡張, ...` | 生成モジュールで言語拡張を有効にする | [ADR 0016](adr/0016-language-extensions.md) |
| `%env 型` | 解析全体で不変な環境の型を宣言する | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `%tabstop N` | `_col` の計算で、タブを N の倍数の桁まで進める | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `%nomemo Name` | 規則のメモ化を外す | [ADR 0017](adr/0017-nomemo-implementation.md) |
| `%syntax` | ロスレスな構文木を返す入口も生成する | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%token Name` | 構文木で、規則の一致を一つのトークンにする | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%trivia Name` | `%token` の規則を、空白やコメントのようなトリビアとして扱う | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%inline Name` | 構文木で、規則の呼び出しをノードにせず、子を呼び出し元に並べる | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%recover label Name` | ラベル `label` の回復の規則を `Name` とする | [ADR 0021](adr/0021-error-recovery.md) |
| `%safe label` | ラベル `label` の安全性の警告を止める | [ADR 0028](adr/0028-label-safety-check.md) |
| `%deriving クラス, ...` | 生成する型が導出するクラス。引数なしなら何も導出しない | [ADR 0075](adr/0075-generated-types-for-rules-without-actions.md) |

`%module`、`%start`、`%env`、`%tabstop`、`%syntax`、`%deriving` は一度しか書けない。
`%entry`、`%export`、`%language`、`%nomemo`、`%token`、`%trivia`、`%inline`、`%recover`、`%safe` は何度でも書ける。
一行に一つの規則を書くディレクティブ（`%entry`、`%nomemo` など）は、規則ごとに一行を書く。

`%module` の値と `%export` の項目は、生成モジュールにそのまま書き出される。
そのため peg-hs は、Haskell の宣言として読める値を拒む（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）。
`%module` の値は、ドットで区切ったモジュール名である。
各部分は大文字で始まり、その後は文字、数字、`_`、`'` だけからなる。
`%export` の項目は、次の形のどれかである。
項目の間と括弧の内側には空白を置ける。

- 修飾してもよい変数名か型の名前（`evalExpr`、`Expr`、`M.f`）
- 型の名前に `(..)` か、名前と括弧で囲んだ演算子をカンマで区切った `( ... )` を続けたもの（`Expr(..)`、`Expr(Add, Mul)`）
- 括弧で囲んだ演算子（`(+++)`）
- これらの前に `type` か `pattern` を付けたもの（`type (:+)`、`pattern P`）
- `module` とモジュール名（`module Data.Text`）

各ディレクティブの使い方は、関係する節で説明する。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `%module` を書き忘れた | `error: missing %module directive` |
| 綴りを誤った（`%modul`） | `error: unknown directive %modul` |
| `%start` を二度書いた | `error: duplicate %start directive` |
| 引数を書き忘れた（`%start`） | `error: %start needs an argument` |
| 規則名でないものを書いた（`%entry A B`） | `error: %entry expects a rule name` |
| 定義していない規則を書いた | `error: undefined rule Name` |
| `%tabstop 0` | `error: %tabstop expects a positive integer` |
| モジュール名でないものを書いた（`%module m`、`%module M where x = 1`） | `error: %module expects a module name, but got m` |
| エクスポートの項目でないものを書いた（`%export f) where`、`%export f -- x`） | `error: %export expects export items, but got f) where` |

### verbatim ブロック

`%{` と `}%` で囲んだ部分は、生成モジュールに Haskell のコードとして丸写しされる。
import、構文木の型、アクションから呼ぶ補助関数をここに書く。
複数のブロックを書いた場合は、出現順に連結される。

```hpeg
%module Example.Digit

%{
import qualified Data.Text as T

digitValue :: Char -> Int
digitValue c = fromEnum c - fromEnum '0'
}%

Digit :: Int
Digit <- d:$[0-9] { digitValue (T.head d) }
```

生成モジュールは Prelude を `PegPrelude` として qualified に import する。
verbatim ブロックが Prelude を import していなければ、生成器は通常の `import Prelude` も補うので、アクションからは普段どおり Prelude の名前を使える（[ADR 0015](adr/0015-implementation-deviations.md)）。
verbatim ブロックで `import Prelude ()` のように Prelude を隠しても、生成コードは影響を受けない。

生成器が内部で使う名前と衝突しないよう、verbatim ブロックでは次の名前を使えない（[ADR 0014](adr/0014-generated-module-api.md)）。

- `peg'` と `Peg'` で始まる名前の定義
- `PegRt` と `PegPrelude` という import の別名

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `}%` で閉じ忘れた | `error: unterminated %{ block` |
| `peg'helper = ...` を定義した | `error: the name peg'helper is reserved for generated code` |
| `import qualified Foo as PegRt` | `error: the module alias PegRt is reserved for generated code` |

### 言語拡張

verbatim ブロックはモジュールの先頭より後ろに置かれる。
そのため、verbatim ブロックに `{-# LANGUAGE OverloadedStrings #-}` を書いても効かない。
言語拡張は `%language` ディレクティブで有効にする（[ADR 0016](adr/0016-language-extensions.md)）。

```hpeg
%module Example.Words
%language OverloadedStrings

%{
import Data.Text (Text)
}%

Sign :: Text
Sign <- '+' { "plus" }
      / '-' { "minus" }
```

`OverloadedStrings` を有効にしたので、アクションの文字列リテラル `"plus"` が `Text` になる。
複数の拡張は `%language OverloadedStrings, LambdaCase` のようにカンマで区切るか、`%language` を複数行に分けて書く。
生成器は、書いた順のままプラグマを生成モジュールの先頭に置く。

言語拡張は利用者のコードだけでなく生成コードにも効く。
生成コードが次の拡張の下で意味を変えないことは、テストで確かめている。
`OverloadedStrings`、`OverloadedLists`、`LambdaCase`、`Strict`、`StrictData`、`NoImplicitPrelude` である。
これ以外の拡張の組み合わせは保証の外にある。

`NoImplicitPrelude` を指定した文法では、生成器は `import Prelude` を補わない。
利用者が暗黙の Prelude を断ったので、Prelude の名前は verbatim ブロックで自分で import する。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `%language RebindableSyntax` | `error: %language RebindableSyntax is not allowed: it changes the meaning of the generated code` |
| 拡張名の字句でないもの（`%language overloaded`） | `error: %language expects extension names, but got overloaded` |
| 存在しない拡張名（`%language OverloadedStringz`） | peg-hs は報告しない。生成モジュールのコンパイルで GHC が報告する |

`RebindableSyntax` は、生成コードの `do` 記法と数値リテラルを利用者の定義で解釈させるので、拒否している。

## 規則

規則は、型注釈と定義の組で書く。

```hpeg
# 断片
Name :: 型
Name <- 選択肢 / 選択肢 / ...
```

型注釈の `::` の右側は、行末までを Haskell の型として扱う。
`[Int]` や `Maybe (Text, Int)` のような型もそのまま書ける。
型の正しさを確かめるのは GHC であり、peg-hs は型を文字列として生成モジュールに写す。

型注釈は省ける。
値を持たない規則の型は、型注釈がなければ `()` である（[ADR 0066](adr/0066-omit-unit-type-annotations.md)）。
空白、区切り、キーワードを読む規則の多くは値を持たないので、定義の一行だけで書ける。

```hpeg
# 断片
Sp <- ' '*    # Sp :: () と書いたのと同じ
```

型注釈もアクションもない規則が値を持つときは、peg-hs が型を推論するか、型を生成する（[型の推論と生成](#型の推論と生成)）。
アクションを書いた規則の型は、型注釈がなければ、選択肢の値によらず `()` である。
値を返すつもりの規則で、アクションを書いて型注釈を書き忘れると、アクションの値が `()` と合わない。
この食い違いは、生成モジュールのコンパイルで、GHC がアクションの位置を指す型の誤りとして報告する。

引数を持つ規則（[引数付き規則](#引数付き規則)）と雛形（[規則の雛形](#規則の雛形)）は、型注釈を省けない。
引数を宣言できるのが型注釈だけだからである。

定義の右辺の選択肢は複数行にわたって書ける。
次の規則の型注釈か定義が始まると、前の規則の定義が終わる。

### 規則名

規則名と束縛名には Unicode の文字を使える（[ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)）。
先頭は英字か `_`、二文字目以降は英数字、`_`、`'` である。
英字の判定は Haskell の `Data.Char.isAlpha` に従うので、漢字や仮名も英字として扱われる。

```hpeg
%module Example.Japanese
%start 数式

%{
import Data.Text (unpack)
}%

数式 :: Int
数式 <- 左:数式 '＋' 右:数 { 左 + 右 }
      / 数

数 :: Int
数 <- ds:$[0-9]+ { read (unpack ds) }
```

`%syntax` の文法では、規則名から Haskell の型名を作る。
漢字のように大文字のない文字で始まる規則名は、型名の前に `Rule'` が付く（[ロスレスな構文木](#ロスレスな構文木)、[ADR 0053](adr/0053-type-names-of-rules-without-case.md)）。

### 開始規則と到達しない規則

開始規則は、`%start` で指定した規則か、ファイルで最初に定義した規則である。
どの規則も、開始規則、`%entry` の規則、`%recover` の回復の規則のどれかから呼び出しをたどって到達できなければならない。
使っていない規則を残すと、誤りになる。

規則の定義と型注釈についての、よくある誤り：

| 書き方 | 報告 |
|---|---|
| 雛形の型注釈を書き忘れた（`T<p> <- p` だけを書いた） | `error: rule T has parameters, so it needs a type annotation` |
| 型注釈だけで定義がない | `error: rule A has a type annotation but no definition` |
| 型注釈の `::` の後に型がない | `error: expected a type` |
| 同じ規則を二度定義した | `error: duplicate definition of A` |
| 同じ規則に型注釈を二度書いた | `error: duplicate type annotation for A` |
| 定義していない規則を呼んだ | `error: undefined rule B` |
| どこからも呼ばれない規則を残した | `error: rule B is unreachable from the start, entry and recovery rules` |
| 規則を一つも書いていない | `error: the grammar has no rules` |
| 規則名の後に `::` も `<-` もない | `error: expected :: or <-` |

## 式

規則の定義の右辺は、終端と演算子を組み合わせた式である。

### 終端

終端は、入力の文字に直接一致する式である。

- **リテラル**：`'abc'` と `"abc"` のどちらでも書ける。書いた文字列に一致する
- **文字クラス**：`[a-z0-9_]` の形。括弧の中の文字か範囲のどれか一文字に一致する
- **任意の一文字**：`.` は Unicode のコードポイント一つに一致する

リテラルと文字クラスでは、次のエスケープを使える。

```
\n \t \r \\ \' \" \] \[ \- \u{XXXX}
```

`\u{XXXX}` は、16 進で書いたコードポイントの文字である（`\u{3042}` は `あ`）。
リテラルと文字クラスの中に改行をそのまま書くことはできないので、`\n` と書く。

文字クラスに否定の形 `[^...]` はない。
「`a` から `z` 以外の一文字」は、否定先読みと `.` を組み合わせて `![a-z] .` と書く。

```hpeg
%module Example.Quoted

%{
import Data.Text (Text)
}%

# ' で囲まれた、改行を含まない文字列
Quoted :: Text
Quoted <- '\'' $(!['\n] .)* '\''
```

よくある誤り：

| 書き方 | 報告 |
|---|---|
| リテラルを閉じ忘れた（`'abc`） | `error: unterminated literal` |
| 知らないエスケープ（`'\q'`） | `error: unknown escape \q` |
| `\u` の後に `{` がない、閉じの `}` がない | `error: expected '{'`、`error: expected '}'` |
| 範囲外のコードポイント（`\u{110000}`） | `error: invalid \u escape` |
| 空の文字クラス（`[]`） | `error: empty character class` |
| 文字クラスを閉じ忘れた（`[a-z`） | `error: unterminated character class` |
| 逆向きの範囲（`[z-a]`） | `error: the range is empty` |
| 否定のつもりの `[^a-z]` | 報告されない。`^` と `a` から `z` のどれか一文字に一致する文字クラスになる |

最後の `[^a-z]` は、誤りにならないまま意図と違う文法になる。
文字クラスの先頭の `^` は普通の文字として読まれるので、否定には `![a-z] .` を使う。

### 演算子

演算子は、結合の強い順に次のとおりである。

| 種類 | 記法 | 意味 |
|---|---|---|
| 接尾辞 | `e*` `e+` `e?` | 0 回以上、1 回以上、省略可能 |
| 失敗ラベル | `e ^label` | `e` が失敗したらラベルを送出する（[構文エラーからの回復](#構文エラーからの回復)） |
| 接頭辞 | `&e` `!e` `$e` | 肯定先読み、否定先読み、テキストキャプチャ |
| 逐次 | `e1 e2` | 左から順に照合する |
| 選択 | `e1 / e2` | 左の選択肢から順に試し、最初に成功したものを採る |

接尾辞は接頭辞より強く結合するので、`$[0-9]+` は `$([0-9]+)` と読む。
括弧 `( ... )` で囲むと、結合を変えられる。

式の入れ子は 256 段までである（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）。
群の括弧、接頭辞と接尾辞の演算子、失敗ラベル、雛形の呼び出しの引数が、それぞれ一段ずつ数える。
`!('a'*)` は、`!`、括弧、`*` の三段である。
並べた式の段は足さない。
`('a') ('b')` は一段である。
上限を超えた式は、超えた段の位置で誤りになる。
上限は変えられない。

先読み `&e` と `!e` は、`e` が一致するか（しないか）だけを確かめ、入力を消費しない。
`!.` は入力の終わりでだけ成功する。

選択 `/` は順序付きである。
前の選択肢が成功すると、後ろの選択肢は試されない。
`'=' / '=='` の `'=='` は、`=` で始まる入力では必ず前の `'='` が先に成功するので、決して成功しない。
長いほうを前に置く。

繰り返し `*` と `+` は、一致できる限り読み進め、後戻りしない。
`[a-z]* 'x'` は `abcx` に一致しない。
`[a-z]*` が `x` まで読んでしまい、`'x'` の分が残らないためである。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 空文字列に一致しうる式の繰り返し（`('a'?)*`） | `error: the repeated expression can match the empty string, which would loop forever` |
| グループの括弧を閉じ忘れた（`('a' / 'b'` で行が終わる） | `error: expected ')'` |
| 演算子や束縛の後に式がない（`'a' ! / 'b'`、`x:`） | `error: expected an expression` |
| 式の入れ子が 256 段を超えた（括弧を 257 重に書いた） | `error: the expression nests deeper than 256` |
| 前の選択肢が必ず成功する（`'a'? / 'b'`） | lint：`warning: the alternative is never tried: the alternative at 3:6 always succeeds [unreachable-alternative]` |
| 前の選択肢が接頭辞に一致する（`'=' / '=='`） | lint：`warning: the alternative never succeeds: the alternative at 3:7 matches its prefix '=' first [unreachable-alternative]` |
| 同じ選択肢を二度書いた | lint：`warning: the alternative never succeeds: it is the same as the alternative at 3:7 [duplicate-alternative]` |

lint の警告の位置（`3:6` など）は、後ろの選択肢を成功させない前の選択肢の位置を指す。

## 値と束縛

### 値を持つ式

アクションから参照できるのは、値を持つ式だけである。

| 式 | 値の型 |
|---|---|
| 規則の呼び出し `Name`、`Name(引数)`、雛形の呼び出し `Name<引数>` | その規則の型 |
| テキストキャプチャ `$e` | 消費した入力の `Text` |
| `e*` `e+` | `e` の値の型のリスト |
| `e?` | `e` の値の型の `Maybe` |
| `e ^label` | `e` の値の型 |

リテラル、文字クラス、`.`、先読み、意味述語は値を持たない。
リテラルや文字クラスに一致した文字が欲しいときは、`$` で取る。

```hpeg
# 断片
Ident :: Text
Ident <- s:$([a-z] [a-z0-9]*) { s }
```

括弧で囲んだグループは、内側の各選択肢が値をちょうど一つ持つときにその値を持ち、それ以外は値を持たない。

### `()` の値は数えない

空白を読む規則のように、型注釈が `()` の規則は、値として情報を持たない。
値を数えるとき、束縛しない `()` の値は数えない（[ADR 0030](adr/0030-unit-values-are-not-counted.md)）。
型注釈が `()` の規則と、それに `*`、`+`、`?` を付けたものがこれにあたる。
値を持たないので型が `()` になる、型注釈のない規則も同じである。
そのため、空白の規則を挟んでもグループの値は一つのままである。

```hpeg
%module Example.List

%{
import Data.Text (Text)
}%

Names :: [Text]
Names <- n:Name ns:(',' Sp Name)* { n : ns }   # グループの値は Name の値

Name :: Text
Name <- $[a-z]+ Sp

Sp <- [ \t]*
```

この規則には三つの但し書きがある。

- `()` 以外の値を持つ要素が一つもない場合は、`()` の値も数える。型注釈が `()` でない規則で `Spaces <- Ws` と書くと、選択肢は `Ws` の値を返す。型注釈が `()` の規則では、この場合の値は常に `()` になる（[アクションの省略](#アクションの省略)）
- 束縛した要素（`u:Sp`）は、`()` でも常に数える
- 型注釈の判定は、空白を除いた文字列が `()` かどうかで行う。`type Unit = ()` のような別名は `()` とみなされない

### 値が使われない位置

値が使われない位置では、グループの選択肢の値の型が違ってもよい（[ADR 0026](adr/0026-discard-unused-values.md)）。
値が使われない位置は、テキストキャプチャ `$e` の中、先読み `&e` と `!e` の中、アクションを書いた選択肢の束縛しない要素である。

```hpeg
%module Example.Word

%{
import Data.Text (Text, unpack)
}%

# Num は Int、Name は Text だが、キャプチャの中なのでグループの値は使われない
Word :: Text
Word <- $(Num / Name)

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }

Name :: Text
Name <- $[a-z]+
```

逆に、グループの値が使われる位置（束縛した要素や、アクションを省略した選択肢の値になる要素）では、どの選択肢の値も同じ型でなければならない。
型が合わなければ、生成モジュールのコンパイルで GHC が `.hpeg` の位置を指して報告する。

### 束縛

`名前:式` の形で、式の値に名前を付ける。
名前はアクション、意味述語、規則の引数から Haskell の変数として参照するので、小文字で始める。

```hpeg
# 断片
Pair :: (Int, Int)
Pair <- '(' a:Num ',' b:Num ')' { (a, b) }
```

束縛には次の制約がある。

- 選択肢の逐次の直下に書く。括弧の内側の束縛は、外のアクションからは見えない
- 値を持たない式には付けられない
- 一つの選択肢の中で同じ名前を二度使えない
- アンダースコアで始まる名前は使えない。生成器の予約である

深い位置の値が欲しい場合は、規則を分けて束縛する。

コードから見える束縛は、位置で決まる（[ADR 0082](adr/0082-static-check-of-binding-references.md)、[ADR 0083](adr/0083-bindings-inside-a-group-are-not-visible.md)）。
アクションからは、その選択肢の逐次の直下の束縛がすべて見える。
意味述語と規則の引数からは、選択肢の逐次の直下の束縛のうち、その位置より左にあるものが見える。
括弧の内側に書いた意味述語と引数からは、括弧より左にあるものが見える。
括弧の内側の束縛は、生成コードが束縛しないので、どのコードからも見えない。
規則の引数と予約束縛は、どこからでも見える。
規則の中で束縛している名前を、見えない位置から参照すると、生成の前に誤りになる。
誤りの位置は、コードの中の名前の位置である。
規則の中で束縛していない名前（Prelude、import、verbatim ブロックの関数）は検査せず、生成モジュールのコンパイルで GHC が報告する。

コードの中の名前は字句の水準で読む。
文字列と文字のリテラル、行コメントとブロックコメント、修飾名（`M.x`）の中の名前と、レコードのフィールドの選択（`r.x`）のフィールドは、束縛の参照と見なさない。
バッククォートで囲んだ名前（`` `div` ``）は参照と見なす。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 値を持たない式に束縛した（`c:[a-z]`） | `error: cannot bind c: the expression has no value (capture the text with $)` |
| 同じ名前を二度使った（`x:A x:A`） | `error: the binding x is used twice in this alternative` |
| アンダースコアで始まる名前（`_x:A`） | `error: the binding _x is reserved: names starting with an underscore belong to the generator` |
| 意味述語が右にある束縛を参照した（`&{ y > 0 } y:N`） | `error: the predicate refers to y, which is bound to its right` |
| 規則の引数が右にある束縛か自分の束縛を参照した（`x:A(y) y:B`、`x:A(x)`） | `error: the argument refers to y, which is bound to its right` |
| 括弧の内側の束縛を参照した（`(y:N) { y }`、`(y:N &{ y > 0 })*`） | `error: y is bound inside a group, which the code cannot see` |
| ほかの選択肢の束縛を参照した（`x:N { x } / M { x }`） | `error: x is not bound in this alternative` |
| 束縛した名前をどこでも使っていない | lint：`warning: the binding x is not used [unused-binding]; remove x:` |

`c:[a-z]` は `c:$[a-z]` と書けば、一致した文字を `Text` として束縛できる。
使っていない束縛の警告は、`%syntax` の文法では出ない。
`%syntax` の文法では、束縛の名前が構文木の取り出し関数の名前にもなるためである。
文字列やコメントの中にだけ名前を書いた束縛は、使っていない束縛である。

### 予約束縛

生成器は、次の名前を自動で束縛する。

| 名前 | 値 | 使える場所 | ADR |
|---|---|---|---|
| `_span` | その選択肢が消費した入力の範囲（`Span`） | アクション | [ADR 0008](adr/0008-source-positions.md) |
| `_env` | `%env` で宣言した環境の値 | アクション、意味述語、規則の引数 | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `_col` | 評価している位置の桁（0 始まり） | 意味述語、規則の引数 | [ADR 0012](adr/0012-context-sensitive-extensions.md) |

## アクション

選択肢の末尾に `{ Haskell の式 }` を書くと、その式が選択肢の値になる。
式の型は、規則の型注釈と一致しなければならない。

```hpeg
# 断片
Signed :: Int
Signed <- '-' n:Num { negate n }
        / n:Num     { n }
```

アクションは純粋な式でなければならない。
左再帰の解析では、同じアクションが複数回評価されることがある。

peg-hs はアクションを、波括弧の釣り合いを数えて読む。
Haskell の文字列リテラルと文字リテラルの中の括弧は数えないので、`{ pack "}" }` は正しく読める。
ブロックコメント `{- -}` の中の括弧は数えてしまうので、アクションにはブロックコメントを書かない。

アクションに型の誤りがあると、GHC はそのエラーを生成されたファイルではなく `.hpeg` ファイルの行と桁で報告する（[ADR 0014](adr/0014-generated-module-api.md)）。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 括弧の釣り合わないアクション（`{ f ) }`） | `error: unbalanced bracket in Haskell code` |
| アクションを閉じ忘れた | `error: unterminated Haskell code` |
| 閉じていない文字列リテラル（`{ "abc }`） | `error: unterminated string literal` |
| グループの中にアクションを書いた（`('a' { 1 })`） | `error: actions are not allowed inside a group` |

グループの中ではアクションを書けない。
グループの値を作り変えたいときは、グループを規則に切り出す。

### アクションの省略

値を持つ要素がちょうど一つの選択肢は、アクションを省略できる。
その要素の値がそのまま選択肢の値になる。
上の `Signed` の二つめの選択肢は、次のように書いてもよい。

```hpeg
# 断片
Signed :: Int
Signed <- '-' n:Num { negate n }
        / Num
```

同じ理由で、束縛した値をそのまま返すアクションは、束縛ごと省ける。
`Paren <- '(' Sp e:Expr ')' Sp { e }` は、`()` の値を数えないので、値を持つ要素は `Expr` だけである。
束縛とアクションを消した `Paren <- '(' Sp Expr ')' Sp` も、`Expr` の値を返す。
`peg-hs lint --verbose` は、このように消せる束縛とアクションに `omittable-identity-action` の info を出す（[ADR 0065](adr/0065-omittable-identity-actions.md)、[lint](#lint)）。
ただし、束縛を消すと値が変わるか、束縛がほかの役目を持つ場合には出さない。

- アクションのコードが、空白を除いて束縛の名前だけでない（`{ negate n }`、`{ (n) }`）
- 名前を同じ選択肢の意味述語や規則の引数でも使っている（`n:Num &{ n > 0 } { n }`）
- ほかにも束縛した要素がある。または、束縛を消すと、値を持つ要素として数えるものが二つ以上になる
- 文法が `%syntax` を持つ。束縛は構文木の取り出し関数の名前にもなるので、消すと生成モジュールの関数が減る

値を持つ要素が 0 個、または 2 個以上の選択肢でアクションを省略すると、誤りになる。
数え方は、[`()` の値は数えない](#-の値は数えない)で述べたとおりである。

ただし、型注釈が `()` の規則には例外がある（[ADR 0063](adr/0063-omit-unit-actions.md)、[ADR 0064](adr/0064-unit-rules-always-return-unit.md)）。
型が `()` の、型注釈のない規則も同じに扱う。
`()` 以外の値を持つ要素が一つもない選択肢は、アクションを省略でき、値は `()` になる。
型が `()` の規則の値は `()` しかないので、`{ () }` を書いても情報は増えないからである。

```hpeg
# 断片
Sp :: ()
Sp <- ' '*                # 値を持つ要素が 0 個

Kw :: ()
Kw <- 'if' ![a-z] Sp      # () の要素が一つ

Gap :: ()
Gap <- Sp ',' Sp          # () の要素が二つ

Spaces :: ()
Spaces <- Sp+             # 要素の値は [()] だが、選択肢の値は ()
```

`()` の要素がいくつあってもよく、束縛した要素（`u:Sp`）を含んでもよい。
数える要素が `Sp+` や `Sp?` のように `[()]` や `Maybe ()` の値を持つ一つだけでも、選択肢の値は `()` である。
型注釈の判定は、[`()` の値は数えない](#-の値は数えない)と同じく、空白を除いた文字列で行う。
雛形の展開した規則では、型の変数を置き換えた後の型注釈で判定する。

この例外には三つの限りがある。

- 要素のない選択肢（`S <- 'a' / { () }` の後ろの選択肢）は、アクションを省略できない。空の選択肢には `{ () }` を書く
- `()` 以外の値を持つ要素がちょうど一つの選択肢は、これまでどおりその値を返す。型が `()` と合わなければ、GHC が型の誤りを報告する。ただし、型注釈もアクションもない規則（[型の推論と生成](#型の推論と生成)）と、`%syntax` の文法の型注釈のない規則（[型を書かない文法](#型を書かない文法)）は別に扱う
- 型注釈が `()` でない規則は、例外の対象にならない。`type Unit = ()` のような別名も `()` とみなさない

省略できる `{ () }` を書いても誤りではない。
`peg-hs lint --verbose` は、それに `omittable-unit-action` の info を出す（[lint](#lint)）。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `Flag <- 'on'`（型注釈が `Bool` の規則で、値を持つ要素が 0 個） | `error: an alternative without an action must have exactly one element with a value, but it has none` |
| `Pair <- Num Num`（型注釈が `(Int, Int)` の規則で、値を持つ要素が 2 個） | `error: an alternative without an action must have exactly one element with a value, but it has 2` |

一つめは `Flag <- 'on' { True }` と書く。
二つめは、二つの値を束縛してアクションで組み立てる。
型注釈とアクションをどちらも書かなければ、`Pair` は型を生成する規則になり、誤りにならない（[型の推論と生成](#型の推論と生成)）。

### 型の推論と生成

`%syntax` のない文法で、型注釈がなく、どの選択肢もアクションを持たない規則は、選択肢の値から型が決まる（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）。
値の型を verbatim ブロックに書き、型注釈と束縛とアクションで値を組み立てる手間を、文法の形から機械的に省くためである。

| 分類 | 条件 | 規則の型 | 選択肢の値 |
|---|---|---|---|
| `()` の規則 | どの選択肢も `()` 以外の値を持つ要素を持たない | `()` | `()` |
| 型を推論する規則 | どの選択肢も、`()` 以外の値を持つ要素をちょうど一つ持ち、それらの型がすべて同じ | その型 | その要素の値 |
| 型を生成する規則 | それ以外 | 生成した型 | 構築子に要素の値を並べたもの |

```hpeg
%module Example.Generated

Expr <- Expr '+' Sp Atom # 型を生成する。値の数が 2 と 1
     / Atom

Sp <- ' '* # () の規則

Num <- $[0-9]+ Sp # 型を推論する。型は Text

Paren <- '(' Sp Expr ')' Sp # 型を推論する。型は Expr

Atom <- Num # 型を生成する。Text と Expr が違う
     / Paren
```

生成モジュールは、型を生成する規則ごとに、次の型を宣言して公開する。

```haskell
data Expr = Expr1 Expr Atom | Expr2 Atom
  deriving (Eq, Show)

data Atom = Atom1 Text | Atom2 Expr
  deriving (Eq, Show)
```

`parse "1+2"` は `Right (Expr1 (Expr2 (Atom1 "1")) (Atom1 "2"))` を返す。
`Paren` は値を一つだけ返すので、構築子で包まずに `Expr` の値を返す。

分類は、規則が互いを呼ぶので、二段の不動点で決める。
はじめに、すべての規則を `()` の規則とみなし、`()` 以外の値を持つ選択肢のある規則を `()` でない規則に移す。
値の数え方は [`()` の値は数えない](#-の値は数えない)と同じで、`[()]` と `Maybe ()` も `()` の値とみなす。
次に、`()` でない規則のうち、値の数が 1 でない選択肢を持つ規則を、型を生成する規則に決める。
残りの規則は、要素の型（[値を持つ式](#値を持つ式)）から型を推論する。
二つの違う型が現れた規則と、型が最後まで決まらない規則は、型を生成する規則に移す。

二つの型が同じかどうかは、型の文字列を空白を除いて比べて決める。
`[Int]` と `[ Int ]` は同じ型、`Text` と別名の `Name`（`type Name = Text`）は違う型である。
雛形の呼び出しの型は、展開した規則の型注釈の型で、型の変数を置き換えた型は括弧で囲まれる（`[(Int)]`）。
比べられないときは型を生成する側に倒れるので、生成モジュールの型が合わなくなることはない。

生成する型は、次のように作る。

- 型の名前は、規則名の先頭を大文字にしたものである。大文字のない文字で始まる規則名は、前に `Rule'` を付ける（`値` の型は `Rule'値`）
- 選択肢ごとに構築子を一つ作る。値を一つだけ持つ選択肢も構築子で包む
- 構築子の名前は、選択肢が一つなら型の名前と同じ、二つ以上なら型の名前に選択肢の番号（1 から）を付けたもの（`Expr1`、`Expr2`）である
- 構築子の引数は、選択肢の `()` 以外の値を持つ要素の値を、現れる順に並べたものである。束縛の有無によらない
- 値を持つ要素のない選択肢は、引数のない構築子になる
- 構築子が一つで引数が一つの型は、`newtype` にする
- 構築子ごと（`Expr(..)`）公開する。`peg-hs gen --export` で入口を絞ったときは、公開する入口の型から辿れる型だけを公開する

選択肢の末尾（アクションを書く位置）に `@名前` を書くと、その選択肢の構築子の名前になる。
`@名前` を書いた規則は、型を推論できる場合も、型を生成する。
既定の名前は選択肢の並びで変わるので、長く使う文法では `@名前` で固定する。
言語サーバーのコードアクションは、既定の名前を `@名前` として書き出す。

```hpeg
# 断片
Expr <- Expr '+' Sp Atom @Add
     / Atom @Single
```

生成する型は、既定で `Eq` と `Show` を導出する。
`%deriving Eq, Ord, Show` のように書くと、導出するクラスが変わり、引数なしの `%deriving` は何も導出しない。
構築子の引数に型注釈で書いた利用者の型が現れ、その型がクラスのインスタンスを持たなければ、GHC の誤りになる。
そのときは、`%deriving` で導出するクラスを減らすか、インスタンスを書く。

型を推論する規則と型を生成する規則は、型注釈とアクションを書いた規則から呼べる。
呼び出し元のアクションは、推論した型か生成した型の値を受け取る。
束縛は書いてよく、束縛した値は意味述語と規則の引数から読める。
選択肢に一つでもアクションを書くと、その規則は対象から外れ、型注釈がなければ型は `()` である。

この書き方は、型注釈とアクションを書いた文法より遅い。
キャプチャした `Text` と構築子を、使うかどうかによらず作るからである。
80 万文字の JSON の文書では、型注釈とアクションを書いた文法に比べて、時間は約 0.97 倍、最大の常駐メモリは約 1.18 倍だった（[docs/benchmarks/2026-11-06-json-generated-types.md](benchmarks/2026-11-06-json-generated-types.md)）。
この値は、生成した型の値をそのまま使う場合のもので、利用者の型に写す時間は含まない。
速さが要る規則だけ、型注釈とアクションを手で書く。
規則ごとに選べるので、時間のかかる規則だけを書き直せる。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 型注釈のある規則に `@名前` を書いた | `error: @Add names a constructor, but rule Expr has a type annotation` |
| アクションのある規則に `@名前` を書いた | `error: @Add names a constructor, but rule Expr has an action` |
| `()` の規則に `@名前` を書いた | `error: @Add names a constructor, but rule Sp has type (): no alternative has a value other than ()` |
| `%syntax` の文法に `@名前` を書いた | `error: @Add names a constructor, but the grammar has %syntax` |
| 小文字で始まる名前（`@add`） | `error: the constructor name add must start with an upper case letter` |
| 同じ名前を二度書いた | `error: the constructor Add is defined twice in rule Expr; name one of the alternatives with @Name` |
| 既定の名前が別の規則の型の名前と重なる（`S <- S1 / ...` と規則 `S1`） | `error: the constructor S1 of rule S has the name of the type of rule S1; name the alternative with @Name` |
| 型の名前が重なる（`expr` と `Expr`） | `error: the rules expr and Expr have the same type name Expr; rename one of them` |
| `%deriving` を二度書いた | `error: duplicate %deriving directive` |
| クラスの名前でないものを書いた（`%deriving eq`） | `error: %deriving expects class names, but got eq` |

`%syntax` の文法では、型注釈のない規則の型は、これまでどおり `()` である（[型を書かない文法](#型を書かない文法)）。
値を持つ要素が二つ以上のグループ（`(a:A ',' b:B)*`）は値を持たないので、値が要るときはグループを規則に切り出す。

### 位置を持つ構文木

アクションの中では、`_span` で選択肢が消費した入力の範囲を参照できる（[ADR 0008](adr/0008-source-positions.md)）。
`Span` は開始と終了の位置を持ち、位置はバイトオフセット、行、桁からなる。
構文木のノードに位置を持たせるときに使う。

```hpeg
%module Example.Located
%export Expr(..)

%{
import Data.Text (unpack)
import Peg.Runtime (Span)

data Expr = Lit Span Int | Add Span Expr Expr
  deriving (Show)
}%

Expr :: Expr
Expr <- l:Expr '+' r:Lit { Add _span l r }
      / Lit

Lit :: Expr
Lit <- n:Num { Lit _span n }

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

構文木の型 `Expr` を利用者のコードから使うため、`%export` で公開している。
`Span` と位置の型 `Pos` は、peg-runtime の `Peg.Runtime` が公開している。

範囲の開始は選択肢の評価を始めた位置、終了は最後に入力を消費した位置である。
先読みと意味述語は入力を消費しないので、`_span` の範囲を動かさない。
選択肢の途中の一点の位置が欲しいときは、そこを規則に切り出し、その規則のアクションで `_span` を取る。

## 規則の雛形

規則名の直後の山括弧に引数を書くと、規則の雛形になる（[ADR 0031](adr/0031-rule-templates.md)）。
雛形は、予約語や区切りのある列のように、文法の中に何度も現れる形を一度だけ書くためのものである。
引数は式であり、雛形の本体では引数を非終端のように書く。

```hpeg
%module Example.Print

%{
import Data.Text (Text)

data Stat = SPrint [Text]
  deriving (Show)
}%

Stat :: Stat
Stat <- K<'print'> xs:List<Name, ','> { SPrint xs }

Name :: Text
Name <- $[a-z]+ Sp

Sp <- [ \t]*

# 予約語：リテラルの後に識別子の文字が続かず、空白を読む
K<w> :: ()
K<w> <- w ![a-zA-Z0-9_] Sp

# 区切りのある一つ以上の列
List<p :: a, sep> :: [a]
List<p, sep> <- x:p xs:(sep Sp p)* { x : xs }
```

この文法は `print a, b` を `SPrint ["a","b"]` にする。
`K<'print'>` は `printer` の先頭には一致しない。

- 規則名と `<` の間に空白を置かない。`<-` はこれまでどおり定義の矢印である
- 引数には選択や逐次を含む任意の式を書ける。カンマや `>` を含む式は括弧で囲む
- 値を使う引数（本体で束縛する、またはアクションの省略で返す引数）は、型注釈で `p :: a` の形の型変数を宣言する。呼び出しごとに、型変数は引数の型に置き換わる
- 型を宣言しない引数（上の `w` と `sep`）は、本体の中で値を持たないものとして扱う
- 型を宣言した引数には、規則の呼び出し、テキストキャプチャ、雛形の呼び出しのように型の分かる式だけを渡せる

生成器は、雛形の呼び出しを引数の組ごとの規則に展開する。
展開した規則は、それぞれがメモ表を持ち、左再帰の解析も展開した後の規則に対して行う。
`%syntax` の文法では、雛形の呼び出しはノードを作らず、子を呼び出し元に並べる。
展開した規則の中の誤りは、雛形の定義の位置で報告される。

`%start`、`%entry`、`%recover`、`%nomemo`、`%token`、`%trivia`、`%inline` に雛形を書くことはできない。

### 呼び出し元の引数を使う雛形の引数

雛形の引数の中では、呼び出し元の規則の引数（[引数付き規則](#引数付き規則)）を使える（[ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)）。
字下げの深さを引数で渡す文法でも、「空行を挟んで同じものが続く」形を一度だけ書ける。

```hpeg
%module Example.Items

Doc <- Items(0)

Items(ind :: Int) :: ()
Items <- Lines<Item(ind)>

# 改行を挟んで p が続く
Lines<p> :: ()
Lines<p> <- p ('\n' p)*

# ちょうど ind 個の空白の後の項目
Item(ind :: Int) :: ()
Item <- ' '* &{ _col == ind } '-'
```

展開した規則は、引数が使った呼び出し元の引数を、同じ名前と型で受け取る。
上の `Lines<Item(ind)>` は `Lines'0(ind)` の呼び出しになり、`Lines'0` は `ind :: Int` を引数に持つ引数付き規則になる。

- 取り込むのは、引数の中の Haskell の断片（規則の呼び出しの引数と意味述語）に現れる名前である。修飾名（`M.ind`）、文字列と文字のリテラルの中、予約束縛（`_env`、`_col`、`_span`）は数えない
- 引数を二つ以上取り込むときは、名前の順に並べる。型は呼び出し元の型注釈に書いたものである
- 同じ引数で別の規則から呼ぶと、取り込んだ引数の型が同じなら同じ展開した規則を使い、違えば別の規則にする
- 雛形の本体が雛形を呼ぶときも、引数は内側の雛形に渡っていく
- 取り込んだ引数を持つ展開した規則は引数付き規則なので、左再帰に加われない。誤りは雛形の定義の位置で報告される

雛形の引数は、呼び出し元の選択肢の束縛（`x:N` の `x`）を使えない。
束縛の型は束縛した式から推論しないと分からず、展開した規則の引数の型を書けないからである。
束縛の値を雛形に渡したいときは、次の節の値の引数で渡す。

取り込む名前が雛形の本体の束縛やコードの名前、雛形の値の引数の名前と同じだと、取り込めない。
雛形の引数は本体に埋め込まれるので、本体の束縛 `x` の後ろに置かれた引数の `x` は、呼び出し元の引数ではなく本体の束縛を指してしまう。
この場合は、呼び出し元の引数の名前を変える。

### 雛形の値の引数

雛形は、引数付き規則と同じ Haskell の値の引数を持てる（[ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)）。
値の引数は型注釈の雛形の引数の後ろに書き、定義には書かない。
字下げの深さのように、本体の中で値として使うものを渡す。

```hpeg
%module Example.Indented

Doc <- Indented<Item(0)>(0)

# 深さ n に字下げした p が、改行を挟んで続く
Indented<p>(n :: Int) :: ()
Indented<p> <- Ind(n) p ('\n' Ind(n) p)*

Item(ind :: Int) :: ()
Item <- '-' (' ' Indented<Item(ind + 2)>(ind + 2))?

# ちょうど n 個の空白
Ind(n :: Int) :: ()
Ind <- ' '* &{ _col == n }
```

呼び出しでは、雛形の引数の `>` の直後に値の引数を書く（`Indented<Item(ind + 2)>(ind + 2)`）。
`>` と `(` の間に空白を置かない。
`Lines<p> (x)` は、これまでどおり雛形の呼び出しと括弧のグループの逐次である。
引数付き規則の呼び出し `Name(args)` と同じ規則である。

展開した規則は、雛形の値の引数（宣言の順）の後に、呼び出し元から取り込んだ引数（名前の順）を引数に持つ。
上の `Indented<Item(ind + 2)>(ind + 2)` は `Indented'1(ind + 2, ind)` の呼び出しになる。

- 値の引数の式は呼び出し元で評価する。引数付き規則の呼び出しと同じく、呼び出し元の引数、左にある束縛、`_env`、`_col` を使える
- 展開した規則は、値の引数の値ごとには分かれない。値は実行時に渡り、メモ表の鍵になる
- 雛形は雛形の引数（`<...>`）を一つ以上持つ。値の引数だけを持つものは引数付き規則である

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 雛形を引数なしで呼んだ（`K`） | `error: the template K needs arguments: K<...>` |
| 引数の数が違う（`K<'a', 'b'>`） | `error: the template K expects 1 argument(s), but got 2` |
| 型を宣言した引数にリテラルを渡した（`List<'a', ','>`） | `error: the argument for p must be a rule, a capture or a template call, since its value is used` |
| 型注釈と定義で引数の名前が違う（`K<w> ::` と `K<v> <-`） | `error: the template parameters of the definition of K do not match its type annotation` |
| 規則名と `<` の間に空白を置いた（`K <'a'>`） | `error: expected a rule, a directive or %{ ... }%` など、構文の誤りになる |
| `%entry K` のように雛形を指定した | `error: the template K cannot be named in %entry` |
| 雛形でない規則を山括弧で呼んだ（`B<'x'>`） | `error: rule B is not a template` |
| 雛形が雛形を際限なく呼ぶ（`T<p> <- T<(p p)>`） | `error: the expansion of the template T does not end: templates call templates more than 64 levels deep` |
| 雛形の引数が呼び出し元の束縛を使った（`x:N Lines<Item(x)>`） | `error: the argument of the template Lines uses the binding x, which a template cannot take; pass it as a value argument` |
| 値の引数を宣言していない雛形に値の引数を渡した（`Lines<Item>(1)`） | `error: the template Lines takes no value arguments` |
| 値の引数の数が違う（`Indented<Item>(1, 2)`） | `error: the template Indented expects 1 value argument(s), but got 2` |
| 雛形の定義の側に値の引数を書いた（`Indented<p>(n :: Int) <- ...`） | `error: parameters belong to the type annotation, not the definition` |
| 本体で `x` を使う雛形の引数が、呼び出し元の引数 `x` を使った | `error: the template T uses the name x in its body, so its argument cannot take the parameter x of the rule B; rename the parameter` |

## 左再帰

規則は自分自身を左端で呼べる（[ADR 0001](adr/0001-bounded-left-recursion.md)）。
直接の左再帰は左結合の値を作る。
右結合にしたい場合は、右再帰で書く。

```hpeg
# 断片
Sub :: Int
Sub <- l:Sub '-' r:Num { l - r }   # 10-3-2 は (10-3)-2 すなわち 5
     / Num

Pow :: Int
Pow <- b:Num '^' e:Pow { b ^ e }   # 2^3^2 は 2^(3^2)
     / Num
```

複数の規則を経由する間接の左再帰も書ける。
演算子の優先順位は、規則の階層で表す。

```hpeg
%module Example.Calc

%{
import Data.Text (unpack)
}%

Expr :: Int
Expr <- l:Expr '+' r:Term { l + r }
      / l:Expr '-' r:Term { l - r }
      / Term

Term :: Int
Term <- l:Term '*' r:Factor { l * r }
      / Factor

Factor :: Int
Factor <- '(' Expr ')'
        / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

`parse "2*(3+4)"` は `Right 14` を返す。

左再帰には二つの制約がある。
引数付き規則は左再帰に関与できない。
左再帰に関与する規則のメモ化は外せない。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 引数付き規則が左再帰する（`E(n :: Int)` と `E <- l:E(n) '+' ...`） | `error: rule E takes parameters and cannot take part in left recursion` |
| 左再帰の規則に `%nomemo` を付けた | `error: rule E takes part in left recursion and must be memoised` |

## 文脈に依存する構文

標準の PEG は、いまの位置から先の入力だけを見て照合を決める。
字下げで構造が決まる言語や、文書の別の場所の定義で解釈が変わる言語は、それだけでは書けない。
次の四つの拡張は、そうした構文のためにある（[ADR 0012](adr/0012-context-sensitive-extensions.md)）。

どの拡張も、規則の結果が「規則、引数、位置の組と、解析環境」だけで決まるように設計されている。
そのため、メモ化と左再帰の解析の正しさを損なわない。
解析中に書き換えられる状態は用意していない。

### 意味述語

`&{ 式 }` は、Haskell の真偽式が真のときに、入力を消費せずに成功する。
`!{ 式 }` は偽のときに成功する。

```hpeg
# 断片
Byte :: Int
Byte <- n:Num &{ n < 256 } { n }
```

式が参照できるのは、同じ選択肢の中で述語より左にある束縛、規則の引数、`_env`、`_col` である。
意味述語の失敗は、エラーの期待一覧に項目を加えない。
意味述語だけで失敗した位置の報告は、`行:桁: parse error` のように位置だけになる。

### 引数付き規則

規則は Haskell の値を引数に取れる。
型注釈で引数の名前と型を宣言し、呼び出しでは Haskell の式を渡す。

```hpeg
# 断片
Indent(w :: Int) :: ()
Indent <- &{ _col >= w }
        / ' ' Indent(w)
```

この規則は、桁が `w` に達するまで空白を読む。
メモ表は規則と位置に加えて引数の値ごとに結果を持つので、同じ位置で引数を変えて呼んでもよい。

- 規則名と `(` の間に空白を置かない。`A(x)` は呼び出し、`A (x)` は非終端 `A` と括弧のグループの逐次である
- 引数の型は `Ord` のインスタンスでなければならない。そうでなければ、生成モジュールのコンパイルで GHC が報告する
- 引数付き規則は、開始規則と `%entry` の規則と回復の規則にできない。入口から渡す値がないためである
- 引数の値の種類が多いと、メモ表のメモリが増える。字下げの幅のように値の範囲が小さい用途に使う

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 引数を取らない規則を `B(1)` の形で呼んだ | `error: rule B takes no arguments` |
| 引数の数が違う（`Indent`） | `error: rule Indent expects 1 argument(s), but got 0` |
| 定義の側に引数を書いた（`A(n :: Int) <- ...`） | `error: parameters belong to the type annotation, not the definition` |
| 型注釈の引数に型がない（`A(n) :: ()`） | `error: expected a parameter of the form name :: Type` |
| 空の引数（`B()`） | `error: expected an argument` |
| 開始規則が引数を取る | `error: the entry rule A cannot take parameters` |

### 解析環境

`%env` で、解析全体を通じて変わらない値の型を宣言できる。
宣言した文法の入口は、最初の引数に環境を取る。
規則の中からは `_env` で参照する。

```hpeg
%module Example.Link
%env Set Text

%{
import Data.Set (Set, member)
import Data.Text (Text)
}%

Link :: Text
Link <- '[' l:$[a-z]+ ']' &{ member l _env } { l }
```

この文法の入口は `parse :: Set Text -> Text -> Either ParseError Text` である。
`[foo]` は、環境の集合に `foo` が含まれるときだけ解析に成功する。

文書の後方にある定義を参照するような構文は、二回の解析で扱う。
一回目の解析で定義を集め、それを環境として二回目の解析に渡す。

### 桁の参照

`_col` は、評価している位置の桁を 0 から数えた値である。
コードポイント一つを 1 桁と数える。
`%tabstop 4` を宣言すると、タブは次の 4 の倍数の桁まで進むものとして数える。
宣言しなければ、タブも 1 桁である。

`_col` は照合の判断に使う値であり、エラーの位置の表示に使う桁（1 から数え、`%tabstop` の影響を受けない）とは別物である。

`_col` はアクションからは参照できない。
桁を値として受け取りたいときは、桁を引数に取ってそのまま返す規則を通す。

```hpeg
%module Example.Column

Item :: Int
Item <- ' '* Col(_col) 'a'

# 何も読まず、受け取った桁を値として返す
Col(c :: Int) :: Int
Col <- { c }
```

`   a` を解析すると、`a` の直前の桁 `3` が値になる。

字下げの判定では、規則に渡す基準の桁を、文字の境界の `_col` ではなく、接頭辞が終わる論理上の桁にする書き方がある。
CommonMark では、コンテナの接頭辞がタブの途中で終わることがある。
タブは一文字なので、`_col` はタブの前か後の桁にしかならない。
接頭辞が終わる桁を計算して規則の引数で渡せば、タブの残りの桁を内容の字下げとして数えられる（[ADR 0018](adr/0018-tab-partial-consumption.md)）。

## メモ化を外す

既定では、すべての規則の結果は位置ごとにメモ表に記録され、同じ規則が同じ位置で二度評価されることはない。
空白や一文字の字句のように、同じ位置で二度呼ばれることがほとんどない規則は、`%nomemo` でメモ化を外すとメモリを減らせる（[ADR 0017](adr/0017-nomemo-implementation.md)）。

```hpeg
# 断片
%nomemo Ws
%nomemo Hex
```

メモ化を外しても、解析の結果と失敗の報告は変わらない。
ただし、深い後戻りの中で何度も呼ばれる規則のメモ化を外すと、解析時間が入力の長さに比例しなくなる。
外す前と後で、ベンチマークを比べる。
左再帰に関与する規則には指定できない（[左再帰](#左再帰)）。

## 生成されるモジュール

### 入口

生成モジュールは、開始規則の入口 `parse` を公開する（[ADR 0014](adr/0014-generated-module-api.md)）。
`%entry` で指定した規則には、規則名を後ろに連結した入口が加わる。
上の `Example.Calc` の文法に `%entry Term` を加えると、生成モジュールは次の二つを公開する。

```haskell
parse     :: Text -> Either ParseError Int   -- 開始規則 Expr
parseTerm :: Text -> Either ParseError Int
```

入口は入力の全体の消費を要求する。
規則が成功しても入力が残っていれば、解析は失敗する。

生成モジュールが公開するのは、入口と、生成した型（[型の推論と生成](#型の推論と生成)）と、`%export` に挙げた名前だけである。
入口と `%syntax` の名前は、`peg-hs gen --export NAME` で使うものだけに狭められる（[ADR 0061](adr/0061-select-generated-exports.md)）。
宣言を削ったモジュールは、使われない import とトップレベルの束縛の警告を出さない。削った規則のアクションだけが使っていた verbatim ブロックの import や関数が、使われなくなるためである。verbatim ブロックのそれらの誤りは、`--export` を付けずに生成して確かめる（[ADR 0062](adr/0062-warnings-of-pruned-generated-modules.md)）。
規則の内部の実装は公開されない。
`%export` には、`%export Expr(..), prettyExpr` のように Haskell のエクスポートの項目をカンマで区切って書く。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 同じ規則を `%entry` に二度書いた | `error: the rule A is named in %entry twice` |
| 引数付き規則を `%entry` に書いた | `error: the entry rule A cannot take parameters` |

### 解析の失敗

解析に失敗すると、入口は `ParseError` を返す。
`ParseError` は、入力の中で最も遠くまで進んだ位置と、その位置で期待していた終端の一覧を持つ（[ADR 0005](adr/0005-error-reporting.md)）。
期待の一覧に入るのは、リテラル、文字クラス、任意の一文字、入力の終わりである。
否定先読みと意味述語による失敗は、一覧に項目を加えない。

peg-runtime の `renderParseError` は、失敗を人間向けの一行にする。
上の `Example.Calc` の文法に `1+*2` を与えると、3 桁目の `*` で失敗し、次のように表示される。

```
1:3: expected '(' or [0-9]
```

`1+2 ` のように末尾に空白があると、4 桁目で、続きうる終端と入力の終わりを期待して失敗する。

```
1:4: expected '*', '+', '-', [0-9] or end of input
```

期待の一覧が空のとき（否定先読みや意味述語だけで失敗したとき）は、`行:桁: parse error` のように位置だけを表示する。

### 位置の数え方

エラーの位置と `_span` の位置は、次の規約で数える。

| 欄 | 数え方 |
|---|---|
| バイトオフセット | 入力の先頭を 0 とする UTF-8 のバイト数 |
| 行 | 1 から数える。LF で改行する。CRLF の CR は行末の一文字、単独の CR は改行にならない |
| 桁 | 1 から数える。コードポイント一つを 1 桁とし、タブも 1 桁 |

## ロスレスな構文木

`%syntax` を書いた文法からは、型付きの値を返す入口に加えて、入力の文字列を一文字も失わない構文木を返す入口が生成される（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。
空白やコメントを扱う lint や formatter のためのものである。
型付きの値に空白やコメントを持たせると、すべての規則のアクションで空白の値を拾うことになり、一か所でも拾い忘れれば元の文字列を復元できなくなる。
構文木は、この手間をなくす。

```hpeg
%module Example.CalcSyntax
%syntax
%token Num
%token Ws
%trivia Ws
%inline Sp

%{
import Data.Text (unpack)
}%

Expr :: Int
Expr <- l:Expr Sp '+' Sp r:Num { l + r }
      / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }

Sp <- Ws?

Ws <- [ \t]+
```

この文法から生成されるモジュールは、`parse` に加えて次の入口を公開する。

```haskell
parseSyntax :: Text -> Either ParseError SyntaxNode
```

構文木は次のように作られる。

- 規則の呼び出しは、規則名を種類とするノードになる。`%inline` の規則は、ノードを作らずに子を呼び出し元に並べる
- `%token` の規則の一致は、内部の構造を持たない一つのトークンになる
- それ以外の終端の一致は、同じノードの直下で連続するものが一つの無名のトークンにまとまる。`'<' '/'` は `</` という一つのトークンになるので、区別したい記号は `%token` の規則として書く
- 先読みと意味述語は木に何も加えない。後戻りで捨てた試行も木に残らない
- 構文木のテキストは、入力の文字列と常に一致する

構文木の入口では、アクションは評価されない。
ただし、意味述語や規則の引数が束縛の値を参照する場合は、その値を計算するためにアクションが評価される。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `%syntax` のない文法に `%token` を書いた | `error: %token requires %syntax`（`%trivia` と `%inline` も同じ） |
| `%token` でない規則を `%trivia` にした | `error: %trivia A must name a %token rule` |
| 同じ規則を `%token` と `%inline` の両方にした | `error: rule B cannot be both %token and %inline` |
| 開始規則か `%entry` の規則を `%inline` にした | `error: the entry rule A cannot be %inline: the root of the syntax tree needs a kind` |
| `%syntax` に引数を書いた | `error: %syntax takes no argument` |

### 型付きの取り出し関数

`%token` と `%inline` 以外の規則ごとに、ノードを包む型と、束縛ごとの取り出し関数が生成される。
上の文法では次のようになる。

```haskell
newtype ExprSyntax = ExprSyntax SyntaxNode
castExprSyntax :: SyntaxNode -> Maybe ExprSyntax
exprL :: ExprSyntax -> Maybe ExprSyntax
exprR :: ExprSyntax -> Maybe SyntaxToken
```

取り出し関数の名前は、規則名の先頭を小文字にし、束縛の名前の先頭を大文字にしてつないだものになる。
型の名前は、規則名の先頭を大文字にしたものに `Syntax` を付ける。
Haskell の型名は大文字で始まらなければならないので、漢字、仮名、`_` のように大文字のない文字で始まる規則名は、前に `Rule'` を付ける（`数式` から `Rule'数式Syntax`、`castRule'数式Syntax`）。
二つの規則が同じ型名になる場合（`expr` と `Expr` など）は、`%syntax` の文法では誤りになる（[ADR 0053](adr/0053-type-names-of-rules-without-case.md)）。

| 書き方 | 報告 |
|---|---|
| `%syntax` の文法に `expr` と `Expr` がある | `error: the rules expr and Expr have the same type name ExprSyntax in the syntax tree; rename one of them` |

束縛の名前の変更は、生成モジュールの公開 API の変更になる。
取り出し関数の名前が verbatim ブロックの名前と重なると、GHC のエラーになる。
取り出し関数は、`%trivia` の種類のトークンを読み飛ばす。

このほか、規則ごとの種類の定数（`syntaxKindExpr` など）、種類の名前を返す `nameOfSyntaxKind`、トリビアの種類かどうかを返す `isTriviaSyntaxKind` が生成される。
構文木の移動と表示の関数は peg-runtime の `Peg.Runtime.Syntax` にある。
`debugTree nameOfSyntaxKind` は、木を一要素一行の字下げで表した文字列にする。

### 型を書かない文法

構文木だけを使うなら、規則の値は要らない。
`%syntax` を付けた文法では、型注釈もアクションも書かずに済む（[ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)）。

```hpeg
%module Example.CalcTree
%syntax
%token Num
%token Ws
%trivia Ws

Expr <- Expr Ws? '+' Ws? Term
     / Term

Term <- Term Ws? '*' Ws? Atom
     / Atom

Atom <- Num
     / '(' Ws? Expr Ws? ')'

Num <- $[0-9]+

Ws <- [ \t]+
```

`Num <- $[0-9]+` は、キャプチャの値（`Text`）を一つだけ持つ選択肢である。
`%syntax` のない文法なら、`Num` は型を推論する規則になり、型は `Text` である（[型の推論と生成](#型の推論と生成)）。
`%syntax` の文法では、型注釈のない規則の、アクションを省略した選択肢の値は、要素によらず `()` になる。
キャプチャ、型注釈のある規則の呼び出し、`()` でない値を持つ要素が、いくつあってもよい。
要素の値は捨てられ、数字の文字列は構文木の `Num` のトークンとして残る。
値は `parseSyntax` の返す木から、取り出し関数と `syntaxText` で読む。

束縛は、これまでどおり束縛する。
`n:Num &{ n > 0 }` の `n` は意味述語から読めるので、型付きの値が要る規則（`Num :: Int` など）を呼んで束縛すれば、値で入力を選り分けられる。
束縛は取り出し関数の名前にもなる。

次の規則は、これまでどおり扱う。

- `%syntax` のない文法。型注釈とアクションのない規則の型は、推論するか生成する（[型の推論と生成](#型の推論と生成)）
- 型注釈のある規則。`:: ()` と書いた規則も含む。型注釈を書くのは、型付きの値を返すつもりだからである
- アクションを書いた選択肢と、要素のない選択肢

型付きの値も使うつもりで型注釈を書き忘れた規則は、値を失っても誤りにならない。
ただし、その規則の値は `()` なので、型付きの値を使う側のコード（呼び出し元のアクションや入口の利用者）がコンパイルできず、そこで気付ける。

構文木を作る費用は、この書き方でも変わらない。
80 万文字の JSON の文書では、この書き方の `parseSyntax` は、`%syntax` のない型付きの文法の `parse` に比べて、時間と最大の常駐メモリがどちらも約 1.2 倍だった（[docs/benchmarks/2026-11-06-json-generated-types.md](benchmarks/2026-11-06-json-generated-types.md)）。
前の計測では、時間が約 1.6 倍、メモリが約 1.1 倍だった（[docs/benchmarks/2026-11-06-json-untyped-syntax.md](benchmarks/2026-11-06-json-untyped-syntax.md)）。
値を組み立てない分、型注釈とアクションを書いた `%syntax` の文法の `parseSyntax` よりは速い。
速さが要るときは、`%syntax` を付けずに型注釈とアクションを書く。

## 構文エラーからの回復

`e ^label` は、`e` が失敗したときにラベル `label` を送出する（[ADR 0021](adr/0021-error-recovery.md)）。
送出は普通の失敗と違い、順序付き選択 `/` は次の選択肢を試さずに、そのまま外に伝える。
先読み（`&e`、`!e`）の中の送出だけは、普通の失敗として扱われる。

ラベルには二つの役割がある。
一つは、誤りの報告にラベルの名前を載せることである。
もう一つは、`%recover` で回復の規則を与え、誤りを含む入力からも結果を得ることである。

```hpeg
%module Example.Commands
%recover close CloseAtLineEnd

%{
import Data.Text (Text)

data Inline = Command Text | Words Text
  deriving (Show)
}%

Line :: [Inline]
Line <- Inline*

Inline :: Inline
Inline <- '[' name:$[a-z]+ (']' ^close) { Command name }
        / w:$[a-z ]+ { Words w }

# 何も読まない。次が行の終わりか入力の終わりなら成功し、`]` がなくても命令を閉じたものとみなす
CloseAtLineEnd <- &('\n' / !.)
```

この文法は、閉じていない `[name` を行の終わりで閉じたものとみなして解析を続ける。

ラベルは、そこで失敗したらどの選択肢でも成功しえない位置にだけ付ける。
そうでない位置に付けると、後戻りすれば受理できた入力まで受理されなくなる。
上の例の `]` は、`[` と名前を読んだ後なので、ほかの選択肢が成功しうる入力は残っていない。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `%recover` の規則が定義されていない | `error: undefined rule R` |
| 同じラベルに `%recover` を二つ書いた | `error: the label l has more than one recovery rule` |
| 文法に現れないラベルを `%recover` か `%safe` に書いた | `error: the label m does not appear in the grammar` |
| 回復の規則が引数を取る | `error: the recovery rule R cannot take parameters` |
| `%recover` の引数が二つでない | `error: %recover expects a label and a rule name` |
| 先読みの中にラベルを書いた（`!('a' ^l)`） | lint：`warning: the label l has no effect: its throw inside the lookahead is a failure of the lookahead [ineffective-label]; remove ^l` |

先読みの中の送出は先読みの普通の失敗になるので、そこに付けたラベルは何の効果も持たない。

### ラベルの安全性の検査

ラベルの位置が安全か（そこで送出しても、受理される入力が変わらないか）を、`peg-hs gen` が検査する（[ADR 0028](adr/0028-label-safety-check.md)）。
危険かもしれないラベルは警告として報告し、生成は続ける。

```
$ peg-hs gen Grammar.hpeg
Grammar.hpeg:3:11: warning: the label l may reject valid input: where it fails, the alternative at 3:28 can match
```

この例は、`S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }` の `l` への警告である。
`ac` は二つめの選択肢で受理できるが、ラベルがあると一つめの選択肢の `'b'` で送出して止まる。
警告の後半は、失敗した後に成功しうる別の道を示す。
ほかに、繰り返しが続きうる（`the repetition at 行:桁 can continue`）、ラベルの後で解析が続きうる（`the parse can continue at 行:桁`）、入口の規則の後で入力が終わりうる（`the input can end after the rule A, which is an entry`）などがある。

各ラベルは、ほかのラベルをすべて外した文法の上で判定する（[ADR 0029](adr/0029-label-safety-implementation-deviations.md)）。
選択肢の共通の部分を比べるときも、ほかのラベルを除いて比べるので、ほかのラベルの有無で判定は変わらない（[ADR 0056](adr/0056-label-insertion-and-template-deviations.md)）。
入れ子のラベルでは、外側のラベルは内側の失敗をそのまま外へ伝えるものとして扱う。
そのため、警告が一つもない文法は、ラベルをすべて外した文法と同じ入力を受理する。
ほかのラベルが送出して止めるおかげで安全なラベルにも警告することがあるが、その代わりに保証が分かりやすくなる。
先読みの中の選択肢も検査し、失敗が先読みの境界に達したところで検査を終える。

検査は入力の次の一文字を基本に判定する近似であり、安全なラベルに警告することがある。
次の三つは、一文字より先まで見て判定する（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）。

- **規則の呼び出しを越えた共通の接頭辞**：失敗した選択肢がそれまでに読んだ要素と、後の選択肢が同じ要素で始まるなら、その部分を除いて比べる。後の選択肢の先頭の規則の呼び出しは、その規則の選択肢に展開して比べる。引数付き規則は、仮引数を実引数に置き換えたうえで、引数の字句が一致する呼び出しを同じものとみなす（選択肢 `BadIndent(ind) / OrphanDef(ind)` の `BadIndent` と `OrphanDef` が、どちらも `Ind(ind)` で始まる場合など）
- **定数の意味述語**：`&{ False }` と `!{ True }` は決して成功せず、`&{ True }` と `!{ False }` は必ず成功するものとして扱う
- **既知の接頭辞**：失敗した選択肢がリテラル（またはリテラルだけの選択肢からなる規則）で始まるなら、入力がその文字列で始まることを使い、後の選択肢がその入力で必ず失敗するかを確かめる（`'%%'` の後の `!'%%'`、`'[='` の後の `'[' Ident` など）

それでも、意味述語で文字を判定する規則（`c:$. &{ isAlpha c }` など）は、どの文字でも成功しうるものとして扱われる。
その規則で始まる選択肢が近くにあると、警告が出やすい。
引数の値の大小（`Ind(n)` と `Ind(n + 2)` が読む空白の数の違いなど）も判定しない。
間接の左再帰で成長する選択肢の中のラベルは、安全とも危険とも判定せず、`the label l cannot be checked: ...` と報告する。

安全なことを確かめたラベルは、`%safe` で警告を止める。
理由はコメントに書く。

```hpeg
# 断片
# [[ と [ は二文字目まで見れば区別できる
%safe table
```

`%safe` はラベルの名前で効く。
同じ名前のラベルを複数の位置で使うと、一か所が危険でもすべての警告が止まるので、確かめた位置ごとに別の名前を付けるのがよい。
安全を確かめるには、`peg-hs gen --strip-labels MODULE` でラベルを外した文法を別のモジュールとして生成し、元の文法と受理する入力を比べるテストを書く。
`peg-hs gen --Werror` は、警告があれば生成せずに失敗する。

#### 安全なラベルの挿入

検査が安全と示せる位置には、`peg-hs label` でラベルをまとめて挿入できる（[ADR 0054](adr/0054-automatic-label-insertion.md)）。
候補は、逐次の中で必ず入力を読む要素より後にある、リテラル、文字クラス、`.`、規則の参照、グループ、`e+`（`$` が付いたものを含む）である。
候補ごとに仮のラベルを置いて検査し、安全と判定したものだけを挿入する。
したがって、挿入したラベルに `peg-hs gen` は警告せず、受理する言語も変わらない。

```hpeg
%module Example.List

List :: [Int]
List <- '[' v:Num vs:(',' Num)* ']' !. { v : vs }

Num :: Int
Num <- [0-9]+ { 1 }
```

この文法に `peg-hs label --write` を実行すると、`List` の定義は次のようになる。

```hpeg
# 断片
List <- '[' v:Num ^List_Num vs:(',' Num ^List_Num_2)* ']' ^List_rbracket !. { v : vs }
```

`'['`、`','`、`[0-9]+` は逐次の先頭にあり、`(...)*` は空文字列に一致し、`!.` は先読みなので、どれも候補にならない。
名前は `規則名_対象` であり、同じ名前の二つめからは `_2`、`_3` が付く。
`S <- 'a' 'b' { () } / 'a' 'c' { () }` では、`'b'` のラベルは `ac` を拒否するので挿入されず、`'c'` にだけ `^S_c` が付く。

挿入されない位置もある。
`%recover` を持つラベルを付けた式の内側と、そこから呼ぶ規則には挿入しない。回復の規則を持たないラベルの送出は外側の回復を素通りするので、回復していた誤りが文法全体の誤りに変わってしまうからである。
`peg-hs lint` が「後の選択肢は試されない」と警告する、常に成功する選択肢とそこから呼ぶ規則にも挿入しない。そこにラベルがあると lint の判定が変わり、決して試されない選択肢への警告が消えてしまうためである（[ADR 0056](adr/0056-label-insertion-and-template-deviations.md)）。
意味述語で文字を判定する規則の近くと間接の左再帰の中は、安全でも検査が示せないので、やはり挿入されない。

挿入したラベルは回復しない。
回復させたいラベルには、`%recover` と回復の規則を書く。
言語サーバーのコードアクション「`%recover` を加える」は、`%recover 名前 Recover_名前` と、同じ逐次の中でラベルを付けた式の次にあるリテラルの手前（なければ行の終わりの手前）まで読み飛ばす回復の規則の雛形を加える。
雛形のアクションは型の穴 `{ _ }` なので、生成したモジュールをコンパイルすると GHC が型を示す。それを見て値を書き入れる。

### 二つのモード

ラベルを含む文法からは、回復しない入口と回復する入口の両方が生成される。
上の `Example.Commands` の文法では次のようになる。

```haskell
parse        :: Text -> Either ParseError [Inline]          -- 回復しない
parseRecover :: Text -> (Maybe [Inline], [SyntaxError])     -- 回復する
```

`%syntax` の文法には、構文木を返す回復の入口 `parseSyntaxRecover :: Text -> (SyntaxNode, [SyntaxError])` も加わる。

回復しない入口は、最初の失敗で止まる。
送出されたラベルは `ParseError` の `parseErrorLabel` に入る。

回復する入口では、ラベルが送出されて `%recover` の回復の規則があれば、送出の位置から回復の規則を評価する。
回復の規則が成功すれば、ラベルを付けた式はその値で成功したものとして解析が続き、構文エラーが一つ記録される。
回復の規則がない、または回復の規則が失敗すれば、送出はさらに外に伝わる。

- 回復の規則は引数を取れない。型は、ラベルを付けた式の値の型と同じでなければならない。値を持たない式に付けたラベルでは、回復の規則の値は捨てられる
- 回復の規則が入力を消費しない場合（閉じ括弧を補うような挿入の回復）、構文エラーの範囲は空になる
- 後戻りで捨てた試行の中の構文エラーは報告されない
- 開始規則の後に入力が残れば、残りの全体が一つの構文エラーになる。開始規則が回復できなければ、入力の全体が一つの構文エラーになる

`parseSyntaxRecover` は、どの入力に対しても構文木を返す。
回復した範囲は種類が `ERROR` のノードになり、構文木のテキストは常に入力と一致する。

構文エラーは `SyntaxError` の列で返る。
ラベル、範囲（バイトオフセット）、範囲の始まりの位置、送出の時点の期待集合を持つ。
ラベルから利用者向けのメッセージへの対応は、利用者が持つ。

## lint

`peg-hs lint` は、生成はできるが明らかに意図と違う書き方を警告する（[ADR 0033](adr/0033-grammar-linter.md)）。
規則は peg-hs が固定で持ち、選ぶことも、加えることも、個別に止めることもできない。
その代わり、どの規則も文法の意味から必ず導ける問題だけを指すので、警告は文法を直せば必ず消える。

```
$ peg-hs lint Op.hpeg
Op.hpeg:4:7: warning: the alternative never succeeds: the alternative at 3:7 matches its prefix '=' first [unreachable-alternative]; move it before the alternative that matches the prefix
```

警告は、位置、文言、角括弧の中の規則の名前、セミコロンの後の直し方の順に並ぶ。
規則は次の四つである。

| 規則 | 警告する書き方 | 節 |
|---|---|---|
| `unreachable-alternative` | 前の選択肢が必ず成功する、または前の選択肢のリテラルが接頭辞になっていて、決して成功しない選択肢 | [演算子](#演算子) |
| `duplicate-alternative` | 前の選択肢と同じ選択肢 | [演算子](#演算子) |
| `ineffective-label` | 先読みの中で効果を持たないラベル | [構文エラーからの回復](#構文エラーからの回復) |
| `unused-binding` | アクション、意味述語、規則の引数のどれにも現れない束縛 | [束縛](#束縛) |

lint は、警告とは別に info を出す。
info は、直せば文法が簡潔になるが、直さなくても誤りではない書き方を知らせる。
直すかどうかは文法の作者が決めることなので、`peg-hs lint` は既定では info を表示しない（[ADR 0067](adr/0067-lint-info-with-verbose.md)）。
`--verbose` を付けると、警告と同じ形で、`warning:` の代わりに `info:` と書いて表示する。
表示の順は、警告と合わせた位置の順である。
`--verbose` の有無によらず、info は終了状態を変えない。
警告と同じく、info も選ぶことや止めることはできない。

```
$ peg-hs lint Sp.hpeg
$ peg-hs lint --verbose Sp.hpeg
Sp.hpeg:4:12: info: the action can be omitted: the rule has type () and the alternative has no value [omittable-unit-action]; remove { () }
```

言語サーバーは、info を重大度 Hint の診断として報告する。
多くのエディタは、Hint に下線を引かずに淡く示す。

info の規則は次の三つである。

| 規則 | 知らせる書き方 | 節 |
|---|---|---|
| `omittable-unit-action` | 型注釈が `()` の規則の、省略できる `{ () }`。位置はアクションの `{` を指す。雛形の中のアクションは、すべての展開で省略できるときに限る | [アクションの省略](#アクションの省略) |
| `omittable-identity-action` | 束縛した値をそのまま返す、束縛ごと省けるアクション（`e:Expr { e }`）。位置はアクションの `{` を指す。`%syntax` の文法には出さない。雛形の中のアクションは、すべての展開で省けるときに限る | [アクションの省略](#アクションの省略) |
| `omittable-unit-annotation` | 型注釈 `A :: ()`。値を持たない、型注釈のない規則の型も `()` なので、行ごと省ける。位置は型注釈の始まりを指す。引数付き規則と雛形の型注釈には出さない | [規則](#規則) |

警告に従って直しても、文法が受理する入力と、誤りの位置は変わらない。
変わりうるのは、リテラルの接頭辞の警告に従って選択肢を消したときの、誤りの文言の「期待したもの」だけである。
`S <- '=' { () } / '==' 'x' { () }` の後ろの選択肢は決して成功しないが、入力が `=` で始まらないときは試されて失敗するので、空の入力の誤りは `1:1: expected '=' or '=='` になる。
後ろの選択肢を消すと、誤りは `1:1: expected '='` になる。
入力しても通らない字句が、誤りの案内から消えるということである（[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)）。

ラベルの安全性の検査は lint に含まれない。
安全なラベルにも警告しうる近似の検査なので、警告を止める手段のない lint には入れていない。
`peg-hs lint` が成功しても、ラベルの安全性は `peg-hs gen` の警告で別に確かめる。
`%safe` は lint の警告を止めない。
