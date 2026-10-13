# .hpeg 記法

peg-hs の文法定義ファイル（`.hpeg`）の書き方を、例を中心に解説する。
記法の各要素について、何をするものか、どう書くか、書き誤ったときに peg-hs が何を報告するかを順に述べる。
規範は各 ADR にあり、この文書はそれを利用者の側から読める形にまとめたものである。
記述が ADR と食い違う場合は ADR が優先する。

この文書は、採択済みの ADR の内容だけを反映する。
反映している ADR は [ADR 0001](adr/0001-bounded-left-recursion.md)、[ADR 0003](adr/0003-typed-semantic-actions.md)、[ADR 0004](adr/0004-peg-notation.md)、[ADR 0005](adr/0005-error-reporting.md)、[ADR 0006](adr/0006-memoization-control.md)、[ADR 0008](adr/0008-source-positions.md)、[ADR 0012](adr/0012-context-sensitive-extensions.md)、[ADR 0014](adr/0014-generated-module-api.md)、[ADR 0015](adr/0015-implementation-deviations.md)、[ADR 0016](adr/0016-language-extensions.md)、[ADR 0017](adr/0017-nomemo-implementation.md)、[ADR 0018](adr/0018-tab-partial-consumption.md)、[ADR 0019](adr/0019-lossless-syntax-tree.md)、[ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)、[ADR 0021](adr/0021-error-recovery.md)、[ADR 0026](adr/0026-discard-unused-values.md)、[ADR 0027](adr/0027-switch-to-self-hosted-parser.md)、[ADR 0028](adr/0028-label-safety-check.md)、[ADR 0029](adr/0029-label-safety-implementation-deviations.md)、[ADR 0030](adr/0030-unit-values-are-not-counted.md)、[ADR 0031](adr/0031-rule-templates.md)、[ADR 0033](adr/0033-grammar-linter.md)、[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)、[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)、[ADR 0050](adr/0050-hpeg-extension.md) である。

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
Hash :: ()
Hash <- '#' { () }    # リテラルの '#' はコメントではない
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

`%module`、`%start`、`%env`、`%tabstop`、`%syntax` は一度しか書けない。
`%entry`、`%export`、`%language`、`%nomemo`、`%token`、`%trivia`、`%inline`、`%recover`、`%safe` は何度でも書ける。
一行に一つの規則を書くディレクティブ（`%entry`、`%nomemo` など）は、規則ごとに一行を書く。

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

ただし `%syntax` の文法では、規則名から Haskell の型名を作る。
漢字のように大文字と小文字の区別のない文字で始まる規則名は型名にならず、生成モジュールのコンパイルが GHC のエラーになる（[ロスレスな構文木](#ロスレスな構文木)）。

### 開始規則と到達しない規則

開始規則は、`%start` で指定した規則か、ファイルで最初に定義した規則である。
どの規則も、開始規則、`%entry` の規則、`%recover` の回復の規則のどれかから呼び出しをたどって到達できなければならない。
使っていない規則を残すと、誤りになる。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 型注釈を書き忘れた | `error: rule A has no type annotation` |
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
Quoted <- '\'' s:$(!['\n] .)* '\'' { s }
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
そのため、空白の規則を挟んでもグループの値は一つのままである。

```hpeg
%module Example.List

%{
import Data.Text (Text)
}%

Names :: [Text]
Names <- n:Name ns:(',' Sp Name)* { n : ns }   # グループの値は Name の値

Name :: Text
Name <- n:$[a-z]+ Sp { n }

Sp :: ()
Sp <- [ \t]* { () }
```

この規則には三つの但し書きがある。

- `()` 以外の値を持つ要素が一つもない場合は、`()` の値も数える。`Spaces <- Ws` のように `()` の規則をそのまま返す選択肢は書ける
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
Word <- w:$(Num / Name) { w }

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }

Name :: Text
Name <- n:$[a-z]+ { n }
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

よくある誤り：

| 書き方 | 報告 |
|---|---|
| 値を持たない式に束縛した（`c:[a-z]`） | `error: cannot bind c: the expression has no value (capture the text with $)` |
| 同じ名前を二度使った（`x:A x:A`） | `error: the binding x is used twice in this alternative` |
| アンダースコアで始まる名前（`_x:A`） | `error: the binding _x is reserved: names starting with an underscore belong to the generator` |
| 束縛した名前をどこでも使っていない | lint：`warning: the binding x is not used [unused-binding]; remove x:` |

`c:[a-z]` は `c:$[a-z]` と書けば、一致した文字を `Text` として束縛できる。
使っていない束縛の警告は、`%syntax` の文法では出ない。
`%syntax` の文法では、束縛の名前が構文木の取り出し関数の名前にもなるためである。

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

値を持つ要素が 0 個、または 2 個以上の選択肢でアクションを省略すると、誤りになる。
数え方は、[`()` の値は数えない](#-の値は数えない)で述べたとおりである。

よくある誤り：

| 書き方 | 報告 |
|---|---|
| `Unit <- 'unit'`（値を持つ要素が 0 個） | `error: an alternative without an action must have exactly one element with a value, but it has none` |
| `Pair <- Num Num`（値を持つ要素が 2 個） | `error: an alternative without an action must have exactly one element with a value, but it has 2` |

一つめは `Unit <- 'unit' { () }` と書く。
二つめは、二つの値を束縛してアクションで組み立てる。

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
Name <- n:$[a-z]+ Sp { n }

Sp :: ()
Sp <- [ \t]* { () }

# 予約語：リテラルの後に識別子の文字が続かず、空白を読む
K<w> :: ()
K<w> <- w ![a-zA-Z0-9_] Sp { () }

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

雛形は、引数付き規則の引数（`Name(x :: Int)`）を取れない。
`%start`、`%entry`、`%recover`、`%nomemo`、`%token`、`%trivia`、`%inline` に雛形を書くこともできない。

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
Factor <- '(' e:Expr ')' { e }
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
Indent <- &{ _col >= w } { () }
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
Item <- ' '* c:Col(_col) 'a' { c }

# 何も読まず、受け取った桁を値として返す
Col(c :: Int) :: Int
Col <- { c }
```

`   a` を解析すると、`a` の直前の桁 `3` が値になる。

字下げの判定では、規則に渡す基準の桁を、文字の境界の `_col` ではなく「接頭辞が本来消費するはずだった桁」にする書き方がある。
CommonMark のように、コンテナの接頭辞がタブの途中までを消費する言語は、この書き方で表せる（[ADR 0018](adr/0018-tab-partial-consumption.md)）。

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

生成モジュールが公開するのは、入口と、`%export` に挙げた名前だけである。
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

Sp :: ()
Sp <- Ws? { () }

Ws :: ()
Ws <- [ \t]+ { () }
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
漢字のように大文字と小文字の区別のない文字で始まる規則名は、`%syntax` の文法では Haskell の型名にならず、GHC のエラーになる。

束縛の名前の変更は、生成モジュールの公開 API の変更になる。
取り出し関数の名前が verbatim ブロックの名前と重なると、GHC のエラーになる。
取り出し関数は、`%trivia` の種類のトークンを読み飛ばす。

このほか、規則ごとの種類の定数（`syntaxKindExpr` など）、種類の名前を返す `nameOfSyntaxKind`、トリビアの種類かどうかを返す `isTriviaSyntaxKind` が生成される。
構文木の移動と表示の関数は peg-runtime の `Peg.Runtime.Syntax` にある。
`debugTree nameOfSyntaxKind` は、木を一要素一行の字下げで表した文字列にする。

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
Line <- is:Inline* { is }

Inline :: Inline
Inline <- '[' name:$[a-z]+ (']' ^close) { Command name }
        / w:$[a-z ]+ { Words w }

# 何も読まない。行の終わりで閉じたとみなす
CloseAtLineEnd :: ()
CloseAtLineEnd <- &('\n' / !.) { () }
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
入れ子のラベルでは、外側のラベルは内側の失敗をそのまま外へ伝えるものとして扱う。
そのため、警告が一つもない文法は、ラベルをすべて外した文法と同じ入力を受理する。
ほかのラベルが送出して止めるおかげで安全なラベルにも警告することがあるが、その代わりに保証が分かりやすくなる。
先読みの中の選択肢も検査し、失敗が先読みの境界に達したところで検査を終える。

検査は入力の次の一文字を基本に判定する近似であり、安全なラベルに警告することがある。
次の三つは、一文字より先まで見て判定する（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）。

- **規則の呼び出しを越えた共通の接頭辞**：失敗した選択肢がそれまでに読んだ要素と、後の選択肢が同じ要素で始まるなら、その部分を除いて比べる。後の選択肢の先頭の規則の呼び出しは、その規則の選択肢に展開して比べる。引数付き規則は、仮引数を実引数に置き換えたうえで、引数の字句が一致する呼び出しを同じものとみなす（`B(n) <- Bad(n) / Orphan(n)` の `Bad` と `Orphan` がどちらも `Ind(n)` で始まる場合など）
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

警告に従って直しても、文法が受理する入力と、誤りの位置は変わらない。
変わりうるのは、リテラルの接頭辞の警告に従って選択肢を消したときの、誤りの文言の「期待したもの」だけである。
`S <- '=' { () } / '==' 'x' { () }` の後ろの選択肢は決して成功しないが、入力が `=` で始まらないときは試されて失敗するので、空の入力の誤りは `1:1: expected '=' or '=='` になる。
後ろの選択肢を消すと、誤りは `1:1: expected '='` になる。
入力しても通らない字句が、誤りの案内から消えるということである（[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)）。

ラベルの安全性の検査は lint に含まれない。
安全なラベルにも警告しうる近似の検査なので、警告を止める手段のない lint には入れていない。
`peg-hs lint` が成功しても、ラベルの安全性は `peg-hs gen` の警告で別に確かめる。
`%safe` は lint の警告を止めない。
