# ADR 0062: エクスポートを選んだ生成モジュールの警告と、nameOfSyntaxKind の参照

ステータス: 採択（未実装）

## 文脈

[ADR 0061](0061-select-generated-exports.md) は、`peg-hs gen --export NAME` で生成モジュールのエクスポートを選び、選んだ名前からたどれる宣言だけを出力すると定めた。
実装したところ、[ADR 0061](0061-select-generated-exports.md) のとおりにはできない点が二つ見つかった。

### 規則を削ると、利用者の断片が使われなくなる

[ADR 0014](0014-generated-module-api.md) は、生成器が出力した部分は `-Wall` の下で警告を出さず、利用者が書いた断片の警告は利用者の責任とする、と定めている。
この区分は、生成器が利用者の断片をすべて出力することを前提にしていた。

`--export` で規則を削ると、その規則のアクション、意味述語、引数も出力されなくなる。
verbatim ブロックの import や補助の関数のうち、削った規則のアクションだけが使っていたものは、使われなくなる。
GHC は、それらを `-Wunused-imports` と `-Wunused-top-binds` で報告する。
verbatim ブロックはつねにすべて出力する（[ADR 0061](0061-select-generated-exports.md)）ので、生成器はこれを避けられない。
生成器は Haskell を解析しない（[ADR 0014](0014-generated-module-api.md)）ので、どの import や関数が使われなくなったかも分からない。

生成器が出力する `import Prelude` も、同じ理由で使われなくなることがある。
生成コードは Prelude を別名 `PegPrelude` で qualified に import するので、暗黙の Prelude の import は働かない。
そこで生成器は、利用者の断片のために、`import Prelude` を出力している（verbatim ブロックが Prelude を自分で import する場合と、`NoImplicitPrelude` の場合を除く）。
この import を使うのは、利用者の断片と一部の入口の定義である。
`%syntax` の名前だけを選ぶなど、どちらも出力しない場合は、生成器が出力した `import Prelude` が警告を受ける。
これは、[ADR 0014](0014-generated-module-api.md) の約束を生成器自身が破ることにあたる。

警告の原因は、利用者が書いた断片の誤りではなく、生成器が宣言を削ったことにある。
利用者は、`--export` を使わずに生成したモジュールでは警告を受けないのに、名前を選んだだけで警告を受ける。
[ADR 0061](0061-select-generated-exports.md) の実装は、入口を一つも出力しない二つのテストに限って、使われない import の警告を許すことで通した。
しかし、規則を一部だけ削る場合も、上の理由で警告は起こりうる。
テストの側で例外を設けるのではなく、生成物の側で決める必要がある。

### nameOfSyntaxKind は種類の定数を参照しない

[ADR 0061](0061-select-generated-exports.md) は、宣言をたどるときの参照として、「`nameOfSyntaxKind` はすべての種類の定数を参照する」と書いた。
実際の生成コードの `nameOfSyntaxKind` は、種類を数値で照合する（`PegRt.SyntaxKind 2 -> "Expr"`）。
種類の定数 `syntaxKind…` を参照しない。
[ADR 0061](0061-select-generated-exports.md) のとおりに定数を残すと、どこからも参照されない定数が残り、`-Wunused-top-binds` を受ける。
実装は、[ADR 0061](0061-select-generated-exports.md) の一般の規則（生成器が出力するコードに現れる参照をたどる）に従い、`nameOfSyntaxKind` から定数をたどらないようにした。

## 実装すること

### 削ったモジュールの警告の抑制

- `--export` を指定し、生成器が出力しない宣言が一つでもあるとき、生成モジュールの先頭に `{-# OPTIONS_GHC -Wno-unused-imports -Wno-unused-top-binds #-}` を出力する
- 出力しない宣言が一つもないとき（選んだ名前からすべての宣言をたどれるとき）と、`--export` を指定しないときは、出力しない。`--export` を指定しない生成物は、これまでとバイト単位で同じである
- 抑制するのは、使われない import とトップレベルの束縛の二つの警告だけとする。宣言を削ることで生じる警告は、この二つに限られる。ほかの警告（型の不一致を除く `-Wall` のすべて）は、これまでどおり利用者の断片の責任とする
- 生成器が出力する部分は、宣言をたどった結果として、抑制がなくても使われない束縛を持たない。抑制は、利用者の断片と `import Prelude` のためのものである

### 参照のたどり方の訂正

- `nameOfSyntaxKind` は、種類の定数を参照しない。`nameOfSyntaxKind` だけを選んだとき、種類の定数は出力しない
- `isTriviaSyntaxKind` など、ほかの名前の参照は、生成コードに現れる参照のとおりにたどる。[ADR 0061](0061-select-generated-exports.md) の一般の規則と同じである

### テスト

- [ADR 0061](0061-select-generated-exports.md) の実装で、入口を一つも出力しない二つの場合に設けた「使われない import の警告を許す」型検査をやめ、すべての場合を `-Wall -Werror` で型検査する
- アクションだけが使う import と補助の関数を verbatim ブロックに持つ文法で、その規則を削る `--export` を指定した生成物が、`-Wall -Werror` で通ること
- 出力しない宣言のない `--export` の指定（すべての入口と `%syntax` の名前を選ぶ）で、プラグマを出力しないこと
- `--export` を指定しない生成物が変わらないことは、既存の再生成のテストが確かめる

### 文書

- docs/syntax.md の「生成されるモジュール」と README の `--export` の説明に、宣言を削ったモジュールでは使われない import とトップレベルの束縛の警告を出さないこと、利用者の断片のそれらの誤りは `--export` を付けずに生成して確かめることを書く。docs/syntax.md の冒頭の「反映している ADR」にこの ADR を加える
- docs/specifications.md の生成するコードの節に、同じことをこの ADR へのリンクつきで書く
- [ADR 0061](0061-select-generated-exports.md) のステータスを「採択→削ったモジュールの警告と nameOfSyntaxKind の参照は ADR 0062」に、[ADR 0014](0014-generated-module-api.md) のステータスに、警告の例外が本 ADR にあることを加える

## 実装しないこと

- 生成器による Haskell の解析と、使われなくなった import や関数の削除。[ADR 0014](0014-generated-module-api.md) の方針のとおり、生成器は利用者の断片を解析しない
- 削った規則のアクションだけが使う verbatim ブロックの部分を、利用者が分けて書く仕組み
- `--export` を指定しない生成物への警告の抑制

## テスト設計

先に書き、いまの実装（[ADR 0061](0061-select-generated-exports.md) の pull request）で失敗させる。

- **警告のないこと**：[ADR 0061](0061-select-generated-exports.md) の型検査のすべての場合（入口を一つも出力しない二つの場合を含む）を、例外なく `-Wall -Werror` で型検査して通ること
- **規則の一部を削る場合**：アクションだけが使う `import Data.Char (isDigit)` と補助の関数 `digit` を持ち、二つの入口のうち一方だけがその規則を呼ぶ文法を用意する。もう一方の入口だけを `--export` で選んだ生成物が、`-Wall -Werror` で通ること
- **プラグマの有無**：宣言を削った生成物の先頭にプラグマがあり、削らなかった生成物（すべての名前を選んだ場合と `--export` なし）にプラグマがないこと
- **nameOfSyntaxKind**：`nameOfSyntaxKind` だけを選んだ生成物が、種類の定数を出力しないこと
- **既存の生成物**：`scripts/regen-fixtures.sh` を実行して、リポジトリのすべての生成物が変わらないこと

## トレードオフ

- 宣言を削ったモジュールでは、利用者の断片の本当に使われていない import や関数も報告されなくなる。`--export` を付けずに生成したモジュールでは、これまでどおり報告されるので、利用者の断片の誤りは、そちらで確かめられる。Golem のように同じ文法から `--export` なしでも生成する利用者は、そこで気付ける
- プラグマはモジュール全体に効くので、警告を抑える範囲を削った宣言に関わるものだけに絞ることはできない。GHC の警告の制御は、モジュールの単位か、警告の種類の単位でしかない
- 生成物の先頭の行が、`--export` の指定によって増える。生成物は文法とオプションから決まるので、決定性（[ADR 0002](0002-standalone-code-generator.md)）は保たれる
- 抑制せずに、利用者に verbatim ブロックを分けてもらう案もある。しかし、どの import がどの規則のアクションに使われるかは文法とオプションの組み合わせで変わり、利用者が追うのは難しい

## 参考文献

- GHC User's Guide, Warnings and sanity-checking, `-Wunused-imports`、`-Wunused-top-binds`. https://downloads.haskell.org/ghc/9.10.3/docs/users_guide/using-warnings.html
- GHC User's Guide, Command line options in source files（`OPTIONS_GHC` プラグマ）. https://downloads.haskell.org/ghc/9.10.3/docs/users_guide/using.html
