# ADR 0061: 生成モジュールのエクスポートを gen の --export で選ぶ

ステータス: 採択（未実装）

## 文脈

生成モジュールのエクスポート一覧は、文法だけで決まる（[ADR 0014](0014-generated-module-api.md)）。
生成器は、入口の `parse` と `%entry` の入口を必ず公開する。
`%syntax` があれば `parseSyntax`、種類の定数 `syntaxKind…`、`nameOfSyntaxKind`、`isTriviaSyntaxKind`、型付きのラッパー、`cast…Syntax`、取り出し関数も公開する（[ADR 0019](0019-lossless-syntax-tree.md)）。
ラベルがあれば `parseRecover` と、`%syntax` もあれば `parseSyntaxRecover` を公開する（[ADR 0021](0021-error-recovery.md)）。
最後に `%export` の名前を並べる。
一覧を組み立てるのは `Peg.Codegen` の `render` の `exports` で、利用者が一覧を狭める手段はない（[Codegen.hs の 210 行から 224 行](https://github.com/tett23/peg-hs/blob/c20439cf3651b65cdeebd1734a4a42afbbee33bc/packages/peg-codegen/src/Peg/Codegen.hs#L210-L224)）。

Golem は、エクスポートは使われていることで正当化される、という規則を採った。
Golem は peg-hs の c20439cf を固定し、[gen-parser.sh](https://github.com/tett23/golem/blob/312e1997b2fbf16e9330f453fe26da6086e2ee5b/scripts/gen-parser.sh) で同じ文法から二つのモジュールを生成している。
二つが公開する名前と、Golem が実際に使う名前は次のとおりである（Golem の 312e1997 を検索して数えた）。

| モジュール | 生成のしかた | 公開する名前 | Golem が使う名前 |
|---|---|---|---|
| `Golem.Parser.Generated` | `gen --Werror` | 244 | `parseSyntaxRecover`、`nameOfSyntaxKind` |
| `StrippedGrammar`（テスト用） | `gen --Werror --strip-labels StrippedGrammar` | 254 | `parse` |

`Golem.Parser.Generated` の 244 の内訳は、入口が 4、種類の定数が 112、ラッパーの型が 62、`cast…Syntax` が 62、その他が 4 である。
`StrippedGrammar` は、[ADR 0038](0038-label-check-precision-and-strip-labels-entries.md) が回復の規則を `%entry` に加えるので、`parseSkipBlock` などの入口が 10 個増える。
生成物は gen-parser.sh が上書きするので、手で一覧を削ることもできない。

では、エクスポートを減らすだけで足りるだろうか。
足りない。
一覧から外した入口は、定義だけが残る。
GHC 9.14.1 で確かめたところ、`-Wall` の `-Wunused-top-binds` は、エクスポートから参照をたどれないトップレベルの束縛を、`peg'` で始まる名前も含めてすべて報告した。
入口を外すと、その入口の定義と、その入口からしか呼ばれない規則が警告を受ける。
`StrippedGrammar` で `parse` だけを残すと、回復の規則（`SkipBlock` など）はどの入口からも呼ばれなくなる。
[ADR 0014](0014-generated-module-api.md) は、生成器が出力した部分は `-Wall` の下で警告を出さないと定めている。
エクスポートを選ぶ仕組みは、使われなくなった宣言を出力しないところまで含めないと、この約束を破る。

## 実装すること

### --export の仕組みを CLI のオプションにする理由

選ぶ手段の候補は三つあった。

- **CLI のオプション**：`peg-hs gen --export NAME`
- **文法のディレクティブ**：`.hpeg` に書く
- **設定ファイル**：エクスポートの一覧を別のファイルに書く

ディレクティブは、Golem の使い方を表せない。
Golem は一つの文法から、`parseSyntaxRecover` を公開するモジュールと、`parse` を公開するラベルなしのモジュールを作る。
ディレクティブは両方に効くうえ、ラベルを外した文法には `parseSyntaxRecover` がない。
何をエクスポートするかは、文法ではなく生成の呼び出しごとに決まる。
設定ファイルは呼び出しごとに分けられるが、新しいファイルの書式と、その読み方と、パスの解決の規則が増える。
`gen` の呼び出しはすでにシェルスクリプトに書かれており、オプションを足せば足りる。

### CLI

- `peg-hs gen` に `--export NAME` を加える。一つの指定で一つの名前を選び、何度でも指定できる。`label --rule RULE`（[ADR 0054](0054-automatic-label-insertion.md)）と同じ形である
- `--export` を一つも指定しなければ、生成物は今と同じで、バイト単位で一致する
- `--export` を指定すると、生成器が定義する名前のうち、指定した名前だけを公開する
- 選べるのは、生成器が定義する公開の名前である。入口（`parse`、`parse名前`、`parseSyntax…`、`parseRecover…`、`parseSyntaxRecover…`）と、`%syntax` の名前（`nameOfSyntaxKind`、`isTriviaSyntaxKind`、`syntaxKind…`、ラッパーの型、`cast…Syntax`、取り出し関数）がこれにあたる
- ラッパーの型は、`(..)` を除いた型の名前で選ぶ（`--export ExprSyntax` で `ExprSyntax(..)` を公開する）。括弧はシェルで引用が要るためである
- `%export` の名前は、`--export` によらず常に公開する。作者が文法に書いた時点で公開を選んでいるからである
- `--debug-entry` の入口（`peg'parseWith` など）は、`--export` によらず `--debug-entry` に従う。生成器のテストのためのものなので、選ぶ対象にしない
- `--strip-labels` と併せると、ラベルを外した文法が定義する名前から選ぶ
- 同じ名前を二度指定しても誤りにしない。`--rule` と同じく、集合として扱う
- 公開する順序は、`--export` を指定した順序によらず、今の一覧の順序とする。オプションの順序を入れ替えても生成物は変わらない

Golem の gen-parser.sh は、次のように書けるようになる。

```sh
"$PEG" gen modules/golem-parser/grammar/Golem.hpeg --Werror \
  --export parseSyntaxRecover --export nameOfSyntaxKind \
  -o modules/golem-parser/src/Golem/Parser/Generated.hs
"$PEG" gen modules/golem-parser/grammar/Golem.hpeg --Werror --strip-labels StrippedGrammar \
  --export parse -o modules/golem-parser/test/StrippedGrammar.hs
```

### 存在しない名前

生成器が定義しない名前を指定したら、生成せずに失敗する。

- 文言は `the generator does not define NAME` とし、位置は文法の 1 行 1 桁とする。表示は `Grammar.hpeg:1:1: error: the generator does not define parseRecover` となる。文法にない規則を `label --rule` に指定したときの `undefined rule R`（1 行 1 桁）と同じ扱いである
- 終了状態は 1 とし、モジュールを書かない。名前が正しいかは文法によって決まるので、使い方の誤り（2）ではなく文法の誤りと同じ扱いにする
- 存在しない名前が複数あれば、指定した順に、名前ごとに一つずつ報告する
- ラベルのない文法の `parseRecover`、`%syntax` のない文法の `parseSyntax`、`%export` に書いた名前、`(..)` 付きで書いた型の名前は、いずれもこの誤りになる。似た名前の候補は示さない

### 宣言の出力

生成器は、公開する名前から参照をたどれる宣言だけを出力する。

- 根は、公開する入口と `%syntax` の名前と `--debug-entry` の入口である
- 参照は、生成器が出力するコードに現れる参照である。入口は規則と `peg'config` と `peg'newStore` を、規則は呼ぶ規則と、ラベルの回復の規則と、`%syntax` では自分の種類の定数を参照する。取り出し関数は、ラッパーの型と種類の定数と、`Elements` の取り出しでは `isTriviaSyntaxKind` を参照する。`nameOfSyntaxKind` はすべての種類の定数を、`isTriviaSyntaxKind` は `%trivia` の種類の定数を参照する
- 出力しない規則は、メモ表のレコード `Peg'Store` の欄からも除く
- verbatim ブロックは常にすべて出力する。生成器は Haskell を解析しない（[ADR 0014](0014-generated-module-api.md)）ので、verbatim ブロックやアクションが生成器の名前を参照していても、それを根に加えない。参照された名前を出力しなかった場合は、GHC が `Variable not in scope` で失敗する。利用者はその名前を `--export` に加える
- `--export` がないときは、すべての名前が根になる。今の生成物では、すべての規則が開始規則、`%entry`、`%recover` のどれかから到達でき（[ADR 0014](0014-generated-module-api.md) の静的検査）、すべての種類の定数を公開しているので、除かれる宣言はない

### ライブラリ

- `Peg.Codegen` の `Options` に `optExports :: Maybe [Text]` を加える。`Nothing` が今の挙動で、`defaultOptions` は `Nothing` とする
- 存在しない名前の誤りは `generate` が `Left [Diagnostic]` で返す。CLI はそれを表示するだけにする
- `Options` を作っているすべての箇所（peg-cli の `gen` と `parse`、peg-lsp、テスト）に欄を加える。peg-hs は Hackage に公開していないので（[ADR 0058](0058-no-hackage-candidates-for-pre-releases.md)）、欄を加えても PVP の上の互換の問題は生じない

### 文書

- README（日本語と英語）の `gen` の節に `--export` を書き、生成したモジュールが公開する名前の一覧の後に、`--export` で狭められることを一文加える
- docs/specifications.md の「生成するコード」に、`--export` で公開する名前を選べること、選ばなかった名前に関わる宣言は出力しないことを、この ADR へのリンクつきで書く
- docs/syntax.md の「生成されるモジュール」の「生成モジュールが公開するのは、入口と、`%export` に挙げた名前だけである」の後に、`gen --export` で入口と `%syntax` の名前を狭められることを一文加え、冒頭の「反映している ADR」にこの ADR を加える
- `peg-hs help gen` に `--export NAME` の説明と、例を一つ加える
- `Peg.Codegen` のモジュールの Haddock と `optExports` の Haddock を英語で書く
- peg-codegen と peg-cli の `CHANGELOG.md` の 0.1.0.0 の Added に加える
- [ADR 0014](0014-generated-module-api.md) のステータスを「採択→エクスポートの選択は ADR 0061」に変える

### リリース

この ADR のためのリリースは要らない。
Golem は peg-hs をコミットで固定している（`cabal.project` の `source-repository-package` の `tag`）。
この ADR の実装がマージされたら、Golem はそのマージのコミットに `tag` を上げ、gen-parser.sh に `--export` を加えて生成し直す。
Golem の側の変更は Golem のリポジトリで行い、この ADR には含めない。
`v0.1.0-rc3` や `v0.1.0` に含めるかは、リリースの時に決める。

## 実装しないこと

- 文法のディレクティブや設定ファイルでの指定
- エクスポートから名前を除く指定（`--no-export NAME` のような否定の形）。肯定の形だけにすると、生成物に何が出るかが指定から一意に読める
- 名前のパターンやグループでの指定（`--export 'syntaxKind*'` など）
- `%export` の名前の選択と、verbatim ブロックの宣言の削除
- 存在しない名前の候補の提示
- Golem の gen-parser.sh と `cabal.project` の変更
- リポジトリ内の生成物（自己記述のパーサー、言語サーバーの JSON パーサー、適合性テストのパーサー）への `--export` の適用

## テスト設計

先に書き、今の実装で失敗させる。

### エクスポート一覧の golden（peg-codegen）

`optExports` を与えて生成し、モジュールの見出しのエクスポート一覧（`module` の行から `) where` の行まで）を `test/golden/exports/` の golden と比べる。

- **Golem と同じ形**：`Recover.hpeg`（`%syntax`、ラベル、`%export Block(..), Inline(..)` を持つ）を `parseSyntaxRecover` と `nameOfSyntaxKind` で生成すると、一覧はこの二つと `%export` の二つだけである
- **順序**：同じ二つを逆の順で与えても、生成物がバイト単位で一致する
- **重複**：同じ名前を二度与えても、生成物が一度与えたときと一致する
- **ラベルを外した文法**：`RecoverShared.hpeg` を `stripLabelsAs` してから `parse` だけで生成すると、一覧は `parse` だけで、回復の規則の入口も規則の宣言も出力しない
- **`%entry` だけ**：`RunsSyntax.hpeg` を `parsePlainDoc` だけで生成すると、開始規則からしか呼ばれない規則の宣言を出力しない
- **入口なし**：`Syntax.hpeg` を `nameOfSyntaxKind` だけで生成すると、規則、`peg'config`、`Peg'Store` を出力しない
- **ラッパーの型**：`ExprSyntax` のように型の名前を与えると、`ExprSyntax(..)` を公開する
- **`--debug-entry`**：`optDebugEntry` と併せると、`peg'parseWith` などが選んだ名前とともに公開される
- **既定**：`optExports = Nothing` の生成物が今と一致することは、既存の「committed fixtures are up to date」が確かめる

### 警告のないこと

上の各場合の生成物を、既存の `typecheck` と同じ方法で `-Wall -Werror` を付けて GHC で型検査し、警告なく通ること。
`%env` の文法（`Link.hpeg`）と `%nomemo` の文法（`NoMemo.hpeg`）を `--export parse` で生成した場合と、`%entry` を持つ `%syntax` のない文法（`Arith.hpeg`）を `parseTerm` だけで生成した場合も加える。

### 振る舞いが変わらないこと

`Recover.hpeg` を `parseSyntaxRecover` と `nameOfSyntaxKind` だけで生成したモジュールを `Fixture.RecoverExports` としてコミットし、scripts/regen-fixtures.sh で生成し直す対象に加える。
無作為な入力で、`Fixture.Recover.parseSyntaxRecover` と同じ構文木と誤りを返すこと（プロパティテスト）。
コミットした生成物が最新であることは、既存の再生成のテストに加えて確かめる。

### 誤り（peg-codegen）

- ラベルのない文法で `parseRecover` を与えると、`Diagnostic (Loc 1 1) "the generator does not define parseRecover"` が返ること
- `%export` に書いた名前、`(..)` を付けた型の名前、`%syntax` のない文法の `parseSyntax` が、同じ誤りになること
- 存在しない名前を二つ与えると、与えた順に二つの誤りが返ること

### CLI（peg-cli）

- `gen --export parse --export parseSyntax` が、二つの入口だけを公開するモジュールを書き、終了状態が 0 であること
- 存在しない名前を与えると、終了状態が 1 で、標準エラーに `GRAMMAR.hpeg:1:1: error: the generator does not define NAME` を出し、出力のファイルを書かないこと
- `--strip-labels` と併せると、ラベルを外した文法の名前から選ぶこと（`--export parseRecover` が誤りになる）
- `peg-hs help gen` に `--export` が載ること

## トレードオフ

- 宣言を削る処理が生成器に加わる。生成器はこれまで、文法の規則をすべてそのまま出力していた。参照のたどり方を誤ると、必要な宣言を落としてコンパイルできないか、不要な宣言が残って警告を受ける。どちらも上の型検査のテストで表に出る。黙って振る舞いが変わる誤りは、振る舞いの比較のテストで確かめる
- `--export` を使う利用者は、使う名前を一つずつ書く。244 の名前から 2 つを選ぶ Golem には合うが、ほとんどの名前を使う利用者には、否定の形のほうが短く書ける。否定の形は、生成物に何が出るかを読むのに文法の全体が要るので採らない
- verbatim ブロックが生成器の名前を参照すると、`--export` に加えるまでコンパイルできない。生成器は Haskell を解析しない方針なので、参照を自動で見つけることはしない。誤りは GHC のコンパイルの誤りとして現れ、黙って誤動作することはない
- 存在しない名前の誤りの位置は、文法の中に対応する場所がないので 1 行 1 桁とする。`label --rule` の前例に合わせたが、位置としての意味はない
- エクスポートを選んだモジュールは、別の利用者が別の名前を使いたくなったとき、生成し直しが要る。生成物は文法とオプションから決まるので、gen の呼び出しを変えれば足りる

## 参考文献

- [Golem の scripts/gen-parser.sh](https://github.com/tett23/golem/blob/312e1997b2fbf16e9330f453fe26da6086e2ee5b/scripts/gen-parser.sh)
- [Golem の modules/golem-parser/src/Golem/Parser.hs](https://github.com/tett23/golem/blob/312e1997b2fbf16e9330f453fe26da6086e2ee5b/modules/golem-parser/src/Golem/Parser.hs)（`G.parseSyntaxRecover` だけを使う）
- [Golem の modules/golem-parser/src/Golem/Parser/Convert.hs](https://github.com/tett23/golem/blob/312e1997b2fbf16e9330f453fe26da6086e2ee5b/modules/golem-parser/src/Golem/Parser/Convert.hs)（`nameOfSyntaxKind` だけを import する）
- [Golem の modules/golem-parser/test/LabelSafetySpec.hs](https://github.com/tett23/golem/blob/312e1997b2fbf16e9330f453fe26da6086e2ee5b/modules/golem-parser/test/LabelSafetySpec.hs)（`Stripped.parse` だけを使う）
- [peg-hs c20439cf の packages/peg-codegen/src/Peg/Codegen.hs](https://github.com/tett23/peg-hs/blob/c20439cf3651b65cdeebd1734a4a42afbbee33bc/packages/peg-codegen/src/Peg/Codegen.hs)
- GHC User's Guide, Warnings and sanity-checking, `-Wunused-top-binds`. https://downloads.haskell.org/ghc/9.10.3/docs/users_guide/using-warnings.html
- Hickey, R. 2011. Simple Made Easy. Strange Loop 2011. https://www.infoq.com/presentations/Simple-Made-Easy/
