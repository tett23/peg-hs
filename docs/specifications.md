# peg-hs 仕様書

peg-hs は、PEG（Parsing Expression Grammar）の定義から Haskell のパーサーを生成するツールチェーンである。
標準的な PEG の全構文に加えて左再帰を受理し、文法定義ファイルから Haskell ソースコードを生成する。
最初の利用者は組版システム Golem だが、peg-hs 自体は Golem に依存しない汎用ライブラリとして開発する。

この文書は、peg-hs の能力、配布の形、意図的に採用しなかったもの、設計原則、モジュール構成、開発順序を定める。
実装の詳細は書かず、それを定めた ADR（Architecture Decision Record、設計の決定の記録）へのリンクで示す。
ADR は `docs/adr/` に連番で置く。
コミットした ADR は、ステータスの行の変更とリンクだけの変更を除いて変更しない。
性能の判断の根拠にした計測の記録は `docs/benchmarks/` に置き、これもコミットした後は変更しない。
この二つの決まりは [adr-guard](https://github.com/tett23/adr-guard) v0.10.0 が pre-commit のフックと CI で検査する（[ADR 0043](adr/0043-adr-guard-v0.8.0.md)、[ADR 0047](adr/0047-adr-guard-v0.8.1.md)、[ADR 0059](adr/0059-adr-guard-v0.8.2.md)、[ADR 0060](adr/0060-adr-guard-v0.8.3.md)、[ADR 0076](adr/0076-adr-guard-v0.10.0.md)）。
プルリクエストは、main の必須のチェック（`adr` と `ci`）が通ると自動でマージする。
`ci` は CI のジョブの結果をまとめるジョブで、文書（`docs/` の下と `.md` のファイル）だけの変更では、ほかのジョブを飛ばして成功する（[ADR 0072](adr/0072-required-checks-for-auto-merge.md)）。

## 目的

PEG は、文法を「入力をどう読むか」の手順として書く形式である。
選択肢を書いた順に試し、最初に成功したものを採る（順序付き選択）ので、文法が曖昧になることがなく、小さな文法を組み合わせて大きな文法を作れる。
一方で、規則が自分自身の呼び出しから始まる形（**左再帰**）は、素朴な実装では無限再帰に陥る。
左結合の演算子や左結合の後置構文（メソッド呼び出し、添字、フィールド参照）は左再帰で書くのが自然であり、この制限は文法を書く側に不自然な書き換えと結果の再結合を強いてきた。
peg-hs は左再帰を意味論のレベルでサポートし、文法を自然な形のまま書けるようにする。

パーサーは実行時にコンビネータで組み立てるのではなく、文法定義ファイルからソースコードとして生成する。
生成されたコードはリポジトリにコミットでき、レビューと版管理の対象になる。
生成したパーサーが依存するのは実行時ライブラリ peg-runtime だけなので、利用者のプロジェクトは peg-hs の生成器そのものに依存しない。

パッケージは Hackage で公開し、ライセンスは MIT とする（[ADR 0009](adr/0009-hackage-publication.md)）。
公開の形と版の付け方は「配布と版」の節に定める。

## 能力

### 受理する文法

Ford が定義した標準 PEG の全構文を受理する。

- 逐次、順序付き選択 `/`
- 繰り返し `*` `+`、省略 `?`
- 先読み述語 `&` `!`
- 任意の一文字 `.`、リテラル、文字クラス
- 直接と間接の左再帰を含む規則

左再帰の意味論は Medeiros らの bounded left recursion に従う（[ADR 0001](adr/0001-bounded-left-recursion.md)）。
この意味論では、左再帰の規則を「一回だけ展開した結果」から始め、展開の回数を増やしながら、より長く読めなくなるまで結果を育てる。
`E <- E '+' n / n` のような直接左再帰は左結合の構文木を生じ、複数の規則にまたがる間接左再帰も同じ意味論で扱う。
nullable な式（空文字列を受理しうる式）を前置した左再帰（隠れ左再帰）も同じ意味論の下で動作することを目標とし、テストで確認する。
左再帰の規則が何段入れ子になっても、評価の回数は段の数と入力の長さに比例する範囲に収まる（[ADR 0024](adr/0024-discard-seed-dependents-only.md)）。
回復するモードでは、`%recover l R` を持つ `e ^l` は `e` が失敗した位置で `R` を試すので、`e / R` のように振る舞う。
左再帰に関与する規則の判定は、この `R` への呼び出しも左端の呼び出しに数え、回復の規則を経由して同じ位置に戻る規則も左再帰の規則とする（[ADR 0095](adr/0095-left-recursion-through-recovery-rules.md)）。
これにより、回復するモードの解析は同じ位置に戻っても終わる。
引数付き規則と `%nomemo` の規則に対する制約も、こうして数えた規則に及ぶ。

文法の式の入れ子の深さは 256 段までとする。
群の括弧、前置と後置の演算子（`&`、`!`、`$`、`*`、`+`、`?`）、ラベル（`^`）、雛形の呼び出しの引数が、それぞれ一段ずつ数える。
上限を超えた文法は、超えた段の位置で `the expression nests deeper than 256` の誤りになる。
記法のパーサーは上限を超える段に入る手前で止まるので、深い入れ子を拒むまでの時間は入力の長さに比例する範囲に収まる。
`gen`、`fmt`、`lint`、`parse`、言語サーバー、wasm のどれも、この上限で文法を拒む。
上限は変えられない（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）。

標準 PEG の外側の拡張として、次の四つを受理する（[ADR 0012](adr/0012-context-sensitive-extensions.md)）。
CommonMark のように、字下げの幅や開いた括弧の数といった文脈で読み方が変わる言語を書くためのものである。
どれも「規則の結果は、規則、引数、位置の組と、解析環境だけの関数である」という不変条件を保つ。
この不変条件があるので、同じ規則を同じ位置で評価した結果を覚えて使い回す仕組み（**メモ化**）と、左再帰の結果を育てる仕組みの前提が壊れない。

- **意味述語** `&{ 式 }` `!{ 式 }`：左にある束縛などを参照する純粋な真偽式
- **引数付き規則** `Name(式)`：値の引数を取る規則。引数が違えば別の結果として覚える。左再帰への関与は禁止
- **解析環境** `%env 型`：解析全体で不変な値を入口から渡し、`_env` で参照する
- **桁の参照** `_col`：評価位置の桁。`%tabstop N` でタブの幅を指定する。タブの一部だけを字下げとして読む場合も扱う（[ADR 0018](adr/0018-tab-partial-consumption.md)）

記法の利便のために、次の三つを持つ。

- **単位の値**：アクションを省略した選択肢は、値を持つ要素がちょうど一つならその値を返す。このとき、束縛していない `()` の値は数えない（[ADR 0030](adr/0030-unit-values-are-not-counted.md)）
- **使われない値**：テキストキャプチャ `$e` の中、先読みの中、アクションを書いた選択肢の束縛していない要素のように、値が使われない位置の式は、値の型が選択肢の間で食い違っていても誤りにしない（[ADR 0026](adr/0026-discard-unused-values.md)）
- **規則の雛形** `Name<式, ...>`：規則や式を引数に取る規則。引数の組ごとに普通の規則へ生成時に展開するので、展開した規則にもメモ化と左再帰の意味論がそのまま効く（[ADR 0031](adr/0031-rule-templates.md)）。雛形の引数は呼び出し元の引数を使え、雛形は値の引数（`Name<p>(n :: Int)`）も持てる。展開した規則は、それらを引数に持つ引数付き規則になる（[ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)）

規則名と束縛名には Unicode の英字と数字を使える（[ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)）。

### 生成するコード

生成器は文法定義ファイル（`.hpeg`）を読み、単一の Haskell モジュールを出力する。

- 各規則はユーザーが指定した結果型を持ち、パーサーは中間表現を経由せず、利用者の定義した構文木の型（AST）の値を直接返す（[ADR 0003](adr/0003-typed-semantic-actions.md)）
- 生成コードは peg-runtime の上で動く薄いコードとし、メモ化と左再帰の機構は peg-runtime が担う
- 生成モジュールは、開始規則の入口 `parse :: Text -> Either ParseError a` を公開する。入口は入力の全体の消費を要求する。`%entry` で、ほかの規則にも入口を作れる。エクスポートの範囲、生成器の内部の名前と利用者の名前が衝突しない仕組み、位置の数え方は [ADR 0014](adr/0014-generated-module-api.md) に定める
- 入口は `Text` だけを受け取る。ファイルなどから読んだ UTF-8 のバイト列は、peg-runtime の `decodeInput :: ByteString -> Either Utf8Error Text` で `Text` に直してから入口に渡す。`decodeInput` は先頭の BOM を除き、UTF-8 として正しくない入力では最初の正しくない列の先頭の位置を `Utf8Error` で返す。この位置は、BOM を除いた後のバイトで `ParseError` の位置と同じく数える。`renderUtf8Error` は、それを `行:桁: invalid UTF-8` の一行にする（[ADR 0093](adr/0093-utf8-bytestring-input.md)）
- アクションに書いた Haskell の式が型の誤りを起こすと、GHC はそれを `.hpeg` ファイルの行と桁で報告する（[ADR 0014](adr/0014-generated-module-api.md)）
- 文法に埋め込んだ Haskell（verbatim ブロック、アクション、意味述語、`%env`）は、生成したモジュールをコンパイルして使うときに利用者の権限で動く。これが信頼境界である。埋め込みのブロックの外の値（`%module` の値、`%export` の項目、文法のファイルと出力のファイルの名前）も、生成したモジュールに入る。peg-hs はそれらを検査して、Haskell の宣言として読める値を拒む。`%module` の値は、ドットで区切った Haskell のモジュール名でなければならない。`%export` の項目は、エクスポートの一覧の項目の字句の形（修飾してもよい名前、型の名前に `(..)` か名前と括弧で囲んだ演算子の並びを続けたもの、括弧で囲んだ演算子、それらの前に `type` か `pattern` を付けたもの、`module` とモジュール名）のどれかでなければならない。どちらの誤りも値の位置で報告する。ファイルの名前が制御文字（U+0000 から U+001F と U+007F）を含むときは、1 行 1 桁の誤り `the file name contains a control character` とし、何も生成しない（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）
- `%language` で、生成モジュールの言語拡張を有効にできる。生成コードの意味を変える `RebindableSyntax` は拒否する（[ADR 0016](adr/0016-language-extensions.md)）
- `%nomemo` で、規則ごとにメモ化を外せる。左再帰に関与する規則には指定できない（[ADR 0006](adr/0006-memoization-control.md)、[ADR 0017](adr/0017-nomemo-implementation.md)）
- `--strip-labels MODULE` で指定する生成先にも `%module` と同じモジュール名の字句規則を適用する。不正な名前を渡すと生成を拒否する（[ADR 0097](adr/0097-verify-hpeg-and-generated-haskell-in-lean.md)）。
- `peg-hs gen --export NAME` で、入口と `%syntax` の名前のうち公開するものを選べる。`%export` の名前は常に公開する。選ばなかった名前からしか参照されない宣言（規則、メモ表の欄、種類の定数など）は出力しない。生成器が定義しない名前は誤りとする（[ADR 0061](adr/0061-select-generated-exports.md)）
- `--export` で宣言を削った生成モジュールは、使われない import とトップレベルの束縛の警告を出さない。削った規則のアクションだけが使っていた verbatim ブロックの部分が使われなくなり、生成器は Haskell を解析しないので、どれがそうかを知れないためである（[ADR 0062](adr/0062-warnings-of-pruned-generated-modules.md)）
- `%syntax` の文法では、型注釈のない規則の、アクションを省略した選択肢の値は、要素の値によらず `()` になる。要素は値を捨てて生成し、束縛した要素は意味述語と引数のためにこれまでどおり束縛する。`%syntax` のない文法と、型注釈（`:: ()` を含む）のある規則は、この規則の対象にならない（[ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)）
- `%syntax` のない文法で、型注釈がなく、どの選択肢もアクションを持たない規則は、選択肢の値から型を決める。どの選択肢も `()` 以外の値を持たなければ `()`、どの選択肢も `()` 以外の値をちょうど一つ持ち、型がすべて同じならその型（推論）、それ以外は規則ごとに生成した代数的データ型である。規則が互いを呼ぶので、`()` かどうかの不動点と、推論した型の不動点の二段で決める。型は空白を除いた文字列で比べ、別名は別の型とみなす。比べられなければ生成する側に倒すので、分類で生成モジュールの型が合わなくなることはない。生成する型の名前は規則名の先頭を大文字にしたもの（大文字のない規則名には `Rule'` を付ける）で、選択肢ごとに構築子を持ち、構築子の引数は選択肢の `()` 以外の値を現れる順に並べたものである。構築子の既定の名前は、選択肢が一つなら型の名前、二つ以上なら型の名前に選択肢の番号を付けたもので、選択肢の末尾の `@名前` で変えられる。構築子が一つで引数が一つの型は `newtype` にする。生成する型は既定で `Eq` と `Show` を導出し、`%deriving` で導出するクラスを変える。生成する型は構築子ごと公開し、`--export` で入口を絞ったときは、公開する入口の型から辿れる型だけを公開する。生成できていた文法の生成コードは、この規則で変わらない（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）

生成モジュールの先頭のコメントには、そのモジュールが要る peg-runtime の版の範囲を `peg-runtime >=0.1 && <0.2` の形で書く（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。
生成コードは、peg-runtime のうち生成コードのためだけにある内部向けのモジュール（`Peg.Runtime.Internal`）を使う。
このモジュールを変えると、古い生成物が新しい peg-runtime で動かなくなりうる。
そのため、範囲は互換が崩れるときにだけ上げ、このモジュールの変更は PVP の上でメジャーの変更として扱う。

生成器は、同じ文法と同じ引数からバイト単位で同じ出力を生成する。
ただし、生成モジュールは `peg-hs gen` に渡された文法と出力のパスを、渡されたとおりに記録する。
GHC の誤りの位置を `.hpeg` の行で示すためである。
そのため、絶対パスを渡すと機械ごとに出力が変わる。
生成モジュールをコンパイルするパッケージのディレクトリからの相対パスで渡せば、機械によらず同じ出力になり、エディタも誤りの位置を開ける（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

### ほかのファイルの規則の取り込み

文法は、ほかのファイルの規則を取り込める（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）。
規則を取り込まれるファイルを**ライブラリ**と呼ぶ。
ライブラリは、引数のない `%library` を書いた `.hpeg` ファイルで、`%library`、コメント、規則（型注釈、定義、雛形、引数付き規則）だけを持つ。
ほかの指示、verbatim ブロック、`%import` は、その位置の誤りとする。
`%module` を書いた文法（根の文法）は、`%import パス` を一行に一つ、何度でも書ける。

- **パス**：根の文法のディレクトリからの相対パスである。検索パスは持たない。`/` で区切った一つ以上の部分からなり、`/` で始まらず、各部分は空でない ASCII の英字、数字、`_`、`-`、`.` の並びで `.` と `..` ではなく、最後の部分は `.hpeg` で終わる。外れるものは `%import` の引数の位置の誤りとする。そのため取り込めるのは根の文法のディレクトリとその下のファイルだけで、パスを書いたとおりに比べれば同じファイルかどうかが決まる。パスのどの部分もシンボリックリンクであってはならず、リンクは辿らずに `cannot import P: it is a symbolic link` の誤りにする。読めないファイルは `cannot import P: no such file`、`%library` のないファイルは `P is not a library: it has no %library directive`、同じパスの二度目は `P is imported twice` の誤りにする
- **名前**：根の文法とライブラリの規則は一つの名前の集まりになり、修飾名も選んだ規則だけの取り込みも持たない。同じ名前の規則が二つのファイルにあれば、後に読んだほうの定義の位置で `duplicate definition` の誤りにする。読む順は根の文法、ライブラリを `%import` の順である。ライブラリの規則が呼べるのは同じライブラリの規則だけで、ほかは `undefined rule` の誤りにする。根の文法は取り込んだ規則と雛形を自分の規則と同じに呼べ、指示で名指しできる。根の文法から到達しないライブラリの規則は、誤りにせず、生成もしない
- **単独の検査**：ライブラリはそれだけで検査できる。その検査は、根の文法がないと決まらない検査（開始規則と到達、規則の値と型）をしない
- **生成**：出力は単一のモジュールで、規則を根の文法、ライブラリを `%import` の順に並べてから、これまでと同じ検査と生成にかける。モジュールについての決定（モジュール名、言語拡張、`%env`、`%syntax`、`%deriving`、`%export`、`%safe`、`%recover`）は根の文法だけが下し、ライブラリの Haskell の名前は根の文法のモジュールの中で解決される。ライブラリのアクションの `{-# LINE #-}` は、根の文法のパスのディレクトリに `%import` のパスを `/` でつないだパスを指す
- **位置**：誤りと警告は、それが起きたファイルで報告する。peg-grammar の位置 `Loc` は、行と桁に加えて、根の文法（`0`）か何番目の `%import` のライブラリかを持つ

ライブラリを `peg-hs gen` に渡すと、これまでどおり `missing %module directive` になる。

### ビルドの中での生成

コマンドで生成してコミットする代わりに、利用者の cabal パッケージのビルドの中で文法からモジュールを生成することもできる（[ADR 0085](adr/0085-generate-modules-in-the-build-with-setup-hooks.md)）。
パッケージ peg-hooks の `Peg.Hooks` は、`build-type: Hooks`（Cabal 3.14 からの SetupHooks）のためのフック `pegSetupHooks :: [Grammar] -> SetupHooks` を出す。
`Grammar` は、文法のファイルのパス（パッケージの根からの相対パス）と、生成するモジュールの名前の組である。
利用者は、この値を自分の `SetupHooks.hs` の `setupHooks` にする。
ほかのフックとは `<>` でつなぐ。

フックは、文法のそれぞれについて、ビルドの前の規則（pre-build rule）を一つ登録する。
規則は、文法のファイルと文法が取り込むライブラリのファイルを入力とし、コンポーネントの autogen のディレクトリのモジュールを出力とする（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）。
規則は文法を読み、`peg-hs gen` と同じ検査をしてモジュールを書く。
`peg-hs gen` と規則は、peg-codegen の同じ公開の関数（`generateWithWarnings`）を使う。
モジュールの `{-# LINE #-}` は、文法を `Grammar` に書いたパスで指し、生成したモジュール自身をパッケージの根からの相対パスで指す。
誤りは `renderDiagnostic` の形で標準エラーに出し、ビルドを止める。
ラベルの警告は `peg-hs gen` と同じ形で出し、ビルドは続ける。
文法の `%module` が `Grammar` のモジュールの名前と違うときは、`%module` の位置の誤りとしてビルドを止める。
`--Werror`、`--strip-labels`、`--export`、`--debug-entry` に当たるものはない。
規則は、モジュールを `autogen-modules` に書いたコンポーネントにだけ登録する。
peg-hooks の版が変わると、cabal は setup スクリプトをビルドし直し、規則はモジュールを生成し直す。

文法のファイルと、文法が取り込むライブラリのファイルは `.cabal` の `extra-source-files` に書く。
書かないと、cabal は文法の変更を見ず、古いモジュールのままビルドする。
利用者は `cabal-version: 3.14` 以上と、Cabal 3.14 以上を setup の依存に使える cabal-install が要る。
GHC 9.10 に付属する Cabal は 3.12 なので、最初のビルドで Cabal をソースからビルドする。

生成モジュールは GHC 9.10、9.12、9.14 でコンパイルできる（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）。CI で確かめるのは ghcup の recommended の版（9.10）だけで、9.12 と 9.14 は v0.1.0-rc2 まで確かめた（[ADR 0057](adr/0057-recommended-ghc-only.md)）。

### ロスレスな構文木

`%syntax` を書いた文法では、型付きの値の入口に加えて、元の文字列を一文字も失わない構文木（**CST**、具象構文木）を返す入口を生成する（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。
規則の呼び出しがノードに、終端の一致がトークンになり、空白やコメントの規則も木に残る。
木を連結すると、元の入力に戻る。
木の各ノードから親と絶対位置をたどれ、束縛ごとに型の付いた取り出し関数が生成される。
lint や formatter のように、空白とコメントを扱う用途のためのものである。

構文木だけを使う文法は、`%syntax` を付けて型注釈もアクションも書かずに書ける。
型注釈のない規則の値は、キャプチャや型注釈のある規則の呼び出しを含んでも `()` になり、利用者は値を構文木から取り出す（[ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)）。
構文木を作る費用はこの書き方でも変わらないので、速さが要る文法は `%syntax` を付けずに型注釈とアクションを書く。

### 静的検査

生成器は文法を検査し、次の問題をコード生成前に報告する。

- 未定義の非終端の参照
- 開始規則から到達不能な規則
- nullable な式の繰り返し（`e*` で `e` が空文字列を受理する形。実行時の無限ループになるため拒否する）
- 同じ規則を二度挙げた `%entry`（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）
- コードから見えない束縛の参照。意味述語と規則の引数が右にある束縛（自分の束縛を含む）を参照する、括弧の内側の束縛（生成コードが束縛しない）を参照する、ほかの選択肢の束縛を参照する、の三つを、コードの中の名前の位置で報告する。コードの名前は字句の水準で読み、文字列、文字、コメント、修飾名、フィールドの選択の中の名前は参照と見なさない。規則の中で束縛していない名前は検査しない（[ADR 0082](adr/0082-static-check-of-binding-references.md)、[ADR 0083](adr/0083-bindings-inside-a-group-are-not-visible.md)）

ラベル（次の「構文エラーからの回復」の節）の位置が安全かも検査し、危険かもしれないラベルを警告する（[ADR 0028](adr/0028-label-safety-check.md)）。
ラベルが安全であるとは、ほかのラベルをすべて外した文法の上で、そのラベルを外しても受理する言語が変わらないことである（[ADR 0029](adr/0029-label-safety-implementation-deviations.md)）。
検査は、ほかのラベルを外した文法の上で各ラベルを判定するので、ほかのラベルの有無で判定は変わらない（[ADR 0087](adr/0087-other-labels-do-not-change-the-label-check.md)、[ADR 0088](adr/0088-correct-the-second-example-of-adr-0087.md)）。
すべてのラベルが安全なら、ラベルを付けた文法と外した文法は同じ言語を受理する。
検査は近似であり、安全と判定したラベルは安全だが、安全なラベルに警告することがある。
近似を詰めるために、規則の呼び出しを越えて共通の接頭辞を除いて比べ、`&{ False }` のような定数の意味述語を解釈し、先頭のリテラルが確定していれば二文字目以降も使って比べる（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）。
作者が確かめたラベルは `%safe` で警告を止める。

### エラー報告

失敗の表現はラベル付き失敗（labeled failures）の型を持つ。
失敗は、解析が最も先まで進んだ位置（最遠到達位置）と、その位置で期待していたもの（失敗した終端の集合、期待集合）を報告する（[ADR 0005](adr/0005-error-reporting.md)）。
位置情報はバイトオフセットと行と桁の両方を保持する（[ADR 0008](adr/0008-source-positions.md)）。
文法の作者は、`%expect` で規則に**表示名**（誤りの表示で規則を指す名詞句）を付けられる（[ADR 0089](adr/0089-rule-names-and-label-messages-in-errors.md)）。
表示名を持つ規則の中で最も遠い失敗が規則の始まりの位置にあれば、その位置の期待集合を表示名だけに置き換える。
規則がいくらか読んだ後の失敗は置き換えない。
表示名は期待集合の中で終端より先に並び、受理する言語と最遠到達位置を変えない。
`renderParseError` は、失敗を `行:桁: expected A, B or C` の形の文に直す（[ADR 0014](adr/0014-generated-module-api.md)）。
失敗を止めたラベルに `%message` の**文言**があれば、`行:桁: 文言` の形にする（[ADR 0089](adr/0089-rule-names-and-label-messages-in-errors.md)）。

### 構文エラーからの回復

文法の作者は、そこで失敗したら構文エラーである位置に `e ^label` を書き（**ラベル**）、ラベルごとに回復の規則を `%recover` で与える（[ADR 0021](adr/0021-error-recovery.md)）。
送出されたラベルは順序付き選択の後戻りを止める。
回復するモードの入口は、回復の規則で入力を同期の位置まで読み飛ばして解析を続け、構文エラーの列を返す。
`%syntax` の文法では、回復した範囲を誤りのノードとして含む構文木を、どの入力に対しても返す。
構文木のロスレス性は、エラーを含む入力でも成り立つ。
回復しないモードの入口は、最初の失敗で停止し、送出されたラベルとその文言を失敗に含める。
回復した構文エラーも、ラベルの文言を持つ。
ラベルを付けた式の値が使われない位置では、回復の規則の値も、ラベルを付けた式の値も捨てる。
そのため、二つの値の型が違っても、生成したパーサーはコンパイルできる（[ADR 0021](adr/0021-error-recovery.md)、[ADR 0026](adr/0026-discard-unused-values.md)、[ADR 0094](adr/0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md)）。
`renderSyntaxError` は、構文エラーを `renderParseError` と同じ形の文に直す（[ADR 0089](adr/0089-rule-names-and-label-messages-in-errors.md)）。

### GHC を使わない解析

文法を解釈して入力を解析するインタプリタを、peg-grammar の `Peg.Grammar.Interpret` に持つ（[ADR 0090](adr/0090-grammar-interpreter-without-ghc.md)）。
インタプリタは GHC を呼ばない。
規則のパーサーを、生成コードと同じ peg-runtime の関数で実行時に組み立て、同じ実行の関数で走らせる。
左再帰、メモ化、ラベル、回復、期待集合は生成コードと同じ実装を通るので、解釈できる文法では、拒否のときの `ParseError` と受理のときの構文木が、生成したパーサーのものと一致する。
`%syntax` のない文法も、`%syntax` を加えた文法として構文木を作る。
回復するモードの木と `SyntaxError` の列も返す。
規則を包むメモ化の関数の選択と、構文木の子に束縛の名前を付ける要素の選択は、peg-grammar の関数を生成器と共有する。

アクションの値（AST）は返さない。
アクションと verbatim ブロックは Haskell のコードなので読まない。
意味述語と規則の引数も Haskell の式だが、次の形のものだけを評価する。

- 述語：`True`、`False`、または `項 比較 項`。比較は `==`、`/=`、`<`、`<=`、`>`、`>=` のどれか
- 項：`原子`、`原子 + 原子`、`原子 - 原子`
- 原子：10 進の非負の整数、規則の引数の名前、`_col`

引数の名前は、同じ名前の束縛が左に見えない位置でだけ引数を指す。
述語が読む引数と、その引数に渡す実引数をたどって、解析の結果に関わる引数を決める。
関わる引数の型は `Int` と書かれていなければならず、関わらない引数の実引数は評価しない。
この形の外の述語を含む文法と、関わる引数にこの形の外の実引数を渡す文法は、解釈できない述語と実引数をすべて位置つきで報告して受け付けない。
解釈できない述語を成功や失敗とみなすことはしない。
`_env` は原子に含まれないので、`%env` の文法は、述語と関わる引数が `_env` を読まないときに限り、環境の値なしで解釈する。

### 文法ファイルの道具

文法ファイルを書くための道具を、`peg-hs` のコマンドとエディタの支援として持つ。
コマンドは `peg-hs <command>` の形のサブコマンドであり（[ADR 0037](adr/0037-cli-subcommands.md)）、次の八つがある。

- **生成** `peg-hs gen`：文法から Haskell のモジュールを生成する（[ADR 0002](adr/0002-standalone-code-generator.md)）
- **整形** `peg-hs fmt`：空白と改行だけを書き換え、文法を一つに固定した流儀に揃える。流儀の議論をなくすため、設定と整形を止める指示は持たない。整形の前後で文法の意味が変わらないことを、整形の結果を解析し直して確かめる。`--check` は書き換えずに差の有無だけを調べる（[ADR 0032](adr/0032-grammar-formatter.md)）
- **lint** `peg-hs lint`：到達しない選択肢、効果のないラベル、使われない束縛のように、文法の意味から必ず問題だと言えるものだけを警告する。偽陽性がないので、利用者は規則を加えられず、警告を抑制できない。警告は文法を直せば消える（[ADR 0033](adr/0033-grammar-linter.md)）。警告に従って直しても、受理する入力と誤りの位置は変わらない。リテラルの接頭辞の警告に従って選択肢を消すと、決して成功しない字句が誤りの文言の期待したものから消える（[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)）。警告とは別に、直さなくても誤りではないが直せば簡潔になる書き方に info を出す。info は `--verbose` を付けたときだけ `info:` と書き分けて表示し、終了状態を変えない。規則は、型注釈が `()` の規則の省略できる `{ () }` を知らせる `omittable-unit-action` 、束縛した値をそのまま返すアクション（`e:Expr { e }`）を束縛ごと省けることを知らせる `omittable-identity-action`、省ける型注釈 `A :: ()` を知らせる `omittable-unit-annotation` である。`omittable-identity-action` は、構文木の取り出し関数を変えないよう、`%syntax` の文法には出さない。言語サーバーは info を重大度 Hint の診断として報告する（[ADR 0063](adr/0063-omit-unit-actions.md)、[ADR 0065](adr/0065-omittable-identity-actions.md)、[ADR 0066](adr/0066-omit-unit-type-annotations.md)、[ADR 0067](adr/0067-lint-info-with-verbose.md)）
- **ラベルの挿入** `peg-hs label`：ラベルの安全性の検査が安全と示せる位置を探し、そこに `^規則名_対象` の形のラベルを挿入する。候補は、逐次の中で必ず入力を読む要素より後にある要素であり、候補ごとに仮のラベルを置いて検査し、安全と判定したものだけを残す。挿入したラベルは受理する言語を変えない。残した候補のラベルをすべて置いた文法を `peg-hs gen` と同じ検査にかけ、警告された挿入のラベルを候補から外して、挿入のラベルが一つも警告されなくなるまで繰り返す。もとからあったラベルの警告はそのまま残す。そのため、挿入したラベルに `peg-hs gen` は警告しない。候補の判定も挿入した後の検査も、ほかのラベルを外した文法の上で行うので、この検査で外れるラベルはないはずである。検査は、判定の見落としに備えて残している（[ADR 0087](adr/0087-other-labels-do-not-change-the-label-check.md)）。言語サーバーのラベルの挿入も同じ結果になる（[ADR 0086](adr/0086-inserted-labels-pass-the-label-check.md)）。回復の規則を持つラベルの内側と、そこから呼ぶ規則には挿入しない。`peg-hs lint` が `duplicate-alternative` と警告する、同じ規則のほかの選択肢と同じ選択肢には、前のものにも後のものにも挿入しない。挿入すると重複への警告が消えるためである（[ADR 0094](adr/0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md)）。既定では一覧を書くだけで、`--write` でファイルを書き換える。回復の規則と `%recover` は書かない（[ADR 0054](adr/0054-automatic-label-insertion.md)）
- **解析の表示** `peg-hs parse`：文法で入力を解析し、AST（アクションの値）と CST を表示する。文法を書きながら、生成したパーサーが入力をどう読むかを確かめるためのものである。生成したパーサーを、`PATH` にある GHC（9.10 から 9.14）でコンパイルして実行する。`%env` を宣言した文法は、環境の値を渡せないので扱わない（[ADR 0036](adr/0036-parse-command.md)、[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）。コンパイルの作業ディレクトリは、一時ディレクトリの下に乱数の名前で、`mkdir` 一回で作る。POSIX では権限を作るときに 0700 とする。名前がすでにある場合（ディレクトリ、ファイル、リンクのどれでも）は、それを使わずに別の名前で作り直し、100 回作れなければ誤りで終わる。作業ディレクトリは、コンパイルの成否と例外によらず消す。コンパイルしたパーサーのキャッシュのディレクトリは、利用者のキャッシュのディレクトリの下にあり、所有者だけが書けることを前提とする。ほかの利用者が書けるキャッシュのディレクトリでは、置かれた実行ファイルを `parse` が実行してしまう（[ADR 0077](adr/0077-fixes-of-the-security-audit.md)）。`--interpret` を付けると、コンパイルせずに文法のインタプリタで解析し、CST を表示する。`ghc` を探さず、キャッシュのディレクトリも作らない。標準出力、標準エラー出力、終了状態は、同じ文法と入力での `--format cst` と一致する。`--format` の既定は `cst` で、`--format ast` と `--format all`、`--ghc-arg` は使い方の誤りとする。`--entry` は `%entry` の規則に限る。解釈できない文法は、インタプリタの誤りを位置つきで報告し、`--interpret` を外せばコンパイルして解析できることを添えて終了状態 1 で終わる。`%env` の文法は、インタプリタが解釈できるときだけ `--interpret` で扱う。文法が解釈できても、`--interpret` を付けなければインタプリタは使わない（[ADR 0090](adr/0090-grammar-interpreter-without-ghc.md)）。`gen`、`parse`、`test` は、文法が取り込むライブラリを読んで使う。コンパイルしたパーサーのキャッシュの鍵は、文法のテキストに加えて、ライブラリのパスとテキストを `%import` の順に含む（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）
- **例の試験** `peg-hs test`：文法の入力の例を解析して、結果を期待と比べる。文法の作者が、文法を直した後も前の入力を同じく受理するか、拒否するかを確かめるためのものである。`NAME.hpeg` の例は隣のディレクトリ `NAME.cases` に置き、一つの例を入力 `X.in` と期待 `X.cst` か `X.err` の二つのファイルとする。入力はエスケープも区切りもないそのままのバイト列で、終わりの改行も入力の一部とし、UTF-8 で読んで先頭のバイト順マークを読み飛ばす。`X.cst` は受理と `peg-hs parse --format cst` の形の構文木を、`X.err` は拒否と `renderParseError` の形の一行の誤りを期待する。空の `X.err` は拒否したことだけを確かめ、位置と期待した字句を比べない。期待のファイルの終わりの改行の有無は比べない。`NAME.cases/RULE` の例は `%entry` の規則 `RULE` で解析する。期待の両方がある入力、入力のない期待、`%entry` にない名前のディレクトリ、二段目のディレクトリは誤りとし、ほかの拡張子のファイルは無視する。例の置き場所を選ぶオプションは持たない。文法の選び方は `fmt` と `lint` と同じで、探して見つけた文法のうち `NAME.cases` のないものは飛ばし、名指しした文法に `NAME.cases` がなければ誤りとする。通った例は表示せず、通らない例を標準出力に書き、最後に `3 passed, 1 failed` の形で例の数を書く。通らない例か期待のない例があれば終了状態 1 で終わる。`--accept` は、比べる代わりに結果で期待のファイルを書き、もう一方の期待を消す。拒否した例の空の `X.err` は空のまま残し、結果と一致するファイルは書き直さない。例はインタプリタで GHC を使わずに解析し、インタプリタが扱えない文法は `peg-hs parse` と同じくコンパイルして解析する。どちらで解析するかは文法だけで決まり、`ghc` の有無で変えない。`%env` の文法は、インタプリタが扱える場合だけ試し、それ以外は誤りとする。AST と回復するモードの結果は比べない（[ADR 0091](adr/0091-grammar-test-command.md)）
- **ライブラリの扱い**：`peg-hs lint` は、根の文法を取り込みを解決した上で検査して根の文法の中の警告と info だけを報告し、ライブラリは単独で検査してその中の警告と info を報告する。ディレクトリを探索しても、ライブラリの警告は一度だけ出る。`peg-hs fmt` はファイルごとに整形し、取り込みを解決しない。`peg-hs label` は取り込みを解決した文法の上で候補を判定し、根の文法の規則にだけラベルを挿入して、ライブラリのファイルを書き換えない（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）
- **言語サーバー** `peg-hs lsp`：LSP（Language Server Protocol）の言語サーバーを標準入出力で起動する。診断、整形、semantic tokens、定義への移動、参照の検索、ホバー、文書の記号を提供する。コードアクションとして、`peg-hs label` と同じラベルを一つずつ、またはまとめて挿入する「ラベルを付ける」と、回復の規則を持たないラベルに `%recover` と回復の規則の雛形を加える「`%recover` を加える」を出す（[ADR 0054](adr/0054-automatic-label-insertion.md)）。型を生成する規則の `@名前` のない選択肢に、既定の構築子の名前を書き出すコードアクションも出す。ホバーは、型を推論する規則に推論した型を、型を生成する規則に生成した型の宣言を、`@名前` に構築子の型を示し、`()` は `()` の規則にだけ示す（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）。編集の途中の誤りを含む文書でも、回復した構文木をもとに働く（[ADR 0035](adr/0035-language-server.md)）。打鍵が検査より速く、変更の通知が続けて届いたときは、届いた通知をすべて読んでから、変更のあった文書ごとに最後の版だけを検査して診断を送る。途中の版の診断は送らない。メッセージは届いた順に処理し、要求にはその時点の最新の版で答える。同じ版の概要と診断は一度だけ計算する（[ADR 0070](adr/0070-faster-checks-in-the-language-server.md)）。文書の同期は変更の部分だけを受け取る形（`TextDocumentSyncKind.Incremental`）で、変更の範囲は言語サーバーの位置の単位（UTF-16 か UTF-8）で解釈する。版ごとの構文解析は、文書を最上位の要素の断片に区切り、前の版から変わっていない断片の結果を使い回す。結果は文書全体を一度に解析した結果と同じで、構文の誤りがある版の診断は全体の解析から求める。目安は、Golem の大きさの文法で、1 回の編集の診断と、編集の後の semantic tokens の要求がそれぞれ 16 ms 以内である（[ADR 0071](adr/0071-incremental-parsing-in-the-language-server.md)）。メッセージの大きさには上限がある。ヘッダーは、終わりの空行を含めて 64 KiB（65536 バイト）まで、本文（`Content-Length`）は 64 MiB（67108864 バイト）までとする。届ききらないメッセージのために溜めるバイト数は、この二つの和を超えない。ヘッダーの終わりが 64 KiB の中に見つからないとき、または `Content-Length` が 64 MiB を超えるとき、言語サーバーは標準エラー出力に理由を書き、終了状態 1 で終わる。次のメッセージがどこから始まるかがわからないので、読み飛ばして続けることはしない（[ADR 0077](adr/0077-fixes-of-the-security-audit.md)）。本文の JSON は、文字列の外の `[` と `{` の入れ子が 256 段を超えるとき、解析する前に線形の走査で拒み、JSON でない本文と同じく `-32700` の誤りで応えて次のメッセージに進む。入れ子の深さが上限を超える文法を開くと、その誤りを診断として返し、整形の要求には空の編集で応える（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）。言語サーバーが読むファイルは、`file://` の URI の文法が取り込むライブラリだけである。根の文法のディレクトリの下の、パスの字句の検査を通った `.hpeg` を、リンクを辿らずに読む。読むのは純粋な状態機械の外の入出力の部分で、開いている文書のライブラリはそのテキストを使い、ディスクから読まない。ほかの URI（`untitled:` など）の文法の `%import` は `imports need a file: save the grammar first` の誤りにする。根の文法の診断のうち位置がライブラリにあるものは、`%import` の行に `lex/Ident.hpeg:3:5: 文言` の形で出し、開いているライブラリには単独の検査の診断を出す。開いているライブラリが変わると、それを取り込む開いている文法も検査し直す。開いていないライブラリのディスクの上の変更は、文法を開き直すか編集するまで反映しない。取り込んだ規則の参照から、ライブラリの定義へ移動でき、ホバーは取り込んだ規則にも推論した型と生成した型を示す（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）
- **ヘルプ** `peg-hs help`：コマンドの一覧を、`peg-hs help COMMAND` でそのコマンドの説明を表示する

`fmt` と `lint` は、ファイルを指定しなければ、現在のディレクトリから再帰的にたどったすべての `.hpeg` ファイルを対象にする。
文法ファイルの拡張子は `.hpeg` である。以前の拡張子 `.peg` はほかの PEG の道具と重なるので探索では探さないが、ファイルを直接渡せば拡張子によらず扱う。エディタの言語の名前も `hpeg` とする（[ADR 0050](adr/0050-hpeg-extension.md)）。
名前が `.` で始まるディレクトリと `dist-newstyle` はたどらない（[ADR 0032](adr/0032-grammar-formatter.md)）。
探索は、ファイルへのものもディレクトリへのものも、シンボリックリンクをたどらずに黙って飛ばす。探索は始めたディレクトリの中だけを見て、循環するリンクがあっても終わる。引数で名指ししたファイルは、リンクでもリンクの先を読み書きする。名指ししたディレクトリは、リンクでもその先を探索の始まりとするが、その中のリンクはたどらない（[ADR 0077](adr/0077-fixes-of-the-security-audit.md)）。

すべてのコマンドは、次の約束に従う（[ADR 0037](adr/0037-cli-subcommands.md)、[ADR 0045](adr/0045-fixes-before-v0-1-0.md)、[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

- **出力の先**：結果は標準出力に、誤りと警告は標準エラー出力に書く。文法の誤りと警告は `ファイル:行:桁: error: 文言` の形で書く
- **終了状態**：成功は 0、検査で問題が見つかった場合（文法の誤り、lint の警告、`fmt --check` の差、`parse` の解析の失敗、`test` の通らない例、ファイルの読み書きの失敗）は 1、使い方の誤り（未知のコマンドとオプション、引数の不足）は 2 とする
- **文字コード**：文法、入力、生成モジュールのファイルは、ロケールによらず UTF-8 で読み書きする。先頭のバイト順マーク（BOM）は読み飛ばす。文法と生成モジュールはソースコードなので、文字コードを選ぶオプションは持たない
- **ファイルの誤り**：読めない、書けないファイルは、`peg-hs: cannot read FILE: no such file` のように、どのファイルの読み込みと書き込みのどちらが、なぜ失敗したかを一行で報告し、直し方の手がかりを添える。`fmt` と `lint` は、読めないファイルを報告して残りのファイルを続ける
- **オプション**：値を取るオプションは `--name value` と `--name=value` の両方の形を受け付ける
- **ヘルプと誤りの文言**：各コマンドのヘルプは、使い方、説明、オプション、例の順に書き、例を一つ以上含む。使い方の誤りには `peg-hs help COMMAND` の案内を添える。知らないコマンドが既知のコマンドに近い綴りなら、候補を示す

エディタでは、言語サーバー、lint、整形、シンタックスハイライトの四つがそろう。
整形の流儀は一つに固定しているので、保存のたびに整形するのを既定とする（[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）。
エディタの支援として、リポジトリの `editors/` に次のものを置く。

- **シンタックスハイライト**：TextMate と tree-sitter の文法。`%import` の引数はパスとして区別し、tree-sitter では `@string.special.path`、TextMate では `string.other.path.hpeg` とする（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）。アクションや verbatim ブロックの中の Haskell の断片は、Haskell の文法に任せて色を付ける（[ADR 0034](adr/0034-syntax-highlighting.md)）。tree-sitter の文法は、verbatim ブロックの中身を `peg-hs gen` と同じ境界で読む（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）。括弧、アクションと verbatim ブロックの区切り、束縛の `:`、雛形の引数の `,`、ラベルの `^` にも色を付け、指示の引数は、規則の名前、ラベル、モジュールの名前、言語拡張の名前を区別する。capture の名前は nvim-treesitter と Helix の慣用に合わせる（[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）。構築子の名前（`@名前`）と `%deriving` のクラスの名前も区別する。tree-sitter では構築子の名前を `@constructor`、クラスを `@type`、`@` を `@punctuation.special` とし、TextMate では VS Code の Haskell の文法の構築子とクラスの scope（`constant.other`、`storage.type`）に合わせる（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）
- **折り畳み、字下げ、名前の定義と参照**：tree-sitter の問い合わせ。型注釈と定義をまとめた規則、verbatim ブロック、複数行のアクションを畳み、続きの選択肢の行を定義の `<-` の桁に字下げする。規則の定義と参照、束縛を名前の定義と参照とする（[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）
- **semantic tokens**：言語サーバーが、規則、束縛、ラベルなどの種類を返す（[ADR 0035](adr/0035-language-server.md)）。指示の引数の規則の名前は `function`、ラベルは `decorator`、`%module` の引数は `namespace` とし、括弧や区切りには返さない（[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）。構築子の名前は `enumMember`、`%deriving` のクラスの名前は `type` とする（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）
- **VS Code の拡張機能**：TextMate の文法と言語サーバーの起動を含み、言語 `hpeg` の保存時の整形（`editor.formatOnSave`）を既定で有効にする。リポジトリから入れる（[ADR 0034](adr/0034-syntax-highlighting.md)、[ADR 0035](adr/0035-language-server.md)、[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）。vscode-languageclient が依存する minimatch は、既知の DoS を直した 11.0.1 以上に npm の `overrides` で上書きする。minimatch 11 が削った `makeRe()` は、言語サーバーが glob のパターンを送る機能（ファイル操作、診断のフィルター、ノートブックの文書）でだけ呼ばれ、peg-hs の言語サーバーはこれらを宣言しない（[ADR 0077](adr/0077-fixes-of-the-security-audit.md)）。言語サーバーの実行ファイルを指す設定 `peg-hs.path` は scope を `machine` とし、利用者の設定でだけ決まる。ワークスペースの設定では上書きできない。言語サーバーは文法と文法が取り込むライブラリを読むだけで文法の Haskell を動かさないので、`capabilities.untrustedWorkspaces` を `limited` と宣言し、信頼していないワークスペースでも、利用者の設定の `peg-hs.path` で言語サーバーを起動する。`restrictedConfigurations` に `peg-hs.path` を挙げる（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）

Neovim と Helix は、tree-sitter の文法と言語サーバーを設定して使う。
Neovim では、nvim-treesitter で、tree-sitter の文法を clone せずに GitHub のリリースのタグから入れられる（[ADR 0074](adr/0074-neovim-tree-sitter-from-github.md)）。
README の設定は、保存時に言語サーバーで整形する設定を含む（[ADR 0069](adr/0069-richer-highlighting-and-format-on-save.md)）。
エディタごとの手での確認の記録は `docs/editors/` に置く（[ADR 0044](adr/0044-release-v0-1-0.md)）。

## 文法定義の記法

記法は Ford の PEG 表記を基礎に、型注釈とセマンティックアクションを加える。
確定した記法は [ADR 0004](adr/0004-peg-notation.md) に定め、利用者向けの解説は [docs/syntax.md](syntax.md) に置く。
解説の英語版は [docs/syntax.en.md](syntax.en.md) に置く。

```
%module Example.Parser

%{
import Data.Text (unpack)
}%

# 加算式
Expr :: Int
Expr <- l:Expr '+' r:Term { l + r }
      / Term

Term :: Int
Term <- ds:$[0-9]+ { read (unpack ds) }
```

規則は型注釈（`::`）と定義（`<-`）の組で書き、選択肢ごとに**アクション**（その選択肢が成功したときの値を作る式）をブレース内の Haskell 式として与える。
部分式の結果は `名前:` の束縛で参照し、消費した入力そのものは `$` キャプチャで `Text` として取る。
アクションでは暗黙の予約束縛 `_span` で選択肢の消費範囲を参照できる（[ADR 0008](adr/0008-source-positions.md)）。
アクションを省略した選択肢は、値を持つ要素がちょうど一つのときその値をそのまま返す。
型注釈が `()` の規則では、`()` 以外の値を持つ要素が一つもない選択肢もアクションを省略でき、値は常に `()` になる（[ADR 0063](adr/0063-omit-unit-actions.md)、[ADR 0064](adr/0064-unit-rules-always-return-unit.md)）。
要素のない選択肢は省略できない。
型注釈は省ける。値を持たない、型注釈のない規則の型は `()` で、型注釈 `()` の規則と同じに扱う。引数付き規則と雛形は、引数を宣言する場所が型注釈しかないので、型注釈を省けない（[ADR 0066](adr/0066-omit-unit-type-annotations.md)）。
`%syntax` の文法では、型注釈のない規則の、アクションを省略した選択肢は、値を持つ要素の数と型によらず値を `()` とする（[ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)）。
`%syntax` のない文法で、型注釈もアクションもない規則は、値から型を推論するか、型と構築子を生成する。構築子の名前は選択肢の末尾の `@名前` で、生成する型の導出するクラスは `%deriving` で指定する（[ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)）。
モジュール名は `%module` ディレクティブで宣言し、import と補助関数は `%{ ... }%` の **verbatim ブロック**（生成モジュールにそのまま写す Haskell のコード）に書く。
コメントは `#` から行末までとする。

## 配布と版

公開するパッケージは peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli、peg-hooks の六つである（[ADR 0009](adr/0009-hackage-publication.md)、[ADR 0044](adr/0044-release-v0-1-0.md)、[ADR 0085](adr/0085-generate-modules-in-the-build-with-setup-hooks.md)）。
peg-lsp は peg-cli が依存するので、peg-cli を Hackage から入れるために公開する。
そのため、言語サーバーの API も PVP の対象になる。
適合性テストのパッケージ peg-conformance は公開しない。
エディタの文法と VS Code の拡張機能は、リポジトリの `editors/` で配布する。
TextMate と tree-sitter の文法は、GitHub の Releases の文法のアーカイブ（`peg-hs-editors-<版>.tar.gz`）と、実行ファイルのアーカイブの `editors/` にも入れる。tree-sitter の文法は生成済みのパーサー（`src/`）と問い合わせを含む。アーカイブの中身は `scripts/pack-editors.sh` が作る（[ADR 0073](adr/0073-editor-grammars-in-releases.md)）。

版は PVP（Haskell Package Versioning Policy）に従う。
1.0 までは 0.x とし、互換の崩れる変更は x を上げて示す（[ADR 0009](adr/0009-hackage-publication.md)）。
1.0 は、自己記述化の完了と Golem での実利用を条件とする。
生成モジュールが使う `Peg.Runtime.Internal` の変更も、互換の崩れる変更として扱う（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

六つのパッケージは同じ版で出す（[ADR 0044](adr/0044-release-v0-1-0.md)）。
版の対応を考える手間をなくすためであり、変更のないパッケージの版も上がる。
リリースのタグは、cabal の版の上の三つの桁に `v` を付けたもの（`0.1.0.0` なら `v0.1.0`）とする。
四つめの桁は、タグを伴わない出し直しに使う。
プレリリースのタグは `v0.1.0-rc1` のように `-` の後に印を付け、cabal の版は `-` の前と同じ（`0.1.0.0`）とする。
PVP の版は rc を表せないためである。

リリースは GitHub の Release として公開し、六つのパッケージのソースのアーカイブと Haddock のアーカイブ（実行ファイルだけの peg-cli も含む。[ADR 0048](adr/0048-release-commands-and-haddock-of-peg-cli.md)）、`peg-hs` の実行ファイル（Linux の x86-64 と macOS の arm64）、エディタの文法のアーカイブ、wasm（`peg-hs.wasm`）、それらのチェックサムを添付する。
リリースノートは変更を「追加」「変更」「削除」「修正」などに分け、各変更にコミットと ADR へのリンクを添える。
各パッケージは、版ごとの変更を英語の `CHANGELOG.md` に記録する。

Hackage への公開は、Release の内容を確かめた後に人が行う。
Hackage の資格情報を CI に置かないためである。
プレリリースは Hackage に上げない。候補も上げない（[ADR 0058](adr/0058-no-hackage-candidates-for-pre-releases.md)）。
正式な版を公開する前に、候補として上げて表示を確かめる。
Hackage に一度公開した版は取り消せないためである。

### wasm

文法の解析、生成、整形を、WASI preview1 の reactor の wasm にして、リリースに `peg-hs.wasm` という名前で添付する（[ADR 0078](adr/0078-grammar-analysis-in-wasm.md)）。
名前に版は入れない。版はタグで区別する。
ブラウザの Web Worker や Deno で、テキストで渡した文法に `peg-hs gen` と `peg-hs fmt` と同じことをする。
入力のテキストは、GHC を使わない文法のインタプリタで解析する（[ADR 0090](adr/0090-grammar-interpreter-without-ghc.md)）。

- **エクスポート**：`memory`、`_initialize`、`hs_init`、`malloc`、`free`、`analyze`、`format`、`parse`。呼ぶ側は `_initialize`、`hs_init(0, 0)` の順に一度ずつ呼んでから、`analyze`、`format`、`parse` を呼ぶ。
- **受け渡し**：要求は JSON を UTF-8 で書いた領域の先頭と長さで渡す。応答は新しく確保した領域で、先頭の 4 バイトが長さ（リトルエンディアン）、その後に JSON が続く。呼んだ側が `free` で解放する。Haskell の例外は捕まえて `{"error": ...}` で返す。長さが負のとき、または先頭と長さの和が線形メモリの大きさを超えるときは、要求を写さずに `{"error": "the request is outside the memory"}` を返す。要求の JSON の、文字列の外の `[` と `{` の入れ子が 256 段を超えるときは、JSON でない要求と同じく `{"error": ...}` を返す（[ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)）。
- **`analyze`**：誤りと警告、書いたとおりの文法の構文木、生成した型の宣言、生成したモジュールを返す。モジュールは同じ要求の `peg-hs gen` が書くファイルとバイト単位で一致する。文法が取り込むライブラリは、要求の `"imports"` にパスからテキストへの対応として渡す。省略は空の対応で、対応にないパスは `cannot import P: no such file` の誤りになる。wasm はファイルを読まない。ライブラリの中の誤りと警告は、`"file"` に `%import` のパスを持つ（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）。構文木のノードは、種類、位置、短い文字列、子の並びを持つ同じ形のオブジェクトである。
- **`format`**：`peg-hs fmt` と同じ整形の結果を返す。
- **`parse`**：文法と入力のテキストと、省略できる `%entry` の規則の名前を受け取り、インタプリタで解析する。応答は、文法とインタプリタの誤り（`analyze` の誤りと同じ形）、受理したか、拒否したときの誤り（行、コードポイントで数えた桁、UTF-8 のバイトの位置、期待したもの、送出されたラベル、`renderParseError` の文言）、受理したときの CST である。CST のノードとトークンは、種類の名前、バイトの位置の範囲、束縛の名前、トークンの文字列、子の並びを持つ同じ形のオブジェクトである。回復するモードは出さない（[ADR 0090](adr/0090-grammar-interpreter-without-ghc.md)）。ライブラリは `analyze` と同じく `"imports"` で渡す（[ADR 0092](adr/0092-import-rules-from-other-grammars.md)）。
- **import**：`wasi_snapshot_preview1` の `args_get`、`args_sizes_get`、`environ_get`、`environ_sizes_get`、`clock_time_get`、`clock_res_get`、`random_get`、`fd_write`（標準出力と標準エラーだけ）、`proc_exit` だけを import してよい。GHC のランタイムと C ライブラリが import する、この一覧の外の 13 個の関数（ファイルとポーリング）は、ビルドの後に wasm の中の関数で置きかえる。置きかえた関数は引数を読まずに誤りの番号を返す。`fd_prestat_get` は `EBADF`（8）、ほかは `ENOSYS`（52）である（[ADR 0079](adr/0079-stub-wasi-imports-outside-the-contract.md)）。

wasm は非公開のパッケージ `peg-wasm`（`wasm/`）から、コミットを固定した ghc-wasm-meta のツールチェーンで `scripts/build-wasm.sh` がビルドする。
要求と応答の JSON の形は、README の WebAssembly の節に書く。

## 意図的に採用しなかったもの

以下は検討の上で落とした。
それぞれの根拠は対応する ADR に記録する。

- **Warth らの seed-growing（OMeta 系）**：間接左再帰で結合性が壊れる既知の反例があり、正当性の根拠が弱い。形式意味論を持つ bounded left recursion を採る（[ADR 0001](adr/0001-bounded-left-recursion.md)）。
- **静的な左再帰除去**：文法変換で左再帰を消す方式は、構文木の形が変わるため再結合アクションの合成が必要になり、型付きアクションと両立しない（[ADR 0001](adr/0001-bounded-left-recursion.md)）。
- **Template Haskell quasiquoter**：生成器はスタンドアロンのコマンドとして提供する。生成のコアを純関数として設計しているので、TH のフロントエンドは後から追加できる（[ADR 0002](adr/0002-standalone-code-generator.md)）。
- **構文木だけを返すパーサー**：生成パーサーは型付きの AST を直接返す（[ADR 0003](adr/0003-typed-semantic-actions.md)）。ロスレスな構文木は、`%syntax` を書いた文法でだけ、もう一つの入口として加わる（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。
- **構文木の書き換え**：構文木は読むためのものとし、書き換えの API は作らない。formatter は構文木を読んで新しい文字列を作る（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。
- **可変な利用者状態**：Parsec 型の状態は、同じ規則と位置の評価が同じ結果を返すというメモ化の前提を壊す。解析中に変わらない解析環境と引数付き規則で代える（[ADR 0012](adr/0012-context-sensitive-extensions.md)）。
- **アクション内の副作用**：セマンティックアクションは純粋な Haskell 式に限る。左再帰の成長はアクションを複数回実行しうるため、副作用があると意味論が壊れる。
- **インクリメンタルパースとストリーミングパース**：入力は全体をメモリに載せた `Text` とする。
- **自動のエラー回復**：同期の位置を生成器が自動で探す回復、生成器による暗黙のラベルの挿入、回復の規則の自動の生成はしない。回復の位置は文法の作者がラベルと回復の規則で決める（[ADR 0021](adr/0021-error-recovery.md)、[ADR 0054](adr/0054-automatic-label-insertion.md)）。
- **結合性と優先順位のアノテーション**：yacc 系の `%left` `%prec` は導入しない。左再帰が書けるため、結合性は文法の形で表現できる。
- **整形と lint の設定**：整形の流儀を変える設定、lint の規則を加えたり止めたりする設定は持たない（[ADR 0032](adr/0032-grammar-formatter.md)、[ADR 0033](adr/0033-grammar-linter.md)）。
- **生成モジュールへの peg-hs の版の記録**：書くと、版を上げるたびにすべての生成物が変わる。互換が崩れるときにだけ変わる peg-runtime の版の範囲を書く（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。
- **生成器によるパスの書き換え**：GHC がどのディレクトリで動くかを生成器は知らないので、生成モジュールに記録するパスを生成器は相対パスに直さない（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。
- **ロケールに従う文字コード**：ファイルは UTF-8 だけを扱う（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）。
- **Hackage への自動の公開**、**Windows と x86-64 の macOS の実行ファイル**（[ADR 0044](adr/0044-release-v0-1-0.md)）。

## 設計原則

**決定性**。
生成器は同一の入力からバイト単位で同一の出力を生成する。
生成コードにタイムスタンプや実行した機械の情報を含めない。
例外は利用者が渡したパスであり、相対パスで渡せば機械によらず同じになる。
利用者が生成物をコミットしたとき、差分は文法の変更とだけ対応する。

**広い型、狭い実装**。
将来の拡張が予見される箇所（失敗のラベル、メモ化の制御）は型を先に広く取り、実装は当面の用途に絞る。
未実装の機能に遭遇したらエラーで停止し、黙って無視しない。

**生成コアの純粋性**。
文法から Haskell ソースへの変換は純関数として実装し、CLI はその薄いラッパーとする。
この分離が TH フロントエンドの後付けとテストの容易さの両方を支える。
言語サーバーも、メッセージの処理を純粋な関数とし、入出力と分ける（[ADR 0035](adr/0035-language-server.md)）。

**自己記述**。
`.hpeg` 記法のパーサーは、記法を peg-hs 自身で書いた文法から生成したものである（[ADR 0027](adr/0027-switch-to-self-hosted-parser.md)）。
記法の誤りの文言は、その文法のラベル（[ADR 0021](adr/0021-error-recovery.md)）から作る。

**依存の最小化**。
依存するライブラリは必要なものに限る。
引数の解析や表示の整形のように再実装が容易なものは、外部のライブラリに頼らず再実装する（[ADR 0036](adr/0036-parse-command.md)、[ADR 0037](adr/0037-cli-subcommands.md)）。

## モジュール構成

```
packages/
  peg-runtime   -- 生成コードが依存する実行時ライブラリ
                --   入力、位置、失敗（ラベル付き）、メモ化、左再帰、回復、ロスレスな構文木
  peg-grammar   -- .hpeg 記法のパーサー（自己記述）、文法 AST、静的検査、整形と lint、文法のインタプリタ
  peg-codegen   -- 文法 AST から Haskell ソースへの純関数変換
  peg-lsp       -- 言語サーバー
  peg-cli       -- コマンド peg-hs（gen、fmt、lint、parse、lsp、help）
  peg-hooks     -- 利用者のパッケージのビルドの中で生成する SetupHooks
```

```
examples/
  hooks  -- peg-hooks を使う利用者のパッケージの例。CI でビルドして動かす
```

```
editors/
  textmate         -- TextMate の文法
  tree-sitter-hpeg  -- tree-sitter の文法
  vscode           -- VS Code の拡張機能
  README.md        -- リリースのアーカイブに入れる、文法の説明
```

依存は `peg-cli → peg-codegen → peg-grammar → peg-runtime`、`peg-cli → peg-lsp → peg-grammar`、`peg-hooks → peg-codegen` の一方向とし、peg-runtime は他のどのパッケージにも依存しない。
peg-grammar が peg-runtime に依存するのは、自己記述の記法のパーサー（peg-hs 自身で生成したもの）を含むためである（[ADR 0015](adr/0015-implementation-deviations.md)）。
生成されたコードが依存するのは peg-runtime だけである。構文木の実行時の部分も peg-runtime に置く（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。

```
conformance/
  peg-conformance  -- 実在する言語の文法による適合性テスト（非公開）
```

peg-conformance は公開パッケージ群とは分けて置き、Hackage には公開しない。

```
wasm/
  peg-wasm  -- 文法の解析と生成を JSON で受け渡す関数と、それをエクスポートする wasm の reactor（非公開）
```

peg-wasm も Hackage には公開しない（[ADR 0078](adr/0078-grammar-analysis-in-wasm.md)）。

## 適合性テスト

機構単位のテストに加えて、実在する言語の文法を peg-hs で書き、公開のテストスイートで検証する。
四つの言語は役割が異なる。

- **JSON**：生成器が実用文法を端から端まで処理できることの確認。全件の合格を要求し、その合格を非左再帰の生成器の完成の判定基準とする（[ADR 0010](adr/0010-json-conformance.md)）
- **CommonMark**：PEG の表現力の限界の測定。適合率と失敗の原因分類を記録して、記法の拡張を検討する根拠資料とする（[ADR 0011](adr/0011-commonmark-expressiveness-probe.md)）。拡張（[ADR 0012](adr/0012-context-sensitive-extensions.md)）と論理桁の受け渡し（[ADR 0018](adr/0018-tab-partial-consumption.md)）によって全件の適合を目指す
- **Lua 5.5**：左再帰の実用の規模での検証。`prefixexp`、`var`、`functioncall` の間接の左再帰と 12 段の演算子の優先順位を、マニュアルの構文のまま書く。公式のテストスイートの全ファイルの受理に加え、参照実装から作った正解で構造（優先順位と結合性）と拒否を検査する（[ADR 0022](adr/0022-lua-conformance.md)、[ADR 0025](adr/0025-lua-toml-implementation-deviations.md)）
- **TOML 1.1.0**：構文の後の検査との分担と、エラーからの回復の検証。キーの重複や表の再定義は文法の後の組み立てで拒否し、拒否した段階を記録する。toml-test の全件で回復の全域性とロスレス性を検査する（[ADR 0023](adr/0023-toml-conformance.md)、[ADR 0025](adr/0025-lua-toml-implementation-deviations.md)）

CommonMark の適合率と失敗分類、Lua の文法の書き換えの記録と計測、TOML の拒否の段階の集計のスナップショットは `docs/conformance/` に置く。

## 開発順序

peg-runtime → peg-grammar → peg-codegen（左再帰なし）→ JSON の適合性テスト → ベンチマーク → 左再帰対応 → CommonMark の表現力測定 → 文脈依存の拡張と再測定 → 自己記述化、の順に進める。
段階と ADR の対応は [ADR 0013](adr/0013-roadmap-toolchain-memo.md) に定める。
その後に、言語拡張の指定（[ADR 0016](adr/0016-language-extensions.md)）、メモ化の選択（[ADR 0017](adr/0017-nomemo-implementation.md)）、タブの部分消費（[ADR 0018](adr/0018-tab-partial-consumption.md)）、ロスレスな構文木（[ADR 0019](adr/0019-lossless-syntax-tree.md)）を実装する。
エラーからの回復（[ADR 0021](adr/0021-error-recovery.md)）の後に、Lua（[ADR 0022](adr/0022-lua-conformance.md)）と TOML（[ADR 0023](adr/0023-toml-conformance.md)）の適合性テストを行う。二つは互いに独立である。Lua の前に、入れ子の左再帰の評価の回数の修正（[ADR 0024](adr/0024-discard-seed-dependents-only.md)）を行う。
自己記述のパーサーへの切り替えは、手書きのパーサーと同じ結果を返すことを確かめ、CommonMark の全件適合を含むすべての検査に合格した後に行った（[ADR 0015](adr/0015-implementation-deviations.md)、[ADR 0027](adr/0027-switch-to-self-hosted-parser.md)）。
その後に、単位の値（[ADR 0030](adr/0030-unit-values-are-not-counted.md)）、規則の雛形（[ADR 0031](adr/0031-rule-templates.md)）、サブコマンドへの分割（[ADR 0037](adr/0037-cli-subcommands.md)）、整形（[ADR 0032](adr/0032-grammar-formatter.md)）、lint（[ADR 0033](adr/0033-grammar-linter.md)）、シンタックスハイライト（[ADR 0034](adr/0034-syntax-highlighting.md)）、言語サーバー（[ADR 0035](adr/0035-language-server.md)）、解析の表示（[ADR 0036](adr/0036-parse-command.md)）の順に実装する。
最初のリリース `v0.1.0-rc1` は、リリースの範囲と手順（[ADR 0044](adr/0044-release-v0-1-0.md)）、使い勝手と移植性の修正（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）、文書と CLI の細部の修正（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）を実装した後に打つ。
ADR の連番は決定の順であり、実装の順ではない。

左再帰を後置するのは、非左再帰のパックラットパーサーが先に実働していれば、成長ループの追加が「メモ表の初期値と更新規則の変更」として局所化できるためである。
最初から左再帰を組み込むと、バグが基礎機構のものか成長ループのものかを切り分けられない。

## 未決事項

以下は残課題として保持し、この文書では確定させない。

- 回復の規則に覆われた位置へのラベルの挿入。回復の規則を持たないラベルの送出を外側のラベルの回復で受け止めるよう、実行時の意味論を変える必要がある（[ADR 0054](adr/0054-automatic-label-insertion.md)）
- ラベルの安全性の検査が証明できない形。Golem の文法は、次の理由で 14 個のラベルに `%safe` を付けている。いずれも検査の近似が粗いための偽陽性である（[ADR 0029](adr/0029-label-safety-implementation-deviations.md)、[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）
  - 規則の引数の値を比べない。`Ind(ind)` と `Ind(ind + 2)` が読む字数の違いがわからない
  - 確定した先頭のリテラルを、後に続く選択肢との比較にだけ使い、繰り返しの後ろでは使わない
  - 二つのループを比べられない
  - 一致した規則の中を見ない。一致した行が特定の文字で始まることがわからない
  - 意味述語の値（`r == h` など）を知らない。意味述語が判定する文字の範囲の宣言も、[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md) が別に回したまま残っている
- VS Code の拡張機能の vsix の作成と Marketplace への公開（[ADR 0044](adr/0044-release-v0-1-0.md)）。いまはリポジトリの `editors/` から入れる
- Helix で、tree-sitter の文法を clone せずに git から入れる例（`[[grammar]]` の `source` の `git`、`rev`、`subpath`）。確かめていないので README に載せていない（[ADR 0074](adr/0074-neovim-tree-sitter-from-github.md)）

## 参考文献

- Ford, B. 2004. Parsing Expression Grammars: A Recognition-Based Syntactic Foundation. POPL 2004.
- Medeiros, S., Mascarenhas, F., Ierusalimschy, R. 2014. Left Recursion in Parsing Expression Grammars. Science of Computer Programming 96.
- Warth, A., Douglass, J., Millstein, T. 2008. Packrat Parsers Can Support Left Recursion. PEPM 2008.（比較対象。採用しない）
- Maidl, A. M., Mascarenhas, F., Medeiros, S., Ierusalimschy, R. 2016. Error Reporting in Parsing Expression Grammars. Science of Computer Programming 132.
