# peg-hs 仕様書

peg-hs は、PEG（Parsing Expression Grammar）の定義から Haskell のパーサーを生成するツールチェーンである。
標準的な PEG の全構文に加えて左再帰を受理し、文法定義ファイルから Haskell ソースコードを生成する。
最初の利用者は組版システム Golem だが、peg-hs 自体は Golem に依存しない汎用ライブラリとして開発する。

この文書は、peg-hs の能力、配布の形、意図的に採用しなかったもの、設計原則、モジュール構成、開発順序を定める。
実装の詳細は書かず、それを定めた ADR（Architecture Decision Record、設計の決定の記録）へのリンクで示す。
ADR は `docs/adr/` に連番で置く。
コミットした ADR は、ステータスの行と ADR の参照に付けるリンクを除いて変更しない。
性能の判断の根拠にした計測の記録は `docs/benchmarks/` に置き、これもコミットした後は変更しない。
この二つの決まりは [adr-guard](https://github.com/tett23/adr-guard) v0.8.1 が pre-commit のフックと CI で検査する（[ADR 0043](adr/0043-adr-guard-v0.8.0.md)、[ADR 0047](adr/0047-adr-guard-v0.8.1.md)）。

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
- **規則の雛形** `Name<式, ...>`：規則や式を引数に取る規則。引数の組ごとに普通の規則へ生成時に展開するので、展開した規則にもメモ化と左再帰の意味論がそのまま効く（[ADR 0031](adr/0031-rule-templates.md)）

規則名と束縛名には Unicode の英字と数字を使える（[ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)）。

### 生成するコード

生成器は文法定義ファイル（`.hpeg`）を読み、単一の Haskell モジュールを出力する。

- 各規則はユーザーが指定した結果型を持ち、パーサーは中間表現を経由せず、利用者の定義した構文木の型（AST）の値を直接返す（[ADR 0003](adr/0003-typed-semantic-actions.md)）
- 生成コードは peg-runtime の上で動く薄いコードとし、メモ化と左再帰の機構は peg-runtime が担う
- 生成モジュールは、開始規則の入口 `parse :: Text -> Either ParseError a` を公開する。入口は入力の全体の消費を要求する。`%entry` で、ほかの規則にも入口を作れる。エクスポートの範囲、生成器の内部の名前と利用者の名前が衝突しない仕組み、位置の数え方は [ADR 0014](adr/0014-generated-module-api.md) に定める
- アクションに書いた Haskell の式が型の誤りを起こすと、GHC はそれを `.hpeg` ファイルの行と桁で報告する（[ADR 0014](adr/0014-generated-module-api.md)）
- `%language` で、生成モジュールの言語拡張を有効にできる。生成コードの意味を変える `RebindableSyntax` は拒否する（[ADR 0016](adr/0016-language-extensions.md)）
- `%nomemo` で、規則ごとにメモ化を外せる。左再帰に関与する規則には指定できない（[ADR 0006](adr/0006-memoization-control.md)、[ADR 0017](adr/0017-nomemo-implementation.md)）

生成モジュールの先頭のコメントには、そのモジュールが要る peg-runtime の版の範囲を `peg-runtime >=0.1 && <0.2` の形で書く（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。
生成コードは、peg-runtime のうち生成コードのためだけにある内部向けのモジュール（`Peg.Runtime.Internal`）を使う。
このモジュールを変えると、古い生成物が新しい peg-runtime で動かなくなりうる。
そのため、範囲は互換が崩れるときにだけ上げ、このモジュールの変更は PVP の上でメジャーの変更として扱う。

生成器は、同じ文法と同じ引数からバイト単位で同じ出力を生成する。
ただし、生成モジュールは `peg-hs gen` に渡された文法と出力のパスを、渡されたとおりに記録する。
GHC の誤りの位置を `.hpeg` の行で示すためである。
そのため、絶対パスを渡すと機械ごとに出力が変わる。
生成モジュールをコンパイルするパッケージのディレクトリからの相対パスで渡せば、機械によらず同じ出力になり、エディタも誤りの位置を開ける（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

生成モジュールは GHC 9.10、9.12、9.14 でコンパイルできる（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）。

### ロスレスな構文木

`%syntax` を書いた文法では、型付きの値の入口に加えて、元の文字列を一文字も失わない構文木（**CST**、具象構文木）を返す入口を生成する（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。
規則の呼び出しがノードに、終端の一致がトークンになり、空白やコメントの規則も木に残る。
木を連結すると、元の入力に戻る。
木の各ノードから親と絶対位置をたどれ、束縛ごとに型の付いた取り出し関数が生成される。
lint や formatter のように、空白とコメントを扱う用途のためのものである。

### 静的検査

生成器は文法を検査し、次の問題をコード生成前に報告する。

- 未定義の非終端の参照
- 開始規則から到達不能な規則
- nullable な式の繰り返し（`e*` で `e` が空文字列を受理する形。実行時の無限ループになるため拒否する）
- 同じ規則を二度挙げた `%entry`（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）

ラベル（次の「構文エラーからの回復」の節）の位置が安全かも検査し、危険かもしれないラベルを警告する（[ADR 0028](adr/0028-label-safety-check.md)）。
ラベルが安全であるとは、ほかのラベルをすべて外した文法の上で、そのラベルを外しても受理する言語が変わらないことである（[ADR 0029](adr/0029-label-safety-implementation-deviations.md)）。
すべてのラベルが安全なら、ラベルを付けた文法と外した文法は同じ言語を受理する。
検査は近似であり、安全と判定したラベルは安全だが、安全なラベルに警告することがある。
近似を詰めるために、規則の呼び出しを越えて共通の接頭辞を除いて比べ、`&{ False }` のような定数の意味述語を解釈し、先頭のリテラルが確定していれば二文字目以降も使って比べる（[ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)）。
作者が確かめたラベルは `%safe` で警告を止める。

### エラー報告

失敗の表現はラベル付き失敗（labeled failures）の型を持つ。
失敗は、解析が最も先まで進んだ位置（最遠到達位置）と、その位置で期待していたもの（失敗した終端の集合、期待集合）を報告する（[ADR 0005](adr/0005-error-reporting.md)）。
位置情報はバイトオフセットと行と桁の両方を保持する（[ADR 0008](adr/0008-source-positions.md)）。
`renderParseError` は、失敗を `行:桁: expected A, B or C` の形の文に直す（[ADR 0014](adr/0014-generated-module-api.md)）。

### 構文エラーからの回復

文法の作者は、そこで失敗したら構文エラーである位置に `e ^label` を書き（**ラベル**）、ラベルごとに回復の規則を `%recover` で与える（[ADR 0021](adr/0021-error-recovery.md)）。
送出されたラベルは順序付き選択の後戻りを止める。
回復するモードの入口は、回復の規則で入力を同期の位置まで読み飛ばして解析を続け、構文エラーの列を返す。
`%syntax` の文法では、回復した範囲を誤りのノードとして含む構文木を、どの入力に対しても返す。
構文木のロスレス性は、エラーを含む入力でも成り立つ。
回復しないモードの入口は、最初の失敗で停止し、送出されたラベルを失敗に含める。

### 文法ファイルの道具

文法ファイルを書くための道具を、`peg-hs` のコマンドとエディタの支援として持つ。
コマンドは `peg-hs <command>` の形のサブコマンドであり（[ADR 0037](adr/0037-cli-subcommands.md)）、次の六つがある。

- **生成** `peg-hs gen`：文法から Haskell のモジュールを生成する（[ADR 0002](adr/0002-standalone-code-generator.md)）
- **整形** `peg-hs fmt`：空白と改行だけを書き換え、文法を一つに固定した流儀に揃える。流儀の議論をなくすため、設定と整形を止める指示は持たない。整形の前後で文法の意味が変わらないことを、整形の結果を解析し直して確かめる。`--check` は書き換えずに差の有無だけを調べる（[ADR 0032](adr/0032-grammar-formatter.md)）
- **lint** `peg-hs lint`：到達しない選択肢、効果のないラベル、使われない束縛のように、文法の意味から必ず問題だと言えるものだけを警告する。偽陽性がないので、利用者は規則を加えられず、警告を抑制できない。警告は文法を直せば消える（[ADR 0033](adr/0033-grammar-linter.md)）。警告に従って直しても、受理する入力と誤りの位置は変わらない。リテラルの接頭辞の警告に従って選択肢を消すと、決して成功しない字句が誤りの文言の期待したものから消える（[ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)）
- **解析の表示** `peg-hs parse`：文法で入力を解析し、AST（アクションの値）と CST を表示する。文法を書きながら、生成したパーサーが入力をどう読むかを確かめるためのものである。生成したパーサーを、`PATH` にある GHC（9.10 から 9.14）でコンパイルして実行する。`%env` を宣言した文法は、環境の値を渡せないので扱わない（[ADR 0036](adr/0036-parse-command.md)、[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）
- **言語サーバー** `peg-hs lsp`：LSP（Language Server Protocol）の言語サーバーを標準入出力で起動する。診断、整形、semantic tokens、定義への移動、参照の検索、ホバー、文書の記号を提供する。編集の途中の誤りを含む文書でも、回復した構文木をもとに働く（[ADR 0035](adr/0035-language-server.md)）
- **ヘルプ** `peg-hs help`：コマンドの一覧を、`peg-hs help COMMAND` でそのコマンドの説明を表示する

`fmt` と `lint` は、ファイルを指定しなければ、現在のディレクトリから再帰的にたどったすべての `.hpeg` ファイルを対象にする。
文法ファイルの拡張子は `.hpeg` である。以前の拡張子 `.peg` はほかの PEG の道具と重なるので探索では探さないが、ファイルを直接渡せば拡張子によらず扱う。エディタの言語の名前も `hpeg` とする（[ADR 0050](adr/0050-hpeg-extension.md)）。
名前が `.` で始まるディレクトリと `dist-newstyle` はたどらない（[ADR 0032](adr/0032-grammar-formatter.md)）。

すべてのコマンドは、次の約束に従う（[ADR 0037](adr/0037-cli-subcommands.md)、[ADR 0045](adr/0045-fixes-before-v0-1-0.md)、[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

- **出力の先**：結果は標準出力に、誤りと警告は標準エラー出力に書く。文法の誤りと警告は `ファイル:行:桁: error: 文言` の形で書く
- **終了状態**：成功は 0、検査で問題が見つかった場合（文法の誤り、lint の警告、`fmt --check` の差、`parse` の解析の失敗、ファイルの読み書きの失敗）は 1、使い方の誤り（未知のコマンドとオプション、引数の不足）は 2 とする
- **文字コード**：文法、入力、生成モジュールのファイルは、ロケールによらず UTF-8 で読み書きする。先頭のバイト順マーク（BOM）は読み飛ばす。文法と生成モジュールはソースコードなので、文字コードを選ぶオプションは持たない
- **ファイルの誤り**：読めない、書けないファイルは、`peg-hs: cannot read FILE: no such file` のように、どのファイルの読み込みと書き込みのどちらが、なぜ失敗したかを一行で報告し、直し方の手がかりを添える。`fmt` と `lint` は、読めないファイルを報告して残りのファイルを続ける
- **オプション**：値を取るオプションは `--name value` と `--name=value` の両方の形を受け付ける
- **ヘルプと誤りの文言**：各コマンドのヘルプは、使い方、説明、オプション、例の順に書き、例を一つ以上含む。使い方の誤りには `peg-hs help COMMAND` の案内を添える。知らないコマンドが既知のコマンドに近い綴りなら、候補を示す

エディタの支援として、リポジトリの `editors/` に次のものを置く。

- **シンタックスハイライト**：TextMate と tree-sitter の文法。アクションや verbatim ブロックの中の Haskell の断片は、Haskell の文法に任せて色を付ける（[ADR 0034](adr/0034-syntax-highlighting.md)）。tree-sitter の文法は、verbatim ブロックの中身を `peg-hs gen` と同じ境界で読む（[ADR 0045](adr/0045-fixes-before-v0-1-0.md)）
- **semantic tokens**：言語サーバーが、規則、束縛、ラベルなどの種類を返す（[ADR 0035](adr/0035-language-server.md)）
- **VS Code の拡張機能**：TextMate の文法と言語サーバーの起動を含む。リポジトリから入れる（[ADR 0034](adr/0034-syntax-highlighting.md)、[ADR 0035](adr/0035-language-server.md)）

Neovim と Helix は、tree-sitter の文法と言語サーバーを設定して使う。
エディタごとの手での確認の記録は `docs/editors/` に置く（[ADR 0044](adr/0044-release-v0-1-0.md)）。

## 文法定義の記法

記法は Ford の PEG 表記を基礎に、型注釈とセマンティックアクションを加える。
確定した記法は [ADR 0004](adr/0004-peg-notation.md) に定め、利用者向けの解説は [docs/syntax.md](syntax.md) に置く。

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
モジュール名は `%module` ディレクティブで宣言し、import と補助関数は `%{ ... }%` の **verbatim ブロック**（生成モジュールにそのまま写す Haskell のコード）に書く。
コメントは `#` から行末までとする。

## 配布と版

公開するパッケージは peg-runtime、peg-grammar、peg-codegen、peg-lsp、peg-cli の五つである（[ADR 0009](adr/0009-hackage-publication.md)、[ADR 0044](adr/0044-release-v0-1-0.md)）。
peg-lsp は peg-cli が依存するので、peg-cli を Hackage から入れるために公開する。
そのため、言語サーバーの API も PVP の対象になる。
適合性テストのパッケージ peg-conformance は公開しない。
エディタの文法と VS Code の拡張機能は、リポジトリの `editors/` で配布する。

版は PVP（Haskell Package Versioning Policy）に従う。
1.0 までは 0.x とし、互換の崩れる変更は x を上げて示す（[ADR 0009](adr/0009-hackage-publication.md)）。
1.0 は、自己記述化の完了と Golem での実利用を条件とする。
生成モジュールが使う `Peg.Runtime.Internal` の変更も、互換の崩れる変更として扱う（[ADR 0046](adr/0046-docs-cli-and-ci-before-v0-1-0.md)）。

五つのパッケージは同じ版で出す（[ADR 0044](adr/0044-release-v0-1-0.md)）。
版の対応を考える手間をなくすためであり、変更のないパッケージの版も上がる。
リリースのタグは、cabal の版の上の三つの桁に `v` を付けたもの（`0.1.0.0` なら `v0.1.0`）とする。
四つめの桁は、タグを伴わない出し直しに使う。
プレリリースのタグは `v0.1.0-rc1` のように `-` の後に印を付け、cabal の版は `-` の前と同じ（`0.1.0.0`）とする。
PVP の版は rc を表せないためである。

リリースは GitHub の Release として公開し、五つのパッケージのソースのアーカイブと Haddock のアーカイブ（実行ファイルだけの peg-cli も含む。[ADR 0048](adr/0048-release-commands-and-haddock-of-peg-cli.md)）、`peg-hs` の実行ファイル（Linux の x86-64 と macOS の arm64）、それらのチェックサムを添付する。
リリースノートは変更を「追加」「変更」「削除」「修正」などに分け、各変更にコミットと ADR へのリンクを添える。
各パッケージは、版ごとの変更を英語の `CHANGELOG.md` に記録する。

Hackage への公開は、Release の内容を確かめた後に人が行う。
Hackage の資格情報を CI に置かないためである。
プレリリースは Hackage に公開せず、候補として上げて表示を確かめるだけにする。
Hackage に一度公開した版は取り消せないためである。

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
- **自動のエラー回復**：同期の位置を生成器が自動で探す回復や、ラベルの自動挿入はしない。回復の位置は文法の作者がラベルと回復の規則で決める（[ADR 0021](adr/0021-error-recovery.md)）。
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
  peg-grammar   -- .hpeg 記法のパーサー（自己記述）、文法 AST、静的検査、整形と lint
  peg-codegen   -- 文法 AST から Haskell ソースへの純関数変換
  peg-lsp       -- 言語サーバー
  peg-cli       -- コマンド peg-hs（gen、fmt、lint、parse、lsp、help）
```

```
editors/
  textmate         -- TextMate の文法
  tree-sitter-hpeg  -- tree-sitter の文法
  vscode           -- VS Code の拡張機能
```

依存は `peg-cli → peg-codegen → peg-grammar → peg-runtime` と `peg-cli → peg-lsp → peg-grammar` の一方向とし、peg-runtime は他のどのパッケージにも依存しない。
peg-grammar が peg-runtime に依存するのは、自己記述の記法のパーサー（peg-hs 自身で生成したもの）を含むためである（[ADR 0015](adr/0015-implementation-deviations.md)）。
生成されたコードが依存するのは peg-runtime だけである。構文木の実行時の部分も peg-runtime に置く（[ADR 0019](adr/0019-lossless-syntax-tree.md)）。

```
conformance/
  peg-conformance  -- 実在する言語の文法による適合性テスト（非公開）
```

peg-conformance は公開パッケージ群とは分けて置き、Hackage には公開しない。

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

- ラベルの自動挿入（[ADR 0021](adr/0021-error-recovery.md)、[ADR 0028](adr/0028-label-safety-check.md)）
- VS Code の拡張機能の vsix の作成と Marketplace への公開（[ADR 0044](adr/0044-release-v0-1-0.md)）。いまはリポジトリの `editors/` から入れる
- 雛形と引数付き規則の組み合わせのうち、雛形が自分の値の引数を持つこと（`Indented<p>(n :: Int)`）。雛形の引数が呼び出し元の引数を使う組み合わせは、[ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md) の段階 1 で入った。値の引数を渡す呼び出しの記法（`Name<args>(vals)`）は段階 2 で入ったが、雛形はまだ値の引数を宣言できず、値の引数を渡す呼び出しは誤りになる。雛形の値の引数の意味（段階 3）が残っている（[ADR 0031](adr/0031-rule-templates.md)、却下した [ADR 0040](adr/0040-templates-with-parameterized-rules.md)）

## 参考文献

- Ford, B. 2004. Parsing Expression Grammars: A Recognition-Based Syntactic Foundation. POPL 2004.
- Medeiros, S., Mascarenhas, F., Ierusalimschy, R. 2014. Left Recursion in Parsing Expression Grammars. Science of Computer Programming 96.
- Warth, A., Douglass, J., Millstein, T. 2008. Packrat Parsers Can Support Left Recursion. PEPM 2008.（比較対象。採用しない）
- Maidl, A. M., Mascarenhas, F., Medeiros, S., Ierusalimschy, R. 2016. Error Reporting in Parsing Expression Grammars. Science of Computer Programming 132.
