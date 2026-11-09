# ADR 0096: 診断の文言の中の位置にファイル名を付ける

ステータス: 採択（未実装）

## 文脈

[ADR 0092](0092-import-rules-from-other-grammars.md) は、誤りと警告をそれが起きたファイルで報告すると決めた。
診断の先頭の位置は、そのとおりになった。
`Loc` が `locFile` を持ち、`renderDiagnostic` が根の文法のパスと `%import` から、`locFile` に当たるファイルの名前を決める。

ところが、診断の文言の中に埋め込んだ位置は、いまも `行:桁` だけである。
文言は純粋な関数が作り、その関数はファイルの名前を知らない。
名前を知っているのは表示する側だけである。

埋め込んだ位置は、先頭の位置と別のファイルを指すことがある。
main（7e718a6）から作った `peg-hs gen` で、次のように出ることを確かめた。

```
lex/Lib.hpeg:5:8: error: an alternative without an action must have exactly one element with a value, but it has none (in the template O, expanded at 5:6)
lex/Lib.hpeg:8:11: warning: the label l may reject valid input: where it fails, the alternative at 6:6 can match
Arg.hpeg:5:9: warning: the label l may reject valid input: where it fails, the parse can continue at 4:12
Arg2.hpeg:5:14: warning: the label m may reject valid input: where it fails, the repetition at 7:9 can continue
Arg3.hpeg:5:9: warning: the label n may reject valid input: where it fails, the lookahead at 10:9 can match
```

一つめの `5:6` は根の文法 `Tmpl.hpeg` の雛形の呼び出しで、二つめの `6:6` も根の文法 `Lbl.hpeg` の選択肢である。
三つめから五つめの `4:12`、`7:9`、`10:9` は、逆にライブラリ `lex/Q.hpeg` の雛形の中を指す。
どれも、読む人は先頭のファイルの位置だと受け取る。
`T2.hpeg` の例では `lex/O2.hpeg:5:8: error: ... (in the template O, expanded at 5:8)` となり、根の文法の `5:8` と先頭の位置が同じ数字に見える。
`peg-hs gen g/Tmpl.hpeg` と渡しても、先頭は `g/lex/Lib.hpeg:5:8` になるのに、文言の中は `5:6` のままである。

文言に位置を埋め込む箇所は三つのモジュールにある。

- `Peg.Grammar.Templates` の `templateNotes`：`(in the template N, expanded at L:C)`。雛形の定義と呼び出しは別のファイルにありうる。
- `Peg.Grammar.Labels` の `labelWarnings`：`the alternative at L:C can match`、`the parse can continue at L:C`、`the lookahead at L:C can match`、`the repetition at L:C can continue`。理由の文言（`Verdict` の `Unsafe Text`）は、`ruleFailed` で呼び出し元の規則へ進み、雛形の本体はライブラリから、引数は根の文法から来る。どちらの道でもファイルをまたぐ。
- `Peg.Grammar.Lint`：`unreachable-alternative` と `duplicate-alternative` の `the alternative at L:C`。比べるのは同じ選択の中の選択肢で、`lint` は展開の前の文法を見る。さらに `peg-hs lint` と言語サーバーは、根の文法については `locFile` が `0` の警告だけを出す（`Server.hs` の `lints`、[ADR 0092](0092-import-rules-from-other-grammars.md) の `peg-hs lint`）。そのため、ファイルをまたがない。

言語サーバーも同じ文言を出す。
根の文法の診断のうち位置がライブラリにあるものは、`%import` の行に `lex/Lib.hpeg:8:11: 文言` の形で出す（`Server.hs` の `atImport`）。
文言の中の `6:6` は、ここでもライブラリの位置に読める。
wasm の `analyze` は、先頭の位置についてだけ `"file"` を返す（`Wasm.hs` の `diagnostic`）。
言語サーバーと wasm のこの振る舞いは、コードを読んで確かめた。
動かしてはいない。

### もう一つの論点：開いていないライブラリの読み直し

言語サーバーは、根の文法を開くか編集するたびに、開いていないライブラリをディスクから読み直す。
ファイルの更新時刻で読み直しを省くべきかを、調査で測った。
次の値は調査の報告で、この ADR を書くときには測り直していない。

- `BigRoot` に `Peg.hpeg` をライブラリとして取り込んだ文法で、1 回の編集の診断が、ライブラリを開いていないとき 11.8 ms と 11.6 ms、開いているとき 14.7 ms と 17.5 ms だった。取り込みのない文法では 7.4 ms と 7.6 ms だった。
- 開いていないときのほうが速いので、ディスクから読む費用は測れるほどではない。
- 取り込みの有無による約 4 ms の差は、解析のたびにライブラリのテキストを `resolveImports` で解析し直すことによると推測されている。`analysed`（`Server.hs`）は、一回の解析で取り込みの解決を四回行う（`diagnoseWith`、`insertLabelsWithImports`、`recoverProposalsWithImports`、`docTypes`）。四回の呼び出しはコードで確かめたが、差の原因はプロファイルで確かめていない。

## 実装すること

### 文言を部品の並びにする

診断の文言を、語と位置の部品の並びとして持つ。
位置の部品をどう書くかは表示する側が決める。
書き方の規則は一つである。

- 部品の位置が、診断の先頭の位置と同じファイルにあれば、これまでどおり `行:桁` と書く。
- 別のファイルにあれば、そのファイルの名前を前に付けて `名前:行:桁` と書く。

同じファイルの位置はいまの文言と変わらないので、[ADR 0028](0028-label-safety-check.md)、[0031](0031-rule-templates.md)、[0055](0055-templates-and-parameterized-rules-in-stages.md) などに書いた文言、syntax.md の例（`the alternative at 3:28 can match` など）、`label-warnings.txt` と `lint-warnings.txt` と言語サーバーの `session.txt` の golden は変わらない。
変わるのは、ファイルをまたぐ位置だけである。

```
lex/Lib.hpeg:5:8: error: ... (in the template O, expanded at Tmpl.hpeg:5:6)
lex/Lib.hpeg:8:11: warning: the label l may reject valid input: where it fails, the alternative at Lbl.hpeg:6:6 can match
Arg.hpeg:5:9: warning: the label l may reject valid input: where it fails, the parse can continue at lex/Q.hpeg:4:12
```

### 文言を作る側

- `templateNotes` は、元の診断の部品の後ろに ` (in the template N, expanded at `、呼び出しの位置の部品、`)` を足す。いまの `note` は `Diagnostic l msg` を分解して作り直すので、元の文言に位置の部品があると失われる。部品を保ったまま足す。
- `Peg.Grammar.Labels` の `Verdict` の `Unsafe` と `Unchecked` は、`Text` の代わりに部品の並びを持つ。上の四つの文言の位置を位置の部品にする。
- `Peg.Grammar.Import` の `inFile` は、ライブラリの単独の検査の診断を `locFile` が `i` の位置に付け替える。先頭の位置と一緒に、位置の部品もすべて付け替える。いまの形のままだと、部品の位置は `0` に残り、根の文法の位置として名前が付いてしまう。
- `Peg.Grammar.Lint` は変えない。上に書いたとおり、ファイルをまたがない。`LintWarning` は `Diagnostic` ではなく `Text` の文言を持つので、変えないでも型は合う。

### 表示する側

ファイルの番号から名前を決める関数を、表示する側がそれぞれ渡す。

- **`peg-hs` のコマンドと peg-hooks**：`renderDiagnostic` と `Peg.Codegen` の `renderWarning` は、`diagnosticFile file imports` で名前を決める。先頭の位置と同じ規則なので、`peg-hs gen g/Tmpl.hpeg` では文言の中も `g/Tmpl.hpeg:5:6` になる。peg-hooks は `renderDiagnostic` を使うので、ほかに変えるところはない。
- **言語サーバー**：ライブラリは `%import` のパスで、根の文法は URI の最後の部分（`/` の後ろ）のパーセント符号化を解いたもので名指す。解けないときは、最後の部分をそのまま使う。どちらも根の文法のディレクトリからの相対の名前になる。`atImport` は、診断を `%import` の行へ移す前に、元の先頭の位置を基準に文言を書く。移した後に書くと、先頭が根の文法の位置になり、ライブラリの中の位置に名前が付き、根の文法の位置には付かなくなるためである。根の文法の中の診断（`Arg.hpeg` の例）も、`diagnosticValue` で同じ規則で書く。
- **wasm**：`analyze` は、要求の `"sourceName"`（既定は `Grammar.hpeg`）と `%import` から、`peg-hs gen` と同じ `diagnosticFile` で名前を決める。`"message"` は、`gen` に `sourceName` のパスを渡したときの表示から `ファイル名:行:桁: error: ` を除いたものと一致する。`parse` の要求にも、同じ既定の省略できる `"sourceName"` を足す。`parse` の誤りにも、雛形の展開の注記が付くためである。`"file"` は変えない。

### 型と関数

後の「データ構造」の節に書く。
peg-grammar の公開の API を変えるので、版の付け方は [ADR 0092](0092-import-rules-from-other-grammars.md) と同じく、仕様書の「配布と版」に従う。

### 文書

- `renderDiagnostic` の使い方を示す Haddock の例が、引数一つの古い形のまま残っている。`Peg.Grammar.Format`、`Peg.Grammar.LabelInsertion`、`Peg.Grammar.Labels`、`Peg.Grammar.Interpret`、`Peg.Grammar.Check`、`Peg.Grammar.Parser` の冒頭の例を、`renderDiagnostic file imports` の形に直す。
- syntax.md と syntax.en.md の「ほかのファイルの規則を取り込む」の節で、誤りと警告をそれが起きたファイルで報告すると書いた文の後に、文言の中の別のファイルの位置にはファイルの名前が付くことを足す。両方の冒頭の「反映している ADR」の一覧に、この ADR を足す。
- 仕様書の、取り込みの「位置」の項目、言語サーバーの項目、wasm の `analyze` と `parse` の項目を直す。
- README.md と README.ja.md の、ライブラリの誤りの形の説明と、wasm の要求の `sourceName` の説明を直す。

### [ADR 0092](0092-import-rules-from-other-grammars.md) のステータス

[ADR 0092](0092-import-rules-from-other-grammars.md) の「診断の位置」は、先頭の位置だけを決め、文言の中の位置を決めていなかった。
この ADR がそれを補う。
実装の pull-req で、[ADR 0092](0092-import-rules-from-other-grammars.md) のステータスの行を `採択→診断の文言の中の位置は [ADR 0096](0096-file-names-of-positions-in-messages.md)` に変える。

## データ構造

`Peg.Grammar` の `Diagnostic` を次のように変える。

```haskell
-- | A piece of the message of a diagnostic.
data MessagePart
  = Words Text
  | Place Loc
  deriving (Eq, Show)

data Diagnostic = DiagnosticWith Loc [MessagePart]
  deriving (Eq, Show)

diagParts :: Diagnostic -> [MessagePart]

-- | The diagnostic of a message without locations, and the message with
-- every location written as line:column.
pattern Diagnostic :: Loc -> Text -> Diagnostic
pattern Diagnostic {diagLoc, diagMessage} <- ...
  where Diagnostic l m = DiagnosticWith l [Words m]
{-# COMPLETE Diagnostic #-}
{-# COMPLETE DiagnosticWith #-}

-- | The message, naming the file of a location that is not in the file of
-- the diagnostic.
messageText :: (Int -> Text) -> Diagnostic -> Text

-- | The diagnostic with the function applied to its location and to the
-- locations in its message.
relocateDiagnostic :: (Loc -> Loc) -> Diagnostic -> Diagnostic
```

文言を作る箇所の多くは、位置を埋め込まない `Diagnostic l m` である。
`Peg.Grammar.Check` と `Peg.Grammar.Assemble` だけでも数十箇所ある。
双方向の pattern synonym にすると、それらはそのまま通る。
GHC 9.10.3 で、record の pattern synonym が view pattern を使って分解と構築の両方をできることを、小さなモジュールで確かめた。

`diagMessage` は、位置の部品をすべて `行:桁` と書いた文言を返す。
ファイルの名前は付かないので、表示には `messageText` を使う。

pattern synonym には落とし穴が一つある。
`Diagnostic l m` で分解して `Diagnostic l' m` で作り直すと、位置の部品は語の部品になり、ファイルの番号を失う。
record の更新（`d {diagLoc = l}`）も、同じく作り直しになる。
いまのコードで分解して作り直す箇所は、`inFile`、`templateNotes` の `note`、言語サーバーの `atImport` の三つで、どれもこの ADR で部品を保つ形に書き換える。
record の更新は、いまのコードにない。
Haddock に、位置を動かすときは `relocateDiagnostic` を使うことを書く。

`Eq` は部品の並びをそのまま比べる。
同じ文言でも、語の部品だけのものと位置の部品を含むものは等しくない。
位置を埋め込む診断を `Diagnostic` の値と `==` で比べているテストは、`packages/peg-grammar/test/Interpret.hs` の一つ（`expanded at 2:6`）で、`diagLoc` と `diagMessage` を比べる形に直す。

## 実装しないこと

- **`Peg.Grammar.Lint` の文言の部品化**。ファイルをまたがない（文脈の節）。またぐ検査を足すときに、その ADR で部品にする。
- **LSP の `DiagnosticRelatedInformation`**。関連する位置へ移動できるようになるが、クライアントが `textDocument.publishDiagnostics.relatedInformation` を宣言したときにだけ送るので、宣言を読む処理と、宣言しないクライアントのための文言の両方が要る。いまの言語サーバーはこの能力を読まない（`Server.hs` に `relatedInformation` はない）。文言の名前だけで位置は一意に決まるので、移動が欲しくなってから別の ADR で決める。部品の並びがあれば、そのとき文言を作る側は変えずに済む。
- **wasm の構造化した関連位置**（`"related": [...]`）。文言で一意に決まるのは言語サーバーと同じで、使う側がまだない。
- **gcc や clang の `note:` の行**。`Diagnostic` は一行の文言を持つ約束で（Haddock の「one line of English」）、言語サーバーと wasm の `"message"` もそれに乗っている。行を分けると、その約束と golden の形を変えることになる。
- **同じファイルの位置にも名前を付けること**。どの位置も一意になるが、ADR、syntax.md、golden に書いた文言をすべて変えることになり、名前のない文言が今後も大半を占める。
- **開いていないライブラリの更新時刻による読み直しの省略**。調査では、読み直しは測れるほどの費用ではなかった（文脈の節）。
- **ライブラリの解析結果の使い回し**（テキストを鍵にする、一回の解析で取り込みの解決を一回にする）。取り込みのある文法の編集は、開いたライブラリで 17.5 ms と、[ADR 0071](0071-incremental-parsing-in-the-language-server.md) の目安の 16 ms を超える値が報告されている。ただ、原因はプロファイルで確かめていない。測り直してから別の ADR で決める。

## テスト設計

先に書いて失敗させてから実装する。
新しい関数と構築子を使うテストは、いまはコンパイルの誤りで失敗する。
文言を比べるテストは、文脈の節に書いたいまの文言（名前のない `行:桁`）との違いで失敗する。

### peg-grammar

文脈の節の文法（`Tmpl`、`T2`、`Lbl`、`Arg`、`Arg2`、`Arg3` と、それぞれのライブラリ）をテストに置く。

- `Tmpl`：`templateNotes` の後の誤りが、先頭の `locFile` が `1`、位置の部品の `locFile` が `0` で `5:6` を持つ。`messageText` に `0` を `Tmpl.hpeg`、`1` を `lex/Lib.hpeg` とする関数を渡すと `expanded at Tmpl.hpeg:5:6` になり、`diagMessage` は `expanded at 5:6` のままである。
- `T2`：位置の部品が `locFile` `0` の `5:8` を持つ。
- `Lbl`：`labelWarnings` の後に `templateNotes` を通した警告が、先頭の `locFile` が `1`、部品が `locFile` `0` の `6:6` を持つ。
- `Arg`、`Arg2`、`Arg3`：警告の先頭の `locFile` が `0`、部品がそれぞれ `locFile` `1` の `4:12`、`7:9`、`10:9` を持つ。`messageText` は `lex/Q.hpeg:4:12` などと書く。
- 同じファイル：`messageText` は、部品の位置が先頭と同じファイルなら名前を付けない。`label-warnings.txt` の golden がいまのまま通る。
- `relocateDiagnostic`：先頭の位置と部品の位置の両方に関数がかかる。ライブラリの中で雛形を呼ぶライブラリを根の文法から取り込み、単独の検査の誤りの部品の `locFile` が、先頭と同じ `i` になる。
- pattern synonym：`Diagnostic l m` で作った診断の `diagParts` が `[Words m]` で、位置の部品を持つ診断を `Diagnostic l m` で分解すると `m` が `行:桁` の文言になる。

### peg-cli

- `peg-hs gen g/Tmpl.hpeg` の標準エラー出力が `g/lex/Lib.hpeg:5:8: error: ... (in the template O, expanded at g/Tmpl.hpeg:5:6)` になる。
- `peg-hs gen g/Arg.hpeg` の警告が `g/Arg.hpeg:5:9: warning: ... the parse can continue at g/lex/Q.hpeg:4:12` になる。

### peg-lsp

- `file:///w/Lbl.hpeg` を開き、`lex/Lib.hpeg` のテキストを返すと、`%import` の行の診断の文言が `lex/Lib.hpeg:8:11: the label l ... the alternative at Lbl.hpeg:6:6 can match` になる。
- `file:///w/Arg.hpeg` の `5:9` の診断の文言が `... the parse can continue at lex/Q.hpeg:4:12` になる。
- URI の最後の部分がパーセント符号化されている根の文法（`file:///w/My%20Lbl.hpeg`）では、名前が `My Lbl.hpeg` になる。
- `session.txt` の golden がいまのまま通る。

### wasm

- `analyze` に `Tmpl` の文法、`"imports"`、`"sourceName": "Tmpl.hpeg"` を渡すと、`"file": "lex/Lib.hpeg"` の誤りの `"message"` が `... expanded at Tmpl.hpeg:5:6)` で終わる。`"sourceName"` を省くと `Grammar.hpeg:5:6` になる。
- `parse` に同じ文法と `"sourceName"` を渡すと、同じ文言になる。`"sourceName"` が文字列でなければ `sourceName is not a string` の誤りになる。
- `Arg` の警告の `"message"` が `lex/Q.hpeg:4:12` を含む。
- 同じファイルの位置の警告（`wasm/test/Main.hs` と `wasm_test.ts` の `the alternative at 2:28 can match`）は変わらない。

## トレードオフ

- 文言を作る関数にファイルの名前を決める関数を渡す形も考えた。型の変更は小さいが、`check` や `labelWarnings` のような純粋な関数のすべての呼び出しに名前の関数が要る。言語サーバーは `atImport` で先頭の位置を移すので、作った後の文言をもう一度書き直すことになる。部品の並びにすれば、文言を作る側は名前を知らずに済み、表示する側がそれぞれの名前の付け方を選べる。
- pattern synonym で `Diagnostic l m` の形を保つ代わりに、分解して作り直すと位置の部品を失う落とし穴を抱える。いまの三箇所はこの ADR で直し、テストで部品の `locFile` を確かめるが、今後の変更で同じ形を書けば、型の検査では気付けない。
- 別のファイルの位置にだけ名前を付けるので、同じ文言の中で名前のある位置とない位置が混ざる。名前のない位置は先頭のファイルの位置である、と読めば一意に決まる。
- 言語サーバーは根の文法を URI の最後の部分で、ライブラリを `%import` のパスで名指す。CLI のように実行したディレクトリからのパスにはならないが、どちらも根の文法のディレクトリからの相対の名前なので、二つの名前の基準は揃う。

## 参考文献

- [ADR 0028](0028-label-safety-check.md)、[ADR 0031](0031-rule-templates.md)、[ADR 0055](0055-templates-and-parameterized-rules-in-stages.md)：文言に位置を埋め込む警告と注記
- [ADR 0071](0071-incremental-parsing-in-the-language-server.md)：言語サーバーの診断の目安
- [ADR 0092](0092-import-rules-from-other-grammars.md)：取り込みと診断の位置
- GHC User's Guide, Pattern synonyms（record pattern synonyms、explicitly bidirectional pattern synonyms、`COMPLETE` pragma）：https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/pattern_synonyms.html
- Language Server Protocol Specification 3.17, `DiagnosticRelatedInformation` と `PublishDiagnosticsClientCapabilities.relatedInformation`：https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/
