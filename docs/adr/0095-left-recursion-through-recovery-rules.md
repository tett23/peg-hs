# ADR 0095: 回復の規則を経由する左再帰を左再帰として判定する

ステータス: 採択（未実装）

## 文脈

[ADR 0021](0021-error-recovery.md) は、回復するモードの入口（`parseRecover` と `parseSyntaxRecover`）が、どの入力に対しても結果を返すと定めた。
[ADR 0090](0090-grammar-interpreter-without-ghc.md) の `interpretRecover` も同じ意味論に従う。
ところが、回復するモードの解析が終わらない文法がある。

回復するモードでは、`e ^l` の `e` が普通の失敗をすると、`e` を試みた位置から `l` の回復の規則を評価する（ランタイムの `labeledWith`）。
回復の規則を `R` とすれば、`e ^l` はその位置で `e / R` のように振る舞う。
違いは、`R` で成功したときに構文エラーを一つ記録することだけである。

一方、左再帰の静的な判定（peg-grammar の `Check` の `leftCalls` と `exprNullable`）は、`e ^l` の `e` しか見ていない。
`R` への呼び出しは左端の呼び出しに数えず、`R` が空文字列に一致しても `e ^l` は nullable にならない。
そのため、回復の規則を経由したときにだけ同じ位置で自分を呼ぶ規則は、左再帰と判定されない。
左再帰でない規則は `memo` で包まれる（[ADR 0001](0001-bounded-left-recursion.md)）。
`memo` は本体の評価を終えてからメモ表に書くので、評価の途中で同じ位置から呼び直されると、表を引けずに本体をまた評価する。
これが止まらない。

main（7e718a6）の `interpretRecover` で、次の四つの文法を確かめた。
どれも `%module M` と `%syntax` を付け、`cabal repl peg-grammar` を `+RTS -M1g` で動かした。
`analysisLeftRecursive` はどれも空集合だった。

| 名前 | 文法 | 入力 | 結果 |
|---|---|---|---|
| A | `%recover l E`、`S <- ('a' ^l) S / !.`、`E <- ''` | `aa` | heap overflow |
| B | `%recover l R`、`S <- 'a' ^l`、`R <- S / 'x'` | `b` | heap overflow |
| D | `%recover l E`、`S <- '(' L ')'`、`L <- (Item ^l) L / ''`、`Item <- 'a'`、`E <- &')'` | `(a)` | heap overflow |
| E | `%recover l E`、`S <- '(' L`、`L <- ('a' ^l) (')' / L)`、`E <- ''` | `(ab)` | heap overflow |

E は `(aa)` なら終わる。
`(ab)` では、位置 2 の `L` で `'a'` が `b` に失敗し、`E` が空の範囲で回復する。
続く `(')' / L)` は `')'` に失敗して、位置 2 の `L` をまた呼ぶ。
入力を一文字も進めないまま、同じ位置の `L` に戻ってくる。

ラベルの安全性の検査（`labelWarnings`）は、A、B、D のラベルを「正しい入力を拒否しうる」と警告するが、E のラベルには何も報告しない。
安全と判定されたラベルでも、解析が終わらないことがある。
D は、Golem の「段落の終わりで閉じたとみなす」と同じ挿入の回復（回復の規則が空文字列に一致する）を、繰り返しの中のラベルに使った形である。

生成したモジュールも、規則ごとにどのメモ化を使うかを解釈器と同じ `ruleMemoisation` で決め、同じランタイムの関数を呼ぶ。
E の文法から生成したモジュールでは、規則 `L` が `PegRt.memo` で包まれていることを確かめた。
生成したモジュールの `parseSyntaxRecover` が `(ab)` で終わらないことは、同じ包み方とランタイムからの推論であり、この ADR を書いた時点では実行して確かめきれていない。

## 実装すること

### 左再帰の判定

左再帰の判定に限って、回復の規則を持つラベル `e ^l` を `e / R` として扱う（`R` は `%recover l R` の規則）。

- `e ^l` は、`e` か `R` が nullable なら nullable とする
- `e ^l` の左端の呼び出しには、`e` の左端の呼び出しに加えて `R` を含める
- この nullable は、上の規則を入れて規則の集合の不動点として求め直す。求めた集合は左再帰の判定にだけ使う
- `%recover` を持たないラベルの扱いは変えない

回復しないモードの言語についての判定は変えない。
`analysisNullable` と、繰り返しの中身が空文字列に一致する誤り（`repetitionErrors`）は、これまでの nullable で判定する。
ランタイムの繰り返しは入力を進めなかった反復で止まるので、回復の規則が空に一致しても繰り返しは止まる。

`analysisLeftRecursive` は、拡げた判定の結果になる。
`ruleMemoisation` は変えず、この集合に入った規則は回復するモードでも回復しないモードでも `memoLR` で包まれる。
生成するコードと解釈器は、これまでどおり規則ごとに一つの包み方を持つ。
回復するモードでは、成長ループが同じ位置の再入を種の失敗で受け止め、bounded left recursion（[ADR 0001](0001-bounded-left-recursion.md)）の意味論で結果を決める。

回復しないモードでは、拡げた判定で加わった規則は実際には左再帰しない。
回復の規則が呼ばれないので、本体が自分の種を読むことはない。
成長ループは一回めの結果と同じ終わりの位置の結果を得て止まり、一回めの結果を返す。

### 既存の検査への波及

左再帰の規則に対する既存の誤りは、拡げた集合に対して出す。

- `error: rule E takes parameters and cannot take part in left recursion`
- `error: rule E takes part in left recursion and must be memoised`

この二つに当たる規則は、回復するモードで同じ位置に再入すると、いまも終わらない（`memoArg` も評価の後に表へ書き、`%nomemo` の規則は表を持たない）。
誤りの文言は変えない。

`%recover` は根の文法だけが決める（[ADR 0092](0092-import-rules-from-other-grammars.md)）。
取り込んだ規則は、根の文法の `%recover` で拡げた判定を受ける。

### 文書

- docs/syntax.md と docs/syntax.en.md の「左再帰」の節に、回復の規則を経由して同じ位置に戻る呼び出しも左再帰に数えることと、そのとき二つの制約（引数付き規則、`%nomemo`）が及ぶことを書く。「構文エラーからの回復」の節から、その説明を参照する。両方の冒頭の「反映している ADR」の一覧に、この ADR を加える
- docs/specifications.md の左再帰の説明に、回復の規則を経由する左再帰を加え、この ADR へリンクする
- [ADR 0001](0001-bounded-left-recursion.md) のステータスを `採択→左再帰に関与する規則の判定（回復の規則を経由する呼び出し）は [ADR 0095](0095-left-recursion-through-recovery-rules.md)` にする
- [ADR 0021](0021-error-recovery.md) のステータスを `採択→ラベルの文言（実装すること、実装しないこと）は [ADR 0089](0089-rule-names-and-label-messages-in-errors.md)、回復するモードが終わるための左再帰の判定は [ADR 0095](0095-left-recursion-through-recovery-rules.md)` にする

## 実装しないこと

- 回復するモードでだけ `memoLR` を使い、回復しないモードでは `memo` を使う切り替え。規則の包み方に、モードで分岐する四つめの種類を加えることになり、生成器、解釈器、`Memoisation` の型のすべてに手が入る。得られるのは、すでに回復するモードで終わらない文法の、回復しないモードの評価の定数倍だけである。リポジトリの文法の左再帰の集合は変わらない（テスト設計を参照）ので、この ADR で影響を受けるのは、いまの main で回復するモードが終わらない文法に限られる
- 空文字列に一致する回復の規則を拒むこと。[ADR 0021](0021-error-recovery.md) と docs/syntax.md は挿入の回復（幅 0 の回復）を認めている。B のように回復の規則が空に一致しなくても終わらない例にも効かない
- 実行時の再入の検出（評価中の規則と位置の組を記録し、再入を失敗にする）。すべての呼び出しに記録の費用がかかり、`%nomemo` の規則の循環にも別の扱いが要る。再入を失敗にするのは新しい意味論であり、bounded left recursion の結果とも食い違う
- ラベルの安全性の検査（[ADR 0087](0087-other-labels-do-not-change-the-label-check.md) など）と、ラベルの自動挿入（[ADR 0054](0054-automatic-label-insertion.md)）の変更。どちらも回復しないモードの言語について判定しており、独自の左再帰の解析を持つ。拡げた判定は使わない
- 回復の規則の中のラベルの扱いの変更。[ADR 0021](0021-error-recovery.md) は「回復の規則の中の送出は、回復の失敗として扱う。回復が入れ子になって止まらなくなるのを防ぐためである」と書く。実装は、回復の規則から外へ出た送出を回復の失敗とし、外側のラベルを送出する。回復の規則の評価は回復するモードのまま行われるので、回復の規則の中のラベルは、それぞれの回復の規則で回復する。B が終わらない原因は同じ位置への再入であり、この ADR の判定で止まる。入れ子の回復を禁じるかどうかは、この ADR では決めない
- 左再帰の誤りの文言に、回復の規則を経由したことを書き足すこと

## テスト設計

次のテストを先に書き、main で失敗することを確かめてから実装する。
回復するモードが終わらないことによる失敗は、テストの中で時間の上限（`System.Timeout.timeout`、たとえば 5 秒）を設け、上限を超えたら失敗とする。
`-M` を付けずに走らせると、上限より先にメモリを使い尽くすおそれがある。
テストでは入力を短く保ち、上限を短くする。

- **判定**（peg-grammar の `analysisLeftRecursive`）：A は `{S}`、B は `{R, S}`、D は `{L}`、E は `{L}`。いまはどれも空集合なので失敗する
- **回復するモードが終わる**（`interpretRecover`）：いまはどれも時間の上限で失敗する。期待する結果は、Check.hs だけを試しに直した版で観察した値である
  - A の `aa`：構文エラーなし、木は 0..2
  - B の `b`：ラベル `l`、範囲 (0, 1) の構文エラーが一つ
  - D の `(a)`：構文エラーなし、木は 0..3
  - E の `(aa)`：構文エラーなし。`(ab)`：ラベルなし、範囲 (0, 4) の構文エラーが一つ（開始規則の失敗による入力全体のエラー）
- **生成したモジュール**：E と D の形を持つ fixture（`packages/peg-codegen/test/fixtures/RecoverLeft.hpeg`）を加えて再生成し、`parseSyntaxRecover` が上の入力で終わり、解釈器と一致することを Agreement のテストで確かめる。いまの生成器では `L` が `memo` で包まれ、時間の上限で失敗する
- **回復しないモードの結果は変わらない**：A、B、D、E と、その `%recover` の行を除いた文法（ラベルは残る。拡げた判定に入らないので `memo` で包まれる）で、`interpret` の結果（値または `ParseError`）が、長さ 6 までの `a`、`b`、`(`、`)`、`x` の全入力で一致すること。`memoLR` で包んでも回復しないモードの結果が変わらないことの確認である
- **既存の誤りが及ぶ**：B を変えて、回復の規則を経由する循環の中の規則に引数を付けた文法で `takes parameters and cannot take part in left recursion`、循環の中の規則に `%nomemo` を付けた文法で `must be memoised` が報告されること。いまはどちらも誤りなく検査を通るので失敗する
- **リポジトリの文法の判定は変わらない**：`%recover` を持つ 12 の文法（conformance/bench/JsonRecover.hpeg、conformance/bench/Memo.hpeg、conformance/toml/Toml.hpeg、editors/tree-sitter-hpeg/test/highlight/notation.hpeg、packages/peg-codegen/test/derived の RecoverExports.hpeg と RecoverInsertLabeled.hpeg、packages/peg-codegen/test/fixtures の Expect.hpeg、ExpectSyntax.hpeg、Recover.hpeg、RecoverInsert.hpeg、RecoverShared.hpeg、packages/peg-grammar/grammar/PegSyntax.hpeg）の `analysisLeftRecursive` が、いまの値と一致すること。これは回帰の検出のためのテストであり、いまも通る
- **無作為な文法で終わる**：ラベルの検査のテストの文法の生成器（peg-grammar の test/Labels.hs の `genGrammar`）に `%recover l R` を加え、`R` を、文法の規則を呼ぶものと呼ばないもの、空に一致するものとしないものから無作為に作る。短い入力で `interpretRecover` が時間の上限（QuickCheck の `within`、1 件あたり 1 秒など）までに終わることを確かめる。上限は時間で区切る。このプロパティが main で反例を見つけるかは確かめていない。main で失敗することは、上の固定の例が担う

## トレードオフ

- 拡げた判定で加わった規則は、回復しないモードでも成長ループを通る。成功するたびに本体をもう一度評価する（二回めの評価の中の呼び出しは、種を読まないのでメモ表から返る）。対象は、いまの main で回復するモードが終わらない文法の規則に限られる。リポジトリの 12 の文法と、手元の Golem の文法（golem-parser の Golem.hpeg、golem-emet の Emet.hpeg）では、試しに直した版でも左再帰の集合が変わらなかった
- 判定は静的な近似である。回復の規則が実際には同じ位置に戻らない入力しかなくても、経路があれば左再帰とする。既存の左再帰の判定と同じ性質である
- 引数付き規則や `%nomemo` の規則が回復の規則を経由する循環にあると、いままで通った文法が誤りになる。そうした文法は、循環に入る入力で回復するモードが終わらない
- 回復の結果は bounded left recursion の意味論で決まる。E の `(ab)` は局所的に回復せず、入力全体が一つの構文エラーになる。入力を進めない回復の規則が同じ位置に戻る文法では、回復の位置は文法の作者が書いた意図と一致しないことがある。終わることを優先し、回復の質は文法の書き方に委ねる

## 参考文献

- Medeiros, S., Mascarenhas, F., Ierusalimschy, R. 2014. Left Recursion in Parsing Expression Grammars. Science of Computer Programming 96.
- Medeiros, S., Mascarenhas, F. 2018. Syntax Error Recovery in Parsing Expression Grammars. Proceedings of the 33rd ACM Symposium on Applied Computing (SAC 2018).
