# ADR 0083: 群の内側の束縛は、同じ群の中のコードからも見えない

ステータス: 採択

## 文脈

[ADR 0082](0082-static-check-of-binding-references.md) は、コードの位置から見える束縛を次のように決めた。

- 意味述語と引数からは、同じ逐次の中でその位置より左にある束縛と、外側の逐次の中で群より左にある束縛

そのうえで、テスト設計の「誤りにならないもの」に `S <- x:N (y:N &{ x > 0 && y > 0 })*` を挙げた。
群の中の述語が、同じ群の中で左にある `y` を参照する例である。

この例は誤っていた。
生成器は、群の内側の束縛をどのコードにも渡さない。
群の選択肢は、束縛を無視する形で生成されるからである（`Peg.Codegen` の `passThrough` を `honorBind = False` で呼ぶ）。
これは [ADR 0004](0004-peg-notation.md) の「グループ内の束縛は外から見えない」と、束縛を選択肢の逐次の直下に限る決定に沿っている。
そのため、群の中の述語が同じ群の束縛を参照すると、GHC が `Variable not in scope` を出す。
v0.1.0-rc5 で `S <- x:N (y:N &{ y > 0 })* { () }` を生成して GHC 9.10.3 でコンパイルすると、`W.hpeg:3:18: error: [GHC-88464] Variable not in scope: y` になった。

[ADR 0082](0082-static-check-of-binding-references.md) を書く前に確かめたのは、群の中の述語が群より左の `x` を参照する例だけだった。
同じ群の `y` を参照する例は、確かめていなかった。
[ADR 0012](0012-context-sensitive-extensions.md) の「同じ逐次の中で述語より左にある束縛」を、群の逐次にも当てはまると読んだのが原因である。

[ADR 0082](0082-static-check-of-binding-references.md) の実装（[#62](https://github.com/tett23/peg-hs/pull/62)）は、[ADR 0082](0082-static-check-of-binding-references.md) の原則「コードの位置から見える名前は、生成したコードで GHC が見る名前と同じである」に従った。
群の内側の束縛は、同じ群の中の述語と引数からも見えないものとして検査する。
[ADR 0082](0082-static-check-of-binding-references.md) の例は、誤りとして報告される。

作業者の判断で、この振る舞いを残し、[ADR 0082](0082-static-check-of-binding-references.md) の見える束縛の規定を、この ADR で正す。

## 実装すること

### 見える束縛の訂正

[ADR 0082](0082-static-check-of-binding-references.md) の「見える束縛と見えない束縛」の、意味述語と引数の項を次のように読み替える。

- 意味述語と引数からは、選択肢の逐次の直下で、その位置より左にある束縛が見える。位置が群の中にあるときは、その群を含む選択肢の逐次の直下で、群より左にある束縛が見える。
- 群の内側の束縛は、どこからも見えない。同じ群の中の意味述語と引数、入れ子にした群の中のコードからも見えない。参照すると、`x is bound inside a group, which the code cannot see` を報告する。

規則の引数、予約束縛、アクションから見える束縛、ほかの二つの誤りは、[ADR 0082](0082-static-check-of-binding-references.md) のとおりである。

### 文書

- [ADR 0082](0082-static-check-of-binding-references.md) のステータスの行を `採択→群の内側の束縛の見え方は ADR 0083` にする。
- `docs/syntax.md` の「反映している ADR」の一覧にこの ADR を足し、束縛の節の参照に添える。誤りの表の `(y:N &{ y > 0 })*` の例は、すでにこの ADR の振る舞いを書いている。
- `docs/specifications.md` の検査の項に、この ADR へのリンクを足す。

製品のコードは変えない。
#62 の実装が、すでにこの ADR の振る舞いである。

## 実装しないこと

- 群の内側の束縛を、同じ群の中のコードから見えるようにすること。生成器が群の選択肢で束縛を作るように変える必要があり、[ADR 0026](0026-discard-unused-values.md) の値を捨てる文脈の生成にも関わる。必要になったら別の ADR で決める。
- 群の内側の束縛そのものを、誤りか lint の警告にすること。参照しない限り、今の文法は正しく生成される。
- [ADR 0082](0082-static-check-of-binding-references.md) の本文の書きかえ。ADR はコミットした後は変えない。

## テスト設計

この ADR の振る舞いを固定するテストは、#62 ですでに入っている。

- `packages/peg-grammar/test/Main.hs`
  - `S <- x:N (y:N &{ x > 0 && y > 0 })* { x }` で、`y` の位置（3 行 27 桁）に `y is bound inside a group, which the code cannot see` が出る（[ADR 0082](0082-static-check-of-binding-references.md) の誤った例そのもの）。
  - `S <- x:N (y:N &{ x > 0 })* { x }` は誤りにならない。
- `packages/peg-codegen/test/Main.hs` の GHC との一致のテスト
  - 検査なしで生成した `S <- x:N (y:N &{ pegUnchecked > 0 })* { x }` と `S <- x:N ys:(y:N &{ pegUnchecked > 0 })* { x + length ys }` で、GHC が `y` の位置に `Variable not in scope` を出す。
  - `S <- x:N (y:N &{ x > 0 })* { x }` はコンパイルが通る。

この ADR で足すテストはない。
採択のときに、`adr-guard links` が通ることと、上のテストが main で通ることを確かめる。

## トレードオフ

- 群の中で、群の要素の値に依存する述語を書けない。`(y:N &{ y > 0 })*` のような書き方は、規則に分ければ書ける（`S <- x:N P* { x }`、`P <- y:N &{ y > 0 }`）。規則を分けるとメモ化の単位も分かれる。[ADR 0004](0004-peg-notation.md) が、束縛を逐次の直下に限ったときに受け入れた制約と同じである。
- [ADR 0082](0082-static-check-of-binding-references.md) の本文には、誤った例が残る。ステータスの行のリンクで、この ADR に行けるようにする。

## 参考文献

- [ADR 0004](0004-peg-notation.md)
- [ADR 0012](0012-context-sensitive-extensions.md)
- [ADR 0082](0082-static-check-of-binding-references.md)
