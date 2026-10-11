# CommonMark の適合率：ADR 0012 の拡張を使う文法（2026-10-11）

ADR 0011 の二回目のスナップショットである。
ADR 0012 の拡張（意味述語、引数付き規則、解析環境、桁の参照）を使って書いた文法で、CommonMark 0.31.2 の 652 件の例を判定した。
結果は 652 件中 649 件の適合（99.5%）だった。
初回のスナップショット（v1 の記法、500 件）から 149 件増えた。

## 測定の条件

- 仕様：CommonMark 0.31.2（`conformance/data/commonmark-spec-0.31.2/spec.txt`）
- 文法：`conformance/commonmark/Block.peg` と `conformance/commonmark/Inline.peg`
- 判定：仕様の例の HTML との完全一致（`→` はタブに戻す）。適合した例の一覧は `conformance/commonmark/passing.txt` にあり、テスト（`cabal test peg-conformance:commonmark-conformance`）がこの一覧との双方向の一致を検査する

構成は ADR 0011 の制約に従う。
入力の照合はすべて生成パーサーが行い、手書きのコードは解析後の AST の変換（リスト項目のまとめ、参照定義の収集、強調の組み立て、HTML の出力）に限った。

## 拡張が埋めた穴

初回のスナップショットで字下げの状態に分類した失敗は、開いているコンテナの列を引数付き規則で渡し、各行で継続の接頭辞を照合し直すことで解消した。
前方参照に分類した失敗は、ブロックの解析で集めた参照定義を解析環境としてインラインの解析に渡すことで解消した。
コードスパンの区切りの長さの比較と、フェンスの長さと字下げの比較には、意味述語を使った。

## 残った失敗

残った 3 件はすべてタブの部分消費（ADR 0012 の「実装しないこと」に挙げた構文）である。
コンテナの接頭辞がタブの途中までを消費し、残りの桁が内容の字下げとして数えられる。
PEG は文字を単位として消費するため、この挙動は拡張を使っても書けない。

## 結果

| section | pass | total |
|---|---:|---:|
| Tabs | 8 | 11 |
| Backslash escapes | 13 | 13 |
| Entity and numeric character references | 17 | 17 |
| Precedence | 1 | 1 |
| Thematic breaks | 19 | 19 |
| ATX headings | 18 | 18 |
| Setext headings | 27 | 27 |
| Indented code blocks | 12 | 12 |
| Fenced code blocks | 29 | 29 |
| HTML blocks | 44 | 44 |
| Link reference definitions | 27 | 27 |
| Paragraphs | 8 | 8 |
| Blank lines | 1 | 1 |
| Block quotes | 25 | 25 |
| List items | 48 | 48 |
| Lists | 26 | 26 |
| Inlines | 1 | 1 |
| Code spans | 22 | 22 |
| Emphasis and strong emphasis | 132 | 132 |
| Links | 90 | 90 |
| Images | 22 | 22 |
| Autolinks | 19 | 19 |
| Raw HTML | 20 | 20 |
| Hard line breaks | 15 | 15 |
| Soft line breaks | 2 | 2 |
| Textual content | 3 | 3 |

| cause | failing examples |
|---|---:|
| tab-columns | 3 |

| example | section | cause | reason |
|---:|---|---|---|
| 5 | Tabs | tab-columns | 項目の内容の桁がタブの途中にあり、タブの残りの桁を内容の字下げとして数える必要がある |
| 6 | Tabs | tab-columns | 引用の '>' の後のタブが一部だけ消費され、残りの桁がコードブロックの字下げになる |
| 7 | Tabs | tab-columns | リストのマーカーの後のタブが一部だけ消費され、残りの桁がコードブロックの字下げになる |
