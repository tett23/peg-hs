# CommonMark の適合率：論理桁の受け渡し（2026-10-11）

ADR 0011 の三回目のスナップショットである。
ADR 0018 に従い、コンテナの接頭辞の規則が論理桁を返し、各ブロックの規則がそれを基準の桁として受け取るように文法を変えた。
結果は 652 件すべての適合だった。
二回目のスナップショット（ADR 0012 の拡張を使う文法、649 件）で残っていたタブの部分消費の 3 件（例 5、6、7）が適合した。

## 測定の条件

- 仕様：CommonMark 0.31.2（`conformance/data/commonmark-spec-0.31.2/spec.txt`）
- 文法：`conformance/commonmark/Block.peg` と `conformance/commonmark/Inline.peg`
- 判定：仕様の例の HTML との完全一致。適合した例の一覧は `conformance/commonmark/passing.txt`

文法の記法は変えていない。
論理桁は既存の引数付き規則と、`_col` を値として返す規則で受け渡している。

## 入れ子のタブ

仕様の例に加えて、入れ子のコンテナの接頭辞の途中にタブがかかる入力を 10 例作り、参照実装（commonmark.js 0.31.2）の出力と比べた（`conformance/commonmark/tabs/`）。
10 例すべてが一致した。

## 結果

| section | pass | total |
|---|---:|---:|
| Tabs | 11 | 11 |
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
