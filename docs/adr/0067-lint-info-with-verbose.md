# ADR 0067: lint の notice を info に改め、--verbose のときだけ表示する

ステータス: 採択（未実装）

## 文脈

[ADR 0063](0063-omit-unit-actions.md) は、lint に、失敗させない知らせの水準 notice を設けた。
省略できる `{ () }` を `omittable-unit-action` の notice で知らせ、`peg-hs lint` は notice を警告と同じく標準エラーに毎回表示する。
提案中の [ADR 0065](0065-omittable-identity-actions.md) と [ADR 0066](0066-omit-unit-type-annotations.md) も、同じ水準に規則を加える。

notice は、直さなくても誤りではない書き方を知らせる。
直すかどうかは文法の作者が決めることで、直さないと決めた作者にも、`peg-hs lint` を実行するたびに同じ知らせが出る。
CI のログにも毎回残る。
警告は直せば消えるが、notice は直さないことを選べるので、毎回表示されると邪魔になる。

## 実装すること

### 水準の名前

- notice の水準を info と呼ぶ。出力は `notice:` の代わりに `info:` と書く（`G.hpeg:3:13: info: the action can be omitted: ... [omittable-unit-action]; remove { () }`）
- 規則の名前（`omittable-unit-action` など）は変えない

### --verbose

- `peg-hs lint` に `--verbose` を加える
- `--verbose` を付けないときは、info を表示しない。警告と誤りは、これまでどおり表示する
- `--verbose` を付けたときは、info も表示する。表示の順は、これまでの notice と同じく、位置の順とする
- info は、`--verbose` の有無によらず、終了状態を変えない
- `peg-hs help lint` に `--verbose` を載せ、例を一つ加える

### 言語サーバー

- 言語サーバー（[ADR 0035](0035-language-server.md)）は、info を診断の重大度 Hint で報告する。[ADR 0063](0063-omit-unit-actions.md) の Information より目立たない重大度で、多くのエディタは下線を引かずに淡く示す。エディタは文法を開いている間ずっと診断を表示するので、`--verbose` を付けない lint と同じく、目立たせない

### 文書

- docs/syntax.md の lint の節、README の lint の説明、docs/specifications.md の lint の説明の notice を info に改め、`--verbose` を書く。docs/syntax.md の冒頭の「反映している ADR」にこの ADR を加える
- [ADR 0063](0063-omit-unit-actions.md) のステータスに、lint の知らせの水準と表示がこの ADR にあることを加える
- 提案中の [ADR 0065](0065-omittable-identity-actions.md) と [ADR 0066](0066-omit-unit-type-annotations.md) は、notice の代わりに info を使う形で書く

## 実装しないこと

- 規則ごとに info を表示するかを選ぶ仕組み。lint の規則を選ばせないという [ADR 0033](0033-grammar-linter.md) の方針に従う
- info を失敗にするオプション
- 警告を `--verbose` のときだけにすること。警告は誤りなので、常に表示する

## テスト設計

先に書き、いまの実装（[ADR 0063](0063-omit-unit-actions.md) の実装）で失敗させる。

- **既定**：省略できる `{ () }` を含む文法に `peg-hs lint` を実行すると、標準エラーが空で、終了状態が 0 であること。警告もある文法では、警告だけが表示され、終了状態が 1 であること
- **--verbose**：同じ文法に `peg-hs lint --verbose` を実行すると、`info:` の行が位置の順に表示され、終了状態が 0 であること。警告もある文法では、警告と info が表示され、終了状態が 1 であること
- **出力の golden**：lint の出力の golden の notice を info に改めること
- **ヘルプ**：`peg-hs help lint` の golden に `--verbose` が載ること
- **言語サーバー**：info の診断の重大度が Hint であること

## トレードオフ

- `--verbose` を付けないと info を見ないので、省略できる書き方に気付く機会が減る。言語サーバーは Hint として示すので、エディタで文法を書く作者は気付ける
- 水準の名前が notice から info に変わる。[ADR 0063](0063-omit-unit-actions.md) の実装がまだリリースされていないので、利用者への影響はない

## 参考文献

- Language Server Protocol Specification 3.17, DiagnosticSeverity. https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnosticSeverity
