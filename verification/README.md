# Lean による peg-hs の検証

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) に基づき、hpeg の構文解析、拒否条件、生成する Haskell の一部を Lean で検証する。
各定理の対象と公開入口までの未証明部分を次の表に示す。

| 不変条件 | Lean が検査する性質 | 実装との対応と残る課題 |
| --- | --- | --- |
| 1 | [Parsing.lean](Parsing.lean) は有限の式の実行と帰納的な判定関係の同値、深さ 256 の境界を証明する。[Lexical.lean](Lexical.lean) は空白とコメントのモデルを検査する。 | [check-core.sh](check-core.sh) は非回復時のランタイムの一部とモデルを比較し、[check-lexical.sh](check-lexical.sh) は実メタ文法の該当規則を照合する。任意のテキストに対する公開入口 `parseTops` とメタ文法全体の導出の同値は未証明。意味述語の Haskell 式は、モデルへ真偽値を渡す前に評価されると仮定する。 |
| 2 | [Guard.lean](Guard.lean) は二つのファイル名に制御文字がある場合の診断との同値を証明する。[Nullable.lean](Nullable.lean) は有限の正の式に対する空文字受理集合の最小不動点と停止性を証明する。[Reachable.lean](Reachable.lean) は有限の参照グラフにおける到達集合の正確性と停止性を証明する。[Signatures.lean](Signatures.lean) は規則の重複、参照の存在、引数個数を判定する。 | [check-guard.sh](check-guard.sh) は生成器の文字比較を翻訳して照合し、[check-nullable.sh](check-nullable.sh) と [check-reachable.sh](check-reachable.sh) は Haskell の該当処理を固定の定義と照合する。[ExtractSignatures.hs](ExtractSignatures.hs) は二つのメタ文法と `Templates.hpeg` の定義と参照を抽出し、Lean が三件とも検査する。空文字受理判定と署名抽出から公開入口の全診断までの同値、全段階の停止性は未証明。 |
| 3 | [Header.lean](Header.lean) はモジュール名と `module` 行の構文を検査する。[Literal.lean](Literal.lean) は文字列リテラルの引用とエスケープを検査する。 | [check-header.sh](check-header.sh) は対応する Haskell の定義を照合し、[check-literal.sh](check-literal.sh) は GHC の `Show` と 97 個の一文字および 9,409 個の二文字を比較する。生成モジュール全体の Haskell 構文導出は未証明。実際に再生成した二つのメタ文法は GHC に渡して検査する。 |

[File.lean](File.lean) は、先頭の `Ws` に続いて、入力を消費する `TopItem` の導出を有限回つないで末尾に達することと、開始規則 `File` が成功することの同値を証明する。[ExtractFile.hs](ExtractFile.hs) は `Peg.hpeg` と `PegSyntax.hpeg` から開始規則と、その呼び出し先のうち11規則の認識に使う演算子を翻訳する。それぞれの翻訳について、空入力で `Ws` が成功し、`TopItem` がラベルなしで失敗し、`File` が空入力を受理することを Lean が検査する。したがって、各メタ文法に開始規則の定理を適用するとき、空入力での失敗を仮定に置く必要がなくなる。

[Consumption.lean](Consumption.lean) は、PEG 式の成功後に残る文字列が、元の入力の接尾辞であることを示す。この性質から、各メタ文法の `File` の成功を、先頭の空白を読み終えた位置から非空の接頭辞を項目として順に消費し、末尾に達する導出と結びつける。

この翻訳では束縛とキャプチャの値を捨て、成功時に値を作るアクションは入力位置を変えないと仮定する。展開しない規則呼び出しと意味述語には出現箇所ごとに独立の PEG 式を与え、どの式を与えても定理が成り立つことを検査する。これは非回復時の認識モデルに関する証明である。任意の非空入力で、残る呼び出しや埋め込み Haskell の評価が実パーサーと一致することは今後の課題である。

[Whitespace.lean](Whitespace.lean) は、各実メタ文法から取り出した `Ws` が任意の入力でどこまで読み進むかを証明する。`SpaceChar` の捕捉と意味述語を一文字の文字クラスに翻訳し、コメントとの順序付き選択と繰り返しを開始規則の定理につなぐ。[check-whitespace.sh](check-whitespace.sh) は、Lean の文字表と GHC の `Data.Char.isSpace` を Unicode スカラー値 1,112,064 個すべてについて比較する。

[TemplateQueue.lean](TemplateQueue.lean) は、テンプレート展開で、同じ深さの有限個のインスタンスを FIFO 順に処理し、そこで生じたインスタンスを次の深さで処理することを形式化する。個々の展開が有限個の子を返せば、子の個数に一律の上限がなくても、深さ 65 ですべての残りを拒否して待ち行列が空になる。外側の型分類の反復も、初期カウンター 8 で最大 9 回で終了する。テンプレート本体の置換、型分類、各インスタンスを展開する処理自体の停止性は、この二つの定理の前提に残る。[check-template-queue.sh](check-template-queue.sh) は実装の深さと待ち行列の更新を照合し、実生成器で深さ 64 の生成成功と 65 の診断を検査する。

[Pipeline.lean](Pipeline.lean) は、警告付き生成で外側の診断または内側の `generationModule` を観測するまでの分岐を扱う。各段階が失敗時に空でない診断を返し、テンプレートの注記が診断を空にしないという前提から、合成後の結果が空でない診断か生成テキストになることを証明する。[PipelineProbe.hs](PipelineProbe.hs) は実際の `generateWithWarnings` に構文、import、テンプレート、規則参照、生成オプションのエラーを渡し、外側と内側のどちらから診断が返るかを確かめる。個々の段階が任意の入力で停止し、仕様どおりの診断を生成することは未証明である。

[Pragmas.lean](Pragmas.lean) は、元ファイルの位置を表す `LINE` と `COLUMN`、生成先の位置を復元する行の形式を証明する。位置は自然数で、ファイル名の文字集合は文字列リテラルの定理と同じである。埋め込み本文は任意の文字列として扱う。生成器はユーザーが書いた行と衝突しない復元用マーカーを選ぶ。これにより、ユーザーの quasiquote 内に同じ形式の行があっても、その行を復元対象から除外できる。本文に含まれるコメントやレイアウトが周囲の Haskell の構文に及ぼす影響はこの定理の範囲外である。[check-pragmas.sh](check-pragmas.sh) は引用符を含むファイル名で実際に生成したアクションの位置と復元行を Lean の出力と照合し、モジュールを GHC で検査する。[check-no-record.sh](check-no-record.sh) は `NoTraditionalRecordSyntax` を指定した文法でメモ用ストアと設定のアクセスを含むモジュールを生成し、GHC と実行結果で検査する。

ソースの抽出・照合スクリプトと、そこで使う Haskell の構文の読み取り方は信頼する前提である。
[Audit.lean](Audit.lean) は各証明モジュールの定理ごとに依存する公理を列挙し、Lean 標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理を使うと失敗する。

## 実行方法

リポジトリのルートで次のコマンドを実行する。
GHC と Cabal はプロジェクト指定の版を使う。
elan が [lean-toolchain](lean-toolchain) の Lean を選ぶ。

```sh
cabal build exe:peg-hs
verification/check.sh
```

対応テストでは、深さ 256 の前後で `parseTops` と Lean の結果を比較する。
空ファイル、末尾の余分な文字、未定義参照については実際の診断を確認する。
実ファイルから抽出した規則の署名は三件とも Lean で証明し、未定義参照を加えた負例の証明は Lean が拒否することを確認する。
二つのメタ文法は実ファイルから再生成し、出力を GHC で検査する。
区切りが閉じたアクションに不完全な Haskell 式を入れたケースでは、GHC が構文エラーを返すことを確認する。
