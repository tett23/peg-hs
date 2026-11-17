# Lean による peg-hs の検証

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) に基づき、hpeg の構文解析、拒否条件、生成する Haskell の一部を Lean で検証する。
各定理の対象と公開入口までの未証明部分を次の表に示す。

| 不変条件 | Lean が検査する性質 | 実装との対応と残る課題 |
| --- | --- | --- |
| 1 | [Parsing.lean](Parsing.lean) は有限の式の実行と帰納的な判定関係の同値、深さ 256 の境界を証明する。[Lexical.lean](Lexical.lean) は空白とコメントのモデルを検査する。 | [check-core.sh](check-core.sh) は非回復時のランタイムの一部とモデルを比較し、[check-lexical.sh](check-lexical.sh) は実メタ文法の該当規則を照合する。任意のテキストに対する公開入口 `parseTops` とメタ文法全体の導出の同値は未証明。意味述語の Haskell 式は、モデルへ真偽値を渡す前に評価されると仮定する。 |
| 2 | [Guard.lean](Guard.lean) は二つのファイル名に制御文字がある場合の診断との同値を証明する。[Nullable.lean](Nullable.lean) は有限の正の式に対する空文字受理集合の最小不動点と停止性を証明する。[Reachable.lean](Reachable.lean) は有限の参照グラフにおける到達集合の正確性と停止性を証明する。[Signatures.lean](Signatures.lean) は規則の重複、参照の存在、引数個数を判定する。 | [check-guard.sh](check-guard.sh) は生成器の文字比較を翻訳して照合し、[check-nullable.sh](check-nullable.sh) と [check-reachable.sh](check-reachable.sh) は Haskell の該当処理を固定の定義と照合する。[ExtractSignatures.hs](ExtractSignatures.hs) は二つのメタ文法と `Templates.hpeg` の定義と参照を抽出し、Lean が三件とも検査する。空文字受理判定と署名抽出から公開入口の全診断までの同値、全段階の停止性は未証明。 |
| 3 | [Header.lean](Header.lean) はモジュール名と `module` 行の構文を検査する。[Literal.lean](Literal.lean) は文字列リテラルの引用とエスケープを検査する。 | [check-header.sh](check-header.sh) は対応する Haskell の定義を照合し、[check-literal.sh](check-literal.sh) は GHC の `Show` と 97 個の一文字および 9,409 個の二文字を比較する。生成モジュール全体の Haskell 構文導出は未証明。実際に再生成した二つのメタ文法は GHC に渡して検査する。 |

[File.lean](File.lean) は、先頭の `Ws` に続いて、入力を消費する `TopItem` の導出を有限回つないで末尾に達することと、開始規則 `File` が成功することの同値を証明する。[ExtractFile.hs](ExtractFile.hs) は `Peg.hpeg` と `PegSyntax.hpeg` から開始規則と、その呼び出し先のうち11規則の認識に使う演算子を翻訳する。それぞれの翻訳について、空入力で `Ws` が成功し、`TopItem` がラベルなしで失敗し、`File` が空入力を受理することを Lean が検査する。したがって、各メタ文法に開始規則の定理を適用するとき、空入力での失敗を仮定に置く必要がなくなる。

[CallOrder.lean](CallOrder.lean) は、同じ入力位置で呼び出されうる規則を調べ、呼び出しのたびに規則の順位が下がることを証明する。先読みの中で呼ぶ規則や失敗後に元の位置に戻って試す選択肢も含める。先に文字を消費すれば残りの入力が短くなる。この二つを組み合わせて、呼び出し関係が整礎であることを証明する。[ExtractCallOrder.hs](ExtractCallOrder.hs) は両メタ文法の全規則から、文字消費と呼び出しに関係する演算子を抽出する。空文字の受理可能性と順位は抽出器が候補を作り、Lean が各演算子を走査して全辺を検査する。非回復時のこの証明では意味述語を文字を消費しない演算として扱う。意味述語の Haskell 評価、返す構文木、ランタイムとの対応には別の証明が要る。

[Consumption.lean](Consumption.lean) は、PEG 式の成功後に残る文字列が、元の入力の接尾辞であることを示す。この性質から、各メタ文法の `File` の成功を、先頭の空白を読み終えた位置から非空の接頭辞を項目として順に消費し、末尾に達する導出と結びつける。

この翻訳では束縛とキャプチャの値を捨て、成功時に値を作るアクションは入力位置を変えないと仮定する。展開しない規則呼び出しと意味述語には出現箇所ごとに独立の PEG 式を与え、どの式を与えても定理が成り立つことを検査する。これは非回復時の認識モデルに関する証明である。任意の非空入力で、残る呼び出しや埋め込み Haskell の評価が実パーサーと一致することは今後の課題である。

[Whitespace.lean](Whitespace.lean) は、各実メタ文法から取り出した `Ws` が任意の入力でどこまで読み進むかを証明する。`SpaceChar` の捕捉と意味述語を一文字の文字クラスに翻訳し、コメントとの順序付き選択と繰り返しを開始規則の定理につなぐ。[check-whitespace.sh](check-whitespace.sh) は、Lean の文字表と GHC の `Data.Char.isSpace` を Unicode スカラー値 1,112,064 個すべてについて比較する。

[TemplateQueue.lean](TemplateQueue.lean) は、テンプレート展開で、同じ深さの有限個のインスタンスを FIFO 順に処理し、そこで生じたインスタンスを次の深さで処理することを形式化する。個々の展開が有限個の子を返せば、子の個数に一律の上限がなくても、深さ 65 ですべての残りを拒否して待ち行列が空になる。外側の型分類の反復も、初期カウンター 8 で最大 9 回で終了する。テンプレート本体の置換、型分類、各インスタンスを展開する処理自体の停止性は、この二つの定理の前提に残る。型分類を除くこれらの前提は、次に述べる TemplateExpansionWhole.lean が外す。[check-template-queue.sh](check-template-queue.sh) は実装の深さと待ち行列の更新を照合し、実生成器で深さ 64 の生成成功と 65 の診断を検査する。

[TemplateExpansionWhole.lean](TemplateExpansionWhole.lean) は、`expandTemplates` 全体についての定理 `expandTemplates_whole` を証明する。この定理は四つの性質からなる。展開は終わり、結果は一つに決まる。拒否の結果には診断が一件以上あり、`Left` なので文法を含まない。受理の結果は、展開した通常の規則の後にインスタンスを並べたものである。そこにはテンプレート、テンプレートの呼び出し、テンプレートへの参照が残らず、各インスタンスは入力のどの規則とも異なる名前で一度だけ定義される。

このモデルは、`expandTemplates`、`expandOnce`、`expandRule`、`expandAlt`、`expandItems`、`expandExpr`、`captures`、`argType`、`instanceOf`、`freshName`、`drain` の分岐をすべて写す。`drain` の再帰は関係 `Drain` に、型の反復 `go` は関係 `Go` に写し、それぞれの導出が存在して一つに決まることを証明する。待ち行列の停止性は、深さ d の仕事の後に深さ d + 1 の仕事が並ぶ FIFO の形が保たれることから導く。インスタンスの本体は、テンプレートを呼び出し元として、束縛のスコープを項目ごとに広げて展開する。[TemplateExpansion.lean](TemplateExpansion.lean) にあった、呼び出し元を固定しスコープを広げない `expandExpr` と `expandBody` のモデルは、このモジュールで置き換えた。そのため、[TemplateSubstitution.lean](TemplateSubstitution.lean) の式は、グループの項目に束縛を持つ。

さらに、[check-template-expansion-whole.sh](check-template-expansion-whole.sh) がモデルを実装に結びつける。このスクリプトは、モデルが写す `Templates.hs` の範囲を [template-expansion-whole.source](template-expansion-whole.source) と照合する。続いて、[TemplateExpansionWholeProbe.hs](TemplateExpansionWholeProbe.hs) が `parseGrammar` で読んだ 11 個の文法を、実際の `expandTemplates` とモデルの両方で展開し、規則の型を除いた結果を比べる。比べる文法は、受理、インスタンスの共有、名前の衝突の回避、`%syntax` でのインライン化、各診断、深さの上限を含む。

ただし、次の前提は定理の仮定として残る。

- `haskellIdents`（`codeVariables`）、インスタンスの型を作る `instanceType`、型の分類 `classifiedTypes . classify` は任意の関数として扱う。プローブは型を比べない。
- メモ表のキーは位置を除いた引数の `show` であり、導出された `Show` が単射であることを仮定する。モデルは引数を構造で比べる。
- `Data.Map` と `Data.Set` はリストで写す。`M.fromList` は同じキーの最後の束縛を残し、`S.toAscList` は整列して重複を除く。
- 位置は自然数で写し、プローブは一つのファイルの `Loc f l c` を `l * 100000 + c` と書く。
- `show (k :: Integer)` が `Nat.repr` と一致することは、[check-template-expansion-fresh.sh](check-template-expansion-fresh.sh) のプローブで確かめる。

[Pipeline.lean](Pipeline.lean) は、警告付き生成で外側の診断または内側の `generationModule` を観測するまでの分岐を扱う。各段階が失敗時に空でない診断を返し、テンプレートの注記が診断を空にしないという前提から、合成後の結果が空でない診断か生成テキストになることを証明する。[PipelineProbe.hs](PipelineProbe.hs) は実際の `generateWithWarnings` に構文、import、テンプレート、規則参照、生成オプションのエラーを渡し、外側と内側のどちらから診断が返るかを確かめる。個々の段階が任意の入力で停止し、仕様どおりの診断を生成することは未証明である。

[AssembleValidation.lean](AssembleValidation.lean) は、`Peg.Grammar.Assemble.assemble` の検査を、位置を消した `Top` のモデルで形式化する。`assemble_failure_iff_violation_or_missing_module` と `assemble_ok_iff` は、違反があるか `%module` がないときだけ拒否し、拒否の診断が空でないことを示す。述語は呼び出し側から受け取らない。[AssemblePredicates.lean](AssemblePredicates.lean) が `isValidIdent`、`isClassName`、`isExportItem`、`T.words`、`binderError` などを翻訳し、文字の分類には GHC 9.10.3 の `isAlpha`、`isAlphaNum`、`isUpper` と `ModifierLetter` をすべてのスカラー値で表にした [AssembleChars.lean](AssembleChars.lean) を使う。`TDef` の選択肢は [AssembleBindings.lean](AssembleBindings.lean) の木として持つ。`invariant2_alt_binders_iff` は、取り出した名前が木の中の束縛の出現とちょうど一致することを示し、`invariant2_reserved_binding_iff` と `invariant2_reserved_parameter_iff` は、束縛名と引数名の診断が、出現していて `binderError` が拒否する名前と一致することを示す。[check-assemble-predicates.sh](check-assemble-predicates.sh) は文字の表を作り直して照合し、翻訳元の Haskell の範囲を固定し、Unicode の名前、予約語、`forall`、修飾文字、修飾付きの名前、拡張のキーワード、入れ子の束縛を含む同じ入力で、Haskell と Lean の結果を比べる。`Text` の操作を `List Char` で表すこと、`Int` が 64 ビットであること、診断の文言と位置を消すことは前提に残る。

[LabelCheckModel.lean](LabelCheckModel.lean) は、`Peg.Grammar.Labels` のうち `labelWarnings`、`stripLabels`、`stripLabelsAs` と、それらが呼ぶモジュール内のすべての関数を、関数ごとに Lean の全域関数へ写したモデルである。文字の集合は [LabelCheckCharSet.lean](LabelCheckCharSet.lean) が写す。`failed`、`succeeded`、`ruleFailed`、`ruleSucceeded` の相互再帰は、燃料で段を数える `run` として書く。[check-label-check.sh](check-label-check.sh) がモデルを実装に結びつける。このスクリプトは、`Labels.hs` 全体を [label-check.source](label-check.source) と照合し、`isSpace` の表を GHC 9.10.3 で作り直して照合する。さらに、リポジトリのすべての `.hpeg` と、[ADR 0029](../docs/adr/0029-label-safety-implementation-deviations.md)、[ADR 0087](../docs/adr/0087-other-labels-do-not-change-the-label-check.md)、[ADR 0088](../docs/adr/0088-correct-the-second-example-of-adr-0087.md) の例、`%recover`、入れ子のグループ、重複した選択肢、テンプレート、左再帰、引数の持ち上げを含む文法を [LabelCheckProbe.hs](LabelCheckProbe.hs) で読む。そのうえで、実際の `labelWarnings` と `stripLabelsAs`、左再帰の分類、空文字列を受理しうる規則を、モデルの結果と比べる。

[LabelCheckTermination.lean](LabelCheckTermination.lean) は、ラベルの検査が停止することを示す。各ラベルについて、検査が訪れる文脈は有限の一覧 `keyUniverse` に入る。規則はそのラベルの規則か呼び出し元の規則であり、枠はラベルの枠か呼び出しの枠の末尾である。文字の集合は整列した区間の列で、`0x10FFFF` を超えない。一致した要素の列は 8 個以下で、引数の置き換えは 3 回以下である。各段は訪れた文脈で止まるか新しい文脈を訪れるので、`run_terminates` は燃料 `keyUniverse.length + 1` で結果が出ることを示す。`run_mono` は、それより多い燃料でも結果が変わらないことを示す。これにより `verdictOf` と `labelWarnings` が定まる。`labelWarnings_eq_fuel` は、プローブの燃料で全ラベルの判定が出れば、その警告が `labelWarnings` に一致することを示す。

[LabelCheckTheorems.lean](LabelCheckTheorems.lean) は、ラベルの除去と警告の性質を示す。`unlabelExpr_stripExpr` と `stripExpr_eq_unlabelExpr` は、`stripLabels` がラベルの注記だけを外すことを示す。外した結果からさらにすべてのラベルを消すと、入力からラベルを消したものに一致し、テンプレートの呼び出しがなければラベルは一つも残らない。`stripLabels_rules`、`stripLabels_fields`、`recoveryEntries_spec` は、規則、選択肢、要素の位置と束縛と順序が保たれ、`%recover`、`%safe`、`%message` が空になることを示す。また、回復の規則が、開始規則でも `%entry` でもなければ一度だけ入口に加わることも示す。`sites_labels` と `mem_labelWarnings` は、警告が、`%safe` にない名前のラベルのうち判定が `safe` でないものにちょうど対応することを示す。そのとき、警告の位置はラベルを付けた式を持つ要素の位置であり、文言は「may reject valid input」か「cannot be checked」である。`verdict_ignores_other_labels` は、各ラベルをほかのラベルを外した文法と枠の上で判定することを示す（[ADR 0029](../docs/adr/0029-label-safety-implementation-deviations.md)、[ADR 0087](../docs/adr/0087-other-labels-do-not-change-the-label-check.md)、[ADR 0088](../docs/adr/0088-correct-the-second-example-of-adr-0087.md)）。`verdict_in_lookahead`、`verdict_unchecked_growing`、`ruleSucceeded_entry`、`ruleFailed_recovery` は、[ADR 0028](../docs/adr/0028-label-safety-check.md) の個々の場合を示す。不変条件 2 については、`labels_reject_with_diagnostic` が、ラベルによる生成の失敗は `--Werror` のときだけ起き、そのとき警告が一件以上あることを示す。

ラベルの検査のモデルには、次の前提が残る。訪問済みの集合の鍵に使う Haskell の `show` と Lean の `repr` は、どちらも単射であるとする。`stronglyConnComp` の強連結成分は、規則名が重ならない文法では、モデルが到達可能性から求めるものと一致するとする。規則名の重複は `assemble` と `resolveImports` が拒否し、`expandTemplates` はインスタンスにどの規則とも異なる名前を付ける（TemplateExpansionWhole）。`isAlpha` と `isAlphaNum` は AssembleChars の表と一致するとする。Haskell の `Int` は溢れないとする。`stripExpr` はテンプレートの引数に入らないが、`labelWarnings` と `stripLabelsAs` が受け取る文法は `expandTemplates` の後なので、テンプレートの呼び出しを含まない。

[CheckGroupsModel.lean](CheckGroupsModel.lean) は、`Peg.Grammar.Check` の `check`、`checkRules`、`checkLibrary` と、`checkRules` の 15 個の検査のグループを、関数ごとに Lean の全域関数へ写したモデルである。`Peg.Grammar.Types` の `hasValue`、`countedItems`、`isUnit`、`valueRefs`、`isClassified` も写す。到達可能性の `reach` は、未訪問の名前の数、残りの根の数、スタックの長さの辞書式の順で減る量を持つ。空文字列を受理しうる規則を求める反復は、既知の集合が増えるだけであることを証明として持つ。左再帰は `stronglyConnComp` の代わりに `reach` で求める。どのループも `partial def` を使わない。

[CheckGroupsReach.lean](CheckGroupsReach.lean) は、これらのループが何を返すかを示す。`mem_reach_iff` は、`reach` が始めに見た名前と、そこから一本以上の辺でたどれる名前をちょうど返すことを示す。`mem_reachable_iff` は、これを到達可能性の検査に当てはめる。`mem_leftRecursiveRules_iff` は、規則が左再帰に入ることと、左端の呼び出しをたどって自分に戻ることが同値であることを示す。`nullableRulesWith_fixed` は、反復が段の不動点で止まることを示す。`countedItems_eq`、`allUnitCounted_eq`、`groupOne_eq`、`unitAlts_eq` は、モデルの補助関数が `Types.hs` の `filter` と `all` による定義に一致することを示す。

[CheckGroupsTheorems.lean](CheckGroupsTheorems.lean) は、各グループが何を拒否し何を受理するかを `*_nil` の定理で示す。たとえば `undefinedErrors_nil` は、誤りがないことを、参照と指示に書いた名前がすべて規則であることと同値にする。`repetitionErrors_nil` は、繰り返す式がどれも空文字列を受理しえないことと、`altErrors_nil` は、束縛、束縛名の重複、値のない選択肢、グループの中の束縛の条件と同値にする。`check_ok_iff` は、`check` が受理する文法を、ライブラリでなく、規則を持ち、15 個のグループのどれにも誤りがないものに限る。`check_rejects` は、どのグループの誤りも結果に入ることを示す。検査は最初の失敗で止まらず、すべてのグループを走らせて位置で整列する。不変条件 2 については、`check_error_ne_nil` が、拒否の診断が一件以上あることを示す。`generation_rejects` は、`generate` と `generateWithWarnings` の `Left` に診断が一件以上あり、生成テキストがないことを示す。

[check-check-groups.sh](check-check-groups.sh) がモデルを実装に結びつける。このスクリプトは、`Check.hs` 全体を [check-groups.source](check-groups.source) と照合し、`Types.hs`、`Grammar.hs`、`Templates.hs` の写した範囲と `Codegen.hs` の行を、`git hash-object` と `grep` で固定する。さらに、リポジトリのすべての `.hpeg`、そこから最初の規則を除いた文法、各診断を出すように書いた文法を [CheckGroupsProbe.hs](CheckGroupsProbe.hs) で読む。そのうえで、実際の `check` と `checkLibrary`、モジュール内の関数（`repetitionErrors`、`altErrors`、`bindingReferenceErrors`、`constructorErrors`、`syntaxNameErrors`、`hygieneErrors`、`leftRecursiveRules`、`nullableRulesWith`）の結果を、モデルの結果と比べる。

検査のグループのモデルには、次の前提が残る。`classify` の結果、`codeVariables`、`Data.Char.isUpper` と `toUpper` は、プローブが文法ごとに表として与える。`stronglyConnComp` の強連結成分から得る規則の集合は、規則名が重ならない文法では、左端の呼び出しで自分に戻れる規則の集合に一致するとする。`Data.List.sortOn` と `List.mergeSort` は、同じ順序による安定な整列なので、同じ列を返すとする。位置、長さ、数は自然数で写す。

[Pragmas.lean](Pragmas.lean) は、元ファイルの位置を表す `LINE` と `COLUMN`、生成先の位置を復元する行の形式を証明する。位置は自然数で、ファイル名の文字集合は文字列リテラルの定理と同じである。埋め込み本文は任意の文字列として扱う。生成器はユーザーが書いた行と衝突しない復元用マーカーを選ぶ。これにより、ユーザーの quasiquote 内に同じ形式の行があっても、その行を復元対象から除外できる。本文に含まれるコメントやレイアウトが周囲の Haskell の構文に及ぼす影響はこの定理の範囲外である。[check-pragmas.sh](check-pragmas.sh) は引用符を含むファイル名で実際に生成したアクションの位置と復元行を Lean の出力と照合し、モジュールを GHC で検査する。[check-no-record.sh](check-no-record.sh) は `NoTraditionalRecordSyntax` を指定した文法でメモ用ストアと設定のアクセスを含むモジュールを生成し、GHC と実行結果で検査する。

[RenderDeclarationsGHC.lean](RenderDeclarationsGHC.lean) は GHC 9.10.3 の型シグネチャと関数束縛の規則から、任意の子の導出と引数列を合成する。[RenderDeclarationBinders.lean](RenderDeclarationBinders.lean) は予約語の拒否、`_` の保持、メモ化キーの値と型の置換を扱う。[check-render-declaration-binders.sh](check-render-declaration-binders.sh) は組み立て時の二つの検査箇所と生成時の二つのキー箇所を実ソースで照合する。子の型・式の導出、文字列から GHC トークンへの対応、Haskell の遅延評価、任意の hpeg 構文木から名前の一覧を取り出す処理はこの定理の前提に残る。

[RenderComposition.lean](RenderComposition.lean) は、生成器が組み立てる部品を GHC 9.10.3 のモジュール規則に合成し、出力のトークン列に開始記号からの導出があることを示す。`generated_module_verbatim` と `generated_module_with_rules_verbatim` は、埋め込みブロックが import 宣言だけでなくトップレベル宣言も含む場合を扱う。`Codegen.render` は各ブロックを分割せずに、ソースの順で生成した import と生成した宣言のあいだに置く。そのため、トークン列は、生成した import、各ブロックのトークン、生成した宣言の順に並ぶ。[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) の埋め込みコードの前提は `verbatim_split` と二つの要素の前提になる。ブロックのトークンを連結した列は、import 宣言の並びとトップレベル宣言の並びをこの順に連ねたものであり、各要素が GHC の `importdecl` と `topdecl` から導出できる、という前提である。lexer に関する `initial`、`trace`、`tokens_match` の前提は残る。[check-render-composition.sh](check-render-composition.sh) は `render` の並び、`verbatimBlock` の定義、`grammarVerbatim` がブロックをソースの順に集める行を実ソースと照合する。さらに、import と宣言を含むブロックと規則の後のブロックを持つ文法から実際に生成したモジュールで、ブロックの行がこの位置にこの順で並ぶことを確かめ、GHC で検査する。

[RenderFinalize.lean](RenderFinalize.lean) と [RenderFinalizeModule.lean](RenderFinalizeModule.lean) は、RenderComposition.lean の結論を、公開の入口が実際に返すテキストまで延ばす。`Codegen.generate` が返すのは `render` の出力ではなく、それに `finalize` をかけたものである。`finalize` は、`fragment` と `verbatimBlock` が利用者のコードの後に置いた復帰マーカーの行を、生成したファイルの次の行を指す LINE プラグマに置き換え、末尾に改行を足す。RenderFinalize.lean は、`Data.Text.lines`、`Data.Text.unlines`、`finalize`、`freshRestoreMarker` が選ぶマーカー、`render` の先頭の行（二行のコメント、LANGUAGE プラグマ、OPTIONS_GHC プラグマ）をモデルにする。そのうえで、次の定理を示す。

- `finalize_prefix`: 改行で終わる前半に `finalize` をかけたものは、全体に `finalize` をかけたものの先頭である。
- `finalize_render_header`: 先頭のコメントとプラグマの行は、変わらずに同じ順でファイルの先頭に残る。
- `finalize_line_numbers`: i + 1 行目のマーカーを置き換えた LINE プラグマは、i + 2 行目を指す。

しかし、マーカーの行は GHC にとって字句のない行ではない。GHC 9.10.3 の layout 規則は、行頭にある未知のプラグマ（マーカー）の前に仮想のセミコロンを置く。LINE プラグマの前には置かない。そのため、マーカーを含む `render` の出力は、生成したファイルとは別の字句の列になり、構文解析に失敗する。RenderComposition.lean の lexer の前提を、GHC の lexer がマーカーを含むテキストを読んだ結果として読むと、マーカーを持つモジュールではこの前提が成り立たない。RenderFinalizeModule.lean の `generated_module_finalized`、`generated_module_with_rules_finalized`、`generated_module_with_rules_finalized_header` は、RenderComposition.lean の抽象の lexer に、`finalize` をかけてから GHC の lexer で読む関数（`finalizedLex`）を入れる。`finalize_prefix` により、lexer の前提は、生成したファイルの先頭の部分を GHC が読んだ結果についての前提になる。結論は、`finalize` の出力の字句の列が GHC のモジュールの開始記号から導出できることである。

これらの定理には、次の前提が残る。

- RenderComposition.lean の lexer の前提（`initial`、`trace`、`tokens_match`）。ただし、`render` の出力の各前半に `finalize` をかけたテキストについての前提である。
- 埋め込みコードの前提と、部品の導出の前提（`verbatim_split` など）。
- `source_ok`、`languages_ok`、`shown_ok`: 文法のファイル名、`%language` の引数、`show` した出力のファイル名は改行を含まない。`generate` は制御文字を含むファイル名を拒み、Peg.hpeg の指示の引数は `(!'\n' .)*` であり、`show` は改行をエスケープする。

[check-render-finalize.sh](check-render-finalize.sh) は、モデルを実装に結びつける。まず、`finalize`、`freshRestoreMarker`、`generate` の二回の `render`、`fragment` の定義、`runtimeVersions` の値を実ソースと照合する。次に、7 個の文法から実際にモジュールを生成する。文法は、埋め込みブロックと最初のマーカーと同じ行を持つもの、テンプレート、回復のラベル、`%language`、`%env`、`--export` で宣言を省いたもの、PegSyntax.hpeg である。各モジュールで、出力のファイルの次の行を指す LINE プラグマをマーカーに戻したテキストに Lean の `finalize` を実行し、結果が生成したファイルとバイト単位で一致することを確かめる。先頭の行が `headerLines` と一致することも確かめる。さらに、[check-ghc-parser-trace.sh](check-ghc-parser-trace.sh) が作る GHC 9.10.3 のトレーサーで、生成したファイルを構文解析の受理まで読めることを確かめる。マーカーに戻したテキストの字句の列が生成したファイルと異なるモジュールが少なくとも一つあることも確かめ、`finalizedLex` を使う理由が今も成り立つことを見張る。

生成したパーサーが呼ぶランタイム `Peg.Runtime.Internal` は、[ExtractRuntimeCore.hs](ExtractRuntimeCore.hs) が Lean に翻訳する。対象は、メモ化（`memo`、`memoArg`、`nomemo`、`evalBody`、`replay`、`logUndo` など）、制御の組み合わせ子（モナドの連接、`choice`、`many`、`skipMany`、`optional`、`andP`、`notP`、`labeledWith`、`expecting`）、端末（`lit`、`cls`、`anyChar`）、公開入口の `runParser` と `defaultConfig` である。抽出器は関数ごとに、ソースの行または行の並びを Lean の行へ写す辞書を持ち、辞書にない行があると翻訳を止める。行を消したり並べ替えたりした変更は翻訳を通るので、正しいかどうかは証明が決める。翻訳先の型と ST の参照のモデルは [RuntimeCore.lean](RuntimeCore.lean) に置き、抽出器はそこで写したデータ宣言をソースと照合する。

翻訳した定義についての定理は [RuntimeCoreProof.lean](RuntimeCoreProof.lean) にある。`invariant1_translated_memo_step` と `invariant1_translated_memoArg_step` は、翻訳した `memo` と `memoArg` が [MemoRecognition.lean](MemoRecognition.lean) の `memoStep` と同じ結果と状態を返すことを示す。`invariant1_translated_memo_off_same` は、メモ化の有無と hit・miss によらず、結果、最遠の失敗、依存、エラーの記録が一致することを示す。回復しない構文解析では、連接、選択、`optional`、ラベル、先読みの結果が [LabelPropagation.lean](LabelPropagation.lean) のフレームと先読みに一致し、`many` と `skipMany` は 1 回の反復ごとの式を満たす。端末の `lit`、`cls`、`anyChar` は、スカラー値の境界で `ConcreteTerminal.matchTerm` と同じ入力を受理する。`expecting` は翻訳するが、定理はない。`invariant1_translated_runParser_entry` は、`runParser` が値を返すことと、開始規則の結果を `PublicParsing.entry` に渡して成功することが同値であることを示す。これらの定理により、`check-public-parsing.sh` と `check-memo-recognition.sh` にあったランタイムの SHA-256 の照合を外した。

[check-runtime-core.sh](check-runtime-core.sh) は翻訳と証明を検査し、さらに変異で検査の強さを確かめる。辞書にない五つの変更は翻訳で拒否される。`replay` の失敗の再生、`evalBody` の失敗の記録の初期化、`notP` の失敗の記録の復元、`runParser` の入力末尾の期待の追加の四つを消した変更は、翻訳を通るが証明で拒否される。生成した `parse` が `runParser` を `defaultConfig` で呼ぶことは、[check-public-parsing.sh](check-public-parsing.sh) が生成ソースの該当行と照合する。

ただし、ランタイムの翻訳には次の前提が残る。

- ST は世界の状態の遷移として写し、`newCtx` が作る参照は互いに別の固定の欄とする。メモ表は生成したストアの中を指す参照とし、miss の後に表を読み戻す定理はその参照のレンズ則を仮定する。
- `Data.Set`、`Data.IntSet`、`Data.IntMap`、`Data.Map` は所属と検索の関数で写す。
- `Text` は Unicode スカラー値の UTF-8 符号化とし、オフセットを 0 に正規化した Lean の `String` で写す。`T.pack` は恒等、`TU.lengthWord8` はバイト長、`TA.unsafeIndex` は範囲内のバイトの読み出し、`TU.iter` はバイト位置から始まるスカラー値の復号とする。最後の二つは [CheckUtf8Runtime.hs](CheckUtf8Runtime.hs) が実ライブラリで確かめる。
- 位置はバイトオフセットのまま扱い、行と列への変換は [LineIndex.lean](LineIndex.lean) が別に証明する。
- `ctxLogs` に積む取り消しの動作は消して写す。取り消しを実行する `endIteration` と、それを呼ぶ `memoLR` は翻訳しない。メタ文法のパーサーが `memoLR` を使わないことは [check-memo-meta.sh](check-memo-meta.sh) が確かめる。
- メモ化の定理は、回復と計数が無効であること、成長の反復が走っていないこと（`ctxLogs` が空）、規則本体が失敗の記録と依存を空にして始めたときに同じ結果を返すこと（`BodySpec`）、表の項目が本体を評価した結果に等しいこと（キャッシュの不変条件）を仮定に置く。
- `lit` の比較の繰り返しは、Lean の停止性の証明のために `k < n` の分岐を足す。`go 0` から呼ぶかぎり、足した分岐には到達しない。
- 繰り返しの `many` と `skipMany` の定義には Lean の `partial_fixpoint` を使う。

ソースの抽出・照合スクリプトと、そこで使う Haskell の構文の読み取り方は信頼する前提である。

[CertifiedPublicFiles.lean](CertifiedPublicFiles.lean) は、`Peg.hpeg` と `PegSyntax.hpeg` の現行の内容を `parseTops` のモデルが受理することを証明する。`parseTops` はどの hpeg ファイルも `Peg.hpeg` の文法 (モード `false`) で読むので、`invariant1_public_syntax_as_peg` は `PegSyntax.hpeg` をこの文法で受理することを示す。`invariant1_public_syntax` は、`PegSyntax.hpeg` を自身の規則の表 (モード `true`) で受理することを示す。各ファイルの導出の証明書は [SplitMetaFile.lean](SplitMetaFile.lean) が項目ごとに書き出し、[check-file-items.sh](check-file-items.sh) が検査する。[CheckItemSources.lean](CheckItemSources.lean) は、証明書の入力が実際のファイルの内容と一致することを確かめる。

[FileTops.lean](FileTops.lean) は、`parseTops` が成功したときに返す `[Top]` の形を特徴づける。FileEntry.lean と TotalFile.lean は成功と導出の同値を示すが、開始結果の値を `()` に消している。生成したパーサーでは、`File` の値は `many TopItem` が返すリストであり、`TopItem` は `TopOne` の値を返し、`TopOne` は最初に成功した選択肢の値を返す。`Chain` はこの繰り返しを認識器の導出の上に写し、`Tops` は `File` 全体を写す。`invariant1_tops_iff` は、項目の列を持つ導出があることと、認識器が入力全体を受理することの同値を示す。`invariant1_tops_unique` は、項目の列が一つに決まることを示す。`invariant1_tops_linked` は、項目が先頭の `Ws` の後から順に入力を消費して末尾で終わり、各項目がその種類の選択肢を通った `TopItem` の呼び出しであることを示す。`invariant1_parseTops_value` は、値を運ぶ開始結果で公開入口が `ts` を返すことと、`ts` が導出の値の列であることの同値を示す。`invariant1_parseTops_shape` は、その列が項目ごとに一つの値を項目の順に持ち、i 番目の値が i 番目の項目の選択肢の、その開始位置での値であることを示す。

[check-file-tops.sh](check-file-tops.sh) は、このモデルを実装に結びつける。まず、生成した `File`、`TopItem`、`TopOne` の定義（LINE プラグマを除く）とランタイムの `many` を `git hash-object` で固定する。次に、[FileTopsProbe.hs](FileTopsProbe.hs) が、`packages/` と `editors/` のすべての .hpeg ファイルと境界の入力について、実際の `parseTops` が返す `Top` の種類、順序、件数、位置を書き出す。[FileTopsProbe.lean](FileTopsProbe.lean) は、`runTops_sound` で `Tops` に結びつけた実行可能なモデルから同じものを書き出し、両者を比べる。`conformance/` の文法は比べない。Lean のモデルはメモ化なしで動くので、その中には数分かかるものがあるからである。残る前提は二つある。一つは、`Verbatim`、`Directive`、`Declaration` の値を位置の関数 `value` として抽象したことである。各 `Top` の中身（埋め込みブロックの本文、ディレクティブの引数、規則の選択肢）は、このモジュールでは特徴づけない。もう一つは、規則の本体について、ExtractConcreteTerminals.hs と ExtractSelfHostedFile.hs の翻訳を信頼することである。

[Audit.lean](Audit.lean) は、一覧に挙げたモジュールと Audit.lean 自身の定理ごとに依存する公理を列挙し、Lean 標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理を使うと失敗する。すべてのモジュールを作った後で動かすため、[check.sh](check.sh) の最後に置く。[check-audit-coverage.sh](check-audit-coverage.sh) は、定理を持つ手書きのモジュールと、定理を書き出す生成器が作るモジュールが、この一覧にすべて載っていることを確かめる。SplitMetaFile.lean が書き出す項目ごとの証明書は、CertifiedPublicFiles.lean の定理の前提になるので、その定理の公理の一覧に含まれる。

## 実行方法

リポジトリのルートで次のコマンドを実行する。
GHC と Cabal はプロジェクト指定の版を使う。
生成 Haskell の構文導出には Happy 2.1.7 が必要である。
`happy` が PATH 上にない場合は実行ファイルを `HAPPY` に指定する。
GHC 9.10.3 の `compiler/GHC/Parser.y` を `GHC_PARSER_Y` に、`compiler/GHC/Parser/Lexer.x` を `GHC_LEXER_X` に指定するか、
`ghc-9.10.3-release` タグを持つ GHC チェックアウトを `GHC_SOURCE` に指定する。
検査スクリプトは文法ファイルの SHA-256 を照合する。
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

二つの生成モジュールについて、Happy が GHC の文法から生成したパーサーで全文を読み、
各 shift と reduce を記録する。Lean は各 reduce の右辺をスタックと照合し、
全トークンを消費して開始記号だけが残ることを検査する。
GHC が暗黙のレイアウトを閉じるために挿入する `error` トークンは、元のトークン列と区別する。
ソース文字列からトークンへの変換には GHC の lexer を使う。
