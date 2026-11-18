# Lean による peg-hs の検証

このディレクトリは、[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) に基づき、hpeg の構文解析、拒否条件、生成する Haskell の構文を Lean 4 で検証する証明と、その証明を実装に結びつける検査を置く。
この文書は、何を証明したか、証明がどの前提に依存するか、前提をどの検査が見張るかを、公開の入口から順にたどれるように書く。
数とファイルの行は、この文書を書いた時点の main のファイルから取った。

## 用語

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) は、次の三つの不変条件を定める。

1. 任意の有限の hpeg テキストについて、`parseTops` が成功することと、入力全体に対する構文導出が存在することは同値である。`Peg.hpeg` と `PegSyntax.hpeg` の現行の内容はどちらも導出を持つ。
2. 任意の対象入力で生成処理は停止する。構文違反または検査対象の拒否条件が成立すれば、一件以上の診断を返し、生成テキストを返さない。警告を伴う結果では、内側の `generationModule` まで評価して判定する。
3. 埋め込み Haskell が挿入箇所の構文上の前提を満たす任意の入力で、生成が成功すれば、出力テキスト全体に対象 Haskell モジュールとしての構文導出が存在する。

公開の入口は、利用者が呼ぶ四つの関数である。
`parseTops` は `packages/peg-grammar/src/Peg/Grammar/Parser.hs` にあり、hpeg のテキストを最上位の項目の列に読む。
`generateWithWarnings`、`generate`、`generateFromSource` は `packages/peg-codegen/src/Peg/Codegen.hs` にあり、hpeg のテキストか文法から、診断か生成したモジュールのテキストを返す。

実装との対応のしかたは、次の四種類に分ける。

| 対応のしかた | 意味 |
| --- | --- |
| 検査付きの翻訳 | 抽出器が Haskell か hpeg のソースから Lean の定義を書き出す。抽出器は、扱えない構文に出会うと失敗する。定理は、書き出した定義について成り立つ。 |
| 固定ソースの diff とプローブ | Lean のモデルは手で書く。モデルが写すソースの範囲を、`diff` か `git hash-object` で固定する。プローブが、同じ入力で実関数とモデルの結果を比べる。 |
| 証明書 | 検査が具体的な入力（メタ文法のファイル、GHC のトレース）から導出の証明書を書き出し、Lean のカーネルが検査する。定理は、その入力についてだけ成り立つ。 |
| モデルだけ | Lean のモデルにだけ定理があり、ソースとの結び付けはない。 |

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) は、独立に書いたモデルだけに定理がある段を「モデルを検証済み」と報告すると定める。
この文書では、固定ソースの diff とプローブで結んだ段と、モデルだけの段を「モデルを検証済み」と書く。
プローブは有限個の入力でしか比べないので、モデルと実装の一致は経験的な根拠にとどまるからである。
検査付きの翻訳について定理がある段は「翻訳を検証済み」、証明書がある段は「証明書を検証済み」と書く。
Haskell の関数だけを動かして結果を確かめ、Lean のモデルと比べない検査は、プローブと呼ばず「実装だけの検査」と呼ぶ。

この文書では、次の語も使う。

- 燃料: 再帰の深さの上限として関数に渡す自然数。燃料が尽きると結果を返さない。十分な燃料で結果が出ることを定理で示す。
- 変異: 検査の強さを確かめるために、ソースや証明書を一か所だけ書き換えたもの。検査は、変異を翻訳か証明で拒否することを確かめる。
- トレース: GHC の lexer と parser を動かし、parser に渡した字句の番号と各 shift と reduce を記録したもの。トレースを取るプログラムをトレーサーと呼び、check-ghc-parser-trace.sh が作る。
- fixture: リポジトリにコミットした、生成器の出力のファイル。`scripts/regen-fixtures.sh` が作り直す。

前提は、Lean の定理が仮定に置き、証明しない命題である。
前提の一覧は「残る前提」の節にまとめ、各前提に番号を付ける。

## 公開の入口から結論までの定理の連なり

最上位の定理は [PublicGeneration.lean](PublicGeneration.lean) と [PublicGenerationGHC.lean](PublicGenerationGHC.lean) にある。
PublicGeneration.lean は、公開の入口を各段のモデルの合成として定義し、不変条件 1〜3 を各段の定理から導く。
各段の定義は次のとおりである。

| 段 | Lean の定義 | 実装 |
| --- | --- | --- |
| 構文解析と組み立て | `parse`（PublicGeneration.lean:294）。翻訳したランタイムで `File` を走らせた開始結果 `runtimeStart`（SelfHostedRuntime.lean:946）に、検査付きの翻訳 `translatedGrammar` と `translatedAssemble` を当てる | `parseGrammar src = parseTops src >>= assemble` |
| import の解決 | `resolve`（PublicGeneration.lean:300） | `resolveImports` |
| テンプレートの展開 | `Inputs.expand`（PublicGeneration.lean:272） | `expandTemplates` |
| 規則の検査 | `checkStage`（PublicGeneration.lean:307） | `check` |
| テンプレートの注記 | `notes`（PublicGeneration.lean:312） | `templateNotes` |
| ラベルの除去と警告 | `stripAs`（PublicGeneration.lean:225）、`warningFor`（PublicGeneration.lean:315） | `stripLabelsAs`、`labelWarnings` |
| 内側の生成 | `inner`（PublicGeneration.lean:322） | `generate` |
| 公開の入口 | `generateWithWarnings`（PublicGeneration.lean:335）、`publicModule`（PublicGeneration.lean:343）、`generateFromSource`（PublicGeneration.lean:347） | `generateWithWarnings`、CLI が書き出す `generationModule`、`generateFromSource` |

段と段の間を流れる文法は、共通の型 `Grammar`（PublicGeneration.lean:111）で表す。
式と位置には [LabelCheckModel.lean](LabelCheckModel.lean) の型を使う。
各段のモデルは `Grammar` の射影を読む。
`toLabel` はラベルの検査の文法、`toCheck` は `check` の文法、`toTemplate` はテンプレート展開の文法への射影である。
`toLabel_stripAs`（PublicGeneration.lean:235）は、`stripAs` が射影 `toLabel` の上で `stripLabelsAs` と可換であることを示す。
各段のモデルと実装の関係のうち合成できないものは、構造体 `Premises`（PublicGeneration.lean:360）の四つの欄 `Premises.expandRefines`、`libraryParseNonempty`、`libraryAssembleNonempty`、`assembleAgrees` に置く（前提 A1〜A3）。

### 不変条件 1

不変条件 1 の連なりは、生成の入口から `parseTops` を通り、翻訳したランタイムでの `File` の実行を経て、認識器の導出 `FileResult` まで下りる。
導出 `FileResult`（MetaExecution.lean:34）は、Peg.hpeg の規則本体を翻訳した文脈の上の帰納的な判定関係 `Derives` である。

| 順 | 定理か定義 | 場所 | 示すこと |
| --- | --- | --- | --- |
| 1 | `invariant1_generateWithWarnings` | PublicGeneration.lean:509 | 生成テキストが返るなら、`parseTops` が入力全体を導出し（`FileTops.ParsesTo`）、`assemble` のモデルがその項目を受理する。 |
| 2 | `invariant1_no_derivation` | PublicGeneration.lean:519 | 入力全体の導出がなければ、一件以上の診断を返す。 |
| 3 | `invariant3_visible_success_iff` | Pipeline.lean:211 | 公開の結果が生成テキストなら、構文解析の段は成功している。 |
| 4 | `invariant1_parse_iff` | PublicGeneration.lean:495 | `parseGrammar` の成功は、入力全体の導出と `assemble` の受理と同値である。 |
| 5 | `invariant1_translated_grammar_assembled` | PublicEntryProof.lean:27 | 翻訳した `parseGrammar` の成功は、開始規則が入力の末尾で成功し、`assemble` が誤りを返さないことと同値である。 |
| 6 | `invariant1_parseTops_iff` | PublicParsing.lean:28 | `parseTops` の入口は、開始規則の結果が入力のバイト長で終わるときだけ値を返す。 |
| 7 | `invariant1_parseTops_value` | FileTops.lean:372 | `parseTops` が `ts` を返すことと、`ts` が入力全体の導出の値の列であることは同値である。 |
| 8 | `invariant1_parsesTo_iff`、`invariant1_tops_iff` | FileTops.lean:333、FileTops.lean:302 | 値の列を持つ導出があることと、認識器が入力全体を受理すること（`FileResult false input (.ok 0 env)`）は同値である。 |
| 9 | `invariant1_runtimeStart_eq` | SelfHostedRuntime.lean:955 | `parse` が読む開始結果 `runtimeStart` は、`FileResult` の返答から作る FileTops の開始結果 `startTops` に等しい。 |
| 10 | `invariant1_runtimeResult` | SelfHostedRuntime.lean:920 | `runParser defaultConfig` が作る文脈と世界から、翻訳したランタイムで `File` を走らせた結果は、`FileResult` のある返答と一致する（同じ残りの入力と環境をそのバイト位置で返すか、同じラベルとメッセージを投げるか、失敗する）。 |
| 11 | `invariant1_exec_agrees` | SelfHostedRuntime.lean:560 | 燃料ごとに、規則本体のランタイムでの実行 `exec` は、どの世界から始めても、導出の文脈での実行 `runFuel` と一致する結果を返す。 |
| 12 | `invariant1_file_result` | MetaExecution.lean:38 | どの入力にも `FileResult` の返答がちょうど一つある。 |
| 13 | `recognizeFile` | TotalFile.lean:23 | その返答を燃料の探索で求める全域の関数である。手順 9 の右辺が使う。 |
| 14 | `invariant1_strict_rule_table` | SelfHostedFileProof.lean:131 | 生成した `SelfHosted.hs` の規則を翻訳した本体の表は、導出の文脈の規則の表と同じものである。 |

`parseTops` だけを入口にした場合は、`invariant1_total_public_entry`（TotalFile.lean:70）が、翻訳した入口の成功と `FileResult` の受理の同値を示す。
不変条件 1 の後半は [CertifiedPublicFiles.lean](CertifiedPublicFiles.lean) が示す。
`invariant1_public_peg`（CertifiedPublicFiles.lean:15）は、`Peg.hpeg` の現行の内容を受理することを示す。
`parseTops` はどの hpeg ファイルも `Peg.hpeg` の文法（モード `false`）で読むので、`invariant1_public_syntax_as_peg`（CertifiedPublicFiles.lean:25）は `PegSyntax.hpeg` をこの文法で受理することを示す。
`invariant1_public_syntax`（CertifiedPublicFiles.lean:19）は、`PegSyntax.hpeg` を自身の規則の表（モード `true`）で受理することを示す。

この連なりの定理は、構造体 `Premises` 全体を仮定に取る。
そのうち証明が使う欄は A3 だけである。
ほかに、前提 A5、M1〜M3、R1〜R7、I1、X1 が残る（「残る前提」の節）。

### 不変条件 2

不変条件 2 の連なりは、各段が失敗するときに診断が空でないことを示す定理を、段のつなぎ方の定理に渡して合成する。

| 順 | 定理 | 場所 | 示すこと |
| --- | --- | --- | --- |
| 1 | `invariant2_generateWithWarnings` | PublicGeneration.lean:464 | `generationModule` まで評価した公開の結果は、一件以上の診断か生成テキストである。 |
| 2 | `invariant2_generate` | PublicGeneration.lean:453 | `generate` は、一件以上の診断か生成テキストを返す。 |
| 3 | `invariant2_generateFromSource` | PublicGeneration.lean:475 | `generateFromSource` は、一件以上の診断か生成テキストを返す。 |
| 4 | `invariant2_diagnosticOrModule` | Pipeline.lean:187 | 各段が失敗時に空でない診断を返し、注記が診断を空にしなければ、`generateWithWarnings` の公開の結果は空でない診断か生成テキストである。 |
| 5 | `diagnosticOrModule`、`failureNonempty` | InnerGeneration.lean:189、InnerGeneration.lean:144 | 内側の `generate` について、4 と同じことを示す。 |
| 6 | `parse_error_nonempty` | PublicGeneration.lean:370 | 構文解析と組み立ての失敗には診断がある。`invariant2_diagnosticSortOn_length`（PublicEntryProof.lean:177）により、整列は診断の数を変えない。 |
| 7 | `resolve_error_nonempty` | PublicGeneration.lean:395 | import の解決の失敗には診断がある。`invariant2_resolve_error_nonempty`（ImportResolution.lean:337）を使う。 |
| 8 | `expand_error_nonempty` | PublicGeneration.lean:405 | テンプレート展開の失敗には診断がある。`expandTemplates_whole`（TemplateExpansionWhole.lean:1298）を使う。 |
| 9 | `check_error_nonempty` | PublicGeneration.lean:432 | 規則の検査の失敗には診断がある。`check_error_ne_nil`（CheckGroupsTheorems.lean:68）を使う。 |
| 10 | `notes_nonempty` | PublicGeneration.lean:446 | テンプレートの注記は空でない診断を空にしない。`invariant2_templateNotes_nonempty`（TemplateQueue.lean:118）を使う。 |
| 11 | `inner_error_nonempty` | PublicGeneration.lean:458 | 内側の生成の失敗には診断がある。 |

停止性は、各段のモデルが Lean の全域の定義であることから得る。
Lean は、`partial def` と `partial_fixpoint` を使わない定義に停止の証明を求める。
このディレクトリの `.lean` ファイルは `partial def` を使わない。
`partial_fixpoint` は、ExtractRuntimeCore.hs が書き出すランタイムの `many` と `skipMany` だけが使い（前提 R6）、生成器の段のモデルは使わない。
停止の理由が自明でない段には、次の定理がある。

- 構文解析: `recognizeFile`（TotalFile.lean:23）は、`invariant1_file_result` が返答の存在を示すので、燃料の探索が終わる。
- テンプレート展開: `expandTemplates_whole`（TemplateExpansionWhole.lean:1298）は、`drain` の再帰を写した関係 `Drain` と型の反復を写した関係 `Go` に、導出が存在して一つに決まることを示す。`invariant2_drain_terminates`（TemplateQueue.lean:65）と `invariant2_pass_count`（TemplateQueue.lean:97）は、待ち行列と外側の反復の上限を示す。
- ラベルの検査: `run_terminates`（LabelCheckTermination.lean:750）は、燃料 `keyUniverse.length + 1` で判定が出ることを示す。`run_mono`（LabelCheckTermination.lean:907）は、それより多い燃料でも結果が変わらないことを示す。
- 規則の検査: CheckGroupsModel.lean の `reach` は、減る量を持つ全域の関数である。`mem_reach_iff` などの性質は CheckGroupsReach.lean が示す。

Haskell の実装が停止することは、モデルとの対応を通してだけ言える。
したがって、この連なりには、前提 A1、A2、A5、構文解析の段の前提（M、R の各前提）、ほかの段の前提（T、L、C、I の各前提）、X1 が残る。

### 不変条件 3

不変条件 3 の連なりは、生成テキストを `render` と `finalize` の合成として特徴づけ、GHC の lexer で読んだ字句の列を GHC のモジュールの開始記号から導出する。

| 順 | 定理 | 場所 | 示すこと |
| --- | --- | --- | --- |
| 1 | `invariant3_generateWithWarnings_ghc` | PublicGenerationGHC.lean:67 | 生成テキストを GHC の lexer で読んだ字句の列は、GHC のモジュールの開始記号（非終端記号 0）から `layoutGrammar productions` で導出できる。前提 `renderShape`（PublicGenerationGHC.lean:69）を置く。 |
| 2 | `invariant3_generateWithWarnings_text` | PublicGeneration.lean:534 | 生成テキストは、テンプレート展開と `check` を通った文法 `final` の `render` の出力に `finalize` を当てたものである。マーカーは、最初の `render` から `selectMarker` が選ぶ。`final` はテンプレート、テンプレートの呼び出し、テンプレートへの参照を含まない（`TemplateExpansionWhole.Accepted`）。 |
| 3 | `invariant3_public_render_iff` | InnerGeneration.lean:118 | 公開の結果が生成テキストであることと、各段が成功し、そのテキストが `finalize` の出力であることは同値である。 |
| 4 | `expand_ok_accepted` | PublicGeneration.lean:418 | `expandTemplates` が成功すれば、その結果は `expandTemplates_whole` の受理の形を持つ。 |
| 5 | `finalized_module_derives` | PublicGenerationGHC.lean:52 | `render` の出力が `ModuleShape`（PublicGenerationGHC.lean:33）を満たせば、`finalize` の出力の字句の列は導出を持つ。 |
| 6 | `generated_module_with_rules_finalized` | RenderFinalizeModule.lean:79 | RenderComposition.lean の結論を、`finalize` の出力まで延ばす。lexer に `finalizedLex`（`finalize` をかけてから GHC の lexer で読む関数）を入れる。 |
| 7 | `finalize_prefix` | RenderFinalize.lean:220 | 改行で終わる前半に `finalize` をかけたものは、全体に `finalize` をかけたものの先頭である。 |
| 8 | `generated_module_with_rules_verbatim` | RenderComposition.lean:743 | 生成した import、埋め込みブロック、生成した宣言を並べた字句の列は、モジュールの開始記号から導出できる。 |
| 9 | `generated_module_verbatim`、`generated_parts_valid` | RenderComposition.lean:712、RenderComposition.lean:681 | 8 の部品である。生成した宣言の一覧が各宣言の導出を持つことを含む。 |
| 10 | `generated_with_verbatim`、`parse_module_source` | RenderModuleGHC.lean:539、RenderModuleGHC.lean:579 | モジュールの枠（`module`、export の一覧、`where`、本体）の導出である。 |
| 11 | `invariant3_layout_tokens` | LayoutDerivation.lean:24 | トレースの区切りの証明書から、レイアウトの `error` トークンを消した文法での導出を作る。 |

`Derives`（HaskellDerivation.lean:14）は、文脈自由文法の通常の導出である。
文法 `productions` は、GHC 9.10.3 の `Parser.y` から Happy が作った表を ExtractHappyGrammar.hs が翻訳した GHCGrammar.lean にある。
GHCGrammar.lean は検査のときに生成し、リポジトリには置かない。

コミットした三つの生成物については、埋め込みコードの前提なしで不変条件 3 を示す（「コミットした生成物の証明書」の節）。
この連なりには、前提 A1、A4、A5、G1〜G9、E1、X1 が残る。
定理は構造体 `Premises` 全体を仮定に取り、証明は `expand_ok_accepted` を通して A1 を使う。

## 段ごとの証明と実装との対応

次の表は、段ごとに、主な Lean のモジュール、実装との対応のしかた、報告、主な検査をまとめる。
段の名前が対象の機能を表し、機能の細部と残る前提の番号は、表の後の各節と「残る前提」の節に書く。

| 段 | 主な Lean のモジュール | 対応のしかた | 報告 | 主な検査 |
| --- | --- | --- | --- | --- |
| メタ文法の規則本体と認識 | MetaExecution、EnvironmentEval、EnvironmentDerivation、SelfHostedFileProof、SelfHostedRuntime、SelfHostedMemo、ScopedEnv、ConcreteTerminal、Strict で始まるモジュール | 検査付きの翻訳（ExtractSelfHostedFile.hs、ExtractConcreteTerminals.hs、ExtractRuntimeChoice.hs、ExtractVerbatimBody.hs） | 翻訳を検証済み | check-strict-file.sh、check-concrete-terminals.sh |
| 呼び出しの整礎性 | CallOrder、RecursiveEval | 検査付きの翻訳（ExtractCallOrder.hs） | 翻訳を検証済み | check-call-order.sh |
| 開始規則と空白 | File、Consumption、Whitespace、Lexical | `File` は検査付きの翻訳（ExtractFile.hs）。空白とコメントは規則の行を `grep` で固定する | 翻訳を検証済み（File）、モデルを検証済み（Whitespace、Lexical） | check.sh、check-whitespace.sh、check-lexical.sh |
| PEG の式の意味 | Parsing | 固定ソースの diff とプローブ（非回復時のランタイムの一部と比べる） | モデルを検証済み | check-core.sh |
| `parseTops` の入口 | PublicParsing、PublicEntryProof、FileEntry、TotalFile | 検査付きの翻訳（translate-public-entry.awk） | 翻訳を検証済み | check-public-parsing.sh |
| `parseTops` の値 | FileTops | 固定ソースの diff とプローブ | モデルを検証済み | check-file-tops.sh |
| メタ文法の現行の内容 | CertifiedPublicFiles、SplitMetaFile、ConcreteFileCertificates | 証明書（ファイルの内容を照合する） | 証明書を検証済み | check-file-items.sh、check-file-certificates.sh |
| ランタイム | RuntimeCore、RuntimeCoreProof、RuntimeForms、MemoRecognition、MemoTables、MemoTrace、LabelPropagation | 検査付きの翻訳（ExtractRuntimeCore.hs） | 翻訳を検証済み | check-runtime-core.sh、check-memo-tables.sh、check-memo-meta.sh |
| 位置の行と列 | LineIndex | 固定ソースの diff（line-of.source）と実装だけの検査（CheckLineIndex.hs） | モデルを検証済み | check.sh |
| `assemble` の検査 | AssembleValidation、AssemblePredicates、AssembleChars、AssembleBindings、NestedBindings | 固定ソースの diff とプローブ | モデルを検証済み | check-assemble-validation.sh、check-assemble-predicates.sh、check-assemble-validation-helpers.sh |
| 指示の引数 | SimpleEscapeProof、TabstopProof、DirectiveArityProof、DirectiveCommentProof、DirectiveDecode | 検査付きの翻訳（ExtractSimpleEscapes.hs、ExtractTabstop.hs、ExtractDirectiveArity.hs、ExtractDirectiveComment.hs） | 翻訳を検証済み | check.sh、check-strict-file.sh、check-directive-comment.sh |
| import の解決 | ImportResolution | 固定ソースの diff とプローブ | モデルを検証済み | check-import-resolution.sh |
| テンプレートの展開 | TemplateExpansionWhole、TemplateSubstitution、TemplateQueue、TemplateExpansionFresh | 固定ソースの diff とプローブ | モデルを検証済み | check-template-expansion-whole.sh、check-template-queue.sh、check-template-expansion-fresh.sh、check-template-substitution.sh |
| 規則の検査 | CheckGroupsModel、CheckGroupsReach、CheckGroupsTheorems、RuleRejection、Nullable、Reachable、Signatures、Guard | 固定ソースの diff とプローブ。署名は ExtractSignatures.hs、ファイル名の検査は check-guard.sh が翻訳する | モデルを検証済み（署名とファイル名の検査は翻訳を検証済み） | check-check-groups.sh、check-rule-rejection.sh、check-rule-rejection-nullable.sh、check-nullable.sh、check-reachable.sh、check-guard.sh |
| ラベルの検査 | LabelCheckModel、LabelCheckCharSet、LabelCheckTermination、LabelCheckTheorems、LabelsTranslated（生成）、LabelsTranslatedProof | `stripLabels` と `stripLabelsAs` は GHC の構文木からの検査付きの翻訳（TranslateHaskell.hs）。`labelWarnings` は固定ソースの diff とプローブ | 翻訳を検証済み（`stripLabels`、`stripLabelsAs`）、モデルを検証済み（`labelWarnings`） | check-translate-labels.sh、check-label-check.sh |
| 段のつなぎ | Pipeline、InnerGeneration、PublicGeneration、PublicGenerationGHC | 固定ソースの diff（Pipeline は実装だけの検査 PipelineProbe.hs も） | モデルを検証済み | check-pipeline.sh、check-inner-generation.sh、check-public-generation.sh |
| `render` の合成 | RenderComposition、RenderModuleGHC、RenderDeclarationsGHC、RenderRuleBodyGHC、RenderExpressionGHC、RenderPrimitiveChoice、RenderPrimitiveDo、RenderPrimitiveDoGHC、RenderPrimitiveStatement、RenderModuleNames、RenderDeclarationBinders、RenderExpression、RenderExpressionBoundary | 固定ソースの diff とプローブ（生成したモジュールを GHC でトレースするか検査する） | モデルを検証済み | check-render-composition.sh ほか check-render-*.sh |
| モジュールの先頭とリテラル | Header、Literal、Pragmas | 固定ソースの diff とプローブ（GHC の `Show` と比べる） | モデルを検証済み | check-header.sh、check-literal.sh、check-pragmas.sh |
| `finalize` | RenderFinalize、RenderFinalizeModule | 固定ソースの diff とプローブ | モデルを検証済み | check-render-finalize.sh |
| 式の印字と lexer の橋 | RenderPrinting、RenderExpressionLexer | 固定ソースの diff とプローブ | モデルを検証済み | check-render-printing.sh、check-render-expression-lexer.sh |
| GHC の文法 | HaskellDerivation、LayoutDerivation、TraceChunks、GHCGrammar（生成） | 検査付きの翻訳（ExtractHappyGrammar.hs） | 翻訳を検証済み | check-ghc-derivations.sh、check-ghc-parser-trace.sh |
| コミットした生成物 | CommittedModuleDerivations、DerivationPeg、DerivationPegSyntax、DerivationExtensions（三つとも生成） | 証明書（GHC のトレースから作る） | 証明書を検証済み | check-ghc-parser-trace.sh、check-ghc-derivations.sh、check-trace-language.sh |

以下の節は、段ごとの定理、対象の機能、検査を述べる。

### 構文解析

[Parsing.lean](Parsing.lean) は、有限の式の実行と帰納的な判定関係の同値（`invariant1_core_iff`、Parsing.lean:247）と、深さ 256 の境界（`invariant1_depth_boundary`、Parsing.lean:256）を証明する。
[check-core.sh](check-core.sh) は、非回復時のランタイムの一部とモデルを [CoreProbe.hs](CoreProbe.hs) と [CoreProbe.lean](CoreProbe.lean) で比較する。
[Lexical.lean](Lexical.lean) は空白とコメントのモデルを検査し、[check-lexical.sh](check-lexical.sh) は実メタ文法の `InlineSp` と `Comment` の行を照合する。

[File.lean](File.lean) は、先頭の `Ws` に続いて、入力を消費する `TopItem` の導出を有限回つないで末尾に達することと、開始規則 `File` が成功することの同値を証明する。
[ExtractFile.hs](ExtractFile.hs) は、`Peg.hpeg` と `PegSyntax.hpeg` から開始規則と、その呼び出し先のうち 11 規則の認識に使う演算子を翻訳する。
それぞれの翻訳について、空入力で `Ws` が成功し、`TopItem` がラベルなしで失敗し、`File` が空入力を受理することを Lean が検査する。
したがって、各メタ文法に開始規則の定理を適用するとき、空入力での失敗を仮定に置く必要がない。
この翻訳では束縛とキャプチャの値を捨て、成功時に値を作るアクションは入力位置を変えないと仮定する（前提 M2）。
展開しない規則呼び出しと意味述語には出現箇所ごとに独立の PEG 式を与え、どの式を与えても定理が成り立つことを検査する。
[check.sh](check.sh) は、Peg.hpeg と PegSyntax.hpeg の規則を四通りに書き換え、どれも Lean が拒否することを確かめる。

[Consumption.lean](Consumption.lean) は、PEG 式の成功後に残る文字列が、元の入力の接尾辞であることを示す。
この性質から、各メタ文法の `File` の成功を、先頭の空白を読み終えた位置から非空の接頭辞を項目として順に消費し、末尾に達する導出と結びつける。

[CallOrder.lean](CallOrder.lean) は、同じ入力位置で呼び出されうる規則を調べ、呼び出しのたびに規則の順位が下がることを証明する。
先読みの中で呼ぶ規則と、失敗後に元の位置に戻って試す選択肢も含める。
先に文字を消費すれば残りの入力が短くなる。
この二つを組み合わせて、呼び出し関係が整礎であることを証明する（`invariant1_call_wellFounded`、CallOrder.lean:122）。
[ExtractCallOrder.hs](ExtractCallOrder.hs) は、両メタ文法の全規則から、文字消費と呼び出しに関係する演算子を抽出する。
空文字の受理可能性と順位は抽出器が候補を作り、Lean が各演算子を走査して全辺を検査する。
この証明では、意味述語を文字を消費しない演算として扱う（前提 M1）。

[Whitespace.lean](Whitespace.lean) は、各実メタ文法から取り出した `Ws` が任意の入力でどこまで読み進むかを証明する。
`SpaceChar` の捕捉と意味述語を一文字の文字クラスに翻訳し、コメントとの順序付き選択と繰り返しを開始規則の定理につなぐ。
[check-whitespace.sh](check-whitespace.sh) は、`Ws`、`SpaceChar`、`Comment` の行を照合し、Lean の文字表と GHC の `Data.Char.isSpace` を Unicode スカラー値 1,112,064 個すべてについて比較する。

メタ文法の規則本体は、検査付きの翻訳で導出の文脈に入る。
[check-concrete-terminals.sh](check-concrete-terminals.sh) は、[ExtractConcreteTerminals.hs](ExtractConcreteTerminals.hs) で二つのメタ文法から規則の本体と終端の表を書き出す。
[check-strict-file.sh](check-strict-file.sh) は、[ExtractSelfHostedFile.hs](ExtractSelfHostedFile.hs) で生成した `SelfHosted.hs` の規則を翻訳する。
[SelfHostedFileProof.lean](SelfHostedFileProof.lean) は、翻訳した各規則の本体が導出の文脈の規則と同じであることを `rfl` で示す。
check-strict-file.sh は、`File` が集めた値を捨てる変更と、`File` が繰り返す規則、`TopOne` の選択、`IdentStart` の述語、`Verbatim` の診断を変えた変更が、翻訳か証明で拒否されることも確かめる。

[CertifiedPublicFiles.lean](CertifiedPublicFiles.lean) の定理は、項目ごとの導出の証明書から組み立てる。
各ファイルの証明書は [SplitMetaFile.lean](SplitMetaFile.lean) が項目ごとに書き出し、[check-file-items.sh](check-file-items.sh) が検査する。
[CheckItemSources.lean](CheckItemSources.lean) は、証明書の入力が実際のファイルの内容と一致することを確かめる。

### `parseTops` の値

[FileTops.lean](FileTops.lean) は、`parseTops` が成功したときに返す `[Top]` の形を特徴づける。
FileEntry.lean と TotalFile.lean は成功と導出の同値を示すが、開始結果の値を `()` に消している。
生成したパーサーでは、`File` の値は `many TopItem` が返すリストであり、`TopItem` は `TopOne` の値を返し、`TopOne` は最初に成功した選択肢の値を返す。
`Chain` はこの繰り返しを認識器の導出の上に写し、`Tops` は `File` 全体を写す。
FileTops.lean は次の定理を示す。

- `invariant1_tops_iff`（FileTops.lean:302）: 項目の列を持つ導出があることと、認識器が入力全体を受理することは同値である。
- `invariant1_tops_unique`（FileTops.lean:314）: 項目の列は一つに決まる。
- `invariant1_tops_linked`（FileTops.lean:324）: 項目は先頭の `Ws` の後から順に入力を消費して末尾で終わり、各項目はその種類の選択肢を通った `TopItem` の呼び出しである。
- `invariant1_parseTops_value`（FileTops.lean:372）: 値を運ぶ開始結果で公開の入口が `ts` を返すことと、`ts` が導出の値の列であることは同値である。
- `invariant1_parseTops_shape`（FileTops.lean:350）: その列は項目ごとに一つの値を項目の順に持ち、i 番目の値は i 番目の項目の選択肢の、その開始位置での値である。

[check-file-tops.sh](check-file-tops.sh) は、このモデルを実装に結びつける。
まず、生成した `File`、`TopItem`、`TopOne` の定義（LINE プラグマを除く）とランタイムの `many` を `git hash-object` で固定する。
次に、[FileTopsProbe.hs](FileTopsProbe.hs) が、`packages/` と `editors/` のすべての .hpeg ファイルと境界の入力について、実際の `parseTops` が返す `Top` の種類、順序、件数、位置を書き出す。
[FileTopsProbe.lean](FileTopsProbe.lean) は、`runTops_sound` で `Tops` に結びつけた実行可能なモデルから同じものを書き出し、両者を比べる。
`conformance/` の文法は比べない。
Lean のモデルはメモ化なしで動くので、その中には数分かかるものがあるからである。

### ランタイム

生成したパーサーが呼ぶランタイム `Peg.Runtime.Internal` は、[ExtractRuntimeCore.hs](ExtractRuntimeCore.hs) が Lean に翻訳する。
対象は、メモ化（`memo`、`memoArg`、`nomemo`、`evalBody`、`replay`、`logUndo` など）、制御の組み合わせ子（モナドの連接、`choice`、`many`、`skipMany`、`optional`、`andP`、`notP`、`labeledWith`、`expecting`）、端末（`lit`、`cls`、`anyChar`）、公開の入口の `runParser` と `defaultConfig` である。
抽出器は関数ごとに、ソースの行または行の並びを Lean の行へ写す辞書を持ち、辞書にない行があると翻訳を止める。
行を消したり並べ替えたりした変更は翻訳を通るので、正しいかどうかは証明が決める。
翻訳先の型と ST の参照のモデルは [RuntimeCore.lean](RuntimeCore.lean) に置き、抽出器はそこで写したデータ宣言をソースと照合する。

翻訳した定義についての定理は [RuntimeCoreProof.lean](RuntimeCoreProof.lean) にある。
`invariant1_translated_memo_step`（RuntimeCoreProof.lean:225）と `invariant1_translated_memoArg_step` は、翻訳した `memo` と `memoArg` が [MemoRecognition.lean](MemoRecognition.lean) の `memoStep` と同じ結果と状態を返すことを示す。
`invariant1_translated_memo_off_same`（RuntimeCoreProof.lean:258）は、メモ化の有無と hit か miss かによらず、結果、最遠の失敗、依存、エラーの記録が一致することを示す。
回復しない構文解析では、連接、選択、`optional`、ラベル、先読みの結果が [LabelPropagation.lean](LabelPropagation.lean) のフレームと先読みに一致し、`many` と `skipMany` は 1 回の反復ごとの式を満たす。
端末の `lit`、`cls`、`anyChar` は、スカラー値の境界で `ConcreteTerminal.matchTerm` と同じ入力を受理する。
`expecting` は翻訳するが、定理はない。
`invariant1_translated_runParser_entry`（RuntimeCoreProof.lean:713）は、`runParser` が値を返すことと、開始規則の結果を `PublicParsing.entry` に渡して成功することが同値であることを示す。
これらの定理があるので、`check-public-parsing.sh` と `check-memo-recognition.sh` はランタイムの SHA-256 を照合しない。

[SelfHostedRuntime.lean](SelfHostedRuntime.lean) は、自己ホストしたパーサーをこの翻訳の上で走らせる。
`exec`（SelfHostedRuntime.lean:474）は、規則本体の各構成子を、ExtractSelfHostedFile.hs がその構成子を読み取る生成コードの組み合わせ子で実行する。
連接は `bindP`、選択は `choice`、端末は `lit`、`cls`、`anyChar`、先読みは `andP` と `notP`、ラベルは `labeled` と `labeledMessage`、意味述語は `predicate`、規則の呼び出しは `nomemo` である。
繰り返しは `manyGo` と `skipManyGo` と同じ形のループで、反復から反復へモデルの環境を渡す。
値は、モデルの残りの入力と環境である（前提 R7）。
`predicate` は翻訳の対象でないので、check-runtime-core.sh がソースの行を照合する。
`invariant1_exec_agrees`（SelfHostedRuntime.lean:560）は、燃料についての帰納法で、`exec` と導出の文脈での実行 `runFuel` が一致することを示す。
`invariant1_runtime_file`（SelfHostedRuntime.lean:887）は、これを `runParser defaultConfig` が作る文脈と世界の `File` に当てる。
`invariant1_runtime_runParser`（SelfHostedRuntime.lean:973）は、その `runParser` が値を返すことと、開始結果を `PublicParsing.entry` に渡して同じ値が返ることが同値であることを示す。
`PublicGeneration.parse` は、十分な燃料での実行の開始結果 `runtimeStart` の上に定義する。

ただし、生成コードは規則の呼び出しを `nomemo` ではなくメモ表で包む。
[SelfHostedMemo.lean](SelfHostedMemo.lean) の `execM`（SelfHostedMemo.lean:78）は、`exec` の呼び出しを、引数のない呼び出しでは `memo` に、引数のある呼び出しでは深さの引数を鍵にした `memoArg` に替えたものである。
`invariant1_memoArg_rules`（SelfHostedMemo.lean:478）は、`memoArg` で呼ぶ規則が、ExtractSelfHostedFile.hs が `d` を取り `PegRt.memoArg` で定義されていると読む 12 個の規則に一致することを示す。
表はストアの中の参照であり、キャッシュの不変条件 `Coherent`（SelfHostedMemo.lean:146）は、ストア全体のどの項目も、その鍵でモデルが返すどの返答とも、呼び出し元が使うもの（位置、ラベル、結果の深さ）で一致することをいう。
`invariant1_memo_runs`（SelfHostedMemo.lean:585）は、燃料についての帰納法で、モデルが返答を返す燃料では、不変条件を満たすどの世界からも `execM` がその返答に当たる結果を返し、不変条件を保つことを示す。
`invariant1_memo_file`（SelfHostedMemo.lean:918）と `invariant1_memo_runParser`（SelfHostedMemo.lean:947）は、空の表から始めた `File` の実行が `fileRun` と同じ結果を返し、`runParser defaultConfig` の値も `runtimeResult` から決まることを示す。

引数のない呼び出しの鍵は位置だけであり、呼び出し元の環境を含まない。
そこで、[ScopedEnv.lean](ScopedEnv.lean) の静的な解析 `check` は、規則の本体が、意味述語、アクション、呼び出しの引数で、自分で束縛した名前と深さの引数だけを読むことを確かめる。
`invariant1_scope_sound`（ScopedEnv.lean:295）は解析の健全性を、`invariant1_meta_scoped`（ScopedEnv.lean:587）は、`parseTops` が使う Peg.hpeg のメタ文法のすべての規則が解析を通ることを示す。
`invariant1_plain_call_independent`（ScopedEnv.lean:628）は、引数のない呼び出しを受ける規則が、どの環境から始めても、呼び出し元が使うものの等しい返答を返すことを示す。

また、ExtractSelfHostedFile.hs が規則本体を読むときに落とす書き方は、[RuntimeForms.lean](RuntimeForms.lean) が結果を変えないことを示す。
回復と計数を無効にした翻訳したランタイムでは、どの世界からも次の等式が成り立つ。

- `getOffset_bind`（RuntimeForms.lean:62）、`spanFrom_bind`（RuntimeForms.lean:66）: `getOffset` と `spanFrom` の束縛は、同じ位置と世界で続きを走らせる。
- `withCol_const`（RuntimeForms.lean:70）: 列を使わない関数の `withCol` は、その関数が返すパーサーに等しい。
- `capture_same`（RuntimeForms.lean:79）: `capture p` は `p` と同じ形、位置、世界を返す。
- `choice_one`（RuntimeForms.lean:88）: 一択の `choice [p]` は `p` に等しい。
- `choice_cons`（RuntimeForms.lean:112）: 三択以上の `choice` は二択の入れ子に等しい。
- `optional_choice`（RuntimeForms.lean:126）: `optional p` は `p` と空との選択に等しい。

`getOffset`、`spanFrom`、`withCol`、`capture`、`Span` は翻訳の対象でないので、check-runtime-core.sh がソースの行を照合する。

[check-runtime-core.sh](check-runtime-core.sh) は翻訳と証明を検査し、さらに変異で検査の強さを確かめる。
辞書にない五つの変更は翻訳で拒否される。
`replay` の失敗の再生、`evalBody` の失敗の記録の初期化、`notP` の失敗の記録の復元、`runParser` の入力末尾の期待の追加の四つを消した変更は、翻訳を通るが証明で拒否される。
生成した `parse` が `runParser` を `defaultConfig` で呼ぶことは、[check-public-parsing.sh](check-public-parsing.sh) が生成ソースの該当行と照合する。
check-public-parsing.sh は、[translate-public-entry.awk](translate-public-entry.awk) で `parseGrammar`、`parseTops`、`assemble` の入口を翻訳し、入口を変えた七つの変更を翻訳が拒否することも確かめる。

### `assemble` の検査

[AssembleValidation.lean](AssembleValidation.lean) は、`Peg.Grammar.Assemble.assemble` の検査を、位置を消した `Top` のモデルで形式化する。
`assemble_failure_iff_violation_or_missing_module`（AssembleValidation.lean:217）と `assemble_ok_iff`（AssembleValidation.lean:232）は、違反があるか `%module` がないときだけ拒否し、拒否の診断が空でないことを示す。
述語は呼び出し側から受け取らない。
[AssemblePredicates.lean](AssemblePredicates.lean) が `isValidIdent`、`isClassName`、`isExportItem`、`T.words`、`binderError` などを写す。
文字の分類には、GHC 9.10.3 の `isAlpha`、`isAlphaNum`、`isUpper` と `ModifierLetter` をすべてのスカラー値で表にした [AssembleChars.lean](AssembleChars.lean) を使う。
`TDef` の選択肢は [AssembleBindings.lean](AssembleBindings.lean) の木として持つ。
`invariant2_alt_binders_iff` は、取り出した名前が木の中の束縛の出現とちょうど一致することを示す。
`invariant2_reserved_binding_iff` と `invariant2_reserved_parameter_iff` は、束縛名と引数名の診断が、出現していて `binderError` が拒否する名前と一致することを示す。
[check-assemble-predicates.sh](check-assemble-predicates.sh) は、文字の表を作り直して照合し、写した Haskell の範囲を固定する。
さらに、Unicode の名前、予約語、`forall`、修飾文字、修飾付きの名前、拡張のキーワード、入れ子の束縛を含む同じ入力で、Haskell と Lean の結果を比べる。

### import の解決

[ImportResolution.lean](ImportResolution.lean) は、`packages/peg-grammar/src/Peg/Grammar/Import.hs` の `resolveImports` を、Haskell の定義の手順ごとに写したモデルである。
`invariant2_resolve_error_nonempty`（ImportResolution.lean:337）は、解決の失敗に診断が一件以上あることを示す。
[check-import-resolution.sh](check-import-resolution.sh) は、モデルが写すソースの範囲を固定し、[ImportResolutionProbe.hs](ImportResolutionProbe.hs) と [ImportResolutionProbe.lean](ImportResolutionProbe.lean) で `resolveImports` とモデルの結果を比べる。
ライブラリの読み込みは、root と同じ `parseTops` と `assemble` を通る（Import.hs:79〜84）。

### テンプレートの展開

[TemplateQueue.lean](TemplateQueue.lean) は、テンプレート展開で、同じ深さの有限個のインスタンスを FIFO 順に処理し、そこで生じたインスタンスを次の深さで処理することを形式化する。
個々の展開が有限個の子を返せば、子の個数に一律の上限がなくても、深さ 65 ですべての残りを拒否して待ち行列が空になる。
外側の型分類の反復も、初期カウンター 8 で最大 9 回で終了する。
テンプレート本体の置換、型分類、各インスタンスを展開する処理自体の停止性は、この二つの定理の前提に残る。
型分類を除くこれらの前提は、TemplateExpansionWhole.lean が外す。
[check-template-queue.sh](check-template-queue.sh) は実装の深さと待ち行列の更新を照合し、実生成器で深さ 64 の生成成功と 65 の診断を検査する。

[TemplateExpansionWhole.lean](TemplateExpansionWhole.lean) は、`expandTemplates` 全体についての定理 `expandTemplates_whole`（TemplateExpansionWhole.lean:1298）を証明する。
この定理は四つの性質からなる。
展開は終わり、結果は一つに決まる。
拒否の結果には診断が一件以上あり、`Left` なので文法を含まない。
受理の結果は、展開した通常の規則の後にインスタンスを並べたものである。
そこにはテンプレート、テンプレートの呼び出し、テンプレートへの参照が残らず、各インスタンスは入力のどの規則とも異なる名前で一度だけ定義される。

このモデルは、`expandTemplates`、`expandOnce`、`expandRule`、`expandAlt`、`expandItems`、`expandExpr`、`captures`、`argType`、`instanceOf`、`freshName`、`drain` の分岐をすべて写す。
`drain` の再帰は関係 `Drain` に、型の反復 `go` は関係 `Go` に写し、それぞれの導出が存在して一つに決まることを証明する。
待ち行列の停止性は、深さ d の仕事の後に深さ d + 1 の仕事が並ぶ FIFO の形が保たれることから導く。
インスタンスの本体は、テンプレートを呼び出し元として、束縛のスコープを項目ごとに広げて展開する。
[TemplateExpansion.lean](TemplateExpansion.lean) にある、呼び出し元を固定しスコープを広げない `expandExpr` と `expandBody` のモデルは、このモジュールで置き換えた。
そのため、[TemplateSubstitution.lean](TemplateSubstitution.lean) の式は、グループの項目に束縛を持つ。

[check-template-expansion-whole.sh](check-template-expansion-whole.sh) がモデルを実装に結びつける。
このスクリプトは、モデルが写す `Templates.hs` の範囲を [template-expansion-whole.source](template-expansion-whole.source) と照合する。
続いて、[TemplateExpansionWholeProbe.hs](TemplateExpansionWholeProbe.hs) が `parseGrammar` で読んだ 11 個の文法を、実際の `expandTemplates` とモデルの両方で展開し、規則の型を除いた結果を比べる。
比べる文法は、受理、インスタンスの共有、名前の衝突の回避、`%syntax` でのインライン化、各診断、深さの上限を含む。

### 規則の検査

[Guard.lean](Guard.lean) は、二つのファイル名に制御文字がある場合の診断との同値を証明する。
[check-guard.sh](check-guard.sh) は、生成器の文字比較を翻訳して照合する。
[Nullable.lean](Nullable.lean) は、有限の正の式に対する空文字受理集合の最小不動点と停止性を証明する。
[Reachable.lean](Reachable.lean) は、有限の参照グラフにおける到達集合の正確性と停止性を証明する。
[check-nullable.sh](check-nullable.sh) と [check-reachable.sh](check-reachable.sh) は、Haskell の該当処理を固定の定義と照合する。
[Signatures.lean](Signatures.lean) は、規則の重複、参照の存在、引数個数を判定する。
[ExtractSignatures.hs](ExtractSignatures.hs) は、二つのメタ文法と `Templates.hpeg` の定義と参照を抽出し、Lean が三件とも検査する。
check.sh は、未定義参照を加えた負例の証明を Lean が拒否することも確かめる。

[CheckGroupsModel.lean](CheckGroupsModel.lean) は、`Peg.Grammar.Check` の `check`、`checkRules`、`checkLibrary` と、`checkRules` の 15 個の検査のグループを、関数ごとに Lean の全域関数へ写したモデルである。
`Peg.Grammar.Types` の `hasValue`、`countedItems`、`isUnit`、`valueRefs`、`isClassified` も写す。
到達可能性の `reach` は、未訪問の名前の数、残りの根の数、スタックの長さの辞書式の順で減る量を持つ。
空文字列を受理しうる規則を求める反復は、既知の集合が増えるだけであることを証明として持つ。
左再帰は `stronglyConnComp` の代わりに `reach` で求める。
どのループも `partial def` を使わない。

[CheckGroupsReach.lean](CheckGroupsReach.lean) は、これらのループが何を返すかを示す。
`mem_reach_iff` は、`reach` が始めに見た名前と、そこから一本以上の辺でたどれる名前をちょうど返すことを示す。
`mem_reachable_iff` は、これを到達可能性の検査に当てはめる。
`mem_leftRecursiveRules_iff` は、規則が左再帰に入ることと、左端の呼び出しをたどって自分に戻ることが同値であることを示す。
`nullableRulesWith_fixed` は、反復が段の不動点で止まることを示す。
`countedItems_eq`、`allUnitCounted_eq`、`groupOne_eq`、`unitAlts_eq` は、モデルの補助関数が `Types.hs` の `filter` と `all` による定義に一致することを示す。

[CheckGroupsTheorems.lean](CheckGroupsTheorems.lean) は、各グループが何を拒否し何を受理するかを `*_nil` の定理で示す。
たとえば `undefinedErrors_nil` は、誤りがないことを、参照と指示に書いた名前がすべて規則であることと同値にする。
`repetitionErrors_nil` は、繰り返す式がどれも空文字列を受理しえないことと同値にする。
`altErrors_nil` は、束縛、束縛名の重複、値のない選択肢、グループの中の束縛の条件と同値にする。
`check_ok_iff`（CheckGroupsTheorems.lean:78）は、`check` が受理する文法を、ライブラリでなく、規則を持ち、15 個のグループのどれにも誤りがないものに限る。
`check_rejects`（CheckGroupsTheorems.lean:93）は、どのグループの誤りも結果に入ることを示す。
検査は最初の失敗で止まらず、すべてのグループを走らせて位置で整列する。
`check_error_ne_nil`（CheckGroupsTheorems.lean:68）は、拒否の診断が一件以上あることを示す。
`generation_rejects`（CheckGroupsTheorems.lean:124）は、`generate` と `generateWithWarnings` の `Left` に診断が一件以上あり、生成テキストがないことを示す。

[check-check-groups.sh](check-check-groups.sh) がモデルを実装に結びつける。
このスクリプトは、`Check.hs` 全体を [check-groups.source](check-groups.source) と照合し、`Types.hs`、`Grammar.hs`、`Templates.hs` の写した範囲と `Codegen.hs` の行を、`git hash-object` と `grep` で固定する。
さらに、リポジトリのすべての `.hpeg`、そこから最初の規則を除いた文法、各診断を出すように書いた文法を [CheckGroupsProbe.hs](CheckGroupsProbe.hs) で読む。
そのうえで、実際の `check` と `checkLibrary`、モジュール内の関数（`repetitionErrors`、`altErrors`、`bindingReferenceErrors`、`constructorErrors`、`syntaxNameErrors`、`hygieneErrors`、`leftRecursiveRules`、`nullableRulesWith`）の結果を、モデルの結果と比べる。

### ラベルの検査

[LabelCheckModel.lean](LabelCheckModel.lean) は、`Peg.Grammar.Labels` のうち `labelWarnings`、`stripLabels`、`stripLabelsAs` と、それらが呼ぶモジュール内のすべての関数を、関数ごとに Lean の全域関数へ写したモデルである。
文字の集合は [LabelCheckCharSet.lean](LabelCheckCharSet.lean) が写す。
`failed`、`succeeded`、`ruleFailed`、`ruleSucceeded` の相互再帰は、燃料で段を数える `run` として書く。
[check-label-check.sh](check-label-check.sh) がモデルを実装に結びつける。
このスクリプトは、`Labels.hs` 全体を [label-check.source](label-check.source) と照合し、`isSpace` の表を GHC 9.10.3 で作り直して照合する。
さらに、リポジトリのすべての `.hpeg` と、[ADR 0029](../docs/adr/0029-label-safety-implementation-deviations.md)、[ADR 0087](../docs/adr/0087-other-labels-do-not-change-the-label-check.md)、[ADR 0088](../docs/adr/0088-correct-the-second-example-of-adr-0087.md) の例、`%recover`、入れ子のグループ、重複した選択肢、テンプレート、左再帰、引数の持ち上げを含む文法を [LabelCheckProbe.hs](LabelCheckProbe.hs) で読む。
そのうえで、実際の `labelWarnings` と `stripLabelsAs`、左再帰の分類、空文字列を受理しうる規則を、モデルの結果と比べる。

[LabelCheckTermination.lean](LabelCheckTermination.lean) は、ラベルの検査が停止することを示す。
各ラベルについて、検査が訪れる文脈は有限の一覧 `keyUniverse` に入る。
規則はそのラベルの規則か呼び出し元の規則であり、枠はラベルの枠か呼び出しの枠の末尾である。
文字の集合は整列した区間の列で、`0x10FFFF` を超えない。
一致した要素の列は 8 個以下で、引数の置き換えは 3 回以下である。
各段は訪れた文脈で止まるか新しい文脈を訪れるので、`run_terminates` は燃料 `keyUniverse.length + 1` で結果が出ることを示す。
`run_mono` は、それより多い燃料でも結果が変わらないことを示す。
これにより `verdictOf` と `labelWarnings` が定まる。
`labelWarnings_eq_fuel`（LabelCheckTermination.lean:980）は、プローブの燃料で全ラベルの判定が出れば、その警告が `labelWarnings` に一致することを示す。

[LabelCheckTheorems.lean](LabelCheckTheorems.lean) は、ラベルの除去と警告の性質を示す。
`unlabelExpr_stripExpr` と `stripExpr_eq_unlabelExpr` は、`stripLabels` がラベルの注記だけを外すことを示す。
外した結果からさらにすべてのラベルを消すと、入力からラベルを消したものに一致し、テンプレートの呼び出しがなければラベルは一つも残らない。
`stripLabels_rules`、`stripLabels_fields`、`recoveryEntries_spec` は、規則、選択肢、要素の位置と束縛と順序が保たれ、`%recover`、`%safe`、`%message` が空になることを示す。
また、回復の規則が、開始規則でも `%entry` でもなければ一度だけ入口に加わることも示す。
`sites_labels` と `mem_labelWarnings`（LabelCheckTheorems.lean:416）は、警告が、`%safe` にない名前のラベルのうち判定が `safe` でないものにちょうど対応することを示す。
そのとき、警告の位置はラベルを付けた式を持つ要素の位置であり、文言は「may reject valid input」か「cannot be checked」である。
`verdict_ignores_other_labels` は、各ラベルをほかのラベルを外した文法と枠の上で判定することを示す（[ADR 0029](../docs/adr/0029-label-safety-implementation-deviations.md)、[ADR 0087](../docs/adr/0087-other-labels-do-not-change-the-label-check.md)、[ADR 0088](../docs/adr/0088-correct-the-second-example-of-adr-0087.md)）。
`verdict_in_lookahead`、`verdict_unchecked_growing`、`ruleSucceeded_entry`、`ruleFailed_recovery` は、[ADR 0028](../docs/adr/0028-label-safety-check.md) の個々の場合を示す。
不変条件 2 については、`labels_reject_with_diagnostic`（LabelCheckTheorems.lean:605）が、ラベルによる生成の失敗は `--Werror` のときだけ起き、そのとき警告が一件以上あることを示す。

#### GHC の構文木からの翻訳

`Labels.hs` は、行の辞書や固定の写しではなく、GHC の構文木から Lean へ翻訳する。
[TranslateHaskell.hs](TranslateHaskell.hs) は、GHC 9.10.3 の GHC API でモジュールを構文解析、名前解決、型検査し、名前解決した構文木を読む。
翻訳する関数は、公開の `labelWarnings`、`labelSafeAt`、`matchesEmpty`、`stripLabels`、`stripLabelsAs` と、それらが呼ぶモジュール内のすべての関数である。
型は、型検査の結果から取る（束縛の型と、ライブラリ関数を使う箇所の型）。
扱う構文の部分集合の外の構文と、ライブラリの表にない関数は、位置を付けて翻訳を止める。
翻訳の規則は TranslateHaskell.hs の先頭の注釈に、ライブラリ関数の写しとその評価規則は [HsPrelude.lean](HsPrelude.lean) に書く（「残る前提」の X2、H1〜H8）。

そのため、翻訳を信頼するときの基礎は、構文の種類ごとの規則とライブラリの表だけになる。
行の辞書（ExtractRuntimeCore.hs）では辞書の項目ごとに人が対応を書くが、この翻訳器では関数を足しても人が書く対応は増えない。
停止性は Lean が確かめる。
Lean が停止を示せない再帰は、[translate-labels.hints](translate-labels.hints) に `termination_by` を書くか、燃料の組に入れる。
燃料の組の関数は燃料を引数に取り、組の中の呼び出しごとに一つ使う（規則 H6）。
`labelWarnings`、`labelSafeAt`、`matchesEmpty` は燃料を取り、`stripLabels` と `stripLabelsAs` は取らない。

[LabelsTranslatedProof.lean](LabelsTranslatedProof.lean) は、翻訳した関数がモデルと一致することを、型の射影 `pGrammar` の上で示す。
射影は、位置の整数を自然数に、コードポイントを同じ値に写し、モデルが持たない欄を空にする。
`strip_expr`（LabelsTranslatedProof.lean:110）は、翻訳した `stripLabels` の式の書き換えが、モデルの `stripExpr` に一致することを示す。
`stripLabels_translated`（LabelsTranslatedProof.lean:235）と `stripLabelsAs_translated`（LabelsTranslatedProof.lean:268）は、翻訳した `stripLabels` と `stripLabelsAs` がモデルの同名の関数に一致することを示す。
これにより、LabelCheckTheorems.lean の `stripLabels` についての定理（`unlabelExpr_stripExpr`、`stripLabels_rules`、`stripLabels_fields`、`recoveryEntries_spec`）は、翻訳した関数についても成り立つ。
`stripLabels_template_args`（LabelsTranslatedProof.lean:285）は、翻訳した `stripLabels` がテンプレートの呼び出しの引数を変えないことを示す。
`labelWarnings` の翻訳は Lean で型検査と停止性の検査を通るが、モデルとの一致はまだ示していない。

[check-translate-labels.sh](check-translate-labels.sh) は、翻訳器を作り、`Labels.hs` を翻訳し、翻訳と証明を Lean で検査する。
さらに、三つの変異で検査の強さを確かめる。
タプルの部分適用と、表にないライブラリ関数（`reverse`）を足した二つの変更は、翻訳で拒否される。
`stripLabels` から `*` の場合を消した変更は、翻訳と型検査を通るが、証明で拒否される。
`Data.Char.isSpace` の表は、GHC 9.10.3 で作り直して HsPrelude.lean と照合する。

### 段のつなぎ

[Pipeline.lean](Pipeline.lean) は、警告付き生成で外側の診断または内側の `generationModule` を観測するまでの分岐を扱う。
各段階が失敗時に空でない診断を返し、テンプレートの注記が診断を空にしないという前提から、合成後の結果が空でない診断か生成テキストになることを証明する。
[check-pipeline.sh](check-pipeline.sh) は、`generateWithWarnings` の定義と CLI の呼び出しを `diff` で固定する。
実装だけの検査 [PipelineProbe.hs](PipelineProbe.hs) は、実際の `generateWithWarnings` に構文、import、テンプレート、規則参照、生成オプションのエラーを渡し、外側と内側のどちらから診断が返るかを確かめる。
[InnerGeneration.lean](InnerGeneration.lean) は、`generate` の分岐（ファイル名とモジュール名の検査、展開、検査、未定義の export、`render`、`finalize`）を同じ形で扱う。
[check-inner-generation.sh](check-inner-generation.sh) は、その分岐のソースを固定する。

PublicGeneration.lean は、この二つのモジュールが抽象の引数に置いた段を、前の節までの段のモデルで置き換える。
[check-public-generation.sh](check-public-generation.sh) は、`generateFromSource`、`Generation` の欄の順、`Loc` の順序、`stripLabelsAs` の Haskell の定義を固定する。
段のつなぎ方のほかの部分は、check-pipeline.sh、check-inner-generation.sh、check-assemble-validation.sh、check-public-parsing.sh、check-import-resolution.sh が固定する。
合成したモデルと実関数を比べるプローブはない。
合成は各段の結果をそのまま渡すだけであり、各段はそれぞれのプローブが実関数と比べている。

### `render` の合成

[RenderComposition.lean](RenderComposition.lean) は、生成器が組み立てる部品を GHC 9.10.3 のモジュール規則に合成し、出力のトークン列に開始記号からの導出があることを示す。
`generated_module_verbatim` と `generated_module_with_rules_verbatim` は、埋め込みブロックが import 宣言だけでなくトップレベル宣言も含む場合を扱う。
`Codegen.render` は各ブロックを分割せずに、ソースの順で生成した import と生成した宣言のあいだに置く。
そのため、トークン列は、生成した import、各ブロックのトークン、生成した宣言の順に並ぶ。
[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) の埋め込みコードの前提は、`verbatim_split` と二つの要素の前提（`verbatim_imports_ok`、`verbatim_decls_ok`）になる（前提 E1）。
ブロックのトークンを連結した列は、import 宣言の並びとトップレベル宣言の並びをこの順に連ねたものであり、各要素が GHC の `importdecl` と `topdecl` から導出できる、という前提である。
lexer に関する `initial`、`trace`、`tokens_match` の前提は残る（前提 G1）。
[check-render-composition.sh](check-render-composition.sh) は、`render` の並び、`verbatimBlock` の定義、`grammarVerbatim` がブロックをソースの順に集める行を実ソースと照合する。
さらに、import と宣言を含むブロックと規則の後のブロックを持つ文法から実際に生成したモジュールで、ブロックの行がこの位置にこの順で並ぶことを確かめ、GHC で検査する。

RenderComposition.lean は、次のモジュールの部品の導出を使う。

- [RenderModuleGHC.lean](RenderModuleGHC.lean): モジュールの枠、export の一覧、生成した import。[check-render-module-ghc.sh](check-render-module-ghc.sh) は、`render` の枠のソースを照合し、二つのメタ文法のトレースが枠の規則で終わることと、枠の規則の番号を変えた変異を Lean が拒否することを確かめる。
- [RenderDeclarationsGHC.lean](RenderDeclarationsGHC.lean): GHC 9.10.3 の型シグネチャと関数束縛の規則から、任意の子の導出と引数列を合成する。[check-render-declarations-ghc.sh](check-render-declarations-ghc.sh) がソースとトレースを照合する。
- [RenderDeclarationBinders.lean](RenderDeclarationBinders.lean): 予約語の拒否、`_` の保持、メモ化キーの値と型の置換。[check-render-declaration-binders.sh](check-render-declaration-binders.sh) は、組み立て時の二つの検査箇所と生成時の二つのキー箇所を実ソースで照合する。
- [RenderRuleBodyGHC.lean](RenderRuleBodyGHC.lean)、[RenderPrimitiveChoice.lean](RenderPrimitiveChoice.lean)、[RenderPrimitiveDo.lean](RenderPrimitiveDo.lean)、[RenderPrimitiveDoGHC.lean](RenderPrimitiveDoGHC.lean)、[RenderPrimitiveStatement.lean](RenderPrimitiveStatement.lean): 規則の本体の `PegRt.choice` と do ブロックと文。対応する check-render-primitive-*.sh がソースを照合する。
- [RenderExpressionGHC.lean](RenderExpressionGHC.lean) と [RenderExpression.lean](RenderExpression.lean): 式の包みと選択の導出。[check-render-expression-ghc.sh](check-render-expression-ghc.sh) と [check-render-expression.sh](check-render-expression.sh) がソースを照合する。
- [RenderModuleNames.lean](RenderModuleNames.lean): モジュール名と export の名前の GHC の字句。[check-render-module-names.sh](check-render-module-names.sh) は、Lexer.x の `adjustChar` で 1,114,112 個の文字を分類する。この Lexer.x は、check.sh の中で先に動く check-render-expression-lexer.sh が SHA-256 を照合したものである。[check-render-module-operators.sh](check-render-module-operators.sh) は演算子の export を GHC で検査する。
- [RenderExpressionBoundary.lean](RenderExpressionBoundary.lean): 行コメントが次の改行で止まること。[check-render-expression-boundary.sh](check-render-expression-boundary.sh) が GHC でコンパイルして確かめる。

次の三つのスクリプトが最後に表示する定理の数は、スクリプトに書いた固定の文字列であり、今のモジュールと合わない。
check-render-module-ghc.sh は「20 Lean theorems」と表示するが、RenderModuleGHC.lean の今の定理は 39 個（`private` を除くと 28 個）である。
check-render-expression-ghc.sh は「14 theorems」と表示するが、RenderExpressionGHC.lean の今の定理は 28 個（`private` を除くと 23 個）である。
check-render-primitive-choice.sh は「6 Lean theorems」と表示するが、RenderPrimitiveChoice.lean の今の定理は 2 個である。

[Header.lean](Header.lean) はモジュール名と `module` 行の構文を、[Literal.lean](Literal.lean) は文字列リテラルの引用とエスケープを検査する。
[check-header.sh](check-header.sh) は対応する Haskell の定義を照合する。
[check-literal.sh](check-literal.sh) は、GHC の `Show` と 134 個の一文字および 17,956 個の二文字のリテラルを比べ、Unicode スカラー値 1,112,064 個すべての文字列と文字の綴りも比べる。

[Pragmas.lean](Pragmas.lean) は、元ファイルの位置を表す `LINE` と `COLUMN`、生成先の位置を復元する行の形式を証明する。
位置は自然数で、ファイル名の文字集合は文字列リテラルの定理と同じである。
埋め込み本文は任意の文字列として扱う。
生成器はユーザーが書いた行と衝突しない復元用マーカーを選ぶ。
これにより、ユーザーの quasiquote 内に同じ形式の行があっても、その行を復元対象から除外できる。
本文に含まれるコメントやレイアウトが周囲の Haskell の構文に及ぼす影響は、この定理の範囲外である（前提 E1 に含まれる）。
[check-pragmas.sh](check-pragmas.sh) は、引用符を含むファイル名で実際に生成したアクションの位置と復元行を Lean の出力と照合し、モジュールを GHC で検査する。
[check-no-record.sh](check-no-record.sh) は、`NoTraditionalRecordSyntax` を指定した文法でメモ用ストアと設定のアクセスを含むモジュールを生成し、GHC と実行結果で検査する。

### `finalize`

[RenderFinalize.lean](RenderFinalize.lean) と [RenderFinalizeModule.lean](RenderFinalizeModule.lean) は、RenderComposition.lean の結論を、公開の入口が実際に返すテキストまで延ばす。
`Codegen.generate` が返すのは `render` の出力ではなく、それに `finalize` をかけたものである。
`finalize` は、`fragment` と `verbatimBlock` が利用者のコードの後に置いた復帰マーカーの行を、生成したファイルの次の行を指す LINE プラグマに置き換え、末尾に改行を足す。
RenderFinalize.lean は、`Data.Text.lines`、`Data.Text.unlines`、`finalize`、`freshRestoreMarker` が選ぶマーカー、`render` の先頭の行（二行のコメント、LANGUAGE プラグマ、OPTIONS_GHC プラグマ）をモデルにする。
そのうえで、次の定理を示す。

- `finalize_prefix`（RenderFinalize.lean:220）: 改行で終わる前半に `finalize` をかけたものは、全体に `finalize` をかけたものの先頭である。
- `finalize_render_header`（RenderFinalize.lean:372）: 先頭のコメントとプラグマの行は、変わらずに同じ順でファイルの先頭に残る。
- `finalize_line_numbers`（RenderFinalize.lean:457）: i + 1 行目のマーカーを置き換えた LINE プラグマは、i + 2 行目を指す。

lexer の前提は、マーカーを含む `render` の出力ではなく、`finalize` の後のテキストについて置く。
マーカーの行は、GHC にとって字句のない行ではないからである。
GHC 9.10.3 の layout 規則は、行頭にある未知のプラグマ（マーカー）の前に仮想のセミコロンを置き、LINE プラグマの前には置かない。
そのため、マーカーを含む `render` の出力は、生成したファイルとは別の字句の列になる。
RenderFinalizeModule.lean の `generated_module_finalized`（RenderFinalizeModule.lean:48）、`generated_module_with_rules_finalized`（RenderFinalizeModule.lean:79）、`generated_module_with_rules_finalized_header`（RenderFinalizeModule.lean:116）は、RenderComposition.lean の抽象の lexer に `finalizedLex` を入れる。
`finalize_prefix` により、lexer の前提は、生成したファイルの先頭の部分を GHC が読んだ結果についての前提になる。
結論は、`finalize` の出力の字句の列が GHC のモジュールの開始記号から導出できることである。

[check-render-finalize.sh](check-render-finalize.sh) は、モデルを実装に結びつける。
まず、`finalize`、`freshRestoreMarker`、`generate` の二回の `render`、`fragment` の定義、`runtimeVersions` の値を実ソースと照合する。
次に、7 個の文法から実際にモジュールを生成する。
文法は、埋め込みブロックと最初のマーカーと同じ行を持つもの、テンプレート、回復のラベル、`%language`、`%env`、`--export` で宣言を省いたもの、PegSyntax.hpeg である。
各モジュールで、出力のファイルの次の行を指す LINE プラグマをマーカーに戻したテキストに Lean の `finalize` を実行し、結果が生成したファイルとバイト単位で一致することを確かめる。
先頭の行が `headerLines` と一致することも確かめる。
さらに、[check-ghc-parser-trace.sh](check-ghc-parser-trace.sh) が作る GHC 9.10.3 のトレーサーで、生成したファイルを構文解析の受理まで読めることを確かめる。
マーカーに戻したテキストの字句の列が生成したファイルと異なるモジュールが少なくとも一つあることも確かめ、`finalizedLex` を使う理由が今も成り立つことを見張る。

### 式の印字と lexer の橋

[RenderPrinting.lean](RenderPrinting.lean) は、式を印字する `Codegen.exprCodeU` を Lean の全域関数でモデル化し、印字したテキストから GHC の終端記号の列への橋を作る。
対象は、利用者のコードを含まない式である。
`.`、引数のない規則の参照、リテラル、文字クラス、十種の包み（`*`、`+`、`?` の値の有無、`&`、`!`、`$`、`~`）、各選択肢を do ブロックにしたグループを扱う。
モデルは印字の木 `PExpr` と、そのテキスト `render` と終端記号の列 `tokens` からなる。
`many` と `skipMany` のどちらを使うか、文の形、新しい変数の名前は、文法の解析で決まるので木の欄に置く。
字句のモデル `lexModel` は、GHC 9.10.3 の Lexer.x に合わせた全域の lexer である。
扱うのは、識別子、修飾付きの識別子、予約語の `do` と `_`、予約演算子の `<-`、文字列と文字のリテラル、特殊文字 `( ) [ ] , ; { }` である。
知らない語は `none` になるので、モデルが GHC と異なる字句を主張することはない。
次の定理を示す。

- `printed_lexes`（RenderPrinting.lean:792）: 名前が妥当な木について、`lexModel (render e) = some (tokens e)`。RenderExpressionGHC.lean の `bridge_wrap`、`bridge_choice`、`bridge_do` が前提に置く lexer の等式のうち、印字する側が出す部分を、これらの式については定理にする。
- `printed_derives`（RenderPrinting.lean:989）: `tokens e` は GHC Parser.y の `exp`（非終端記号 211）と `texp`（非終端記号 229）から導出できる。
- `printed_ghc`（RenderPrinting.lean:996）: GHC の lexer が印字したテキストでモデルと一致すれば、その字句の列は `tokens e` であり、`exp` から導出できる。
- `render_wrap`（RenderPrinting.lean:1042）、`render_group`（RenderPrinting.lean:1047）: `render` は、check-render-expression.sh が実ソースと照合する RenderExpression.lean の `renderWrap`、`renderChoice`、`renderDo` に等しい。

[check-render-printing.sh](check-render-printing.sh) は、モデルを実装と GHC に結びつける。
まず、`exprCodeU`、`itemStmt`、`passThroughOf`、`doBlock`、`fresh`、`ruleVar`、`showT` と `hsString` の定義を git hash-object で固定する。
次に、Lexer.x の `reservedWordsFM` がモデルの予約語の一覧と一致することを確かめる。
そのうえで、[RenderPrintingProbe.hs](RenderPrintingProbe.hs) がリポジトリのすべての文法を読み、生成器と同じ `Env` を作る。
各規則の式とその部分式を、値を使う場合と捨てる場合で実際の `exprCodeU` に印字させ、同じ順に新しい名前を取りながら印字の木を作る。
Lean の `render` がすべての木で `exprCodeU` と同じテキストを返すことを確かめる。
`%syntax` のない文法では、各テキストが `generate` の返す `finalize` 後のモジュールに現れることも確かめる。
最後に、すべてのテキストを一つのモジュールに並べ、GHC 9.10.3 のトレーサーで読む。
GHC の lexer がパーサーに渡す終端記号の番号が、`lexModel` の列と一致することを確かめる。

[RenderExpressionLexer.lean](RenderExpressionLexer.lean) は、Lexer.x の ASCII の文字クラスと区切りを写す。
[check-render-expression-lexer.sh](check-render-expression-lexer.sh) は、Lexer.x の SHA-256 を照合し、該当の規則のソースと具体的な字句の例を GHC と比べる。

### コミットした生成物の証明書

[CommittedModuleDerivations.lean](CommittedModuleDerivations.lean) は、リポジトリにコミットした生成物の fixture のうち三つについて、不変条件 3 を埋め込みコードの前提なしで示す。
三つは、`packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs`、`SelfHostedSyntax.hs`、`packages/peg-codegen/test/generated/Fixture/Extensions.hs` である。
[check-ghc-parser-trace.sh](check-ghc-parser-trace.sh) は、`scripts/regen-fixtures.sh` と同じ作業ディレクトリ、ソース名、出力名、オプションで三つを生成し直し、コミットしたファイルとバイト単位で一致することを確かめる。
そのうえで、コミットしたファイルそのものを GHC 9.10.3 のトレーサーで読む。
こうして、導出の証明書とコミットした fixture を、パッケージのテストを介さずに直接結びつける。
regen-fixtures.sh の該当行が変わったときは、この検査が失敗する。
[check-ghc-derivations.sh](check-ghc-derivations.sh) は、三つのトレースから証明書 `DerivationPeg`、`DerivationPegSyntax`、`DerivationExtensions` を作る。
`invariant3_certified_word`（CommittedModuleDerivations.lean:56）と `invariant3_committed_words`（CommittedModuleDerivations.lean:64）は、各証明書の字句の列が GHC のモジュールの開始記号から導出できることを示す。
`invariant3_committed_text`（CommittedModuleDerivations.lean:78）は、GHC の lexer がテキストから証明書の字句の列を返すという前提だけから、RenderFinalizeModule.lean と同じ形の結論を導く。
check-ghc-derivations.sh は、Peg の証明書の最初の終端を変えた変異を Lean が拒否することも確かめる。

証明書は、モジュール全体の字句の列を覆う。
そのため、二つのメタ文法と Extensions.hpeg の埋め込みブロック、アクション、意味述語、引数のコード、型は、すべて証明書の中にある。
RenderComposition.lean と RenderFinalizeModule.lean の定理は任意の文法についての定理なので、埋め込みコードの前提（`verbatim_split`、`verbatim_imports_ok`、`verbatim_decls_ok`、利用者が書く export の項目の `user_ok`、生成した宣言の `decls_ok`）を仮定に置く。
規則本体のアクション、意味述語、型の導出は、`generated_module_with_rules_verbatim` では部品 `GeneratedParts` の欄（`RenderRule` の `types_ok` と `value_ok`、選択肢の文の導出）として仮定に入る。
この三つのモジュールについては、証明書がこれらの前提に置き換わる。
残る前提は、前提 G2 である。

## GHC との対応

証明と検査は、GHC 9.10.3、Happy 2.1.7、Lean 4.35.0 に固定する。
[check-ghc-parser-trace.sh](check-ghc-parser-trace.sh) は、GHC と Happy の版を確かめ、`Parser.y` の SHA-256 が `331304d8f4007fc7c329e48d56f98e0ebe502bc51b1b443d0ec923febca83952` であることを確かめる。
check-render-expression-lexer.sh、check-render-printing.sh、check-render-module-operators.sh は、`Lexer.x` の SHA-256 を照合する。
Happy は `Parser.y` から表と情報ファイルを作り、[ExtractHappyGrammar.hs](ExtractHappyGrammar.hs) が情報ファイルの名前付きの規則を Lean の文法 `productions` に翻訳する。
解決できない記号か規則があれば、翻訳は失敗する。

拡張は、生成したモジュールの LANGUAGE プラグマで扱う。
[TraceGeneratedModule.hs](TraceGeneratedModule.hs) は、GHC のドライバーと同じ順にフラグを決める。
まず、パッケージの `default-language` に当たる `-XGHC2021` を置く。
次に、`getOptions` でモジュールの先頭のプラグマを読み、`parseDynamicFilePragma` で適用する。
lexer と parser は、その結果のフラグから作った `initParserOpts` の下で動く。
`%language` が生成する LANGUAGE プラグマがトレースに反映されるのは、このためである。
check-ghc-parser-trace.sh は、トレーサーが適用したプラグマの一覧が文法の `%language` の並びと一致することを、三つの fixture で確かめる。

[check-trace-language.sh](check-trace-language.sh) は、この反映を検査にする。
まず、トレースするモジュールをコンパイルする `peg-grammar` と `peg-codegen` の cabal ファイルが、`default-language: GHC2021` だけを使い、`default-extensions` を持たないことを確かめる。
次に、四つの文法を生成し、生成したモジュールと、そこから検査する拡張の LANGUAGE の行だけを消したモジュールを読む。
二つの判定は逆になる必要がある。

| 文法 | 拡張 | 段 | プラグマあり | プラグマなし |
| --- | --- | --- | --- | --- |
| Magic | `MagicHash`（`magic#` を一つの名前にする） | lexer | 受理 | 拒否 |
| Arrows | `Arrows`（`proc` を予約語にする） | lexer | 拒否 | 受理 |
| Block | `BlockArguments`（引数の位置の `do`） | parser | 受理 | 拒否 |
| Qualified | `NoImportQualifiedPost`（GHC2021 の拡張を外す） | parser | 拒否 | 受理 |

lexer の段の拡張では、二つのモジュールの字句の列が異なることも確かめる。
Qualified は、トレーサーが GHC2021 から始めることも確かめる。
最後に、先頭のプラグマを無視して GHC2021 のフラグだけで構文解析するトレーサーを作り、Magic を拒否することを確かめる。

証明が使う GHC の非終端記号は、次のとおりである。
Parser.y の規則名をコードの注釈が記録しているのは、211、229、257 だけである。
ほかの番号の欄は、定理がその番号を使う役割で書く。

| 番号 | 役割 | 使う場所 |
| --- | --- | --- |
| 0 | モジュールの開始記号 | PublicGenerationGHC.lean:73、RenderComposition.lean |
| 47 | 利用者が書く export の項目（`user_ok`） | PublicGenerationGHC.lean:39 |
| 59 | 埋め込みブロックの import 宣言（`verbatim_imports_ok`） | PublicGenerationGHC.lean:41 |
| 78 | 埋め込みブロックと生成したトップレベル宣言（`verbatim_decls_ok`、`decls_ok`） | PublicGenerationGHC.lean:42 |
| 163 | 規則の引数と値の型（`types_ok`、`value_ok`） | RenderComposition.lean |
| 211 | `exp` | RenderPrinting.lean:32 |
| 229 | `texp`（引数の位置） | RenderPrinting.lean:33 |
| 257 | `stmt`（do ブロックの文） | RenderRuleBodyGHC.lean、RenderPrinting.lean:836 |
| 321 | モジュール名（`name_ok`） | RenderComposition.lean |

GHC のパーサーとの一致を検証していない規則は、前提 G3〜G5 として「残る前提」の節に挙げる。
要点は、Lean の `Derives` が文脈自由の導出であり、GHC のパーサーが導出のほかに行う判断を写さないことである。
コミットした三つの生成物では、GHC のパーサーが実際に受理したトレースから証明書を作るので、G3〜G5 の差は受理の判定に影響しない。

## 残る前提

次の表は、証明が仮定に置く前提と、それを経験的に見張る検査をまとめる。
「見張る検査」が空の前提は、どの検査も見張らない。

### 公開の入口と全体の前提

| 番号 | 前提 | 仮定する場所 | 見張る検査 |
| --- | --- | --- | --- |
| A1 | `Premises` の `expandRefines`: Haskell の `expandTemplates` が、射影 `toTemplate` の上でモデル `ExpandTemplates` の結果を実現する。拒否の診断はモデルの診断を `templateDiag` で文字列にしたものである。射影が落とす欄は制約しない。 | PublicGeneration.lean:361 | check-template-expansion-whole.sh（11 個の文法で、規則の型を除いて比べる） |
| A2 | `Premises` の `libraryParseNonempty` と `libraryAssembleNonempty`: `resolveImports` が読むライブラリの構文解析と組み立ての失敗には、診断が一件以上ある。 | PublicGeneration.lean:363、PublicGeneration.lean:364 | check-import-resolution.sh（ライブラリの構文の誤りを含む場合を比べる）。翻訳した入口については `invariant2_parseTops_singleton`（PublicParsing.lean:36）と `invariant2_sorted_assembly_error_nonempty`（PublicEntryProof.lean:200）が同じことを示すが、PublicGeneration はこれを合成しない。 |
| A3 | `Premises` の `assembleAgrees`（不変条件 1 だけ）: Haskell の `assemble` が受理した項目を、AssembleValidation のモデルも受理する。 | PublicGeneration.lean:365 | check-assemble-validation.sh、check-assemble-predicates.sh |
| A4 | `renderShape`（不変条件 3 の GHC の導出だけ）: `check` を通り、export を定義した文法の `render` の出力は、選んだマーカーで `ModuleShape` を満たす。`ModuleShape` は、G1 の lexer の前提、E1 の埋め込みコードの前提、生成した宣言の部品 `GeneratedParts` の存在（規則の型と本体の導出を含む）からなる。 | PublicGenerationGHC.lean:69 | check-render-finalize.sh、check-render-composition.sh、check-render-printing.sh |
| A5 | 引数のまま残る関数: 診断の文（`Inputs.failure`、`Inputs.diag`、`Inputs.templateDiag`）、`assemble` が組み立てる文法（`assemblyErrors`、`moduleName`、`build`）、ImportResolution のライブラリの入力、`classify`（`oracle`、`classify`）、`undefinedExports`（`missing`）、`render`、各項目の値（`value`）。Pipeline は `[Diagnostic]` を文字列の列で表すので、段のモデルの診断は `diag` と `templateDiag` で文字列にする。 | PublicGeneration.lean:247 | 段ごとのプローブ |
| A6 | 段のモデルの前提。下の各表の前提である。 | 各モジュール | 各表のとおり |
| X1 | ソースの抽出と照合のスクリプトと、そこで使う Haskell の構文の読み取り方を信頼する。 | 全体 | 抽出器ごとの変異の検査（check-runtime-core.sh、check-strict-file.sh、check-public-parsing.sh） |
| X2 | TranslateHaskell.hs の構文の規則を信頼する。等式の上から順の照合と落ちる先、ガードとパターンガード、where の束縛の持ち上げ、レコードの構築と更新と選択、リストの内包表記、do ブロックを、Haskell と同じ値を返す Lean の項に写す。 | LabelsTranslated（生成） | check-translate-labels.sh（未対応の構文と表にない関数を足した二つの変異を拒否する） |
| H1 | `Int` は Lean の `Int`、`Char` は 0x110000 未満のコードポイント、`Text` は `String` で写す。翻訳した関数は 64 ビットの `Int` の範囲を出ない。 | HsPrelude.lean | |
| H2 | base のリスト、`Maybe`、組、真偽値、整数の関数は、HsPrelude.lean の同名の関数と同じ値を返す。`sortOn` は安定な整列である。`isSpace`、`isAlpha`、`isAlphaNum` は GHC 9.10.3 の表と一致する。 | HsPrelude.lean | check-translate-labels.sh（`isSpace` の表）、check-assemble-predicates.sh（`isAlpha` と `isAlphaNum` の表） |
| H3 | `Data.Text` の関数は、テキストのスカラー値の列の上で HsPrelude.lean の関数と同じ値を返す。 | HsPrelude.lean | |
| H4 | `Data.Map` と `Data.Set` は、キーの重ならない組の列と要素の重ならない列で写す。検索、所属、挿入、列からの構築は containers と同じに振る舞い、等しさは中身で比べる。`S.toList` は昇順に並べる。 | HsPrelude.lean | |
| H5 | `Eq` を導出した型の `==` は、Lean が導出する `BEq` と同じく構成子と欄を比べる。 | HsPrelude.lean | |
| H6 | 停止する Haskell の評価は、Lean の項が表す値を返す。Haskell がパターン照合で失敗する箇所は、型の既定値 `hsUndefined` とする。燃料で翻訳した関数は、十分な燃料で Haskell の関数と同じ値を返す。 | HsPrelude.lean | |
| H7 | `Int` 以外の型の `show` は、結果どうしを比べるところだけで使われ、Lean の `Repr` で写す。Haskell の導出した `Show` と Lean の `Repr` はどちらも単射である。翻訳した `labelWarnings` の訪問済みの集合の鍵が使う。 | HsPrelude.lean | |
| H8 | `Data.Graph.stronglyConnComp` は、containers 0.7 の手順（キーで整列した頂点、転置グラフの後順、深さ優先の森）を写した `HsGraph.stronglyConnComp` と同じ列を返す。キーは重ならない。 | HsPrelude.lean | check-label-check.sh（左再帰の分類を比べる） |

### 構文解析とランタイムの前提

| 番号 | 前提 | 仮定する場所 | 見張る検査 |
| --- | --- | --- | --- |
| M1 | 意味述語の Haskell 式は、モデルへ真偽値を渡す前に評価される。呼び出しの整礎性の証明は、意味述語を文字を消費しない演算として扱う。 | CallOrder.lean、MetaExecution.lean | check-semantic-predicates.sh（メタ文法の意味述語が使う `isAlpha`、`isAlphaNum`、`isSpace` の表を GHC の `Data.Char` から作る）、check-escape-predicates.sh と check-parameter-predicates.sh（意味述語を含む規則の範囲の SHA-256 を照合する） |
| M2 | File.lean の翻訳では、束縛とキャプチャの値を捨て、成功時に値を作るアクションは入力位置を変えない。 | File.lean | check.sh（規則を書き換えた四つの変異を Lean が拒否する） |
| M3 | `Verbatim`、`Directive`、`Declaration` の値は、位置の関数 `value` として抽象する。`parseTops` の各 `Top` の中身（埋め込みブロックの本文、ディレクティブの引数、規則の選択肢）は特徴づけない。規則の本体は、ExtractConcreteTerminals.hs と ExtractSelfHostedFile.hs の翻訳を信頼する。 | FileTops.lean | check-file-tops.sh |
| R1 | ST は世界の状態の遷移として写し、`newCtx` が作る参照は互いに別の固定の欄とする。メモ表は生成したストアの中を指す参照とし、miss の後に表を読み戻す定理はその参照のレンズ則を仮定する。 | RuntimeCore.lean:11 | |
| R2 | `Data.Set`、`Data.IntSet`、`Data.IntMap`、`Data.Map` は、所属と検索の関数で写す。 | RuntimeCore.lean:16 | |
| R3 | `Text` は Unicode スカラー値の UTF-8 符号化とし、オフセットを 0 に正規化した Lean の `String` で写す。`T.pack` は恒等、`TU.lengthWord8` はバイト長、`TA.unsafeIndex` は範囲内のバイトの読み出し、`TU.iter` はバイト位置から始まるスカラー値の復号とする。 | RuntimeCore.lean:19 | check-concrete-terminals.sh（[CheckUtf8Runtime.hs](CheckUtf8Runtime.hs) が最後の二つを実ライブラリで確かめる） |
| R4 | 位置はバイトオフセットのまま扱う。行と列への変換は [LineIndex.lean](LineIndex.lean) が別に証明する。 | RuntimeCore.lean:25 | check.sh（line-of.source と CheckLineIndex.hs） |
| R5 | `ctxLogs` に積む取り消しの動作は消して写す。取り消しを実行する `endIteration` と、それを呼ぶ `memoLR` は翻訳しない。 | RuntimeCore.lean:27 | [check-memo-meta.sh](check-memo-meta.sh)（メタ文法のパーサーが `memoLR` を使わないことを確かめる） |
| R6 | メモ化の定理は、回復と計数が無効であること、成長の反復が走っていないこと（`ctxLogs` が空）、規則本体が失敗の記録と依存を空にして始めたときに同じ結果を返すこと（`BodySpec`）、表の項目が本体を評価した結果に等しいこと（キャッシュの不変条件）を仮定に置く。`lit` の比較の繰り返しには、Lean の停止性の証明のために `k < n` の分岐を足す。`go 0` から呼ぶかぎり、足した分岐には到達しない。`many` と `skipMany` の定義には Lean の `partial_fixpoint` を使う。 | RuntimeCoreProof.lean:14、ExtractRuntimeCore.hs | check-runtime-core.sh（四つの行を消した変異を証明が拒否する）、check-memo-tables.sh |
| R7 | 生成コードの値は Haskell の値と変数の束縛であり、`exec` と `execM` の値はモデルの残りの入力と環境である。`parseTops` が返す `[Top]` の中身は、前提 M3 のとおり特徴づけない。繰り返しでは、生成コードの `many` と `skipMany` は反復の束縛を捨て、`exec` と `execM` は環境を次の反復に渡す。ScopedEnv の解析は本体が読む名前を規則の中で束縛したものに限るが、二つの繰り返しの意味が同じ結果を返すことは示していない。生成コードの組み合わせ子の並びが本体に対応することは、ExtractSelfHostedFile.hs の読み取り（前提 X1）に拠る。メモ表（SelfHostedMemo.lean）と、本体の読み取りで落とす書き方（RuntimeForms.lean）は、前提から外れた。 | SelfHostedRuntime.lean:474（`exec`）、SelfHostedMemo.lean:78（`execM`） | check-strict-file.sh（ExtractSelfHostedFile.hs が生成コードの組み合わせ子の並びを照合する）、check-runtime-core.sh、check-file-tops.sh、check.sh の境界の入力の比較 |

### 規則の検査、ラベル、テンプレート、import の前提

| 番号 | 前提 | 仮定する場所 | 見張る検査 |
| --- | --- | --- | --- |
| C1 | `classify` の結果、`codeVariables`、`Data.Char.isUpper` と `toUpper` は、プローブが文法ごとに表として与える。 | CheckGroupsModel.lean | check-check-groups.sh |
| C2 | `stronglyConnComp` の強連結成分から得る規則の集合は、規則名が重ならない文法では、左端の呼び出しで自分に戻れる規則の集合に一致する。 | CheckGroupsModel.lean | check-check-groups.sh（`leftRecursiveRules` を比べる） |
| C3 | `Data.List.sortOn` と `List.mergeSort` は、同じ順序による安定な整列なので、同じ列を返す。位置、長さ、数は自然数で写す。 | CheckGroupsModel.lean | check-check-groups.sh |
| L1 | 訪問済みの集合の鍵に使う Haskell の `show` と Lean の `repr` は、どちらも単射である。 | LabelCheckModel.lean | check-label-check.sh |
| L2 | `stronglyConnComp` の強連結成分は、規則名が重ならない文法では、モデルが到達可能性から求めるものと一致する。規則名の重複は `assemble` と `resolveImports` が拒否し、`expandTemplates` はインスタンスにどの規則とも異なる名前を付ける（TemplateExpansionWhole）。 | LabelCheckModel.lean | check-label-check.sh（左再帰の分類を比べる） |
| L3 | `isAlpha` と `isAlphaNum` は AssembleChars の表と一致する。Haskell の `Int` は溢れない。 | LabelCheckModel.lean | check-assemble-predicates.sh（表を作り直して照合する） |
| L4 | `labelWarnings` と `stripLabelsAs` が受け取る文法は `expandTemplates` の後なので、テンプレートの呼び出しを含まない。`stripLabels` がテンプレートの引数に入らないことは、前提ではなく `stripLabels_template_args`（LabelsTranslatedProof.lean:285）が翻訳について示す。 | LabelCheckTheorems.lean | check-pipeline.sh（呼び出しの順を固定する） |
| T1 | `haskellIdents`（`codeVariables`）、インスタンスの型を作る `instanceType`、型の分類 `classifiedTypes . classify` は任意の関数として扱う。プローブは型を比べない。 | TemplateExpansionWhole.lean | |
| T2 | メモ表のキーは位置を除いた引数の `show` であり、導出された `Show` が単射である。モデルは引数を構造で比べる。 | TemplateExpansionWhole.lean | check-template-expansion-whole.sh（インスタンスの共有を比べる） |
| T3 | `Data.Map` と `Data.Set` はリストで写す。`M.fromList` は同じキーの最後の束縛を残し、`S.toAscList` は整列して重複を除く。 | TemplateExpansionWhole.lean | check-template-expansion-whole.sh |
| T4 | 位置は自然数で写し、プローブは一つのファイルの `Loc f l c` を `l * 100000 + c` と書く。 | TemplateExpansionWhole.lean、PublicGeneration.lean:164 | check-template-expansion-whole.sh |
| T5 | `show (k :: Integer)` は `Nat.repr` と一致する。 | TemplateExpansionFresh.lean | [check-template-expansion-fresh.sh](check-template-expansion-fresh.sh)（プローブで確かめる） |
| I1 | `assemble` のモデルでは、`Text` の操作を `List Char` で表し、`Int` は 64 ビットとし、診断の文言と位置を消す。 | AssembleValidation.lean、AssemblePredicates.lean | check-assemble-predicates.sh、check-assemble-validation.sh |

### 生成した Haskell と GHC の前提

| 番号 | 前提 | 仮定する場所 | 見張る検査 |
| --- | --- | --- | --- |
| G1 | lexer の前提 `initial`、`trace`、`tokens_match`: GHC の lexer は、`render` の出力の各前半に `finalize` をかけたテキストから、合成したモジュールの字句の列を返す。 | RenderComposition.lean、RenderFinalizeModule.lean | check-render-finalize.sh（7 個の文法で、`finalize` の後のテキストを GHC が受理する） |
| G2 | `lexed`（`invariant3_committed_text`）: GHC の lexer は、コミットしたファイルから証明書の字句の列を返す。トレースの LEXID の呼び出しとして観測し、[check-lexer-trace.awk](check-lexer-trace.awk) が shift と照合する。GHC の lexer の Lean のモデルからは導いていない。 | CommittedModuleDerivations.lean:78 | check-ghc-parser-trace.sh |
| G3 | `Derives` は、Happy の優先順位と結合の宣言と、衝突の解決を写さない。文脈自由の導出があっても、GHC の LALR のパーサーが同じ字句の列を受理するとは限らない。 | HaskellDerivation.lean:14 | check-ghc-parser-trace.sh と check-render-finalize.sh（生成したモジュールを GHC のパーサーで読む） |
| G4 | `Parser.y` の規則の意味アクションが行う検査（構文解析の後の検査で入力を拒否するもの）を写さない。 | GHCGrammar.lean（生成） | G3 と同じ |
| G5 | Happy がレイアウトを閉じるために挿入する `error` トークン（`close -> error`）は、`layoutGrammar` で消す。導出は、GHC のパーサーがどの位置でレイアウトを閉じるかを確かめない。 | LayoutDerivation.lean:7 | G3 と同じ |
| G6 | RenderPrinting.lean の `valid`: 規則の名前は ASCII の `idTail` の文字からなり、束縛の名前は GHC の予約語でない varid である。検査器は ASCII 以外の文字を含む規則の名前も受理するが、字句のモデルはそれを読まない。 | RenderPrinting.lean | check-render-printing.sh（そのテキストを比較から外し、外した件数を表示する） |
| G7 | RenderPrinting.lean の `agrees`（`printed_ghc`）: GHC の lexer は、印字した式のテキストでモデルと同じ字句の列を返す。この前提は、`finalize` をかけた後のテキストについての前提として読む。対象の式は利用者のコードを含まないので復帰マーカーを含まず、印字する改行の後には必ず十個の空白が続く。 | RenderPrinting.lean:996 | check-render-printing.sh（GHC の lexer が渡す終端記号の番号を比べる） |
| G8 | `source_ok`、`languages_ok`、`shown_ok`: 文法のファイル名、`%language` の引数、`show` した出力のファイル名は改行を含まない。`generate` は制御文字を含むファイル名を拒み、Peg.hpeg の指示の引数は `(!'\n' .)*` であり、`show` は改行をエスケープする。 | RenderFinalize.lean、RenderFinalizeModule.lean | check-inner-generation.sh（ファイル名の検査を固定する） |
| G9 | RenderDeclarationsGHC.lean と RenderDeclarationBinders.lean では、子の型と式の導出、文字列から GHC のトークンへの対応、Haskell の遅延評価、任意の hpeg の構文木から名前の一覧を取り出す処理を前提に置く。 | RenderDeclarationsGHC.lean、RenderDeclarationBinders.lean | check-render-declarations-ghc.sh、check-render-declaration-binders.sh |
| E1 | 埋め込みコードの前提（任意の文法）: `verbatim_split`、`verbatim_imports_ok`、`verbatim_decls_ok`、export の項目の `user_ok`、生成した宣言の `decls_ok`、`GeneratedParts` の中の規則本体の導出。埋め込みブロックのトークンは import 宣言の並びとトップレベル宣言の並びをこの順に連ねたものであり、アクション、意味述語、引数のコード、型は挿入箇所の構文カテゴリから導出できる。本文に含まれるコメントやレイアウトが周囲に及ぼす影響もここに含まれる。 | RenderComposition.lean、RenderFinalizeModule.lean | なし。利用者が書く Haskell 全体を形式化しない限り、検査では置き換えられない。二つのメタ文法と Extensions.hpeg では、証明書がこの前提に置き換わる。ほかの fixture は、GHC で検査するパッケージのテストに任せる。 |

前提の数は、公開の入口と全体が 7、構文解析とランタイムが 10、規則の検査とラベルとテンプレートと import が 13、生成した Haskell と GHC が 10 で、合わせて 40 である。

前提のほかに、証明書が覆わない範囲がある。
`packages/peg-lsp` は、生成した `Peg.Lsp.JsonParser` を `default-extensions: LambdaCase OverloadedStrings` の下でコンパイルする。
このモジュールの証明書はなく、不変条件 3 は任意の文法についての定理（前提 E1 を置く）だけで扱う。

## 公理の監査

[Audit.lean](Audit.lean) は、一覧に挙げたモジュールと Audit.lean 自身の定理ごとに依存する公理を列挙し、Lean 標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理を使うと失敗する。
すべてのモジュールを作った後で動かすため、[check.sh](check.sh) の最後に置く。
[check-audit-coverage.sh](check-audit-coverage.sh) は、定理を持つ手書きのモジュールと、定理を書き出す生成器が作るモジュールが、この一覧にすべて載っていることを確かめる。
いまの main で動かすと、「159 modules with theorems are audited」と表示する。
SplitMetaFile.lean が書き出す項目ごとの証明書は、CertifiedPublicFiles.lean の定理の前提になるので、その定理の公理の一覧に含まれる。

## 実行方法

リポジトリのルートで次のコマンドを実行する。
GHC と Cabal はプロジェクト指定の版を使う。
生成 Haskell の構文導出には Happy 2.1.7 が必要である。
`happy` が PATH 上にない場合は実行ファイルを `HAPPY` に指定する。
GHC 9.10.3 の `compiler/GHC/Parser.y` を `GHC_PARSER_Y` に、`compiler/GHC/Parser/Lexer.x` を `GHC_LEXER_X` に指定するか、`ghc-9.10.3-release` タグを持つ GHC チェックアウトを `GHC_SOURCE` に指定する。
elan が [lean-toolchain](lean-toolchain) の Lean を選び、check.sh は `lean --version` がその指定と一致することを最初に確かめる。

```sh
cabal build exe:peg-hs
verification/check.sh
```

check.sh は、Lean の版を確かめた後に check-audit-coverage.sh を、最後に Audit.lean を動かし、そのあいだで各段のモジュールを作って検査スクリプトを呼ぶ。
一部の検査スクリプトは、文法ファイルの該当の規則の範囲の SHA-256 を照合する（check-expression-depth.sh、check-escape-predicates.sh、check-parameter-predicates.sh）。

対応テストでは、深さ 256 の前後で `parseTops` と Lean の結果を比較する。
空ファイル、末尾の余分な文字、未定義参照については実際の診断を確認する。
実ファイルから抽出した規則の署名は三件とも Lean で証明し、未定義参照を加えた負例の証明は Lean が拒否することを確認する。
二つのメタ文法は実ファイルから再生成し、出力を GHC で検査する。
区切りが閉じたアクションに不完全な Haskell 式を入れたケースでは、GHC が構文エラーを返すことを確認する。

三つの fixture について、Happy が GHC の文法から生成したパーサーで全文を読み、各 shift と reduce を記録する。
Lean は各 reduce の右辺をスタックと照合し、全トークンを消費して開始記号だけが残ることを検査する。
GHC が暗黙のレイアウトを閉じるために挿入する `error` トークンは、元のトークン列と区別する。
ソース文字列からトークンへの変換には GHC の lexer を使う。

### 定理の関係の図

[proof-graph.sh](proof-graph.sh) は、コンパイル済みのモジュールを読み、定理どうしの関係を Mermaid の図にして Markdown のファイルに書く。
図は、[ProofGraph.lean](ProofGraph.lean) が Lean の環境の定理の証明項がどの定数を参照するかをたどって作るので、証明が変われば図も変わる。
check.sh は図を作らない。
モジュールを残すには、空のディレクトリを `CHECK_WORK` に指定して check.sh を動かし、そのディレクトリと、その下の `item-certificates` を `:` でつないで渡す。

```sh
CHECK_WORK=/tmp/work verification/check.sh
verification/proof-graph.sh [-d 参照の回数] /tmp/work:/tmp/work/item-certificates 出力先
```

出力先には、全体図の overview.md と、不変条件ごとの図の invariant1.md〜invariant3.md を書く。
全体図は、公開の入口の定理と段を節点にし、段から段への辺に定理の参照の数を付ける。
どのモジュールがどの段に属し、段が実装とどう対応するかは、[proof-graph-stages.tsv](proof-graph-stages.tsv) が「段ごとの証明と実装との対応」の表に合わせて決める。
不変条件ごとの図は、公開の入口から `-d`（既定は 2）回の参照で届く定理と、「公開の入口から結論までの定理の連なり」の表にある定理だけを節点にし、ほかの定理を通る参照を破線の辺に畳む。
構造体 `Premises` の欄と、公開の入口の定理が仮定に取る全称の命題（`renderShape` など）は、前提の節点（六角形）として描く。
表の定理が環境に無いとき、公開の入口から届かないとき、段の無いモジュールがあるときは、標準エラーに書く。

### CI での動き方

CI（`.github/workflows/ci.yml`）の `haskell` ジョブは、ビルドの後に check.sh を動かす。
このジョブは、elan v4.2.4 を SHA-256 を確かめて入れ、Happy 2.1.7 を入れ、ghc/ghc のコミット `3f4d7d38b9661435bdde981451ac50c4335ed090` から `Parser.y` と `Lexer.x` を取得して `GHC_PARSER_Y` と `GHC_LEXER_X` に指定する。
`changes` ジョブは、変更が文書だけのときにビルドとテストを省く（`scripts/ci-changes.mjs`、[ADR 0101](../docs/adr/0101-run-ci-for-documents-that-tests-read.md)）。
この README だけを変えたときは、check.sh は動かない。
メタ文法、生成器、検査器、翻訳器、証明、ツールチェーンのどれかを変えると、check.sh が動く。

## 対象外

[ADR 0097](../docs/adr/0097-verify-hpeg-and-generated-haskell-in-lean.md) の「実装しないこと」により、次のものは検証しない。

- 生成した Haskell の型。
- 利用者の意味アクションの停止性と実行時の安全性。
- ファイルシステムへのアクセス、バイト列のデコード、実機でのメモリやスタックの上限、生成したパーサーに与える入力。

不正入力への保証は、文法を読み込んで生成結果を返す純粋な処理を対象とする。
停止の証明は計算資源の上限を含まないので、巨大な入力による資源の枯渇には別の根拠が要る。
