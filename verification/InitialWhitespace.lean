import WindowReads

namespace PegHs.MetaExecution
open EnvironmentEval

-- One character of lookahead distinguishes the first directive from whitespace.
def initialComments := "# peg-hs の記法（ADR 0004、0005、0012、0014）を peg-hs 自身で書いた文法。\n# 生成したパーサーは最上位の要素の列を返し、組み立て（Peg.Grammar.Assemble）を通る。\n# 誤りの文言は、ラベル（ADR 0021）の %message で与える（ADR 0089）。\n# 誤りの位置の文字で変わる escape、action、argcode の文言だけは、\n# Peg.Grammar.Parser の labelMessage で作る（ADR 0027）。\n# ラベルは、そこで失敗したらどの選択肢でも成功しえない位置にだけ付ける。\n#\n# 識別子と空白の文字は Peg.Grammar.Assemble の関数で判定する（ADR 0020）。\n".toList
def wsWindow := initialComments ++ ['%']

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem invariant1_initial_whitespace_window (mode : Bool) :
    runFuel (context mode wsWindow) 512 ((context mode wsWindow).rules 4)
      wsWindow.length {} = some (.ok 1 {}) := by
  cases mode <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem invariant1_initial_whitespace_reads (mode : Bool) :
    readsFit (context mode wsWindow) 512 ((context mode wsWindow).rules 4)
      wsWindow.length {} = true := by
  cases mode <;> decide +kernel

end PegHs.MetaExecution
