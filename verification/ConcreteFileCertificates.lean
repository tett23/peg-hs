import MetaExecution

open PegHs.EnvironmentEval PegHs.MetaExecution

namespace PegHs.ConcreteFileCertificates

-- The first TopItem of Peg.hpeg, including its trailing whitespace.
-- This local certificate does not establish FileResult for the entire file.
def firstTopItem : List Char := "%module Peg.Grammar.SelfHosted\n\n# 次のラベルは、ラベルの安全性の検査（ADR 0028）が危険と判定するが、安全である。\n# 識別子と空白の文字は意味述語で判定しており、検査は意味述語がどの文字でも成功\n# しうるとみなすため、空白や識別子で始まる別の選択肢と区別できない。安全なことは、\n# ラベルを外した文法との受理の一致のテストで確かめている。\n%safe verbatim\n".toList

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem invariant1_peg_first_top_item_window :
    runFuel (context false firstTopItem) 12000
      ((context false firstTopItem).rules 1) firstTopItem.length {} = some (.ok 15 {}) := by
  decide +kernel

theorem invariant1_peg_first_top_item_derives :
    Derives (context false firstTopItem)
      ((context false firstTopItem).rules 1) firstTopItem.length {} (.ok 15 {}) :=
  invariant1_runFuel_sound invariant1_peg_first_top_item_window

#print axioms invariant1_peg_first_top_item_derives

end PegHs.ConcreteFileCertificates
