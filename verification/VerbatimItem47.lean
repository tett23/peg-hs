import Verbatim47Data
import VerbatimRule
import WindowReads
import PrefixReplay

namespace PegHs.MetaExecution
open EnvironmentEval

def verbatimItem47 : List Char :=
  ['%', '{'] ++ Verbatim47Data.suffix0 ++ ['\n', '\n']

private def wsWindow47 : List Char := ['\n', '\n', 'F']

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem wsObserved47 (mode : Bool) :
    runFuel (context mode wsWindow47) 512 (.call 3 4) wsWindow47.length {} =
      some (.ok 1 {}) := by
  cases mode <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem wsFits47 (mode : Bool) :
    readsFit (context mode wsWindow47) 512 (.call 3 4) wsWindow47.length {} = true := by
  cases mode <;> decide +kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem invariant1_verbatim_item47 (mode : Bool) (pre rest : List Char) :
    Derives (context mode (pre ++ verbatimItem47 ++ ('F' :: rest))) (.call 1 1)
      (verbatimItem47.length + ('F' :: rest).length) {} (.ok ('F' :: rest).length {}) := by
  let tail := wsWindow47 ++ rest
  let xs := Verbatim47Data.suffix0 ++ tail
  have closed : verbatimRest xs = '}' :: '%' :: tail := by
    simpa [xs, tail, List.append_assoc] using
      (invariant1_verbatim_rest_append Verbatim47Data.suffix0 [] tail
        Verbatim47Data.rest0)
  let beforeWs := pre ++ ['%', '{'] ++ Verbatim47Data.suffix0
  let wsCtx := context mode wsWindow47
  have localStep := invariant1_window_run (wsObserved47 mode) (wsFits47 mode)
    (show wsWindow47.length ≤ wsCtx.input.length by
      cases mode <;> exact Nat.le_refl _) rest
  have bound : wsWindow47.length + rest.length ≤ (appendInput wsCtx rest).input.length := by
    have inputEq : wsCtx.input = wsWindow47 := by cases mode <;> rfl
    simp [appendInput, inputEq]
  have lifted := invariant1_prepend_derivation beforeWs localStep bound
  have ctxEq : appendInput wsCtx rest = context mode (wsWindow47 ++ rest) := by
    cases mode <;> rfl
  rw [ctxEq] at lifted
  have beforeEq : {context mode (wsWindow47 ++ rest) with
      input := beforeWs ++ (wsWindow47 ++ rest)} =
      context mode (beforeWs ++ (wsWindow47 ++ rest)) := by
    cases mode <;> rfl
  have field : (context mode (wsWindow47 ++ rest)).input = wsWindow47 ++ rest := by
    cases mode <;> rfl
  rw [field] at lifted
  rw [beforeEq] at lifted
  have inputEq : beforeWs ++ (wsWindow47 ++ rest) = pre ++ '%' :: '{' :: xs := by
    simp [beforeWs, xs, tail, wsWindow47, List.append_assoc]
  rw [inputEq] at lifted
  have ws : Derives (context mode (pre ++ '%' :: '{' :: xs)) (.call 3 4)
      tail.length {} (.ok ('F' :: rest).length {}) := by
    simpa [tail, wsWindow47, Reply.shift, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using lifted
  have item := invariant1_verbatim_top_item mode pre xs tail ('F' :: rest).length
    closed ws
  have source : pre ++ '%' :: '{' :: xs =
      pre ++ verbatimItem47 ++ ('F' :: rest) := by
    simp [xs, tail, verbatimItem47, wsWindow47, List.append_assoc]
  rw [source] at item
  have start : xs.length + 2 = verbatimItem47.length + ('F' :: rest).length := by
    simp [xs, tail, verbatimItem47, wsWindow47, List.length_append] <;> omega
  rw [start] at item
  exact item

#print axioms invariant1_verbatim_item47

end PegHs.MetaExecution
