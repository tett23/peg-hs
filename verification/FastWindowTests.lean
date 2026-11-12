import FastWindow

namespace PegHs.EnvironmentEval

private def testClasses : PegHs.SemanticPredicates.Classes where
  space := fun c => c == ' '
  alpha := fun _ => false
  alnum := fun _ => false

private def testInputs : Inputs where
  rules := fun _ => .eps
  terms := fun site =>
    if site == 0 then some (.lit ['a'])
    else if site == 1 then some (.lit ['a', 'b'])
    else none
  sites := fun _ => none
  actions := fun _ => none
  classes := testClasses
  predicateEnv := fun _ _ => { captured := [], depth := 0 }
  hooks := defaultHooks
  input := ['a']

-- The first component counts reads from the failed left alternative.
example : fastWindow testInputs 3 (.alt (.terminal 1) (.terminal 0)) 1 {} =
    (false, some (.ok 0 {})) := by rfl
example : fastWindow testInputs 3 (.terminal 0) 1 {} =
    (true, some (.ok 0 {})) := by rfl
example : fastWindow testInputs 3 (.terminal 1) 1 {} =
    (false, some .fail) := by rfl
example : fastWindow testInputs 3 (.ahead (.terminal 1)) 1 {} =
    (false, some .fail) := by rfl
example : fastWindow testInputs 3 (.notAhead (.terminal 1)) 1 {} =
    (false, some (.ok 1 {})) := by rfl
example : fastWindow testInputs 3 (.star .eps) 1 {} =
    (true, some (.ok 1 {})) := by rfl
example : fastWindow testInputs 1 (.call 0 0) 1 {} =
    (false, none) := by rfl
example : fastWindow testInputs 0 .eps 1 {} =
    (false, none) := by rfl
example : windowCheck testInputs 3 (.terminal 0) 1 {} (.ok 0 {}) = true := by rfl
example : windowCheck testInputs 3 (.alt (.terminal 1) (.terminal 0)) 1 {} (.ok 0 {}) = false := by rfl

end PegHs.EnvironmentEval
