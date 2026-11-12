import EnvironmentDepth

namespace PegHs.EnvProjection
open PegHs.EnvironmentEval PegHs.EnvironmentDepth

def hasCapture (env : Env) (name : String) : Bool :=
  env.captures.any (fun pair => pair.1 == name)

-- Equality of every value read by the translated metagrammar's predicates,
-- depth actions, and argument calculation. Extra shadowed list entries are
-- ignored, so this relation is weaker than structural Env equality.
structure ObsEq (left right : Env) : Prop where
  depth : left.depth = right.depth
  resultDepth : left.resultDepth = right.resultDepth
  capture : ∀ name, left.lookup name = right.lookup name
  valueDepth : ∀ name, left.valueDepth name = right.valueDepth name
  presence : ∀ name, hasCapture left name = hasCapture right name

theorem ObsEq.refl (env : Env) : ObsEq env env :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem ObsEq.symm {left right : Env} (same : ObsEq left right) :
    ObsEq right left :=
  ⟨same.depth.symm, same.resultDepth.symm,
    fun name => (same.capture name).symm,
    fun name => (same.valueDepth name).symm,
    fun name => (same.presence name).symm⟩

theorem ObsEq.trans {a b c : Env} (ab : ObsEq a b) (bc : ObsEq b c) :
    ObsEq a c :=
  ⟨ab.depth.trans bc.depth, ab.resultDepth.trans bc.resultDepth,
    fun name => (ab.capture name).trans (bc.capture name),
    fun name => (ab.valueDepth name).trans (bc.valueDepth name),
    fun name => (ab.presence name).trans (bc.presence name)⟩

theorem lookup_put (env : Env) (name query : String) (text : List Char) :
    (env.put name text).lookup query =
      if query = name then text else env.lookup query := by
  by_cases h : query = name
  · subst query
    simp [Env.put, Env.lookup]
  · have hb : (name == query) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [Env.put, Env.lookup, h, hb]

theorem presence_put (env : Env) (name query : String) (text : List Char) :
    hasCapture (env.put name text) query =
      if query = name then true else hasCapture env query := by
  by_cases h : query = name
  · subst query; simp [Env.put, hasCapture]
  · have hb : (name == query) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [Env.put, hasCapture, h, hb]

theorem put_congr {left right : Env} (same : ObsEq left right)
    (name : String) (text : List Char) :
    ObsEq (left.put name text) (right.put name text) := by
  refine ⟨same.depth, same.resultDepth, ?_, ?_, ?_⟩
  · intro query
    rw [lookup_put, lookup_put]
    split <;> first | rfl | exact same.capture query
  · exact same.valueDepth
  · intro query
    rw [presence_put, presence_put]
    split <;> first | rfl | exact same.presence query

theorem valueDepth_put (env : Env) (name query : String) (depth : Nat) :
    (env.putDepth name depth).valueDepth query =
      if query = name then some depth else env.valueDepth query := by
  by_cases h : query = name
  · subst query; simp [Env.putDepth, Env.valueDepth]
  · have hb : (name == query) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [Env.putDepth, Env.valueDepth, h, hb]

theorem putDepth_congr {left right : Env} (same : ObsEq left right)
    (name : String) (depth : Nat) :
    ObsEq (left.putDepth name depth) (right.putDepth name depth) := by
  refine ⟨same.depth, same.resultDepth, same.capture, ?_, same.presence⟩
  intro query
  rw [valueDepth_put, valueDepth_put]
  split <;> first | rfl | exact same.valueDepth query

theorem resultDepth_congr {left right : Env} (same : ObsEq left right)
    (depth : Nat) :
    ObsEq {left with resultDepth := depth} {right with resultDepth := depth} :=
  ⟨same.depth, rfl, same.capture, same.valueDepth, same.presence⟩

def predicateProjection (name : Option String) (env : Env) : SemanticPredicates.Env :=
  { depth := env.depth, captured := name.map env.lookup |>.getD [] }

theorem predicateProjection_congr {left right : Env} (same : ObsEq left right)
    (name : Option String) :
    predicateProjection name left = predicateProjection name right := by
  cases name with
  | none => simp [predicateProjection, same.depth]
  | some name => simp [predicateProjection, same.depth, same.capture name]

theorem semanticPredicate_congr {left right : Env} (same : ObsEq left right)
    (classes : SemanticPredicates.Classes) (kind : SemanticPredicates.Kind)
    (name : Option String) :
    SemanticPredicates.eval classes kind (predicateProjection name left) =
      SemanticPredicates.eval classes kind (predicateProjection name right) := by
  rw [predicateProjection_congr same name]

def ActionReads (left right : Env) : DepthAction → Prop
  | .zero => True
  | .copy name | .successor name =>
      left.valueDepth name = right.valueDepth name
  | .add a b | .maximum a b =>
      left.valueDepth a = right.valueDepth a ∧
        left.valueDepth b = right.valueDepth b
  | .plusIfBound value presence =>
      left.valueDepth value = right.valueDepth value ∧
        hasCapture left presence = hasCapture right presence

theorem depthAction_only_reads {left right : Env} (action : DepthAction)
    (reads : ActionReads left right action) :
    DepthAction.eval left action = DepthAction.eval right action := by
  cases action with
  | zero => rfl
  | copy name => exact reads
  | successor name =>
      change left.valueDepth name = right.valueDepth name at reads
      simp [DepthAction.eval, reads]
  | add a b | maximum a b =>
      rcases reads with ⟨ha, hb⟩
      simp [DepthAction.eval, ha, hb]
  | plusIfBound value presence =>
      rcases reads with ⟨hv, hp⟩
      simp only [DepthAction.eval, hv]
      exact congrArg (fun b => (right.valueDepth value).bind fun a =>
        some (a + if b = true then 1 else 0)) hp

theorem depthAction_congr {left right : Env} (same : ObsEq left right)
    (action : DepthAction) :
    DepthAction.eval left action = DepthAction.eval right action := by
  cases action with
  | zero => rfl
  | copy name | successor name => simp [DepthAction.eval, same.valueDepth name]
  | add a b | maximum a b =>
      simp [DepthAction.eval, same.valueDepth a, same.valueDepth b]
  | plusIfBound value presence =>
      have presenceEq :
          (left.captures.any fun pair => pair.1 == presence) =
            (right.captures.any fun pair => pair.1 == presence) :=
        same.presence presence
      simp only [DepthAction.eval, same.valueDepth value]
      rw [presenceEq]

theorem depthArg_congr {left right : Env} (same : ObsEq left right)
    (arg : DepthArg) : evalDepthArg left arg = evalDepthArg right arg := by
  cases arg with
  | zero => rfl
  | current | successor => simp [evalDepthArg, same.depth]
  | plusValue name => simp [evalDepthArg, same.depth, same.valueDepth name]

def OptionObsEq : Option Env → Option Env → Prop
  | none, none => True
  | some left, some right => ObsEq left right
  | _, _ => False

theorem enterCall_congr {left right : Env} (same : ObsEq left right)
    (sites : Nat → Option CallSite) (site : Nat) :
    OptionObsEq (enterCall sites site left) (enterCall sites site right) := by
  unfold enterCall
  cases h : sites site with
  | none => simp [OptionObsEq]
  | some call =>
      rcases call with ⟨caller, callee, args⟩
      cases args with
      | nil => simpa [h, OptionObsEq] using same
      | cons source rest =>
          cases rest with
          | nil =>
              cases hs : depthArgOf source with
              | none => simp [hs, OptionObsEq]
              | some arg =>
                  have equalDepth := depthArg_congr same arg
                  cases hd : evalDepthArg left arg with
                  | none =>
                      simp [hs, hd, ← equalDepth, OptionObsEq]
                  | some depth =>
                      simp [hs, hd, ← equalDepth, OptionObsEq]
                      exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
          | cons extra tail => simp [OptionObsEq]

theorem bindShape_congr {left right : Env} (same : ObsEq left right)
    (shapeAt : Nat → String → List Char → Option PegHs.ExpressionDepth.Shape)
    (site : Nat) (name : String) (text : List Char) :
    OptionObsEq (bindShape shapeAt site name text left)
      (bindShape shapeAt site name text right) := by
  have captured : ObsEq ((left.put name text).putDepth name left.resultDepth)
      ((right.put name text).putDepth name right.resultDepth) := by
    simpa only [same.resultDepth] using
      putDepth_congr (put_congr same name text) name left.resultDepth
  unfold bindShape
  cases shapeAt site name text with
  | none => exact captured
  | some shape =>
      simp only [same.resultDepth]
      split
      · simpa only [OptionObsEq, same.resultDepth] using captured
      · trivial

theorem leaveCall_congr {callerLeft callerRight calleeLeft calleeRight : Env}
    (callers : ObsEq callerLeft callerRight)
    (callees : ObsEq calleeLeft calleeRight)
    (sites : Nat → Option CallSite)
    (shapeAt : Nat → String → List Char → Option PegHs.ExpressionDepth.Shape)
    (site : Nat) :
    ObsEq ((hooks sites shapeAt).leaveCall site callerLeft calleeLeft)
      ((hooks sites shapeAt).leaveCall site callerRight calleeRight) := by
  simpa [hooks, callees.resultDepth] using
    resultDepth_congr callers calleeLeft.resultDepth

#print axioms predicateProjection_congr
#print axioms depthAction_only_reads
#print axioms depthAction_congr
#print axioms enterCall_congr
#print axioms bindShape_congr
#print axioms leaveCall_congr

end PegHs.EnvProjection
