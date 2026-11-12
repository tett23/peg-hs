import PublicParsing

namespace PegHs.LabelPropagation
open PegHs.PublicParsing

abbrev Reply := StartResult Unit

-- Frames around an evaluated child in strict (non-recovering) mode.
-- State used to choose the farthest diagnostic does not alter these outcomes.
inductive Frame where
  | bind (next : Nat → Reply)
  | choice (alternative : Reply)
  | optional (start : Nat)
  | label (start : Nat) (name : String) (msg : Option String)

def unwind (result : Reply) : Frame → Reply
  | .bind next => match result with
    | .ok pos _ => next pos
    | other => other
  | .choice alternative => match result with
    | .fail => alternative
    | other => other
  | .optional start => match result with
    | .fail => .ok start ()
    | other => other
  | .label start name msg => match result with
    | .fail => .throwLabel start name msg
    | other => other

theorem invariant1_frames_preserve_throw (frames : List Frame) (pos : Nat)
    (name : String) (msg : Option String) :
    frames.foldl unwind (.throwLabel pos name msg) = .throwLabel pos name msg := by
  induction frames with
  | nil => rfl
  | cons f fs ih => cases f <;> exact ih

def look (positive : Bool) (pos : Nat) (r : Reply) : Reply :=
  match r with
  | .ok _ _ => if positive then .ok pos () else .fail
  | _ => if positive then .fail else .ok pos ()

theorem invariant1_look_catches (pos atError : Nat) (name : String) (msg : Option String) :
    look true pos (.throwLabel atError name msg) = .fail ∧
      look false pos (.throwLabel atError name msg) = .ok pos () := ⟨rfl, rfl⟩

-- Each loop iteration consumes at least one byte. The bounded cursor carries
-- the actual runtime invariant that no successful match goes past end of input.
inductive BoundedReply (endPos : Nat) where
  | ok (pos : Fin (endPos + 1))
  | fail
  | throwLabel (pos : Nat) (name : String) (msg : Option String)

def manyAt {endPos : Nat} (step : Fin (endPos+1) → BoundedReply endPos)
    (i : Fin (endPos+1)) : Reply :=
  match step i with
  | .ok j => if i < j then manyAt step j else .ok i.val ()
  | .fail => .ok i.val ()
  | .throwLabel t l m => .throwLabel t l m
termination_by endPos - i.val
decreasing_by have := j.isLt; change i.val < j.val at *; omega

inductive ReachesThrow {endPos : Nat} (step : Fin (endPos+1) → BoundedReply endPos)
    (t : Nat) (l : String) (m : Option String) : Fin (endPos+1) → Prop where
  | now {i} (result : step i = .throwLabel t l m) : ReachesThrow step t l m i
  | advance {i j} (result : step i = .ok j) (progress : i < j)
      (rest : ReachesThrow step t l m j) : ReachesThrow step t l m i

theorem invariant1_many_throw {endPos : Nat} {step : Fin (endPos+1) → BoundedReply endPos}
    {i t l m} : manyAt step i = .throwLabel t l m ↔ ReachesThrow step t l m i := by
  constructor
  · intro result
    induction i using manyAt.induct step with
    | case1 i j h progress ih =>
      exact .advance h progress (ih (by rw [manyAt, h] at result; simpa only [ite_true, progress] using result))
    | case2 i j h progress => rw [manyAt, h] at result; simp [progress] at result
    | case3 i h => rw [manyAt, h] at result; contradiction
    | case4 i t' l' m' h => rw [manyAt, h] at result; cases result; exact .now h
  · intro reached
    induction reached with
    | now h => rw [manyAt, h]
    | advance h progress _ ih => rw [manyAt, h]; simpa only [progress, ite_true] using ih

theorem invariant2_unhandled_label (frames : List Frame) (endPos t : Nat) (l : String)
    (m : Option String) (diagnostic : Failure → String) :
    entry endPos (frames.foldl unwind (.throwLabel t l m)) diagnostic =
      .error [diagnostic (.labelled l m)] := by rw [invariant1_frames_preserve_throw]; rfl

end PegHs.LabelPropagation
