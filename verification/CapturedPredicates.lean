import SemanticPredicates

namespace PegHs.CapturedPredicates
open SemanticPredicates

-- Positions are remaining character counts, as in LabeledConcreteBody.runFuel.
def captureAt (input : List Char) (before after : Nat) : Option (List Char) :=
  if after ≤ before ∧ before ≤ input.length then
    some ((input.drop (input.length - before)).take (before - after))
  else none

theorem invariant1_capture_origin (pre body post : List Char) :
    captureAt (pre ++ body ++ post) (body.length + post.length) post.length = some body := by
  simp [captureAt, List.append_assoc]

theorem invariant1_capture_split (xs : List Char) (before after : Nat) (body : List Char) :
    captureAt xs before after = some body ↔
      ∃ pre post, xs = pre ++ body ++ post ∧ before = body.length + post.length ∧
        after = post.length := by
  constructor
  · intro h
    unfold captureAt at h
    split at h
    next valid =>
      simp only [Option.some.injEq] at h
      subst body
      let start := xs.length - before
      let count := before - after
      let tail := xs.drop start
      refine ⟨xs.take start, tail.drop count, ?_, ?_, ?_⟩
      · change xs = xs.take start ++ tail.take count ++ tail.drop count
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      · simp [start, tail, count]; omega
      · simp [start, tail, count]; omega
    next => contradiction
  · rintro ⟨pre, post, rfl, rfl, rfl⟩
    exact invariant1_capture_origin _ _ _

-- The predicate receives the bound substring, including empty captures;
-- failing to obtain a span cannot supply a value to the predicate.
def evalAt (cls : Classes) (kind : Kind) (input : List Char)
    (before after depth : Nat) : Option Bool :=
  (captureAt input before after).map fun text => eval cls kind ⟨text, depth⟩

theorem invariant1_capture_predicate (cls : Classes) (k : Kind)
    (pre body post : List Char) (d : Nat) :
    evalAt cls k (pre ++ body ++ post) (body.length + post.length) post.length d = some true ↔
      Holds cls ⟨body, d⟩ k := by
  unfold evalAt
  rw [invariant1_capture_origin]
  simpa only [Option.map_some, Option.some.injEq] using invariant1_eval_iff cls k ⟨body,d⟩

def singleCharRule (cls : Classes) (k : Kind) : List Char → Option (List Char)
  | [] => none
  | c :: rest => if eval cls k ⟨[c], 0⟩ then some rest else none

theorem invariant1_singleChar (cls : Classes) (k : Kind) (input rest : List Char) :
    singleCharRule cls k input = some rest ↔
      ∃ c, input = c :: rest ∧ Holds cls ⟨[c], 0⟩ k := by
  cases input with
  | nil => simp [singleCharRule]
  | cons c cs =>
    simp only [singleCharRule, List.cons.injEq]
    constructor
    · intro h; split at h
      next valid => cases h; exact ⟨c, ⟨rfl,rfl⟩, (invariant1_eval_iff ..).mp valid⟩
      next => contradiction
    · rintro ⟨_, ⟨rfl,rfl⟩, h⟩
      simp [(invariant1_eval_iff ..).mpr h]

-- TypeText captures the maximal prefix before a newline, checks it, and
-- returns the stripped type while leaving the newline for the caller.
def typeText (cls : Classes) (input : List Char) : Option (List Char × List Char) :=
  let line := input.takeWhile (· != '\n')
  if eval cls .typeText ⟨line,0⟩ then
    some (ParameterPredicates.stripEnd cls.space line, input.dropWhile (· != '\n'))
  else none

def EndsAtLine (input line rest : List Char) : Prop :=
  input = line ++ rest ∧ '\n' ∉ line ∧ (rest = [] ∨ rest.head? = some '\n')

private theorem takeDropLine (line rest : List Char) (noLF : '\n' ∉ line)
    (stop : rest = [] ∨ rest.head? = some '\n') :
    (line ++ rest).takeWhile (· != '\n') = line ∧
    (line ++ rest).dropWhile (· != '\n') = rest := by
  induction line with
  | nil =>
    rcases stop with rfl | h
    · simp
    · cases rest with
      | nil => simp
      | cons x xs => simp at h; subst x; simp
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at noLF
    obtain ⟨ht,hd⟩ := ih noLF.2
    have ne := Ne.symm noLF.1
    simp [ne, ht, hd]

theorem invariant1_typeText_line (cls : Classes) (input line rest : List Char)
    (span : EndsAtLine input line rest) :
    typeText cls input = some (ParameterPredicates.stripEnd cls.space line, rest) ↔
      ∃ c ∈ line, cls.space c = false := by
  obtain ⟨rfl, noLF, stop⟩ := span
  obtain ⟨ht, hd⟩ := takeDropLine line rest noLF stop
  unfold typeText
  rw [ht, hd]
  simpa [Holds] using invariant1_eval_iff cls .typeText ⟨line,0⟩

theorem line_partition (input : List Char) :
    EndsAtLine input (input.takeWhile (· != '\n')) (input.dropWhile (· != '\n')) := by
  induction input with
  | nil => simp [EndsAtLine]
  | cons c cs ih =>
    by_cases h : c = '\n'
    · simp [EndsAtLine, h]
    · obtain ⟨parts, noLF, stop⟩ := ih
      change EndsAtLine (c :: cs) _ _
      simp [EndsAtLine, h, Ne.symm h, parts.symm, noLF, stop]

theorem invariant1_actual_typeText (cls : Classes) (input : List Char) :
    typeText cls input = some
      (ParameterPredicates.stripEnd cls.space (input.takeWhile (· != '\n')),
        input.dropWhile (· != '\n')) ↔
      ∃ c ∈ input.takeWhile (· != '\n'), cls.space c = false :=
  invariant1_typeText_line cls input _ _ (line_partition input)

end PegHs.CapturedPredicates
