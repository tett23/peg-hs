import Parsing

namespace PegVerification

-- The exact PEG body of InlineSp <- [ \t]*, with the class expanded into
-- two single-character alternatives.
def inlineSp : Expr := .many (.choice (.char ' ') (.char '\t'))

def isInlineSpace (c : Char) : Bool := c == ' ' || c == '\t'

theorem invariant1_inlineSp (xs : List Char) :
    run inlineSp xs = .ok (xs.dropWhile isInlineSpace) := by
  induction xs with
  | nil => simp [inlineSp, run, repeatRun]
  | cons c cs ih =>
      change repeatRun (run (.choice (.char ' ') (.char '\t'))) (cs.length + 1) cs =
        .ok (cs.dropWhile isInlineSpace) at ih
      by_cases space : c = ' '
      · subst c
        simpa [inlineSp, run, repeatRun, isInlineSpace] using ih
      · by_cases tab : c = '\t'
        · subst c
          simpa [inlineSp, run, repeatRun, isInlineSpace, space] using ih
        · simp [inlineSp, run, repeatRun, isInlineSpace, space, tab]

-- The exact PEG body of Comment <- '#' (!'\n' .)*.
def commentTail : Expr := .many (.seq (.notAhead (.char '\n')) .any)
def comment : Expr := .seq (.char '#') commentTail

def beforeNewline (c : Char) : Bool := c != '\n'

theorem invariant1_commentTail (xs : List Char) :
    run commentTail xs = .ok (xs.dropWhile beforeNewline) := by
  induction xs with
  | nil => simp [commentTail, run, repeatRun, Except.bind]
  | cons c cs ih =>
      change repeatRun (run (.seq (.notAhead (.char '\n')) .any)) (cs.length + 1) cs =
        .ok (cs.dropWhile beforeNewline) at ih
      by_cases newline : c = '\n'
      · subst c
        simp [commentTail, run, repeatRun, Except.bind, beforeNewline]
      · have keep : beforeNewline c = true := by simp [beforeNewline, newline]
        simpa [commentTail, run, repeatRun, Except.bind, keep, newline] using ih

theorem invariant1_comment (xs : List Char) :
    run comment ('#' :: xs) = .ok (xs.dropWhile beforeNewline) := by
  simpa [comment, run, Except.bind] using invariant1_commentTail xs

theorem invariant1_comment_no_marker (c : Char) (xs : List Char) (neq : c ≠ '#') :
    run comment (c :: xs) = .error none := by
  simp [comment, run, Except.bind, neq]

end PegVerification

#print axioms PegVerification.invariant1_inlineSp

#print axioms PegVerification.invariant1_commentTail
#print axioms PegVerification.invariant1_comment
#print axioms PegVerification.invariant1_comment_no_marker

-- Invariant 1 boundary inputs for the two lexical rules.
example : PegVerification.run PegVerification.inlineSp [] = .ok [] := by
  simpa using PegVerification.invariant1_inlineSp []
example : PegVerification.run PegVerification.inlineSp [' ', '\t', 'x'] = .ok ['x'] := by
  simpa [PegVerification.isInlineSpace] using
    PegVerification.invariant1_inlineSp [' ', '\t', 'x']
example : PegVerification.run PegVerification.comment ['#'] = .ok [] := by
  simpa using PegVerification.invariant1_comment []
example : PegVerification.run PegVerification.comment ['#', 'a', '\n', 'z'] = .ok ['\n', 'z'] := by
  have result := PegVerification.invariant1_comment ['a', '\n', 'z']
  simpa [PegVerification.beforeNewline, List.dropWhile] using result
example : PegVerification.run PegVerification.comment [] = .error none := by
  simp [PegVerification.comment, PegVerification.run, Except.bind]
