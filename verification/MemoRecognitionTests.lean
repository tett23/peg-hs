import MemoRecognition

open PegHs.MemoRecognition

-- Invariant 1: an empty strict table evaluates once, then reuses the same result.
private def sample : Nat → Entry Nat := fun k =>
  { result := .ok (k + 1) (k + 1), failure := k, deps := fun n => n == k, errors := [] }

example : (memoStep true sample [] 3 initial).result = .ok 4 4 := by decide
example : (memoStep true sample [] 3 initial).evaluated = true := by decide
example : (memoStep true sample [(3, sample 3)] 3 initial).evaluated = false := by decide
example : (memoStep true sample [(3, sample 3)] 3 initial).result = .ok 4 4 := by decide

-- Invariant 1: arguments distinguish cache keys at the same byte offset.
example : (memoStep true (fun p : Nat × Nat => sample (p.1 + p.2))
    [((3, 1), sample 4)] (3, 2) initial).evaluated = true := by decide

-- Invariant 1: disabling memoization never reuses an entry.
example : (memoStep false sample [(3, sample 3)] 3 initial).evaluated = true := by decide

-- Invariant 1: replay preserves both kinds of rejection and the failure offset.
private def failed : Nat → Entry Nat := fun k =>
  { result := .fail, failure := k, deps := fun _ => false, errors := [] }
private def thrown : Nat → Entry Nat := fun k =>
  { result := .throw k 7, failure := k, deps := fun _ => false, errors := [] }

example : (memoStep true failed [(3, failed 3)] 3 initial).result = .fail := by decide
example : (memoStep true thrown [(3, thrown 3)] 3 initial).result = .throw 3 7 := by decide
example : (memoStep true sample [(3, sample 3)] 3 initial).state.failure = 3 := by decide
