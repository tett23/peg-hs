import Lean

namespace PegHs.MemoRecognition

-- The strict-mode projection of Internal.hs's Entry. `Result` keeps success,
-- ordinary failure and labelled failure distinct. `failure` is the farthest
-- failure offset; dependencies are the effects replayed on a hit.
-- `errors = []` follows from cfgRecover = False and saveErrors = Nothing.
inductive Result (α : Type) where
  | ok (endPos : Nat) (value : α)
  | fail
  | throw (pos : Nat) (label : Nat)
  deriving DecidableEq

structure Entry (α : Type) where
  result : Result α
  failure : Nat
  deps : Nat → Bool
  errors : List Nat

structure State where
  failure : Nat
  deps : Nat → Bool

def initial : State := { failure := 0, deps := fun _ => false }

def replay (s : State) (e : Entry α) : State :=
  { failure := max s.failure e.failure,
    deps := fun n => s.deps n || e.deps n }

def lookupEntry [DecidableEq κ] : List (κ × Entry α) → κ → Option (Entry α)
  | [], _ => none
  | (k, e) :: rest, wanted => if k = wanted then some e else lookupEntry rest wanted

structure Step (κ α : Type) where
  result : Result α
  state : State
  table : List (κ × Entry α)
  evaluated : Bool

-- The two source functions have the same branch structure after their keys
-- have been projected to κ = offset or κ = (offset, argument).
def memoStep [DecidableEq κ] (enabled : Bool) (evalBody : κ → Entry α)
    (table : List (κ × Entry α)) (key : κ) (s : State) : Step κ α :=
  if enabled then
    match lookupEntry table key with
    | some e => { result := e.result, state := replay s e,
                  table := table, evaluated := false }
    | none =>
      let e := evalBody key
      { result := e.result, state := replay s e,
        table := (key, e) :: table, evaluated := true }
  else
    let e := evalBody key
    { result := e.result, state := replay s e,
      table := table, evaluated := true }

def CacheInvariant [DecidableEq κ] (evalBody : κ → Entry α)
    (table : List (κ × Entry α)) : Prop :=
  ∀ key e, lookupEntry table key = some e → e = evalBody key

theorem empty_invariant [DecidableEq κ] (evalBody : κ → Entry α) :
    CacheInvariant evalBody [] := by
  intro key e h
  simp [lookupEntry] at h

theorem insert_invariant [DecidableEq κ] (evalBody : κ → Entry α)
    (table : List (κ × Entry α)) (key : κ)
    (h : CacheInvariant evalBody table) :
    CacheInvariant evalBody ((key, evalBody key) :: table) := by
  intro wanted e found
  simp only [lookupEntry] at found
  split at found
  · rename_i eq
    cases found
    subst wanted
    rfl
  · exact h wanted e found

theorem step_preserves_invariant [DecidableEq κ] (enabled : Bool)
    (evalBody : κ → Entry α) (table : List (κ × Entry α)) (key : κ)
    (s : State) (h : CacheInvariant evalBody table) :
    CacheInvariant evalBody (memoStep enabled evalBody table key s).table := by
  cases enabled with
  | false => simpa [memoStep] using h
  | true =>
    simp only [memoStep, ↓reduceIte]
    cases lookupEntry table key with
    | none => exact insert_invariant evalBody table key h
    | some e => exact h

-- Local recognition equivalence. A cached entry must still equal the result
-- of evaluating that rule at the same offset and with the same arguments.
-- This stability assumption is the boundary for left-recursive seed changes.
theorem hit_miss_same_recognition [DecidableEq κ] (enabled : Bool)
    (evalBody : κ → Entry α) (table : List (κ × Entry α)) (key : κ)
    (s : State) (h : CacheInvariant evalBody table) :
    (memoStep enabled evalBody table key s).result = (evalBody key).result ∧
    (memoStep enabled evalBody table key s).state = replay s (evalBody key) := by
  cases enabled with
  | false => simp [memoStep]
  | true =>
    simp only [memoStep, ↓reduceIte]
    cases found : lookupEntry table key with
    | none => simp [found]
    | some e =>
      have eq := h key e found
      subst e
      simp [found]

theorem strict_errors_empty [DecidableEq κ] (evalBody : κ → Entry α)
    (table : List (κ × Entry α)) (key : κ)
    (h : CacheInvariant evalBody table)
    (strict : ∀ k, (evalBody k).errors = [])
    (e : Entry α) (found : lookupEntry table key = some e) : e.errors = [] := by
  rw [h key e found]
  exact strict key

#print axioms hit_miss_same_recognition
#print axioms step_preserves_invariant
#print axioms strict_errors_empty

end PegHs.MemoRecognition
