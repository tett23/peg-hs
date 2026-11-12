import MemoRecognition

namespace PegHs.MemoTrace
open MemoRecognition

structure Run (κ α : Type) where
  results : List (Result α)
  state : State
  table : List (κ × Entry α)
  evaluations : Nat

def runFrom [DecidableEq κ] (enabled : Bool) (body : κ → Entry α) :
    List κ → List (κ × Entry α) → State → Run κ α
  | [], table, state =>
      { results := [], state := state, table := table, evaluations := 0 }
  | key :: rest, table, state =>
      let step := memoStep enabled body table key state
      let tail := runFrom enabled body rest step.table step.state
      { results := step.result :: tail.results,
        state := tail.state, table := tail.table,
        evaluations := (if step.evaluated then 1 else 0) + tail.evaluations }

def runMemo [DecidableEq κ] (enabled : Bool) (body : κ → Entry α)
    (keys : List κ) (state : State) : Run κ α :=
  runFrom enabled body keys [] state

def replayAll (body : κ → Entry α) (keys : List κ) (state : State) : State :=
  keys.foldl (fun s k => replay s (body k)) state

theorem runFrom_invariant [DecidableEq κ] (enabled : Bool)
    (body : κ → Entry α) (keys : List κ) (table : List (κ × Entry α))
    (state : State) (inv : CacheInvariant body table) :
    CacheInvariant body (runFrom enabled body keys table state).table := by
  induction keys generalizing table state with
  | nil => simpa [runFrom] using inv
  | cons key rest ih =>
      simp only [runFrom]
      exact ih (memoStep enabled body table key state).table
        (memoStep enabled body table key state).state
        (step_preserves_invariant enabled body table key state inv)

theorem runFrom_sound [DecidableEq κ] (enabled : Bool)
    (body : κ → Entry α) (keys : List κ) (table : List (κ × Entry α))
    (state : State) (inv : CacheInvariant body table) :
    (runFrom enabled body keys table state).results = keys.map (fun k => (body k).result) ∧
    (runFrom enabled body keys table state).state = replayAll body keys state := by
  induction keys generalizing table state with
  | nil => simp [runFrom, replayAll]
  | cons key rest ih =>
      let step := memoStep enabled body table key state
      have same := hit_miss_same_recognition enabled body table key state inv
      have nextInv := step_preserves_invariant enabled body table key state inv
      have tail := ih step.table step.state nextInv
      constructor
      · simp only [runFrom, List.map_cons]
        rw [same.1, tail.1]
      · simp only [runFrom, replayAll, List.foldl_cons]
        rw [tail.2, same.2]
        rfl

theorem runMemo_invariant [DecidableEq κ] (enabled : Bool)
    (body : κ → Entry α) (keys : List κ) (state : State) :
    CacheInvariant body (runMemo enabled body keys state).table := by
  exact runFrom_invariant enabled body keys [] state (empty_invariant body)

-- The public no-premise result: all entries in this trace came from the
-- fixed body oracle, starting with the actual empty-table constructor.
theorem runMemo_same_as_unmemo [DecidableEq κ] (enabled : Bool)
    (body : κ → Entry α) (keys : List κ) (state : State) :
    (runMemo enabled body keys state).results = (runMemo false body keys state).results ∧
    (runMemo enabled body keys state).state = (runMemo false body keys state).state := by
  have a := runFrom_sound enabled body keys [] state (empty_invariant body)
  have b := runFrom_sound false body keys [] state (empty_invariant body)
  exact ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩

#print axioms runMemo_invariant
#print axioms runMemo_same_as_unmemo

end PegHs.MemoTrace
