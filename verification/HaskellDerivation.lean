import Std

namespace PegHs.CFG

inductive Symbol where
  | terminal (kind : Nat)
  | nonterminal (kind : Nat)
  deriving DecidableEq, Repr

abbrev Production := Nat × List Symbol
abbrev Grammar := Array Production

-- An ordinary context-free derivation, independent of the trace checker.
inductive Derives (g : Grammar) : List Symbol → List Symbol → Prop where
  | refl (xs) : Derives g xs xs
  | production {id : Nat} {lhs rhs pre post result} (rule : g[id]? = some (lhs, rhs))
      (next : Derives g (pre ++ rhs ++ post) result) :
      Derives g (pre ++ [.nonterminal lhs] ++ post) result

inductive Action where
  | shift | reduce (id : Nat)
  deriving Repr

structure State where
  stack : List Symbol  -- newest first
  unread : List Nat

def State.word (s : State) := s.stack.reverse ++ s.unread.map Symbol.terminal

def pop : List Symbol → List Symbol → Option (List Symbol)
  | [], stack => some stack
  | _ :: _, [] => none
  | a :: as, b :: bs => if a = b then pop as bs else none

private theorem pop_prefix {rhs stack tail} (ok : pop rhs stack = some tail) :
    stack = rhs ++ tail := by
  induction rhs generalizing stack with
  | nil => simpa [pop] using ok
  | cons a as ih =>
    cases stack with
    | nil => simp [pop] at ok
    | cons b bs =>
      by_cases e : a = b
      · subst b; simp only [pop, ite_true] at ok
        simp [ih ok]
      · simp [pop, e] at ok

def step (g : Grammar) (s : State) : Action → Option State
  | .shift => match s.unread with
    | [] => none
    | t :: ts => some ⟨.terminal t :: s.stack, ts⟩
  | .reduce id => do
    let (lhs, rhs) ← g[id]?
    let tail ← pop rhs.reverse s.stack
    return ⟨.nonterminal lhs :: tail, s.unread⟩

private theorem step_sound (g : Grammar) (s : State) (action : Action) (t : State)
    (ok : step g s action = some t) {result} (old : Derives g s.word result) :
    Derives g t.word result := by
  cases s with
  | mk stack unread =>
    cases action with
    | shift =>
      cases unread with
      | nil => simp [step] at ok
      | cons sym rest =>
        simp [step] at ok
        subst t
        simpa [State.word, List.append_assoc] using old
    | reduce id =>
      cases entry : g[id]? with
      | none => simp [step, entry] at ok
      | some row =>
        obtain ⟨lhs, rhs⟩ := row
        cases popped : pop rhs.reverse stack with
        | none => simp [step, entry, popped] at ok
        | some tail =>
          simp [step, entry, popped] at ok
          subst t
          have orig := pop_prefix popped
          subst stack
          simp only [State.word, List.reverse_cons] at ⊢
          apply Derives.production (pre := tail.reverse) (post := unread.map Symbol.terminal) entry
          simpa [State.word] using old

def replay (g : Grammar) (s : State) : List Action → Option State
  | [] => some s
  | a :: as => (step g s a).bind (fun next => replay g next as)

theorem replay_sound {g s actions t} (ok : replay g s actions = some t) :
    Derives g t.word s.word := by
  suffices ∀ result, Derives g s.word result → Derives g t.word result by
    exact this _ (.refl _)
  induction actions generalizing s with
  | nil =>
    simp [replay] at ok
    subst t
    exact fun _ h => h
  | cons a as ih =>
    cases h : step g s a with
    | none => simp [replay, h] at ok
    | some next =>
      simp [replay, h] at ok
      exact fun result d => ih ok result (step_sound g s a next h d)

def accepts (g : Grammar) (start : Nat) (tokens : List Nat) (actions : List Action) :=
  match replay g ⟨[], tokens⟩ actions with
  | some ⟨[.nonterminal id], []⟩ => id == start
  | _ => false

theorem invariant3_certificate_sound (g : Grammar) (start : Nat) (tokens : List Nat)
    (actions : List Action) (ok : accepts g start tokens actions = true) :
    Derives g [.nonterminal start] (tokens.map Symbol.terminal) := by
  unfold accepts at ok
  split at ok
  next id h =>
    have eq : id = start := by simpa using ok
    subst id
    simpa [State.word] using replay_sound h
  next => contradiction

example : accepts #[(0, [.terminal 1])] 0 [1] [.shift, .reduce 0] = true := by decide
example : accepts #[(0, [.terminal 1])] 0 [2] [.shift, .reduce 0] = false := by decide
example : accepts #[(0, [])] 0 [1] [.reduce 0] = false := by decide

end PegHs.CFG
