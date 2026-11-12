import MemoTrace

namespace PegHs.MemoTables
open MemoRecognition

-- Extensional views of IntMap Entry and IntMap (Map argument Entry).
-- The Haskell source checker pins the concrete IM/M operations. We assume
-- the standard lookup/insert/left-biased-union laws of those containers.
abbrev MemoTable (α : Type) := Nat → Option (Entry α)
abbrev ArgTable (κ α : Type) := Nat → κ → Option (Entry α)

def emptyMemo : MemoTable α := fun _ => none
def lookupMemo (table : MemoTable α) (offset : Nat) : Option (Entry α) := table offset
def insertMemo (table : MemoTable α) (offset : Nat) (entry : Entry α) : MemoTable α :=
  fun query => if query = offset then some entry else table query

def emptyArg : ArgTable κ α := fun _ _ => none
def lookupArg (table : ArgTable κ α) (offset : Nat) (arg : κ) : Option (Entry α) :=
  table offset arg
def insertArg [DecidableEq κ] (table : ArgTable κ α)
    (offset : Nat) (arg : κ) (entry : Entry α) : ArgTable κ α :=
  fun queryOffset queryArg =>
    if queryOffset = offset then
      if queryArg = arg then some entry else table queryOffset queryArg
    else table queryOffset queryArg

theorem insertMemo_hit (table : MemoTable α) (offset : Nat) (entry : Entry α) :
    lookupMemo (insertMemo table offset entry) offset = some entry := by
  simp [lookupMemo, insertMemo]

theorem insertMemo_other (table : MemoTable α) (offset query : Nat)
    (entry : Entry α) (different : query ≠ offset) :
    lookupMemo (insertMemo table offset entry) query = lookupMemo table query := by
  simp [lookupMemo, insertMemo, different]

theorem insertArg_hit [DecidableEq κ] (table : ArgTable κ α)
    (offset : Nat) (arg : κ) (entry : Entry α) :
    lookupArg (insertArg table offset arg entry) offset arg = some entry := by
  simp [lookupArg, insertArg]

theorem insertArg_other [DecidableEq κ] (table : ArgTable κ α)
    (offset queryOffset : Nat) (arg queryArg : κ) (entry : Entry α)
    (different : queryOffset ≠ offset ∨ queryArg ≠ arg) :
    lookupArg (insertArg table offset arg entry) queryOffset queryArg =
      lookupArg table queryOffset queryArg := by
  rcases different with h | h
  · simp [lookupArg, insertArg, h]
  · by_cases same : queryOffset = offset
    · simp [lookupArg, insertArg, same, h]
    · simp [lookupArg, insertArg, same]

-- These folds connect the extensional Haskell table operations to the
-- association-list table used by MemoTrace. Latest insertion wins.
def fromListMemo : List (Nat × Entry α) → MemoTable α
  | [] => emptyMemo
  | (key, entry) :: rest => insertMemo (fromListMemo rest) key entry

def fromListArg [DecidableEq κ] : List ((Nat × κ) × Entry α) → ArgTable κ α
  | [] => emptyArg
  | ((offset, arg), entry) :: rest =>
      insertArg (fromListArg rest) offset arg entry

theorem fromListMemo_lookup (table : List (Nat × Entry α)) (offset : Nat) :
    lookupMemo (fromListMemo table) offset = lookupEntry table offset := by
  induction table with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨key, entry⟩
      simp only [fromListMemo, lookupMemo, insertMemo, lookupEntry]
      by_cases same : key = offset
      · subst offset
        simp
      · simp [same, Ne.symm same, ← ih, lookupMemo]

theorem fromListArg_lookup [DecidableEq κ]
    (table : List ((Nat × κ) × Entry α)) (offset : Nat) (arg : κ) :
    lookupArg (fromListArg table) offset arg = lookupEntry table (offset, arg) := by
  induction table with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨⟨keyOffset, keyArg⟩, entry⟩
      simp only [fromListArg, lookupArg, insertArg, lookupEntry]
      by_cases offsetSame : offset = keyOffset
      · by_cases argSame : arg = keyArg
        · subst offset; subst arg
          simp
        · simp [offsetSame, argSame, Ne.symm argSame, Prod.mk.injEq]
          simpa [lookupArg, offsetSame] using ih
      · simp [offsetSame, Ne.symm offsetSame, ← ih, lookupArg, Prod.mk.injEq]

theorem memo_run_table_stable (enabled : Bool) (body : Nat → Entry α)
    (keys : List Nat) (state : State) (offset : Nat) (entry : Entry α)
    (found : lookupMemo (fromListMemo (MemoTrace.runMemo enabled body keys state).table)
      offset = some entry) : entry = body offset := by
  have inv := MemoTrace.runMemo_invariant enabled body keys state
  exact inv offset entry ((fromListMemo_lookup _ offset).symm.trans found)

theorem memo_arg_run_table_stable [DecidableEq κ] (enabled : Bool)
    (body : Nat × κ → Entry α) (keys : List (Nat × κ)) (state : State)
    (offset : Nat) (arg : κ) (entry : Entry α)
    (found : lookupArg (fromListArg (MemoTrace.runMemo enabled body keys state).table)
      offset arg = some entry) : entry = body (offset, arg) := by
  have inv := MemoTrace.runMemo_invariant enabled body keys state
  exact inv (offset, arg) entry ((fromListArg_lookup _ offset arg).symm.trans found)

#print axioms fromListMemo_lookup
#print axioms fromListArg_lookup
#print axioms memo_run_table_stable
#print axioms memo_arg_run_table_stable

end PegHs.MemoTables
