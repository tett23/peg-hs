import Lean

-- The vocabulary that ExtractRuntimeCore.hs translates
-- packages/peg-runtime/src/Peg/Runtime/Internal.hs into. The extractor keeps
-- the names of the Haskell source (readSTRef (ctxFail c), IS.union,
-- cfgRecover (ctxConfig c), ...) so that each translated line can be read
-- against the source line it comes from. The data declarations that this
-- file restates are compared with the source by the extractor.
--
-- Premises of the model (recorded in verification/README.md):
-- R1 ST. `ST s` is a state transformer over a world, with `none` standing for
--    a computation that does not return. The STRefs that newCtx allocates
--    are distinct; each is a fixed field of the world. A memo table of the
--    generated store is a ref into the store component; the theorems that
--    read a table back after writing it assume the lens laws of that ref.
-- R2 Containers. Data.Set, Data.IntSet, Data.IntMap and Data.Map are their
--    extensional views (membership and lookup functions) with the usual
--    insert, delete, union, insertWith and adjust laws.
-- R3 Text. A Text value is the UTF-8 encoding of a string of scalar values,
--    modelled as a Lean String with its slice offset normalised to 0.
--    T.pack is the identity on scalar strings, TU.lengthWord8 is the byte
--    length, TA.unsafeIndex reads a byte that is in bounds, and TU.iter
--    decodes the scalar that starts at a byte offset (CheckUtf8Runtime.hs
--    probes the last two on the actual library).
-- R4 Positions. posAt keeps the byte offset; LineIndex.lean proves the
--    line and column conversion separately.
-- R5 Undo actions stored in ctxLogs are erased. Only endIteration runs them,
--    and only memoLR calls endIteration; memoLR is not translated.
namespace PegHs.RuntimeCore

abbrev Text := String

inductive Expected where
  | ExpectedName (t : Text)
  | ExpectedLiteral (t : Text)
  | ExpectedClass (t : Text)
  | ExpectedAny
  | ExpectedEnd
  deriving DecidableEq, Repr
export Expected (ExpectedName ExpectedLiteral ExpectedClass ExpectedAny ExpectedEnd)

-- Data.Set Expected, by membership.
abbrev ExpSet := Expected → Bool
namespace S
def empty : ExpSet := fun _ => false
def singleton (e : Expected) : ExpSet := fun x => decide (x = e)
def union (a b : ExpSet) : ExpSet := fun x => a x || b x
end S

-- Data.IntSet, by membership.
abbrev IntSet := Nat → Bool
namespace IS
def empty : IntSet := fun _ => false
def singleton (k : Nat) : IntSet := fun x => decide (x = k)
def union (a b : IntSet) : IntSet := fun x => a x || b x
def member (k : Nat) (a : IntSet) : Bool := a k
def delete (k : Nat) (a : IntSet) : IntSet := fun x => if x = k then false else a x
noncomputable def null (a : IntSet) : Bool :=
  open Classical in decide (∀ x, a x = false)
end IS

-- Data.IntMap and Data.Map, by lookup.
abbrev IntMap (v : Type) := Nat → Option v
namespace IM
def empty : IntMap v := fun _ => none
def lookup (i : Nat) (m : IntMap v) : Option v := m i
def insert (i : Nat) (x : v) (m : IntMap v) : IntMap v :=
  fun q => if q = i then some x else m q
def delete (i : Nat) (m : IntMap v) : IntMap v :=
  fun q => if q = i then none else m q
-- insertWith f i new m stores f new old when i is present.
def insertWith (f : v → v → v) (i : Nat) (x : v) (m : IntMap v) : IntMap v :=
  fun q => if q = i then some (match m i with | some old => f x old | none => x) else m q
def adjust (f : v → v) (i : Nat) (m : IntMap v) : IntMap v :=
  fun q => if q = i then (m i).map f else m q
end IM

abbrev Map (k v : Type) := k → Option v
namespace M
def empty : Map k v := fun _ => none
def lookup (key : k) (m : Map k v) : Option v := m key
def singleton [DecidableEq k] (key : k) (x : v) : Map k v :=
  fun q => if q = key then some x else none
-- Left-biased, as Data.Map.union.
def union (a b : Map k v) : Map k v := fun q => (a q).or (b q)
def delete [DecidableEq k] (key : k) (m : Map k v) : Map k v :=
  fun q => if q = key then none else m q
def insertWith [DecidableEq k] (f : v → v → v) (key : k) (x : v) (m : Map k v) : Map k v :=
  fun q => if q = key then some (match m key with | some old => f x old | none => x) else m q
end M

-- R3: Text internals used by the terminals.
namespace T
def pack (s : String) : Text := s
end T
namespace TU
def lengthWord8 (t : Text) : Nat := t.utf8ByteSize
structure Iter where
  ch : Char
  d : Nat
-- The scalar that starts at byte i. Runtime callers only ask at a scalar
-- boundary below the length; elsewhere the value is irrelevant.
def iter (t : Text) (i : Nat) : Iter :=
  match t.toUTF8.utf8DecodeChar? i with
  | some ch => ⟨ch, ch.utf8Size⟩
  | none => ⟨default, 1⟩
end TU
namespace TA
def unsafeIndex (arr : ByteArray) (k : Nat) : UInt8 := arr.get! k
end TA

inductive Failure where
  | NoFailure
  | Failure (i : Nat) (xs : ExpSet)
export Failure (NoFailure)

inductive Res (α : Type) where
  | Ok (j : Nat) (x : α)
  | Fail
  | Throw (i : Nat) (l : Text) (m : Option Text)
export Res (Ok Fail Throw)

abbrev Pos := Nat

structure SyntaxError where
  syntaxErrorLabel : Option Text
  syntaxErrorRange : Nat × Nat
  syntaxErrorPos : Pos
  syntaxErrorExpected : ExpSet
  syntaxErrorMessage : Option Text

inductive ErrLog where
  | ErrLog (n : Nat) (xs : List SyntaxError)

inductive ErrSlice where
  | ErrSlice (n : Nat) (xs : List SyntaxError)

structure ParseError where
  parseErrorPos : Pos
  parseErrorExpected : ExpSet
  parseErrorLabel : Option Text
  parseErrorMessage : Option Text

structure Config where
  cfgMemo : Bool
  cfgDiscard : Bool
  cfgDiscardAll : Bool
  cfgCount : Bool
  cfgTabstop : Nat
  cfgRecover : Bool
export Config (cfgMemo cfgDiscard cfgDiscardAll cfgCount cfgTabstop cfgRecover)

structure Stats where
  statsEvaluations : Map (Text × Nat) Int
  statsMemoEntries : Int
  statsEntriesByRule : Map Text Int
export Stats (statsEvaluations statsMemoEntries statsEntriesByRule)

def emptyStats : Stats := ⟨M.empty, 0, M.empty⟩

-- R5: the undo action of a log entry is erased to ().
structure World (σ : Type) where
  fail : Failure
  errors : ErrLog
  deps : IntSet
  depth : Nat
  logs : List (List (IntSet × Unit))
  stats : Stats
  store : σ

abbrev ST (σ : Type) := StateT (World σ) Option

structure Ref (σ τ : Type) where
  get : World σ → τ
  set : τ → World σ → World σ

def readSTRef (r : Ref σ τ) : ST σ τ := fun w => some (r.get w, w)
def writeSTRef (r : Ref σ τ) (x : τ) : ST σ Unit := fun w => some ((), r.set x w)
def modifySTRef' (r : Ref σ τ) (f : τ → τ) : ST σ Unit :=
  fun w => some ((), r.set (f (r.get w)) w)

-- A ref into the generated store of memo tables.
def storeRef (get : σ → τ) (set : τ → σ → σ) : Ref σ τ :=
  ⟨fun w => get w.store, fun x w => { w with store := set x w.store }⟩

def failRef : Ref σ Failure := ⟨World.fail, fun x w => { w with fail := x }⟩
def errorsRef : Ref σ ErrLog := ⟨World.errors, fun x w => { w with errors := x }⟩
def depsRef : Ref σ IntSet := ⟨World.deps, fun x w => { w with deps := x }⟩
def depthRef : Ref σ Nat := ⟨World.depth, fun x w => { w with depth := x }⟩
def logsRef : Ref σ (List (List (IntSet × Unit))) := ⟨World.logs, fun x w => { w with logs := x }⟩
def statsRef : Ref σ Stats := ⟨World.stats, fun x w => { w with stats := x }⟩

-- R1: newCtx's newSTRef calls allocate these fixed fields, in this order.
def newFailRef (x : Failure) : ST σ (Ref σ Failure) := do writeSTRef failRef x; pure failRef
def newErrorsRef (x : ErrLog) : ST σ (Ref σ ErrLog) := do writeSTRef errorsRef x; pure errorsRef
def newLogsRef (x : List (List (IntSet × Unit))) : ST σ (Ref σ (List (List (IntSet × Unit)))) := do
  writeSTRef logsRef x; pure logsRef
def newDepsRef (x : IntSet) : ST σ (Ref σ IntSet) := do writeSTRef depsRef x; pure depsRef
def newDepthRef (x : Nat) : ST σ (Ref σ Nat) := do writeSTRef depthRef x; pure depthRef
def newStatsRef (x : Stats) : ST σ (Ref σ Stats) := do writeSTRef statsRef x; pure statsRef

structure Ctx (ρ : Type) where
  ctxInput : Text
  ctxLen : Nat
  ctxStore : ρ
  ctxConfig : Config
export Ctx (ctxInput ctxLen ctxStore ctxConfig)

def ctxFail (_ : Ctx ρ) : Ref σ Failure := failRef
def ctxErrors (_ : Ctx ρ) : Ref σ ErrLog := errorsRef
def ctxDeps (_ : Ctx ρ) : Ref σ IntSet := depsRef
def ctxDepth (_ : Ctx ρ) : Ref σ Nat := depthRef
def ctxLogs (_ : Ctx ρ) : Ref σ (List (List (IntSet × Unit))) := logsRef
def ctxStats (_ : Ctx ρ) : Ref σ Stats := statsRef

inductive Entry (α : Type) where
  | Entry (r : Res α) (f : Failure) (errs : ErrSlice) (d : IntSet)

abbrev Table (σ α : Type) := Ref σ (IntMap (Entry α))
abbrev ArgTable (σ κ α : Type) := Ref σ (IntMap (Map κ (Entry α)))

-- R4
def posAt (_ : Ctx ρ) (i : Nat) : Pos := i

abbrev P (ρ σ α : Type) := Ctx ρ → Nat → ST σ (Res α)
def unP (p : P ρ σ α) : Ctx ρ → Nat → ST σ (Res α) := p

def when (b : Bool) (m : ST σ Unit) : ST σ Unit := if b then m else pure ()
def maybe (d : β) (f : α → β) : Option α → β
  | none => d
  | some x => f x

-- runST: the heap before newCtx is an explicit argument.
def runST (m : ST σ β) (heap : World σ) : Option β := (m.run heap).map Prod.fst

end PegHs.RuntimeCore
