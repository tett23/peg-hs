import TranslatedRuntimeForms

/-!
The runtime of generated parsers, Peg.Runtime.Internal (imported as `PegRt`),
for TranslateHaskell.hs. A generated module calls the runtime's functions; the
translator does not translate them again but replaces each name of its runtime
table with the definition of the same name here. Each definition is the
function that ExtractRuntimeCore.hs translates from the source
(TranslatedRuntimeCore, and TranslatedRuntimeForms for `capture`, `predicate`,
`withCol`, `getOffset` and `spanFrom`), at the types of TranslateHaskell.hs.

Rule H16 (recorded in verification/README.md): the runtime of a generated
module is the translated runtime. A Haskell `String` argument of the runtime
(a literal, a rule name, a label, a message) is the Lean string of its
characters, `HsText.pack`; the generated literals hold scalar values, so the
conversion keeps them. A character range of `cls` converts both ends the same
way. The runtime's `P` is `PegHs.RuntimeCore.P` with offsets of `Nat`; the
offsets that `getOffset` returns and `spanFrom` takes are Haskell `Int`s
(rule H1), equal to the `Nat` offsets (`spanFrom` reads a nonnegative one).
`P`'s monad binds with `bindP`, and its `(>>)` is base's default for a
`Monad`, `m >>= \_ -> k`.

The memo tables of a generated store are refs (premise R1 of RuntimeCore.lean).
-/

namespace HsPegRt
open PegHs.RuntimeCore
noncomputable section

variable {ρ σ α β : Type}

/-- A Haskell `String` passed to the runtime. -/
def str (s : List HsChar) : String := HsText.pack s

def bind (p : P ρ σ α) (k : α → P ρ σ β) : P ρ σ β := bindP p k
def fmap (f : α → β) (p : P ρ σ α) : P ρ σ β := fmapP f p
def ap (pf : P ρ σ (α → β)) (px : P ρ σ α) : P ρ σ β := apP pf px
def pure (x : α) : P ρ σ α := pureP x

def choice (ps : List (P ρ σ α)) : P ρ σ α := PegHs.RuntimeCore.choice ps
def lit (s orig : List HsChar) : P ρ σ Unit := PegHs.RuntimeCore.lit (str s) (str orig)
def cls (ranges : List (HsChar × HsChar)) (orig : List HsChar) : P ρ σ Unit :=
  PegHs.RuntimeCore.cls (ranges.map fun r => (HsText.toChar r.1, HsText.toChar r.2)) (str orig)
def anyChar : P ρ σ Unit := PegHs.RuntimeCore.anyChar
def many (p : P ρ σ α) : P ρ σ (List α) := PegHs.RuntimeCore.many p
def skipMany (p : P ρ σ α) : P ρ σ Unit := PegHs.RuntimeCore.skipMany p
def optional (p : P ρ σ α) : P ρ σ (Option α) := PegHs.RuntimeCore.optional p
def skipOptional (p : P ρ σ α) : P ρ σ Unit := PegHs.RuntimeCore.skipOptional p
def andP (p : P ρ σ α) : P ρ σ Unit := PegHs.RuntimeCore.andP p
def notP (p : P ρ σ α) : P ρ σ Unit := PegHs.RuntimeCore.notP p
def labeled (l : List HsChar) (recovery : Option (P ρ σ α)) (p : P ρ σ α) : P ρ σ α :=
  PegHs.RuntimeCore.labeled (str l) recovery p
def labeledMessage (l msg : List HsChar) (recovery : Option (P ρ σ α)) (p : P ρ σ α) : P ρ σ α :=
  PegHs.RuntimeCore.labeledMessage (str l) (str msg) recovery p
def memo (sel : ρ → Table σ α) (name : List HsChar) (body : P ρ σ α) : P ρ σ α :=
  PegHs.RuntimeCore.memo sel (str name) body
def memoArg (sel : ρ → ArgTable σ Int α) (name : List HsChar) (k : Int) (body : P ρ σ α) : P ρ σ α :=
  PegHs.RuntimeCore.memoArg sel (str name) k body
def capture (p : P ρ σ α) : P ρ σ String := PegHs.GeneratedRuntimeForms.capture p
def predicate (f : Int → Bool) : P ρ σ Unit := PegHs.GeneratedRuntimeForms.predicate f
def withCol (f : Int → P ρ σ α) : P ρ σ α := PegHs.GeneratedRuntimeForms.withCol f
def getOffset : P ρ σ Int := PegHs.GeneratedRuntimeForms.getOffset
def spanFrom (start : Int) : P ρ σ PegHs.GeneratedRuntimeForms.Span := PegHs.GeneratedRuntimeForms.spanFrom start

/-- A generated store is built of refs; their default is never read. -/
instance {τ : Type} [Inhabited τ] : Inhabited (Ref σ τ) := ⟨⟨fun _ => default, fun _ w => w⟩⟩

/-- A computation that does not return: the value of an exhausted fuel. -/
instance : Inhabited (PegHs.RuntimeCore.ST σ α) := ⟨fun _ => none⟩

/-- The erased position of RuntimeCore.lean (premise R4) is the offset of the
full position. -/
theorem posAtPos_offset (c : Ctx ρ) (i : Nat) :
    (PegHs.GeneratedRuntimeForms.posAtPos c i).posOffset = Int.ofNat (posAt c i) := rfl

end
end HsPegRt
