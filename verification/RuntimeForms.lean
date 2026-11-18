import RuntimeCoreProof

/-!
The forms of the generated code that the extracted bodies leave out
(premise R7 of verification/README.md, the third difference).

ExtractSelfHostedFile.hs reads each rule of the generated SelfHosted.hs and
emits the body that `SelfHostedRuntime.exec` and `SelfHostedMemo.execM` run.
It drops `getOffset`, `spanFrom`, `withCol` and `capture`, reads `optional p`
as an alternative with the empty body, reads the one-alternative `choice`
around a rule body as the body, and reads a `choice` of three or more
alternatives as nested two-way choices. This module shows, for the
translated runtime in strict mode, that each of these readings returns the
same result from every world:

- `getOffset_bind`, `spanFrom_bind`: a bind of `getOffset` or `spanFrom`
  continues at the same offset in the same world with the value that the
  generated code uses only to build its own value.
- `withCol_const`: `withCol` of a function that ignores the column is the
  parser it returns.
- `capture_same`: `capture p` returns the shape, the offset and the world
  that `p` returns; only the value differs.
- `choice_one`: `choice [p]` is `p`.
- `choice_cons`: `choice (p :: q :: r :: rest)` is
  `choice [p, choice (q :: r :: rest)]`.
- `optional_choice`: `optional p` is `choice [Just <$> p, pure Nothing]`.

`getOffset`, `spanFrom`, `withCol` and `capture` are not in the translation;
they are restated here from Peg.Runtime.Internal and check-runtime-core.sh
compares the source lines. `Span` is restated with its two positions; the
positions themselves are premise R4.
-/

set_option linter.unusedSimpArgs false
namespace PegHs.RuntimeCore

attribute [local simp] st_bind st_pure st_map

section Forms
variable {ρ σ α β : Type}

/-- `getOffset = P $ \_ i -> pure (Ok i i)`. -/
def getOffset : P ρ σ Nat := fun _ i => pure (Ok i i)

structure Span where
  spanStart : Pos
  spanEnd : Pos

/-- `spanFrom start = P $ \c i -> pure (Ok i (Span (posAt c start) (posAt c i)))`. -/
def spanFrom (start : Nat) : P ρ σ Span := fun c i => pure (Ok i (Span.mk (posAt c start) (posAt c i)))

/-- `withCol f = P $ \c i -> unP (f (colAt c i)) c i`. The column is a
parameter: the generated code passes functions that ignore it. -/
def withCol (colAt : Ctx ρ → Nat → Nat) (f : Nat → P ρ σ α) : P ρ σ α := fun c i => unP (f (colAt c i)) c i

/-- `capture p` with the slice of the input as a parameter. -/
def capture (slice : Text → Nat → Nat → Text) (p : P ρ σ α) : P ρ σ Text := fun c i =>
  unP p c i >>= fun
    | Ok j _ => pure (Ok j (slice (ctxInput c) i j))
    | bad => pure (failed bad)

theorem getOffset_bind (k : Nat → P ρ σ β) (c : Ctx ρ) (i : Nat) (w : World σ) :
    bindP getOffset k c i w = k i c i w := by
  simp [bindP, getOffset, unP]

theorem spanFrom_bind (start : Nat) (k : Span → P ρ σ β) (c : Ctx ρ) (i : Nat) (w : World σ) :
    bindP (spanFrom start) k c i w = k (Span.mk (posAt c start) (posAt c i)) c i w := by
  simp [bindP, spanFrom, unP]

theorem withCol_const (colAt : Ctx ρ → Nat → Nat) (p : P ρ σ α) (c : Ctx ρ) (i : Nat) (w : World σ) :
    withCol colAt (fun _ => p) c i w = p c i w := rfl

/-- The shape and the offset of a result, without the value. -/
def Res.erase : Res α → Res Unit
  | Ok j _ => Ok j ()
  | Fail => Fail
  | Throw t l m => Throw t l m

theorem capture_same (slice : Text → Nat → Nat → Text) (p : P ρ σ α) (c : Ctx ρ) (i : Nat) (w : World σ) :
    (capture slice p c i w).map (fun r => (Res.erase r.1, r.2)) =
      (p c i w).map (fun r => (Res.erase r.1, r.2)) := by
  cases h : p c i w with
  | none => simp [capture, unP, h]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    cases r <;> simp [capture, unP, h, Res.erase, failed]

theorem choice_one {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) (p : P ρ σ α) (i : Nat)
    (w : World σ) : choice [p] c i w = p c i w := by
  cases h : p c i w with
  | none => simp [choice, choice.go, saveErrors_strict strict, unP, h]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    cases r <;> simp [choice, choice.go, saveErrors_strict strict, unP, h]

theorem choice_go_strict {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) (ps : List (P ρ σ α))
    (i : Nat) (w : World σ) : choice ps c i w = choice.go c i none ps w := by
  simp [choice, saveErrors_strict strict]

theorem go_single {c : Ctx ρ} (x : P ρ σ α) (i : Nat) (w : World σ) :
    choice.go c i none [x] w = x c i w := by
  cases h : x c i w with
  | none => simp [choice.go, unP, h]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    cases r <;> simp [choice.go, unP, h]

theorem go_cons_fail {c : Ctx ρ} {p : P ρ σ α} (ps : List (P ρ σ α)) {i : Nat} {w w1 : World σ}
    (h : p c i w = some (Fail, w1)) : choice.go c i none (p :: ps) w = choice.go c i none ps w1 := by
  simp [choice.go, unP, h]

theorem choice_cons {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) (p q r : P ρ σ α)
    (rest : List (P ρ σ α)) (i : Nat) (w : World σ) :
    choice (p :: q :: r :: rest) c i w = choice [p, choice (q :: r :: rest)] c i w := by
  rw [choice_go_strict strict, choice_go_strict strict]
  cases h : p c i w with
  | none => simp [choice.go, unP, h]
  | some pr =>
    obtain ⟨r1, w1⟩ := pr
    cases r1 with
    | Ok j x => simp [choice.go, unP, h]
    | Throw t l m => simp [choice.go, unP, h]
    | Fail =>
      rw [go_cons_fail _ h, go_cons_fail _ h, go_single, choice_go_strict strict]

theorem optional_choice {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) (p : P ρ σ α) (i : Nat)
    (w : World σ) : optional p c i w = choice [fmapP some p, pureP none] c i w := by
  cases h : p c i w with
  | none => simp [optional, choice, choice.go, saveErrors_strict strict, unP, fmapP, h]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    cases r <;> simp [optional, choice, choice.go, saveErrors_strict strict, unP, fmapP, pureP, h, failed]

end Forms

#print axioms getOffset_bind
#print axioms spanFrom_bind
#print axioms withCol_const
#print axioms capture_same
#print axioms choice_one
#print axioms choice_cons
#print axioms optional_choice

end PegHs.RuntimeCore
