import SelfHostedTranslated

/-!
The values of the start rules of the generated Peg.Grammar.SelfHosted, on its
translation from GHC's syntax tree (SelfHostedTranslated, by TranslateHaskell.hs
with translate-selfhosted.hints; check-translate-selfhosted.sh).

FileTops.lean models the value that `parseTops` returns: the value of `File`
is the list that `many TopItem` returns, `TopItem` returns the value of
`TopOne`, and `TopOne` returns the value of the first of `Verbatim`,
`Directive` and `Declaration` that succeeds. These theorems show that the
translated rules have that form, for every fuel. With
`invariant1_translated_many_step` of RuntimeCoreProof.lean (the values that
the translated `many` collects), they replace the source pins of
check-file-tops.sh.

Theorems:
- `invariant1_translated_file_value`: `File` runs `Ws`, then `many TopItem`,
  then the labelled end check `^top`, and returns the list of `many`.
- `invariant1_translated_topItem_value`: `TopItem` returns the value of
  `TopOne` after `Ws`.
- `invariant1_translated_topOne_value`: `TopOne` is the ordered choice of
  `Verbatim`, `Directive` and `Declaration`, and returns the value of the
  alternative.

The memo table and the name of each rule are those of the generated code; the
name only counts evaluations (`cfgCount`).
-/

namespace SelfHostedTranslated
open PegHs.RuntimeCore

variable {σ : Type}

theorem st_bind' {α β : Type} (x : PegHs.RuntimeCore.ST σ α) (f : α → PegHs.RuntimeCore.ST σ β) (w : World σ) :
    (x >>= f) w = (x w).bind (fun p => f p.1 p.2) := by
  show (do let (a, s) ← x w; f a s) = _
  cases x w <;> rfl

/-- A bind whose continuation returns the value is the parser itself. -/
theorem bind_pure_value {ρ α : Type} (p : P ρ σ α) : HsPegRt.bind p (fun v => HsPegRt.pure v) = p := by
  funext c i w
  simp only [HsPegRt.bind, HsPegRt.pure, bindP, pureP, unP, st_bind']
  cases h : p c i w with
  | none => rfl
  | some rw =>
    obtain ⟨r, w'⟩ := rw
    cases r <;> rfl

variable [Inhabited σ]

/-- `TopOne`: the first of `Verbatim`, `Directive` and `Declaration` that
succeeds gives the value. -/
theorem invariant1_translated_topOne_value (fuel : Nat) :
    ∃ name, (peg'rule'TopOne fuel : P (Peg'Store σ) σ AssembleTranslated.Top) =
      HsPegRt.memo Peg'Store.peg'memo'TopOne name
        (HsPegRt.choice [peg'rule'Verbatim, peg'rule'Directive, peg'rule'Declaration fuel]) := by
  unfold peg'rule'TopOne
  simp only [bind_pure_value]
  exact ⟨_, by with_reducible rfl⟩

/-- `TopItem`: the value of `TopOne`, after the whitespace that follows it. -/
theorem invariant1_translated_topItem_value (fuel : Nat) :
    ∃ name, (peg'rule'TopItem fuel : P (Peg'Store σ) σ AssembleTranslated.Top) =
      HsPegRt.memo Peg'Store.peg'memo'TopItem name
        (HsPegRt.choice [HsPegRt.bind (peg'rule'TopOne fuel) fun v =>
          HsPegRt.bind peg'rule'Ws fun _ => HsPegRt.pure v]) := by
  unfold peg'rule'TopItem
  exact ⟨_, by with_reducible rfl⟩

/-- `File`: the list that `many TopItem` returns, after the leading
whitespace and before the labelled check of the end of the input. -/
theorem invariant1_translated_file_value (fuel : Nat) :
    ∃ name label msg, (peg'rule'File (fuel + 1) : P (Peg'Store σ) σ (List AssembleTranslated.Top)) =
      HsPegRt.memo Peg'Store.peg'memo'File name
        (HsPegRt.choice [HsPegRt.bind peg'rule'Ws fun _ =>
          HsPegRt.bind (HsPegRt.many (peg'rule'TopItem fuel)) fun v =>
            HsPegRt.bind (HsPegRt.labeledMessage label msg none
              (HsPegRt.choice [HsPegRt.bind (HsPegRt.notP HsPegRt.anyChar) fun _ => HsPegRt.pure ()]))
              fun _ => HsPegRt.pure v]) := by
  simp only [peg'rule'File]
  exact ⟨_, _, _, by with_reducible rfl⟩

end SelfHostedTranslated
