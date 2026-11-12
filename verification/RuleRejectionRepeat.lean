import RuleRejectionRefs

namespace PegHs.RuleRejectionRepeat

open RuleRejectionRefs

-- A candidate records the location of its containing Item. A nested group
-- supplies a new Item location in Haskell; this model projects locations to
-- one caller-supplied value because only nonemptiness is proved here.
def repeatCandidates (nullable : Expr → Bool) (location : Nat) : Expr → List (Nat × Bool)
  | .star x => (location, nullable x) :: repeatCandidates nullable location x
  | .plus x => (location, nullable x) :: repeatCandidates nullable location x
  | .opt x => repeatCandidates nullable location x
  | .and x => repeatCandidates nullable location x
  | .not x => repeatCandidates nullable location x
  | .capture x => repeatCandidates nullable location x
  | .label _ x _ => repeatCandidates nullable location x
  | .discard x => repeatCandidates nullable location x
  | .group alts => alts.flatMap (fun items => items.flatMap (repeatCandidates nullable location))
  | .lit _ _ => []
  | .charClass _ => []
  | .any => []
  | .ref _ _ _ => []
  | .predicate _ _ => []
  | .template _ _ _ _ => []
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

inductive HasNullableRepeat (nullable : Expr → Bool) : Expr → Prop where
  | starHere {x} : nullable x = true → HasNullableRepeat nullable (.star x)
  | plusHere {x} : nullable x = true → HasNullableRepeat nullable (.plus x)
  | starChild {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.star x)
  | plusChild {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.plus x)
  | opt {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.opt x)
  | and {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.and x)
  | not {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.not x)
  | capture {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.capture x)
  | label {location x name} : HasNullableRepeat nullable x →
      HasNullableRepeat nullable (.label location x name)
  | discard {x} : HasNullableRepeat nullable x → HasNullableRepeat nullable (.discard x)
  | group {alts items x} : items ∈ alts → x ∈ items → HasNullableRepeat nullable x →
      HasNullableRepeat nullable (.group alts)

theorem invariant2_nullableRepeat_candidate (nullable : Expr → Bool) (location : Nat)
    (expression : Expr) (found : HasNullableRepeat nullable expression) :
    (location, true) ∈ repeatCandidates nullable location expression := by
  induction found with
  | starHere h => simp [repeatCandidates, h]
  | plusHere h => simp [repeatCandidates, h]
  | starChild h ih => simp [repeatCandidates, ih]
  | plusChild h ih => simp [repeatCandidates, ih]
  | opt h ih => simpa [repeatCandidates] using ih
  | and h ih => simpa [repeatCandidates] using ih
  | not h ih => simpa [repeatCandidates] using ih
  | capture h ih => simpa [repeatCandidates] using ih
  | label h ih => simpa [repeatCandidates] using ih
  | discard h ih => simpa [repeatCandidates] using ih
  | group hitems hx h ih =>
    simp only [repeatCandidates, List.mem_flatMap]
    exact ⟨_, hitems, _, hx, ih⟩

theorem invariant2_nullableRepeatVisible {G : Type}
    (parsed g0 g : G)
    (resolve expand : G → Except RuleRejection.Diagnostics G)
    (notes : G → RuleRejection.Diagnostics → RuleRejection.Diagnostics)
    (strip : Option (G → G))
    (warningFor : G → G → RuleRejection.Diagnostics)
    (generate : G → Except RuleRejection.Diagnostics String)
    (undefined before after : List RuleRejection.Diagnostic)
    (nullable : Expr → Bool) (location : Nat) (expression : Expr)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (found : HasNullableRepeat nullable expression) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => RuleRejection.checkRoot undefined
            (RuleRejection.repetitionFromNullable
              (repeatCandidates nullable location expression)) before after)
          notes strip warningFor generate) = .error ds := by
  apply RuleRejection.invariant2_nullableRepeatVisible parsed g0 g resolve expand
    notes strip warningFor generate undefined before after
    (repeatCandidates nullable location expression) location hr he hn
  exact invariant2_nullableRepeat_candidate nullable location expression found

theorem invariant2_predicateDirectNoRepetition
    (nullable : Expr → Bool) (location : Nat) (polarity : Bool) (code : String) :
    repeatCandidates nullable location (.predicate polarity code) = [] := by
  simp [repeatCandidates]

theorem invariant2_repeatedPredicateRejected
    (nullable : Expr → Bool) (location : Nat) (polarity : Bool) (code : String)
    (known : nullable (.predicate polarity code) = true) :
    (location, true) ∈ repeatCandidates nullable location
      (.star (.predicate polarity code)) := by
  simp [repeatCandidates, known]

-- Invariant 2: a repeated nullable predicate rejects; a bare predicate does not.
example : (3, true) ∈ repeatCandidates (fun _ => true) 3
    (.star (.predicate true "p")) := by simp [repeatCandidates]
example : (3, true) ∈ repeatCandidates (fun _ => true) 3
    (.group [[.opt (.plus (.predicate false "p"))]]) := by
  simp [repeatCandidates]
example : repeatCandidates (fun _ => true) 3 (.predicate true "p") = [] := by
  simp [repeatCandidates]

end PegHs.RuleRejectionRepeat

#print axioms PegHs.RuleRejectionRepeat.invariant2_nullableRepeat_candidate
#print axioms PegHs.RuleRejectionRepeat.invariant2_nullableRepeatVisible
#print axioms PegHs.RuleRejectionRepeat.invariant2_predicateDirectNoRepetition
#print axioms PegHs.RuleRejectionRepeat.invariant2_repeatedPredicateRejected
