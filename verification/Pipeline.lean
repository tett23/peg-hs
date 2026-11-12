import Std

namespace PegHs.Pipeline

abbrev Diagnostics := List String

structure Generation (Grammar : Type) where
  grammar : Grammar
  warnings : Diagnostics
  -- Haskell leaves `generate opts target` unevaluated until this field is used.
  moduleResult : Unit → Except Diagnostics String

-- Haskell's `either (Left . templateNotes g0) Right`.
def withNotes {Grammar : Type} (notes : Grammar → Diagnostics → Diagnostics)
    (g0 : Grammar) (result : Except Diagnostics Grammar) : Except Diagnostics Grammar :=
  match result with
  | .error ds => .error (notes g0 ds)
  | .ok g => .ok g

-- The arguments represent stage results for the actual values reached by
-- this do/bind chain. Their implementations are outside this theorem.
def pipeline {Grammar : Type}
    (parse : Except Diagnostics Grammar)
    (resolve expand : Grammar → Except Diagnostics Grammar)
    (check : Grammar → Except Diagnostics Unit)
    (notes : Grammar → Diagnostics → Diagnostics)
    (strip : Option (Grammar → Grammar))
    (warningFor : Grammar → Grammar → Diagnostics)
    (generate : Grammar → Except Diagnostics String) :
    Except Diagnostics (Generation Grammar) :=
  match parse with
  | .error ds => .error ds
  | .ok parsed =>
    match resolve parsed with
    | .error ds => .error ds
    | .ok g0 =>
      let checked := match expand g0 with
        | .error ds => .error ds
        | .ok g => match check g with
          | .error ds => .error ds
          | .ok () => .ok g
      match withNotes notes g0 checked with
      | .error ds => .error ds
      | .ok g =>
        let target := match strip with
          | none => g
          | some change => change g
        let warnings := match strip with
          | none => warningFor g0 g
          | some _ => []
        .ok ⟨target, warnings, fun _ => generate target⟩

def visible {Grammar : Type} (result : Except Diagnostics (Generation Grammar)) :
    Except Diagnostics String :=
  match result with
  | .error ds => .error ds
  | .ok generation => generation.moduleResult ()

-- These statements follow the actual reached grammar at each stage.
theorem invariant2_parseFailure {G : Type} (ds : Diagnostics)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String) :
    visible (pipeline (.error ds) resolve expand check notes strip warningFor generate) =
      .error ds := by rfl

theorem invariant2_resolveFailure {G : Type} (parseResult : Except Diagnostics G)
    (parsed : G) (ds : Diagnostics)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (hp : parseResult = .ok parsed) (hr : resolve parsed = .error ds) :
    visible (pipeline parseResult resolve expand check notes strip warningFor generate) =
      .error ds := by
  cases hp
  simp [pipeline, visible, hr]

theorem invariant2_expandFailure {G : Type} (parsed g0 : G) (ds : Diagnostics)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .error ds) :
    visible (pipeline (.ok parsed) resolve expand check notes strip warningFor generate) =
      .error (notes g0 ds) := by
  simp [pipeline, visible, withNotes, hr, he]

theorem invariant2_checkFailure {G : Type} (parsed g0 g : G) (ds : Diagnostics)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hc : check g = .error ds) :
    visible (pipeline (.ok parsed) resolve expand check notes strip warningFor generate) =
      .error (notes g0 ds) := by
  simp [pipeline, visible, withNotes, hr, he, hc]

theorem invariant2_generateFailure {G : Type} (parsed g0 g : G) (ds : Diagnostics)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hc : check g = .ok ())
    (hg : generate (match strip with | none => g | some change => change g) = .error ds) :
    visible (pipeline (.ok parsed) resolve expand check notes strip warningFor generate) =
      .error ds := by
  simp [pipeline, visible, withNotes, hr, he, hc, hg]

theorem invariant2_generateSuccess {G : Type} (parsed g0 g : G) (code : String)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hc : check g = .ok ())
    (hg : generate (match strip with | none => g | some change => change g) = .ok code) :
    visible (pipeline (.ok parsed) resolve expand check notes strip warningFor generate) =
      .ok code := by
  simp [pipeline, visible, withNotes, hr, he, hc, hg]

-- Nonempty stage diagnostics are preserved through the complete composition.
theorem invariant2_visibleFailureNonempty {G : Type}
    (parse : Except Diagnostics G)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (parseNonempty : ∀ ds, parse = .error ds → ds ≠ [])
    (resolveNonempty : ∀ g ds, resolve g = .error ds → ds ≠ [])
    (expandNonempty : ∀ g ds, expand g = .error ds → ds ≠ [])
    (checkNonempty : ∀ g ds, check g = .error ds → ds ≠ [])
    (notesNonempty : ∀ g ds, ds ≠ [] → notes g ds ≠ [])
    (generateNonempty : ∀ g ds, generate g = .error ds → ds ≠ [])
    (ds : Diagnostics)
    (failure : visible (pipeline parse resolve expand check notes strip warningFor generate) =
      .error ds) : ds ≠ [] := by
  cases hp : parse with
  | error pds =>
    have eq : pds = ds := by simpa [pipeline, visible, hp] using failure
    subst ds
    exact parseNonempty pds hp
  | ok parsed =>
    cases hr : resolve parsed with
    | error rds =>
      have eq : ds = rds := by simpa [pipeline, visible, hp, hr] using failure.symm
      subst ds
      exact resolveNonempty parsed rds hr
    | ok g0 =>
      cases he : expand g0 with
      | error eds =>
        have eq : ds = notes g0 eds := by
          simpa [pipeline, visible, withNotes, hp, hr, he] using failure.symm
        subst ds
        exact notesNonempty g0 eds (expandNonempty g0 eds he)
      | ok g =>
        cases hc : check g with
        | error cds =>
          have eq : ds = notes g0 cds := by
            simpa [pipeline, visible, withNotes, hp, hr, he, hc] using failure.symm
          subst ds
          exact notesNonempty g0 cds (checkNonempty g cds hc)
        | ok value =>
          cases value
          let target := match strip with
            | none => g
            | some change => change g
          cases hg : generate target with
          | error gds =>
            have eq : ds = gds := by
              simpa [pipeline, visible, withNotes, hp, hr, he, hc, target, hg] using failure.symm
            subst ds
            exact generateNonempty target gds hg
          | ok code =>
            simp [pipeline, visible, withNotes, hp, hr, he, hc, target, hg] at failure

theorem invariant2_diagnosticOrModule {G : Type}
    (parse : Except Diagnostics G)
    (resolve expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (parseNonempty : ∀ ds, parse = .error ds → ds ≠ [])
    (resolveNonempty : ∀ g ds, resolve g = .error ds → ds ≠ [])
    (expandNonempty : ∀ g ds, expand g = .error ds → ds ≠ [])
    (checkNonempty : ∀ g ds, check g = .error ds → ds ≠ [])
    (notesNonempty : ∀ g ds, ds ≠ [] → notes g ds ≠ [])
    (generateNonempty : ∀ g ds, generate g = .error ds → ds ≠ []) :
    (∃ ds, ds ≠ [] ∧
      visible (pipeline parse resolve expand check notes strip warningFor generate) = .error ds) ∨
    (∃ code,
      visible (pipeline parse resolve expand check notes strip warningFor generate) = .ok code) := by
  cases h : visible (pipeline parse resolve expand check notes strip warningFor generate) with
  | error ds =>
    exact Or.inl ⟨ds, invariant2_visibleFailureNonempty parse resolve expand check notes
      strip warningFor generate parseNonempty resolveNonempty expandNonempty checkNonempty
      notesNonempty generateNonempty ds h, rfl⟩
  | ok code => exact Or.inr ⟨code, rfl⟩

-- Invariant 2: outer and inner failures are both visible.
example : visible (Grammar := Unit) (.error ["parse"]) = .error ["parse"] := by rfl
example : visible (.ok { grammar := (), warnings := [], moduleResult := fun _ => .error ["render"] }) =
    .error ["render"] := by rfl
example : visible (.ok { grammar := (), warnings := ["warning"], moduleResult := fun _ => .ok "module" }) =
    .ok "module" := by rfl

end PegHs.Pipeline

#print axioms PegHs.Pipeline.invariant2_generateFailure
#print axioms PegHs.Pipeline.invariant2_diagnosticOrModule
