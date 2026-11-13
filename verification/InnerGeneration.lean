import Pipeline
import Pragmas

namespace PegHs.InnerGeneration

abbrev Diagnostics := List String

-- The booleans are the two source guards, evaluated on the actual Options and
-- grammar module name. The functions are applied only to reached values.
def innerGenerate {G A : Type} (badFilename validModule : Bool)
    (moduleName : String) (g0 : G)
    (expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics)
    (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) :
    Except Diagnostics String :=
  if badFilename then .error ["the file name contains a control character"]
  else if !validModule then .error ["the generated module name is invalid: " ++ moduleName]
  else match expand g0 with
    | .error ds => .error (notes g0 ds)
    | .ok g => match check g with
      | .error ds => .error (notes g0 ds)
      | .ok analysis => match missing g analysis with
        | [] =>
          let unmarked := render g analysis ""
          let marker := freshMarker unmarked
          .ok (finalize marker (render g analysis marker))
        | names => .error (names.map fun n => "the generator does not define " ++ n)

theorem fileNameFailure {G A : Type} (valid : Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) :
    innerGenerate true valid name g0 expand check notes missing render freshMarker finalize =
      .error ["the file name contains a control character"] := by
  simp [innerGenerate]

theorem moduleNameFailure {G A : Type} (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) :
    innerGenerate false false name g0 expand check notes missing render freshMarker finalize =
      .error ["the generated module name is invalid: " ++ name] := by
  simp [innerGenerate]

theorem expandFailure {G A : Type} (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) (ds : Diagnostics)
    (he : expand g0 = .error ds) :
    innerGenerate false true name g0 expand check notes missing render freshMarker finalize =
      .error (notes g0 ds) := by
  simp [innerGenerate, he]

theorem checkFailure {G A : Type} (name : String) (g0 g : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) (ds : Diagnostics)
    (he : expand g0 = .ok g) (hc : check g = .error ds) :
    innerGenerate false true name g0 expand check notes missing render freshMarker finalize =
      .error (notes g0 ds) := by
  simp [innerGenerate, he, hc]

theorem missingExportsFailure {G A : Type} (name : String) (g0 g : G) (a : A)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (names : List String) (nonempty : names ≠ [])
    (he : expand g0 = .ok g) (hc : check g = .ok a)
    (hm : missing g a = names) :
    innerGenerate false true name g0 expand check notes missing render freshMarker finalize =
      .error (names.map fun n => "the generator does not define " ++ n) := by
  simp [innerGenerate, he, hc, hm]

theorem generatedModule {G A : Type} (name : String) (g0 g : G) (a : A)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (he : expand g0 = .ok g) (hc : check g = .ok a)
    (hm : missing g a = []) :
    innerGenerate false true name g0 expand check notes missing render freshMarker finalize =
      .ok (let unmarked := render g a ""
           let marker := freshMarker unmarked
           finalize marker (render g a marker)) := by
  simp [innerGenerate, he, hc, hm]

theorem success_iff {G A : Type} (bad valid : Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) (code : String) :
    innerGenerate bad valid name g0 expand check notes missing render freshMarker finalize = .ok code ↔
      bad = false ∧ valid = true ∧
        ∃ g a, expand g0 = .ok g ∧ check g = .ok a ∧ missing g a = [] ∧
          code = (let unmarked := render g a ""
                  let marker := freshMarker unmarked
                  finalize marker (render g a marker)) := by
  cases bad <;> cases valid <;> cases he : expand g0 with
  | error ds => simp [innerGenerate, he]
  | ok g =>
    cases hc : check g with
    | error ds => simp [innerGenerate, he, hc]
    | ok a =>
      cases hm : missing g a with
      | nil =>
        simp [innerGenerate, he, hc, hm]
        all_goals exact eq_comm
      | cons x xs => simp [innerGenerate, he, hc, hm]

theorem invariant3_public_render_iff {G A : Type} (parse : Except Diagnostics G)
    (resolve expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Diagnostics) (bad : Bool) (valid : G → Bool) (name : G → String)
    (missing : G → A → List String) (render : G → A → String → String)
    (freshMarker : String → String) (finalize : String → String → String) (code : String) :
    let generate := fun target => innerGenerate bad (valid target) (name target) target
      expand check notes missing render freshMarker finalize
    Pipeline.visible (Pipeline.pipeline parse resolve expand (fun g => (check g).map (fun _ => ()))
      notes strip warnings generate) = .ok code ↔
      ∃ p r g, parse = .ok p ∧ resolve p = .ok r ∧ expand r = .ok g ∧
        (∃ a, check g = .ok a) ∧
        (let target := match strip with | none => g | some change => change g
         bad = false ∧ valid target = true ∧ ∃ final analysis,
           expand target = .ok final ∧ check final = .ok analysis ∧ missing final analysis = [] ∧
           code = (let marker := freshMarker (render final analysis "")
                   finalize marker (render final analysis marker))) := by
  dsimp only
  rw [Pipeline.invariant3_visible_success_iff]
  have checked (g : G) : (check g).map (fun _ => ()) = .ok () ↔ ∃ a, check g = .ok a := by
    cases check g <;> simp [Except.map]
  simp only [checked, success_iff]
  cases strip <;> rfl

#print axioms invariant3_public_render_iff

theorem failureNonempty {G A : Type} (bad valid : Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (expandNonempty : ∀ ds, expand g0 = .error ds → ds ≠ [])
    (checkNonempty : ∀ g ds, check g = .error ds → ds ≠ [])
    (notesNonempty : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (ds : Diagnostics)
    (failure : innerGenerate bad valid name g0 expand check notes missing render freshMarker finalize =
      .error ds) : ds ≠ [] := by
  cases bad with
  | true =>
    have eq : ds = ["the file name contains a control character"] := by
      simpa [innerGenerate] using failure.symm
    rw [eq]
    simp
  | false =>
    cases valid with
    | false =>
      have eq : ds = ["the generated module name is invalid: " ++ name] := by
        simpa [innerGenerate] using failure.symm
      rw [eq]
      simp
    | true =>
      cases he : expand g0 with
      | error eds =>
        have eq : ds = notes g0 eds := by simpa [innerGenerate, he] using failure.symm
        rw [eq]
        exact notesNonempty eds (expandNonempty eds he)
      | ok g =>
        cases hc : check g with
        | error cds =>
          have eq : ds = notes g0 cds := by simpa [innerGenerate, he, hc] using failure.symm
          rw [eq]
          exact notesNonempty cds (checkNonempty g cds hc)
        | ok a =>
          cases hm : missing g a with
          | nil => simp [innerGenerate, he, hc, hm] at failure
          | cons x xs =>
            have eq : ds = (x :: xs).map (fun n => "the generator does not define " ++ n) := by
              simpa [innerGenerate, he, hc, hm] using failure.symm
            rw [eq]
            simp

theorem diagnosticOrModule {G A : Type} (bad valid : Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (expandNonempty : ∀ ds, expand g0 = .error ds → ds ≠ [])
    (checkNonempty : ∀ g ds, check g = .error ds → ds ≠ [])
    (notesNonempty : ∀ ds, ds ≠ [] → notes g0 ds ≠ []) :
    (∃ ds, ds ≠ [] ∧ innerGenerate bad valid name g0 expand check notes missing render freshMarker finalize = .error ds) ∨
    (∃ code, innerGenerate bad valid name g0 expand check notes missing render freshMarker finalize = .ok code) := by
  cases h : innerGenerate bad valid name g0 expand check notes missing render freshMarker finalize with
  | error ds => exact Or.inl ⟨ds, failureNonempty bad valid name g0 expand check notes
      missing render freshMarker finalize expandNonempty checkNonempty notesNonempty ds h, rfl⟩
  | ok code => exact Or.inr ⟨code, rfl⟩

-- The public Generation field evaluates this inner result only when observed.
def innerAt {G A : Type} (bad valid : G → Bool) (name : G → String)
    (expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics)
    (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) (target : G) :
    Except Diagnostics String :=
  innerGenerate (bad target) (valid target) (name target) target
    expand check notes missing render freshMarker finalize

-- The file-name check uses code points, including the Haskell Char surrogate
-- range. Module-name classification takes the host's Unicode predicates.
def controlCodepoint (n : Nat) : Bool := n < 0x20 || n == 0x7f

def fileNameBad (source output : List Nat) : Bool :=
  [source, output].any (fun name => name.any controlCodepoint)

theorem fileNameBad_iff (source output : List Nat) :
    fileNameBad source output = true ↔
      (∃ n ∈ source, n < 0x20 ∨ n = 0x7f) ∨
      (∃ n ∈ output, n < 0x20 ∨ n = 0x7f) := by
  simp [fileNameBad, controlCodepoint, List.any_eq_true]

def identTail (alphaNum : Char → Bool) (c : Char) : Bool :=
  alphaNum c || c == '_' || c == '\''

def modulePart (upper alphaNum : Char → Bool) (part : String) : Bool :=
  match part.toList with
  | [] => false
  | c :: rest => upper c && rest.all (identTail alphaNum)

def moduleNameValid (upper alphaNum : Char → Bool) (name : String) : Bool :=
  (name.splitOn ".").all (modulePart upper alphaNum)

def ModuleNameSyntax (upper alphaNum : Char → Bool) (name : String) : Prop :=
  ∀ part ∈ name.splitOn ".",
    ∃ c rest, part.toList = c :: rest ∧ upper c = true ∧
      ∀ x ∈ rest, alphaNum x = true ∨ x = '_' ∨ x = '\''

theorem moduleNameValid_iff (upper alphaNum : Char → Bool) (name : String) :
    moduleNameValid upper alphaNum name = true ↔
      ModuleNameSyntax upper alphaNum name := by
  simp only [moduleNameValid, ModuleNameSyntax, List.all_eq_true]
  constructor
  · intro h part hp
    have hv := h part hp
    unfold modulePart at hv
    cases hc : part.toList with
    | nil => simp [hc] at hv
    | cons c rest =>
      simp only [hc, Bool.and_eq_true, List.all_eq_true] at hv
      refine ⟨c, rest, rfl, hv.1, ?_⟩
      intro x hx
      have ht := hv.2 x hx
      simpa [identTail, Bool.or_eq_true, or_assoc] using ht
  · intro h part hp
    obtain ⟨c, rest, hc, hu, ht⟩ := h part hp
    unfold modulePart
    simp only [hc, Bool.and_eq_true, List.all_eq_true]
    refine ⟨hu, ?_⟩
    intro x hx
    simpa [identTail, Bool.or_eq_true, or_assoc] using ht x hx

def guardedGenerate {G A : Type} (source output : List Nat)
    (upper alphaNum : Char → Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String) : Except Diagnostics String :=
  innerGenerate (fileNameBad source output) (moduleNameValid upper alphaNum name)
    name g0 expand check notes missing render freshMarker finalize

theorem guardedFileNameFailure {G A : Type} (source output : List Nat)
    (upper alphaNum : Char → Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (bad : (∃ n ∈ source, n < 0x20 ∨ n = 0x7f) ∨
      (∃ n ∈ output, n < 0x20 ∨ n = 0x7f)) :
    guardedGenerate source output upper alphaNum name g0
      expand check notes missing render freshMarker finalize =
      .error ["the file name contains a control character"] := by
  unfold guardedGenerate
  rw [(fileNameBad_iff source output).mpr bad]
  exact fileNameFailure _ _ _ _ _ _ _ _ _ _

theorem guardedModuleNameFailure {G A : Type} (source output : List Nat)
    (upper alphaNum : Char → Bool) (name : String) (g0 : G)
    (expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (safe : fileNameBad source output = false)
    (invalid : ¬ ModuleNameSyntax upper alphaNum name) :
    guardedGenerate source output upper alphaNum name g0
      expand check notes missing render freshMarker finalize =
      .error ["the generated module name is invalid: " ++ name] := by
  have hv : moduleNameValid upper alphaNum name = false := by
    cases h : moduleNameValid upper alphaNum name with
    | false => rfl
    | true => exact False.elim (invalid ((moduleNameValid_iff upper alphaNum name).mp h))
  unfold guardedGenerate
  rw [safe, hv]
  exact moduleNameFailure _ _ _ _ _ _ _ _ _

theorem visibleInnerFailure {G A : Type} (parsed g0 g : G) (ds : Diagnostics)
    (resolve outerExpand : G → Except Diagnostics G)
    (outerCheck : G → Except Diagnostics Unit)
    (outerNotes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (bad valid : G → Bool) (name : G → String)
    (innerExpand : G → Except Diagnostics G)
    (innerCheck : G → Except Diagnostics A)
    (innerNotes : G → Diagnostics → Diagnostics)
    (missing : G → A → List String)
    (render : G → A → String → String) (freshMarker : String → String)
    (finalize : String → String → String)
    (hr : resolve parsed = .ok g0) (he : outerExpand g0 = .ok g)
    (hc : outerCheck g = .ok ())
    (hg : innerAt bad valid name innerExpand innerCheck innerNotes missing render freshMarker finalize
      (match strip with | none => g | some change => change g) = .error ds) :
    PegHs.Pipeline.visible
      (PegHs.Pipeline.pipeline (.ok parsed) resolve outerExpand outerCheck outerNotes
        strip warningFor
        (innerAt bad valid name innerExpand innerCheck innerNotes missing render freshMarker finalize)) =
      .error ds := by
  exact PegHs.Pipeline.invariant2_generateFailure parsed g0 g ds resolve outerExpand
    outerCheck outerNotes strip warningFor
    (innerAt bad valid name innerExpand innerCheck innerNotes missing render freshMarker finalize)
    hr he hc hg

-- Invariant 2 boundary tests were written before innerGenerate existed.
example : innerGenerate true true "M" ()
    (fun _ => .ok ()) (fun _ => .ok ()) (fun _ ds => ds)
    (fun _ _ => []) (fun _ _ _ => "code") id (fun _ code => code) =
      .error ["the file name contains a control character"] := by rfl
example : innerGenerate false false "bad.name" ()
    (fun _ => .ok ()) (fun _ => .ok ()) (fun _ ds => ds)
    (fun _ _ => []) (fun _ _ _ => "code") id (fun _ code => code) =
      .error ["the generated module name is invalid: bad.name"] := by rfl
example : innerGenerate false true "M" ()
    (fun _ => .error ["expand"]) (fun _ => .ok ()) (fun _ ds => "note" :: ds)
    (fun _ _ => []) (fun _ _ _ => "code") id (fun _ code => code) =
      .error ["note", "expand"] := by rfl
example : innerGenerate (A := Unit) false true "M" ()
    (fun _ => .ok ()) (fun _ => .error ["check"]) (fun _ ds => "note" :: ds)
    (fun _ _ => []) (fun _ _ _ => "code") id (fun _ code => code) =
      .error ["note", "check"] := by rfl
example : innerGenerate false true "M" ()
    (fun _ => .ok ()) (fun _ => .ok ()) (fun _ _ => [])
    (fun _ _ => ["A", "B"]) (fun _ _ _ => "code") id (fun _ code => code) =
      .error ["the generator does not define A", "the generator does not define B"] := by rfl
example : innerGenerate false true "M" ()
    (fun _ => .ok ()) (fun _ => .ok ()) (fun _ _ => [])
    (fun _ _ => []) (fun _ _ _ => "rendered") id (fun _ code => "final " ++ code) =
      .ok "final rendered" := by rfl
example : innerGenerate false true "M" ()
    (fun _ => .ok ()) (fun _ => .ok ()) (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ marker => if marker == "" then "unmarked" else "code:" ++ marker)
    (fun first => if first == "unmarked" then "#R" else "wrong")
    (fun marker code => marker ++ "|" ++ code) =
      .ok "#R|code:#R" := by rfl
example : fileNameBad [0xd800] [] = false := by decide
example : fileNameBad [0x7f] [] = true := by decide
example : moduleNameValid (fun c => c == 'A') (fun c => c == '0') "A.A0" = true := by native_decide
example : moduleNameValid (fun c => c == 'A') (fun c => c == '0') "A..A" = false := by native_decide
example : moduleNameValid (fun c => c == 'A') (fun c => c == '0') "" = false := by native_decide

open Peg.Verification in
theorem successful_output_preserves_original_lines {G A : Type} (bad valid : Bool)
    (name path : String) (g0 : G) (expand : G → Except Diagnostics G)
    (check : G → Except Diagnostics A) (notes : G → Diagnostics → Diagnostics)
    (missing : G → A → List String) (render : G → A → String → String) (code : String)
    (success : innerGenerate bad valid name g0 expand check notes missing render selectMarker
      (fun marker => finalizeText marker path) = .ok code) :
    ∃ g a, expand g0 = .ok g ∧ check g = .ok a ∧ missing g a = [] ∧
      let unmarked := render g a ""
      let lines := textLines (render g a (selectMarker unmarked))
      ∀ (i : Nat) (inside : i < lines.length), lines[i] ∈ textLines unmarked →
        (textLines code)[i]? = some lines[i] := by
  obtain ⟨_, _, g, a, he, hc, hm, rfl⟩ := (success_iff ..).mp success
  exact ⟨g, a, he, hc, hm, selected_marker_preserves_text_line _ _ _⟩

#print axioms successful_output_preserves_original_lines

open Peg.Verification in
theorem invariant3_public_output_lines {G A : Type} (parse : Except Diagnostics G)
    (resolve expand : G → Except Diagnostics G) (check : G → Except Diagnostics A)
    (notes : G → Diagnostics → Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Diagnostics) (bad : Bool) (valid : G → Bool) (name : G → String)
    (missing : G → A → List String) (render : G → A → String → String) (path code : String)
    (success : Pipeline.visible (Pipeline.pipeline parse resolve expand (fun g => (check g).map (fun _ => ()))
      notes strip warnings (fun t => innerGenerate bad (valid t) (name t) t expand check notes missing
        render selectMarker (fun marker => finalizeText marker path))) = .ok code) :
    ∃ p r g final a, parse = .ok p ∧ resolve p = .ok r ∧ expand r = .ok g ∧
      expand (match strip with | none => g | some change => change g) = .ok final ∧
      check final = .ok a ∧ missing final a = [] ∧
      let unmarked := render final a ""
      let marker := selectMarker unmarked
      let lines := textLines (render final a marker)
      ∀ (i : Nat) (inside : i < lines.length),
        (textLines code)[i]? = some (if lines[i] = marker then renderLine (i + 2) path else lines[i]) ∧
        (lines[i] ∈ textLines unmarked → (textLines code)[i]? = some lines[i]) := by
  obtain ⟨_, _, _, hp, hr, he, _, _, _, final, a, hf, hc, hm, rfl⟩ :=
    (invariant3_public_render_iff ..).mp success
  refine ⟨_, _, _, final, a, hp, hr, he, hf, hc, hm, ?_⟩
  dsimp only
  intro i inside
  constructor
  · rw [finalizeText_lines]
    exact invariant3_finalize_lines_at _ _ _ i inside
  · exact selected_marker_preserves_text_line _ _ _ i inside

#print axioms invariant3_public_output_lines

end PegHs.InnerGeneration

#print axioms PegHs.InnerGeneration.success_iff
#print axioms PegHs.InnerGeneration.diagnosticOrModule
#print axioms PegHs.InnerGeneration.visibleInnerFailure
#print axioms PegHs.InnerGeneration.fileNameBad_iff
#print axioms PegHs.InnerGeneration.moduleNameValid_iff
