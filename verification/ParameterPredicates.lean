import Std

namespace PegHs.ParameterPredicates

-- A witness for the first separator, including the untrimmed name.
inductive FirstSeparator : List Char → List Char → List Char → Prop where
  | here (rest) : FirstSeparator (':' :: ':' :: rest) [] rest
  | later {c cs name ty} (skip : c ≠ ':' ∨ cs.head? ≠ some ':')
      (found : FirstSeparator cs name ty) : FirstSeparator (c :: cs) (c :: name) ty

def splitParam : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
      if c = ':' ∧ cs.head? = some ':' then some ([], cs.tail)
      else (splitParam cs).map fun (name, ty) => (c :: name, ty)

theorem split_sound {cs name ty} (h : splitParam cs = some (name, ty)) :
    FirstSeparator cs name ty := by
  induction cs generalizing name ty with
  | nil => simp [splitParam] at h
  | cons c cs ih =>
    simp only [splitParam] at h
    split at h
    next test =>
      obtain ⟨rfl, hc⟩ := test
      cases cs with
      | nil => simp at hc
      | cons a rest =>
        simp at hc; subst a; cases h; exact .here _
    next test =>
      cases hs : splitParam cs with
      | none => simp [hs] at h
      | some pair =>
        obtain ⟨n, t⟩ := pair
        simp [hs] at h
        obtain ⟨rfl, rfl⟩ := h
        by_cases colon : c = ':'
        · exact .later (.inr fun h => test ⟨colon, h⟩) (ih hs)
        · exact .later (.inl colon) (ih hs)

theorem split_complete {cs name ty} (found : FirstSeparator cs name ty) :
    splitParam cs = some (name, ty) := by
  induction found with
  | here => simp [splitParam]
  | later skip _ ih =>
    rcases skip with h | h <;> simp [splitParam, h, ih]

def strip (space : Char → Bool) (cs : List Char) :=
  ((cs.dropWhile space).reverse.dropWhile space).reverse

def stripEnd (space : Char → Bool) (cs : List Char) :=
  (cs.reverse.dropWhile space).reverse

private theorem dropWhile_nonspace {space : Char → Bool} {c : Char} (notSpace : space c = false)
    (cs : List Char) : c ∈ cs.dropWhile space ↔ c ∈ cs := by
  induction cs with
  | nil => simp
  | cons d ds ih =>
    cases hd : space d with
    | false => simp [List.dropWhile, hd]
    | true =>
      have ne : c ≠ d := fun eq => by simp [eq, hd] at notSpace
      simp [List.dropWhile, hd, ih, ne]

private theorem nonspace_iff_drop_nonempty {space : Char → Bool} (cs : List Char) :
    cs.dropWhile space ≠ [] ↔ ∃ c ∈ cs, space c = false := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    cases hc : space c with
    | false => simp [List.dropWhile, hc]
    | true => simp [List.dropWhile, hc, ih]

theorem invariant1_typeText (space : Char → Bool) (text : List Char) :
    stripEnd space text ≠ [] ↔ ∃ c ∈ text, space c = false := by
  simpa [stripEnd] using nonspace_iff_drop_nonempty (space := space) text.reverse

theorem invariant1_argumentChunk (space : Char → Bool) (text : List Char) :
    strip space text ≠ [] ↔ ∃ c ∈ text, space c = false := by
  change stripEnd space (text.dropWhile space) ≠ [] ↔ _
  rw [invariant1_typeText]
  exact exists_congr fun c => ⟨fun ⟨mem, hc⟩ => ⟨(dropWhile_nonspace hc text).mp mem, hc⟩,
    fun ⟨mem, hc⟩ => ⟨(dropWhile_nonspace hc text).mpr mem, hc⟩⟩

def identifier (alpha alnum : Char → Bool) : List Char → Bool
  | [] => false
  | c :: cs => (alpha c || c == '_') && cs.all fun d => alnum d || d == '_' || d == '\''

inductive ParamResult where
  | formError | typeError | ok (name ty : List Char)
  deriving DecidableEq, Repr

def classify (space alpha alnum : Char → Bool) (src : List Char) : ParamResult :=
  match splitParam src with
  | none => .formError
  | some (rawName, rawType) =>
    let name := strip space rawName
    if !identifier alpha alnum name then .formError
    else if (strip space rawType).isEmpty then .typeError
    else .ok name (strip space rawType)

theorem invariant1_parameter_accepts {space alpha alnum src n t} :
    classify space alpha alnum src = .ok n t ↔
      ∃ a b, FirstSeparator src a b ∧ strip space a = n ∧ strip space b = t ∧
        identifier alpha alnum n = true ∧ t ≠ [] := by
  constructor
  · intro h
    cases hs : splitParam src with
    | none => simp [classify, hs] at h
    | some pair =>
      obtain ⟨a, b⟩ := pair
      cases hi : identifier alpha alnum (strip space a) with
      | false => simp [classify, hs, hi] at h
      | true =>
        by_cases ht : strip space b = []
        · simp [classify, hs, hi, ht] at h
        · simp [classify, hs, hi, ht] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, _, split_sound hs, rfl, rfl, hi, ht⟩
  · rintro ⟨a, b, hs, rfl, rfl, hi, ht⟩
    simp [classify, split_complete hs, hi, ht]

theorem invariant1_parameter_type_error {space alpha alnum src} :
    classify space alpha alnum src = .typeError ↔
      ∃ a b, FirstSeparator src a b ∧ identifier alpha alnum (strip space a) = true ∧
        strip space b = [] := by
  constructor
  · intro h
    cases hs : splitParam src with
    | none => simp [classify, hs] at h
    | some pair =>
      obtain ⟨a, b⟩ := pair
      cases hi : identifier alpha alnum (strip space a) with
      | false => simp [classify, hs, hi] at h
      | true =>
        by_cases ht : strip space b = []
        · exact ⟨_, _, split_sound hs, hi, ht⟩
        · simp [classify, hs, hi, ht] at h
  · rintro ⟨a, b, hs, hi, ht⟩
    simp [classify, split_complete hs, hi, ht]

theorem invariant1_parameter_form_error {space alpha alnum src} :
    classify space alpha alnum src = .formError ↔
      ¬ ∃ a b, FirstSeparator src a b ∧ identifier alpha alnum (strip space a) = true := by
  constructor
  · rintro h ⟨a, b, found, hi⟩
    by_cases ht : strip space b = [] <;> simp [classify, split_complete found, hi, ht] at h
  · intro missing
    cases hs : splitParam src with
    | none => simp [classify, hs]
    | some pair =>
      obtain ⟨a, b⟩ := pair
      have hi : identifier alpha alnum (strip space a) = false := by
        cases test : identifier alpha alnum (strip space a) with
        | false => rfl
        | true => exact False.elim (missing ⟨_, _, split_sound hs, test⟩)
      simp [classify, hs, hi]

private theorem FirstSeparator.reconstruct {src a b : List Char} (found : FirstSeparator src a b) :
    src = a ++ [':', ':'] ++ b := by
  induction found with
  | here => rfl
  | later _ _ ih => exact congrArg (List.cons _) ih

theorem invariant1_parameter_type_start {space alpha alnum src name ty}
    (accepted : classify space alpha alnum src = .ok name ty) :
    ∃ rawName rawType, FirstSeparator src rawName rawType ∧
      src = (rawName ++ [':', ':'] ++ rawType.takeWhile space) ++ rawType.dropWhile space ∧
      (rawType.dropWhile space).head?.any (fun c => !space c) = true ∧
      stripEnd space (rawType.dropWhile space) = ty := by
  obtain ⟨a, b, found, _, rfl, _, nonempty⟩ := invariant1_parameter_accepts.mp accepted
  have parts := found.reconstruct
  refine ⟨a, b, found, ?_, ?_, rfl⟩
  · simpa [List.append_assoc] using parts
  · have existsChar := (invariant1_argumentChunk space b).1 nonempty
    have remaining := (nonspace_iff_drop_nonempty b).2 existsChar
    cases h : b.dropWhile space with
    | nil => contradiction
    | cons c cs =>
      have first := List.head?_dropWhile_not (p := space) (l := b)
      simp [h] at first
      simpa using first

end PegHs.ParameterPredicates
