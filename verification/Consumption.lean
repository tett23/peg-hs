import File

namespace PegVerification

-- Invariant 1 boundary: lookahead may succeed without consuming input.
example : run (.ahead (.char 'a')) ['a'] = .ok ['a'] := by
  simp [run]

private theorem append_remainders {xs ys zs : List Char}
    (h₁ : ∃ pre, xs = pre ++ ys) (h₂ : ∃ pre, ys = pre ++ zs) :
    ∃ pre, xs = pre ++ zs := by
  obtain ⟨p, rfl⟩ := h₁
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨p ++ q, by simp [List.append_assoc]⟩

theorem invariant1_run_suffix : ∀ (e : Expr) (xs ys : List Char),
    run e xs = .ok ys → ∃ pre, xs = pre ++ ys := by
  intro e
  induction e with
  | any =>
      intro xs ys h
      cases xs with
      | nil => simp [run] at h
      | cons c xs =>
          simp [run] at h
          subst ys
          exact ⟨[c], rfl⟩
  | char c =>
      intro xs ys h
      cases xs with
      | nil => simp [run] at h
      | cons d xs =>
          by_cases same : d = c
          · simp [run, same] at h
            subst ys
            exact ⟨[d], rfl⟩
          · simp [run, same] at h
  | seq a b iha ihb =>
      intro xs ys h
      cases ha : run a xs with
      | error err => simp [run, ha, Except.bind] at h
      | ok mid =>
          have hb : run b mid = .ok ys := by simpa [run, ha, Except.bind] using h
          exact append_remainders (iha xs mid ha) (ihb mid ys hb)
  | choice a b iha ihb =>
      intro xs ys h
      cases ha : run a xs with
      | ok mid =>
          have hy : mid = ys := by simpa [run, ha] using h
          subst ys
          exact iha xs mid ha
      | error err =>
          cases err with
          | none =>
              exact ihb xs ys (by simpa [run, ha] using h)
          | some name => simp [run, ha] at h
  | ahead a iha =>
      intro xs ys h
      cases ha : run a xs with
      | ok mid =>
          have hy : xs = ys := by simpa [run, ha] using h
          subst ys
          exact ⟨[], by simp⟩
      | error err => simp [run, ha] at h
  | notAhead a iha =>
      intro xs ys h
      cases ha : run a xs with
      | ok mid => simp [run, ha] at h
      | error err =>
          have hy : xs = ys := by simpa [run, ha] using h
          subst ys
          exact ⟨[], by simp⟩
  | eof =>
      intro xs ys h
      cases xs with
      | nil =>
          simp [run] at h
          subst ys
          exact ⟨[], rfl⟩
      | cons c xs => simp [run] at h
  | predicate b =>
      intro xs ys h
      cases b with
      | false => simp [run] at h
      | true =>
          have hy : xs = ys := by simpa [run] using h
          subst ys
          exact ⟨[], by simp⟩
  | label name a iha =>
      intro xs ys h
      cases ha : run a xs with
      | ok mid =>
          have hy : mid = ys := by simpa [run, ha] using h
          subst ys
          exact iha xs mid ha
      | error err =>
          cases err with
          | none => simp [run, ha] at h
          | some old => simp [run, ha] at h
  | many a iha =>
      have repeat_suffix : ∀ fuel xs ys,
          repeatRun (run a) fuel xs = .ok ys → ∃ pre, xs = pre ++ ys := by
        intro fuel
        induction fuel with
        | zero =>
            intro xs ys h
            simp [repeatRun] at h
        | succ fuel ih =>
            intro xs ys h
            cases ha : run a xs with
            | ok mid =>
                by_cases progress : mid.length < xs.length
                · have rest : repeatRun (run a) fuel mid = .ok ys := by
                    simpa [repeatRun, ha, progress] using h
                  exact append_remainders (iha xs mid ha) (ih mid ys rest)
                · have hy : xs = ys := by simpa [repeatRun, ha, progress] using h
                  subst ys
                  exact ⟨[], by simp⟩
            | error err =>
                cases err with
                | none =>
                    have hy : xs = ys := by simpa [repeatRun, ha] using h
                    subst ys
                    exact ⟨[], by simp⟩
                | some name => simp [repeatRun, ha] at h
      intro xs ys h
      exact repeat_suffix (xs.length + 1) xs ys (by simpa [run] using h)

-- The universal property includes zero-width and a consuming boundary case.
example (e : Expr) (xs ys : List Char) (ok : run e xs = .ok ys) :
    ∃ pre, xs = pre ++ ys := by
  exact invariant1_run_suffix e xs ys ok

#print axioms invariant1_run_suffix

end PegVerification

namespace PegVerification

-- File.Items phrased as explicit, nonempty consumed prefixes.
inductive PrefixItems (item : Expr) : List Char → Prop where
  | endOfFile : PrefixItems item []
  | next {xs ys pre} : pre ≠ [] → xs = pre ++ ys →
      Eval item xs (.ok ys) → PrefixItems item ys → PrefixItems item xs

theorem invariant1_file_items_prefix (item : Expr) (xs : List Char) :
    File.Items (fun a b => Eval item a (.ok b)) xs ↔ PrefixItems item xs := by
  constructor
  · intro h
    induction h with
    | endOfFile => exact .endOfFile
    | @next xs ys evaluation progress rest ih =>
        have ok : run item xs = .ok ys := run_sound evaluation
        obtain ⟨pre, eq⟩ := invariant1_run_suffix item xs ys ok
        have nonempty : pre ≠ [] := by
          intro empty
          subst pre
          simp at eq
          subst xs
          omega
        exact .next nonempty eq evaluation ih
  · intro h
    induction h with
    | endOfFile => exact .endOfFile
    | @next xs ys pre nonempty eq evaluation rest ih =>
        have progress : ys.length < xs.length := by
          cases pre with
          | nil => contradiction
          | cons c pre =>
              simp only [eq, List.length_append, List.length_cons]
              omega
        exact .next evaluation progress ih

-- The empty file has no item steps; a zero-width item cannot count as one.
example (item : Expr) : PrefixItems item [] := .endOfFile
example : ¬ PrefixItems (.ahead (.char 'a')) ['a'] := by
  intro h
  have items := (invariant1_file_items_prefix (.ahead (.char 'a')) ['a']).mpr h
  cases items with
  | next evaluation shorter rest =>
      have ok := run_sound evaluation
      simp [run] at ok
      simp [← ok] at shorter

#print axioms invariant1_file_items_prefix

end PegVerification
