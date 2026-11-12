import Std

namespace PegHs.TemplateQueue

def allowed (depth size : Nat) : Bool := depth ≤ 64 && size ≤ 10000

variable {Job State : Type}

-- Processing a fresh instance may change the memo table. Its children are only
-- the instances actually appended to the queue, after memo lookup.
structure Worker (Job State : Type) where
  size : Job → Nat
  expand : Nat → Job → State → State × List Job
  reject : Job → State → State

def visit (w : Worker Job State) (depth : Nat) (job : Job) (s : State) : State × List Job :=
  if allowed depth (w.size job) then w.expand depth job s else (w.reject job s, [])

def tag (depth : Nat) (jobs : List Job) := jobs.map (fun j => (depth, j))

-- The direct FIFO recursion in Templates.hs: remove the first instance and
-- append its fresh children behind all previously pending instances.
inductive Drains (w : Worker Job State) : State → List (Nat × Job) → State → Prop where
  | done (s) : Drains w s [] s
  | step {d j s t fresh pending final} (h : visit w d j s = (t, fresh))
      (rest : Drains w t (pending ++ tag (d+1) fresh) final) :
      Drains w s ((d,j) :: pending) final

-- Evaluate one finite layer, retaining FIFO order across parents.
def layer (w : Worker Job State) (d : Nat) : List Job → State → State × List Job
  | [], s => (s, [])
  | j :: js, s =>
    let (t, fresh) := visit w d j s
    let (u, later) := layer w d js t
    (u, fresh ++ later)

private theorem layer_drains (w : Worker Job State) (d : Nat) (jobs : List Job) :
    ∀ s pending final, Drains w (layer w d jobs s).1
      (pending ++ tag (d+1) (layer w d jobs s).2) final →
      Drains w s (tag d jobs ++ pending) final := by
  induction jobs with
  | nil => simp [layer, tag]
  | cons j js ih =>
    intro s pending final next
    cases h : visit w d j s with
    | mk t fresh =>
      cases hl : layer w d js t with
      | mk u later =>
        apply Drains.step h
        change Drains w t ((tag d js ++ pending) ++ tag (d+1) fresh) final
        rw [List.append_assoc]
        apply ih
        simpa [layer, h, hl, tag, List.append_assoc] using next

private theorem terminal_layer (w : Worker Job State) (d : Nat) (past : 64 < d)
    (jobs : List Job) (s : State) : (layer w d jobs s).2 = [] := by
  induction jobs generalizing s with
  | nil => rfl
  | cons j js ih =>
    simp [layer, visit, allowed, Nat.not_le_of_lt past, ih]

-- A FIFO queue initially contains only depth-one occurrences. After each
-- finite layer, the remaining jobs all have the next depth. Beyond the cap
-- every remaining job still executes its rejection action.
theorem invariant2_drain_terminates (w : Worker Job State) (jobs : List Job) (s : State)
    (d : Nat) : ∃ final, Drains w s (tag d jobs) final := by
  by_cases past : 64 < d
  · refine ⟨(layer w d jobs s).1, ?_⟩
    suffices Drains w s (tag d jobs ++ []) (layer w d jobs s).1 by simpa using this
    apply layer_drains
    rw [terminal_layer w d past]
    exact .done _
  · obtain ⟨final, next⟩ := invariant2_drain_terminates w (layer w d jobs s).2
        (layer w d jobs s).1 (d+1)
    refine ⟨final, ?_⟩
    suffices Drains w s (tag d jobs ++ []) final by simpa using this
    apply layer_drains
    simpa using next
termination_by 65 - d
decreasing_by omega

-- The outer pass returns on an error, equal classifications, or exhaustion
-- of the counter. In the last case it still runs the pass at counter zero.
def passes {Known Error Grammar : Type} [DecidableEq Known]
    (expand : Known → Except Error Grammar) (classify : Grammar → Known) :
    Nat → Known → Nat × Except Error Grammar
  | fuel, known =>
    match expand known with
    | .error e => (1, .error e)
    | .ok g =>
      match fuel with
      | 0 => (1, .ok g)
      | k+1 => if classify g = known then (1, .ok g) else
        let (count, result) := passes expand classify k (classify g)
        (count+1, result)

theorem invariant2_pass_count {K E G : Type} [DecidableEq K] (expand : K → Except E G)
    (classify : G → K) (fuel : Nat) (known : K) :
    1 ≤ (passes expand classify fuel known).1 ∧
    (passes expand classify fuel known).1 ≤ fuel+1 := by
  induction fuel generalizing known with
  | zero => cases h : expand known <;> simp [passes, h]
  | succ k ih =>
    cases h : expand known with
    | error e => simp [passes, h]
    | ok g =>
      by_cases same : classify g = known
      · simp [passes, h, same]
      · have bounds := ih (classify g)
        simp only [passes.eq_1 expand classify (k+1) known, h, same, ite_false]
        omega

-- The note changes one diagnostic at a time before Data.List.nub removes
-- duplicates. Its wording and the number of repeated diagnostics are immaterial.
def templateNotes {D : Type} [BEq D] (note : D → D) (ds : List D) :=
  (ds.map note).eraseDups

theorem invariant2_templateNotes_nonempty {D : Type} [BEq D] [LawfulBEq D]
    (note : D → D) (ds : List D) (nonempty : ds ≠ []) : templateNotes note ds ≠ [] := by
  cases ds with
  | nil => contradiction
  | cons d ds =>
    have member : note d ∈ templateNotes note (d :: ds) := by
      apply List.mem_eraseDups.mpr
      simp
    intro empty
    simp [empty] at member

example : allowed 64 10000 = true := by decide
example : allowed 65 10000 = false := by decide
example : allowed 64 10001 = false := by decide

end PegHs.TemplateQueue
