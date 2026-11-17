import LabelCheckModel

/-!
A model of `check` of packages/peg-grammar/src/Peg/Grammar/Check.hs: the
branch of `check`, `checkRules` with its fifteen groups of errors, and every
function of the module they reach, translated function by function, with
`hasValue`, `countedItems`, `isUnit`, `valueRefs` and `isClassified` of
Peg.Grammar.Types. check-check-groups.sh fixes the whole Haskell module
(check-groups.source) and the spans of Types.hs, Grammar.hs, Templates.hs and
Codegen.hs that the model translates, and compares this model with the real
functions on the grammars of CheckGroupsProbe.hs.

The translation keeps the Haskell names. The differences of form:
- The expressions, items, locations and diagnostics are those of
  LabelCheckModel. `Data.Map` and `Data.Set` are lists. `M.fromList` keeps
  the last binding of a key (`findLast`); `M.fromListWith (\_ x -> x)` and
  `M.insertWith (\_ x -> x)` keep the first (`lookupFirst`). A set is a list
  read by membership.
- `M.toList (M.fromListWith (flip (++)) ...)` of the duplicate bindings and
  labels is `secondOccurrences`: the distinct keys in ascending order, each
  with the location of its second occurrence.
- `reach` makes no call when the new names are empty, where the Haskell
  function calls itself with `seen ∪ ∅` and `[] ++ ns`: the same arguments.
  Its new names are those of a finite list `univ`; `reach_universe`
  shows that the names of the grammar are in it, so the filter keeps all.
- `nullableRulesWith` carries the proof that the known set only grows
  (`nullableGoWith`), which bounds its loop, as in LabelCheckModel.
- `stronglyConnComp` of Data.Graph is replaced by `reach` from the callees
  of each rule: a rule is in left recursion when it reaches itself by at
  least one edge (see the premises).
- `hasValue`, `isUnit` and `countedItems` recurse into the items of a group
  through list functions (`valuedL`, `sigL`, `allUnitCounted`), which bound
  the recursion; CheckGroupsTheorems shows that they are the filters and
  `all` of the Haskell definitions.
- Text is `String`; `T.lines` and `T.words` are `linesOf` and `wordsOf` on
  the characters.
- `sortOn diagLoc` is `List.mergeSort` by the order of `Loc`.

Premises (not proved here; the probe compares the results):
- `classify` of Peg.Grammar.Types is not translated: its units, unknown
  rules, generated rules and data types are the field `classes` of `Oracle`.
- `codeVariables` of Peg.Grammar, and `Data.Char.isUpper` and `toUpper`, are
  the fields `codeVariables`, `isUpper` and `toUpper` of `Oracle`.
- `stronglyConnComp` returns the strongly connected components of the graph
  of the rules, without the edges to names that are not rules; a rule is in
  a `CyclicSCC`, or in an `AcyclicSCC` with an edge to itself, exactly when
  it reaches itself by at least one edge. The rule names are distinct:
  `assemble` and `resolveImports` reject a rule named twice, and
  `expandTemplates` names each instance with a name no rule has.
- `Data.List.sortOn` and `List.mergeSort` are both stable sorts by the same
  order, so they give the same list.
- Haskell's `Int` locations, counts and lengths are natural numbers.
-/

namespace PegHs.CheckGroups

open PegHs.LabelCheck (Loc Expr Item Diagnostic findLast lookupFirst indexed Sub setEq missing_lt isSpace)

/-! ## The grammar -/

-- An alternative: its location, items, action and constructor name.
structure Alt where
  loc : Loc
  items : List Item
  action : Option (Loc × String)
  constructor : Option (Loc × String)
  deriving Repr

-- `templateParams` is the length of `ruleTemplateParams`, which `check`
-- reads only through `null`; `params` are the names of `ruleParams`.
structure Rule where
  name : String
  loc : Loc
  params : List String
  templateParams : Nat
  annotation : Option Loc
  alts : List Alt
  deriving Repr

-- The fields of a grammar that `check` reads.
structure Grammar where
  library : Option Loc
  start : Option (Loc × String)
  entries : List (Loc × String)
  noMemo : List (Loc × String)
  languages : List (Loc × String)
  syntaxLoc : Option Loc
  tokens : List (Loc × String)
  trivia : List (Loc × String)
  inline : List (Loc × String)
  recovers : List ((Loc × String) × (Loc × String))
  safe : List (Loc × String)
  expects : List ((Loc × String) × (Loc × String))
  messages : List ((Loc × String) × (Loc × String))
  verbatim : List (Loc × String)
  rules : List Rule
  deriving Repr

structure Constructor where
  name : String
  nameLoc : Option Loc
  altLoc : Loc
  deriving Repr

structure DataType where
  rule : String
  name : String
  constructors : List Constructor
  deriving Repr

-- What `check` reads of `classify g`: `classUnits`, `classUnknown`, the
-- rules whose `classRules` entry is `Generated`, and `classDataTypes`.
structure Classification where
  units : List String
  unknown : List String
  generated : List String
  dataTypes : List DataType
  deriving Repr

-- The functions that the model does not translate (see the premises).
structure Oracle where
  classes : Classification
  codeVariables : Loc → String → List (Loc × String)
  isUpper : Char → Bool
  toUpper : Char → Char

-- `sortOn diagLoc`: `Loc` is ordered by file, line and column.
def locLe (a b : Loc) : Bool :=
  a.file < b.file || (a.file == b.file && (a.line < b.line || (a.line == b.line && a.col ≤ b.col)))

def sortOnLoc (ds : List Diagnostic) : List Diagnostic :=
  ds.mergeSort (fun a b => locLe a.loc b.loc)

def diag (l : Loc) (m : String) : Diagnostic := ⟨l, m⟩

def showT (n : Nat) : String := toString n

-- The distinct keys in ascending order, each with the location of its
-- second occurrence: `(n, _ : l : _) <- M.toList (M.fromListWith (flip
-- (++)) [(n, [l]) | ...])`.
def secondOf (n : String) : List Loc → List (String × Loc)
  | _ :: l :: _ => [(n, l)]
  | _ => []

def secondOccurrences (xs : List (String × Loc)) : List (String × Loc) :=
  ((xs.map Prod.fst).eraseDups.mergeSort (fun a b => decide (a ≤ b))).flatMap fun n =>
    secondOf n ((xs.filter (fun x => x.1 == n)).map Prod.snd)

/-! ## Expressions -/

-- `exprRefs`: the references, with their locations and numbers of arguments.
def exprRefs : Expr → List (Loc × String × Nat)
  | .ref l n args => [(l, n, args.length)]
  | .group alts => exprRefs.alts alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprRefs x
  | .label _ x _ => exprRefs x
  | .template _ _ args _ => exprRefs.list args
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List (Loc × String × Nat)
    | [] => []
    | a :: as => exprRefs.items a ++ exprRefs.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items : List Item → List (Loc × String × Nat)
    | [] => []
    | (_, _, e) :: is => exprRefs e ++ exprRefs.items is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
  list : List Expr → List (Loc × String × Nat)
    | [] => []
    | x :: xs => exprRefs x ++ exprRefs.list xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega

-- `itemsRefs`.
def itemsRefs (items : List Item) : List (Loc × String × Nat) := exprRefs.items items

-- `exprLabels`: the labels written in an expression.
def exprLabels : Expr → List String
  | .label _ x n => n :: exprLabels x
  | .discard x | .star x | .plus x | .opt x | .and x | .not x | .capture x => exprLabels x
  | .template _ _ args _ => exprLabels.list args
  | .group alts => exprLabels.alts alts
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List String
    | [] => []
    | a :: as => exprLabels.items a ++ exprLabels.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items : List Item → List String
    | [] => []
    | (_, _, e) :: is => exprLabels e ++ exprLabels.items is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
  list : List Expr → List String
    | [] => []
    | x :: xs => exprLabels x ++ exprLabels.list xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega

-- `valueRefs` of Peg.Grammar.Types.
def valueRefs : Expr → List String
  | .ref _ n _ => [n]
  | .group alts => valueRefs.alts alts
  | .star x | .plus x | .opt x => valueRefs x
  | .label _ x _ => valueRefs x
  | .template _ _ args _ => valueRefs.list args
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List String
    | [] => []
    | a :: as => valueRefs.items a ++ valueRefs.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items : List Item → List String
    | [] => []
    | (_, _, e) :: is => valueRefs e ++ valueRefs.items is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
  list : List Expr → List String
    | [] => []
    | x :: xs => valueRefs x ++ valueRefs.list xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega

/-! ## Values (Peg.Grammar.Types) -/

mutual
-- `hasValue units`.
def hasValue (u : List String) : Expr → Bool
  | .ref .. => true
  | .capture _ => true
  | .star x | .plus x | .opt x => hasValue u x
  | .label _ x _ => hasValue u x
  | .template .. => true
  | .group alts => !alts.isEmpty && groupOne u alts
  | _ => false
termination_by e => (sizeOf e, 0)

-- `all ((== 1) . length . countedItems units)`.
def groupOne (u : List String) : List (List Item) → Bool
  | [] => true
  | a :: as => (countedItems u a).length == 1 && groupOne u as
termination_by as => (sizeOf as, 0)

-- `isUnit units`.
def isUnit (u : List String) : Expr → Bool
  | .ref _ n _ => u.contains n
  | .star x | .plus x | .opt x => isUnit u x
  | .label _ x _ => isUnit u x
  | .group alts => !alts.isEmpty && unitAlts u alts && hasValue u (.group alts)
  | _ => false
termination_by e => (sizeOf e, 1)

-- `all (\is -> all (isUnit units . itemExpr) (countedItems units is))`.
def unitAlts (u : List String) : List (List Item) → Bool
  | [] => true
  | a :: as => allUnitCounted u a && unitAlts u as
termination_by as => (sizeOf as, 0)

-- `countedItems units items`.
def countedItems (u : List String) (items : List Item) : List Item :=
  if sigL u items = [] then valuedL u items else sigL u items
termination_by (sizeOf items, 2)

-- `[i | i <- items, hasValue units (itemExpr i)]`.
def valuedL (u : List String) : List Item → List Item
  | [] => []
  | (l, b, e) :: is => if hasValue u e then (l, b, e) :: valuedL u is else valuedL u is
termination_by is => (sizeOf is, 0)

-- `[i | i <- valued, isJust (itemBind i) || not (isUnit units (itemExpr i))]`.
def sigL (u : List String) : List Item → List Item
  | [] => []
  | (l, b, e) :: is =>
    if hasValue u e && (b.isSome || !isUnit u e) then (l, b, e) :: sigL u is else sigL u is
termination_by is => (sizeOf is, 0)

-- `all (isUnit units . itemExpr) (countedItems units items)`.
def allUnitCounted (u : List String) (items : List Item) : Bool :=
  if sigL u items = [] then allUnitValued u items else allUnitSig u items
termination_by (sizeOf items, 2)

def allUnitValued (u : List String) : List Item → Bool
  | [] => true
  | (_, _, e) :: is => (!hasValue u e || isUnit u e) && allUnitValued u is
termination_by is => (sizeOf is, 0)

def allUnitSig (u : List String) : List Item → Bool
  | [] => true
  | (_, b, e) :: is =>
    (!(hasValue u e && (b.isSome || !isUnit u e)) || isUnit u e) && allUnitSig u is
termination_by is => (sizeOf is, 0)
end

/-! ## Nullability -/

-- The recovery rule of each label: `M.fromList`, so the last one.
abbrev Recovery := List (String × String)

mutual
def exprNullableWith (rec : Recovery) (known : List String) : Expr → Bool
  | .lit t _ => t.isEmpty
  | .cls .. => false
  | .any => false
  | .ref _ n _ => known.contains n
  | .group alts => altsNullableWith rec known alts
  | .star _ => true
  | .opt _ => true
  | .plus x => exprNullableWith rec known x
  | .and _ => true
  | .not _ => true
  | .pred .. => true
  | .capture x => exprNullableWith rec known x
  | .label _ x l =>
    exprNullableWith rec known x || (match findLast rec l with
      | some r => known.contains r
      | none => false)
  | .discard x => exprNullableWith rec known x
  | .template .. => true
termination_by e => sizeOf e

-- `seqNullableWith recovery known`.
def seqNullableWith (rec : Recovery) (known : List String) : List Item → Bool
  | [] => true
  | (_, _, e) :: is => exprNullableWith rec known e && seqNullableWith rec known is
termination_by is => sizeOf is

-- `any (seqNullableWith recovery known)`.
def altsNullableWith (rec : Recovery) (known : List String) : List (List Item) → Bool
  | [] => false
  | a :: as => seqNullableWith rec known a || altsNullableWith rec known as
termination_by as => sizeOf as
end

def exprNullable (known : List String) (e : Expr) : Bool := exprNullableWith [] known e

def nullStepWith (rec : Recovery) (rules : List Rule) (known : List String) : List String :=
  (rules.filter (fun r => r.alts.any (fun a => seqNullableWith rec known a.items))).map (·.name)

mutual
theorem exprNullableWith_mono {rec : Recovery} {k k' : List String} (h : Sub k k') :
    (e : Expr) → exprNullableWith rec k e = true → exprNullableWith rec k' e = true
  | .lit .., hn => by simpa [exprNullableWith] using hn
  | .cls .., hn | .any, hn => by simp [exprNullableWith] at hn
  | .ref _ n _, hn => by
    simp [exprNullableWith] at hn ⊢
    exact h n hn
  | .group alts, hn => by
    simp only [exprNullableWith] at hn ⊢
    exact altsNullableWith_mono h alts hn
  | .plus x, hn | .capture x, hn | .discard x, hn => by
    simp only [exprNullableWith] at hn ⊢
    exact exprNullableWith_mono h x hn
  | .label _ x l, hn => by
    simp only [exprNullableWith, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (exprNullableWith_mono h x hn)
    · right
      cases hr : findLast rec l with
      | none => simp [hr] at hn
      | some r =>
        simp [hr] at hn ⊢
        exact h r hn
  | .star _, _ | .opt _, _ | .and _, _ | .not _, _ | .pred .., _ | .template .., _ => by
    simp [exprNullableWith]
termination_by e => sizeOf e

theorem seqNullableWith_mono {rec : Recovery} {k k' : List String} (h : Sub k k') :
    (is : List Item) → seqNullableWith rec k is = true → seqNullableWith rec k' is = true
  | [], _ => by simp [seqNullableWith]
  | (_, _, e) :: is, hn => by
    simp only [seqNullableWith, Bool.and_eq_true] at hn ⊢
    exact ⟨exprNullableWith_mono h e hn.1, seqNullableWith_mono h is hn.2⟩
termination_by is => sizeOf is

theorem altsNullableWith_mono {rec : Recovery} {k k' : List String} (h : Sub k k') :
    (as : List (List Item)) → altsNullableWith rec k as = true → altsNullableWith rec k' as = true
  | [], hn => by simp [altsNullableWith] at hn
  | a :: as, hn => by
    simp only [altsNullableWith, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (seqNullableWith_mono h a hn)
    · exact Or.inr (altsNullableWith_mono h as hn)
termination_by as => sizeOf as
end

theorem nullStepWith_mono {rec : Recovery} {rules : List Rule} {k k' : List String} (h : Sub k k') :
    Sub (nullStepWith rec rules k) (nullStepWith rec rules k') := by
  intro x hx
  simp only [nullStepWith, List.mem_map, List.mem_filter, List.any_eq_true] at hx ⊢
  obtain ⟨r, ⟨hr, a, ha, hn⟩, rfl⟩ := hx
  exact ⟨r, ⟨hr, a, ha, seqNullableWith_mono h _ hn⟩, rfl⟩

theorem nullStepWith_names (rec : Recovery) (rules : List Rule) (k : List String) :
    Sub (nullStepWith rec rules k) (rules.map (·.name)) := by
  intro x hx
  simp only [nullStepWith, List.mem_map, List.mem_filter] at hx ⊢
  obtain ⟨r, ⟨hr, _⟩, rfl⟩ := hx
  exact ⟨r, hr, rfl⟩

-- The loop `go` of nullableRulesWith, from a set that the step does not
-- shrink.
set_option linter.unusedVariables false in
def nullableGoWith (rec : Recovery) (rules : List Rule) (known : List String)
    (h : Sub known (nullStepWith rec rules known)) : List String :=
  let next := nullStepWith rec rules known
  if hne : setEq next known then known
  else nullableGoWith rec rules next (nullStepWith_mono h)
termination_by ((rules.map (·.name)).filter (fun x => !known.contains x)).length
decreasing_by
  exact missing_lt (names := rules.map (·.name)) h (nullStepWith_names rec rules known) (by simpa using hne)

def nullableRulesWith (rec : Recovery) (rules : List Rule) : List String :=
  nullableGoWith rec rules [] (fun _ h => by simp at h)

def nullableRules (rules : List Rule) : List String := nullableRulesWith [] rules

/-! ## Repetitions -/

-- `repetitionErrors known r`, `exprErrs l` and `seqErrs`.
def repExprErrs (known : List String) (l : Loc) : Expr → List Diagnostic
  | .star x | .plus x =>
    (if exprNullable known x then
      [diag l "the repeated expression can match the empty string, which would loop forever"]
    else []) ++ repExprErrs known l x
  | .opt x | .and x | .not x | .capture x | .discard x => repExprErrs known l x
  | .label _ x _ => repExprErrs known l x
  | .group alts => repExprErrs.alts known alts
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts (known : List String) : List (List Item) → List Diagnostic
    | [] => []
    | a :: as => repExprErrs.seq known a ++ repExprErrs.alts known as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  seq (known : List String) : List Item → List Diagnostic
    | [] => []
    | (l, _, e) :: is => repExprErrs known l e ++ repExprErrs.seq known is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

def repetitionErrors (known : List String) (r : Rule) : List Diagnostic :=
  r.alts.flatMap (fun a => repExprErrs.seq known a.items)

/-! ## Left recursion -/

-- `leftCalls recovery known`: `go` and `exprLeftCalls`.
def exprLeftCalls (rec : Recovery) (known : List String) : Expr → List String
  | .ref _ n _ => [n]
  | .group alts => exprLeftCalls.alts rec known alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprLeftCalls rec known x
  | .label _ x l => exprLeftCalls rec known x ++ (findLast rec l).toList
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts (rec : Recovery) (known : List String) : List (List Item) → List String
    | [] => []
    | a :: as => exprLeftCalls.go rec known a ++ exprLeftCalls.alts rec known as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  go (rec : Recovery) (known : List String) : List Item → List String
    | [] => []
    | (_, _, e) :: is =>
      exprLeftCalls rec known e ++ (if exprNullableWith rec known e then exprLeftCalls.go rec known is else [])
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

def leftCalls (rec : Recovery) (known : List String) (items : List Item) : List String :=
  exprLeftCalls.go rec known items

-- The number of names of `univ` that are not in `seen`.
def unseen (univ seen : List String) : Nat :=
  (univ.filter (fun x => !seen.contains x)).length

theorem unseen_append_le (univ seen next : List String) :
    unseen univ (seen ++ next) ≤ unseen univ seen := by
  unfold unseen
  apply PegHs.LabelCheck.filter_length_le
  intro y hy
  simp at hy ⊢
  exact fun h => hy.1 h

theorem unseen_append_lt (univ seen next : List String) (x : String)
    (hx : x ∈ univ) (hn : x ∈ next) (hs : x ∉ seen) :
    unseen univ (seen ++ next) < unseen univ seen := by
  unfold unseen
  apply PegHs.LabelCheck.filter_length_lt univ _ _ _ x hx
  · simpa using hs
  · simp [hn]
  · intro y hy
    simp at hy ⊢
    exact fun h => hy.1 h

-- `reach seen ns es` of checkRules, over a successor function: pop a name,
-- mark its unseen successors and push them; when the stack is empty, take
-- the next root. The new names are those of `univ`.
def reach (univ : List String) (succ : String → List String) (seen : List String) :
    List String → List String → List String
  | [], [] => seen
  | [], e :: es => reach univ succ seen [e] es
  | n :: ns, es =>
    let next := (succ n).filter (fun m => !seen.contains m && univ.contains m)
    if next = [] then reach univ succ seen ns es
    else reach univ succ (seen ++ next) (next ++ ns) es
termination_by ns es => (unseen univ seen, es.length, ns.length)
decreasing_by
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by simp))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
  · apply Prod.Lex.left
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (by assumption)
    have hx' := List.mem_filter.1 hx
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hx'
    exact unseen_append_lt univ seen _ x hx'.2.2 hx (by simpa using hx'.2.1)

-- The callees of a rule at the start of its alternatives, without
-- duplicates (`S.toList (S.fromList ...)` in any order: the model reads it by
-- membership).
def edges (rec : Recovery) (known : List String) (r : Rule) : List String :=
  (r.alts.flatMap (fun a => leftCalls rec known a.items)).eraseDups

-- The rules in left recursion: each rule that reaches itself by at least
-- one edge, the edges to names that are not rules left out.
def leftRecursiveRules (rec : Recovery) (rules : List Rule) : List String :=
  let known := nullableRulesWith rec rules
  let names := rules.map (·.name)
  let succ := fun n => match findLast (rules.map (fun r => (r.name, r))) n with
    | some r => (edges rec known r).filter (names.contains ·)
    | none => []
  names.filter (fun n => (reach names succ (succ n) (succ n) []).contains n)

/-! ## Alternatives -/

def omitsUnitAction (units : List String) (rule : String) (items : List Item) : Bool :=
  units.contains rule && !items.isEmpty && allUnitCounted units items

def discardsValues (discarding : List String) (rule : String) (items : List Item) : Bool :=
  discarding.contains rule && !items.isEmpty

def discardingRules (g : Grammar) : List String :=
  match g.syntaxLoc with
  | none => []
  | some _ => (g.rules.filter (fun r => r.annotation.isNone)).map (·.name)

def isClassified (g : Grammar) (r : Rule) : Bool :=
  g.syntaxLoc.isNone && r.annotation.isNone && r.templateParams == 0 && r.alts.all (fun a => a.action.isNone)

def valuedRules (g : Grammar) (c : Classification) : List String :=
  (g.rules.filter (fun r => isClassified g r && !c.units.contains r.name)).map (·.name)

-- `bindingErrors` of altErrors.
def bindingErrors (withValues : Bool) (units : List String) (items : List Item) : List Diagnostic :=
  items.flatMap fun (l, b, e) => match b with
    | none => []
    | some n =>
      ((if "_".isPrefixOf n then
          ["the binding " ++ n ++ " is reserved: names starting with an underscore belong to the generator"]
        else []) ++
       (if withValues && !hasValue units e then
          ["cannot bind " ++ n ++ ": the expression has no value (capture the text with $)"]
        else [])).map (diag l)

-- `duplicateErrors` of altErrors.
def duplicateErrors (items : List Item) : List Diagnostic :=
  (secondOccurrences (items.filterMap fun (l, b, _) => b.map (·, l))).map fun (n, l) =>
    diag l ("the binding " ++ n ++ " is used twice in this alternative")

-- `groupErrors` and `exprGroupErrors` of altErrors.
def groupExprErrs (withValues : Bool) (units : List String) : Expr → List Diagnostic
  | .group alts => groupExprErrs.alts withValues units alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => groupExprErrs withValues units x
  | .label _ x _ => groupExprErrs withValues units x
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts (withValues : Bool) (units : List String) : List (List Item) → List Diagnostic
    | [] => []
    | is :: as => bindingErrors withValues units is ++ groupExprErrs.items withValues units is ++
        groupExprErrs.alts withValues units as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items (withValues : Bool) (units : List String) : List Item → List Diagnostic
    | [] => []
    | (_, _, e) :: is => groupExprErrs withValues units e ++ groupExprErrs.items withValues units is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

-- `omissionErrors` of altErrors.
def omissionErrors (units discarding valued unknown : List String) (r : Rule) (a : Alt) : List Diagnostic :=
  match a.action with
  | some _ => []
  | none =>
    if valued.contains r.name then []
    else if unknown.contains r.name || (valueRefs.items a.items).any (unknown.contains ·) then []
    else
      let k := (countedItems units a.items).length
      if k == 1 then []
      else if omitsUnitAction units r.name a.items then []
      else if discardsValues discarding r.name a.items then []
      else if k == 0 then
        [diag a.loc "an alternative without an action must have exactly one element with a value, but it has none"]
      else
        [diag a.loc ("an alternative without an action must have exactly one element with a value, but it has " ++ showT k)]

def altErrors (withValues : Bool) (units discarding valued unknown : List String) (r : Rule) :
    List Diagnostic :=
  r.alts.flatMap fun a =>
    bindingErrors withValues units a.items ++ duplicateErrors a.items ++
      (if withValues then omissionErrors units discarding valued unknown r a else []) ++
      groupExprErrs.items withValues units a.items

/-! ## References to bindings -/

-- A piece of code with its kind and the bindings on its left.
abbrev Code := String × List String × (Loc × String)

-- `exprCodes left`.
def exprCodes (left : List String) : Expr → List Code
  | .pred _ c => [("predicate", left, c)]
  | .ref _ _ args => args.map (("argument", left, ·))
  | .template _ _ args vs => vs.map (("argument", left, ·)) ++ exprCodes.list left args
  | .group alts => exprCodes.alts left alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprCodes left x
  | .label _ x _ => exprCodes left x
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts (left : List String) : List (List Item) → List Code
    | [] => []
    | a :: as => exprCodes.items left a ++ exprCodes.alts left as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items (left : List String) : List Item → List Code
    | [] => []
    | (_, _, e) :: is => exprCodes left e ++ exprCodes.items left is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
  list (left : List String) : List Expr → List Code
    | [] => []
    | x :: xs => exprCodes left x ++ exprCodes.list left xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega

-- `boundIn` and `exprBound`: the bindings of a sequence, inside its groups too.
def exprBound : Expr → List String
  | .group alts => exprBound.alts alts
  | .template _ _ args _ => exprBound.list args
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprBound x
  | .label _ x _ => exprBound x
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List String
    | [] => []
    | a :: as => exprBound.boundIn a ++ exprBound.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  boundIn : List Item → List String
    | [] => []
    | (_, b, e) :: is => b.toList ++ exprBound e ++ exprBound.boundIn is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega
  list : List Expr → List String
    | [] => []
    | x :: xs => exprBound x ++ exprBound.list xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega

def boundIn (items : List Item) : List String := exprBound.boundIn items

-- The names bound at the top of a sequence: `[n | Item _ (Just n) _ <- items]`.
def topBound (items : List Item) : List String := items.filterMap (fun i => i.2.1)

-- `codes`: the predicates and arguments of a sequence, each with the
-- bindings on its left.
def codes (items : List Item) : List Code :=
  (indexed 0 items).flatMap fun (k, i) => exprCodes (topBound (items.take k)) i.2.2

def refMessage (kind n : String) (top inAlt : List String) : String :=
  if top.contains n then "the " ++ kind ++ " refers to " ++ n ++ ", which is bound to its right"
  else if inAlt.contains n then n ++ " is bound inside a group, which the code cannot see"
  else n ++ " is not bound in this alternative"

-- The code of an alternative: its action, then the codes of its sequence.
def altCodes (a : Alt) : List Code :=
  (match a.action with
    | some c => [("action", topBound a.items, c)]
    | none => []) ++ codes a.items

def bindingReferenceErrors (vars : Loc → String → List (Loc × String)) (r : Rule) : List Diagnostic :=
  let allBound := r.alts.flatMap (fun a => boundIn a.items)
  r.alts.flatMap fun a =>
    (altCodes a).flatMap fun (kind, left, l0, code) =>
      (vars l0 code).flatMap fun (l, n) =>
        if !r.params.contains n && allBound.contains n && !left.contains n then
          [diag l (refMessage kind n (topBound a.items) (boundIn a.items))]
        else []

/-! ## Constructor names -/

def lookupRule (rules : List Rule) (n : String) : Option Rule :=
  findLast (rules.map (fun r => (r.name, r))) n

def constructorPrefix (n : String) : String := "@" ++ n ++ " names a constructor, but "

def misplaced (g : Grammar) (c : Classification) (r : Rule) (n : String) : Option String :=
  if g.syntaxLoc.isSome then some (constructorPrefix n ++ "the grammar has %syntax")
  else if r.annotation.isSome then some (constructorPrefix n ++ "rule " ++ r.name ++ " has a type annotation")
  else if r.alts.any (fun a => a.action.isSome) then some (constructorPrefix n ++ "rule " ++ r.name ++ " has an action")
  else if c.unknown.contains r.name then none
  else if !c.generated.contains r.name then
    some (constructorPrefix n ++ "rule " ++ r.name ++ " has type (): no alternative has a value other than ()")
  else none

def startsUpper (isUpper : Char → Bool) (n : String) : Bool :=
  match n.toList with
  | c :: _ => isUpper c
  | [] => false

-- The data types whose rules have known types.
def knownTypes (c : Classification) : List DataType :=
  c.dataTypes.filter (fun d => !c.unknown.contains d.rule)

def typeNameErrors (g : Grammar) (c : Classification) : List Diagnostic :=
  let types := knownTypes c
  (indexed 0 types).flatMap fun (k, d) =>
    match (types.take k).filter (fun e => e.name == d.name) with
    | e :: _ =>
      [diag ((lookupRule g.rules d.rule).map (·.loc) |>.getD ⟨0, 1, 1⟩)
        ("the rules " ++ e.rule ++ " and " ++ d.rule ++ " have the same type name " ++ d.name ++ "; rename one of them")]
    | [] => []

-- `typeOwners`: the first rule of each type name, among the types without
-- a constructor of their name.
def typeOwners (c : Classification) : List (String × String) :=
  ((knownTypes c).filter (fun d => !(d.constructors.map (·.name)).contains d.name)).map fun d => (d.name, d.rule)

-- `constructors`: those of the types whose names are not those of earlier types.
def constructorList (c : Classification) : List (DataType × Constructor) :=
  let types := knownTypes c
  (indexed 0 types).flatMap fun (i, d) =>
    if (types.take i |>.map (·.name)).contains d.name then [] else d.constructors.map (d, ·)

-- `M.insertWith (\_ x -> x) n v seen`.
def insertFirst (seen : List (String × String)) (n v : String) : List (String × String) :=
  if (seen.map Prod.fst).contains n then seen else seen ++ [(n, v)]

-- A constructor whose name is that of the type of another rule.
def ownerClash (owners : List (String × String)) (d : DataType) (k : Constructor) : List Diagnostic :=
  match lookupFirst owners k.name with
  | some owner =>
    if owner != d.rule then
      [diag (k.nameLoc.getD k.altLoc) ("the constructor " ++ k.name ++ " of rule " ++ d.rule ++
        " has the name of the type of rule " ++ owner ++ "; name the alternative with @Name")]
    else []
  | none => []

-- `again` of clashes.
def clashAgain (owners seen : List (String × String)) (d : DataType) (k : Constructor) : List Diagnostic :=
  match lookupFirst seen k.name with
  | some owner =>
    if owner == d.rule then
      [diag (k.nameLoc.getD k.altLoc) ("the constructor " ++ k.name ++ " is defined twice in rule " ++ owner ++
        "; name one of the alternatives with @Name")]
    else
      [diag (k.nameLoc.getD k.altLoc) ("the constructor " ++ k.name ++ " of rule " ++ d.rule ++
        " is also a constructor of rule " ++ owner ++ "; name one of the alternatives with @Name")]
  | none => ownerClash owners d k

def clashes (owners : List (String × String)) :
    List (String × String) → List (DataType × Constructor) → List Diagnostic
  | _, [] => []
  | seen, (d, k) :: rest => clashAgain owners seen d k ++ clashes owners (insertFirst seen k.name d.rule) rest

-- The constructor names written where no type is generated.
def misplacedErrors (g : Grammar) (c : Classification) : List Diagnostic :=
  g.rules.flatMap fun r => r.alts.flatMap fun a => match a.constructor with
    | some (l, n) => (misplaced g c r n).toList.map (diag l)
    | none => []

-- The constructor names that do not start with an upper case letter.
def lowerErrors (g : Grammar) (c : Classification) (isUpper : Char → Bool) : List Diagnostic :=
  g.rules.flatMap fun r =>
    if c.generated.contains r.name || c.unknown.contains r.name then
      r.alts.flatMap fun a => match a.constructor with
        | some (l, n) =>
          if !startsUpper isUpper n then [diag l ("the constructor name " ++ n ++ " must start with an upper case letter")]
          else []
        | none => []
    else []

def constructorErrors (g : Grammar) (c : Classification) (isUpper : Char → Bool) : List Diagnostic :=
  misplacedErrors g c ++ lowerErrors g c isUpper ++ typeNameErrors g c ++
    clashes (typeOwners c) [] (constructorList c)

/-! ## Hygiene -/

-- `T.lines`, on characters: the current line is kept reversed.
def linesGo : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc => if c == '\n' then acc.reverse :: linesGo cs [] else linesGo cs (c :: acc)

def linesOf (s : String) : List String := (linesGo s.toList []).map String.ofList

-- `T.words`.
def wordsGo : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc =>
    if isSpace c then (if acc.isEmpty then wordsGo cs [] else acc.reverse :: wordsGo cs [])
    else wordsGo cs (c :: acc)

def wordsOf (s : String) : List String := (wordsGo s.toList []).map String.ofList

def takeWhileS (p : Char → Bool) (s : String) : String := String.ofList (s.toList.takeWhile p)

def reservedName (t : String) : Bool := "peg'".isPrefixOf t || "Peg'".isPrefixOf t

def atColumnOne (line : String) : Bool :=
  match line.toList with
  | c :: _ => !(c == ' ' || c == '\t')
  | [] => false

-- `defined` of lineErrors.
def definedName (line : String) : Option String :=
  match wordsOf line with
  | k :: n :: _ =>
    if ["data", "newtype", "type", "class", "pattern"].contains k then some n
    else if atColumnOne line then some (takeWhileS (fun c => c != '(' && c != ':') k)
    else none
  | [n] => if atColumnOne line then some (takeWhileS (fun c => c != '(' && c != ':') n) else none
  | [] => none

-- `afterAs`.
def afterAs (ws : List String) : Option (List String) :=
  match ws.dropWhile (· != "as") with
  | _ :: a :: _ => some [takeWhileS (fun c => c != '(' && c != ' ') a]
  | _ => none

-- `alias` of lineErrors.
def aliases (line : String) : List String :=
  match wordsOf line with
  | "import" :: rest => (afterAs rest).getD []
  | _ => []

def lineErrors (f ln : Nat) (line : String) : List Diagnostic :=
  ((definedName line).toList.flatMap fun n =>
      if atColumnOne line && reservedName n then [diag ⟨f, ln, 1⟩ ("the name " ++ n ++ " is reserved for generated code")]
      else []) ++
    (aliases line).flatMap fun a =>
      if ["PegRt", "PegPrelude"].contains a then [diag ⟨f, ln, 1⟩ ("the module alias " ++ a ++ " is reserved for generated code")]
      else []

def hygieneErrors (v : Loc × String) : List Diagnostic :=
  (indexed v.1.line (linesOf v.2)).flatMap fun (ln, line) => lineErrors v.1.file ln line

/-! ## Names in the syntax tree -/

-- `syntaxTypeName` of Peg.Grammar.
def syntaxTypeName (o : Oracle) (n : String) : String :=
  match n.toList with
  | c :: rest => if o.isUpper (o.toUpper c) then String.ofList (o.toUpper c :: rest) ++ "Syntax" else "Rule'" ++ n ++ "Syntax"
  | [] => "Rule'" ++ n ++ "Syntax"

def syntaxNameGo (o : Oracle) : List (String × String) → List Rule → List Diagnostic
  | _, [] => []
  | seen, r :: rs =>
    let t := syntaxTypeName o r.name
    match lookupFirst seen t with
    | some earlier =>
      diag r.loc ("the rules " ++ earlier ++ " and " ++ r.name ++ " have the same type name " ++ t ++ " in the syntax tree; rename one of them")
        :: syntaxNameGo o seen rs
    | none => syntaxNameGo o (seen ++ [(t, r.name)]) rs

def syntaxNameErrors (g : Grammar) (o : Oracle) : List Diagnostic :=
  match g.syntaxLoc with
  | none => []
  | some _ =>
    let noNode := (g.tokens ++ g.inline).map Prod.snd
    syntaxNameGo o [] (g.rules.filter (fun r => !noNode.contains r.name))

/-! ## The groups of checkRules -/

def ruleNames (g : Grammar) : List String := g.rules.map (·.name)

def refs (g : Grammar) : List (Loc × String × Nat) :=
  g.rules.flatMap fun r => r.alts.flatMap fun a => itemsRefs a.items

-- The names of the directives that must name rules.
def directiveNames (g : Grammar) : List (Loc × String) :=
  g.start.toList ++ g.entries ++ g.noMemo ++ g.tokens ++ g.trivia ++ g.inline ++ g.expects.map Prod.fst

def undefinedErrors (g : Grammar) : List Diagnostic :=
  (refs g).flatMap (fun (l, n, _) => if (ruleNames g).contains n then [] else [diag l ("undefined rule " ++ n)]) ++
    (directiveNames g).flatMap (fun (l, n) => if (ruleNames g).contains n then [] else [diag l ("undefined rule " ++ n)])

def arityMessage (n : String) (expected k : Nat) : String :=
  if expected == 0 then "rule " ++ n ++ " takes no arguments"
  else "rule " ++ n ++ " expects " ++ showT expected ++ " argument(s), but got " ++ showT k

def arityErrors (g : Grammar) : List Diagnostic :=
  (refs g).flatMap fun (l, n, k) => match lookupRule g.rules n with
    | some r => if k != r.params.length then [diag l (arityMessage n r.params.length k)] else []
    | none => []

def startName (g : Grammar) (firstRule : Rule) : String :=
  match g.start with
  | some (_, n) => n
  | none => firstRule.name

def startLoc (g : Grammar) (firstRule : Rule) : Loc :=
  match g.start with
  | some (l, _) => l
  | none => firstRule.loc

def entryErrors (g : Grammar) (firstRule : Rule) : List Diagnostic :=
  ((startLoc g firstRule, startName g firstRule) :: g.entries).flatMap (fun (l, n) =>
    match lookupRule g.rules n with
    | some r => if !r.params.isEmpty then [diag l ("the entry rule " ++ n ++ " cannot take parameters")] else []
    | none => []) ++
  (indexed 0 g.entries).flatMap fun (k, l, n) =>
    if ((g.entries.take k).map Prod.snd).contains n then [diag l ("the rule " ++ n ++ " is named in %entry twice")]
    else []

def roots (g : Grammar) : List String := g.entries.map Prod.snd ++ g.recovers.map (fun p => p.2.2)

-- The names that `reach` may mark: the start, the roots and the callees.
def reachUniverse (g : Grammar) (firstRule : Rule) : List String :=
  startName g firstRule :: roots g ++ (refs g).map (fun x => x.2.1)

def callees (g : Grammar) (n : String) : List String :=
  match lookupRule g.rules n with
  | some r => r.alts.flatMap (fun a => (itemsRefs a.items).map (fun x => x.2.1))
  | none => []

def reachable (g : Grammar) (firstRule : Rule) : List String :=
  reach (reachUniverse g firstRule) (callees g) (startName g firstRule :: roots g) [startName g firstRule] (roots g)

def reachabilityErrors (g : Grammar) (firstRule : Rule) : List Diagnostic :=
  g.rules.flatMap fun r =>
    if r.loc.file == 0 && !(reachable g firstRule).contains r.name then
      [diag r.loc ("rule " ++ r.name ++ " is unreachable from the start, entry and recovery rules")]
    else []

def languageErrors (g : Grammar) : List Diagnostic :=
  g.languages.flatMap fun (l, x) =>
    if ["RebindableSyntax"].contains x then
      [diag l ("%language " ++ x ++ " is not allowed: it changes the meaning of the generated code")]
    else []

def usedLabels (g : Grammar) : List String :=
  g.rules.flatMap fun r => r.alts.flatMap fun a => exprLabels.items a.items

def recoverErrors (g : Grammar) : List Diagnostic :=
  g.recovers.flatMap (fun (_, l, n) => if (ruleNames g).contains n then [] else [diag l ("undefined rule " ++ n)]) ++
  g.recovers.flatMap (fun (_, l, n) => match lookupRule g.rules n with
    | some r => if !r.params.isEmpty then [diag l ("the recovery rule " ++ n ++ " cannot take parameters")] else []
    | none => []) ++
  (secondOccurrences (g.recovers.map fun p => (p.1.2, p.1.1))).map (fun (n, l) =>
    diag l ("the label " ++ n ++ " has more than one recovery rule")) ++
  g.recovers.flatMap (fun ((l, n), _) =>
    if (usedLabels g).contains n then [] else [diag l ("the label " ++ n ++ " does not appear in the grammar")]) ++
  g.safe.flatMap (fun (l, n) =>
    if (usedLabels g).contains n then [] else [diag l ("the label " ++ n ++ " does not appear in the grammar")]) ++
  g.messages.flatMap (fun ((l, n), _) =>
    if (usedLabels g).contains n then [] else [diag l ("the label " ++ n ++ " does not appear in the grammar")])

def recovery (g : Grammar) : Recovery := g.recovers.map (fun p => (p.1.2, p.2.2))

def lrOf (g : Grammar) : List String := leftRecursiveRules (recovery g) g.rules

def nomemoErrors (g : Grammar) : List Diagnostic :=
  g.noMemo.flatMap fun (l, n) =>
    if (lrOf g).contains n then [diag l ("rule " ++ n ++ " takes part in left recursion and must be memoised")] else []

def syntaxErrors (g : Grammar) (firstRule : Rule) : List Diagnostic :=
  match g.syntaxLoc with
  | none =>
    [("token", g.tokens), ("trivia", g.trivia), ("inline", g.inline)].flatMap fun (d, xs) =>
      xs.map fun (l, _) => diag l ("%" ++ d ++ " requires %syntax")
  | some _ =>
    let tokenNames := g.tokens.map Prod.snd
    g.trivia.flatMap (fun (l, n) =>
      if tokenNames.contains n then [] else [diag l ("%trivia " ++ n ++ " must name a %token rule")]) ++
    g.inline.flatMap (fun (l, n) =>
      if tokenNames.contains n then [diag l ("rule " ++ n ++ " cannot be both %token and %inline")] else []) ++
    g.inline.flatMap (fun (l, n) =>
      if (startName g firstRule :: g.entries.map Prod.snd).contains n then
        [diag l ("the entry rule " ++ n ++ " cannot be %inline: the root of the syntax tree needs a kind")]
      else [])

def paramLrErrors (g : Grammar) : List Diagnostic :=
  g.rules.flatMap fun r =>
    if !r.params.isEmpty && (lrOf g).contains r.name then
      [diag r.loc ("rule " ++ r.name ++ " takes parameters and cannot take part in left recursion")]
    else []

-- The fifteen groups of `errors`, in the order of checkRules.
def groups (g : Grammar) (firstRule : Rule) (o : Oracle) : List (List Diagnostic) :=
  let c := o.classes
  let nullable := nullableRules g.rules
  [ undefinedErrors g
  , arityErrors g
  , entryErrors g firstRule
  , reachabilityErrors g firstRule
  , g.rules.flatMap (repetitionErrors nullable)
  , g.rules.flatMap (altErrors true c.units (discardingRules g) (valuedRules g c) c.unknown)
  , g.rules.flatMap (bindingReferenceErrors o.codeVariables)
  , constructorErrors g c o.isUpper
  , paramLrErrors g
  , syntaxNameErrors g o
  , g.verbatim.flatMap hygieneErrors
  , languageErrors g
  , nomemoErrors g
  , syntaxErrors g firstRule
  , recoverErrors g ]

-- `libraryErrors`: the six groups of a library on its own.
def libraryGroups (g : Grammar) (o : Oracle) : List (List Diagnostic) :=
  let c := o.classes
  let nullable := nullableRules g.rules
  [ undefinedErrors g
  , arityErrors g
  , g.rules.flatMap (repetitionErrors nullable)
  , g.rules.flatMap (altErrors false c.units (discardingRules g) (valuedRules g c) c.unknown)
  , g.rules.flatMap (bindingReferenceErrors o.codeVariables)
  , paramLrErrors g ]

def errors (g : Grammar) (firstRule : Rule) (o : Oracle) : List Diagnostic := (groups g firstRule o).flatten

def libraryErrors (g : Grammar) (o : Oracle) : List Diagnostic := (libraryGroups g o).flatten

-- What `Analysis` holds, without `analysisTypes`, which is `classify g`.
structure Analysis where
  start : String
  leftRecursive : List String
  nullable : List String
  units : List String
  deriving Repr

def checkRules (root : Bool) (g : Grammar) (firstRule : Rule) (o : Oracle) : Except (List Diagnostic) Analysis :=
  match sortOnLoc (if root then errors g firstRule o else libraryErrors g o) with
  | [] => .ok ⟨startName g firstRule, lrOf g, nullableRules g.rules, o.classes.units⟩
  | es => .error es

def check (g : Grammar) (o : Oracle) : Except (List Diagnostic) Analysis :=
  match g.library, g.rules with
  | some _, _ => .error [diag ⟨0, 1, 1⟩ "missing %module directive"]
  | none, [] => .error [diag ⟨0, 1, 1⟩ "the grammar has no rules"]
  | none, firstRule :: _ => checkRules true g firstRule o

def checkLibrary (g : Grammar) (o : Oracle) : List Diagnostic :=
  match g.rules with
  | [] => []
  | firstRule :: _ => match checkRules false g firstRule o with
    | .error es => es
    | .ok _ => []

end PegHs.CheckGroups
