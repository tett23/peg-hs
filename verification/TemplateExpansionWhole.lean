import TemplateExpansionFresh

/-!
The whole of `expandTemplates` in packages/peg-grammar/src/Peg/Grammar/Templates.hs
(ADR 0031, ADR 0055), with every branch of `expandTemplates`, `expandOnce`,
`expandRule`, `expandAlt`, `expandItems`, `expandExpr`, `captures`, `argType`,
`instanceOf`, `freshName` and `drain`. The Haskell recursion of `drain` is the
relation `Drain`, one constructor per branch, and the pass loop `go` is the
relation `Go`. The other functions are total Lean functions.

The pieces come from the earlier modules: `substitute` and `valueErrors`
(TemplateSubstitution), the fresh decimal search (TemplateExpansionFresh), and
the depth and size limits `allowed` (TemplateQueue).

`expandTemplates_whole` states the whole theorem: a result exists and is
unique; a rejection has at least one diagnostic and no grammar; an accepted
grammar has no template, no template call and no reference to a template, and
it is the expanded ordinary rules followed by the instances, each instance
defined once under a name that no rule of the input has.

check-template-expansion-whole.sh fixes the Haskell source of every function
modelled here, and TemplateExpansionWholeProbe.hs compares the model with
the real `expandTemplates` on grammars parsed by `parseGrammar`.

Premises (explicit parameters, not proved here):
- `Env.idents` is `haskellIdents`, the lexer `codeVariables` (ADR 0082). The
  theorems hold for every function; the probe uses the Haskell results.
- `Env.instanceType` is `instanceType` and `classify` is
  `classifiedTypes . classify` of Peg.Grammar.Types. Only rule types depend on
  them; the theorems hold for every function, and the probe does not compare
  types.
- The key of the memo table is `show` of the arguments without locations.
  Derived `Show` is injective, so two keys are equal exactly when the plain
  arguments and the captured parameters are equal; the model compares them
  structurally through `Repr`.
- `show (k :: Integer)` of a nonnegative counter is `Nat.repr`
  (TemplateExpansionFresh, checked by its probe).
- `Data.Map` and `Data.Set` are modelled by lists: `M.fromList` keeps the last
  binding of a key, `M.insert` puts the newest binding first, `S.toAscList`
  sorts and removes duplicates, and membership is list membership.
- A location is a natural number; the probe writes `Loc f l c` as
  `l * 100000 + c` for the one file it parses.
- Haskell's `Int` depth and `Integer` sizes and counter never overflow here:
  the depth is incremented only while it is at most 64.
-/

namespace PegHs.TemplateExpansionWhole

open TemplateSubstitution (Expr Diagnostic Substitution substitute substituteAlt valueErrors)

abbrev Item := Option String × Expr

structure Alt where
  items : List Item
  action : Option String
  constructor : Option String := none
  deriving Repr

structure Rule where
  name : String
  location : Nat
  params : List (String × String)
  templateParams : List (String × Option String)
  type : String
  alts : List Alt
  annotation : Option Nat := none
  deriving Repr

-- The fields of the grammar that expandTemplates reads or writes; the others
-- are returned as they are.
structure Grammar where
  rules : List Rule
  start : List (Nat × String)
  entries : List (Nat × String)
  recovers : List (Nat × String)
  nomemo : List (Nat × String)
  tokens : List (Nat × String)
  trivia : List (Nat × String)
  inline : List (Nat × String)
  expects : List (Nat × String)
  syntaxMode : Bool
  deriving Repr

structure Env where
  idents : String → List String
  instanceType : Rule → List (Option String) → String

-- M.fromList: the last binding of a key wins.
def lookupLast {α : Type} (xs : List (String × α)) (n : String) : Option α :=
  (xs.reverse.find? (·.1 == n)).map (·.2)

-- M.lookup in a map built by M.insert, newest first.
def lookupFirst {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  (xs.find? (·.1 == k)).map (·.2)

def isTemplate (r : Rule) : Bool := !r.templateParams.isEmpty

def templatesOf (g : Grammar) : String → Option Rule :=
  lookupLast ((g.rules.filter isTemplate).map fun r => (r.name, r))

def ordinaryOf (g : Grammar) : List Rule := g.rules.filter (fun r => !isTemplate r)

-- The Haskell `exprChildren`.
def children : Expr → List Expr
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => [x]
  | .label _ x _ => [x]
  | _ => []

theorem item_lt {item : Item} {items : List Item} {alts : List (List Item)}
    (h1 : items ∈ alts) (h2 : item ∈ items) : sizeOf item.2 < sizeOf alts := by
  have a := List.sizeOf_lt_of_mem h1
  have b := List.sizeOf_lt_of_mem h2
  have c : sizeOf item.2 < sizeOf item := by cases item; simp; omega
  omega

-- The termination of the expression folds below, which follow the Haskell
-- recursion through groups, items and arguments.
macro "expr_decreasing" : tactic => `(tactic| (
  all_goals simp_wf
  all_goals first
    | omega
    | (have := item_lt (by assumption) (by assumption); omega)
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)))

mutual
def callsTemplateExpr : Expr → Bool
  | .template .. => true
  | .group alts => callsTemplateAlts alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => callsTemplateExpr x
  | .label _ x _ => callsTemplateExpr x
  | _ => false

def callsTemplateAlts : List (List Item) → Bool
  | [] => false
  | items :: alts => callsTemplateItems items || callsTemplateAlts alts

def callsTemplateItems : List Item → Bool
  | [] => false
  | (_, e) :: items => callsTemplateExpr e || callsTemplateItems items
end

def callsTemplate (r : Rule) : Bool :=
  r.alts.any fun a => callsTemplateItems a.items

-- The guard of expandTemplates and the first guard of expandOnce.
def plainGrammar (g : Grammar) : Bool :=
  !(g.rules.any isTemplate) && !(g.rules.any callsTemplate)

def exprCode : Expr → List String
  | .ref _ _ args => args
  | .predicate _ c => [c]
  | .group alts => alts.flatMap fun items => items.flatMap fun item => exprCode item.2
  | .template _ _ args vals => args.flatMap exprCode ++ vals
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprCode x
  | .label _ x _ => exprCode x
  | _ => []
termination_by e => sizeOf e
decreasing_by expr_decreasing

def altCode (a : Alt) : List String :=
  a.action.toList ++ a.items.flatMap fun item => exprCode item.2

def exprBinds : Expr → List String
  | .group alts => alts.flatMap fun items => items.flatMap fun item => item.1.toList ++ exprBinds item.2
  | .template _ _ args _ => args.flatMap exprBinds
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprBinds x
  | .label _ x _ => exprBinds x
  | _ => []
termination_by e => sizeOf e
decreasing_by expr_decreasing

-- The value parameters, the bindings and the identifiers of the code in the
-- body of a template.
def bodyNames (env : Env) (t : Rule) : List String :=
  t.params.map Prod.fst ++ t.alts.flatMap fun a =>
    (altCode a).flatMap env.idents ++ a.items.flatMap fun item => item.1.toList ++ exprBinds item.2

def ascending (xs : List String) : List String :=
  xs.eraseDups.mergeSort (fun a b => decide (a ≤ b))

def reservedBindings : List String := ["_env", "_col", "_span"]

structure Caller where
  name : String
  params : String → Option String

-- The constants of one expansion pass.
structure Ctx where
  env : Env
  templates : String → Option Rule
  used : List String
  ruleTypes : String → Option String

def ctxOf (env : Env) (known : List (String × String)) (g : Grammar) : Ctx where
  env := env
  templates := templatesOf g
  used := g.rules.map Rule.name
  ruleTypes := fun n => (lookupFirst known n).orElse fun _ => lookupLast (g.rules.map fun r => (r.name, r.type)) n

structure Job where
  name : String
  template : Rule
  args : List Expr
  captured : List (String × String)
  depth : Nat
  location : Nat

abbrev Key := String × String × List (String × String)

structure State where
  instances : List (Key × String) := []
  pending : List Job := []
  errors : List Diagnostic := []
  count : Nat := 0
  instanceTypes : List (String × String) := []
  generated : List String := []

-- addError for each diagnostic in order.
def addErrors (ds : List Diagnostic) (st : State) : State :=
  { st with errors := ds.reverse ++ st.errors }

-- Haskell's `plain`: the arguments without locations.
def plain : Expr → Expr
  | .ref _ n args => .ref 0 n args
  | .group alts => .group (alts.map fun items => items.map fun item => (item.1, plain item.2))
  | .star x => .star (plain x)
  | .plus x => .plus (plain x)
  | .opt x => .opt (plain x)
  | .and x => .and (plain x)
  | .not x => .not (plain x)
  | .capture x => .capture (plain x)
  | .label _ x n => .label 0 (plain x) n
  | .template _ n args vals => .template 0 n (args.map plain) vals
  | .discard x => .discard (plain x)
  | e => e
termination_by e => sizeOf e
decreasing_by expr_decreasing

def keyOf (t : Rule) (args : List Expr) (captured : List (String × String)) : Key :=
  (t.name, reprStr (args.map plain), captured)

-- freshName: the first k from the counter whose decimal name no rule and no
-- instance has. The bounded search finds it (TemplateExpansionFresh).
def freshName (used : List String) (base : String) (n : Nat) (generated : List String) : String :=
  match TemplateExpansion.boundedSearch base used generated n with
  | some k => TemplateExpansion.decimalName base k
  | none => base

def captures (c : Ctx) (caller : Caller) (scope : List String) (l : Nat) (t : Rule)
    (args : List Expr) : List (String × String) × List Diagnostic :=
  let names := ascending (args.flatMap fun a => (exprCode a).flatMap c.env.idents)
  let bound := names.filter (· ∈ scope)
  let taken := names.filterMap fun x =>
    if x ∈ reservedBindings ∨ x ∈ scope then none else (caller.params x).map (x, ·)
  let inBody := bodyNames c.env t
  (taken, bound.map (fun x => (l, "the argument of the template " ++ t.name ++ " uses the binding " ++ x ++
      ", which a template cannot take; pass it as a value argument")) ++
    (taken.filter (·.1 ∈ inBody)).map fun p => (l, "the template " ++ t.name ++ " uses the name " ++ p.1 ++
      " in its body, so its argument cannot take the parameter " ++ p.1 ++ " of the rule " ++ caller.name ++
      "; rename the parameter"))

def argType (c : Ctx) (st : State) (l : Nat) (p : String × Option String) (a : Expr) :
    Option String × List Diagnostic :=
  match p.2 with
  | none => (none, [])
  | some _ =>
    match a with
    | .ref _ n _ => (some ((lookupFirst st.instanceTypes n).getD ((c.ruleTypes n).getD "()")), [])
    | .capture _ => (some "PegRt.Text", [])
    | _ => (some "()", [(l, "the argument for " ++ p.1 ++ " must be a rule, a capture or a template call, since its value is used")])

def instanceOf (c : Ctx) (l depth : Nat) (t : Rule) (args : List Expr) (tys : List (Option String))
    (captured : List (String × String)) (st : State) : String × State :=
  let key := keyOf t args captured
  match lookupFirst st.instances key with
  | some name => (name, st)
  | none =>
    let name := freshName c.used t.name st.count st.generated
    (name, { st with
      instances := (key, name) :: st.instances
      pending := st.pending ++ [⟨name, t, args, captured, depth + 1, l⟩]
      count := st.count + 1
      instanceTypes := (name, c.env.instanceType t tys) :: st.instanceTypes
      generated := name :: st.generated })

def addBind (b : Option String) (scope : List String) : List String :=
  match b with
  | some x => x :: scope
  | none => scope

mutual
def expandExpr (c : Ctx) (caller : Caller) (depth : Nat) (scope : List String) :
    Expr → State → Expr × State
  | .ref l n args, st =>
    if (c.templates n).isSome then
      (.ref l n args, addErrors [(l, "the template " ++ n ++ " needs arguments: " ++ n ++ "<...>")] st)
    else (.ref l n args, st)
  | .template l n args vals, st =>
    match c.templates n with
    | none => (.ref l n [], addErrors [(l, "rule " ++ n ++ " is not a template")] st)
    | some t =>
      let st1 := addErrors (valueErrors l n t.params.length vals) st
      let r2 := expandArgs c caller depth scope args st1
      if r2.1.length != t.templateParams.length then
        (.ref l n [], addErrors [(l, "the template " ++ n ++ " expects " ++ toString t.templateParams.length ++
          " argument(s), but got " ++ toString r2.1.length)] r2.2)
      else
        let cap := captures c caller scope l t r2.1
        let st3 := addErrors cap.2 r2.2
        let tys := (t.templateParams.zip r2.1).map fun pa => argType c st3 l pa.1 pa.2
        let st4 := addErrors (tys.flatMap Prod.snd) st3
        let r5 := instanceOf c l depth t r2.1 (tys.map Prod.fst) cap.1 st4
        (.ref l r5.1 (vals ++ cap.1.map Prod.fst), r5.2)
  | .group alts, st =>
    let r := expandGroup c caller depth scope alts st
    (.group r.1, r.2)
  | .star x, st => let r := expandExpr c caller depth scope x st; (.star r.1, r.2)
  | .plus x, st => let r := expandExpr c caller depth scope x st; (.plus r.1, r.2)
  | .opt x, st => let r := expandExpr c caller depth scope x st; (.opt r.1, r.2)
  | .and x, st => let r := expandExpr c caller depth scope x st; (.and r.1, r.2)
  | .not x, st => let r := expandExpr c caller depth scope x st; (.not r.1, r.2)
  | .capture x, st => let r := expandExpr c caller depth scope x st; (.capture r.1, r.2)
  | .label l x n, st => let r := expandExpr c caller depth scope x st; (.label l r.1 n, r.2)
  | .discard x, st => let r := expandExpr c caller depth scope x st; (.discard r.1, r.2)
  | .lit v w, st => (.lit v w, st)
  | .charClass w, st => (.charClass w, st)
  | .any, st => (.any, st)
  | .predicate b code, st => (.predicate b code, st)

def expandArgs (c : Ctx) (caller : Caller) (depth : Nat) (scope : List String) :
    List Expr → State → List Expr × State
  | [], st => ([], st)
  | a :: as, st =>
    let r1 := expandExpr c caller depth scope a st
    let r2 := expandArgs c caller depth scope as r1.2
    (r1.1 :: r2.1, r2.2)

-- The bindings to the left of an item are in its scope.
def expandItems (c : Ctx) (caller : Caller) (depth : Nat) (scope : List String) :
    List Item → State → List Item × State
  | [], st => ([], st)
  | (b, e) :: is, st =>
    let r1 := expandExpr c caller depth scope e st
    let r2 := expandItems c caller depth (addBind b scope) is r1.2
    ((b, r1.1) :: r2.1, r2.2)

-- The bindings in a group are not in scope after the group.
def expandGroup (c : Ctx) (caller : Caller) (depth : Nat) (scope : List String) :
    List (List Item) → State → List (List Item) × State
  | [], st => ([], st)
  | items :: alts, st =>
    let r1 := expandItems c caller depth scope items st
    let r2 := expandGroup c caller depth scope alts r1.2
    (r1.1 :: r2.1, r2.2)
end

def expandAlts (c : Ctx) (caller : Caller) (depth : Nat) : List Alt → State → List Alt × State
  | [], st => ([], st)
  | a :: as, st =>
    let r1 := expandItems c caller depth [] a.items st
    let r2 := expandAlts c caller depth as r1.2
    ({ a with items := r1.1 } :: r2.1, r2.2)

def expandRules (c : Ctx) : List Rule → State → List Rule × State
  | [], st => ([], st)
  | r :: rs, st =>
    let caller : Caller := ⟨r.name, lookupLast r.params⟩
    let r1 := expandAlts c caller 0 r.alts st
    let r2 := expandRules c rs r1.2
    ({ r with alts := r1.1 } :: r2.1, r2.2)

def substitutionFor (t : Rule) (args : List Expr) : Substitution :=
  lookupLast ((t.templateParams.zip args).map fun pa => (pa.1.1, (pa.1.2.isSome, pa.2)))

def exprSize : Expr → Nat
  | .group alts => 1 + (alts.map fun items => (items.map fun item => exprSize item.2).sum).sum
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => 1 + exprSize x
  | .label _ x _ => 1 + exprSize x
  | .template _ _ args _ => 1 + (args.map exprSize).sum
  | _ => 1
termination_by e => sizeOf e
decreasing_by expr_decreasing

def argsSize (j : Job) : Nat := (j.args.map exprSize).sum

def depthMessage (t : Rule) : String :=
  "the expansion of the template " ++ t.name ++ " does not end: templates call templates more than " ++
    toString 64 ++ " levels deep"

-- The rejecting branch of drain.
def rejectJob (j : Job) (st : State) : State :=
  addErrors [(j.location, depthMessage j.template)] st

-- The expanding branch of drain: the instance rule of a job, with the
-- template as its caller (ADR 0055).
def instantiate (c : Ctx) (j : Job) (st : State) : Rule × State :=
  let t := j.template
  let sub := substitutionFor t j.args
  let caller : Caller := ⟨t.name, lookupLast (t.params ++ j.captured)⟩
  let r := expandAlts c caller j.depth (t.alts.map fun a => { a with items := substituteAlt sub a.items }) st
  let ty := (lookupFirst r.2.instanceTypes j.name).getD "()"
  let used := (r.1.flatMap altCode).flatMap c.env.idents
  let params := t.params ++ j.captured.map fun p =>
    (if p.1 ∈ used then p.1 else "_" ++ p.1 ++ "'", p.2)
  ({ t with name := j.name, params := params, templateParams := [], type := ty, alts := r.1 }, r.2)

-- drain: one constructor for each branch of the Haskell recursion.
inductive Drain (c : Ctx) : State → List Rule → State → Prop where
  | done {st : State} : st.pending = [] → Drain c st [] st
  | reject {st : State} {j : Job} {rest : List Job} {outs : List Rule} {fin : State} :
      st.pending = j :: rest → TemplateQueue.allowed j.depth (argsSize j) = false →
      Drain c (rejectJob j { st with pending := rest }) outs fin → Drain c st outs fin
  | expand {st : State} {j : Job} {rest : List Job} {outs : List Rule} {fin : State} :
      st.pending = j :: rest → TemplateQueue.allowed j.depth (argsSize j) = true →
      Drain c (instantiate c j { st with pending := rest }).2 outs fin →
      Drain c st ((instantiate c j { st with pending := rest }).1 :: outs) fin

def directiveErrors (g : Grammar) : List Diagnostic :=
  let templates := templatesOf g
  let named := [("start", g.start), ("entry", g.entries), ("recover", g.recovers), ("nomemo", g.nomemo),
    ("token", g.tokens), ("trivia", g.trivia), ("inline", g.inline), ("expect", g.expects)]
  let byName := ascending ((g.rules.filter isTemplate).map Rule.name)
  (named.flatMap fun dn => (dn.2.filter fun ln => (templates ln.2).isSome).map fun ln =>
    (ln.1, "the template " ++ ln.2 ++ " cannot be named in %" ++ dn.1)) ++
  (byName.filterMap templates).flatMap fun r =>
    let names := r.templateParams.map Prod.fst
    ((names.filter fun x => names.count x > 1).eraseDups).map fun p =>
      (r.location, "the template " ++ r.name ++ " has two parameters named " ++ p)

def finish (errs : List Diagnostic) : List Diagnostic := TemplateSubstitution.finishErrors errs

def accepted (g : Grammar) (rules : List Rule) (generated : List String) : Grammar :=
  { g with
    rules := rules
    inline := g.inline ++ (rules.filter fun r => g.syntaxMode && r.name ∈ generated).map fun r =>
      (r.location, r.name) }

-- expandOnce: its guards, then the expansion of the ordinary rules and the
-- queue of instances, from the empty state.
inductive ExpandOnce (env : Env) (known : List (String × String)) (g : Grammar) :
    Except (List Diagnostic) Grammar → Prop where
  | plain : plainGrammar g = true → ExpandOnce env known g (.ok g)
  | directives : plainGrammar g = false → directiveErrors g ≠ [] →
      ExpandOnce env known g (.error (directiveErrors g))
  | rejected {outs : List Rule} {fin : State} : plainGrammar g = false → directiveErrors g = [] →
      Drain (ctxOf env known g) (expandRules (ctxOf env known g) (ordinaryOf g) {}).2 outs fin →
      fin.errors ≠ [] → ExpandOnce env known g (.error (finish fin.errors))
  | expanded {outs : List Rule} {fin : State} : plainGrammar g = false → directiveErrors g = [] →
      Drain (ctxOf env known g) (expandRules (ctxOf env known g) (ordinaryOf g) {}).2 outs fin →
      fin.errors = [] →
      ExpandOnce env known g (.ok (accepted g ((expandRules (ctxOf env known g) (ordinaryOf g) {}).1 ++ outs)
        fin.generated))

abbrev Known := List (String × String)

-- go: the passes with the types of the previous pass, from the counter 8.
inductive Go (env : Env) (classify : Grammar → Known) (g : Grammar) :
    Nat → Known → Except (List Diagnostic) Grammar → Prop where
  | error {k : Nat} {known : Known} {ds : List Diagnostic} :
      ExpandOnce env known g (.error ds) → Go env classify g k known (.error ds)
  | stop {k : Nat} {known : Known} {g' : Grammar} :
      ExpandOnce env known g (.ok g') → (classify g' = known ∨ k = 0) → Go env classify g k known (.ok g')
  | next {k : Nat} {known : Known} {g' : Grammar} {r : Except (List Diagnostic) Grammar} :
      ExpandOnce env known g (.ok g') → classify g' ≠ known → Go env classify g k (classify g') r →
      Go env classify g (k + 1) known r

inductive ExpandTemplates (env : Env) (classify : Grammar → Known) (g : Grammar) :
    Except (List Diagnostic) Grammar → Prop where
  | plain : plainGrammar g = true → ExpandTemplates env classify g (.ok g)
  | passes {r : Except (List Diagnostic) Grammar} : plainGrammar g = false → Go env classify g 8 [] r →
      ExpandTemplates env classify g r

-- A computation of the relations with a bound on the steps of drain, for the
-- probe. `expandTemplatesRun_sound` shows that what it returns is the result
-- of the relations.
def drainRun (c : Ctx) : Nat → State → Option (List Rule × State)
  | 0, _ => none
  | fuel + 1, st =>
    match st.pending with
    | [] => some ([], st)
    | j :: rest =>
      if TemplateQueue.allowed j.depth (argsSize j) then
        let r := instantiate c j { st with pending := rest }
        (drainRun c fuel r.2).map fun p => (r.1 :: p.1, p.2)
      else drainRun c fuel (rejectJob j { st with pending := rest })

def expandOnceRun (env : Env) (fuel : Nat) (known : Known) (g : Grammar) :
    Option (Except (List Diagnostic) Grammar) :=
  if plainGrammar g then some (.ok g)
  else if directiveErrors g ≠ [] then some (.error (directiveErrors g))
  else
    let c := ctxOf env known g
    let r := expandRules c (ordinaryOf g) {}
    (drainRun c fuel r.2).map fun p =>
      if p.2.errors ≠ [] then .error (finish p.2.errors) else .ok (accepted g (r.1 ++ p.1) p.2.generated)

def goRun (env : Env) (classify : Grammar → Known) (fuel : Nat) (g : Grammar) :
    Nat → Known → Option (Except (List Diagnostic) Grammar)
  | k, known =>
    match expandOnceRun env fuel known g with
    | none => none
    | some (.error ds) => some (.error ds)
    | some (.ok g') =>
      match k with
      | 0 => some (.ok g')
      | k + 1 => if classify g' = known then some (.ok g') else goRun env classify fuel g k (classify g')

def expandTemplatesRun (env : Env) (classify : Grammar → Known) (fuel : Nat) (g : Grammar) :
    Option (Except (List Diagnostic) Grammar) :=
  if plainGrammar g then some (.ok g) else goRun env classify fuel g 8 []

/-! ## Invariants -/

-- No template call and no reference to a template.
mutual
def cleanExpr (isT : String → Bool) : Expr → Bool
  | .ref _ n _ => !isT n
  | .template .. => false
  | .group alts => cleanAlts isT alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => cleanExpr isT x
  | .label _ x _ => cleanExpr isT x
  | _ => true

def cleanAlts (isT : String → Bool) : List (List Item) → Bool
  | [] => true
  | items :: alts => cleanItems isT items && cleanAlts isT alts

def cleanItems (isT : String → Bool) : List Item → Bool
  | [] => true
  | (_, e) :: items => cleanExpr isT e && cleanItems isT items
end

def CleanRule (isT : String → Bool) (r : Rule) : Prop :=
  r.templateParams = [] ∧ ∀ a ∈ r.alts, cleanItems isT a.items = true

def isT (c : Ctx) (n : String) : Bool := (c.templates n).isSome

-- Every template is a rule of the grammar.
def WF (c : Ctx) : Prop := ∀ n t, c.templates n = some t → n ∈ c.used

-- The diagnostics only grow; the queue and the instance names only grow at
-- the back and the front, by the same jobs, each one level deeper.
structure Grows (depth : Nat) (st st' : State) : Prop where
  errors : st.errors.length ≤ st'.errors.length
  jobs : ∃ new : List Job, st'.pending = st.pending ++ new ∧
    st'.generated = (new.map Job.name).reverse ++ st.generated ∧ ∀ j ∈ new, j.depth = depth + 1

-- The instance names are distinct, no rule has one, and the memo table only
-- returns them.
def Fresh (c : Ctx) (st : State) : Prop :=
  st.generated.Nodup ∧ (∀ n ∈ st.generated, n ∉ c.used) ∧ (∀ p ∈ st.instances, p.2 ∈ st.generated)

-- A step from st to st' that keeps the invariants, and whose result has the
-- property `clean` when it added no diagnostic.
def Spec (c : Ctx) (depth : Nat) (st st' : State) (clean : Prop) : Prop :=
  Grows depth st st' ∧ (Fresh c st → Fresh c st' ∧ (st'.errors.length = st.errors.length → clean))

theorem Spec.refl (c : Ctx) (depth : Nat) (st : State) {P : Prop} (h : P) : Spec c depth st st P :=
  ⟨⟨Nat.le_refl _, [], by simp, by simp, by simp⟩, fun f => ⟨f, fun _ => h⟩⟩

theorem Spec.trans {c : Ctx} {d : Nat} {st st1 st2 : State} {P Q : Prop}
    (h1 : Spec c d st st1 P) (h2 : Spec c d st1 st2 Q) : Spec c d st st2 (P ∧ Q) := by
  obtain ⟨⟨e1, n1, p1, g1, d1⟩, f1⟩ := h1
  obtain ⟨⟨e2, n2, p2, g2, d2⟩, f2⟩ := h2
  refine ⟨⟨by omega, n1 ++ n2, by simp [p2, p1], by simp [g2, g1, List.reverse_append], ?_⟩, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact d1 j hj
    · exact d2 j hj
  · intro f
    obtain ⟨f1', c1⟩ := f1 f
    obtain ⟨f2', c2⟩ := f2 f1'
    exact ⟨f2', fun eq => ⟨c1 (by omega), c2 (by omega)⟩⟩

theorem Spec.mono {c : Ctx} {d : Nat} {st st' : State} {P Q : Prop}
    (h : Spec c d st st' P) (imp : P → Q) : Spec c d st st' Q :=
  ⟨h.1, fun f => ⟨(h.2 f).1, fun eq => imp ((h.2 f).2 eq)⟩⟩

theorem addErrors_spec (c : Ctx) (d : Nat) (ds : List Diagnostic) (st : State) :
    Spec c d st (addErrors ds st) (ds = []) := by
  refine ⟨⟨by simp [addErrors], [], by simp [addErrors], by simp [addErrors], by simp⟩, ?_⟩
  intro f
  refine ⟨f, fun eq => ?_⟩
  simp [addErrors] at eq
  exact eq

theorem freshName_fresh (used : List String) (base : String) (n : Nat) (generated : List String) :
    freshName used base n generated ∉ used ∧ freshName used base n generated ∉ generated := by
  obtain ⟨k, hk⟩ := TemplateExpansion.boundedSearch_succeeds base used generated n
  have first := TemplateExpansion.boundedSearch_first base used generated n k hk
  simp only [freshName, hk]
  exact ⟨first.2.2.1, first.2.2.2.1⟩

theorem lookupFirst_mem {α β : Type} [BEq α] [LawfulBEq α] {xs : List (α × β)} {k : α} {v : β}
    (h : lookupFirst xs k = some v) : (k, v) ∈ xs := by
  unfold lookupFirst at h
  cases hf : xs.find? (·.1 == k) with
  | none => simp [hf] at h
  | some p =>
    simp [hf] at h
    have mem := List.mem_of_find?_eq_some hf
    have key := List.find?_some hf
    simp at key
    cases p
    simp_all

theorem lookupLast_mem {α : Type} {xs : List (String × α)} {n : String} {v : α}
    (h : lookupLast xs n = some v) : (n, v) ∈ xs := by
  unfold lookupLast at h
  cases hf : xs.reverse.find? (·.1 == n) with
  | none => simp [hf] at h
  | some p =>
    simp [hf] at h
    have mem := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
    have key := List.find?_some hf
    simp at key
    cases p
    simp_all

theorem instanceOf_spec (c : Ctx) (wf : WF c) (l depth : Nat) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × String)) (st : State) :
    Spec c depth st (instanceOf c l depth t args tys captured st).2
      (isT c (instanceOf c l depth t args tys captured st).1 = false) := by
  have notTemplate : ∀ n, n ∉ c.used → isT c n = false := by
    intro n out
    cases h : c.templates n with
    | none => simp [isT, h]
    | some t => exact absurd (wf n t h) out
  unfold instanceOf
  dsimp only
  cases hk : lookupFirst st.instances (keyOf t args captured) with
  | some name =>
    simp only []
    refine ⟨⟨Nat.le_refl _, [], by simp, by simp, by simp⟩, fun f => ⟨f, fun _ => ?_⟩⟩
    exact notTemplate name (f.2.1 name (f.2.2 _ (lookupFirst_mem hk)))
  | none =>
    simp only []
    have fresh := freshName_fresh c.used t.name st.count st.generated
    refine ⟨⟨by simp, [_], rfl, by simp, by simp⟩, fun f => ⟨?_, fun _ => notTemplate _ fresh.1⟩⟩
    refine ⟨List.nodup_cons.mpr ⟨fresh.2, f.1⟩, ?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact fresh.1
      · exact f.2.1 n hn
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (f.2.2 p hp)

mutual
theorem expandExpr_spec (c : Ctx) (wf : WF c) (caller : Caller) (depth : Nat) :
    ∀ (scope : List String) (e : Expr) (st : State),
      Spec c depth st (expandExpr c caller depth scope e st).2
        (cleanExpr (isT c) (expandExpr c caller depth scope e st).1 = true)
  | scope, .ref l n args, st => by
    unfold expandExpr
    split
    · exact (addErrors_spec c depth _ st).mono (by simp)
    · exact Spec.refl c depth st (by simp [cleanExpr, isT, *])
  | scope, .template l n args vals, st => by
    unfold expandExpr
    split
    · exact (addErrors_spec c depth _ st).mono (by simp)
    · rename_i t _
      dsimp only
      have s1 := addErrors_spec c depth (valueErrors l n t.params.length vals) st
      have s2 := expandArgs_spec c wf caller depth scope args
        (addErrors (valueErrors l n t.params.length vals) st)
      split
      · exact ((s1.trans s2).trans (addErrors_spec c depth _ _)).mono (by simp)
      · refine (((s1.trans s2).trans (addErrors_spec c depth _ _)).trans
          ((addErrors_spec c depth _ _).trans (instanceOf_spec c wf _ _ _ _ _ _ _))).mono ?_
        intro h
        have name := h.2.2
        simp only [cleanExpr]
        rw [name]
        rfl
  | scope, .group alts, st => by
    unfold expandExpr
    exact (expandGroup_spec c wf caller depth scope alts st).mono (by simp [cleanExpr])
  | scope, .star x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .plus x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .opt x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .and x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .not x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .capture x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .label l x n, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .discard x, st => by
    unfold expandExpr
    exact (expandExpr_spec c wf caller depth scope x st).mono (by simp [cleanExpr])
  | scope, .lit v w, st => by
    unfold expandExpr
    exact Spec.refl c depth st (by simp [cleanExpr])
  | scope, .charClass w, st => by
    unfold expandExpr
    exact Spec.refl c depth st (by simp [cleanExpr])
  | scope, .any, st => by
    unfold expandExpr
    exact Spec.refl c depth st (by simp [cleanExpr])
  | scope, .predicate b code, st => by
    unfold expandExpr
    exact Spec.refl c depth st (by simp [cleanExpr])

theorem expandArgs_spec (c : Ctx) (wf : WF c) (caller : Caller) (depth : Nat) :
    ∀ (scope : List String) (args : List Expr) (st : State),
      Spec c depth st (expandArgs c caller depth scope args st).2 True
  | scope, [], st => by
    unfold expandArgs
    exact Spec.refl c depth st trivial
  | scope, a :: as, st => by
    unfold expandArgs
    exact ((expandExpr_spec c wf caller depth scope a st).trans
      (expandArgs_spec c wf caller depth scope as _)).mono (fun _ => trivial)

theorem expandItems_spec (c : Ctx) (wf : WF c) (caller : Caller) (depth : Nat) :
    ∀ (scope : List String) (items : List Item) (st : State),
      Spec c depth st (expandItems c caller depth scope items st).2
        (cleanItems (isT c) (expandItems c caller depth scope items st).1 = true)
  | scope, [], st => by
    unfold expandItems
    exact Spec.refl c depth st (by simp [cleanItems])
  | scope, (b, e) :: is, st => by
    unfold expandItems
    exact ((expandExpr_spec c wf caller depth scope e st).trans
      (expandItems_spec c wf caller depth (addBind b scope) is _)).mono (by simp [cleanItems])

theorem expandGroup_spec (c : Ctx) (wf : WF c) (caller : Caller) (depth : Nat) :
    ∀ (scope : List String) (alts : List (List Item)) (st : State),
      Spec c depth st (expandGroup c caller depth scope alts st).2
        (cleanAlts (isT c) (expandGroup c caller depth scope alts st).1 = true)
  | scope, [], st => by
    unfold expandGroup
    exact Spec.refl c depth st (by simp [cleanAlts])
  | scope, items :: alts, st => by
    unfold expandGroup
    exact ((expandItems_spec c wf caller depth scope items st).trans
      (expandGroup_spec c wf caller depth scope alts _)).mono (by simp [cleanAlts])
end

theorem expandAlts_spec (c : Ctx) (wf : WF c) (caller : Caller) (depth : Nat) :
    ∀ (alts : List Alt) (st : State),
      Spec c depth st (expandAlts c caller depth alts st).2
        (∀ a ∈ (expandAlts c caller depth alts st).1, cleanItems (isT c) a.items = true)
  | [], st => by
    unfold expandAlts
    exact Spec.refl c depth st (by simp)
  | a :: as, st => by
    unfold expandAlts
    refine ((expandItems_spec c wf caller depth [] a.items st).trans
      (expandAlts_spec c wf caller depth as _)).mono ?_
    intro h b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact h.2 b hb

theorem expandRules_spec (c : Ctx) (wf : WF c) :
    ∀ (rules : List Rule) (st : State),
      Spec c 0 st (expandRules c rules st).2
        (∀ r ∈ (expandRules c rules st).1, ∀ a ∈ r.alts, cleanItems (isT c) a.items = true)
  | [], st => by
    unfold expandRules
    exact Spec.refl c 0 st (by simp)
  | r :: rs, st => by
    unfold expandRules
    refine ((expandAlts_spec c wf _ 0 r.alts st).trans (expandRules_spec c wf rs _)).mono ?_
    intro h q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact h.2 q hq

theorem expandRules_names (c : Ctx) :
    ∀ (rules : List Rule) (st : State),
      (expandRules c rules st).1.map Rule.name = rules.map Rule.name ∧
      (expandRules c rules st).1.map Rule.templateParams = rules.map Rule.templateParams
  | [], st => by simp [expandRules]
  | r :: rs, st => by
    unfold expandRules
    have ih := expandRules_names c rs (expandAlts c ⟨r.name, lookupLast r.params⟩ 0 r.alts st).2
    simp [ih.1, ih.2]

theorem instantiate_spec (c : Ctx) (wf : WF c) (j : Job) (st : State) :
    Spec c j.depth st (instantiate c j st).2 (CleanRule (isT c) (instantiate c j st).1) ∧
    (instantiate c j st).1.name = j.name := by
  unfold instantiate
  dsimp only
  refine ⟨(expandAlts_spec c wf _ j.depth _ st).mono fun h => ⟨rfl, h⟩, rfl⟩

-- The names of the jobs already taken from the queue, then the queue, are the
-- instance names in the order they were made.
def Queued (P : List String) (st : State) : Prop :=
  st.generated.reverse = P ++ st.pending.map Job.name

theorem drain_spec (c : Ctx) (wf : WF c) {st : State} {outs : List Rule} {fin : State}
    (d : Drain c st outs fin) :
    ∀ P, Fresh c st → Queued P st →
      Fresh c fin ∧ fin.pending = [] ∧ st.errors.length ≤ fin.errors.length ∧
      ∃ Q, fin.generated.reverse = P ++ Q ∧
        (fin.errors.length = st.errors.length →
          outs.map Rule.name = Q ∧ ∀ r ∈ outs, CleanRule (isT c) r) := by
  induction d with
  | done empty =>
    intro P f q
    refine ⟨f, empty, Nat.le_refl _, [], by simpa [Queued, empty] using q, fun _ => ⟨rfl, by simp⟩⟩
  | @reject st j rest outs fin hp _ _ ih =>
    intro P f q
    have f1 : Fresh c (rejectJob j { st with pending := rest }) := f
    have q1 : Queued (P ++ [j.name]) (rejectJob j { st with pending := rest }) := by
      simp only [Queued, hp, List.map_cons] at q
      simp [Queued, rejectJob, addErrors, q]
    obtain ⟨ff, fp, fe, Q, fg, fo⟩ := ih (P ++ [j.name]) f1 q1
    have grow : st.errors.length + 1 ≤ fin.errors.length := by
      simpa [rejectJob, addErrors] using fe
    refine ⟨ff, fp, by omega, j.name :: Q, by simp [fg], fun eq => by omega⟩
  | @expand st j rest outs fin hp _ _ ih =>
    intro P f q
    have s := instantiate_spec c wf j { st with pending := rest }
    obtain ⟨⟨e1, new, p1, g1, _⟩, f1⟩ := s.1
    obtain ⟨f2, clean⟩ := f1 f
    have q1 : Queued (P ++ [j.name]) (instantiate c j { st with pending := rest }).2 := by
      simp only [Queued, hp, List.map_cons] at q
      simp [Queued, p1, g1, q]
    obtain ⟨ff, fp, fe, Q, fg, fo⟩ := ih (P ++ [j.name]) f2 q1
    refine ⟨ff, fp, by simp at e1; omega, j.name :: Q, by simp [fg], fun eq => ?_⟩
    have same : (instantiate c j { st with pending := rest }).2.errors.length = st.errors.length := by
      simp at e1
      omega
    obtain ⟨names, cleans⟩ := fo (by omega)
    refine ⟨by simp [names, s.2], ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact clean same
    · exact cleans r hr

-- Every remaining job is beyond the depth limit: each is rejected.
theorem drain_exists_beyond (c : Ctx) :
    ∀ (n : Nat) (st : State), st.pending.length = n → (∀ j ∈ st.pending, 64 < j.depth) →
      ∃ outs fin, Drain c st outs fin
  | 0, st, len, _ => ⟨[], st, .done (List.eq_nil_of_length_eq_zero len)⟩
  | n + 1, st, len, deep => by
    cases hp : st.pending with
    | nil => simp [hp] at len
    | cons j rest =>
      have past : TemplateQueue.allowed j.depth (argsSize j) = false := by
        have := deep j (by simp [hp])
        simp [TemplateQueue.allowed]
        omega
      obtain ⟨outs, fin, d⟩ := drain_exists_beyond c n (rejectJob j { st with pending := rest })
        (by simp [hp] at len; simp [rejectJob, addErrors, len])
        (by intro k hk; exact deep k (by simp [rejectJob, addErrors] at hk; simp [hp, hk]))
      exact ⟨outs, fin, .reject hp past d⟩

-- A FIFO queue of jobs at depth d followed by jobs at depth d + 1 drains:
-- each job at depth d appends jobs at depth d + 1 only.
theorem drain_exists_layer (c : Ctx) (wf : WF c) (d : Nat) (A B : List Job) (st : State)
    (hp : st.pending = A ++ B) (hA : ∀ j ∈ A, j.depth = d) (hB : ∀ j ∈ B, j.depth = d + 1) :
    ∃ outs fin, Drain c st outs fin := by
  match A with
  | [] =>
    by_cases past : 64 < d + 1
    · exact drain_exists_beyond c _ st rfl (by intro j hj; simp [hp] at hj; rw [hB j hj]; exact past)
    · exact drain_exists_layer c wf (d + 1) B [] st (by simp [hp]) hB (by simp)
  | j :: A' =>
    have hj : j.depth = d := hA j (by simp)
    have hA' : ∀ k ∈ A', k.depth = d := fun k hk => hA k (by simp [hk])
    have hp' : st.pending = j :: (A' ++ B) := by simp [hp]
    cases ha : TemplateQueue.allowed j.depth (argsSize j) with
    | false =>
      obtain ⟨outs, fin, dr⟩ := drain_exists_layer c wf d A' B (rejectJob j { st with pending := A' ++ B })
        (by simp [rejectJob, addErrors]) hA' hB
      exact ⟨outs, fin, .reject hp' ha dr⟩
    | true =>
      obtain ⟨⟨_, new, p1, _, dn⟩, _⟩ := (instantiate_spec c wf j { st with pending := A' ++ B }).1
      obtain ⟨outs, fin, dr⟩ := drain_exists_layer c wf d A' (B ++ new)
        (instantiate c j { st with pending := A' ++ B }).2 (by simp [p1]) hA'
        (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hB k hk
          · rw [dn k hk, hj])
      exact ⟨_, fin, .expand hp' ha dr⟩
termination_by (65 - d, A.length)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp
  · apply Prod.Lex.right
    simp

theorem drain_unique {c : Ctx} {st : State} {o1 : List Rule} {f1 : State}
    (d1 : Drain c st o1 f1) : ∀ {o2 f2}, Drain c st o2 f2 → o1 = o2 ∧ f1 = f2 := by
  induction d1 with
  | done e =>
    intro o2 f2 d2
    cases d2 with
    | done _ => exact ⟨rfl, rfl⟩
    | reject hp _ _ => simp [e] at hp
    | expand hp _ _ => simp [e] at hp
  | reject hp ha _ ih =>
    intro o2 f2 d2
    cases d2 with
    | done e => simp [e] at hp
    | reject hp2 _ d2 =>
      rw [hp] at hp2
      cases hp2
      exact ih d2
    | expand hp2 ha2 _ =>
      rw [hp] at hp2
      cases hp2
      rw [ha] at ha2
      cases ha2
  | expand hp ha _ ih =>
    intro o2 f2 d2
    cases d2 with
    | done e => simp [e] at hp
    | reject hp2 ha2 _ =>
      rw [hp] at hp2
      cases hp2
      rw [ha] at ha2
      cases ha2
    | expand hp2 _ d2 =>
      rw [hp] at hp2
      cases hp2
      obtain ⟨o, f⟩ := ih d2
      exact ⟨by rw [o], f⟩

theorem drainRun_sound (c : Ctx) :
    ∀ (fuel : Nat) (st : State) (outs : List Rule) (fin : State),
      drainRun c fuel st = some (outs, fin) → Drain c st outs fin
  | 0, _, _, _, h => by simp [drainRun] at h
  | fuel + 1, st, outs, fin, h => by
    unfold drainRun at h
    split at h
    · rename_i e
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact .done e
    · rename_i j rest e
      split at h
      · rename_i ha
        cases hr : drainRun c fuel (instantiate c j { st with pending := rest }).2 with
        | none => simp [hr] at h
        | some p =>
          simp [hr] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .expand e ha (drainRun_sound c fuel _ p.1 p.2 hr)
      · rename_i ha
        exact .reject e (by simpa using ha) (drainRun_sound c fuel _ outs fin h)

/-! ## expandOnce, the passes and expandTemplates -/

theorem wf_ctxOf (env : Env) (known : Known) (g : Grammar) : WF (ctxOf env known g) := by
  intro n t h
  have mem := lookupLast_mem h
  simp only [List.mem_map, List.mem_filter] at mem
  obtain ⟨r, ⟨hr, _⟩, eq⟩ := mem
  simp only [Prod.mk.injEq] at eq
  simp only [ctxOf, List.mem_map]
  exact ⟨r, hr, eq.1⟩

theorem fresh_empty (c : Ctx) : Fresh c {} := by
  simp [Fresh]

-- The grammar that expandTemplates accepts: the expanded ordinary rules, then
-- the instances; no template, no template call, no reference to a template;
-- each instance under a new name, defined once.
def Accepted (g g' : Grammar) : Prop :=
  ∃ expanded instances : List Rule,
    g'.rules = expanded ++ instances ∧
    expanded.map Rule.name = (ordinaryOf g).map Rule.name ∧
    (∀ r ∈ g'.rules, CleanRule (fun n => (templatesOf g n).isSome) r) ∧
    (instances.map Rule.name).Nodup ∧
    (∀ r ∈ instances, r.name ∉ g.rules.map Rule.name) ∧
    (∀ r ∈ instances, (g'.rules.map Rule.name).count r.name = 1)

mutual
theorem clean_of_no_call : ∀ e : Expr, callsTemplateExpr e = false → cleanExpr (fun _ => false) e = true
  | .ref _ _ _, _ => by simp [cleanExpr]
  | .template .., h => by simp [callsTemplateExpr] at h
  | .group alts, h => by
    simp only [callsTemplateExpr] at h
    simp only [cleanExpr]
    exact cleanAlts_of_no_call alts h
  | .star x, h | .plus x, h | .opt x, h | .and x, h | .not x, h | .capture x, h | .discard x, h => by
    simp only [callsTemplateExpr] at h
    simp only [cleanExpr]
    exact clean_of_no_call x h
  | .label _ x _, h => by
    simp only [callsTemplateExpr] at h
    simp only [cleanExpr]
    exact clean_of_no_call x h
  | .lit _ _, _ | .charClass _, _ | .any, _ | .predicate _ _, _ => by simp [cleanExpr]

theorem cleanAlts_of_no_call :
    ∀ alts : List (List Item), callsTemplateAlts alts = false → cleanAlts (fun _ => false) alts = true
  | [], _ => by simp [cleanAlts]
  | items :: alts, h => by
    simp only [callsTemplateAlts, Bool.or_eq_false_iff] at h
    simp only [cleanAlts, Bool.and_eq_true]
    exact ⟨cleanItems_of_no_call items h.1, cleanAlts_of_no_call alts h.2⟩

theorem cleanItems_of_no_call :
    ∀ items : List Item, callsTemplateItems items = false → cleanItems (fun _ => false) items = true
  | [], _ => by simp [cleanItems]
  | (_, e) :: items, h => by
    simp only [callsTemplateItems, Bool.or_eq_false_iff] at h
    simp only [cleanItems, Bool.and_eq_true]
    exact ⟨clean_of_no_call e h.1, cleanItems_of_no_call items h.2⟩
end

theorem accepted_plain (g : Grammar) (plain : plainGrammar g = true) : Accepted g g := by
  simp only [plainGrammar, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at plain
  obtain ⟨noTemplate, noCall⟩ := plain
  have none : ∀ n, templatesOf g n = none := by
    intro n
    have empty : g.rules.filter isTemplate = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      simpa using noTemplate r hr
    simp [templatesOf, lookupLast, empty]
  have ordinary : ordinaryOf g = g.rules := by
    rw [ordinaryOf, List.filter_eq_self]
    intro r hr
    simpa using noTemplate r hr
  refine ⟨g.rules, [], by simp, by rw [ordinary], ?_, by simp, by simp, by simp⟩
  intro r hr
  refine ⟨?_, ?_⟩
  · have := noTemplate r hr
    simpa [isTemplate] using this
  · intro a ha
    have calls := noCall r hr
    simp only [callsTemplate, List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at calls
    simp only [none, Option.isSome_none]
    exact cleanItems_of_no_call a.items (calls a ha)

theorem nodup_reverse {l : List String} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp fun ne eq => ne eq.symm

theorem count_one {xs ys : List String} {n : String} (out : n ∉ xs) (nodup : ys.Nodup) (mem : n ∈ ys) :
    (xs ++ ys).count n = 1 := by
  rw [List.count_append, List.count_eq_zero_of_not_mem out, Nat.zero_add]
  induction ys with
  | nil => simp at mem
  | cons y ys ih =>
    rw [List.nodup_cons] at nodup
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [List.count_cons_self, List.count_eq_zero_of_not_mem nodup.1]
    · have ne : y ≠ n := fun eq => nodup.1 (eq ▸ mem)
      rw [List.count_cons_of_ne ne]
      exact ih nodup.2 mem

theorem expandOnce_accepted {env : Env} {known : Known} {g g' : Grammar}
    (h : ExpandOnce env known g (.ok g')) : Accepted g g' := by
  cases h with
  | plain p => exact accepted_plain g p
  | @expanded outs fin _ _ dr empty =>
    have wf := wf_ctxOf env known g
    have s := expandRules_spec (ctxOf env known g) wf (ordinaryOf g) {}
    obtain ⟨⟨_, new, p1, g1, _⟩, f1⟩ := s
    obtain ⟨f2, cleanRules⟩ := f1 (fresh_empty _)
    have q : Queued [] (expandRules (ctxOf env known g) (ordinaryOf g) {}).2 := by
      simp [Queued, p1, g1]
    obtain ⟨ff, _, fe, Q, fg, fo⟩ := drain_spec _ wf dr [] f2 q
    have zero : (expandRules (ctxOf env known g) (ordinaryOf g) {}).2.errors.length = 0 := by
      have h := fe
      rw [empty, List.length_nil] at h
      omega
    obtain ⟨names, cleanOuts⟩ := fo (by rw [empty, zero]; rfl)
    have same : (expandRules (ctxOf env known g) (ordinaryOf g) {}).2.errors.length =
        ({} : State).errors.length := by rw [zero]; rfl
    have nodup : (outs.map Rule.name).Nodup := by
      rw [names]
      have := nodup_reverse ff.1
      rw [fg] at this
      simpa using this
    have outside : ∀ r ∈ outs, r.name ∉ g.rules.map Rule.name := by
      intro r hr
      have inQ : r.name ∈ Q := by
        rw [← names]
        exact List.mem_map_of_mem hr
      have inGen : r.name ∈ fin.generated := by
        rw [← List.mem_reverse, fg]
        simpa using inQ
      exact ff.2.1 r.name inGen
    have shape := expandRules_names (ctxOf env known g) (ordinaryOf g) {}
    refine ⟨(expandRules (ctxOf env known g) (ordinaryOf g) {}).1, outs, rfl, shape.1, ?_, nodup, outside, ?_⟩
    · intro r hr
      simp only [accepted, List.mem_append] at hr
      rcases hr with hr | hr
      · refine ⟨?_, cleanRules same r hr⟩
        have tp : r.templateParams ∈ (ordinaryOf g).map Rule.templateParams := by
          rw [← shape.2]
          exact List.mem_map_of_mem hr
        obtain ⟨o, ho, eq⟩ := List.mem_map.mp tp
        simp only [ordinaryOf, List.mem_filter, isTemplate, Bool.not_eq_true', Bool.not_eq_false'] at ho
        rw [← eq]
        simpa using ho.2
      · exact cleanOuts r hr
    · intro r hr
      simp only [accepted, List.map_append]
      apply count_one
      · rw [shape.1]
        intro mem
        apply outside r hr
        obtain ⟨o, ho, eq⟩ := List.mem_map.mp mem
        exact eq ▸ List.mem_map_of_mem (List.mem_filter.mp ho).1
      · exact nodup
      · exact List.mem_map_of_mem hr

theorem expandOnce_rejected {env : Env} {known : Known} {g : Grammar} {ds : List Diagnostic}
    (h : ExpandOnce env known g (.error ds)) : ds ≠ [] := by
  cases h with
  | directives _ nonempty => exact nonempty
  | rejected _ _ _ nonempty => exact TemplateSubstitution.finishErrors_nonempty _ nonempty

theorem expandOnce_exists (env : Env) (known : Known) (g : Grammar) :
    ∃ r, ExpandOnce env known g r := by
  cases hp : plainGrammar g with
  | true => exact ⟨_, .plain hp⟩
  | false =>
    by_cases hd : directiveErrors g = []
    · have wf := wf_ctxOf env known g
      obtain ⟨⟨_, new, p1, _, dn⟩, _⟩ := expandRules_spec (ctxOf env known g) wf (ordinaryOf g) {}
      obtain ⟨outs, fin, dr⟩ := drain_exists_layer _ wf 1 new []
        (expandRules (ctxOf env known g) (ordinaryOf g) {}).2
        (by simp [p1]) dn (by simp)
      by_cases he : fin.errors = []
      · exact ⟨_, .expanded hp hd dr he⟩
      · exact ⟨_, .rejected hp hd dr he⟩
    · exact ⟨_, .directives hp hd⟩

theorem expandOnce_unique {env : Env} {known : Known} {g : Grammar}
    {r1 r2 : Except (List Diagnostic) Grammar}
    (h1 : ExpandOnce env known g r1) (h2 : ExpandOnce env known g r2) : r1 = r2 := by
  cases h1 <;> cases h2 <;> simp_all
  all_goals
    rename_i d1 _ _ _ _ _ d2 _
    have u := drain_unique d1 d2
    simp_all

theorem go_exists (env : Env) (classify : Grammar → Known) (g : Grammar) :
    ∀ (k : Nat) (known : Known), ∃ r, Go env classify g k known r := by
  intro k
  induction k with
  | zero =>
    intro known
    obtain ⟨r, h⟩ := expandOnce_exists env known g
    cases r with
    | error ds => exact ⟨_, .error h⟩
    | ok g' => exact ⟨_, .stop h (Or.inr rfl)⟩
  | succ k ih =>
    intro known
    obtain ⟨r, h⟩ := expandOnce_exists env known g
    cases r with
    | error ds => exact ⟨_, .error h⟩
    | ok g' =>
      by_cases same : classify g' = known
      · exact ⟨_, .stop h (Or.inl same)⟩
      · obtain ⟨r, next⟩ := ih (classify g')
        exact ⟨r, .next h same next⟩

theorem go_unique {env : Env} {classify : Grammar → Known} {g : Grammar} {k : Nat} {known : Known}
    {r1 : Except (List Diagnostic) Grammar} (h1 : Go env classify g k known r1) :
    ∀ {r2}, Go env classify g k known r2 → r1 = r2 := by
  induction h1 with
  | error e1 =>
    intro r2 h2
    cases h2 with
    | error e2 => exact expandOnce_unique e1 e2
    | stop e2 _ => exact expandOnce_unique e1 e2
    | next e2 _ _ => cases expandOnce_unique e1 e2
  | stop e1 s1 =>
    intro r2 h2
    cases h2 with
    | error e2 => exact expandOnce_unique e1 e2
    | stop e2 _ => exact expandOnce_unique e1 e2
    | next e2 ne _ =>
      cases expandOnce_unique e1 e2
      simp_all
  | next e1 ne1 _ ih =>
    intro r2 h2
    cases h2 with
    | error e2 => cases expandOnce_unique e1 e2
    | stop e2 s2 =>
      cases expandOnce_unique e1 e2
      simp_all
    | next e2 _ n2 =>
      cases expandOnce_unique e1 e2
      exact ih n2

theorem go_pass {env : Env} {classify : Grammar → Known} {g : Grammar} {k : Nat} {known : Known}
    {r : Except (List Diagnostic) Grammar} (h : Go env classify g k known r) :
    ∃ known', ExpandOnce env known' g r := by
  induction h with
  | error e => exact ⟨_, e⟩
  | stop e _ => exact ⟨_, e⟩
  | next _ _ _ ih => exact ih

theorem goRun_sound (env : Env) (classify : Grammar → Known) (fuel : Nat) (g : Grammar) :
    ∀ (k : Nat) (known : Known) (r : Except (List Diagnostic) Grammar),
      goRun env classify fuel g k known = some r → Go env classify g k known r := by
  have once : ∀ known r, expandOnceRun env fuel known g = some r → ExpandOnce env known g r := by
    intro known r h
    unfold expandOnceRun at h
    split at h
    · rename_i p
      simp at h
      subst h
      exact .plain p
    · rename_i p
      have p' : plainGrammar g = false := by simpa using p
      split at h
      · rename_i d
        simp at h
        subst h
        exact .directives p' d
      · rename_i d
        have d' : directiveErrors g = [] := by simpa using d
        cases hr : drainRun (ctxOf env known g) fuel (expandRules (ctxOf env known g) (ordinaryOf g) {}).2 with
        | none => simp [hr] at h
        | some pr =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          have dr := drainRun_sound _ fuel _ pr.1 pr.2 hr
          split at h
          · subst h
            rename_i e
            exact .rejected p' d' dr e
          · subst h
            rename_i e
            exact .expanded p' d' dr (by simpa using e)
  intro k
  induction k with
  | zero =>
    intro known r h
    unfold goRun at h
    split at h
    · simp at h
    · rename_i ds e
      simp at h
      subst h
      exact .error (once known _ e)
    · rename_i g' e
      simp at h
      subst h
      exact .stop (once known _ e) (Or.inr rfl)
  | succ k ih =>
    intro known r h
    unfold goRun at h
    split at h
    · simp at h
    · rename_i ds e
      simp at h
      subst h
      exact .error (once known _ e)
    · rename_i g' e
      simp only at h
      split at h
      · rename_i same
        simp at h
        subst h
        exact .stop (once known _ e) (Or.inl same)
      · rename_i same
        exact .next (once known _ e) same (ih _ _ h)

theorem expandTemplatesRun_sound (env : Env) (classify : Grammar → Known) (fuel : Nat) (g : Grammar)
    (r : Except (List Diagnostic) Grammar) (h : expandTemplatesRun env classify fuel g = some r) :
    ExpandTemplates env classify g r := by
  unfold expandTemplatesRun at h
  split at h
  · rename_i p
    simp at h
    subst h
    exact .plain p
  · rename_i p
    exact .passes (by simpa using p) (goRun_sound env classify fuel g 8 [] r h)

/-- The whole theorem about `expandTemplates`. Its expansion ends with exactly
one result; a rejection carries at least one diagnostic and, being `Left`, no
grammar; an accepted grammar is the expanded ordinary rules followed by the
instances, with no template, no template call and no reference to a template,
and each instance is defined exactly once under a name that no rule of the
input has. -/
theorem expandTemplates_whole (env : Env) (classify : Grammar → Known) (g : Grammar) :
    (∃ r, ExpandTemplates env classify g r) ∧
    (∀ r1 r2, ExpandTemplates env classify g r1 → ExpandTemplates env classify g r2 → r1 = r2) ∧
    (∀ ds, ExpandTemplates env classify g (.error ds) → ds ≠ []) ∧
    (∀ g', ExpandTemplates env classify g (.ok g') → Accepted g g') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hp : plainGrammar g with
    | true => exact ⟨_, .plain hp⟩
    | false =>
      obtain ⟨r, h⟩ := go_exists env classify g 8 []
      exact ⟨r, .passes hp h⟩
  · intro r1 r2 h1 h2
    cases h1 with
    | plain p1 =>
      cases h2 with
      | plain _ => rfl
      | passes p2 _ => simp [p1] at p2
    | passes p1 g1 =>
      cases h2 with
      | plain p2 => simp [p1] at p2
      | passes _ g2 => exact go_unique g1 g2
  · intro ds h
    cases h with
    | passes _ go =>
      obtain ⟨_, e⟩ := go_pass go
      exact expandOnce_rejected e
  · intro g' h
    cases h with
    | plain p => exact accepted_plain g p
    | passes _ go =>
      obtain ⟨_, e⟩ := go_pass go
      exact expandOnce_accepted e

end PegHs.TemplateExpansionWhole

#print axioms PegHs.TemplateExpansionWhole.expandTemplates_whole
#print axioms PegHs.TemplateExpansionWhole.expandTemplatesRun_sound
