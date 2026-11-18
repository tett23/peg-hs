import LabelsBridge

/-!
The simulation of the label check (`knownStrings`, `simExpr`, `simSeq`,
`choice`, `star`, `knownFails`) and the comparison of later alternatives
(`compareWith`, `laterCheck`): the translated functions of
Peg.Grammar.Labels (LabelsTranslated) against LabelCheckModel, on embedded
values, at every fuel from some bound on.
-/

set_option linter.unusedSimpArgs false

namespace PegHs.LabelsBridge

open PegHs.LabelCheck

/-! ## Known prefixes -/

theorem literalsOnly_e (e : Expr) : LabelsTranslated.knownStrings.literalsOnly_831 (eExpr e) = literalsOnly e := by
  cases e <;> simp [LabelsTranslated.knownStrings.literalsOnly_831, literalsOnly, eExpr]

theorem sequence_eq : ∀ (xs : List (List String)), HsList.sequence xs = sequenceL xs
  | [] => rfl
  | x :: xs => by simp [HsList.sequence, sequenceL, sequence_eq xs]

theorem sequenceLiterals_e (is : List Item) :
    LabelsTranslated.knownStrings.sequenceLiterals_830 (eItems is) = sequenceLiterals is := by
  simp only [LabelsTranslated.knownStrings.sequenceLiterals_830, sequenceLiterals, HsMaybe.fmap]
  have : HsMaybe.mapM (fun i => LabelsTranslated.knownStrings.literalsOnly_831 (LabelsTranslated.Item.itemExpr i))
      (eItems is) = is.mapM (fun i => literalsOnly (itemExpr i)) := by
    rw [eItems_map]
    have := mapM_e (fun i => LabelsTranslated.knownStrings.literalsOnly_831 (LabelsTranslated.Item.itemExpr i))
      (fun i => literalsOnly (itemExpr i)) eItem id is
      (fun i _ => by simp [eItem, LabelsTranslated.Item.itemExpr, literalsOnly_e, itemExpr])
    simpa using this
  rw [this]
  cases is.mapM (fun i => literalsOnly (itemExpr i)) <;> simp [sequence_eq, HsText.concat]

theorem literals_e {tc : LabelsTranslated.Ctx} {mc : Ctx} (h : CtxCorr tc mc) :
    (e : Expr) → LabelsTranslated.knownStrings.literals_823 tc (eExpr e) = literals mc e
  | .lit t w => by simp [eExpr, LabelsTranslated.knownStrings.literals_823, literals]
  | .capture x => by simp only [eExpr]; rw [LabelsTranslated.knownStrings.literals_823, literals, literals_e h x]
  | .label l x n => by simp only [eExpr]; rw [LabelsTranslated.knownStrings.literals_823, literals, literals_e h x]
  | .discard x => by simp only [eExpr]; rw [LabelsTranslated.knownStrings.literals_823, literals, literals_e h x]
  | .ref l n args => by
    cases args with
    | cons a as => simp [eExpr, LabelsTranslated.knownStrings.literals_823, literals]
    | nil =>
      simp only [eExpr, List.map_nil]
      rw [LabelsTranslated.knownStrings.literals_823, literals]
      have hr := h.rules n
      revert hr
      cases HsMap.lookup n tc.ctxRules with
      | none =>
        cases findLast mc.rules n with
        | none => intro _; simp
        | some _ => intro hr; exact hr.elim
      | some tr =>
        cases findLast mc.rules n with
        | none => intro hr; exact hr.elim
        | some mr =>
        intro hr
        simp only [RuleOpt] at hr
        simp only [HsBase.not, HsList.null]
        have hlen : tr.ruleAlts.isEmpty = mr.alts.isEmpty := by
          have := congrArg List.length hr.items
          simp [eAlts_map] at this
          cases h1 : tr.ruleAlts <;> cases h2 : mr.alts <;> simp_all
        have hmap : HsMaybe.mapM (fun a => LabelsTranslated.knownStrings.sequenceLiterals_830
            (LabelsTranslated.Alt.altItems a)) tr.ruleAlts = mr.alts.mapM (fun a => sequenceLiterals a.items) := by
          rw [mapM_map (fun is => LabelsTranslated.knownStrings.sequenceLiterals_830 is), hr.items, eAlts_map,
            List.map_map]
          have := mapM_e (fun is => LabelsTranslated.knownStrings.sequenceLiterals_830 is)
            (fun a => sequenceLiterals a.items) (fun a => eItems a.items) id mr.alts
            (fun a _ => by simp [sequenceLiterals_e])
          simpa [Function.comp_def] using this
        by_cases he : mr.alts.isEmpty = true
        · simp [hlen, he]
        · have he' : mr.alts.isEmpty = false := by simpa using he
          simp only [hlen, he', Bool.not_false, ↓reduceIte, Bool.false_eq_true, HsMaybe.fmap, hmap]
          cases mr.alts.mapM (fun a => sequenceLiterals a.items) <;> simp [HsList.concat]
  | .group .. | .cls .. | .any | .star _ | .plus _ | .opt _ | .and _ | .not _ | .pred .. | .template .. => by
    simp [eExpr, LabelsTranslated.knownStrings.literals_823, literals]

theorem knownGo_e {tc : LabelsTranslated.Ctx} {mc : Ctx} (h : CtxCorr tc mc) : ∀ (items : List Item),
    LabelsTranslated.knownStrings.go_819 tc (eItems items) = (knownGo mc items).map String.ofList
  | [] => by simp [eItems, LabelsTranslated.knownStrings.go_819, knownGo]
  | (l, b, e) :: rest => by
    simp only [eItems]
    rw [LabelsTranslated.knownStrings.go_819, knownGo]
    simp only [LabelsTranslated.Item.itemExpr, literals_e h, itemExpr]
    cases literals mc e with
    | none => simp
    | some ts =>
      simp only [HsList.take, HsList.concatMap, HsInt.ge, HsText.length, LabelsTranslated.maxKnown, maxKnown,
        knownGo_e h rest, List.map_take]
      congr 1
      rw [List.map_flatMap]
      congr 1
      funext t
      by_cases ht : 4 ≤ t.length
      · have ht' : (4 : Int) ≤ (t.toList.length : Int) := by rw [String.length_toList]; omega
        simp [ht, ht', HsText.take, HsText.append, String.toList_ofList]
      · have ht' : ¬ ((4 : Int) ≤ (t.toList.length : Int)) := by rw [String.length_toList]; omega
        simp [ht, ht', HsText.take, HsText.append, String.toList_ofList, List.map_map, Function.comp_def,
          List.flatMap_map, flatMap_single]

theorem knownStrings_e {tc : LabelsTranslated.Ctx} {mc : Ctx} (h : CtxCorr tc mc) (items : List Item) :
    LabelsTranslated.knownStrings tc (eItems items) = (knownStrings mc items).map String.ofList := by
  simp only [LabelsTranslated.knownStrings, knownStrings, knownGo_e h, HsBase.not, HsText.null]
  induction knownGo mc items with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.filter_cons, String.toList_ofList, ih]
    cases t <;> simp


/-! ## The outcomes of the simulation -/

theorem eSim_inj {a b : Sim} (h : eSim a = eSim b) : a = b := by
  cases a <;> cases b <;> simp [eSim] at h ⊢
  exact String.ofList_injective h

theorem sim_beq_e (a b : Sim) : (eSim a == eSim b) = decide (a = b) := by
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  cases a <;> cases b <;>
    simp [eSim, BEq.beq, LabelsTranslated.instBEqSim.beq] <;>
    (try exact ⟨fun h => String.ofList_injective h, fun h => h ▸ rfl⟩)

theorem simElem_e (r : Sim) (acc : List Sim) : HsList.elem (eSim r) (acc.map eSim) = acc.contains r := by
  induction acc with
  | nil => rfl
  | cons a as ih =>
    simp only [HsList.elem, List.map_cons, List.any_cons, List.contains_cons] at ih ⊢
    rw [ih, sim_beq_e a r]
    by_cases hra : a = r
    · subst hra; simp
    · have : r ≠ a := fun e => hra e.symm
      simp [hra, this]

theorem simFoldr_e (rs : List Sim) :
    HsList.foldr (fun r acc => if HsList.elem r acc then acc else r :: acc) [] (rs.map eSim) =
      (rs.foldr (fun r acc => if acc.contains r then acc else r :: acc) []).map eSim := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [HsList.foldr, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, simElem_e]
    split <;> simp

theorem capSim_e (rs : List Sim) : LabelsTranslated.capSim (rs.map eSim) = (capSim rs).map eSim := by
  simp only [LabelsTranslated.capSim, capSim, simFoldr_e, HsInt.gt, HsList.length, List.length_map]
  by_cases h : (rs.foldr (fun r acc => if acc.contains r then acc else r :: acc) []).length > 16
  · have h' : ((rs.foldr (fun r acc => if acc.contains r then acc else r :: acc) []).length : Int) > 16 := by
      omega
    simp only [Int.ofNat_eq_natCast, h', decide_true, ↓reduceIte, h]
    rfl
  · have h' : ¬ (((rs.foldr (fun r acc => if acc.contains r then acc else r :: acc) []).length : Int) > 16) := by
      omega
    simp only [Int.ofNat_eq_natCast, h', decide_false, Bool.false_eq_true, ↓reduceIte, h]

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.flatMap_cons, h x (by simp), flatMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem isOk_e (r : Sim) : LabelsTranslated.simExpr.isOk_895 (eSim r) = isOk r := by
  cases r <;> rfl

theorem sim_eq_fail (r : Sim) : HsBase.eq (eSim r) LabelsTranslated.Sim.SFail = (r == .fail) := by
  have := sim_beq_e r .fail
  rw [show LabelsTranslated.Sim.SFail = eSim .fail from rfl, HsBase.eq, this]
  cases r <;> simp

theorem sim_ne_fail (r : Sim) : HsBase.ne (eSim r) LabelsTranslated.Sim.SFail = (r != .fail) := by
  have := sim_eq_fail r
  simp only [HsBase.eq] at this
  simp only [HsBase.ne, this]
  cases r <;> rfl

theorem one_e (p : HsChar → Bool) (q : Char → Bool) (hpq : ∀ c, p (HsChar.ofChar c) = q c) (t : List Char) :
    LabelsTranslated.simExpr.one_892 (String.ofList t) p = (one q t).map eSim := by
  cases t with
  | nil => simp [LabelsTranslated.simExpr.one_892, one, uncons_toList, String.toList_ofList, eSim]
  | cons c cs =>
    simp only [LabelsTranslated.simExpr.one_892, one, uncons_toList, String.toList_ofList, hpq]
    split <;> simp [eSim]


theorem allFail_e (rs : List Sim) :
    HsList.all (fun r => HsBase.eq r LabelsTranslated.Sim.SFail) (rs.map eSim) = rs.all (· == .fail) := by
  simp [HsList.all, List.all_map, Function.comp_def, sim_eq_fail]

theorem allOk_e (rs : List Sim) :
    HsList.all (fun r => LabelsTranslated.simExpr.isOk_895 r) (rs.map eSim) = rs.all isOk := by
  simp [HsList.all, List.all_map, Function.comp_def, isOk_e]

theorem notElemFail_e (rs : List Sim) :
    HsList.notElem LabelsTranslated.Sim.SFail (rs.map eSim) = !rs.contains .fail := by
  simp only [HsList.notElem]
  congr 1
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.any_cons, ih, List.contains_cons]
    rw [show LabelsTranslated.Sim.SFail = eSim .fail from rfl, sim_beq_e]
    cases r <;> simp

theorem filterFail_e (rs : List Sim) :
    List.filter (fun r => HsBase.ne r LabelsTranslated.Sim.SFail) (rs.map eSim) = (rs.filter (· != .fail)).map eSim := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro r _
  simp [Function.comp_def, sim_ne_fail]

theorem inClass_e (rs : List (HChar × HChar)) (c : Char) :
    HsList.any (fun p => match p with | (a, b) => HsBase.and (HsChar.le a (HsChar.ofChar c)) (HsChar.le (HsChar.ofChar c) b))
      (rs.map eCharPair) = inClass rs c := by
  simp only [HsList.any, inClass, List.any_map, Function.comp_def, eCharPair, eChar, HsBase.and, HsChar.le,
    HsChar.ofChar]
  rfl

theorem simLit_e (l : String) (t : List Char) :
    (let n := HsInt.min (HsText.length l) (HsText.length (String.ofList t))
     if HsText.null l = true then [LabelsTranslated.Sim.SOk (String.ofList t)]
     else if HsBase.ne (HsText.take n l) (HsText.take n (String.ofList t)) = true then [LabelsTranslated.Sim.SFail]
     else if HsInt.le (HsText.length l) (HsText.length (String.ofList t)) = true then
       [LabelsTranslated.Sim.SOk (HsText.drop (HsText.length l) (String.ofList t))]
     else [LabelsTranslated.Sim.SUnknown]) =
    (let l' := l.toList
     let n := min l'.length t.length
     if l'.isEmpty then [Sim.ok t]
     else if l'.take n != t.take n then [Sim.fail]
     else if l'.length ≤ t.length then [Sim.ok (t.drop l'.length)]
     else [Sim.unknown]).map eSim := by
  simp only [HsText.length, String.toList_ofList, HsInt.min, HsText.null, HsText.take, HsText.drop, HsInt.le,
    HsBase.ne]
  have hmin : (if (l.toList.length : Int) ≤ (t.length : Int) then (l.toList.length : Int) else (t.length : Int)) =
      ((min l.toList.length t.length : Nat) : Int) := by split <;> omega
  simp only [Int.ofNat_eq_natCast, hmin, Int.toNat_natCast]
  by_cases h1 : l.toList.isEmpty = true
  · simp [h1, eSim]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    have hne : (String.ofList (l.toList.take (min l.toList.length t.length)) ==
        String.ofList (t.take (min l.toList.length t.length))) =
        (l.toList.take (min l.toList.length t.length) == t.take (min l.toList.length t.length)) := by
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq]
      exact ⟨fun h => String.ofList_injective h, fun h => h ▸ rfl⟩
    rw [hne]
    by_cases h2 : (l.toList.take (min l.toList.length t.length) == t.take (min l.toList.length t.length)) = true
    · have h2' : (l.toList.take (min l.toList.length t.length) != t.take (min l.toList.length t.length)) = false := by
        simp [bne, h2]
      simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2']
      by_cases h3 : l.toList.length ≤ t.length
      · have h3' : (l.toList.length : Int) ≤ (t.length : Int) := by omega
        simp [h3, h3', eSim, String.toList_ofList]
      · have h3' : ¬ ((l.toList.length : Int) ≤ (t.length : Int)) := by omega
        simp [h3, h3', eSim]
    · have h2' : (l.toList.take (min l.toList.length t.length) != t.take (min l.toList.length t.length)) = true := by
        simp [bne] at h2 ⊢; exact h2
      simp only [h2', ↓reduceIte]
      have : (!(l.toList.take (min l.toList.length t.length) == t.take (min l.toList.length t.length))) = true := by
        simpa [bne] using h2'
      simp [this, eSim]

variable {tc : LabelsTranslated.Ctx} {mc : Ctx} {E : Nat}

mutual
theorem simExpr_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (d : Nat) (t : List Char) : (e : Expr) → Eventually (fun f =>
      LabelsTranslated.simExpr f tc d (String.ofList t) (eExpr e) = (simExpr mc d t e).map eSim)
  | .lit l w => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact simLit_e l t
  | .cls rs w => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact one_e _ _ (inClass_e rs) t
  | .any => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact one_e _ _ (fun _ => rfl) t
  | .ref l n args => by
    by_cases hd : d > 0
    · have hall : Eventually (fun f => ∀ alts, expandCall mc n args = some alts →
          LabelsTranslated.simExpr.choice_898 f tc (String.ofList t) ((d - 1 : Nat) : Int) (eAlts alts) =
            (choice mc (d - 1) t alts).map eSim) := by
        cases hx : expandCall mc n args with
        | none => exact Eventually.of (fun _ alts h => by cases h)
        | some alts =>
          exact (choice_ev h hE (d - 1) t alts).mono (fun f hf alts' he => by cases he; exact hf)
      obtain ⟨N, hN⟩ := hall
      refine ⟨max N E + 1, fun f hf => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      rw [LabelsTranslated.simExpr, simExpr]
      simp only [eExpr, HsInt.gt, hd, ↓reduceDIte]
      have hd' : decide ((d : Int) > 0) = true := by simp; omega
      simp only [hd', ↓reduceIte, hE m (by omega) n args]
      cases hx : expandCall mc n args with
      | none => simp [eSim]
      | some alts =>
        simp only [Option.map_some, HsInt.sub, show (d : Int) - 1 = ((d - 1 : Nat) : Int) by omega]
        exact hN m (by omega) alts hx
    · refine ⟨1, fun f hf => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      rw [LabelsTranslated.simExpr, simExpr]
      have hd' : decide ((d : Int) > 0) = false := by simp; omega
      simp [eExpr, HsInt.gt, hd, hd', eSim]
  | .group alts => by
    obtain ⟨N, hN⟩ := choice_ev h hE d t alts
    refine ⟨N + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact hN m (by omega)
  | .star x => by
    obtain ⟨N, hN⟩ := star_ev h hE d x t
    refine ⟨N + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact hN m (by omega)
  | .plus x => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    have hres : Eventually (fun f => ∀ r ∈ simExpr mc d t x, ∀ t', r = .ok t' →
        LabelsTranslated.simExpr.star_905 f tc d (eExpr x) (String.ofList t') = (star mc d x t').map eSim) :=
      Eventually.forall_mem _ (fun r _ => match r with
        | .ok t' => (star_ev h hE d x t').mono (fun f hf t'' he => by cases he; exact hf)
        | .fail => Eventually.of (fun _ _ he => by cases he)
        | .unknown => Eventually.of (fun _ _ he => by cases he))
    obtain ⟨N2, h2⟩ := hres
    refine ⟨max N1 N2 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr, h1 m (by omega), HsList.concatMap, List.flatMap_map]
    rw [← capSim_e, List.map_flatMap]
    congr 1
    apply flatMap_congr_mem
    intro r hr
    cases r with
    | ok t' => simp only [eSim]; exact h2 m (by omega) _ hr t' rfl
    | fail => rfl
    | unknown => rfl
  | .opt x => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    refine ⟨N1 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr, h1 m (by omega), HsList.concatMap, List.flatMap_map]
    rw [← capSim_e, List.map_flatMap]
    congr 1
    apply flatMap_congr_mem
    intro r _
    cases r <;> rfl
  | .and x => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    refine ⟨N1 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr, h1 m (by omega), allFail_e, allOk_e]
    split <;> (try split) <;> rfl
  | .not x => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    refine ⟨N1 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr, h1 m (by omega), allFail_e, allOk_e]
    split <;> (try split) <;> rfl
  | .capture x | .discard x => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    refine ⟨N1 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr] <;> simp only [eExpr] <;> exact h1 m (by omega)
  | .label l x name => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    refine ⟨N1 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr]
    exact h1 m (by omega)
  | .pred b c => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    simp only [eExpr, constantPred_e]
    cases constantPred b c with
    | none => rfl
    | some v => cases v <;> rfl
  | .template .. => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr, simExpr]
    rfl
termination_by e => (d, sizeOf e, t.length, 0)

theorem simSeq_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (d : Nat) (t : List Char) : (is : List Item) → Eventually (fun f =>
      LabelsTranslated.simSeq f tc d (String.ofList t) ((eItems is).map LabelsTranslated.Item.itemExpr) =
        (simSeq mc d t is).map eSim)
  | [] => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simSeq.eq_def, simSeq]
    rfl
  | (l, b, e) :: es => by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t e
    have hres : Eventually (fun f => ∀ r ∈ simExpr mc d t e, ∀ t', r = .ok t' →
        LabelsTranslated.simSeq f tc d (String.ofList t') ((eItems es).map LabelsTranslated.Item.itemExpr) =
          (simSeq mc d t' es).map eSim) :=
      Eventually.forall_mem _ (fun r _ => match r with
        | .ok t' => (simSeq_ev h hE d t' es).mono (fun f hf t'' he => by cases he; exact hf)
        | .fail => Eventually.of (fun _ _ he => by cases he)
        | .unknown => Eventually.of (fun _ _ he => by cases he))
    obtain ⟨N2, h2⟩ := hres
    refine ⟨max N1 (N2 + 1) + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simSeq.eq_def, simSeq]
    simp only [eItems, List.map_cons, LabelsTranslated.Item.itemExpr, h1 m (by omega), HsList.concatMap,
      List.flatMap_map]
    rw [← capSim_e, List.map_flatMap]
    congr 1
    apply flatMap_congr_mem
    intro r hr
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [LabelsTranslated.simSeq.next__855.eq_def]
    cases r with
    | ok t' => simp only [eSim]; exact h2 k (by omega) _ hr t' rfl
    | fail => rfl
    | unknown => rfl
termination_by is => (d, sizeOf is, t.length, 0)

theorem choice_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (d : Nat) (t : List Char) : (alts : List (List Item)) → Eventually (fun f =>
      LabelsTranslated.simExpr.choice_898 f tc (String.ofList t) d (eAlts alts) = (choice mc d t alts).map eSim)
  | [] => by
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr.choice_898.eq_def, choice]
    rfl
  | alt :: rest => by
    obtain ⟨N1, h1⟩ := simSeq_ev h hE d t alt
    obtain ⟨N2, h2⟩ := choice_ev h hE d t rest
    refine ⟨max N1 N2 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr.choice_898.eq_def, choice]
    simp only [eAlts, h1 m (by omega), h2 m (by omega), allFail_e, notElemFail_e]
    split
    · rfl
    · split
      · rfl
      · rw [filterFail_e, HsList.append, ← List.map_append, capSim_e]
termination_by alts => (d, sizeOf alts, t.length, 0)

theorem star_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (d : Nat) (x : Expr) (t : List Char) : Eventually (fun f =>
      LabelsTranslated.simExpr.star_905 f tc d (eExpr x) (String.ofList t) = (star mc d x t).map eSim) := by
    obtain ⟨N1, h1⟩ := simExpr_ev h hE d t x
    have hres : Eventually (fun f => ∀ r ∈ simExpr mc d t x, ∀ t'', r = .ok t'' → t''.length < t.length →
        LabelsTranslated.simExpr.star_905 f tc d (eExpr x) (String.ofList t'') = (star mc d x t'').map eSim) :=
      Eventually.forall_mem _ (fun r _ => match r with
        | .ok t'' => if hl : t''.length < t.length then
            (star_ev h hE d x t'').mono (fun f hf t3 he _ => by cases he; exact hf)
          else Eventually.of (fun _ t3 he hl' => by cases he; exact absurd hl' hl)
        | .fail => Eventually.of (fun _ _ he => by cases he)
        | .unknown => Eventually.of (fun _ _ he => by cases he))
    obtain ⟨N2, h2⟩ := hres
    refine ⟨max N1 N2 + 1, fun f hf => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [LabelsTranslated.simExpr.star_905.eq_def, star]
    simp only [h1 m (by omega), HsList.concatMap, List.flatMap_map]
    rw [← capSim_e, List.map_flatMap]
    congr 1
    apply flatMap_congr_mem
    intro r hr
    cases r with
    | ok t'' =>
      simp only [eSim, HsInt.lt, HsText.length, String.toList_ofList]
      by_cases hl : t''.length < t.length
      · have hl' : decide (Int.ofNat t''.length < Int.ofNat t.length) = true := by simp; omega
        simp only [hl', ↓reduceIte, hl, ↓reduceDIte]
        exact h2 m (by omega) _ hr t'' rfl hl
      · have hl' : decide (Int.ofNat t''.length < Int.ofNat t.length) = false := by simp; omega
        simp only [hl', Bool.false_eq_true, ↓reduceIte, hl, ↓reduceDIte]
        rfl
    | fail => rfl
    | unknown => rfl
termination_by (d, sizeOf x, t.length, 1)
end


/-! ## Later alternatives -/

theorem all_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x (by simp), all_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem expandDepth_e : LabelsTranslated.expandDepth = ((expandDepth : Nat) : Int) := rfl

theorem knownFails_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (matched rest : List Item) :
    Eventually (fun f => LabelsTranslated.knownFails f tc (eItems matched) (eItems rest) = knownFails mc matched rest) := by
  have hall : Eventually (fun f => ∀ t ∈ knownStrings mc matched,
      LabelsTranslated.simSeq f tc expandDepth (String.ofList t) ((eItems rest).map LabelsTranslated.Item.itemExpr) =
        (simSeq mc expandDepth t rest).map eSim) :=
    Eventually.forall_mem _ (fun t _ => simSeq_ev h hE expandDepth t rest)
  refine hall.mono (fun f hf => ?_)
  have key : HsList.all (fun t => HsList.all (fun r => HsBase.eq r LabelsTranslated.Sim.SFail)
      (LabelsTranslated.simSeq f tc LabelsTranslated.expandDepth t
        (List.map LabelsTranslated.Item.itemExpr (eItems rest)))) ((knownStrings mc matched).map String.ofList) =
      (knownStrings mc matched).all (fun t => (simSeq mc expandDepth t rest).all (· == .fail)) := by
    simp only [HsList.all]
    rw [List.all_map]
    apply all_congr_mem
    intro t ht
    simp only [Function.comp_def]
    rw [expandDepth_e, hf t ht]
    exact allFail_e _
  simp only [LabelsTranslated.knownFails, knownFails, knownStrings_e h]
  revert key
  cases knownStrings mc matched with
  | nil => intro _; rfl
  | cons t ts => intro key; exact key

/-- `compareWith` of `failed`, in the model. -/
def mCompareWith (ctx : Ctx) (matched : List Item) (k : CharSet) (al : Loc) (a' : List Item) : Verdict :=
  let m := commonPrefix matched a'
  let rest' := a'.drop m
  if (possible (seqAbs ctx.pass rest')).meets (beforeItems ctx (matched.drop m) k) &&
      !knownFails ctx (matched.drop m) rest' then
    Verdict.mayReject ("the alternative at " ++ showLoc al ++ " can match")
  else .safe

/-- `laterCheck` of `failed`, in the model. -/
def mLaterCheck (ctx : Ctx) (items : List Item) (j : Nat) (matched : List Item) (k : CharSet)
    (p : Nat × Loc × List Item) : Verdict :=
  if commonPrefix items p.2.2 > j then Verdict.safe
  else ((expansions ctx expandDepth matched p.2.2).map (mCompareWith ctx matched k p.2.1)).foldr andAlso .safe

theorem andAlso_e (a b : Verdict) : LabelsTranslated.andAlso (eVerdict a) (eVerdict b) = eVerdict (andAlso a b) := by
  cases a <;> cases b <;> rfl

theorem foldrAndAlso_e (vs : List Verdict) :
    HsList.foldr (fun a b => LabelsTranslated.andAlso a b) LabelsTranslated.Verdict.Safe (vs.map eVerdict) =
      eVerdict (vs.foldr andAlso .safe) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [HsList.foldr] at ih ⊢
    simp only [List.map_cons, List.foldr_cons, ih, andAlso_e]

theorem compareWith_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (matched : List Item) (k : CharSet) (a' : List Item) :
    Eventually (fun f => ∀ al, LabelsTranslated.failed.compareWith_544 f tc (eItems matched) (eCS k) (eLoc al) (eItems a') =
      eVerdict (mCompareWith mc matched k al a')) := by
  refine (knownFails_ev h hE (matched.drop (commonPrefix matched a')) (a'.drop (commonPrefix matched a'))).mono
    (fun f hf al => ?_)
  simp only [LabelsTranslated.failed.compareWith_544, mCompareWith, commonPrefix_e, eItems_drop, kAt_e h,
    seqAbs_e h.pass, possible_e, meets_e, HsBase.and, HsBase.not, hf]
  split <;> simp [eVerdict, HsText.append, showLoc_e, String.append_assoc]

theorem laterCheck_ev (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (items : List Item) (j : Nat) (matched : List Item) (k : CharSet) (p : Nat × Loc × List Item) :
    Eventually (fun f => LabelsTranslated.failed.laterCheck_541 f tc (eItems items) j (eItems matched) (eCS k)
      (eLoc p.2.1, eItems p.2.2) = eVerdict (mLaterCheck mc items j matched k p)) := by
  have hall : Eventually (fun f => ∀ a' ∈ expansions mc expandDepth matched p.2.2, ∀ al,
      LabelsTranslated.failed.compareWith_544 f tc (eItems matched) (eCS k) (eLoc al) (eItems a') =
        eVerdict (mCompareWith mc matched k al a')) :=
    Eventually.forall_mem _ (fun a' _ => compareWith_ev h hE matched k a')
  obtain ⟨N, hN⟩ := hall
  refine ⟨max N E, fun f hf => ?_⟩
  simp only [LabelsTranslated.failed.laterCheck_541, mLaterCheck, commonPrefix_e, HsInt.gt]
  by_cases hc : commonPrefix items p.2.2 > j
  · have hc' : decide ((commonPrefix items p.2.2 : Int) > (j : Int)) = true := by simp; omega
    simp [hc, hc', eVerdict]
  · have hc' : decide ((commonPrefix items p.2.2 : Int) > (j : Int)) = false := by simp; omega
    simp only [hc', Bool.false_eq_true, ↓reduceIte, hc]
    rw [expandDepth_e, expansions_e (hE f (by omega)), ← foldrAndAlso_e]
    congr 1
    simp only [HsList.concatMap, List.flatMap_map, List.map_map, flatMap_single]
    apply List.map_congr_left
    intro a' ha'
    exact hN f (by omega) a' ha' p.2.1

end PegHs.LabelsBridge
