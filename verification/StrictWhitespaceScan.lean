import StrictWhitespace

namespace PegHs.MetaExecution
open EnvironmentEval
set_option maxRecDepth 8192

private theorem comment_rest_lt (cs : List Char) :
    (cs.dropWhile (· != '\n')).length < cs.length + 1 := by
  have parts := congrArg List.length (List.takeWhile_append_dropWhile (p := (· != '\n')) (l := cs))
  simp only [List.length_append] at parts
  omega

def afterWhitespace : List Char → List Char
  | [] => []
  | c :: cs =>
    if GhcPredicates.space c then afterWhitespace cs
    else if c = '#' then afterWhitespace (cs.dropWhile (· != '\n'))
    else c :: cs
termination_by xs => xs.length
decreasing_by
  all_goals simp only [List.length_cons]
  · exact Nat.lt_succ_self _
  · exact comment_rest_lt cs

private abbrev wsItem : Body := .alt (.call 7 5) (.call 8 6)

private theorem ws_loop (input pre xs : List Char) (env : Env)
    (atCursor : input = pre ++ xs) (zero : env.resultDepth = 0) :
    Derives (context false input) (.starLoop wsItem) xs.length env
      (.ok (afterWhitespace xs).length env) := by
  induction xs using (measure (List.length (α := Char))).wf.induction generalizing pre with
  | h xs ih =>
    let ctx := context false input
    have reset : {env with resultDepth := 0} = env := by cases env; simp_all
    have stop (h : Derives ctx translatedStrictWs xs.length env (.ok xs.length {env with resultDepth := 0})) :
        Derives ctx (.starLoop wsItem) xs.length env (.ok xs.length env) := by
      cases h with | star child => simpa only [reset] using child
    cases xs with
    | nil =>
      simpa only [afterWhitespace] using stop (invariant1_strict_ws_eof input env)
    | cons c cs =>
      have entered7 : ctx.hooks.enterCall 7 env = some env := rfl
      have entered8 : ctx.hooks.enterCall 8 env = some env := rfl
      have space := invariant1_strict_space_char pre c cs env
      rw [← atCursor] at space
      cases isSpace : GhcPredicates.space c with
      | true =>
        rw [isSpace] at space
        let bound := (({env with resultDepth := 0} : Env).put "c" [c]).putDepth "c" 0
        have parsed : Derives ctx (ctx.rules 5) (c :: cs).length env (.ok cs.length bound) :=
          invariant1_runFuel_sound space
        have call : Derives ctx (.call 7 5) (c :: cs).length env (.ok cs.length {env with resultDepth := 0}) :=
          .call entered7 parsed
        rw [reset] at call
        have next := ih cs (Nat.lt_succ_self _) (pre ++ [c]) (by simpa using atCursor)
        rw [afterWhitespace]; simp only [isSpace, ite_true]
        apply Derives.loopMore (.altLeft call (by intro h; cases h)) (Nat.lt_succ_self _)
        simpa using next
      | false =>
        by_cases hash : c = '#'
        · subst c
          let rest := cs.dropWhile (· != '\n')
          have progress : rest.length < ('#' :: cs).length := by
            exact comment_rest_lt cs
          rw [isSpace] at space
          have rejected : Derives ctx (ctx.rules 5) ('#' :: cs).length env .fail :=
            invariant1_runFuel_sound space
          have comment := invariant1_strict_comment pre cs env
          dsimp only at comment
          rw [← atCursor] at comment
          have left : Derives ctx (.call 7 5) ('#' :: cs).length env .fail := .call entered7 rejected
          have right : Derives ctx (.call 8 6) ('#' :: cs).length env (.ok rest.length {env with resultDepth := 0}) :=
            Derives.call (rule := 6) entered8 comment
          rw [reset] at right
          have next := ih rest progress ((pre ++ ['#']) ++ cs.takeWhile (· != '\n'))
            (by simpa [rest, List.append_assoc] using atCursor)
          rw [afterWhitespace]; simp only [isSpace, Bool.false_eq_true, ite_false, ite_true]
          apply Derives.loopMore (.altRetry left right) progress
          simpa using next
        · have h := invariant1_strict_ws_stop pre c cs env isSpace hash
          dsimp only at h
          rw [← atCursor] at h
          simpa [afterWhitespace, isSpace, hash] using stop h

theorem invariant1_strict_whitespace_scan (pre xs : List Char) (env : Env) :
    Derives (context false (pre ++ xs)) translatedStrictWs xs.length env
      (.ok (afterWhitespace xs).length {env with resultDepth := 0}) :=
  .star (ws_loop _ pre xs _ rfl rfl)

-- Ws is memoized by offset and returns (). Its only callee state visible
-- on return is resultDepth. Both that depth and the end cursor are fixed
-- even if the caller entered with different captures and bindings.
theorem invariant1_strict_ws_memo_reply (pre xs : List Char) (env : Env) (reply : Reply) :
    let ctx := context false (pre ++ xs)
    (∃ fuel, runFuel ctx fuel (ctx.rules 4) xs.length env = some reply) ↔
      reply = .ok (afterWhitespace xs).length {env with resultDepth := 0} := by
  obtain ⟨fuel, succeeded⟩ := invariant1_derivation_has_fuel
    (invariant1_strict_whitespace_scan pre xs env)
  constructor
  · rintro ⟨k, observed⟩
    exact invariant1_result_unique _ observed succeeded
  · rintro rfl
    exact ⟨fuel, succeeded⟩

-- The runtime table indexes by byte offset. Equal byte keys into the same
-- input select the same suffix even when prefixes contain multibyte scalars.
private theorem suffix_at_byte_key {p q xs ys : List Char}
    (input : p ++ xs = q ++ ys) (key : p.utf8Encode.size = q.utf8Encode.size) :
    xs = ys := by
  have bytes := congrArg List.utf8Encode input
  rw [List.utf8Encode_append, List.utf8Encode_append] at bytes
  have suffix := congrArg (fun b : ByteArray => b.extract p.utf8Encode.size b.size) bytes
  simp only [ByteArray.size_append] at suffix
  rw [ByteArray.extract_append_eq_right rfl rfl,
    ByteArray.extract_append_eq_right key rfl] at suffix
  simpa using congrArg ByteArray.utf8Decode? suffix

theorem invariant1_strict_ws_cache_hit {p q xs ys : List Char} (left right : Env)
    (input : p ++ xs = q ++ ys) (key : p.utf8Encode.size = q.utf8Encode.size) :
    let rest := (afterWhitespace xs).length
    (∃ fuel, runFuel (context false (p ++ xs)) fuel ((context false (p ++ xs)).rules 4)
      xs.length left = some (.ok rest {left with resultDepth := 0})) ∧
    (∃ fuel, runFuel (context false (q ++ ys)) fuel ((context false (q ++ ys)).rules 4)
      ys.length right = some (.ok rest {right with resultDepth := 0})) := by
  obtain rfl := suffix_at_byte_key input key
  exact ⟨(invariant1_strict_ws_memo_reply p xs left _).2 rfl,
    (invariant1_strict_ws_memo_reply q xs right _).2 rfl⟩

#print axioms invariant1_strict_ws_cache_hit
#print axioms invariant1_strict_ws_memo_reply
#print axioms invariant1_strict_whitespace_scan
end PegHs.MetaExecution
