# Translate the strict runParser result branches to recognition and diagnostics.
# ST state supplies the formatted message; the proof quantifies over this lookup.
function reject() { bad = 1; exit 1 }
function emit(s) { print s }
BEGIN {
  emit("import PublicParsing")
  emit("namespace PegHs.PublicParsing")
  emit("def translatedRuntime {T} (bytes : Nat) (start : StartResult T)")
  emit("    : Except Failure T :=")
  emit("  match start with")
}
/^parseGrammar src =/ {
  if (assembly++ || $0 != "parseGrammar src = parseTops src >>= assemble") reject()
  next
}
/^parseTops src = case SelfHosted.parse src of$/ {
  if (wrapper++ || stage != 6) reject()
  emit("def translatedPublic {T} (d : Failure → String) : Except Failure T → Except PegHs.Pipeline.Diagnostics T")
  next
}
wrapper == 1 && !done {
  if (!right && $0 == "  Right tops -> Right tops") {
    emit("  | .ok tops => .ok tops"); right = 1; next
  }
  if (right && !left && $0 == "  Left e ->") { left = 1; next }
  # The actual text and location computed by these local bindings are abstracted by d.
  if (left && $0 ~ /^    (let p = |    rendered = |    msg = |      \(Just l, Nothing\) -> |      _ -> )/) next
  if (left && $0 == "     in Left [Diagnostic (Loc 0 (posLine p) (posColumn p)) msg]") {
    emit("  | .error e => .error [d e]"); done = 1; next
  }
  reject()
}
/^  res <- case r of$/ { if (seen++) reject(); active = 1; next }
!active { next }
$0 == "  s <- readSTRef (ctxStats ctx)" {
  if (stage != 6) reject()
  active = 0
  next
}
stage == 0 && $0 == "    Ok j x | j == ctxLen ctx -> pure (Right x)" {
  emit("  | .ok j x => if j = bytes then .ok x")
  stage++; next
}
stage == 1 && $0 == "    Ok j _ -> do" { stage++; next }
stage == 2 && $0 == "      mergeFail ctx (Failure j (S.singleton ExpectedEnd))" { stage++; next }
stage == 3 && $0 == "      Left <$> currentError ctx Nothing Nothing" {
  emit("    else .error (.expectedEnd j)"); stage++; next
}
stage == 4 && $0 == "    Throw _ l m -> Left <$> currentError ctx (Just l) m" {
  emit("  | .throwLabel _ l m => .error (.labelled l m)"); stage++; next
}
stage == 5 && $0 == "    Fail -> Left <$> currentError ctx Nothing Nothing" {
  emit("  | .fail => .error .ordinary"); stage++; next
}
{ reject() }
END {
  if (bad || active || seen != 1 || stage != 6 || !done || assembly != 1) exit 1
  emit("def translatedGrammar {T G} (bytes : Nat) (start : StartResult T) (d : Failure → String)")
  emit("    (assemble : T → Except PegHs.Pipeline.Diagnostics G) : Except PegHs.Pipeline.Diagnostics G :=")
  emit("  (translatedPublic d (translatedRuntime bytes start)).bind assemble")
  emit("end PegHs.PublicParsing")
}
