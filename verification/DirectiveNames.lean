namespace PegHs.DirectiveNames

def pathChar (c : Char) :=
  c.isAlphanum || c == '_' || c == '-' || c == '.'

def pathPart (s : String) :=
  !s.isEmpty && s != "." && s != ".." && s.toList.all pathChar

-- The parts between the slashes (T.splitOn "/"), on the characters: Lean's
-- String.splitOn has no lemmas, and AssembleTranslatedProof compares this
-- with the translation of isImportPath.
def pathParts (s : String) : List String :=
  (s.toList.splitOn '/').map String.ofList

def validImportPath (s : String) :=
  (pathParts s).all pathPart && ".hpeg".toList.isSuffixOf s.toList

def validExtension (s : String) := match s.toList with
  | [] => false
  | c :: cs => c.isUpper && cs.all Char.isAlphanum

theorem invariant2_import_path (s : String) : validImportPath s = true ↔
    (∀ p ∈ pathParts s, p.isEmpty = false ∧ p ≠ "." ∧ p ≠ ".." ∧
      ∀ c ∈ p.toList, pathChar c = true) ∧ ".hpeg".toList.isSuffixOf s.toList = true := by
  simp [validImportPath, pathPart, List.all_eq_true, and_assoc]

theorem invariant2_extension (s : String) : validExtension s = true ↔
    ∃ c cs, s.toList = c :: cs ∧ c.isUpper = true ∧ ∀ x ∈ cs, x.isAlphanum = true := by
  cases h : s.toList <;> simp [validExtension, h, List.all_eq_true] <;> grind

#guard validImportPath "lex/Ident.hpeg" && !(validImportPath "../x.hpeg") &&
    !(validImportPath "x//y.hpeg") && !(validImportPath "字.hpeg")
example : validExtension "NoDoRec" && !(validExtension "Δ") && !(validExtension "X_1") := by decide +kernel

end PegHs.DirectiveNames
