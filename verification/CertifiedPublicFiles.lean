import TotalFile
import PegFull
import SyntaxFull

namespace PegHs.MetaExecution

private theorem acceptsSource {mode input env} (accepted : FileResult mode input (.ok 0 env))
    (diagnostic : PublicParsing.Failure → String) :
    parseFile mode (String.ofList input) diagnostic = .ok () := by
  rw [invariant1_parseFile_entry]
  apply (FileEntry.invariant1_public_entry (recognizeFile _ _).property diagnostic).mpr
  exact ⟨env, by simpa only [String.toList_ofList] using accepted⟩

theorem invariant1_public_peg (diagnostic : PublicParsing.Failure → String) :
    parseFile false (String.ofList MetaPieces.Peg.source) diagnostic = .ok () :=
  acceptsSource MetaProof.Peg.invariant1_file_result diagnostic

theorem invariant1_public_syntax (diagnostic : PublicParsing.Failure → String) :
    parseFile true (String.ofList MetaPieces.Syntax.source) diagnostic = .ok () :=
  acceptsSource MetaProof.Syntax.invariant1_file_result diagnostic

#print axioms invariant1_public_peg
#print axioms invariant1_public_syntax
end PegHs.MetaExecution
