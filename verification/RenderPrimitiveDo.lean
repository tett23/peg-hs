import RenderExpression

namespace PegHs.RenderPrimitiveDo

-- Direct translation of Codegen.doBlock's Text.concat (intersperse ...).
def printedDo (statements : List String) : String :=
  "do { " ++ String.join (List.intersperse "\n          ; " statements) ++
    "\n          }"

theorem join_intersperse (separator : String) (items : List String) :
    String.join (List.intersperse separator items) =
      String.intercalate separator items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second more =>
      simp only [List.intersperse, String.join_cons,
        String.intercalate_cons_cons, ih]
      simp [String.append_assoc]

theorem printed_do_is_render_do (statements : List String) :
    printedDo statements =
      Peg.Verification.RenderExpression.renderDo statements := by
  simp [printedDo, Peg.Verification.RenderExpression.renderDo,
    join_intersperse]

theorem printed_do_syntax (statementSyntax : String → Prop)
    (statements : List String) (nonempty : statements ≠ [])
    (valid : ∀ statement ∈ statements, statementSyntax statement) :
    Peg.Verification.RenderExpression.DoSyntax statementSyntax
      (printedDo statements) := by
  rw [printed_do_is_render_do]
  exact Peg.Verification.RenderExpression.invariant3_sequence
    statementSyntax statements nonempty valid

#print axioms join_intersperse
#print axioms printed_do_is_render_do
#print axioms printed_do_syntax

end PegHs.RenderPrimitiveDo
