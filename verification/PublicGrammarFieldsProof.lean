import PublicGeneration

namespace PegHs.PublicGrammarFieldsProof
open PublicGeneration
open LabelsBridge (eLoc eLocated)

theorem root_adr0097_i3_exports_preserved (g : Grammar) :
    LabelsTranslated.Grammar.grammarExports (toTranslated g) = g.exports.map eLocated := by rfl

theorem root_adr0097_i3_environment_preserved (g : Grammar) :
    LabelsTranslated.Grammar.grammarEnv (toTranslated g) = g.env.map eLocated := by rfl

theorem root_adr0097_i3_tabstop_preserved (g : Grammar) :
    LabelsTranslated.Grammar.grammarTabstop (toTranslated g) =
      g.tabstop.map (fun p => LabelsTranslated.Located.Located (eLoc p.1) p.2) := by rfl

theorem root_adr0097_i3_deriving_preserved (g : Grammar) :
    LabelsTranslated.Grammar.grammarDeriving (toTranslated g) =
      g.derivingClasses.map (fun p =>
        LabelsTranslated.Located.Located (eLoc p.1) (p.2.map eLocated)) := by rfl

theorem root_adr0097_i3_rule_type_location_preserved (r : Rule) :
    LabelsTranslated.Rule.ruleType r.toTranslated = eLocated r.type := by rfl

theorem root_adr0097_i3_parameter_type_locations_preserved (r : Rule) :
    (LabelsTranslated.Rule.ruleParams r.toTranslated).map LabelsTranslated.Param.paramType =
      r.params.map (fun p => eLocated p.2) := by
  simp [Rule.toTranslated, List.map_map, Function.comp_def,
    LabelsTranslated.Rule.ruleParams, LabelsTranslated.Param.paramType]

#print axioms PegHs.PublicGrammarFieldsProof.root_adr0097_i3_environment_preserved
#print axioms PegHs.PublicGrammarFieldsProof.root_adr0097_i3_parameter_type_locations_preserved
end PegHs.PublicGrammarFieldsProof
