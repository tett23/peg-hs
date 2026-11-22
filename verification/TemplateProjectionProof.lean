import PublicGeneration

namespace PegHs.TemplateProjectionProof
open PublicGeneration

theorem root_adr0097_i2_annotation_preserved (r : Rule) :
    r.toTemplate.annotation = r.annotation.map locNat := by
  rfl

theorem root_adr0097_i2_constructors_preserved (r : Rule) :
    (r.toTemplate.alts.map TemplateExpansionWhole.Alt.constructor) =
      r.alts.map (fun a => a.constructor.map Prod.snd) := by
  simp [Rule.toTemplate, List.map_map]

#print axioms PegHs.TemplateProjectionProof.root_adr0097_i2_annotation_preserved
#print axioms PegHs.TemplateProjectionProof.root_adr0097_i2_constructors_preserved
end PegHs.TemplateProjectionProof
