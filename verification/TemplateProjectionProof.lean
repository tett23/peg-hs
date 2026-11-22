import PublicGeneration

namespace PegHs.TemplateProjectionProof
open PublicGeneration

theorem root_adr0097_i2_location_fields_preserved (l : LabelCheck.Loc) :
    ((templateLoc l).file, (templateLoc l).line, (templateLoc l).col) =
      (l.file, l.line, l.col) := by
  rfl

theorem root_adr0097_i2_location_projection_injective (a b : LabelCheck.Loc)
    (same : templateLoc a = templateLoc b) : a = b := by
  cases a
  cases b
  simpa [templateLoc] using same

theorem root_adr0097_i2_files_distinct :
    templateLoc ⟨0, 2, 3⟩ ≠ templateLoc ⟨1, 2, 3⟩ := by decide

theorem root_adr0097_i2_long_columns_distinct :
    templateLoc ⟨0, 2, 100003⟩ ≠ templateLoc ⟨0, 3, 3⟩ := by decide

theorem root_adr0097_i2_annotation_preserved (r : Rule) :
    r.toTemplate.annotation = r.annotation.map templateLoc := by
  rfl

theorem root_adr0097_i2_constructors_preserved (r : Rule) :
    (r.toTemplate.alts.map TemplateExpansionWhole.Alt.constructor) =
      r.alts.map (fun a => a.constructor.map Prod.snd) := by
  simp [Rule.toTemplate, List.map_map]

#print axioms PegHs.TemplateProjectionProof.root_adr0097_i2_annotation_preserved
#print axioms PegHs.TemplateProjectionProof.root_adr0097_i2_location_projection_injective
#print axioms PegHs.TemplateProjectionProof.root_adr0097_i2_constructors_preserved
end PegHs.TemplateProjectionProof
