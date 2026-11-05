; Folds (ADR 0069): a rule with its type annotation, a verbatim block and a
; multi-line action. Neovim folds only the captures over several lines.

; A type annotation and the definition after it fold together.
((annotation
  name: (rule_name) @_annotated) @fold
  .
  (definition
    name: (rule_name) @_defined) @fold
  (#eq? @_annotated @_defined))

(definition) @fold

(verbatim) @fold

(action) @fold
