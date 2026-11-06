; Locals (ADR 0069): rules are defined by their definitions and referred to
; in expressions and in the arguments of directives; bindings are defined in
; alternatives.

(definition
  name: (rule_name) @local.definition.function)

(rule_reference) @local.reference

(rule_name_argument) @local.reference

(binding
  name: (identifier) @local.definition.var)
