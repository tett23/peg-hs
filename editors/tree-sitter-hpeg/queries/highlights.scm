; The captures follow the table of ADR 0034.

(comment) @comment

(directive_name) @keyword.directive

(directive_argument) @string.special

(rule_name) @function

(rule_reference) @function.call

(template_parameters ["<" ">"] @punctuation.bracket)

(template_call ["<" ">"] @punctuation.bracket)

(template_parameter (identifier) @variable.parameter)

(binding) @variable.parameter

(literal) @string

(escape) @string.escape

(class) @string.regexp

(any) @constant.builtin

["<-" "::"] @keyword.operator

"/" @operator

(repetition operator: _ @operator)

(lookahead ["&" "!"] @operator)

(predicate ["&" "!"] @operator)

(capture "$" @operator)

(label) @label

(reserved_binding) @variable.builtin
