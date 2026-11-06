; The captures follow the table of ADR 0034, with the punctuation and the
; arguments of directives of ADR 0069, and the constructor names and the
; classes of %deriving of ADR 0075.

(comment) @comment

(directive_name) @keyword.directive

(directive_argument) @string.special

(module_name) @module

(rule_name_argument) @function.call

(label_argument) @label

(extension_name) @constant

(class_name) @type

(constructor_name) @constructor

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

; Punctuation (ADR 0069). The brackets of a class are part of the class, and
; the brackets inside Haskell code are left to Haskell.

(group ["(" ")"] @punctuation.bracket)

(parameters ["(" ")"] @punctuation.bracket)

(call ["(" ")"] @punctuation.bracket)

(template_call ["(" ")"] @punctuation.bracket)

(action ["{" "}"] @punctuation.special)

(predicate ["{" "}"] @punctuation.special)

(verbatim ["%{" "}%"] @punctuation.special)

(binding ":" @punctuation.delimiter)

(template_parameters "," @punctuation.delimiter)

(template_call "," @punctuation.delimiter)

(label "^" @operator)

(alternative "@" @punctuation.special)
