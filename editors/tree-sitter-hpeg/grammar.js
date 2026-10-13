/**
 * @file The .hpeg notation of peg-hs (ADR 0034).
 *
 * The rules follow packages/peg-grammar/grammar/Peg.hpeg, the notation's own
 * grammar. Haskell fragments (verbatim blocks, types, actions, predicates,
 * arguments) are read with the rules of ActionCode and HsPart there, and
 * are injected as Haskell by queries/injections.scm.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const IDENT = /[\p{L}_][\p{L}\p{N}_']*/u;

module.exports = grammar({
  name: 'hpeg',

  extras: $ => [/\s/, $.comment],

  // The text of a verbatim block, up to the first }% (src/scanner.c). A
  // regular expression cannot leave out the } of }% after other }s, as in
  // f = g {}}% (ADR 0045).
  externals: $ => [$._verbatim_body],

  word: $ => $.identifier,

  // A sequence ends where the next declaration starts, which is known only
  // after its name (Peg.hpeg reads ahead with DeclStart): these are resolved
  // by trying both.
  conflicts: $ => [

    [$.alternative],
  ],

  rules: {
    source_file: $ => repeat(choice($.verbatim, $.directive, $.annotation, $.definition)),

    comment: _ => token(seq('#', /[^\n]*/)),

    identifier: _ => IDENT,

    // Top-level items -----------------------------------------------------------

    verbatim: $ => seq('%{', optional(alias($._verbatim_body, $.haskell)), '}%'),


    directive: $ => seq(
      field('name', $.directive_name),
      optional(field('argument', $.directive_argument)),
    ),

    directive_name: _ => token(seq('%', IDENT)),

    // The rest of the line up to a comment.
    directive_argument: _ => token.immediate(/[ \t]*[^ \t\n#][^\n#]*/),

    annotation: $ => seq(
      field('name', $.rule_name),
      optional($.template_parameters),
      optional($.parameters),
      '::',
      field('type', $.type),
    ),

    // The rest of the line.
    type: _ => token.immediate(/[ \t]*[^ \t\n][^\n]*/),

    definition: $ => seq(
      field('name', $.rule_name),
      optional($.template_parameters),
      '<-',
      $.alternatives,
    ),

    rule_name: $ => $.identifier,

    template_parameters: $ => seq(
      token.immediate('<'),
      commaSep1($.template_parameter),
      '>',
    ),

    template_parameter: $ => seq($.identifier, optional(seq('::', $.identifier))),

    parameters: $ => seq(token.immediate('('), commaSep1(alias($._argument_code, $.haskell)), ')'),

    // Alternatives and expressions ----------------------------------------------

    alternatives: $ => seq($.alternative, repeat(seq('/', $.alternative))),

    alternative: $ => choice(
      seq(repeat1($.item), optional($.action)),
      $.action,
    ),

    item: $ => seq(optional($.binding), $._prefix),

    binding: $ => seq(field('name', $.identifier), token.immediate(':')),

    _prefix: $ => choice(
      $.predicate,
      $.lookahead,
      $.capture,
      $._labeled,
    ),

    predicate: $ => seq(choice('&', '!'), '{', optional(alias($._action_code, $.haskell)), '}'),

    lookahead: $ => seq(choice('&', '!'), $._prefix),

    capture: $ => seq('$', $._prefix),

    _labeled: $ => choice($._suffix, $.labeled),

    labeled: $ => seq($._suffix, $.label),

    label: $ => seq('^', field('name', $.identifier)),

    _suffix: $ => choice($._primary, $.repetition),

    repetition: $ => seq($._suffix, field('operator', choice('*', '+', '?'))),

    _primary: $ => choice(
      $.literal,
      $.class,
      $.any,
      $.group,
      $.call,
      $.template_call,
      $.rule_reference,
    ),

    any: _ => '.',

    group: $ => seq('(', optional($._group_alternatives), ')'),

    _group_alternatives: $ => choice(
      seq(repeat1($.item), repeat(seq('/', repeat($.item)))),
      repeat1(seq('/', repeat($.item))),
    ),

    call: $ => seq(
      field('name', alias($.identifier, $.rule_reference)),
      token.immediate('('),
      commaSep1(alias($._argument_code, $.haskell)),
      ')',
    ),

    // The value arguments follow > without a space (ADR 0055): T<a> (b) is
    // a template call and a group.
    template_call: $ => seq(
      field('name', alias($.identifier, $.rule_reference)),
      token.immediate('<'),
      commaSep1($.template_argument),
      '>',
      optional(seq(token.immediate('('), commaSep1(alias($._argument_code, $.haskell)), ')')),
    ),

    template_argument: $ => $._group_alternatives,

    rule_reference: $ => $.identifier,

    // Literals and classes ------------------------------------------------------

    // The contents take precedence over a comment: '#' is a literal.
    literal: $ => choice(
      seq("'", repeat(choice($.escape, token.immediate(prec(1, /[^'\\\n]+/)))), token.immediate("'")),
      seq('"', repeat(choice($.escape, token.immediate(prec(1, /[^"\\\n]+/)))), token.immediate('"')),
    ),

    class: $ => seq('[', repeat1(choice($.escape, token.immediate(prec(1, /[^\]\\\n]+/)))), token.immediate(']')),

    escape: _ => token.immediate(seq('\\', choice(/[ntr\\'"\]\[\-]/, /u\{[0-9a-fA-F]*\}/))),

    // Haskell fragments ----------------------------------------------------------

    action: $ => seq('{', optional(alias($._action_code, $.haskell)), '}'),

    // Up to the '}' at depth 0.
    _action_code: $ => repeat1(choice($._hs_part, ',')),

    // Up to the ',' or ')' at depth 0.
    _argument_code: $ => repeat1($._hs_part),

    _hs_part: $ => choice(
      $._hs_nested,
      $._hs_string,
      $._hs_char,
      $.reserved_binding,
      $._hs_identifier,
      $._hs_other,
    ),

    _hs_nested: $ => choice(
      seq('(', repeat(choice($._hs_part, ',')), ')'),
      seq('[', repeat(choice($._hs_part, ',')), ']'),
      seq('{', repeat(choice($._hs_part, ',')), '}'),
    ),

    _hs_string: _ => token(prec(2, /"([^"\\\n]|\\.)*"/)),

    _hs_char: _ => token(prec(2, choice(/'\\.[^'\n]*'/, /'[^\\\n]'/, "'"))),

    reserved_binding: _ => token(prec(3, choice('_span', '_env', '_col'))),

    _hs_identifier: _ => token(prec(2, /[\p{L}\p{N}_][\p{L}\p{N}_']*/u)),

    _hs_other: _ => token(prec(1, /[^(){}\[\]"',\p{L}\p{N}_]+/u)),
  },
});

/**
 * @param {RuleOrLiteral} rule
 */
function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)));
}
