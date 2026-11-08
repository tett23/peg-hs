# The .hpeg notation

[日本語版](syntax.md)

This document explains how to write peg-hs grammar files (`.hpeg`), mainly through examples.
For each element of the notation, it describes in turn what the element does, how to write it, and what peg-hs reports when it is written wrongly.
The norms are in the ADRs, and this document puts them together in a form that can be read from the user's side.
Where the description disagrees with an ADR, the ADR takes precedence.

This document reflects only the content of adopted ADRs.
The reflected ADRs are [ADR 0001](adr/0001-bounded-left-recursion.md), [ADR 0003](adr/0003-typed-semantic-actions.md), [ADR 0004](adr/0004-peg-notation.md), [ADR 0005](adr/0005-error-reporting.md), [ADR 0006](adr/0006-memoization-control.md), [ADR 0008](adr/0008-source-positions.md), [ADR 0012](adr/0012-context-sensitive-extensions.md), [ADR 0014](adr/0014-generated-module-api.md), [ADR 0015](adr/0015-implementation-deviations.md), [ADR 0016](adr/0016-language-extensions.md), [ADR 0017](adr/0017-nomemo-implementation.md), [ADR 0018](adr/0018-tab-partial-consumption.md), [ADR 0019](adr/0019-lossless-syntax-tree.md), [ADR 0020](adr/0020-unicode-identifiers-self-hosted.md), [ADR 0021](adr/0021-error-recovery.md), [ADR 0026](adr/0026-discard-unused-values.md), [ADR 0027](adr/0027-switch-to-self-hosted-parser.md), [ADR 0028](adr/0028-label-safety-check.md), [ADR 0029](adr/0029-label-safety-implementation-deviations.md), [ADR 0030](adr/0030-unit-values-are-not-counted.md), [ADR 0031](adr/0031-rule-templates.md), [ADR 0033](adr/0033-grammar-linter.md), [ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md), [ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md), [ADR 0050](adr/0050-hpeg-extension.md), [ADR 0053](adr/0053-type-names-of-rules-without-case.md), [ADR 0054](adr/0054-automatic-label-insertion.md), [ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md), [ADR 0056](adr/0056-label-insertion-and-template-deviations.md), [ADR 0061](adr/0061-select-generated-exports.md), [ADR 0062](adr/0062-warnings-of-pruned-generated-modules.md), [ADR 0063](adr/0063-omit-unit-actions.md), [ADR 0064](adr/0064-unit-rules-always-return-unit.md), [ADR 0065](adr/0065-omittable-identity-actions.md), [ADR 0066](adr/0066-omit-unit-type-annotations.md), [ADR 0067](adr/0067-lint-info-with-verbose.md), [ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md), [ADR 0075](adr/0075-generated-types-for-rules-without-actions.md), [ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md), [ADR 0082](adr/0082-static-check-of-binding-references.md), [ADR 0083](adr/0083-bindings-inside-a-group-are-not-visible.md), [ADR 0086](adr/0086-inserted-labels-pass-the-label-check.md), [ADR 0087](adr/0087-other-labels-do-not-change-the-label-check.md) and [ADR 0088](adr/0088-correct-the-second-example-of-adr-0087.md).

Among the code blocks of this document, those that start with `%module` are complete grammars, and `peg-hs gen` can generate code from them as they are.
The others are fragments taken out of a grammar.

## A minimal example

We start with a grammar of expressions that have addition only.

```hpeg
%module Example.Sum

%{
import Data.Text (unpack)
}%

# Left-associative addition
Sum :: Int
Sum <- l:Sum '+' r:Num { l + r }
     / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

`peg-hs gen Sum.hpeg` generates the Haskell module `Example.Sum` from this grammar.
The module exports the entry point `parse :: Text -> Either ParseError Int`, and `parse "1+2+3"` returns `Right 6`.
`Sum` is a left-recursive rule, which calls itself at its left end, and `1+2+3` is built in the order `(1+2)+3`.

Most elements of the notation appear in this short grammar.
`%module` is a directive, `%{ ... }%` is Haskell code copied verbatim, `Sum :: Int` is the type annotation of a rule, and `Sum <- ...` is the definition of the rule.
`l:Sum` is a binding, which names a value, `$[0-9]+` is a text capture, which takes the text it read, and `{ l + r }` is an action, which makes the value of the alternative.
The following sections explain each of them.

## Reading errors and warnings

peg-hs writes errors in a grammar to the standard error in the following form.

```
Sum.hpeg:3:6: error: undefined rule Num
```

The file name, the line and the column are followed by the message of the error.
If there is even one error, `peg-hs gen` generates nothing and ends with exit status 1.

Besides errors, there are warnings about ways of writing that can be generated but may differ from what was meant.
Warnings come from two sources.

- **Warnings about the safety of labels**: given by `peg-hs gen`. Generation continues. With `--Werror`, generation fails if there are warnings ([Checking the safety of labels](#checking-the-safety-of-labels))
- **Warnings of lint**: given by `peg-hs lint`. If there is even one warning, it ends with exit status 1 ([lint](#lint))

`peg-hs lint` also gives info, apart from warnings.
Info points out ways of writing that would make the grammar simpler if fixed, but are not errors if left as they are.
Only with `--verbose` is info shown, written `info:` in place of `warning:`, and it does not change the exit status.

The "common mistakes" tables in the following sections pair a way of writing with the message peg-hs gives for it.
The messages are shown without the file name and the position.

## The structure of a file

A file is a sequence of directives, verbatim blocks and rules.
They can come in any order, but it reads well to put the directives and verbatim blocks together at the top and the rules after them.

### Comments

From `#` to the end of the line is a comment.
A `#` inside a literal, a character class or an action is not a comment.

```hpeg
%module Example.Hash

# This line is a comment
Hash <- '#' # The '#' of the literal is not a comment
```

A comment can also follow the arguments of a directive.
However, the argument of `%env` is a type up to the end of the line as it is, so do not write a comment on the line of `%env`.

### Directives

A directive is a line that starts with `%`, and specifies something about the whole grammar.

| Directive | Meaning | ADR |
|---|---|---|
| `%module A.B.C` | The name of the module to generate. Required | [ADR 0004](adr/0004-peg-notation.md) |
| `%start Name` | The start rule. If omitted, the rule defined first is the start rule | [ADR 0004](adr/0004-peg-notation.md) |
| `%entry Name` | Generates an entry point for a rule other than the start rule too | [ADR 0014](adr/0014-generated-module-api.md) |
| `%export item, ...` | Exports names defined in verbatim blocks from the generated module | [ADR 0014](adr/0014-generated-module-api.md) |
| `%language Extension, ...` | Enables language extensions in the generated module | [ADR 0016](adr/0016-language-extensions.md) |
| `%env Type` | Declares the type of an environment that does not change through the whole parse | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `%tabstop N` | In computing `_col`, advances a tab to a column that is a multiple of N | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `%nomemo Name` | Turns off the memoization of a rule | [ADR 0017](adr/0017-nomemo-implementation.md) |
| `%syntax` | Also generates entry points that return a lossless syntax tree | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%token Name` | Makes a match of the rule one token in the syntax tree | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%trivia Name` | Treats a `%token` rule as trivia, such as whitespace and comments | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%inline Name` | In the syntax tree, does not make a call of the rule a node, and places its children in the caller | [ADR 0019](adr/0019-lossless-syntax-tree.md) |
| `%recover label Name` | Makes `Name` the recovery rule of the label `label` | [ADR 0021](adr/0021-error-recovery.md) |
| `%safe label` | Stops the safety warnings for the label `label` | [ADR 0028](adr/0028-label-safety-check.md) |
| `%deriving Class, ...` | The classes that the generated types derive. Without arguments, nothing is derived | [ADR 0075](adr/0075-generated-types-for-rules-without-actions.md) |

`%module`, `%start`, `%env`, `%tabstop`, `%syntax` and `%deriving` can be written only once.
`%entry`, `%export`, `%language`, `%nomemo`, `%token`, `%trivia`, `%inline`, `%recover` and `%safe` can be written any number of times.
For directives that take one rule per line (`%entry`, `%nomemo` and so on), write one line for each rule.

The value of `%module` and the items of `%export` are written into the generated module as they are.
peg-hs therefore rejects values that would read as Haskell declarations ([ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
The value of `%module` is a module name of parts separated by dots.
Each part starts with an upper case letter, followed by letters, digits, `_` and `'` only.
An item of `%export` takes one of the following forms.
Spaces may separate the items and stand inside the parentheses.

- A variable or type name, which may be qualified (`evalExpr`, `Expr`, `M.f`)
- A type name followed by `(..)`, or by `( ... )` with names and operators in parentheses separated by commas (`Expr(..)`, `Expr(Add, Mul)`)
- An operator in parentheses (`(+++)`)
- Any of these after `type` or `pattern` (`type (:+)`, `pattern P`)
- `module` and a module name (`module Data.Text`)

The use of each directive is explained in the section it concerns.

Common mistakes:

| Writing | Report |
|---|---|
| Forgot `%module` | `error: missing %module directive` |
| Misspelled it (`%modul`) | `error: unknown directive %modul` |
| Wrote `%start` twice | `error: duplicate %start directive` |
| Forgot the argument (`%start`) | `error: %start needs an argument` |
| Wrote something that is not a rule name (`%entry A B`) | `error: %entry expects a rule name` |
| Wrote a rule that is not defined | `error: undefined rule Name` |
| `%tabstop 0` | `error: %tabstop expects a positive integer` |
| Wrote something that is not a module name (`%module m`, `%module M where x = 1`) | `error: %module expects a module name, but got m` |
| Wrote something that is not an export item (`%export f) where`, `%export f -- x`) | `error: %export expects export items, but got f) where` |

### Verbatim blocks

The part enclosed in `%{` and `}%` is copied verbatim into the generated module as Haskell code.
Write imports, the types of the syntax tree, and helper functions called from actions here.
If there are several blocks, they are concatenated in the order they appear.

```hpeg
%module Example.Digit

%{
import qualified Data.Text as T

digitValue :: Char -> Int
digitValue c = fromEnum c - fromEnum '0'
}%

Digit :: Int
Digit <- d:$[0-9] { digitValue (T.head d) }
```

The generated module imports the Prelude qualified as `PegPrelude`.
If the verbatim blocks do not import the Prelude, the generator also adds the ordinary `import Prelude`, so actions can use the names of the Prelude as usual ([ADR 0015](adr/0015-implementation-deviations.md)).
Hiding the Prelude in a verbatim block, as in `import Prelude ()`, does not affect the generated code.

So as not to collide with names that the generator uses internally, verbatim blocks cannot use the following names ([ADR 0014](adr/0014-generated-module-api.md)).

- Definitions of names that start with `peg'` or `Peg'`
- The import aliases `PegRt` and `PegPrelude`

Common mistakes:

| Writing | Report |
|---|---|
| Forgot to close with `}%` | `error: unterminated %{ block` |
| Defined `peg'helper = ...` | `error: the name peg'helper is reserved for generated code` |
| `import qualified Foo as PegRt` | `error: the module alias PegRt is reserved for generated code` |

### Language extensions

Verbatim blocks are placed after the top of the module.
So writing `{-# LANGUAGE OverloadedStrings #-}` in a verbatim block has no effect.
Enable language extensions with the `%language` directive ([ADR 0016](adr/0016-language-extensions.md)).

```hpeg
%module Example.Words
%language OverloadedStrings

%{
import Data.Text (Text)
}%

Sign :: Text
Sign <- '+' { "plus" }
      / '-' { "minus" }
```

Since `OverloadedStrings` is enabled, the string literal `"plus"` in the action becomes a `Text`.
Write several extensions separated by commas, as in `%language OverloadedStrings, LambdaCase`, or on several `%language` lines.
The generator places the pragmas at the top of the generated module, in the order written.

Language extensions affect not only the user's code but also the generated code.
The tests check that the generated code does not change its meaning under the following extensions:
`OverloadedStrings`, `OverloadedLists`, `LambdaCase`, `Strict`, `StrictData` and `NoImplicitPrelude`.
Other combinations of extensions are outside the guarantee.

In a grammar that specifies `NoImplicitPrelude`, the generator does not add `import Prelude`.
The user has declined the implicit Prelude, so import the names of the Prelude yourself in a verbatim block.

Common mistakes:

| Writing | Report |
|---|---|
| `%language RebindableSyntax` | `error: %language RebindableSyntax is not allowed: it changes the meaning of the generated code` |
| Something that is not an extension name as a token (`%language overloaded`) | `error: %language expects extension names, but got overloaded` |
| An extension name that does not exist (`%language OverloadedStringz`) | peg-hs does not report it. GHC reports it when compiling the generated module |

`RebindableSyntax` is rejected because it makes the user's definitions interpret the `do` notation and numeric literals of the generated code.

## Rules

A rule is written as a pair of a type annotation and a definition.

```hpeg
# Fragment
Name :: Type
Name <- alternative / alternative / ...
```

The right side of `::` in a type annotation, up to the end of the line, is taken as a Haskell type.
Types such as `[Int]` and `Maybe (Text, Int)` can be written as they are.
It is GHC that checks that the type is correct; peg-hs copies the type into the generated module as a string.

The type annotation can be omitted.
The type of a rule without a value is `()` when there is no type annotation ([ADR 0066](adr/0066-omit-unit-type-annotations.md)).
Many rules that read whitespace, separators and keywords have no value, so they can be written with the line of the definition only.

```hpeg
# Fragment
Sp <- ' '*    # The same as writing Sp :: ()
```

When a rule with neither a type annotation nor an action has a value, peg-hs infers its type or generates a type ([Inferring and generating types](#inferring-and-generating-types)).
The type of a rule with actions is `()` when there is no type annotation, whatever the values of its alternatives.
If you write an action in a rule meant to return a value and forget the type annotation, the value of the action does not match `()`.
GHC reports this mismatch when compiling the generated module, as a type error that points at the position of the action.

Rules with parameters ([Parameterized rules](#parameterized-rules)) and templates ([Rule templates](#rule-templates)) cannot omit the type annotation.
This is because only the type annotation can declare parameters.

The alternatives on the right side of a definition can span several lines.
The definition of a rule ends where the type annotation or the definition of the next rule starts.

### Rule names

Rule names and binding names can use Unicode letters ([ADR 0020](adr/0020-unicode-identifiers-self-hosted.md)).
The first character is a letter or `_`, and the following characters are letters, digits, `_` and `'`.
Whether a character is a letter follows Haskell's `Data.Char.isAlpha`, so kanji and kana are also treated as letters.

```hpeg
%module Example.Japanese
%start 数式

%{
import Data.Text (unpack)
}%

数式 :: Int
数式 <- 左:数式 '＋' 右:数 { 左 + 右 }
      / 数

数 :: Int
数 <- ds:$[0-9]+ { read (unpack ds) }
```

In a grammar with `%syntax`, Haskell type names are made from rule names.
A rule name that starts with a character without case, such as a kanji, gets `Rule'` before its type name ([Lossless syntax trees](#lossless-syntax-trees), [ADR 0053](adr/0053-type-names-of-rules-without-case.md)).

### The start rule and unreachable rules

The start rule is the rule specified with `%start`, or the rule defined first in the file.
Every rule must be reachable by following calls from the start rule, a rule of `%entry`, or a recovery rule of `%recover`.
Leaving a rule that is not used is an error.

Common mistakes in the definitions and type annotations of rules:

| Writing | Report |
|---|---|
| Forgot the type annotation of a template (wrote only `T<p> <- p`) | `error: rule T has parameters, so it needs a type annotation` |
| A type annotation without a definition | `error: rule A has a type annotation but no definition` |
| No type after `::` in a type annotation | `error: expected a type` |
| Defined the same rule twice | `error: duplicate definition of A` |
| Wrote a type annotation for the same rule twice | `error: duplicate type annotation for A` |
| Called a rule that is not defined | `error: undefined rule B` |
| Left a rule that is not called from anywhere | `error: rule B is unreachable from the start, entry and recovery rules` |
| Wrote no rules at all | `error: the grammar has no rules` |
| Neither `::` nor `<-` after a rule name | `error: expected :: or <-` |

## Expressions

The right side of the definition of a rule is an expression that combines terminals and operators.

### Terminals

A terminal is an expression that matches characters of the input directly.

- **Literals**: can be written either as `'abc'` or as `"abc"`. Matches the string written
- **Character classes**: of the form `[a-z0-9_]`. Matches one character that is one of the characters or ranges in the brackets
- **Any character**: `.` matches one Unicode code point

Literals and character classes can use the following escapes.

```
\n \t \r \\ \' \" \] \[ \- \u{XXXX}
```

`\u{XXXX}` is the character of a code point written in hexadecimal (`\u{3042}` is `あ`).
A newline cannot be written as it is inside a literal or a character class, so write `\n`.

Character classes have no negated form `[^...]`.
Write "one character other than `a` to `z`" as `![a-z] .`, combining a negative lookahead with `.`.

```hpeg
%module Example.Quoted

%{
import Data.Text (Text)
}%

# A string enclosed in ', without newlines
Quoted :: Text
Quoted <- '\'' $(!['\n] .)* '\''
```

Common mistakes:

| Writing | Report |
|---|---|
| Forgot to close a literal (`'abc`) | `error: unterminated literal` |
| An unknown escape (`'\q'`) | `error: unknown escape \q` |
| No `{` after `\u`, or no closing `}` | `error: expected '{'`, `error: expected '}'` |
| A code point out of range (`\u{110000}`) | `error: invalid \u escape` |
| An empty character class (`[]`) | `error: empty character class` |
| Forgot to close a character class (`[a-z`) | `error: unterminated character class` |
| A reversed range (`[z-a]`) | `error: the range is empty` |
| `[^a-z]` meant as a negation | Not reported. It becomes a character class that matches `^` or one character from `a` to `z` |

The last one, `[^a-z]`, gives a grammar different from what was meant, without an error.
A `^` at the start of a character class is read as an ordinary character, so use `![a-z] .` for a negation.

### Operators

The operators are as follows, from the most tightly binding.

| Kind | Notation | Meaning |
|---|---|---|
| Suffix | `e*` `e+` `e?` | Zero or more times, one or more times, optional |
| Failure label | `e ^label` | Throws the label if `e` fails ([Recovery from syntax errors](#recovery-from-syntax-errors)) |
| Prefix | `&e` `!e` `$e` | Positive lookahead, negative lookahead, text capture |
| Sequence | `e1 e2` | Matches from left to right |
| Choice | `e1 / e2` | Tries the alternatives from the left, and takes the first that succeeds |

Suffixes bind more tightly than prefixes, so `$[0-9]+` reads as `$([0-9]+)`.
Enclosing an expression in parentheses `( ... )` changes the binding.

An expression nests at most 256 levels deep ([ADR 0080](adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
The parentheses of a group, a prefix or suffix operator, a failure label and the arguments of a template call each count as one level.
`!('a'*)` has three levels: `!`, the parentheses and `*`.
The levels of expressions side by side are not added.
`('a') ('b')` has one level.
An expression deeper than the limit is an error at the level that goes over it.
The limit cannot be changed.

The lookaheads `&e` and `!e` only check whether `e` matches (or does not), and do not consume input.
`!.` succeeds only at the end of the input.

The choice `/` is ordered.
When an earlier alternative succeeds, the later alternatives are not tried.
In `'=' / '=='`, `'=='` never succeeds, because on input starting with `=` the earlier `'='` always succeeds first.
Put the longer one first.

The repetitions `*` and `+` read as far as they can match, and do not backtrack.
`[a-z]* 'x'` does not match `abcx`.
This is because `[a-z]*` reads up to `x`, and nothing is left for `'x'`.

Common mistakes:

| Writing | Report |
|---|---|
| A repetition of an expression that can match the empty string (`('a'?)*`) | `error: the repeated expression can match the empty string, which would loop forever` |
| Forgot to close the parentheses of a group (the line ends with `('a' / 'b'`) | `error: expected ')'` |
| No expression after an operator or a binding (`'a' ! / 'b'`, `x:`) | `error: expected an expression` |
| An expression nests deeper than 256 levels (257 nested parentheses) | `error: the expression nests deeper than 256` |
| An earlier alternative always succeeds (`'a'? / 'b'`) | lint: `warning: the alternative is never tried: the alternative at 3:6 always succeeds [unreachable-alternative]` |
| An earlier alternative matches a prefix (`'=' / '=='`) | lint: `warning: the alternative never succeeds: the alternative at 3:7 matches its prefix '=' first [unreachable-alternative]` |
| Wrote the same alternative twice | lint: `warning: the alternative never succeeds: it is the same as the alternative at 3:7 [duplicate-alternative]` |

The position in a lint warning (`3:6` and so on) points at the earlier alternative that keeps the later alternative from succeeding.

## Values and bindings

### Expressions with values

Actions can refer only to expressions that have values.

| Expression | Type of the value |
|---|---|
| A call of a rule `Name`, `Name(args)`, a call of a template `Name<args>` | The type of the rule |
| A text capture `$e` | The `Text` of the consumed input |
| `e*` `e+` | A list of the type of the value of `e` |
| `e?` | `Maybe` of the type of the value of `e` |
| `e ^label` | The type of the value of `e` |

Literals, character classes, `.`, lookaheads and semantic predicates have no values.
When you want the characters that matched a literal or a character class, take them with `$`.

```hpeg
# Fragment
Ident :: Text
Ident <- s:$([a-z] [a-z0-9]*) { s }
```

A group enclosed in parentheses has a value when each alternative inside it has exactly one value, and that value is the value of the group; otherwise the group has no value.

### Values of `()` are not counted

A rule whose type annotation is `()`, such as a rule that reads whitespace, carries no information as a value.
In counting values, values of `()` that are not bound are not counted ([ADR 0030](adr/0030-unit-values-are-not-counted.md)).
This applies to rules whose type annotation is `()`, and to such rules with `*`, `+` or `?` attached.
The same holds for a rule without a type annotation whose type is `()` because it has no value.
So putting a whitespace rule in a group keeps the value of the group one.

```hpeg
%module Example.List

%{
import Data.Text (Text)
}%

Names :: [Text]
Names <- n:Name ns:(',' Sp Name)* { n : ns }   # The value of the group is the value of Name

Name :: Text
Name <- $[a-z]+ Sp

Sp <- [ \t]*
```

This rule has three provisos.

- If there is no element with a value other than `()`, values of `()` are counted. In a rule whose type annotation is not `()`, writing `Spaces <- Ws` makes the alternative return the value of `Ws`. In a rule whose type annotation is `()`, the value in this case is always `()` ([Omitting actions](#omitting-actions))
- A bound element (`u:Sp`) is always counted, even if it is `()`
- Whether a type annotation is `()` is decided by whether the string without whitespace is `()`. An alias such as `type Unit = ()` is not regarded as `()`

### Positions where values are not used

In positions where values are not used, the alternatives of a group may have values of different types ([ADR 0026](adr/0026-discard-unused-values.md)).
The positions where values are not used are inside a text capture `$e`, inside the lookaheads `&e` and `!e`, and the elements that are not bound in an alternative with an action.

```hpeg
%module Example.Word

%{
import Data.Text (Text, unpack)
}%

# Num is Int and Name is Text, but the value of the group is not used, since it is inside the capture
Word :: Text
Word <- $(Num / Name)

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }

Name :: Text
Name <- $[a-z]+
```

Conversely, in positions where the value of a group is used (a bound element, or an element that becomes the value of an alternative whose action is omitted), the values of all alternatives must have the same type.
If the types do not match, GHC reports it when compiling the generated module, pointing at the position in the `.hpeg` file.

### Bindings

The form `name:expr` gives a name to the value of an expression.
The name is referred to as a Haskell variable from actions, semantic predicates and the arguments of rules, so start it with a lower case letter.

```hpeg
# Fragment
Pair :: (Int, Int)
Pair <- '(' a:Num ',' b:Num ')' { (a, b) }
```

Bindings have the following constraints.

- Write them directly under the sequence of an alternative. A binding inside parentheses is not visible from the action outside
- They cannot be attached to an expression without a value
- The same name cannot be used twice in one alternative
- Names that start with an underscore cannot be used. They are reserved for the generator

When you want a value at a deeper position, split out a rule and bind it.

Which bindings code can see is decided by position ([ADR 0082](adr/0082-static-check-of-binding-references.md), [ADR 0083](adr/0083-bindings-inside-a-group-are-not-visible.md)).
An action sees all the bindings directly under the sequence of its alternative.
A semantic predicate and the arguments of a rule see the bindings directly under the sequence of the alternative that are to the left of their position.
A semantic predicate and arguments written inside parentheses see the bindings to the left of the parentheses.
A binding inside parentheses is not visible from any code, since the generated code does not bind it.
The parameters of the rule and the reserved bindings are visible from everywhere.
Referring to a name bound in the rule from a position where it is not visible is an error before generation.
The position of the error is the position of the name in the code.
Names that are not bound in the rule (the Prelude, imports, functions of verbatim blocks) are not checked, and GHC reports them when compiling the generated module.

Names in code are read at the lexical level.
Names inside string and character literals, line comments and block comments, and qualified names (`M.x`), and the fields of record field selections (`r.x`), are not regarded as references to bindings.
A name enclosed in backquotes (`` `div` ``) is regarded as a reference.

Common mistakes:

| Writing | Report |
|---|---|
| Bound an expression without a value (`c:[a-z]`) | `error: cannot bind c: the expression has no value (capture the text with $)` |
| Used the same name twice (`x:A x:A`) | `error: the binding x is used twice in this alternative` |
| A name that starts with an underscore (`_x:A`) | `error: the binding _x is reserved: names starting with an underscore belong to the generator` |
| A semantic predicate referred to a binding to its right (`&{ y > 0 } y:N`) | `error: the predicate refers to y, which is bound to its right` |
| An argument of a rule referred to a binding to its right or to its own binding (`x:A(y) y:B`, `x:A(x)`) | `error: the argument refers to y, which is bound to its right` |
| Referred to a binding inside parentheses (`(y:N) { y }`, `(y:N &{ y > 0 })*`) | `error: y is bound inside a group, which the code cannot see` |
| Referred to a binding of another alternative (`x:N { x } / M { x }`) | `error: x is not bound in this alternative` |
| A bound name is not used anywhere | lint: `warning: the binding x is not used [unused-binding]; remove x:` |

Writing `c:[a-z]` as `c:$[a-z]` binds the matched character as a `Text`.
The warning about unused bindings is not given in grammars with `%syntax`.
This is because in grammars with `%syntax`, the name of a binding is also the name of an accessor of the syntax tree.
A binding whose name is written only inside strings or comments is an unused binding.

### Reserved bindings

The generator binds the following names automatically.

| Name | Value | Where it can be used | ADR |
|---|---|---|---|
| `_span` | The range of input that the alternative consumed (`Span`) | Actions | [ADR 0008](adr/0008-source-positions.md) |
| `_env` | The value of the environment declared with `%env` | Actions, semantic predicates, arguments of rules | [ADR 0012](adr/0012-context-sensitive-extensions.md) |
| `_col` | The column of the position being evaluated (starting at 0) | Semantic predicates, arguments of rules | [ADR 0012](adr/0012-context-sensitive-extensions.md) |

## Actions

Writing `{ Haskell expression }` at the end of an alternative makes the expression the value of the alternative.
The type of the expression must match the type annotation of the rule.

```hpeg
# Fragment
Signed :: Int
Signed <- '-' n:Num { negate n }
        / n:Num     { n }
```

An action must be a pure expression.
In parsing left recursion, the same action may be evaluated more than once.

peg-hs reads an action by counting the balance of braces.
Brackets inside Haskell string literals and character literals are not counted, so `{ pack "}" }` is read correctly.
Brackets inside a block comment `{- -}` are counted, so do not write block comments in actions.

When an action has a type error, GHC reports the error at the line and column of the `.hpeg` file, not of the generated file ([ADR 0014](adr/0014-generated-module-api.md)).

Common mistakes:

| Writing | Report |
|---|---|
| An action with unbalanced brackets (`{ f ) }`) | `error: unbalanced bracket in Haskell code` |
| Forgot to close an action | `error: unterminated Haskell code` |
| An unclosed string literal (`{ "abc }`) | `error: unterminated string literal` |
| Wrote an action inside a group (`('a' { 1 })`) | `error: actions are not allowed inside a group` |

Actions cannot be written inside a group.
When you want to rework the value of a group, split the group out into a rule.

### Omitting actions

An alternative with exactly one element with a value can omit its action.
The value of that element becomes the value of the alternative as it is.
The second alternative of `Signed` above may be written as follows.

```hpeg
# Fragment
Signed :: Int
Signed <- '-' n:Num { negate n }
        / Num
```

For the same reason, an action that returns a bound value as it is can be omitted together with the binding.
In `Paren <- '(' Sp e:Expr ')' Sp { e }`, values of `()` are not counted, so the only element with a value is `Expr`.
`Paren <- '(' Sp Expr ')' Sp`, without the binding and the action, also returns the value of `Expr`.
`peg-hs lint --verbose` gives the info `omittable-identity-action` for bindings and actions that can be removed in this way ([ADR 0065](adr/0065-omittable-identity-actions.md), [lint](#lint)).
However, it is not given when removing the binding changes the value, or when the binding has another role.

- The code of the action is not only the name of the binding, apart from whitespace (`{ negate n }`, `{ (n) }`)
- The name is also used in a semantic predicate or an argument of a rule in the same alternative (`n:Num &{ n > 0 } { n }`)
- There are other bound elements. Or, removing the binding makes two or more elements that are counted as elements with values
- The grammar has `%syntax`. A binding is also the name of an accessor of the syntax tree, so removing it removes a function of the generated module

Omitting the action of an alternative with zero, or two or more, elements with values is an error.
How they are counted is as described in [Values of `()` are not counted](#values-of--are-not-counted).

However, there is an exception for rules whose type annotation is `()` ([ADR 0063](adr/0063-omit-unit-actions.md), [ADR 0064](adr/0064-unit-rules-always-return-unit.md)).
A rule without a type annotation whose type is `()` is treated in the same way.
An alternative without any element with a value other than `()` can omit its action, and its value is `()`.
This is because the only value of a rule of type `()` is `()`, so writing `{ () }` adds no information.

```hpeg
# Fragment
Sp :: ()
Sp <- ' '*                # Zero elements with values

Kw :: ()
Kw <- 'if' ![a-z] Sp      # One element of ()

Gap :: ()
Gap <- Sp ',' Sp          # Two elements of ()

Spaces :: ()
Spaces <- Sp+             # The value of the element is [()], but the value of the alternative is ()
```

There may be any number of elements of `()`, and they may include bound elements (`u:Sp`).
Even if the counted element is a single one with a value of `[()]` or `Maybe ()`, such as `Sp+` or `Sp?`, the value of the alternative is `()`.
Whether a type annotation is `()` is decided by the string without whitespace, as in [Values of `()` are not counted](#values-of--are-not-counted).
For a rule expanded from a template, it is decided by the type annotation after the type variables are substituted.

This exception has three limits.

- An alternative without elements (the latter alternative of `S <- 'a' / { () }`) cannot omit its action. Write `{ () }` for an empty alternative
- An alternative with exactly one element with a value other than `()` returns that value, as before. If its type does not match `()`, GHC reports a type error. However, rules with neither a type annotation nor an action ([Inferring and generating types](#inferring-and-generating-types)) and rules without a type annotation in grammars with `%syntax` ([Grammars without types](#grammars-without-types)) are treated separately
- Rules whose type annotation is not `()` are not covered by the exception. An alias such as `type Unit = ()` is not regarded as `()` either

Writing an omittable `{ () }` is not an error.
`peg-hs lint --verbose` gives the info `omittable-unit-action` for it ([lint](#lint)).

Common mistakes:

| Writing | Report |
|---|---|
| `Flag <- 'on'` (in a rule whose type annotation is `Bool`, zero elements with values) | `error: an alternative without an action must have exactly one element with a value, but it has none` |
| `Pair <- Num Num` (in a rule whose type annotation is `(Int, Int)`, two elements with values) | `error: an alternative without an action must have exactly one element with a value, but it has 2` |

Write the first as `Flag <- 'on' { True }`.
For the second, bind the two values and build the value in an action.
If neither the type annotation nor an action is written, `Pair` becomes a rule whose type is generated, and it is not an error ([Inferring and generating types](#inferring-and-generating-types)).

### Inferring and generating types

In a grammar without `%syntax`, the type of a rule without a type annotation and with no action in any alternative is decided from the values of its alternatives ([ADR 0075](adr/0075-generated-types-for-rules-without-actions.md)).
This removes, mechanically from the shape of the grammar, the work of writing the types of values in verbatim blocks and building the values with type annotations, bindings and actions.

| Category | Condition | Type of the rule | Value of an alternative |
|---|---|---|---|
| Rule of `()` | No alternative has an element with a value other than `()` | `()` | `()` |
| Rule whose type is inferred | Every alternative has exactly one element with a value other than `()`, and their types are all the same | That type | The value of that element |
| Rule whose type is generated | Otherwise | The generated type | A constructor applied to the values of the elements |

```hpeg
%module Example.Generated

Expr <- Expr '+' Sp Atom # Its type is generated. The numbers of values are 2 and 1
     / Atom

Sp <- ' '* # A rule of ()

Num <- $[0-9]+ Sp # Its type is inferred. The type is Text

Paren <- '(' Sp Expr ')' Sp # Its type is inferred. The type is Expr

Atom <- Num # Its type is generated. Text and Expr differ
     / Paren
```

For each rule whose type is generated, the generated module declares and exports the following types.

```haskell
data Expr = Expr1 Expr Atom | Expr2 Atom
  deriving (Eq, Show)

data Atom = Atom1 Text | Atom2 Expr
  deriving (Eq, Show)
```

`parse "1+2"` returns `Right (Expr1 (Expr2 (Atom1 "1")) (Atom1 "2"))`.
`Paren` returns only one value, so it returns the value of `Expr` without wrapping it in a constructor.

Since rules call each other, the categories are decided by a fixed point in two stages.
First, all rules are regarded as rules of `()`, and rules with an alternative that has a value other than `()` are moved to rules that are not `()`.
Values are counted as in [Values of `()` are not counted](#values-of--are-not-counted), and `[()]` and `Maybe ()` are also regarded as values of `()`.
Next, among the rules that are not `()`, rules with an alternative whose number of values is not 1 are decided to be rules whose type is generated.
The types of the remaining rules are inferred from the types of the elements ([Expressions with values](#expressions-with-values)).
Rules in which two different types appear, and rules whose type is never decided, are moved to rules whose type is generated.

Whether two types are the same is decided by comparing the strings of the types without whitespace.
`[Int]` and `[ Int ]` are the same type, while `Text` and its alias `Name` (`type Name = Text`) are different types.
The type of a call of a template is the type of the type annotation of the expanded rule, and a type substituted for a type variable is enclosed in parentheses (`[(Int)]`).
When types cannot be compared, the decision falls on the side of generating a type, so the types of the generated module never fail to match.

The generated types are made as follows.

- The name of the type is the rule name with its first letter in upper case. A rule name that starts with a character without case gets `Rule'` before it (the type of `値` is `Rule'値`)
- One constructor is made for each alternative. An alternative with only one value is also wrapped in a constructor
- The name of a constructor is the same as the name of the type if there is one alternative, and the name of the type followed by the number of the alternative (from 1) if there are two or more (`Expr1`, `Expr2`)
- The arguments of a constructor are the values of the elements of the alternative with values other than `()`, in the order they appear. Whether they are bound does not matter
- An alternative without elements with values becomes a constructor without arguments
- A type with one constructor with one argument is made a `newtype`
- The type is exported with its constructors (`Expr(..)`). When `peg-hs gen --export` narrows the entry points, only the types reachable from the types of the exported entry points are exported

Writing `@Name` at the end of an alternative (the position where an action is written) makes it the name of the constructor of that alternative.
A rule with `@Name` has its type generated, even when its type could be inferred.
The default names change with the order of the alternatives, so fix them with `@Name` in a grammar that will be used for a long time.
A code action of the language server writes out the default names as `@Name`.

```hpeg
# Fragment
Expr <- Expr '+' Sp Atom @Add
     / Atom @Single
```

The generated types derive `Eq` and `Show` by default.
Writing `%deriving Eq, Ord, Show` changes the derived classes, and `%deriving` without arguments derives nothing.
If a user type written in a type annotation appears in the arguments of a constructor and that type has no instance of a class, it is an error of GHC.
In that case, reduce the classes derived with `%deriving`, or write the instances.

Rules whose type is inferred and rules whose type is generated can be called from rules with type annotations and actions.
The action of the caller receives a value of the inferred type or the generated type.
Bindings may be written, and the bound values can be read from semantic predicates and the arguments of rules.
If even one alternative has an action, the rule is out of scope, and its type is `()` when there is no type annotation.

This way of writing is slower than a grammar with type annotations and actions.
This is because it makes the captured `Text` and the constructors whether or not they are used.
On a JSON document of 800,000 characters, compared with a grammar with type annotations and actions, the time was about 0.97 times and the peak live memory was about 1.18 times ([docs/benchmarks/2026-11-06-json-generated-types.md](benchmarks/2026-11-06-json-generated-types.md)).
These figures are for using the values of the generated types as they are, and do not include the time to convert them into the user's types.
Write type annotations and actions by hand only for the rules that need speed.
Since this can be chosen rule by rule, only the rules that take time can be rewritten.

Common mistakes:

| Writing | Report |
|---|---|
| Wrote `@Name` in a rule with a type annotation | `error: @Add names a constructor, but rule Expr has a type annotation` |
| Wrote `@Name` in a rule with an action | `error: @Add names a constructor, but rule Expr has an action` |
| Wrote `@Name` in a rule of `()` | `error: @Add names a constructor, but rule Sp has type (): no alternative has a value other than ()` |
| Wrote `@Name` in a grammar with `%syntax` | `error: @Add names a constructor, but the grammar has %syntax` |
| A name that starts with a lower case letter (`@add`) | `error: the constructor name add must start with an upper case letter` |
| Wrote the same name twice | `error: the constructor Add is defined twice in rule Expr; name one of the alternatives with @Name` |
| A default name is the same as the name of the type of another rule (`S <- S1 / ...` and a rule `S1`) | `error: the constructor S1 of rule S has the name of the type of rule S1; name the alternative with @Name` |
| The names of types are the same (`expr` and `Expr`) | `error: the rules expr and Expr have the same type name Expr; rename one of them` |
| Wrote `%deriving` twice | `error: duplicate %deriving directive` |
| Wrote something that is not a class name (`%deriving eq`) | `error: %deriving expects class names, but got eq` |

In grammars with `%syntax`, the type of a rule without a type annotation is `()`, as before ([Grammars without types](#grammars-without-types)).
A group with two or more elements with values (`(a:A ',' b:B)*`) has no value, so when you need a value, split the group out into a rule.

### Syntax trees with positions

Inside an action, `_span` refers to the range of input that the alternative consumed ([ADR 0008](adr/0008-source-positions.md)).
A `Span` has a start position and an end position, and a position consists of a byte offset, a line and a column.
It is used to give positions to the nodes of a syntax tree.

```hpeg
%module Example.Located
%export Expr(..)

%{
import Data.Text (unpack)
import Peg.Runtime (Span)

data Expr = Lit Span Int | Add Span Expr Expr
  deriving (Show)
}%

Expr :: Expr
Expr <- l:Expr '+' r:Lit { Add _span l r }
      / Lit

Lit :: Expr
Lit <- n:Num { Lit _span n }

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

The type of the syntax tree `Expr` is exported with `%export` so that the user's code can use it.
`Span` and the type of positions `Pos` are exported by `Peg.Runtime` of peg-runtime.

The start of the range is the position where the evaluation of the alternative started, and the end is the position where input was last consumed.
Lookaheads and semantic predicates do not consume input, so they do not move the range of `_span`.
When you want the position of a point in the middle of an alternative, split that part out into a rule, and take `_span` in the action of that rule.

## Rule templates

Writing parameters in angle brackets right after a rule name makes the rule a template ([ADR 0031](adr/0031-rule-templates.md)).
Templates are for writing only once a shape that appears many times in a grammar, such as keywords or sequences with separators.
The arguments are expressions, and in the body of a template, a parameter is written like a nonterminal.

```hpeg
%module Example.Print

%{
import Data.Text (Text)

data Stat = SPrint [Text]
  deriving (Show)
}%

Stat :: Stat
Stat <- K<'print'> xs:List<Name, ','> { SPrint xs }

Name :: Text
Name <- $[a-z]+ Sp

Sp <- [ \t]*

# A keyword: a literal not followed by a character of an identifier, then whitespace
K<w> :: ()
K<w> <- w ![a-zA-Z0-9_] Sp

# A sequence of one or more items with separators
List<p :: a, sep> :: [a]
List<p, sep> <- x:p xs:(sep Sp p)* { x : xs }
```

This grammar turns `print a, b` into `SPrint ["a","b"]`.
`K<'print'>` does not match the start of `printer`.

- Do not put whitespace between the rule name and `<`. `<-` is the arrow of a definition, as before
- Any expression, including choices and sequences, can be written as an argument. Enclose an expression that contains a comma or `>` in parentheses
- A parameter whose value is used (a parameter that the body binds, or returns by omitting the action) declares a type variable in the type annotation, in the form `p :: a`. At each call, the type variable is replaced by the type of the argument
- A parameter without a declared type (`w` and `sep` above) is treated as having no value inside the body
- Only expressions whose type is known, such as calls of rules, text captures and calls of templates, can be passed to a parameter with a declared type

The generator expands the calls of a template into a rule for each combination of arguments.
Each expanded rule has its own memo table, and left recursion is also parsed on the rules after expansion.
In grammars with `%syntax`, a call of a template does not make a node, and places its children in the caller.
Errors inside an expanded rule are reported at the position of the definition of the template.

Templates cannot be written in `%start`, `%entry`, `%recover`, `%nomemo`, `%token`, `%trivia` or `%inline`.

### Template arguments that use the caller's parameters

Inside the arguments of a template, the parameters of the calling rule ([Parameterized rules](#parameterized-rules)) can be used ([ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)).
Even in a grammar that passes the depth of indentation as a parameter, the shape "the same thing repeated with blank lines between" can be written only once.

```hpeg
%module Example.Items

Doc <- Items(0)

Items(ind :: Int) :: ()
Items <- Lines<Item(ind)>

# p repeated with newlines between
Lines<p> :: ()
Lines<p> <- p ('\n' p)*

# An item after exactly ind spaces
Item(ind :: Int) :: ()
Item <- ' '* &{ _col == ind } '-'
```

An expanded rule receives the caller's parameters that the arguments used, with the same names and types.
`Lines<Item(ind)>` above becomes a call of `Lines'0(ind)`, and `Lines'0` becomes a parameterized rule with the parameter `ind :: Int`.

- What is taken in are the names that appear in the Haskell fragments of the arguments (the arguments of calls of rules, and semantic predicates). Qualified names (`M.ind`), names inside string and character literals, and reserved bindings (`_env`, `_col`, `_span`) are not counted
- When two or more parameters are taken in, they are ordered by name. Their types are those written in the type annotation of the caller
- When the template is called with the same arguments from another rule, the same expanded rule is used if the types of the parameters taken in are the same, and a different rule otherwise
- When the body of a template calls a template, the parameters are passed on to the inner template too
- An expanded rule with parameters taken in is a parameterized rule, so it cannot take part in left recursion. The error is reported at the position of the definition of the template

The arguments of a template cannot use the bindings of the caller's alternative (`x` in `x:N`).
The type of a binding is not known without inferring it from the bound expression, so the type of the parameter of the expanded rule cannot be written.
When you want to pass the value of a binding to a template, pass it as a value argument, described in the next section.

A name cannot be taken in if it is the same as a binding or a name in the code of the body of the template, or the name of a value parameter of the template.
The arguments of a template are embedded in its body, so an `x` in an argument placed after a binding `x` of the body refers to the binding of the body, not to the caller's parameter.
In this case, rename the caller's parameter.

### Value arguments of templates

A template can have Haskell value parameters, the same as a parameterized rule ([ADR 0055](adr/0055-templates-and-parameterized-rules-in-stages.md)).
The value parameters are written after the template parameters in the type annotation, and not in the definition.
They pass things that are used as values in the body, such as the depth of indentation.

```hpeg
%module Example.Indented

Doc <- Indented<Item(0)>(0)

# p indented to depth n, repeated with newlines between
Indented<p>(n :: Int) :: ()
Indented<p> <- Ind(n) p ('\n' Ind(n) p)*

Item(ind :: Int) :: ()
Item <- '-' (' ' Indented<Item(ind + 2)>(ind + 2))?

# Exactly n spaces
Ind(n :: Int) :: ()
Ind <- ' '* &{ _col == n }
```

In a call, the value arguments are written right after the `>` of the template arguments (`Indented<Item(ind + 2)>(ind + 2)`).
Do not put whitespace between `>` and `(`.
`Lines<p> (x)` is, as before, a sequence of a call of a template and a parenthesized group.
This is the same rule as for the call of a parameterized rule `Name(args)`.

An expanded rule has as its parameters the value parameters of the template (in the order of declaration), followed by the parameters taken in from the caller (in the order of name).
`Indented<Item(ind + 2)>(ind + 2)` above becomes a call of `Indented'1(ind + 2, ind)`.

- The expressions of the value arguments are evaluated in the caller. As in the call of a parameterized rule, they can use the caller's parameters, the bindings to their left, `_env` and `_col`
- Expanded rules are not split by the values of the value arguments. The values are passed at run time, and are keys of the memo table
- A template has one or more template parameters (`<...>`). A rule that has only value parameters is a parameterized rule

Common mistakes:

| Writing | Report |
|---|---|
| Called a template without arguments (`K`) | `error: the template K needs arguments: K<...>` |
| A different number of arguments (`K<'a', 'b'>`) | `error: the template K expects 1 argument(s), but got 2` |
| Passed a literal to a parameter with a declared type (`List<'a', ','>`) | `error: the argument for p must be a rule, a capture or a template call, since its value is used` |
| Different parameter names in the type annotation and the definition (`K<w> ::` and `K<v> <-`) | `error: the template parameters of the definition of K do not match its type annotation` |
| Put whitespace between the rule name and `<` (`K <'a'>`) | A syntax error, such as `error: expected a rule, a directive or %{ ... }%` |
| Named a template, as in `%entry K` | `error: the template K cannot be named in %entry` |
| Called a rule that is not a template with angle brackets (`B<'x'>`) | `error: rule B is not a template` |
| A template calls templates without end (`T<p> <- T<(p p)>`) | `error: the expansion of the template T does not end: templates call templates more than 64 levels deep` |
| An argument of a template used a binding of the caller (`x:N Lines<Item(x)>`) | `error: the argument of the template Lines uses the binding x, which a template cannot take; pass it as a value argument` |
| Passed value arguments to a template that declares no value parameters (`Lines<Item>(1)`) | `error: the template Lines takes no value arguments` |
| A different number of value arguments (`Indented<Item>(1, 2)`) | `error: the template Indented expects 1 value argument(s), but got 2` |
| Wrote value parameters on the side of the definition of the template (`Indented<p>(n :: Int) <- ...`) | `error: parameters belong to the type annotation, not the definition` |
| An argument of a template that uses `x` in its body used the caller's parameter `x` | `error: the template T uses the name x in its body, so its argument cannot take the parameter x of the rule B; rename the parameter` |

## Left recursion

A rule can call itself at its left end ([ADR 0001](adr/0001-bounded-left-recursion.md)).
Direct left recursion makes left-associative values.
When you want right associativity, write it with right recursion.

```hpeg
# Fragment
Sub :: Int
Sub <- l:Sub '-' r:Num { l - r }   # 10-3-2 is (10-3)-2, that is, 5
     / Num

Pow :: Int
Pow <- b:Num '^' e:Pow { b ^ e }   # 2^3^2 is 2^(3^2)
     / Num
```

Indirect left recursion through several rules can also be written.
The precedence of operators is expressed by the hierarchy of rules.

```hpeg
%module Example.Calc

%{
import Data.Text (unpack)
}%

Expr :: Int
Expr <- l:Expr '+' r:Term { l + r }
      / l:Expr '-' r:Term { l - r }
      / Term

Term :: Int
Term <- l:Term '*' r:Factor { l * r }
      / Factor

Factor :: Int
Factor <- '(' Expr ')'
        / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }
```

`parse "2*(3+4)"` returns `Right 14`.

Left recursion has two constraints.
Parameterized rules cannot take part in left recursion.
The memoization of rules that take part in left recursion cannot be turned off.

Common mistakes:

| Writing | Report |
|---|---|
| A parameterized rule is left-recursive (`E(n :: Int)` and `E <- l:E(n) '+' ...`) | `error: rule E takes parameters and cannot take part in left recursion` |
| Put `%nomemo` on a left-recursive rule | `error: rule E takes part in left recursion and must be memoised` |

## Context-sensitive syntax

A standard PEG decides a match by looking only at the input from the current position onward.
Languages whose structure is decided by indentation, and languages whose interpretation changes with definitions elsewhere in the document, cannot be written with that alone.
The following four extensions are for such syntax ([ADR 0012](adr/0012-context-sensitive-extensions.md)).

Every extension is designed so that the result of a rule is decided only by "the combination of the rule, its arguments and the position, and the parse environment".
So they do not harm the correctness of memoization and of the parsing of left recursion.
No state that is rewritten during the parse is provided.

### Semantic predicates

`&{ expr }` succeeds without consuming input when the Haskell boolean expression is true.
`!{ expr }` succeeds when it is false.

```hpeg
# Fragment
Byte :: Int
Byte <- n:Num &{ n < 256 } { n }
```

The expression can refer to the bindings to the left of the predicate in the same alternative, the parameters of the rule, `_env` and `_col`.
A failure of a semantic predicate does not add items to the expected list of the error.
The report of a position that failed only because of semantic predicates is the position only, as in `line:column: parse error`.

### Parameterized rules

A rule can take Haskell values as arguments.
The names and types of the parameters are declared in the type annotation, and a call passes Haskell expressions.

```hpeg
# Fragment
Indent(w :: Int) :: ()
Indent <- &{ _col >= w }
        / ' ' Indent(w)
```

This rule reads spaces until the column reaches `w`.
The memo table keeps results for each value of the arguments in addition to the rule and the position, so the rule may be called at the same position with different arguments.

- Do not put whitespace between the rule name and `(`. `A(x)` is a call, and `A (x)` is a sequence of the nonterminal `A` and a parenthesized group
- The types of the parameters must be instances of `Ord`. Otherwise, GHC reports it when compiling the generated module
- A parameterized rule cannot be the start rule, a rule of `%entry` or a recovery rule. This is because there is no value to pass from an entry point
- If the arguments take many different values, the memory of the memo table grows. Use them for purposes with a small range of values, such as the width of indentation

Common mistakes:

| Writing | Report |
|---|---|
| Called a rule that takes no arguments in the form `B(1)` | `error: rule B takes no arguments` |
| A different number of arguments (`Indent`) | `error: rule Indent expects 1 argument(s), but got 0` |
| Wrote parameters on the side of the definition (`A(n :: Int) <- ...`) | `error: parameters belong to the type annotation, not the definition` |
| A parameter in the type annotation without a type (`A(n) :: ()`) | `error: expected a parameter of the form name :: Type` |
| An empty argument (`B()`) | `error: expected an argument` |
| The start rule takes parameters | `error: the entry rule A cannot take parameters` |

### The parse environment

`%env` declares the type of a value that does not change through the whole parse.
The entry points of a grammar that declares it take the environment as their first argument.
Inside rules, it is referred to with `_env`.

```hpeg
%module Example.Link
%env Set Text

%{
import Data.Set (Set, member)
import Data.Text (Text)
}%

Link :: Text
Link <- '[' l:$[a-z]+ ']' &{ member l _env } { l }
```

The entry point of this grammar is `parse :: Set Text -> Text -> Either ParseError Text`.
`[foo]` parses successfully only when the set of the environment contains `foo`.

Syntax that refers to definitions later in the document is handled with two parses.
The first parse collects the definitions, and passes them as the environment to the second parse.

### Column references

`_col` is the column of the position being evaluated, counted from 0.
One code point counts as one column.
Declaring `%tabstop 4` counts a tab as advancing to the next column that is a multiple of 4.
Without the declaration, a tab is also one column.

`_col` is a value used to decide matches, and is different from the column used to show the positions of errors (counted from 1, and not affected by `%tabstop`).

`_col` cannot be referred to from actions.
When you want the column as a value, go through a rule that takes the column as an argument and returns it as it is.

```hpeg
%module Example.Column

Item :: Int
Item <- ' '* Col(_col) 'a'

# Reads nothing, and returns the received column as its value
Col(c :: Int) :: Int
Col <- { c }
```

Parsing `   a` gives the value `3`, the column just before `a`.

In deciding indentation, the reference column passed to a rule can be the logical column where a prefix ends, instead of `_col` at a character boundary.
In CommonMark, the prefix of a container can end in the middle of a tab.
A tab is one character, so `_col` can only be the column before or after the tab.
If a rule computes the column where the prefix ends and passes it as an argument, the rest of the tab counts as the indentation of the content ([ADR 0018](adr/0018-tab-partial-consumption.md)).

## Turning off memoization

By default, the results of all rules are recorded in the memo table for each position, and the same rule is never evaluated twice at the same position.
For rules that are hardly ever called twice at the same position, such as whitespace and one-character tokens, turning off memoization with `%nomemo` reduces memory ([ADR 0017](adr/0017-nomemo-implementation.md)).

```hpeg
# Fragment
%nomemo Ws
%nomemo Hex
```

Turning off memoization does not change the results of parsing or the reports of failures.
However, turning off the memoization of a rule that is called many times inside deep backtracking makes the parse time no longer proportional to the length of the input.
Compare benchmarks before and after turning it off.
It cannot be specified for rules that take part in left recursion ([Left recursion](#left-recursion)).

## The generated module

### Entry points

The generated module exports `parse`, the entry point of the start rule ([ADR 0014](adr/0014-generated-module-api.md)).
For the rules specified with `%entry`, entry points with the rule name appended are added.
Adding `%entry Term` to the grammar `Example.Calc` above makes the generated module export the following two.

```haskell
parse     :: Text -> Either ParseError Int   -- the start rule Expr
parseTerm :: Text -> Either ParseError Int
```

An entry point requires the whole input to be consumed.
If input is left after the rule succeeds, the parse fails.

The generated module exports only the entry points, the generated types ([Inferring and generating types](#inferring-and-generating-types)) and the names listed in `%export`.
The entry points and the names of `%syntax` can be narrowed to those used, with `peg-hs gen --export NAME` ([ADR 0061](adr/0061-select-generated-exports.md)).
A module with declarations removed does not give warnings about unused imports and top-level bindings. This is because imports and functions of verbatim blocks that only the actions of removed rules used become unused. Check for those errors in verbatim blocks by generating without `--export` ([ADR 0062](adr/0062-warnings-of-pruned-generated-modules.md)).
The internal implementation of rules is not exported.
In `%export`, write Haskell export items separated by commas, as in `%export Expr(..), prettyExpr`.

Common mistakes:

| Writing | Report |
|---|---|
| Wrote the same rule in `%entry` twice | `error: the rule A is named in %entry twice` |
| Wrote a parameterized rule in `%entry` | `error: the entry rule A cannot take parameters` |

### Parse failures

When a parse fails, the entry point returns a `ParseError`.
A `ParseError` has the position that got farthest in the input, and the list of terminals expected at that position ([ADR 0005](adr/0005-error-reporting.md)).
What enters the expected list are literals, character classes, any character, and the end of input.
Failures caused by negative lookaheads and semantic predicates do not add items to the list.

`renderParseError` of peg-runtime turns a failure into one line for humans.
Giving `1+*2` to the grammar `Example.Calc` above fails at the `*` in column 3, and is shown as follows.

```
1:3: expected '(' or [0-9]
```

With a trailing space, as in `1+2 `, the parse fails at column 4, expecting the terminals that can follow and the end of input.

```
1:4: expected '*', '+', '-', [0-9] or end of input
```

When the expected list is empty (when the parse failed only because of negative lookaheads or semantic predicates), only the position is shown, as in `line:column: parse error`.

### How positions are counted

The positions of errors and of `_span` are counted by the following conventions.

| Field | How it is counted |
|---|---|
| Byte offset | The number of UTF-8 bytes, with the start of the input as 0 |
| Line | Counted from 1. LF breaks a line. The CR of CRLF is one character at the end of the line, and a lone CR does not break a line |
| Column | Counted from 1. One code point is one column, and a tab is also one column |

## Lossless syntax trees

From a grammar with `%syntax`, in addition to the entry points that return typed values, entry points are generated that return a syntax tree that loses not a single character of the input string ([ADR 0019](adr/0019-lossless-syntax-tree.md)).
This is for lint tools and formatters that deal with whitespace and comments.
Making typed values carry whitespace and comments means picking up the values of whitespace in the actions of all rules, and missing it in even one place makes it impossible to restore the original string.
The syntax tree removes this work.

```hpeg
%module Example.CalcSyntax
%syntax
%token Num
%token Ws
%trivia Ws
%inline Sp

%{
import Data.Text (unpack)
}%

Expr :: Int
Expr <- l:Expr Sp '+' Sp r:Num { l + r }
      / Num

Num :: Int
Num <- ds:$[0-9]+ { read (unpack ds) }

Sp <- Ws?

Ws <- [ \t]+
```

The module generated from this grammar exports the following entry point in addition to `parse`.

```haskell
parseSyntax :: Text -> Either ParseError SyntaxNode
```

The syntax tree is made as follows.

- A call of a rule becomes a node whose kind is the rule name. A rule of `%inline` makes no node, and places its children in the caller
- A match of a rule of `%token` becomes one token without internal structure
- Other matches of terminals that are consecutive directly under the same node are put together into one anonymous token. `'<' '/'` becomes one token `</`, so write symbols you want to distinguish as rules of `%token`
- Lookaheads and semantic predicates add nothing to the tree. Attempts discarded by backtracking do not remain in the tree either
- The text of the syntax tree always equals the input string

At the entry points of the syntax tree, actions are not evaluated.
However, when semantic predicates or arguments of rules refer to the values of bindings, actions are evaluated to compute those values.

Common mistakes:

| Writing | Report |
|---|---|
| Wrote `%token` in a grammar without `%syntax` | `error: %token requires %syntax` (the same for `%trivia` and `%inline`) |
| Made a rule that is not `%token` `%trivia` | `error: %trivia A must name a %token rule` |
| Made the same rule both `%token` and `%inline` | `error: rule B cannot be both %token and %inline` |
| Made the start rule or a rule of `%entry` `%inline` | `error: the entry rule A cannot be %inline: the root of the syntax tree needs a kind` |
| Wrote an argument for `%syntax` | `error: %syntax takes no argument` |

### Typed accessors

For each rule other than `%token` and `%inline` rules, a type that wraps the node and an accessor for each binding are generated.
For the grammar above, they are as follows.

```haskell
newtype ExprSyntax = ExprSyntax SyntaxNode
castExprSyntax :: SyntaxNode -> Maybe ExprSyntax
exprL :: ExprSyntax -> Maybe ExprSyntax
exprR :: ExprSyntax -> Maybe SyntaxToken
```

The name of an accessor is the rule name with its first letter in lower case, joined with the name of the binding with its first letter in upper case.
The name of the type is the rule name with its first letter in upper case, followed by `Syntax`.
Haskell type names must start with an upper case letter, so a rule name that starts with a character without case, such as kanji, kana or `_`, gets `Rule'` before it (from `数式`, `Rule'数式Syntax` and `castRule'数式Syntax`).
When two rules have the same type name (such as `expr` and `Expr`), it is an error in grammars with `%syntax` ([ADR 0053](adr/0053-type-names-of-rules-without-case.md)).

| Writing | Report |
|---|---|
| A grammar with `%syntax` has `expr` and `Expr` | `error: the rules expr and Expr have the same type name ExprSyntax in the syntax tree; rename one of them` |

Changing the name of a binding changes the public API of the generated module.
When the name of an accessor is the same as a name in a verbatim block, it is an error of GHC.
Accessors skip tokens of the kinds of `%trivia`.

Besides these, constants of the kind of each rule (such as `syntaxKindExpr`), `nameOfSyntaxKind`, which returns the name of a kind, and `isTriviaSyntaxKind`, which returns whether a kind is trivia, are generated.
The functions for moving around and showing the syntax tree are in `Peg.Runtime.Syntax` of peg-runtime.
`debugTree nameOfSyntaxKind` turns a tree into a string that shows it with one element per line, indented.

### Grammars without types

If you use only the syntax tree, the values of rules are not needed.
In a grammar with `%syntax`, neither type annotations nor actions need to be written ([ADR 0068](adr/0068-untyped-rules-in-syntax-grammars.md)).

```hpeg
%module Example.CalcTree
%syntax
%token Num
%token Ws
%trivia Ws

Expr <- Expr Ws? '+' Ws? Term
     / Term

Term <- Term Ws? '*' Ws? Atom
     / Atom

Atom <- Num
     / '(' Ws? Expr Ws? ')'

Num <- $[0-9]+

Ws <- [ \t]+
```

`Num <- $[0-9]+` is an alternative with only one value, the value of the capture (`Text`).
In a grammar without `%syntax`, `Num` would be a rule whose type is inferred, and the type would be `Text` ([Inferring and generating types](#inferring-and-generating-types)).
In a grammar with `%syntax`, the value of an alternative whose action is omitted, in a rule without a type annotation, is `()`, whatever its elements.
There may be any number of captures, calls of rules with type annotations, and elements with values that are not `()`.
The values of the elements are discarded, and the string of digits remains in the syntax tree as a token of `Num`.
Values are read from the tree that `parseSyntax` returns, with accessors and `syntaxText`.

Bindings bind, as before.
The `n` of `n:Num &{ n > 0 }` can be read from the semantic predicate, so calling and binding a rule that needs a typed value (such as `Num :: Int`) lets you sort input by value.
Bindings are also the names of accessors.

The following rules are treated as before.

- Grammars without `%syntax`. The type of a rule without type annotations and actions is inferred or generated ([Inferring and generating types](#inferring-and-generating-types))
- Rules with type annotations. This includes rules written with `:: ()`. A type annotation is written because the rule is meant to return a typed value
- Alternatives with actions, and alternatives without elements

A rule meant to be used for typed values too, but whose type annotation was forgotten, loses its value without an error.
However, the value of that rule is `()`, so the code that uses the typed value (the action of the caller, or the user of the entry point) does not compile, and you notice it there.

The cost of making the syntax tree does not change with this way of writing.
On a JSON document of 800,000 characters, `parseSyntax` of this way of writing took about 1.2 times both the time and the peak live memory, compared with `parse` of a typed grammar without `%syntax` ([docs/benchmarks/2026-11-06-json-generated-types.md](benchmarks/2026-11-06-json-generated-types.md)).
An earlier measurement gave about 1.6 times the time and about 1.1 times the memory ([docs/benchmarks/2026-11-06-json-untyped-syntax.md](benchmarks/2026-11-06-json-untyped-syntax.md)).
Since it does not build values, it is faster than `parseSyntax` of a grammar with `%syntax` that has type annotations and actions.
When speed is needed, write type annotations and actions without `%syntax`.

## Recovery from syntax errors

`e ^label` throws the label `label` when `e` fails ([ADR 0021](adr/0021-error-recovery.md)).
Unlike an ordinary failure, a throw is passed outward as it is, without the ordered choice `/` trying the next alternative.
Only a throw inside a lookahead (`&e`, `!e`) is treated as an ordinary failure.

Labels have two roles.
One is to put the name of the label in the report of the error.
The other is to give a recovery rule with `%recover`, and get a result even from input that contains errors.

```hpeg
%module Example.Commands
%recover close CloseAtLineEnd

%{
import Data.Text (Text)

data Inline = Command Text | Words Text
  deriving (Show)
}%

Line :: [Inline]
Line <- Inline*

Inline :: Inline
Inline <- '[' name:$[a-z]+ (']' ^close) { Command name }
        / w:$[a-z ]+ { Words w }

# Reads nothing. Succeeds before the end of a line or of the input, and regards the command as closed without `]`
CloseAtLineEnd <- &('\n' / !.)
```

This grammar regards an unclosed `[name` as closed at the end of the line, and continues parsing.

Put a label only at a position where, if the parse fails there, no alternative can succeed.
Putting one at any other position makes input that could have been accepted by backtracking no longer accepted.
The `]` in the example above comes after `[` and a name have been read, so no input is left on which another alternative could succeed.

Common mistakes:

| Writing | Report |
|---|---|
| The rule of `%recover` is not defined | `error: undefined rule R` |
| Wrote two `%recover` for the same label | `error: the label l has more than one recovery rule` |
| Wrote a label that does not appear in the grammar in `%recover` or `%safe` | `error: the label m does not appear in the grammar` |
| The recovery rule takes parameters | `error: the recovery rule R cannot take parameters` |
| The arguments of `%recover` are not two | `error: %recover expects a label and a rule name` |
| Wrote a label inside a lookahead (`!('a' ^l)`) | lint: `warning: the label l has no effect: its throw inside the lookahead is a failure of the lookahead [ineffective-label]; remove ^l` |

A throw inside a lookahead becomes an ordinary failure of the lookahead, so a label put there has no effect.

### Checking the safety of labels

`peg-hs gen` checks whether the position of a label is safe (whether throwing there leaves the accepted input unchanged) ([ADR 0028](adr/0028-label-safety-check.md)).
Labels that may be unsafe are reported as warnings, and generation continues.

```
$ peg-hs gen Grammar.hpeg
Grammar.hpeg:3:11: warning: the label l may reject valid input: where it fails, the alternative at 3:28 can match
```

This example is the warning for `l` in `S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }`.
`ac` can be accepted by the second alternative, but with the label, the parse throws at the `'b'` of the first alternative and stops.
The latter half of the warning shows another path that can succeed after the failure.
Others include that a repetition can continue (`the repetition at line:column can continue`), that the parse can continue after the label (`the parse can continue at line:column`), and that the input can end after a rule of an entry point (`the input can end after the rule A, which is an entry`).

Each label is judged on the grammar with all other labels removed ([ADR 0029](adr/0029-label-safety-implementation-deviations.md)).
When the common parts of alternatives are compared, the other labels are also removed before comparing, so whether other labels are present does not change the judgement ([ADR 0056](adr/0056-label-insertion-and-template-deviations.md), [ADR 0087](adr/0087-other-labels-do-not-change-the-label-check.md)).
For nested labels, an outer label is treated as passing the failure of the inner one outward as it is.
So a grammar without any warning accepts the same input as the grammar with all labels removed.
This may warn about a label that is safe because other labels throw and stop the parse, but in return the guarantee is easier to understand.
Alternatives inside lookaheads are also checked, and the check ends where the failure reaches the boundary of the lookahead.

The check is an approximation that judges mainly by the next character of the input, and may warn about safe labels.
The following three are judged by looking further than one character ([ADR 0038](adr/0038-label-check-precision-and-strip-labels-entries.md)).

- **Common prefixes across calls of rules**: if a later alternative starts with the same elements that the failed alternative had read so far, that part is removed before comparing. A call of a rule at the start of a later alternative is expanded into the alternatives of that rule for comparing. For parameterized rules, the formal parameters are replaced by the actual arguments, and calls whose arguments match as tokens are regarded as the same (such as when `BadIndent` and `OrphanDef` in the choice `BadIndent(ind) / OrphanDef(ind)` both start with `Ind(ind)`)
- **Constant semantic predicates**: `&{ False }` and `!{ True }` are treated as never succeeding, and `&{ True }` and `!{ False }` as always succeeding
- **Known prefixes**: if the failed alternative starts with a literal (or a rule whose alternatives are literals only), the fact that the input starts with that string is used to check whether a later alternative always fails on that input (`!'%%'` after `'%%'`, `'[' Ident` after `'[='`, and so on)

Even so, rules that judge characters with semantic predicates (such as `c:$. &{ isAlpha c }`) are treated as able to succeed on any character.
When an alternative that starts with such a rule is nearby, warnings are more likely.
The magnitude of the values of arguments (such as the difference in the number of spaces that `Ind(n)` and `Ind(n + 2)` read) is not judged either.
A label inside an alternative that grows in indirect left recursion is judged neither safe nor unsafe, and is reported as `the label l cannot be checked: ...`.

For a label confirmed to be safe, stop the warning with `%safe`.
Write the reason in a comment.

```hpeg
# Fragment
# [[ and [ can be told apart by looking up to the second character
%safe table
```

`%safe` works by the name of the label.
If a label with the same name is used at several positions, all the warnings are stopped even if one position is unsafe, so it is better to give a different name to each position you have confirmed.
To confirm safety, generate the grammar with labels removed as another module with `peg-hs gen --strip-labels MODULE`, and write a test that compares the input it accepts with that of the original grammar.
`peg-hs gen --Werror` fails without generating if there are warnings.

#### Inserting safe labels

At positions the check can show to be safe, `peg-hs label` inserts labels all at once ([ADR 0054](adr/0054-automatic-label-insertion.md)).
The candidates are literals, character classes, `.`, references to rules, groups and `e+` (including those with `$`), that come after an element that always reads input in a sequence.
For each candidate, a provisional label is placed and checked, and only those judged safe are inserted.
So the accepted language does not change.
Then the grammar with the labels of all the remaining candidates is checked as `peg-hs gen` checks it.
If some of the labels are warned about, they are taken out of the candidates, and the check is made again until there is no warning ([ADR 0086](adr/0086-inserted-labels-pass-the-label-check.md)).
So `peg-hs gen` does not warn about the inserted labels.

```hpeg
%module Example.List

List :: [Int]
List <- '[' v:Num vs:(',' Num)* ']' !. { v : vs }

Num :: Int
Num <- [0-9]+ { 1 }
```

Running `peg-hs label --write` on this grammar makes the definition of `List` as follows.

```hpeg
# Fragment
List <- '[' v:Num ^List_Num vs:(',' Num ^List_Num_2)* ']' ^List_rbracket !. { v : vs }
```

`'['`, `','` and `[0-9]+` are at the start of a sequence, `(...)*` matches the empty string, and `!.` is a lookahead, so none of them is a candidate.
The name is `Rule_target`, and from the second of the same name on, `_2`, `_3` are appended.
In `S <- 'a' 'b' { () } / 'a' 'c' { () }`, the label of `'b'` rejects `ac`, so it is not inserted, and only `'c'` gets `^S_c`.

There are also positions where labels are not inserted.
They are not inserted inside an expression with a label that has `%recover`, or in the rules called from there. This is because the throw of a label without a recovery rule passes through the outer recovery, so an error that was being recovered from would turn into an error of the whole grammar.
They are not inserted in an alternative that always succeeds, about which `peg-hs lint` warns that "the later alternatives are never tried", or in the rules called from there either. This is because a label there would change the judgement of lint, and the warning about the alternatives that are never tried would disappear ([ADR 0056](adr/0056-label-insertion-and-template-deviations.md)).
Near rules that judge characters with semantic predicates, and inside indirect left recursion, the check cannot show safety even where it holds, so labels are not inserted there either.

Inserted labels do not recover.
For labels you want to recover, write `%recover` and a recovery rule.
The code action "Add `%recover`" of the language server adds `%recover name Recover_name` and a template of a recovery rule that skips up to just before the literal that follows the labelled expression in the same sequence (or up to just before the end of the line if there is none).
The action of the template is the typed hole `{ _ }`, so compiling the generated module makes GHC show the type. Look at it and fill in the value.

### Two modes

From a grammar that contains labels, both an entry point that does not recover and an entry point that recovers are generated.
For the grammar `Example.Commands` above, they are as follows.

```haskell
parse        :: Text -> Either ParseError [Inline]          -- does not recover
parseRecover :: Text -> (Maybe [Inline], [SyntaxError])     -- recovers
```

A grammar with `%syntax` also gets the recovering entry point that returns a syntax tree, `parseSyntaxRecover :: Text -> (SyntaxNode, [SyntaxError])`.

The entry point that does not recover stops at the first failure.
The thrown label goes into `parseErrorLabel` of the `ParseError`.

At an entry point that recovers, when a label is thrown and there is a recovery rule of `%recover`, the recovery rule is evaluated from the position of the throw.
If the recovery rule succeeds, the parse continues as if the labelled expression had succeeded with that value, and one syntax error is recorded.
If there is no recovery rule, or the recovery rule fails, the throw is passed further outward.

- A recovery rule cannot take parameters. Its type must be the same as the type of the value of the labelled expression. For a label put on an expression without a value, the value of the recovery rule is discarded
- When a recovery rule does not consume input (a recovery by insertion, such as supplying a closing bracket), the range of the syntax error is empty
- Syntax errors inside attempts discarded by backtracking are not reported
- If input is left after the start rule, all the rest is one syntax error. If the start rule cannot recover, the whole input is one syntax error

`parseSyntaxRecover` returns a syntax tree for any input.
A recovered range becomes a node of the kind `ERROR`, and the text of the syntax tree always equals the input.

Syntax errors are returned as a list of `SyntaxError`.
Each has the label, the range (byte offsets), the position of the start of the range, and the expected set at the time of the throw.
The mapping from labels to messages for users is kept by the user.

## lint

`peg-hs lint` warns about ways of writing that can be generated but clearly differ from what was meant ([ADR 0033](adr/0033-grammar-linter.md)).
peg-hs has a fixed set of rules, and they cannot be selected, added to, or stopped individually.
In return, every rule points only at problems that necessarily follow from the meaning of the grammar, so a warning always disappears when the grammar is fixed.

```
$ peg-hs lint Op.hpeg
Op.hpeg:4:7: warning: the alternative never succeeds: the alternative at 3:7 matches its prefix '=' first [unreachable-alternative]; move it before the alternative that matches the prefix
```

A warning consists of, in this order, the position, the message, the name of the rule in square brackets, and how to fix it after the semicolon.
There are the following four rules.

| Rule | Way of writing it warns about | Section |
|---|---|---|
| `unreachable-alternative` | An alternative that never succeeds, because an earlier alternative always succeeds or a literal of an earlier alternative is its prefix | [Operators](#operators) |
| `duplicate-alternative` | An alternative that is the same as an earlier alternative | [Operators](#operators) |
| `ineffective-label` | A label that has no effect inside a lookahead | [Recovery from syntax errors](#recovery-from-syntax-errors) |
| `unused-binding` | A binding that appears in none of the actions, semantic predicates and arguments of rules | [Bindings](#bindings) |

lint gives info, apart from warnings.
Info points out ways of writing that would make the grammar simpler if fixed, but are not errors if left as they are.
Whether to fix them is for the author of the grammar to decide, so `peg-hs lint` does not show info by default ([ADR 0067](adr/0067-lint-info-with-verbose.md)).
With `--verbose`, info is shown in the same form as warnings, written `info:` in place of `warning:`.
They are shown in the order of position, together with the warnings.
With or without `--verbose`, info does not change the exit status.
Like warnings, info cannot be selected or stopped.

```
$ peg-hs lint Sp.hpeg
$ peg-hs lint --verbose Sp.hpeg
Sp.hpeg:4:12: info: the action can be omitted: the rule has type () and the alternative has no value [omittable-unit-action]; remove { () }
```

The language server reports info as diagnostics with the severity Hint.
Many editors show Hints faintly, without underlining them.

There are the following three rules of info.

| Rule | Way of writing it points out | Section |
|---|---|---|
| `omittable-unit-action` | An omittable `{ () }` of a rule whose type annotation is `()`. The position points at the `{` of the action. An action inside a template only when it can be omitted in all expansions | [Omitting actions](#omitting-actions) |
| `omittable-identity-action` | An action that returns a bound value as it is, and can be omitted together with the binding (`e:Expr { e }`). The position points at the `{` of the action. Not given for grammars with `%syntax`. An action inside a template only when it can be omitted in all expansions | [Omitting actions](#omitting-actions) |
| `omittable-unit-annotation` | The type annotation `A :: ()`. The type of a rule without a value and without a type annotation is also `()`, so the whole line can be removed. The position points at the start of the type annotation. Not given for the type annotations of parameterized rules and templates | [Rules](#rules) |

Fixing a grammar as the warnings say does not change the input the grammar accepts or the positions of errors.
What can change is only "what was expected" in the message of an error, when an alternative is removed as the warning about a literal prefix says.
The latter alternative of `S <- '=' { () } / '==' 'x' { () }` never succeeds, but it is tried and fails when the input does not start with `=`, so the error for the empty input is `1:1: expected '=' or '=='`.
Removing the latter alternative makes the error `1:1: expected '='`.
That is, a token that would not get through even if typed disappears from the guidance of the error ([ADR 0049](adr/0049-lint-false-positive-test-and-expected-sets.md)).

The check of the safety of labels is not part of lint.
It is an approximate check that may warn about safe labels too, so it is not put in lint, which has no means of stopping warnings.
Even if `peg-hs lint` succeeds, check the safety of labels separately with the warnings of `peg-hs gen`.
`%safe` does not stop the warnings of lint.
