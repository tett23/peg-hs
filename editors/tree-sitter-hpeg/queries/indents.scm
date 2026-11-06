; Indents (ADR 0069). A line of a definition after its first, as an
; alternative starting with /, is aligned with the <- of the definition,
; which is how peg-hs fmt lays them out (ADR 0032).

((definition) @indent.align
  (#set! indent.open_delimiter "<-")
  (#set! indent.increment 0))

; Haskell code keeps the indent it is written with.
[
  (verbatim)
  (action)
  (predicate)
  (haskell)
] @indent.auto
