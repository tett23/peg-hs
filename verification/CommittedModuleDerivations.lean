import DerivationPeg
import DerivationPegSyntax
import DerivationExtensions
import RenderModuleGHC

/-
ADR 0097 invariant 3 for committed generated modules, with no premise on
embedded code.

check-ghc-parser-trace.sh regenerates three committed fixtures as
scripts/regen-fixtures.sh does, compares them byte for byte with the files in
the repository, and traces the committed files with GHC 9.10.3's lexer and
parser:
- packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs (from Peg.hpeg),
- packages/peg-grammar/src/Peg/Grammar/SelfHostedSyntax.hs (PegSyntax.hpeg),
- packages/peg-codegen/test/generated/Fixture/Extensions.hs (Extensions.hpeg,
  whose six %language extensions are LANGUAGE pragmas of the module).
The tracer starts from GHC2021, the default-language of the packages that
compile these files, and applies the module's header pragmas before it lexes
and parses (TraceGeneratedModule.hs; check-trace-language.sh shows that a
LANGUAGE pragma changes its verdict and its tokens). extract-happy-trace.awk
writes each trace as a certificate module (DerivationPeg, DerivationPegSyntax,
DerivationExtensions). In each, `source0` is the token word of the lexer's
callbacks on the committed file, and `invariant3_source_tokens` derives it
from GHC's module start symbol.

The theorems of RenderComposition and RenderFinalizeModule hold for any
grammar, so they take the ADR 0097 premise on embedded code as hypotheses
(`verbatim_split`, `verbatim_imports_ok`, `verbatim_decls_ok`, and `user_ok`
and `decls_ok` for the actions, predicates and types inside rule bodies). For
these three modules a certificate covers the whole token word: the verbatim
blocks, actions, semantic predicates, argument code and types of the two
metagrammars and of Extensions.hpeg are inside it. No premise on embedded code
is left for them.

Premise left explicit:
- `lexed` (invariant3_committed_text): GHC's lexer on the text gives the
  certificate's token word. It is observed (the LEXID callbacks of the trace,
  checked against the shifts by check-lexer-trace.awk), not derived from a
  Lean model of GHC's lexer.
-/

namespace PegHs.CommittedModuleDerivations

open CFG GHCGrammar

def certifiedWord (source : List Nat) : List Symbol :=
  source.map Symbol.terminal

-- The token words of the three committed modules.
inductive Certified : List Nat → Prop where
  | selfHosted : Certified Peg.source0
  | selfHostedSyntax : Certified PegSyntax.source0
  | extensions : Certified Extensions.source0

theorem invariant3_certified_word {source : List Nat} (certified : Certified source) :
    Derives (layoutGrammar productions) [.nonterminal moduleStart]
      (certifiedWord source) := by
  cases certified with
  | selfHosted => exact Peg.invariant3_source_tokens
  | selfHostedSyntax => exact PegSyntax.invariant3_source_tokens
  | extensions => exact Extensions.invariant3_source_tokens

theorem invariant3_committed_words :
    Derives (layoutGrammar productions) [.nonterminal moduleStart]
        (certifiedWord Peg.source0) ∧
      Derives (layoutGrammar productions) [.nonterminal moduleStart]
        (certifiedWord PegSyntax.source0) ∧
      Derives (layoutGrammar productions) [.nonterminal moduleStart]
        (certifiedWord Extensions.source0) :=
  ⟨invariant3_certified_word .selfHosted,
    invariant3_certified_word .selfHostedSyntax,
    invariant3_certified_word .extensions⟩

-- The conclusion of RenderFinalizeModule's theorems (the lexer's word on the
-- text derives from GHC's start symbol, nonterminal 0), with the lexer
-- observation as the only premise.
theorem invariant3_committed_text (ghcLex : String → List Symbol) (text : String)
    {source : List Nat} (certified : Certified source)
    (lexed : ghcLex text = certifiedWord source) :
    ghcLex text = certifiedWord source ∧
      Derives (layoutGrammar productions) [.nonterminal 0] (ghcLex text) := by
  refine ⟨lexed, ?_⟩
  rw [lexed]
  exact RenderModuleGHC.parse_module_source (invariant3_certified_word certified)

-- The certificates are of the whole modules, not of empty words.
theorem certified_words_nonempty :
    Peg.source0 ≠ [] ∧ PegSyntax.source0 ≠ [] ∧ Extensions.source0 ≠ [] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Peg.source0, PegSyntax.source0, Extensions.source0,
    Peg.lexer0, PegSyntax.lexer0, Extensions.lexer0]

end PegHs.CommittedModuleDerivations
