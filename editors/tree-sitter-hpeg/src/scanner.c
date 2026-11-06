// The external scanner of the .hpeg notation.
//
// The text of a verbatim block (ADR 0045), which ends before the first }%.
// With }}% the first } is text, which a regular expression of tree-sitter
// cannot say.
//
// The spaces before an argument of a directive (ADR 0069), which are a
// token only when something other than a comment follows them on the line.
// A token of spaces in the grammar would take in the spaces before other
// tokens.
#include "tree_sitter/parser.h"

enum TokenType { VERBATIM_BODY, DIRECTIVE_SPACE };

void *tree_sitter_hpeg_external_scanner_create(void) { return NULL; }

void tree_sitter_hpeg_external_scanner_destroy(void *payload) { (void)payload; }

unsigned tree_sitter_hpeg_external_scanner_serialize(void *payload, char *buffer) {
  (void)payload;
  (void)buffer;
  return 0;
}

void tree_sitter_hpeg_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
  (void)payload;
  (void)buffer;
  (void)length;
}

bool tree_sitter_hpeg_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
  (void)payload;
  if (!valid_symbols[VERBATIM_BODY]) {
    if (!valid_symbols[DIRECTIVE_SPACE]) return false;
    if (lexer->lookahead != ' ' && lexer->lookahead != '\t') return false;
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') lexer->advance(lexer, false);
    if (lexer->eof(lexer)) return false;
    switch (lexer->lookahead) {
      case '\n':
      case '\r':
      case '#':
        return false;
      default:
        lexer->result_symbol = DIRECTIVE_SPACE;
        return true;
    }
  }
  bool any = false;
  for (;;) {
    if (lexer->eof(lexer)) {
      // An unclosed block: its text, and the parser reports the missing }%.
      lexer->mark_end(lexer);
      lexer->result_symbol = VERBATIM_BODY;
      return any;
    }
    if (lexer->lookahead == '}') {
      // The token ends before this } if a % follows it.
      lexer->mark_end(lexer);
      lexer->advance(lexer, false);
      if (lexer->lookahead == '%') {
        lexer->result_symbol = VERBATIM_BODY;
        return any;
      }
      any = true;
      continue;
    }
    lexer->advance(lexer, false);
    any = true;
  }
}
