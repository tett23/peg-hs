/* The size of the linear memory of the reactor in bytes (ADR 0080): the
   pages of memory 0, of 65536 bytes each. Reactor.hs checks that a request
   lies inside it before it copies the request. */
unsigned long long peg_memory_size(void) {
  return (unsigned long long)__builtin_wasm_memory_size(0) * 65536ULL;
}
