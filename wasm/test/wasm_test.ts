// Tests of the wasm reactor (ADR 0078, ADR 0079), with a WASI that has only
// the functions of the import contract, as the page has.
//
//   PEG_HS_WASM=peg-hs.wasm PEG_HS_WASM_RAW=raw.wasm PEG_HS=/path/to/peg-hs \
//     deno test --allow-read --allow-write --allow-env --allow-run wasm/test
//
// PEG_HS_WASM is the wasm of scripts/build-wasm.sh, PEG_HS_WASM_RAW the one
// that wasm32-wasi-cabal built before the stubs were merged, and PEG_HS the
// native peg-hs to compare with.

// The assertions are written here, so that the tests need no packages.
const assert = (ok: boolean, message = "assertion failed"): void => {
  if (!ok) throw new Error(message);
};

// Equality of JSON values: the values compared here come from JSON.
const assertEquals = (actual: unknown, expected: unknown, message = ""): void => {
  const a = JSON.stringify(actual);
  const e = JSON.stringify(expected);
  if (a !== e) throw new Error(`${message}${message === "" ? "" : ": "}expected ${e.slice(0, 2000)}, got ${a.slice(0, 2000)}`);
};

const root = new URL("../../", import.meta.url).pathname;

const env = (name: string): string => {
  const v = Deno.env.get(name);
  if (v === undefined || v === "") throw new Error(`set ${name}`);
  return v;
};

// The import contract of ADR 0078.
const allowed = [
  "args_get",
  "args_sizes_get",
  "environ_get",
  "environ_sizes_get",
  "clock_time_get",
  "clock_res_get",
  "random_get",
  "fd_write",
  "proc_exit",
];

// The export table of ADR 0078.
const exportNames = ["memory", "_initialize", "hs_init", "malloc", "free", "analyze", "format"];

const ESUCCESS = 0;
const EBADF = 8;

type Exports = {
  memory: WebAssembly.Memory;
  _initialize: () => void;
  hs_init: (argc: number, argv: number) => void;
  malloc: (n: number) => number;
  free: (p: number) => void;
  analyze: (p: number, n: number) => number;
  format: (p: number, n: number) => number;
};

type Reactor = {
  exports: Exports;
  call: (name: "analyze" | "format", request: Uint8Array) => string;
  // The milliseconds from reading the bytes to the end of hs_init.
  startup: number;
};

// A WASI of the functions of the contract only: no arguments, no
// environment, the clocks, random bytes, and writes to stdout and stderr.
const wasi = (memory: () => WebAssembly.Memory) => {
  const view = () => new DataView(memory().buffer);
  const sizes = (count: number, size: number) => {
    view().setUint32(count, 0, true);
    view().setUint32(size, 0, true);
    return ESUCCESS;
  };
  const functions: Record<string, (...args: never[]) => number> = {
    args_get: () => ESUCCESS,
    args_sizes_get: sizes,
    environ_get: () => ESUCCESS,
    environ_sizes_get: sizes,
    clock_time_get: (_id: number, _precision: bigint, out: number) => {
      view().setBigUint64(out, BigInt(Math.round(performance.timeOrigin + performance.now())) * 1000000n, true);
      return ESUCCESS;
    },
    clock_res_get: (_id: number, out: number) => {
      view().setBigUint64(out, 1000n, true);
      return ESUCCESS;
    },
    random_get: (buf: number, len: number) => {
      crypto.getRandomValues(new Uint8Array(memory().buffer, buf, len));
      return ESUCCESS;
    },
    fd_write: (fd: number, iovs: number, count: number, written: number) => {
      if (fd !== 1 && fd !== 2) return EBADF;
      let total = 0;
      for (let i = 0; i < count; i++) {
        const p = view().getUint32(iovs + 8 * i, true);
        const n = view().getUint32(iovs + 8 * i + 4, true);
        const text = new TextDecoder().decode(new Uint8Array(memory().buffer, p, n));
        (fd === 1 ? Deno.stdout : Deno.stderr).writeSync(new TextEncoder().encode(text));
        total += n;
      }
      view().setUint32(written, total, true);
      return ESUCCESS;
    },
    proc_exit: (code: number) => {
      throw new Error(`proc_exit(${code})`);
    },
  };
  return functions;
};

const load = (): Reactor => {
  const t0 = performance.now();
  const module = new WebAssembly.Module(Deno.readFileSync(env("PEG_HS_WASM")));
  let memory: WebAssembly.Memory | undefined;
  const instance = new WebAssembly.Instance(module, {
    wasi_snapshot_preview1: wasi(() => memory!),
  });
  const exports = instance.exports as unknown as Exports;
  memory = exports.memory;
  exports._initialize();
  exports.hs_init(0, 0);
  const startup = performance.now() - t0;
  const call = (name: "analyze" | "format", request: Uint8Array) => {
    const p = exports.malloc(request.length);
    new Uint8Array(exports.memory.buffer, p, request.length).set(request);
    const r = exports[name](p, request.length);
    // The request is copied before the function returns (ADR 0078).
    exports.free(p);
    const n = new DataView(exports.memory.buffer).getUint32(r, true);
    const text = new TextDecoder("utf-8", { fatal: true }).decode(new Uint8Array(exports.memory.buffer, r + 4, n));
    exports.free(r);
    return text;
  };
  return { exports, call, startup };
};

const reactor = load();

type Diagnostic = { severity: string; line: number; column: number; message: string };
type Node = { kind: string; line: number | null; column: number | null; text: string | null; children: Node[] };
type Analysis = { diagnostics: Diagnostic[]; ast: Node | null; types: string | null; module: string | null };
type Formatted = { text: string | null; diagnostics: Diagnostic[] };

const encode = (v: unknown) => new TextEncoder().encode(JSON.stringify(v));
const analyze = (request: Record<string, unknown>): Analysis => JSON.parse(reactor.call("analyze", encode(request)));
const format = (grammar: string): Formatted => JSON.parse(reactor.call("format", encode({ grammar })));
const read = (path: string) => Deno.readTextFileSync(root + path);

const calcGenerated = [
  "%module Calc.Generated",
  "",
  "Expr <- Expr '+' Sp Term @Add",
  "     / Term",
  "",
  "Term <- Term '*' Sp Atom @Mul",
  "     / Atom",
  "",
  "Atom <- Num",
  "     / '(' Sp Expr ')' Sp",
  "",
  "Num <- $[0-9]+ Sp",
  "",
  "Sp <- ' '*",
  "",
].join("\n");

// The grammar files under a directory of the repository, without the test
// data of the conformance tests.
const grammarsUnder = (dir: string, ext: string): string[] =>
  [...Deno.readDirSync(root + dir)]
    .map((e) => ({ e, path: `${dir}/${e.name}` }))
    .sort((a, b) => (a.path < b.path ? -1 : 1))
    .flatMap(({ e, path }) =>
      e.isDirectory ? (e.name === "data" ? [] : grammarsUnder(path, ext)) : path.endsWith(ext) ? [path] : []
    );

const grammars = [
  ...grammarsUnder("conformance", ".hpeg"),
  ...grammarsUnder("packages/peg-codegen/test/fixtures", ".hpeg"),
  ...grammarsUnder("packages/peg-codegen/test/explicit", ".txt"),
];

// Run the native peg-hs in a fresh directory with the grammar at source;
// the file it writes at output, or null when it fails.
const native = async (args: (source: string) => string[], source: string, output: string, grammar: Uint8Array) => {
  const dir = await Deno.makeTempDir({ prefix: "peg-wasm-test" });
  try {
    for (const p of [source, output]) {
      const d = p.split("/").slice(0, -1).join("/");
      if (d !== "") await Deno.mkdir(`${dir}/${d}`, { recursive: true });
    }
    await Deno.writeFile(`${dir}/${source}`, grammar);
    const r = await new Deno.Command(env("PEG_HS"), { args: args(source), cwd: dir, stdout: "null", stderr: "null" }).output();
    return r.success ? await Deno.readTextFile(`${dir}/${output}`) : null;
  } finally {
    await Deno.remove(dir, { recursive: true });
  }
};

Deno.test("the imports are those of the contract", () => {
  const module = new WebAssembly.Module(Deno.readFileSync(env("PEG_HS_WASM")));
  const imports = WebAssembly.Module.imports(module);
  for (const i of imports) {
    assertEquals(i.module, "wasi_snapshot_preview1", `${i.module}.${i.name}`);
    assert(allowed.includes(i.name), `${i.name} is not in the contract`);
  }
});

Deno.test("the exports are those of the table", () => {
  const module = new WebAssembly.Module(Deno.readFileSync(env("PEG_HS_WASM")));
  assertEquals(WebAssembly.Module.exports(module).map((e) => e.name).sort(), [...exportNames].sort());
});

Deno.test("wasm/stubs.wat stubs the imports of the build outside the contract", () => {
  const raw = new WebAssembly.Module(Deno.readFileSync(env("PEG_HS_WASM_RAW")));
  const outside = WebAssembly.Module.imports(raw)
    .filter((i) => !allowed.includes(i.name))
    .map((i) => `${i.module}.${i.name}`)
    .sort();
  const stubs = [...read("wasm/stubs.wat").matchAll(/\(export "([^"]+)"\)/g)]
    .map((m) => `wasi_snapshot_preview1.${m[1]}`)
    .sort();
  assertEquals(stubs, outside);
});

Deno.test("JsonGenerated.hpeg has no diagnostics and generates data Value", () => {
  const t0 = performance.now();
  const r = analyze({ grammar: read("conformance/bench/JsonGenerated.hpeg") });
  const ms = performance.now() - t0;
  assertEquals(r.diagnostics, []);
  assert(r.types!.includes("data Value"));
  assert(r.module !== null);
  console.log(`load to the end of hs_init: ${reactor.startup.toFixed(1)} ms; analyze of JsonGenerated.hpeg: ${ms.toFixed(1)} ms`);
});

Deno.test("the README grammar generates data Expr", () => {
  const r = analyze({ grammar: calcGenerated });
  assertEquals(r.diagnostics, []);
  assert(r.types!.includes("data Expr = Add Expr Term | Expr2 Term"));
});

Deno.test("an undefined rule is an error at the reference", () => {
  const r = analyze({ grammar: "%module A\n\nS <- 'a' T\n" });
  assertEquals(r.diagnostics, [{ severity: "error", line: 3, column: 10, message: "undefined rule T" }]);
  assert(r.ast !== null);
  assert(r.types !== null);
  assertEquals(r.module, null);
});

Deno.test("a syntax error has no ast, types or module", () => {
  const r = analyze({ grammar: "%module A\n\nS <- ('a'\n" });
  assertEquals([r.ast, r.types, r.module], [null, null, null]);
  assertEquals(r.diagnostics.length, 1);
  assertEquals(r.diagnostics[0].severity, "error");
  assert(r.diagnostics[0].line > 0 && r.diagnostics[0].column > 0);
});

Deno.test("a label that may reject valid input is a warning, and the module is generated", () => {
  const r = analyze({ grammar: "%module A\nS <- 'a' ('b' ^l) { () } / 'a' 'c' { () }\n" });
  assertEquals(r.diagnostics, [{
    severity: "warning",
    line: 2,
    column: 11,
    message: "the label l may reject valid input: where it fails, the alternative at 2:28 can match",
  }]);
  assert(r.module !== null);
});

Deno.test("non-ASCII names and comments come back as written", () => {
  const grammar = "%module A\n\n# 数式の文法\n数式 <- 項 ('+' 項)*\n\n項 <- [0-9]+\n";
  const r = analyze({ grammar });
  assertEquals(r.diagnostics, []);
  assertEquals(r.ast!.children.filter((c) => c.kind === "Rule").map((c) => c.text), ["数式", "項"]);
  assert(format(grammar).text!.includes("# 数式の文法"));
  assert(r.module!.includes("数式"));
});

Deno.test("the names of the files default as in peg-hs gen", async () => {
  const bytes = new TextEncoder().encode(calcGenerated);
  assertEquals(analyze({ grammar: calcGenerated }).module, await native((s) => ["gen", s], "Grammar.hpeg", "Grammar.hs", bytes));
  assertEquals(
    analyze({ grammar: calcGenerated, sourceName: "grammar/Calc.hpeg" }).module,
    await native((s) => ["gen", s], "grammar/Calc.hpeg", "grammar/Calc.hs", bytes),
  );
});

for (const file of grammars) {
  for (const debugEntry of [false, true]) {
    Deno.test(`the module of ${file}${debugEntry ? " --debug-entry" : ""} is the one of peg-hs gen`, async () => {
      const bytes = Deno.readFileSync(root + file);
      const name = file.split("/").pop()!;
      const base = name.replace(/\.[^.]*$/, "");
      const source = `grammar/${name}`;
      const output = `src/${base}.hs`;
      const expected = await native(
        (s) => ["gen", s, "-o", output, ...(debugEntry ? ["--debug-entry"] : [])],
        source,
        output,
        bytes,
      );
      const r = analyze({ grammar: new TextDecoder().decode(bytes), sourceName: source, outputName: output, debugEntry });
      assert(expected !== null || r.diagnostics.some((d) => d.severity === "error"));
      assertEquals(r.module, expected);
    });
  }
  Deno.test(`the format of ${file} is the one of peg-hs fmt`, async () => {
    const bytes = Deno.readFileSync(root + file);
    const expected = await native((s) => ["fmt", s], "G.hpeg", "G.hpeg", bytes);
    assertEquals(format(new TextDecoder().decode(bytes)).text, expected);
  });
}

Deno.test("100 alternating calls of analyze and format give the same responses", () => {
  const grammar = encode({ grammar: read("conformance/json/Json.hpeg") });
  const first = [reactor.call("analyze", grammar), reactor.call("format", grammar)];
  for (let i = 0; i < 100; i++) {
    assertEquals(reactor.call(i % 2 === 0 ? "analyze" : "format", grammar), first[i % 2]);
  }
});

Deno.test("a request that is not UTF-8 gets only an error, and the wasm still works", () => {
  for (const name of ["analyze", "format"] as const) {
    const bad = new Uint8Array([...new TextEncoder().encode('{"grammar": "'), 0xff, 0xfe, ...new TextEncoder().encode('"}')]);
    const r = JSON.parse(reactor.call(name, bad));
    assertEquals(Object.keys(r), ["error"]);
    assertEquals(typeof r.error, "string");
  }
  assertEquals(analyze({ grammar: calcGenerated }).diagnostics, []);
});
