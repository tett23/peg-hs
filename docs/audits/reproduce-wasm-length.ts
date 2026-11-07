const mod = new WebAssembly.Module(Deno.readFileSync(Deno.env.get("PEG_HS_WASM") ?? "peg-hs.wasm"));
let mem: WebAssembly.Memory;
const allowed: Record<string, (...a: number[]) => number> = {
  environ_get: () => 0,
  environ_sizes_get: (c, s) => { const v = new DataView(mem.buffer); v.setUint32(c, 0, true); v.setUint32(s, 0, true); return 0; },
  clock_time_get: (_id, _p, out) => { new DataView(mem.buffer).setBigUint64(out, BigInt(Date.now()) * 1000000n, true); return 0; },
  fd_write: (fd, iovs, n, out) => { const v = new DataView(mem.buffer); let t = 0; for (let i = 0; i < n; i++) { const p = v.getUint32(iovs + 8 * i, true), l = v.getUint32(iovs + 8 * i + 4, true); if (fd === 1 || fd === 2) console.error(`fd${fd}:`, new TextDecoder().decode(new Uint8Array(mem.buffer, p, l))); t += l; } v.setUint32(out, t, true); return 0; },
  proc_exit: (c) => { throw new Error("proc_exit " + c); },
};
const wasi: Record<string, (...a: number[]) => number> = {};
for (const i of WebAssembly.Module.imports(mod)) { const f = allowed[i.name]; wasi[i.name] = (...a) => f ? f(...a) : (i.name === "fd_prestat_get" ? 8 : 52); }
const inst = new WebAssembly.Instance(mod, { wasi_snapshot_preview1: wasi });
const ex = inst.exports as any; mem = ex.memory;
ex._initialize(); ex.hs_init(0, 0);
const callLen = (f: string, s: string, len: number) => { const b = new TextEncoder().encode(s); const p = ex.malloc(b.length); new Uint8Array(mem.buffer, p, b.length).set(b); const r = ex[f](p, len); ex.free(p); const n = new DataView(mem.buffer).getUint32(r, true); const out = new TextDecoder().decode(new Uint8Array(mem.buffer, r + 4, n)); ex.free(r); return out; };
const mode = Deno.args[0];
try {
  if (mode === "neg") { console.log(callLen("analyze", '{"grammar":"%module A\\nS <- \'a\'\\n"}', -1)); }
  if (mode === "huge") { console.log(callLen("analyze", '{"grammar":"%module A\\nS <- \'a\'\\n"}', 0x7fffffff).slice(0, 200)); }
  if (mode === "ok") { console.log(callLen("analyze", '{"grammar":"%module A\\nS <- \'a\'\\n"}', 36).slice(0, 200)); }
  if (mode === "file") { const s = Deno.readTextFileSync(Deno.args[1]); const t = performance.now(); const out = callLen(Deno.args[2] ?? "analyze", s, new TextEncoder().encode(s).length); console.log("ms", (performance.now() - t).toFixed(1), "len", out.length, out.slice(0, 300)); console.log("memory MiB", mem.buffer.byteLength / 1048576); }
  console.log("after: alive?", callLen("format", '{"grammar":"%module A\\nS <- \'a\'\\n"}', 36).slice(0, 80));
} catch (e) { console.log("caught:", String(e)); try { console.log("after: alive?", callLen("format", '{"grammar":"%module A\\nS <- \'a\'\\n"}', 36).slice(0, 80)); } catch (e2) { console.log("dead:", String(e2)); } }
