-- ADR 0022: accept or reject verdicts of the reference implementation for
-- mutated test files. Each mutation edits the tokens of one file: deleting
-- a token, duplicating a token, swapping two adjacent tokens, or deleting a
-- bracket. Offsets are 0-based bytes of the file after the first line is
-- dropped if it starts with '#' (keeping its newline), which is what
-- luaL_loadfilex does.
--
-- Output, one mutation per line, separated by tabs:
--   file  kind  a  b  c  d  verdict
-- kind delete: remove [a, b). duplicate: insert a copy of [a, b) at b.
-- swap: exchange [a, b) and [c, d), with b <= c. c and d are 0 unless used.
-- verdict: accept, syntax (a syntax error), or semantic (an error that is not
-- about the syntax; see 'semantic' below).
-- Usage: lua mutate.lua DIR PER-FILE SEED FILE...

local dir, perFile, seed = arg[1], tonumber(arg[2]), tonumber(arg[3])

-- Errors of the reference parser that a grammar does not detect.
local semantic = {
  "attempt to assign to const variable", "break outside loop", "control structure too long",
  "global variables cannot be to-be-closed", "already defined on line",
  "multiple to-be-closed variables", "no visible label", "unknown attribute", "not declared",
  "is global when accessing variable", "jumps into the scope", "too many",
  "outside a vararg function", "overflow",
}

local function classify(msg)
  for _, p in ipairs(semantic) do
    if msg:find(p, 1, true) then return "semantic" end
  end
  return "syntax"
end

local function prepare(src)
  if src:sub(1, 1) == "#" then
    local nl = src:find("\n", 1, true)
    return nl and src:sub(nl) or ""
  end
  return src
end

-- A rough tokenizer: it only has to find token boundaries for mutations.
local function longBracket(src, i)
  local eq = src:match("^%[(=*)%[", i)
  if not eq then return nil end
  local close = "]" .. eq .. "]"
  local s = src:find(close, i + #eq + 2, true)
  return s and s + #close - 1 or #src
end

local symbols = {"...", "..", "==", "~=", "<=", ">=", "<<", ">>", "//", "::"}

local function tokens(src)
  local toks, i, n = {}, 1, #src
  while i <= n do
    local c = src:sub(i, i)
    if c:match("[ \t\r\n\f\v]") then
      i = i + 1
    elseif src:sub(i, i + 1) == "--" then
      local e = longBracket(src, i + 2)
      if not e then e = (src:find("\n", i, true) or n + 1) - 1 end
      i = e + 1
    else
      local e
      if c == "[" then e = longBracket(src, i) end
      if not e and (c == '"' or c == "'") then
        local j = i + 1
        while j <= n and src:sub(j, j) ~= c and src:sub(j, j) ~= "\n" do
          j = j + (src:sub(j, j) == "\\" and 2 or 1)
        end
        e = math.min(j, n)
      end
      if not e and (c:match("%d") or src:match("^%.%d", i)) then
        local j = i
        while j <= n do
          if src:match("^[eEpP][+-]", j) then j = j + 2
          elseif src:sub(j, j):match("[%w%.]") then j = j + 1
          else break end
        end
        e = j - 1
      end
      if not e and c:match("[%a_]") then e = select(2, src:find("^[%w_]+", i)) end
      if not e then
        for _, s in ipairs(symbols) do
          if src:sub(i, i + #s - 1) == s then e = i + #s - 1; break end
        end
      end
      e = e or i
      toks[#toks + 1] = {i - 1, e}
      i = e + 1
    end
  end
  return toks
end

math.randomseed(seed)
for k = 4, #arg do
  local name = arg[k]
  local fh = assert(io.open(dir .. "/" .. name, "rb"))
  local src = prepare(fh:read("a"))
  fh:close()
  local toks = tokens(src)
  local brackets = {}
  for _, t in ipairs(toks) do
    if src:sub(t[1] + 1, t[2]):match("^[%(%)%[%]{}]$") then brackets[#brackets + 1] = t end
  end
  for _ = 1, perFile do
    local kind = ({"delete", "duplicate", "swap", "delete-bracket"})[math.random(4)]
    local a, b, c, d, mutated = 0, 0, 0, 0, nil
    if kind == "delete-bracket" and #brackets > 0 then
      local t = brackets[math.random(#brackets)]
      a, b = t[1], t[2]
      mutated = src:sub(1, a) .. src:sub(b + 1)
    elseif kind == "swap" then
      local j = math.random(#toks - 1)
      a, b, c, d = toks[j][1], toks[j][2], toks[j + 1][1], toks[j + 1][2]
      mutated = src:sub(1, a) .. src:sub(c + 1, d) .. src:sub(b + 1, c) .. src:sub(a + 1, b) .. src:sub(d + 1)
    elseif kind == "duplicate" then
      local t = toks[math.random(#toks)]
      a, b = t[1], t[2]
      mutated = src:sub(1, b) .. src:sub(a + 1, b) .. src:sub(b + 1)
    else
      kind = "delete"
      local t = toks[math.random(#toks)]
      a, b = t[1], t[2]
      mutated = src:sub(1, a) .. src:sub(b + 1)
    end
    local f, msg = load(mutated, "=" .. name, "t")
    local verdict = f and "accept" or classify(msg)
    print(table.concat({name, kind, a, b, c, d, verdict}, "\t"))
  end
end
