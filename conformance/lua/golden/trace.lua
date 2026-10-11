-- ADR 0022: the structure of random expressions as parsed by the reference
-- implementation. Leaves are names bound to tables whose metamethods return
-- the S-expression of the operation, so evaluating an expression yields the
-- tree the reference parser built. Output: one "expression<TAB>tree" per line.
-- Usage: lua trace.lua COUNT SEED

local count, seed = tonumber(arg[1]), tonumber(arg[2])
math.randomseed(seed)

local mt = {}
local function T(s) return setmetatable({s = s}, mt) end
local function str(v) return type(v) == "table" and v.s or tostring(v) end
local function bin(op) return function(a, b) return T("(" .. op .. " " .. str(a) .. " " .. str(b) .. ")") end end
for k, op in pairs {__add = "+", __sub = "-", __mul = "*", __div = "/", __mod = "%", __pow = "^",
                    __idiv = "//", __band = "&", __bor = "|", __bxor = "~", __shl = "<<", __shr = ">>",
                    __concat = ".."} do
  mt[k] = bin(op)
end
mt.__unm = function(a) return T("(neg " .. str(a) .. ")") end
mt.__bnot = function(a) return T("(bnot " .. str(a) .. ")") end
mt.__len = function(a) return T("(len " .. str(a) .. ")") end
mt.__index = function(a, k) return T("(idx " .. str(a) .. " " .. str(k) .. ")") end
mt.__call = function(f, ...)
  local parts = {"call", str(f)}
  for _, v in ipairs {...} do parts[#parts + 1] = str(v) end
  return T("(" .. table.concat(parts, " ") .. ")")
end
local env = setmetatable({}, {__index = function(_, k) return T(k) end})

local binops = {"|", "~", "&", "<<", ">>", "..", "+", "-", "*", "/", "//", "%", "^"}
local unops = {"-", "~", "#"}
local names = {"a", "b", "c", "d", "e", "f", "g", "h"}

local function pick(t) return t[math.random(#t)] end

local gen
local function primary(depth)
  local r = math.random(10)
  if depth <= 0 or r <= 5 then return pick(names) end
  if r <= 7 then return "(" .. gen(depth - 1) .. ")" end
  return pick(names)
end
local function suffixed(depth)
  local e = primary(depth)
  for _ = 1, math.random(0, depth > 0 and 2 or 0) do
    local r = math.random(4)
    if r == 1 then e = e .. "." .. pick(names)
    elseif r == 2 then e = e .. "[" .. gen(depth - 1) .. "]"
    elseif r == 3 then e = e .. "(" .. gen(depth - 1) .. ", " .. gen(depth - 1) .. ")"
    else e = e .. ":" .. pick(names) .. "(" .. gen(depth - 1) .. ")" end
  end
  return e
end
gen = function(depth)
  if depth <= 0 then return suffixed(0) end
  local r = math.random(10)
  if r <= 6 then return gen(depth - 1) .. " " .. pick(binops) .. " " .. gen(depth - 1) end
  if r <= 8 then return pick(unops) .. " " .. gen(depth - 1) end
  return suffixed(depth)
end

local seen = {}
local n = 0
while n < count do
  local e = gen(math.random(1, 4))
  if not seen[e] then
    seen[e] = true
    local f = assert(load("return " .. e, "=expr", "t", env))
    print(e .. "\t" .. str(f()))
    n = n + 1
  end
end
