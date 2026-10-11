-- ADR 0022: the values of random expressions built from the operators whose
-- structure the metamethods cannot reveal (or, and, comparisons, not), mixed
-- with addition and subtraction. A runtime error, such as comparing a
-- boolean with a number, is recorded as "error".
-- Output: one "expression<TAB>value" per line. Usage: lua eval.lua COUNT SEED

local count, seed = tonumber(arg[1]), tonumber(arg[2])
math.randomseed(seed)

local cmpops = {"<", ">", "<=", ">=", "==", "~="}
local function pick(t) return t[math.random(#t)] end

-- Numbers and booleans are generated apart so that most expressions are
-- well typed as written; a different parse then tends to change the value
-- or raise an error. One subexpression in ten has a random type.
local num, bool
local function any(depth)
  if math.random(2) == 1 then return num(depth) end
  return bool(depth)
end
num = function(depth)
  local r = math.random(10)
  if depth <= 0 or r <= 2 then return tostring(math.random(0, 5)) end
  if r == 3 then return any(depth - 1) end
  if r <= 6 then return num(depth - 1) .. " " .. pick {"+", "-"} .. " " .. num(depth - 1) end
  if r == 7 then return "- " .. num(depth - 1) end
  if r == 8 then return bool(depth - 1) .. " and " .. num(depth - 1) .. " or " .. num(depth - 1) end
  return "(" .. num(depth - 1) .. ")"
end
bool = function(depth)
  local r = math.random(10)
  if depth <= 0 or r <= 1 then return pick {"true", "false", "nil"} end
  if r == 2 then return any(depth - 1) end
  if r <= 5 then return num(depth - 1) .. " " .. pick(cmpops) .. " " .. num(depth - 1) end
  if r <= 7 then return bool(depth - 1) .. " " .. pick {"and", "or"} .. " " .. bool(depth - 1) end
  if r <= 8 then return "not " .. any(depth - 1) end
  if r == 9 then return bool(depth - 1) .. " " .. pick {"==", "~="} .. " " .. bool(depth - 1) end
  return "(" .. bool(depth - 1) .. ")"
end
local gen = any

local seen = {}
local n = 0
while n < count do
  local e = gen(math.random(1, 5))
  if not seen[e] then
    seen[e] = true
    local f = assert(load("return " .. e, "=expr", "t", {}))
    local ok, v = pcall(f)
    print(e .. "\t" .. (ok and tostring(v) or "error"))
    n = n + 1
  end
end
