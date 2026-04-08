-- tex/impl/thmlookup.lua
-- MVP: sehr einfache Tokenisierung + α-Normalisierung (primär für \forall/\exists)
-- Registry/Debug als Build-Artefakte (Overleaf: "Logs and output files")

local M = thmlookup or {}

-- ---------- config ----------
local job = (tex and tex.jobname) or "main"
M.registry_path = "thmlookup." .. job .. ".registry.tsv"
M.debug_path    = "thmlookup." .. job .. ".debug.log"

M.format_version = "1"

M.normalize_free_vars = (M.normalize_free_vars ~= false) -- default: true
M.duplicate_policy = M.duplicate_policy or "error"       -- "error" | "warn" | "keep"


-- in-memory index (für Lookup im selben Compile)
M.by_key = M.by_key or {}   -- key -> { record, record, ... }
M.by_id  = M.by_id  or {}   -- id -> { env=..., label=... }


-- ---------- helpers ----------
local function escape_field(s)
  -- TSV: Tabs/Newlines escapen, Backslash escapen
  s = s or ""
  s = s:gsub("\\", "\\\\")
  s = s:gsub("\t", "\\t")
  s = s:gsub("\r", "\\n")
  s = s:gsub("\n", "\\n")
  return s
end

local function append_line(path, line)
  local f = io.open(path, "a") -- öffnet Datei f im Modus append 
  if not f then 
    -- öffnen schlägt fehl
    texio.write_nl("thmlookup: cannot open file for append: " .. tostring(path))
    return
  end
  f:write(line)
  f:write("\n")
  f:close()
end

local function write_debug_block(raw, canon, key, status, candidates)
  local out = {}
  out[#out+1] = "[QUERY]"
  out[#out+1] = "raw:   " .. (raw or "")
  out[#out+1] = "canon: " .. (canon or "")
  out[#out+1] = "key:   " .. (key or "")
  out[#out+1] = "status: " .. (status or "")
  out[#out+1] = "candidates:"
  if candidates and #candidates > 0 then
    for _, r in ipairs(candidates) do
      out[#out+1] =
        string.format("  - label=%s number=%s env=%s title=%s",
          r.label or "", r.number or "", r.env or "", r.title or "")
    end
  end
  out[#out+1] = ""
  append_line(M.debug_path, table.concat(out, "\n"))
end

-- ---------- hashing ----------
-- Prefer MD5 if available; fallback to using canonical text as key (works, just longer).
local md5_ok, md5 = pcall(require, "md5")
local function md5_hex(s)
  if md5_ok and md5 then
    if type(md5.sumhexa) == "function" then return md5.sumhexa(s) end
    if type(md5.sum) == "function" then return md5.sum(s) end
  end
  return nil
end

local function make_key(canon)
  local h = md5_hex(canon)
  if h then return "am" .. h end
  -- fallback (still deterministic)
  return "am" .. canon
end

-- ---------- tokenization (MVP) ----------
-- Produces tokens: control sequences like \forall, symbols '(', ')', ',', identifiers, single letters.
local function tokenize(s)
  local toks = {}
  local i, n = 1, #s

  local function is_space(ch)
    return ch == " " or ch == "\t" or ch == "\n" or ch == "\r"
  end

  while i <= n do
    local ch = s:sub(i,i)

    if is_space(ch) then
      i = i + 1

    elseif ch == "\\" then
      -- control sequence: \word or \, \; etc.
      local j = i + 1
      if j <= n then
        local nextch = s:sub(j,j)
        if nextch:match("[%a]") then
          while j <= n and s:sub(j,j):match("[%a]") do j = j + 1 end
          toks[#toks+1] = s:sub(i, j-1) -- e.g. \forall
          i = j
        else
          toks[#toks+1] = s:sub(i, j)   -- e.g. \,
          i = j + 1
        end
      else
        toks[#toks+1] = "\\"
        i = i + 1
      end

    elseif ch == "(" or ch == ")" or ch == "," or ch == "=" then
      toks[#toks+1] = ch
      i = i + 1

    else
      -- identifier chunk: letters/digits/_/:
      local j = i
      while j <= n do
        local c = s:sub(j,j)
        if c == "\\" or is_space(c) or c == "(" or c == ")" or c == "," or c == "=" then break end
        j = j + 1
      end
      toks[#toks+1] = s:sub(i, j-1)
      i = j
    end
  end
  return toks
end

-- Collapse TeX conditionals of the form: \ifmmode <A> \else <B> \fi
-- We assume we're *not* in math mode during \edef (true for your usage),
-- so we keep the ELSE-branch (<B>). If no \else is present, we keep <A>.
local function resolve_ifmmode(toks)
  local out = {}
  local i = 1
  while i <= #toks do
    local tok = toks[i]
    if tok == "\\ifmmode" then
      i = i + 1
      local then_part = {}
      while i <= #toks and toks[i] ~= "\\else" and toks[i] ~= "\\fi" do
        then_part[#then_part+1] = toks[i]
        i = i + 1
      end

      local else_part = {}
      if i <= #toks and toks[i] == "\\else" then
        i = i + 1
        while i <= #toks and toks[i] ~= "\\fi" do
          else_part[#else_part+1] = toks[i]
          i = i + 1
        end
      end

      if i <= #toks and toks[i] == "\\fi" then
        i = i + 1
      end

      local keep = (#else_part > 0) and else_part or then_part
      for _, t in ipairs(keep) do
        out[#out+1] = t
      end
    else
      out[#out+1] = tok
      i = i + 1
    end
  end
  return out
end


local function is_spacing_cmd(tok)
  return tok == "\\," or tok == "\\;" or tok == "\\!" or tok == "\\:" or tok == "\\ " or
  tok == "\\quad" or tok == "\\qquad" or tok == "\\allowbreak" or tok == "~" or
  -- Delimiter sizing / fences (sollen *nicht* den Key beeinflussen)
  tok == "\\left" or tok == "\\right" or tok == "\\middle" or
  tok == "\\big" or tok == "\\Big" or tok == "\\bigg" or tok == "\\Bigg" or
  tok == "\\bigl" or tok == "\\bigr" or
  tok == "\\Bigl" or tok == "\\Bigr" or
  tok == "\\biggl" or tok == "\\biggr" or
  tok == "\\Biggl" or tok == "\\Biggr" or 
  tok == "\\mskip" or tok == "\\mkern" or tok == "\\kern" or 
  tok == "\\thinmuskip" or tok == "\\medmuskip" or tok == "\\thickmuskip" or
  tok == "\\ifmmode" or tok == "\\else" or tok == "\\fi" or
  tok == "\\protect" or tok == "\\relax"
end



local function is_quantifier(tok)
  return tok == "\\forall" or tok == "\\exists"
end

local function is_variable(tok)
  -- MVP: a single ASCII letter token
  return tok:match("^[A-Za-z]$") ~= nil
end

-- ---------- alpha normalization (MVP) ----------
-- IMPORTANT: Works best if quantifier scopes are parenthesized:
--   \forall x( ... ) or \forall x ( ... )
-- If no '(' follows, binder remains active until end (acceptable MVP limitation).
local function alpha_normalize(statement)
  local toks = resolve_ifmmode(tokenize(statement))
  local out = {}

  local map = {} -- var -> canon (string)
  local binder_stack = {} -- stack of {var, old, active_level, armed}
  local paren_level = 0
  local next_id = 1

  local function push_binder(var)
    local canon = "V" .. tostring(next_id)
    next_id = next_id + 1
    binder_stack[#binder_stack+1] = { var = var, old = map[var], armed = true, canon = canon, active_level = nil }
    return canon
  end

  local function activate_top_binder(current_level)
    local b = binder_stack[#binder_stack]
    if b and b.armed then
      b.armed = false
      b.active_level = current_level
      map[b.var] = b.canon
    end
  end

  local function pop_binders_if_needed(current_level)
    -- pop binders whose scope ended (when paren_level dropped below active_level)
    while true do
      local b = binder_stack[#binder_stack]
      if not b then return end
      if b.active_level == nil then
        -- never activated -> keep
        return
      end
      if current_level < b.active_level then
        -- scope ended
        map[b.var] = b.old
        binder_stack[#binder_stack] = nil
      else
        return
      end
    end
  end

  local idx = 1
  
  local function norm_cmd_name(name)
    if name == "lbrace" or name == "textbraceleft" then return "{" end
    if name == "rbrace" or name == "textbraceright" then return "}" end
    -- vereinheitliche häufige Synonyme
    if name == "rightarrow" then return "to" end

    -- dein Separator-Makro: \dsep expandiert zu ",\allowbreak\ "
    -- wir normalisieren direkt auf "," damit     Lookup/Registry gleich werden
    if name == "dsep" then return "," end

    return name
  end

    -- Normalisiere Einzelbuchstaben, die als Sub-/Superskript im selben Token hängen (z.B. R_A, R^A, f_n)
  local function canon_free_var(v)
    if (not map[v]) and M.normalize_free_vars then
      map[v] = "V" .. tostring(next_id)
      next_id = next_id + 1
    end
    return map[v] or v
  end

  local function normalize_subsup_in_token(tok)
    -- zuerst geklammerte Varianten
    tok = tok:gsub("_%{([A-Za-z])%}", function(v) return "_{" .. canon_free_var(v) .. "}" end)
    tok = tok:gsub("%^%{([A-Za-z])%}", function(v) return "^{" .. canon_free_var(v) .. "}" end)
    -- dann ungeklammerte Varianten
    tok = tok:gsub("_([A-Za-z])", function(v) return "_{" .. canon_free_var(v) .. "}" end)
    tok = tok:gsub("%^([A-Za-z])", function(v) return "^{" .. canon_free_var(v) .. "}" end)
    return tok
  end


  
  while idx <= #toks do
    local tok = toks[idx]

    if is_spacing_cmd(tok) then
      idx = idx + 1

    elseif is_quantifier(tok) then
      local q = (tok == "\\forall") and "forall" or "exists"
      out[#out+1] = q

      -- next non-spacing token should be variable
      idx = idx + 1
      while idx <= #toks and is_spacing_cmd(toks[idx]) do idx = idx + 1 end
      local v = toks[idx] or ""
      if is_variable(v) then
        local canonv = push_binder(v)
        out[#out+1] = canonv
        idx = idx + 1
        -- Wenn keine Klammer folgt, Binder sofort aktivieren (Scope = "bis Ende")
        local j = idx
        while j <= #toks and is_spacing_cmd(toks[j]) do j = j + 1 end
        if toks[j] ~= "(" then
          local b = binder_stack[#binder_stack]
          if b and b.armed then
            b.armed = false
            b.active_level = -10^9
            map[b.var] = b.canon
          end
        end
      else
        -- malformed quantifier usage: keep as-is
        out[#out+1] = v
        idx = idx + 1
      end

    elseif tok == "(" then
      paren_level = paren_level + 1
      -- if a binder is waiting, activate it for this parenthesis scope
      activate_top_binder(paren_level)
      out[#out+1] = "("
      idx = idx + 1

    elseif tok == ")" then
      out[#out+1] = ")"
      paren_level = paren_level - 1
      pop_binders_if_needed(paren_level)
      idx = idx + 1

    elseif is_variable(tok) then
      -- bound vars: map[tok] ist gesetzt
      -- free vars (MVP): ebenfalls kanonisieren, damit P, Q, x, ... gleichbehandelt werden
      if (not map[tok]) and M.normalize_free_vars then
        map[tok] = "V" .. tostring(next_id)
        next_id = next_id + 1
      end
      out[#out+1] = map[tok] or tok
      idx = idx + 1
    else
      -- treat \{ and \} as literal braces (set-builder notation)
      if tok == "\\{" then tok = "{" end
      if tok == "\\}" then tok = "}" end

      -- *** NEU: Sub-/Superskript-Buchstaben im Token normalisieren (R_A, R^A, ...)
      tok = normalize_subsup_in_token(tok)

      -- generic token: normalize some common operators by stripping backslash
      if tok:sub(1,1) == "\\" then
        local name = tok:sub(2)
        out[#out+1] = norm_cmd_name(name)
      else
        out[#out+1] = tok
      end
      idx = idx + 1
    end
  end

  -- any armed binders never activated: activate immediately (scope=end)
  -- (This is a limitation; encourage parentheses for reliable scope.)
  for i = 1, #binder_stack do
    local b = binder_stack[i]
    if b and b.armed then
      map[b.var] = b.canon
      b.armed = false
      b.active_level = -10^9
    end
  end

  return table.concat(out, " ")
end

function M.register(label, env, number, statement, title)
  label = label or ""
  env = env or ""
  number = number or ""
  statement = statement or ""
  title = title or ""

  local canon = alpha_normalize(statement)
  local key = make_key(canon)

  local record = {
    label = label,
    env = env,
    number = number,
    key = key,
    canon = canon,
    title = title,
    loaded = false,
    self_loaded = false,
  }

  M.by_key[key] = M.by_key[key] or {}

  local line = table.concat({
    escape_field(M.format_version),
    escape_field(label),
    escape_field(env),
    escape_field(number),
    escape_field(key),
    escape_field(canon),
    escape_field(title)
  }, "\t")

  -- gleicher Eintrag (gleiches label/env): idempotent bzw. stale-Eintrag aktualisieren
  for idx, r in ipairs(M.by_key[key]) do
    if r.label == label and r.env == env then
      if r.loaded ~= false then
        M.by_key[key][idx] = record
        append_line(M.registry_path, line)
      end
      return
    end
  end

  -- gleiche Struktur, aber anderes Label/andere ID: ausdrücklich zulassen
  -- optional nur fürs Debug-Log festhalten
  if #M.by_key[key] > 0 then
    write_debug_block(statement, canon, key, "same-key-multiple", M.by_key[key])
  end

  table.insert(M.by_key[key], record)
  append_line(M.registry_path, line)
end



 -- ---------- id registry ----------
function M.register_id(id, env, label)
  id = id or ""
  env = env or ""
  label = label or ""
  if id == "" then return end

  local existing = M.by_id[id]
  if existing then
    -- nur self-loaded Altlast darf überschrieben werden
    if not (existing.loaded == true and existing.self_loaded == true) then
      texio.write_nl("thmlookup WARNING: duplicate id '" .. id .. "' (keeping first)")
      return
    end
  end

  -- in-memory (fresh)
  M.by_id[id] = { env = env, label = label, loaded = false, self_loaded = false }

  -- persistieren in TSV
  local line = table.concat({
    "ID",
    escape_field(id),
    escape_field(env),
    escape_field(label)
  }, "\t")
  append_line(M.registry_path, line)
end



function M.ref_by_id(id)
  id = id or ""
  local r = M.by_id[id]
  if not r then
    tex.sprint("\\textbf{[Theorem nicht gefunden]}")
    return
  end
  tex.sprint("\\hyperref[" .. (r.label or "") .. "]{\\ShowFormulaSource{" .. id .. "}}")
end


-- ---------- opts parsing (MVP) ----------
local function parse_opts(opts)
  -- MVP: support "env=theorem" (exact match). Everything else ignored.
  local t = {}
  if not opts or opts == "" then return t end
  for k,v in opts:gmatch("([%a]+)%s*=%s*([%w%-%_]+)") do
    t[k] = v
  end
  return t
end

-- ---------- lookup ----------
function M.ref_by_structure(opts, expr, starred)
  opts = opts or ""
  expr = expr or ""

  local o = parse_opts(opts)
  local canon = alpha_normalize(expr)
  local key = make_key(canon)

  local all = M.by_key[key] or {}
  local candidates = {}
  local blocked_forward = false
  local self_candidates = {}

  for _, r in ipairs(all) do
    if r.self_loaded == true then
      blocked_forward = true
      self_candidates[#self_candidates+1] = r
    else
      candidates[#candidates+1] = r
    end
  end

  -- optional env filter (auf beide Listen anwenden)
  if o.env then
    local function filt(list)
      local out = {}
      for _, r in ipairs(list) do
        if r.env == o.env then out[#out+1] = r end
      end
      return out
    end
    candidates = filt(candidates)
    self_candidates = filt(self_candidates)
  end

  -- 1) frischer Treffer
  if #candidates == 1 then
    local r = candidates[1]
    tex.sprint("\\ThmLookupEmitRef{" .. (r.env or "") .. "}{" .. (r.label or "") .. "}")
    return
  end

  -- 2) Fallback: genau ein self_loaded Treffer
  if #candidates == 0 and #self_candidates == 1 then
    local r = self_candidates[1]
    tex.sprint("\\ThmLookupEmitRef{" .. (r.env or "") .. "}{" .. (r.label or "") .. "}")
    return
  end

  if #candidates == 0 then
    write_debug_block(expr, canon, key, blocked_forward and "blocked-forward" or "none", {})
    tex.sprint("\\textbf{[Theorem nicht gefunden]}")
    return
  end

  -- ambiguous (wie bisher)
  write_debug_block(expr, canon, key, "ambiguous", candidates)
  if starred then
    tex.sprint("\\textbf{[Mehrdeutig: bitte wählen]}\\,")
    tex.sprint("\\begin{itemize}")
    for _, r in ipairs(candidates) do
      local item = string.format("\\item %s (%s) \\texttt{%s}",
        r.number or "?", r.env or "?", r.label or "")
      tex.sprint(item)
    end
    tex.sprint("\\end{itemize}")
  else
    tex.sprint("\\textbf{[Mehrdeutige Theorem-Referenz]}")
  end
end


function M.reset_files()
  local f = io.open(M.registry_path, "w")
  if f then f:write(""); f:close() end

  local g = io.open(M.debug_path, "w")
  if g then g:write(""); g:close() end

  M.by_key = {}
  M.by_id  = {}
end

-- --------- load previous registry (for forward references across runs) ---------
local function unescape_field(s)
  s = s or ""
  s = s:gsub("\\n", "\n")
  s = s:gsub("\\t", "\t")
  s = s:gsub("\\\\", "\\")
  return s
end

local function split_tsv(line)
  local res = {}
  local start = 1
  while true do
    local tab = line:find("\t", start, true)
    if tab then
      res[#res+1] = line:sub(start, tab - 1)
      start = tab + 1
    else
      res[#res+1] = line:sub(start)
      break
    end
  end
  return res
end

function M.load_registry()
  local f = io.open(M.registry_path, "r")
  if not f then return end

  for line in f:lines() do
    if line ~= "" then
      local c = split_tsv(line)
      local tag = c[1] or ""

      if tag == "ID" then
        local id    = unescape_field(c[2] or "")
        local env   = unescape_field(c[3] or "")
        local label = unescape_field(c[4] or "")
        if id ~= "" then
          -- self-registry => self_loaded = true
          M.by_id[id] = { env = env, label = label, loaded = true, self_loaded = true }
        end

      else
        local label  = unescape_field(c[2] or "")
        local env    = unescape_field(c[3] or "")
        local number = unescape_field(c[4] or "")
        local key    = unescape_field(c[5] or "")
        local canon  = unescape_field(c[6] or "")
        local title  = unescape_field(c[7] or "")

        if key ~= "" then
          M.by_key[key] = M.by_key[key] or {}
          table.insert(M.by_key[key], {
            label = label, env = env, number = number,
            key = key, canon = canon, title = title,
            loaded = true,
            self_loaded = true, -- self-registry
          })
        end
      end
    end
  end

  f:close()
end


-- Call at begin of document:
-- 1) Load previous run registry into memory (enables forward refs)
-- 2) Truncate output files for this run
function M.prepare_run()
  M.by_key = {}
  M.by_id  = {}
  M.load_registry()

  local f = io.open(M.registry_path, "w")
  if f then f:write(""); f:close() end

  local g = io.open(M.debug_path, "w")
  if g then g:write(""); g:close() end
end

-- Lädt eine Registry-Datei (TSV) in den aktuellen Speicherindex (M.by_key)
function M.load_registry_file(path)
  local f = io.open(path, "r")
  if not f then
    texio.write_nl("thmlookup: cannot open registry file: " .. tostring(path))
    return
  end

  for line in f:lines() do
    if line ~= "" then
      local cols = split_tsv(line)
      local tag = cols[1] or ""

      if tag == "ID" then
        -- Format: ID, id, env, label
        local id    = unescape_field(cols[2] or "")
        local env   = unescape_field(cols[3] or "")
        local label = unescape_field(cols[4] or "")

        if id ~= "" then
          local existing = M.by_id[id]
          -- Cross-band darf self-loaded überschreiben; echte Konflikte nicht
          if (not existing) or (existing.self_loaded == true) then
            M.by_id[id] = { env = env, label = label, loaded = true, self_loaded = false }
          end
        end

      else
        -- erwartetes Format: ver, label, env, number, key, canon, title
        local label  = unescape_field(cols[2] or "")
        local env    = unescape_field(cols[3] or "")
        local number = unescape_field(cols[4] or "")
        local key_in = unescape_field(cols[5] or "")
        local canon  = unescape_field(cols[6] or "")
        local title  = unescape_field(cols[7] or "")

        local rec = {
          label = label, env = env, number = number,
          canon = canon, title = title,
          loaded = true,
          self_loaded = false,
        }

        -- 1) unter dem Key aus der TSV ablegen (falls vorhanden)
        if key_in ~= "" then
          M.by_key[key_in] = M.by_key[key_in] or {}
          table.insert(M.by_key[key_in], rec)
        end

        -- 2) zusätzlich unter dem *aktuell* berechneten Key ablegen
        local key_now = make_key(canon)
        if key_now ~= "" and key_now ~= key_in then
          M.by_key[key_now] = M.by_key[key_now] or {}
          table.insert(M.by_key[key_now], rec)
        end
      end
    end
  end

  f:close()
end



-- --------- forward-ref support via .aux ---------

-- simple FNV-1a 32-bit hash (fallback if md5 is not available)
local function fnv1a32_hex(s)
  local h = 2166136261
  for i = 1, #s do
    h = h ~ s:byte(i)
    h = (h * 16777619) % 2^32
  end
  return string.format("%08x", h)
end

local function stable_hash_hex(s)
  local h = md5_hex(s)
  if h then return h end
  return fnv1a32_hex(s)
end

-- query key: depends on canonicalized expr + opts (so env-filter etc. is part of key)
function M.query_key(opts, expr)
  opts = opts or ""
  expr = expr or ""
  local canon = alpha_normalize(expr)
  local blob = canon .. "\n" .. tostring(opts)
  return "q" .. stable_hash_hex(blob)
end

-- defines TeX macro \mxFwdRef@<qkey> to the resolved reference (or "nicht gefunden")
function M.define_ref_macro(qkey, opts, expr, starred)
  qkey = qkey or ""
  opts = opts or ""
  expr = expr or ""
  starred = (starred == 1) or (starred == true)

  local o = parse_opts(opts)
  local canon = alpha_normalize(expr)
  local key = make_key(canon)

  local candidates = M.by_key[key] or {}

  -- optional env filter
  if o.env then
    local filtered = {}
    for _, r in ipairs(candidates) do
      if r.env == o.env then filtered[#filtered+1] = r end
    end
    candidates = filtered
  end

  local texcode
  if #candidates == 1 then
    local r = candidates[1]
    texcode = "\\ThmLookupEmitRef{" .. (r.env or "") .. "}{" .. (r.label or "") .. "}"
  elseif #candidates == 0 then
    texcode = "\\textbf{[Theorem nicht gefunden]}"
  else
    -- ambiguous
    if starred then
      texcode = "\\textbf{[Mehrdeutig: bitte wählen]}"
    else
      texcode = "\\textbf{[Mehrdeutige Theorem-Referenz]}"
    end
  end

  tex.sprint("\\expandafter\\gdef\\csname mxFwdRef@" .. qkey .. "\\endcsname{" .. texcode .. "}")
end



return M
