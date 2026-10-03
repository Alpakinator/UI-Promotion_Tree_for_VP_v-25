-- Deterministic, dependency-free planar rotations for promotion graphs.
-- Adapted from NetworkX 3.5's algorithms/planarity.py LRPlanarity implementation.
-- Copyright (c) 2004-2025, NetworkX Developers; Aric Hagberg, Dan Schult,
-- Pieter Swart. All rights reserved. NetworkX uses the 3-clause BSD license:
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
-- 1. Redistributions of source code must retain the above copyright notice,
--    this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in the
--    documentation and/or other materials provided with the distribution.
-- 3. Neither the name of the NetworkX Developers nor contributors may be used
--    to endorse or promote products derived from this software without
--    specific prior written permission.
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
-- ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
-- LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
-- CONSEQUENTIAL DAMAGES (INCLUDING PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
-- LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
-- OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
-- DAMAGE.

local SOURCE = "__PROMOTION_SOURCE__"
local MAX_NODES, MAX_EDGES = 256, 1024

local function sortedKeys(map)
  local out = {}
  for key in pairs(map) do
    out[#out + 1] = key
  end
  table.sort(out)
  return out
end

local function copy(list)
  local out = {}
  for i = 1, #list do
    out[i] = list[i]
  end
  return out
end

local function pairKey(a, b)
  if a < b then
    return a .. "\001" .. b
  end
  return b .. "\001" .. a
end

local function edgeId(parent, child)
  return parent .. "\002" .. child
end

local function buildEmbeddingGraph(graph, includeSource, options)
  options = options or {}
  local inputOrder = options.orderVariant == "input"
  if type(graph) ~= "table" or type(graph.nodes) ~= "table" then
    return nil, "promotion graph with nodes required"
  end
  if graph.invalid then
    return nil, "promotion graph is invalid"
  end
  local names = {}
  if graph.order and #graph.order > 0 then
    names = copy(graph.order)
  elseif #graph.nodes > 0 then
    names = copy(graph.nodes)
  else
    names = sortedKeys(graph.nodes)
  end
  if not inputOrder then
    table.sort(names)
  end
  local present = {}
  for i = 1, #names do
    local name = names[i]
    if type(name) ~= "string" or name == SOURCE or present[name] then
      return nil, "duplicate or invalid promotion ID"
    end
    present[name] = true
  end
  if #names > MAX_NODES then
    return nil, "promotion graph exceeds node bound"
  end
  local semantic = {}
  local seenEdge = {}
  local function add(parent, child, kind)
    if
      type(parent) ~= "string"
      or type(child) ~= "string"
      or not present[parent]
      or not present[child]
      or parent == child
    then
      return false, "dangling or self prerequisite"
    end
    local key = pairKey(parent, child)
    if seenEdge[key] then
      return false, "duplicate prerequisite"
    end
    seenEdge[key] = true
    semantic[#semantic + 1] = {
      parent = parent,
      child = child,
      kind = kind or "prerequisite",
      id = edgeId(parent, child),
    }
    return true
  end
  if type(graph.edges) == "table" then
    for i = 1, #graph.edges do
      local edge = graph.edges[i]
      local ok, reason = add(edge.parent, edge.child)
      if not ok then
        return nil, reason
      end
    end
  else
    for i = 1, #names do
      local child = names[i]
      local node = graph.nodes[child]
      if type(node) ~= "table" then
        return nil, "node metadata missing"
      end
      for j = 1, #(node.parents or {}) do
        local ok, reason = add(node.parents[j], child)
        if not ok then
          return nil, reason
        end
      end
    end
  end
  if not inputOrder then
    table.sort(semantic, function(a, b)
      if a.parent ~= b.parent then
        return a.parent < b.parent
      end
      return a.child < b.child
    end)
  end
  local incoming = {}
  for i = 1, #semantic do
    incoming[semantic[i].child] = true
  end
  local remaining, children = {}, {}
  for i = 1, #names do
    remaining[names[i]], children[names[i]] = 0, {}
  end
  for i = 1, #semantic do
    local e = semantic[i]
    remaining[e.child] = remaining[e.child] + 1
    children[e.parent][#children[e.parent] + 1] = e.child
  end
  local queue, head = {}, 1
  for i = 1, #names do
    if remaining[names[i]] == 0 then
      queue[#queue + 1] = names[i]
    end
  end
  local visited = 0
  while queue[head] do
    local current = queue[head]
    head = head + 1
    visited = visited + 1
    for i = 1, #children[current] do
      local child = children[current][i]
      remaining[child] = remaining[child] - 1
      if remaining[child] == 0 then
        queue[#queue + 1] = child
      end
    end
  end
  if visited ~= #names then
    return nil, "prerequisite cycle"
  end
  local roots = {}
  for i = 1, #names do
    if not incoming[names[i]] then
      roots[#roots + 1] = names[i]
    end
  end
  if graph.roots then
    if type(graph.roots) ~= "table" then
      return nil, "graph roots must be a list"
    end
    local supplied = copy(graph.roots)
    table.sort(supplied)
    if #supplied ~= #roots then
      return nil, "graph roots disagree with prerequisites"
    end
    for i = 1, #roots do
      if supplied[i] ~= roots[i] then
        return nil, "graph roots disagree with prerequisites"
      end
    end
  end
  local allNames = copy(names)
  if includeSource ~= false then
    if inputOrder then
      table.insert(allNames, 1, SOURCE)
    else
      allNames[#allNames + 1] = SOURCE
      table.sort(allNames)
    end
    local sources = {}
    for i = 1, #roots do
      sources[#sources + 1] =
        { parent = SOURCE, child = roots[i], kind = "source", id = edgeId(SOURCE, roots[i]) }
    end
    if inputOrder then
      for i = #sources, 1, -1 do
        table.insert(semantic, 1, sources[i])
      end
    else
      for i = 1, #sources do
        semantic[#semantic + 1] = sources[i]
      end
    end
  end
  if #semantic > MAX_EDGES then
    return nil, "promotion graph exceeds edge bound"
  end
  local adj = {}
  local edgeByPair, edgeById = {}, {}
  for i = 1, #allNames do
    adj[allNames[i]] = {}
  end
  for i = 1, #semantic do
    local e = semantic[i]
    local key = pairKey(e.parent, e.child)
    if edgeByPair[key] then
      return nil, "parallel source/prerequisite edge"
    end
    edgeByPair[key] = e
    edgeById[e.id] = e
    adj[e.parent][#adj[e.parent] + 1] = e.child
    adj[e.child][#adj[e.child] + 1] = e.parent
  end
  if not inputOrder then
    for i = 1, #allNames do
      table.sort(adj[allNames[i]])
    end
  end
  return {
    names = allNames,
    promotions = names,
    roots = roots,
    edges = semantic,
    adj = adj,
    edgeByPair = edgeByPair,
    edgeById = edgeById,
  }
end

local function interval(low, high)
  return { low = low, high = high }
end
local function empty(value)
  return value.low == nil and value.high == nil
end
local function clone(value)
  return interval(value.low, value.high)
end
local function pair()
  return { left = interval(), right = interval() }
end
local function swap(value)
  value.left, value.right = value.right, value.left
end

local function findLeftRightEmbedding(data)
  local names, adj = data.names, data.adj
  local n, m = #names, #data.edges
  if n > 2 and m > 3 * n - 6 then
    return nil, "nonplanar edge bound"
  end
  local state = {
    height = {},
    roots = {},
    parent = {},
    lowpt = {},
    lowpt2 = {},
    nesting = {},
    tail = {},
    head = {},
    outgoing = {},
    directed = {},
    ref = {},
    side = {},
    stack = {},
    bottom = {},
    lowEdge = {},
    ordered = {},
    leftRef = {},
    rightRef = {},
  }
  for i = 1, #names do
    state.outgoing[names[i]] = {}
    state.directed[names[i]] = {}
  end
  local function orient(v)
    local pe = state.parent[v]
    for i = 1, #adj[v] do
      local w = adj[v][i]
      if not state.directed[v][w] and not state.directed[w][v] then
        local id = #state.tail + 1
        state.tail[id], state.head[id] = v, w
        state.directed[v][w] = id
        state.outgoing[v][#state.outgoing[v] + 1] = id
        state.lowpt[id], state.lowpt2[id] = state.height[v], state.height[v]
        if state.height[w] == nil then
          state.parent[w] = id
          state.height[w] = state.height[v] + 1
          orient(w)
        else
          state.lowpt[id] = state.height[w]
        end
        state.nesting[id] = 2 * state.lowpt[id]
        if state.lowpt2[id] < state.height[v] then
          state.nesting[id] = state.nesting[id] + 1
        end
        if pe then
          if state.lowpt[id] < state.lowpt[pe] then
            state.lowpt2[pe] = math.min(state.lowpt[pe], state.lowpt2[id])
            state.lowpt[pe] = state.lowpt[id]
          elseif state.lowpt[id] > state.lowpt[pe] then
            state.lowpt2[pe] = math.min(state.lowpt2[pe], state.lowpt[id])
          else
            state.lowpt2[pe] = math.min(state.lowpt2[pe], state.lowpt2[id])
          end
        end
      end
    end
  end
  for i = 1, #names do
    local v = names[i]
    if state.height[v] == nil then
      state.height[v] = 0
      state.roots[#state.roots + 1] = v
      orient(v)
    end
  end
  local function sortOutgoing()
    for i = 1, #names do
      local v = names[i]
      local scored = {}
      for j = 1, #state.outgoing[v] do
        local id = state.outgoing[v][j]
        scored[#scored + 1] = { id = id, order = j }
      end
      table.sort(scored, function(a, b)
        local x, y = state.nesting[a.id], state.nesting[b.id]
        if x ~= y then
          return x < y
        end
        return a.order < b.order
      end)
      local out = {}
      for j = 1, #scored do
        out[j] = scored[j].id
      end
      state.ordered[v] = out
    end
  end
  sortOutgoing()
  local function conflicting(I, e)
    return not empty(I) and state.lowpt[I.high] > state.lowpt[e]
  end
  local function lowest(P)
    if empty(P.left) then
      return state.lowpt[P.right.low]
    end
    if empty(P.right) then
      return state.lowpt[P.left.low]
    end
    return math.min(state.lowpt[P.left.low], state.lowpt[P.right.low])
  end
  local function addConstraints(ei, e)
    local P = pair()
    repeat
      local Q = table.remove(state.stack)
      if not Q then
        return false
      end
      if not empty(Q.left) then
        swap(Q)
      end
      if not empty(Q.left) then
        return false
      end
      if state.lowpt[Q.right.low] > state.lowpt[e] then
        if empty(P.right) then
          P.right = clone(Q.right)
        else
          state.ref[P.right.low] = Q.right.high
        end
        P.right.low = Q.right.low
      else
        state.ref[Q.right.low] = state.lowEdge[e]
      end
    until state.stack[#state.stack] == state.bottom[ei]
    while #state.stack > 0 do
      local top = state.stack[#state.stack]
      if not (conflicting(top.left, ei) or conflicting(top.right, ei)) then
        break
      end
      local Q = table.remove(state.stack)
      if conflicting(Q.right, ei) then
        swap(Q)
      end
      if conflicting(Q.right, ei) then
        return false
      end
      if P.right.low then
        state.ref[P.right.low] = Q.right.high
      end
      if Q.right.low then
        P.right.low = Q.right.low
      end
      if empty(P.left) then
        P.left = clone(Q.left)
      else
        state.ref[P.left.low] = Q.left.high
      end
      P.left.low = Q.left.low
    end
    if not (empty(P.left) and empty(P.right)) then
      state.stack[#state.stack + 1] = P
    end
    return true
  end
  local function removeBackEdges(e)
    local u = state.tail[e]
    while #state.stack > 0 and lowest(state.stack[#state.stack]) == state.height[u] do
      local P = table.remove(state.stack)
      if P.left.low then
        state.side[P.left.low] = -1
      end
    end
    if #state.stack > 0 then
      local P = table.remove(state.stack)
      while P.left.high and state.head[P.left.high] == u do
        P.left.high = state.ref[P.left.high]
      end
      if not P.left.high and P.left.low then
        state.ref[P.left.low] = P.right.low
        state.side[P.left.low] = -1
        P.left.low = nil
      end
      while P.right.high and state.head[P.right.high] == u do
        P.right.high = state.ref[P.right.high]
      end
      if not P.right.high and P.right.low then
        state.ref[P.right.low] = P.left.low
        state.side[P.right.low] = -1
        P.right.low = nil
      end
      state.stack[#state.stack + 1] = P
    end
    if state.lowpt[e] < state.height[u] then
      local top = state.stack[#state.stack]
      if not top then
        return false
      end
      local hl, hr = top.left.high, top.right.high
      if hl and (not hr or state.lowpt[hl] > state.lowpt[hr]) then
        state.ref[e] = hl
      else
        state.ref[e] = hr
      end
    end
    return true
  end
  local function test(v)
    local pe = state.parent[v]
    local ordered = state.ordered[v]
    for i = 1, #ordered do
      local ei = ordered[i]
      local w = state.head[ei]
      state.bottom[ei] = state.stack[#state.stack]
      if ei == state.parent[w] then
        if not test(w) then
          return false
        end
      else
        state.lowEdge[ei] = ei
        state.stack[#state.stack + 1] = { left = interval(), right = interval(ei, ei) }
      end
      if state.lowpt[ei] < state.height[v] then
        if i == 1 then
          state.lowEdge[pe] = state.lowEdge[ei]
        elseif not addConstraints(ei, pe) then
          return false
        end
      end
    end
    if pe then
      return removeBackEdges(pe)
    end
    return true
  end
  for i = 1, #state.roots do
    if not test(state.roots[i]) then
      return nil, "nonplanar LR conflict"
    end
  end
  local function sign(e)
    local r = state.ref[e]
    if r then
      state.ref[e] = nil
      state.side[e] = (state.side[e] or 1) * sign(r)
    end
    return state.side[e] or 1
  end
  for id = 1, #state.tail do
    state.nesting[id] = sign(id) * state.nesting[id]
  end
  sortOutgoing()
  local rotation, leftmost = {}, {}
  for i = 1, #names do
    rotation[names[i]] = {}
  end
  local function insert(v, w, relation, reference)
    local list = rotation[v]
    if #list == 0 then
      list[1] = w
      leftmost[v] = w
      return true
    end
    if not reference then
      return false
    end
    local index
    for i = 1, #list do
      if list[i] == reference then
        index = i
        break
      end
    end
    if not index then
      return false
    end
    if relation == "cw" then
      table.insert(list, index, w)
      if reference == leftmost[v] then
        leftmost[v] = w
      end
    else
      table.insert(list, index + 1, w)
    end
    return true
  end
  for i = 1, #names do
    local v = names[i]
    local previous
    for j = 1, #state.ordered[v] do
      local w = state.head[state.ordered[v][j]]
      if not insert(v, w, "ccw", previous) then
        return nil, "embedding initialization failed"
      end
      previous = w
    end
  end
  local function complete(v)
    local ordered = state.ordered[v]
    for i = 1, #ordered do
      local ei = ordered[i]
      local w = state.head[ei]
      if ei == state.parent[w] then
        if not insert(w, v, "cw", leftmost[w]) then
          return false
        end
        state.leftRef[v], state.rightRef[v] = w, w
        if not complete(w) then
          return false
        end
      else
        if (state.side[ei] or 1) == 1 then
          if not insert(w, v, "ccw", state.rightRef[w]) then
            return false
          end
        else
          if not insert(w, v, "cw", state.leftRef[w]) then
            return false
          end
          state.leftRef[w] = v
        end
      end
    end
    return true
  end
  for i = 1, #state.roots do
    if not complete(state.roots[i]) then
      return nil, "embedding completion failed"
    end
  end
  return rotation
end

local function cyclicBitonic(ranks)
  if #ranks < 3 then
    return true
  end
  local signs = {}
  for i = 1, #ranks do
    local a, b = ranks[i], ranks[i % #ranks + 1]
    if a ~= b then
      signs[#signs + 1] = b > a and 1 or -1
    end
  end
  local turns = 0
  for i = 1, #signs do
    if signs[i] ~= signs[i % #signs + 1] then
      turns = turns + 1
    end
  end
  return turns <= 2
end

local function monotoneSideSplits(clockwise)
  if #clockwise == 0 then
    return { { ascending = {}, descending = {} } }
  end
  local low, high = math.huge, -math.huge
  for i = 1, #clockwise do
    low = math.min(low, clockwise[i].rank)
    high = math.max(high, clockwise[i].rank)
  end
  local splits, seen = {}, {}
  for start = 1, #clockwise do
    if clockwise[start].rank == low then
      local ordered = {}
      for i = 1, #clockwise do
        ordered[i] = clockwise[(start + i - 2) % #clockwise + 1]
      end
      for peak = 1, #ordered do
        if ordered[peak].rank == high then
          local valid = true
          for i = 1, peak - 1 do
            if ordered[i].rank > ordered[i + 1].rank then
              valid = false
              break
            end
          end
          if valid then
            for i = peak + 1, #ordered - 1 do
              if ordered[i].rank < ordered[i + 1].rank then
                valid = false
                break
              end
            end
          end
          if valid then
            local up, down, keys = {}, {}, {}
            for i = 1, peak do
              up[#up + 1] = ordered[i]
              keys[#keys + 1] = ordered[i].id
            end
            keys[#keys + 1] = "|"
            for i = peak + 1, #ordered do
              down[#down + 1] = ordered[i]
              keys[#keys + 1] = ordered[i].id
            end
            local key = table.concat(keys, "\001")
            if not seen[key] then
              seen[key] = true
              splits[#splits + 1] = {
                ascending = up,
                descending = down,
                start = start,
                peak = peak,
              }
            end
          end
        end
      end
    end
  end
  return splits
end

local function after(list, value)
  local at
  for i = 1, #list do
    if list[i] == value then
      at = i
      break
    end
  end
  if not at then
    return nil
  end
  local out = {}
  for i = at + 1, #list do
    out[#out + 1] = list[i]
  end
  for i = 1, at - 1 do
    out[#out + 1] = list[i]
  end
  return out
end

local function contractChains(data, rotation, chains)
  local rot, rep, blocks = {}, {}, {}
  for i = 1, #data.names do
    local name = data.names[i]
    rot[name], rep[name] = {}, name
    blocks[name] = { id = name, members = { name } }
    for j = 1, #rotation[name] do
      local other = rotation[name][j]
      local original = data.edgeByPair[pairKey(name, other)]
      if not original then
        return nil, "embedding names unknown edge"
      end
      rot[name][j] = original.id
    end
  end
  local internal = {}
  local occupied = {}
  for index = 1, #chains do
    local chain = chains[index]
    if type(chain) ~= "table" or #chain < 2 then
      return nil, "malformed family chain"
    end
    for i = 1, #chain do
      if not rep[chain[i]] or occupied[chain[i]] then
        return nil, "overlapping or unknown family member"
      end
      occupied[chain[i]] = true
    end
    local base = chain[1]
    for i = 1, #chain - 1 do
      local a, b = chain[i], chain[i + 1]
      local e = data.edgeByPair[pairKey(a, b)]
      if not e or e.parent ~= a or e.child ~= b or e.kind ~= "prerequisite" then
        return nil, "family ranks are not prerequisite-connected"
      end
      local u, v = rep[a], rep[b]
      if u == v then
        return nil, "family contraction cycle"
      end
      local au, av = after(rot[u], e.id), after(rot[v], e.id)
      if not au or not av then
        return nil, "family edge missing from rotation"
      end
      local merged = au
      for j = 1, #av do
        merged[#merged + 1] = av[j]
      end
      rot[u], rot[v] = merged, nil
      rep[b] = u
      internal[e.id] = true
    end
    local id = "chain:" .. base
    rot[id], rot[base] = rot[base], nil
    blocks[base] = nil
    for i = 1, #chain do
      rep[chain[i]] = id
      blocks[chain[i]] = nil
    end
    blocks[id] = { id = id, members = copy(chain), kind = "family" }
  end
  local blockList = {}
  for _, id in ipairs(sortedKeys(blocks)) do
    local block = blocks[id]
    local memberRank = {}
    for i = 1, #block.members do
      memberRank[block.members[i]] = i
    end
    local clockwise, ranks = {}, {}
    for i = 1, #rot[id] do
      local edge = data.edgeById[rot[id][i]]
      if not internal[edge.id] then
        local member = memberRank[edge.parent] and edge.parent or edge.child
        if not memberRank[member] then
          return nil, "external edge not incident to block"
        end
        local other = member == edge.parent and edge.child or edge.parent
        if rep[other] == id then
          return nil, "family contraction made a self-loop"
        end
        local rank = memberRank[member]
        ranks[#ranks + 1] = rank
        clockwise[#clockwise + 1] = {
          id = edge.id,
          parent = edge.parent,
          child = edge.child,
          kind = edge.kind,
          member = member,
          rank = rank,
          otherBlock = rep[other],
        }
      end
    end
    block.clockwise = clockwise
    if #block.members > 1 then
      block.cyclicBitonic = cyclicBitonic(ranks)
      if not block.cyclicBitonic then
        return nil, "family ports are not bitonic"
      end
      block.sideSplits = monotoneSideSplits(clockwise)
      if #block.sideSplits == 0 then
        return nil, "family ports have no side split"
      end
      block.orientationChoices = {
        "horizontal-forward-upper-A",
        "horizontal-forward-lower-A",
        "horizontal-reverse-upper-A",
        "horizontal-reverse-lower-A",
        "vertical-forward-right-A",
        "vertical-forward-left-A",
        "vertical-reverse-right-A",
        "vertical-reverse-left-A",
      }
    end
    blockList[#blockList + 1] = block
  end
  return blockList
end

local function cardinal(side)
  if side == "T" then
    return 0, -1
  end
  if side == "B" then
    return 0, 1
  end
  if side == "L" then
    return -1, 0
  end
  return 1, 0
end

local function assignPortsForSplit(
  block,
  placement,
  geometry,
  split,
  mirror,
  preferredCaps,
  useCaps
)
  local placementId = block.members[1]
  if placement.member and placement.member[placementId] then
    placementId = placement.member[placementId]
  end
  local placed = placement.blocks and placement.blocks[placementId]
  if not placed or (placed.orientation ~= "h" and placed.orientation ~= "v") then
    return nil, "missing horizontal/vertical family block"
  end
  local direction = placed.direction
    or (
      placement.ogdfDiagnostic
      and placement.ogdfDiagnostic.familyDirections
      and placement.ogdfDiagnostic.familyDirections[placementId]
    )
  local reverse = placed.reverse == true or direction == "reverse"
  local flip = mirror ~= reverse
  local aSide, bSide
  if placed.orientation == "h" then
    aSide, bSide = flip and "B" or "T", flip and "T" or "B"
  else
    aSide, bSide = flip and "L" or "R", flip and "R" or "L"
  end
  local buttonOf = {}
  for i = 1, #(placement.buttons or {}) do
    buttonOf[placement.buttons[i].type] = placement.buttons[i]
  end
  local bw, bh = geometry.buttonW, geometry.buttonH
  local minPitch = geometry.portPitch or 8
  local assigned, score = {}, 0
  local capped = {}
  local firstCap, lastCap
  if placed.orientation == "h" then
    firstCap, lastCap = reverse and "R" or "L", reverse and "L" or "R"
  else
    firstCap, lastCap = reverse and "B" or "T", reverse and "T" or "B"
  end
  local function addCap(records, side, rank)
    local chosen, seen = {}, {}
    for i = 1, #records do
      local record = records[i]
      if record and not seen[record.id] and record.rank == rank then
        seen[record.id] = true
        local desired = preferredCaps and preferredCaps[record.id]
        local field = record.parent == record.member and "sourceSide" or "targetSide"
        if desired and desired[field] == side then
          chosen[#chosen + 1] = record
        end
      end
    end
    local length = (side == "T" or side == "B") and bw or bh
    if #chosen > 0 and length / (#chosen + 1) < minPitch then
      return false, "ordered end-cap ports cannot fit at native pitch"
    end
    for i = 1, #chosen do
      local record = chosen[i]
      local card = buttonOf[record.member]
      if not card then
        return false, "family end card has no placement"
      end
      local offset = math.floor(length * i / (#chosen + 1) + 0.5)
      -- Clockwise traversal follows T left-to-right, R top-to-bottom,
      -- B right-to-left, and L bottom-to-top.
      if side == "B" or side == "L" then
        offset = length - offset
      end
      local port
      if side == "T" then
        port = { x = card.x + offset, y = card.y }
      elseif side == "B" then
        port = { x = card.x + offset, y = card.y + bh }
      elseif side == "L" then
        port = { x = card.x, y = card.y + offset }
      else
        port = { x = card.x + bw, y = card.y + offset }
      end
      local entry = assigned[record.id] or {}
      if record.parent == record.member then
        entry.sourceSide, entry.sourcePort, entry.sourceLane = side, port, i
      else
        entry.targetSide, entry.targetPort, entry.targetLane = side, port, i
      end
      assigned[record.id] = entry
      capped[record.id] = true
    end
    return true
  end
  if useCaps then
    local first = split.ascending[1]
    local trailing = split.descending[#split.descending]
    local peak = split.ascending[#split.ascending]
    local afterPeak = split.descending[1]
    local firstBoundary = {}
    if trailing then
      firstBoundary[#firstBoundary + 1] = trailing
    end
    if first then
      firstBoundary[#firstBoundary + 1] = first
    end
    local lastBoundary = {}
    if peak then
      lastBoundary[#lastBoundary + 1] = peak
    end
    if afterPeak then
      lastBoundary[#lastBoundary + 1] = afterPeak
    end
    local ok, why = addCap(firstBoundary, firstCap, 1)
    if not ok then
      return nil, why
    end
    ok, why = addCap(lastBoundary, lastCap, #block.members)
    if not ok then
      return nil, why
    end
    if not next(capped) then
      return nil, "no guide-compatible end-cap dart"
    end
  end
  local function addSide(records, side, increasing)
    local counts, used = {}, {}
    for i = 1, #records do
      local member = records[i].member
      if not capped[records[i].id] then
        counts[member] = (counts[member] or 0) + 1
      end
    end
    for i = 1, #records do
      local record = records[i]
      if not capped[record.id] then
        local member = record.member
        local card = buttonOf[member]
        if not card then
          return false, "family card has no placement"
        end
        used[member] = (used[member] or 0) + 1
        local count = counts[member]
        local length = (side == "T" or side == "B") and bw or bh
        if length / (count + 1) < minPitch then
          return false, "ordered family ports cannot fit at native pitch"
        end
        local position = increasing and used[member] or (count + 1 - used[member])
        local offset = math.floor(length * position / (count + 1) + 0.5)
        local port
        if side == "T" then
          port = { x = card.x + offset, y = card.y }
        elseif side == "B" then
          port = { x = card.x + offset, y = card.y + bh }
        elseif side == "L" then
          port = { x = card.x, y = card.y + offset }
        else
          port = { x = card.x + bw, y = card.y + offset }
        end
        local entry = assigned[record.id] or {}
        local field = record.parent == member and "sourceSide" or "targetSide"
        local desired = preferredCaps and preferredCaps[record.id]
        if
          desired
          and desired[field]
          and (desired[field] == firstCap or desired[field] == lastCap)
          and desired[field] ~= side
        then
          score = score + (geometry.capMismatchPenalty or 25)
        end
        if record.parent == member then
          entry.sourceSide, entry.sourcePort, entry.sourceLane = side, port, i
        else
          entry.targetSide, entry.targetPort, entry.targetLane = side, port, i
        end
        assigned[record.id] = entry
        local own = placement.blockCenters and placement.blockCenters[placementId]
        local otherId = record.otherBlock
        if otherId and otherId:sub(1, 6) == "chain:" then
          otherId = otherId:sub(7)
        end
        if placement.member and placement.member[otherId] then
          otherId = placement.member[otherId]
        end
        local other = placement.blockCenters and placement.blockCenters[otherId]
        if own and other then
          local dx, dy = other.x - own.x, other.y - own.y
          local distance = math.sqrt(dx * dx + dy * dy)
          if distance > 0 then
            local nx, ny = cardinal(side)
            local dot = (nx * dx + ny * dy) / distance
            score = score + (1 - dot) * 10
            if dot < 0 then
              score = score + 20
            end
          end
        end
      end
    end
    return true
  end
  local ok, why = addSide(split.ascending, aSide, true)
  if not ok then
    return nil, why
  end
  ok, why = addSide(split.descending, bSide, false)
  if not ok then
    return nil, why
  end
  return {
    assignment = assigned,
    score = score,
    split = split,
    aSide = aSide,
    bSide = bSide,
    mirror = mirror,
    capped = capped,
    reverse = reverse,
  }
end

local function mergePortAssignments(first, second)
  local out = {}
  for id, fields in pairs(first) do
    local row = {}
    for key, value in pairs(fields) do
      row[key] = value
    end
    out[id] = row
  end
  for id, fields in pairs(second) do
    local row = out[id] or {}
    for key, value in pairs(fields) do
      if row[key] ~= nil then
        return nil
      end
      row[key] = value
    end
    out[id] = row
  end
  return out
end

-- Diagnostic for a block drawing's topological sectors.  It observes the
-- first intersection of each guide with a thin halo around its block, then
-- compares the clockwise edge groups to the contracted LR rotation.  Guides
-- that leave through the same halo point form one unresolved group; their
-- eventual branch order is deliberately not guessed here.
function PromotionEmbeddingGuideRotation(embedded, placement, graph, geometry)
  geometry = geometry or {}
  local guides, roots = geometry.guideMap, geometry.rootGuides
  if not guides and type(PlanarPromotionBlockGuides) == "function" then
    guides, roots = PlanarPromotionBlockGuides(graph, placement)
  end
  if not guides or not placement.blockBoxes then
    return nil, "block guides and rectangles required"
  end
  local halo = geometry.guideRotationHalo or 4
  local tolerance = geometry.guideRotationTolerance or 1
  local results = {}
  local allForward, allMirror = true, true
  local function exitPoint(path, box, reverse)
    local x0, y0 = box.x - halo, box.y - halo
    local x1, y1 = box.x + box.w + halo, box.y + box.h + halo
    local pts = {}
    if reverse then
      for i = #path, 1, -1 do
        pts[#pts + 1] = path[i]
      end
    else
      for i = 1, #path do
        pts[i] = path[i]
      end
    end
    local function inside(p)
      return p.x >= x0 - 0.001 and p.x <= x1 + 0.001 and p.y >= y0 - 0.001 and p.y <= y1 + 0.001
    end
    for i = 1, #pts - 1 do
      local a, b = pts[i], pts[i + 1]
      if inside(a) and not inside(b) then
        if b.x < x0 then
          return { x = x0, y = a.y }
        end
        if b.x > x1 then
          return { x = x1, y = a.y }
        end
        if b.y < y0 then
          return { x = a.x, y = y0 }
        end
        if b.y > y1 then
          return { x = a.x, y = y1 }
        end
      end
    end
    return nil
  end
  local function perimeter(p, box)
    local w, h = box.w + 2 * halo, box.h + 2 * halo
    local left, top = box.x - halo, box.y - halo
    local x, y = p.x - left, p.y - top
    if math.abs(y) < 0.002 then
      return x
    end
    if math.abs(x - w) < 0.002 then
      return w + y
    end
    if math.abs(y - h) < 0.002 then
      return w + h + (w - x)
    end
    return 2 * w + h + (h - y)
  end
  local function matches(groups, oracle, reverse)
    local n = #oracle
    if n == 0 then
      return true
    end
    for start = 1, n do
      local cursor = start
      local valid = true
      for i = 1, #groups do
        local group = groups[i]
        local expected = {}
        for j = 1, #group.ids do
          expected[oracle[cursor]] = true
          cursor = ((cursor - 1 + (reverse and -1 or 1) + n) % n) + 1
        end
        for j = 1, #group.ids do
          if not expected[group.ids[j]] then
            valid = false
            break
          end
        end
        if not valid then
          break
        end
      end
      if valid then
        return true
      end
    end
    return false
  end
  for i = 1, #embedded.blocks do
    local block = embedded.blocks[i]
    local id = block.members[1] or block.id
    if placement.member and placement.member[id] then
      id = placement.member[id]
    end
    local box = placement.blockBoxes[id]
    local rays, oracle = {}, {}
    if box then
      for j = 1, #block.clockwise do
        local dart = block.clockwise[j]
        local guide = dart.kind == "source" and (roots and roots[dart.child])
          or guides[dart.parent .. "\001" .. dart.child]
        local path = guide and guide.points
        if path and #path >= 2 then
          local point = exitPoint(path, box, dart.child == dart.member)
          if point then
            local key = dart.parent .. "\001" .. dart.child
            rays[#rays + 1] = { key = key, perimeter = perimeter(point, box) }
          end
        end
      end
      local included = {}
      for j = 1, #rays do
        included[rays[j].key] = true
      end
      for j = 1, #block.clockwise do
        local dart = block.clockwise[j]
        local key = dart.parent .. "\001" .. dart.child
        if included[key] then
          oracle[#oracle + 1] = key
        end
      end
    end
    table.sort(rays, function(a, b)
      if a.perimeter ~= b.perimeter then
        return a.perimeter < b.perimeter
      end
      return a.key < b.key
    end)
    local groups = {}
    for j = 1, #rays do
      local ray = rays[j]
      local last = groups[#groups]
      if last and math.abs(last.perimeter - ray.perimeter) <= tolerance then
        last.ids[#last.ids + 1] = ray.key
      else
        groups[#groups + 1] = { perimeter = ray.perimeter, ids = { ray.key } }
      end
    end
    local forward = matches(groups, oracle, false)
    local mirrored = matches(groups, oracle, true)
    results[#results + 1] = {
      id = id,
      checked = #rays,
      groups = groups,
      forward = forward,
      mirrored = mirrored,
    }
    allForward = allForward and forward
    allMirror = allMirror and mirrored
  end
  return { forward = allForward, mirrored = allMirror, blocks = results }
end

-- Assign every external family edge to an ordered exact port and halo lane.
-- A single mirror bit is used across all blocks, preserving the LR rotation.
-- The optional projector callback measures native-clear guide feasibility.
function PromotionEmbeddingAssignPorts(embedded, placement, graph, geometry, projector)
  if type(embedded) ~= "table" or type(placement) ~= "table" or type(geometry) ~= "table" then
    return nil, "embedding, placement and geometry required", "invalid_input"
  end
  local family = {}
  for i = 1, #embedded.blocks do
    local block = embedded.blocks[i]
    if #block.members > 1 then
      family[#family + 1] = block
    end
  end
  table.sort(family, function(a, b)
    if #a.sideSplits ~= #b.sideSplits then
      return #a.sideSplits < #b.sideSplits
    end
    return a.id < b.id
  end)
  local guideMap, rootGuides = geometry.guideMap, geometry.rootGuides
  if not guideMap and type(PlanarPromotionBlockGuides) == "function" then
    guideMap, rootGuides = PlanarPromotionBlockGuides(graph, placement)
  end
  local preferredCaps = {}
  for id, sides in pairs(geometry.preferredCaps or {}) do
    preferredCaps[id] = { sourceSide = sides.sourceSide, targetSide = sides.targetSide }
  end
  local tolerance = geometry.guidePortTolerance or 2
  local function boundarySide(p, box)
    if not p or not box then
      return nil
    end
    if math.abs(p.x - box.x) <= tolerance then
      return "L"
    end
    if math.abs(p.x - (box.x + box.w)) <= tolerance then
      return "R"
    end
    if math.abs(p.y - box.y) <= tolerance then
      return "T"
    end
    if math.abs(p.y - (box.y + box.h)) <= tolerance then
      return "B"
    end
    return nil
  end
  if guideMap and placement.blockBoxes then
    for i = 1, #family do
      local block = family[i]
      local placementId = placement.member and placement.member[block.members[1]]
        or block.members[1]
      local box = placement.blockBoxes[placementId]
      for j = 1, #block.clockwise do
        local record = block.clockwise[j]
        local guide = record.kind == "source" and (rootGuides and rootGuides[record.child])
          or guideMap[record.parent .. "\001" .. record.child]
        local points = guide and guide.points
        if points and #points > 0 then
          local field = record.parent == record.member and "sourceSide" or "targetSide"
          local p = field == "sourceSide" and points[1] or points[#points]
          local side = boundarySide(p, box)
          if side then
            preferredCaps[record.id] = preferredCaps[record.id] or {}
            if not preferredCaps[record.id][field] then
              preferredCaps[record.id][field] = side
            end
          end
        end
      end
    end
  end
  local rotationInfo = PromotionEmbeddingGuideRotation(embedded, placement, graph, geometry)
  local completeRotation = rotationInfo ~= nil
  if completeRotation then
    for i = 1, #embedded.blocks do
      if rotationInfo.blocks[i].checked ~= #embedded.blocks[i].clockwise then
        completeRotation = false
        break
      end
    end
  end
  local requiredMirror
  if completeRotation then
    if not rotationInfo.forward and not rotationInfo.mirrored then
      return nil, "block guides disagree with LR cyclic edge order", "incompatible_block_rotation"
    end
    if rotationInfo.forward ~= rotationInfo.mirrored then
      requiredMirror = rotationInfo.mirrored
    end
  end
  projector = projector or geometry.projectGuideCheck or PromotionLayoutProjectGuideCheck
  local beamWidth = geometry.portBeamWidth or 96
  if beamWidth < 1 then
    beamWidth = 1
  end
  if beamWidth > 256 then
    beamWidth = 256
  end
  local best, candidates = nil, {}
  for mirrorIndex = 0, 1 do
    local mirror = mirrorIndex == 1
    if requiredMirror == nil or mirror == requiredMirror then
      local beam = { { assignment = {}, score = 0, choices = {} } }
      for i = 1, #family do
        local block = family[i]
        local options = {}
        for j = 1, #block.sideSplits do
          for cap = 0, 1 do
            local option = assignPortsForSplit(
              block,
              placement,
              geometry,
              block.sideSplits[j],
              mirror,
              preferredCaps,
              cap == 1
            )
            if option then
              options[#options + 1] = option
            end
          end
        end
        if #options == 0 then
          return nil,
            "family ports cannot fit their chosen block side",
            "incompatible_block_rotation"
        end
        local expanded = {}
        for j = 1, #beam do
          for k = 1, #options do
            local merged = mergePortAssignments(beam[j].assignment, options[k].assignment)
            if merged then
              local choices = copy(beam[j].choices)
              choices[#choices + 1] = {
                block = block.id,
                split = options[k].split,
                aSide = options[k].aSide,
                bSide = options[k].bSide,
                capped = options[k].capped,
                reverse = options[k].reverse,
              }
              expanded[#expanded + 1] = {
                assignment = merged,
                score = beam[j].score + options[k].score,
                choices = choices,
              }
            end
          end
        end
        table.sort(expanded, function(a, b)
          return a.score < b.score
        end)
        beam = {}
        for j = 1, math.min(beamWidth, #expanded) do
          beam[j] = expanded[j]
        end
        if #beam == 0 then
          return nil,
            "family side choices conflict on an external edge",
            "incompatible_block_rotation"
        end
      end
      for i = 1, #beam do
        local candidate = beam[i]
        local projected, sourceProjected, missingGuides = 0, 0, 0
        if type(projector) == "function" and guideMap then
          local opts = {}
          for key, value in pairs(geometry) do
            opts[key] = value
          end
          opts.portAssignment = candidate.assignment
          for j = 1, #embedded.edges do
            local edge = embedded.edges[j]
            local guide = edge.kind == "source" and (rootGuides and rootGuides[edge.child])
              or guideMap[edge.parent .. "\001" .. edge.child]
            if guide then
              if projector(guide, placement, opts) then
                if edge.kind == "source" then
                  sourceProjected = sourceProjected + 1
                else
                  projected = projected + 1
                end
              end
            else
              missingGuides = missingGuides + 1
            end
          end
        end
        candidate.projected = projected
        candidate.sourceProjected = sourceProjected
        candidate.missingGuides = missingGuides
        candidate.mirror = mirror
        candidates[#candidates + 1] = candidate
      end
    end
  end
  -- The guide check above measures one route at a time.  Two individually
  -- feasible routes may still compete for the same halo.  When available,
  -- score the best few choices after the projector reserves earlier routes.
  table.sort(candidates, function(a, b)
    local ac, bc = a.projected + a.sourceProjected, b.projected + b.sourceProjected
    if ac ~= bc then
      return ac > bc
    end
    if a.sourceProjected ~= b.sourceProjected then
      return a.sourceProjected > b.sourceProjected
    end
    return a.score < b.score
  end)
  -- Pairwise scoring can be much more expensive than the embedding itself;
  -- callers opt in when evaluating offline candidates.
  local globalScore = geometry.scoreAssignment
  local trials = geometry.portGlobalTrials or 24
  if trials < 1 then
    trials = 1
  end
  if trials > #candidates then
    trials = #candidates
  end
  if type(globalScore) == "function" then
    for i = 1, trials do
      local candidate = candidates[i]
      local projected, sourceProjected =
        globalScore(graph, placement, embedded, geometry, candidate.assignment)
      candidate.globalProjected = projected or 0
      candidate.globalSourceProjected = sourceProjected or 0
      if
        not best
        or candidate.globalProjected + candidate.globalSourceProjected > best.globalProjected + best.globalSourceProjected
        or (candidate.globalProjected + candidate.globalSourceProjected == best.globalProjected + best.globalSourceProjected and candidate.globalSourceProjected > best.globalSourceProjected)
        or (
          candidate.globalProjected + candidate.globalSourceProjected
            == best.globalProjected + best.globalSourceProjected
          and candidate.globalSourceProjected == best.globalSourceProjected
          and candidate.score < best.score
        )
      then
        best = candidate
      end
    end
  else
    best = candidates[1]
  end
  if not best then
    return nil, "no compatible family port assignment", "incompatible_block_rotation"
  end
  return best.assignment,
    {
      projected = best.projected,
      sourceProjected = best.sourceProjected,
      missingGuides = best.missingGuides,
      globalProjected = best.globalProjected,
      globalSourceProjected = best.globalSourceProjected,
      mirror = best.mirror,
      score = best.score,
      choices = best.choices,
      guideRotation = completeRotation and rotationInfo or nil,
    }
end

function PromotionPlanarEmbedding(graph, includeSource, options)
  local data, reason = buildEmbeddingGraph(graph, includeSource, options)
  if not data then
    return nil, reason, "invalid_graph"
  end
  local rotation
  rotation, reason = findLeftRightEmbedding(data)
  if not rotation then
    return nil, reason, "nonplanar"
  end
  local blocks
  blocks, reason = contractChains(data, rotation, graph.chains or {})
  if not blocks then
    return nil, reason, "unsupported_family_embedding"
  end
  local blockById = {}
  for i = 1, #blocks do
    blockById[blocks[i].id] = blocks[i]
  end
  local rotationOrder, mirroredRotationOrder = {}, {}
  for i = 1, #blocks do
    local block = blocks[i]
    local placementId = block.members[1] or block.id
    local forward, reverse = {}, {}
    for j = 1, #block.clockwise do
      local record = block.clockwise[j]
      local key = record.parent .. "\001" .. record.child
      forward[key], reverse[key] = j, #block.clockwise - j + 1
    end
    rotationOrder[placementId] = forward
    mirroredRotationOrder[placementId] = reverse
  end
  return {
    rotation = rotation,
    blocks = blocks,
    blockById = blockById,
    rotationOrder = rotationOrder,
    mirroredRotationOrder = mirroredRotationOrder,
    edges = data.edges,
    roots = data.roots,
    source = includeSource == false and nil or SOURCE,
    nodes = data.names,
  }
end

-- Select a deterministic runtime embedding that actually matches complete
-- block guides.  The two LR traversal orders can choose different valid
-- rotations at separation pairs; neither is a fixed per-class fixture.
function PromotionEmbeddingChooseForPlacement(graph, placement, geometry)
  for _, variant in ipairs({ "sorted", "input" }) do
    local options = variant == "input" and { orderVariant = "input" } or nil
    local embedded = PromotionPlanarEmbedding(graph, true, options)
    if embedded then
      local diagnostic = PromotionEmbeddingGuideRotation(embedded, placement, graph, geometry)
      local complete = diagnostic ~= nil
      if complete then
        for i = 1, #embedded.blocks do
          if diagnostic.blocks[i].checked ~= #embedded.blocks[i].clockwise then
            complete = false
            break
          end
        end
      end
      if complete and (diagnostic.forward or diagnostic.mirrored) then
        return embedded,
          {
            variant = variant,
            mirrored = not diagnostic.forward,
            diagnostic = diagnostic,
          }
      end
    end
  end
  return nil, "no runtime LR rotation matches the block guides", "incompatible_block_rotation"
end

return {
  embed = PromotionPlanarEmbedding,
  assignPorts = PromotionEmbeddingAssignPorts,
  guideRotation = PromotionEmbeddingGuideRotation,
  chooseForPlacement = PromotionEmbeddingChooseForPlacement,
  source = SOURCE,
}
