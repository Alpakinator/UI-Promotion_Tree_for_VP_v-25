-- Bounded generic fallback for dense DAGs whose ordinary rank layout cannot
-- route every prerequisite. This module never recognizes promotion IDs or
-- graph signatures; its placement decisions use ranks, degrees and the
-- already-audited ordinary layout as a row warm start.

local function denseGraphMetrics(graph)
  if
    type(graph) ~= "table"
    or type(graph.order) ~= "table"
    or type(graph.nodes) ~= "table"
    or #graph.order < 24
  then
    return nil
  end
  local edgeCount, maximumIndegree, maximumOutdegree = 0, 0, 0
  for _, name in ipairs(graph.order) do
    local node = graph.nodes[name]
    if not node then
      return nil
    end
    local indegree = #(node.parents or {})
    local outdegree = #(node.children or {})
    edgeCount = edgeCount + indegree
    maximumIndegree = math.max(maximumIndegree, indegree)
    maximumOutdegree = math.max(maximumOutdegree, outdegree)
  end
  if edgeCount < #graph.order * 1.15 then
    return nil
  end

  local rank, visiting = {}, {}
  local function prerequisiteRank(name)
    if rank[name] ~= nil then
      return rank[name]
    end
    if visiting[name] then
      return nil
    end
    visiting[name] = true
    local value = 0
    for _, parent in ipairs(graph.nodes[name].parents or {}) do
      if not graph.nodes[parent] then
        return nil
      end
      local parentRank = prerequisiteRank(parent)
      if parentRank == nil then
        return nil
      end
      value = math.max(value, parentRank + 1)
    end
    visiting[name] = nil
    rank[name] = value
    return value
  end
  local maxRank = 0
  for _, name in ipairs(graph.order) do
    local value = prerequisiteRank(name)
    if value == nil then
      return nil
    end
    maxRank = math.max(maxRank, value)
  end
  local lateMerges = 0
  for _, name in ipairs(graph.order) do
    if rank[name] >= maxRank - 1 and #(graph.nodes[name].parents or {}) >= 2 then
      lateMerges = lateMerges + 1
    end
  end
  if
    lateMerges < math.max(3, math.ceil(#graph.order * 0.1))
    or (maximumIndegree < 3 and maximumOutdegree < 5)
  then
    return nil
  end
  return {
    rank = rank,
    maxRank = maxRank,
    edges = edgeCount,
    lateMerges = lateMerges,
    maxIn = maximumIndegree,
    maxOut = maximumOutdegree,
  }
end

function PromotionDenseLayoutEligible(graph)
  return denseGraphMetrics(graph) ~= nil
end

local function cloneRoute(route)
  local copy = {
    parent = route.parent,
    child = route.child,
    dim = route.dim,
    originalKey = route.originalKey,
    points = {},
    gaps = {},
  }
  for _, point in ipairs(route.points or {}) do
    copy.points[#copy.points + 1] = { x = point.x, y = point.y }
  end
  for _, gap in ipairs(route.gaps or {}) do
    copy.gaps[#copy.gaps + 1] = { segment = gap.segment, from = gap.from, to = gap.to }
  end
  return copy
end

local function copyOptions(source)
  local out = {}
  for key, value in pairs(source or {}) do
    out[key] = value
  end
  return out
end

local function edgePresent(routes, parent, child)
  for _, route in ipairs(routes or {}) do
    if route.parent == parent and route.child == child then
      return true
    end
  end
  return false
end

local function layoutScore(layout, accepted, rendered, native)
  return #(layout.routes or {}) * 100
    + (accepted and 30 or 0)
    + (rendered and 20 or 0)
    + (native and 10 or 0)
end

local function checkCandidate(graph, layout, geometry)
  local accepted = false
  if type(PromotionCheckLayout) == "function" then
    local ok, value = pcall(PromotionCheckLayout, graph, layout, geometry)
    accepted = ok and value == true
  end
  local rendered = false
  if type(PromotionRenderedCardClear) == "function" then
    local ok, value =
      pcall(PromotionRenderedCardClear, layout, geometry.buttonW, geometry.buttonH, 160)
    rendered = ok and value == true
  end
  local native = false
  if type(PipeManagerValidateNetwork) == "function" then
    local combined = layout.paintedRoutes
    if not combined then
      combined = {}
      for _, route in ipairs(layout.sourceRoutes or {}) do
        combined[#combined + 1] = route
      end
      for _, route in ipairs(layout.routes or {}) do
        combined[#combined + 1] = route
      end
    end
    local ok, value = pcall(
      PipeManagerValidateNetwork,
      combined,
      { scale = layout.scale, nativeArt = (layout.scale or 1) < 0.999 }
    )
    native = ok and value == true
  end
  return accepted, rendered, native
end

local function copyButtons(buttons)
  local out = {}
  for _, button in ipairs(buttons or {}) do
    out[#out + 1] = { type = button.type, x = button.x, y = button.y }
  end
  return out
end

local function makePlacement(graph, stats, geometry, warmStart)
  if type(warmStart) ~= "table" or type(warmStart.buttons) ~= "table" then
    return nil
  end
  local baseW = geometry.defaultW or geometry.viewportW
  local baseH = geometry.defaultH or geometry.viewportH
  local viewportW, viewportH = geometry.viewportW or baseW, geometry.viewportH or baseH
  if
    not (baseW and baseW > 0 and baseH and baseH > 0 and geometry.buttonW and geometry.buttonH)
  then
    return nil
  end

  -- A proportional 150% area canvas keeps the viewport aspect ratio. At this
  -- limit, the art is fitted at 1/sqrt(1.5) and native card clearance is the
  -- dominant constraint for the final columns.
  local factor = math.sqrt(1.5)
  local width, height = baseW * factor, baseH * factor
  local scale = math.min(viewportW / width, viewportH / height)
  local buttonW, buttonH = geometry.buttonW, geometry.buttonH
  local warmScale =
    math.min(baseW / (warmStart.width or baseW), baseH / (warmStart.height or baseH))
  if warmScale <= 0 then
    warmScale = 1
  end
  local baseY, orderIndex = {}, {}
  for i, name in ipairs(graph.order) do
    orderIndex[name] = i
  end
  local minX, maxRight = math.huge, -math.huge
  for _, button in ipairs(warmStart.buttons) do
    baseY[button.type] = button.y * warmScale
    minX = math.min(minX, button.x * warmScale)
    maxRight = math.max(maxRight, (button.x + buttonW) * warmScale)
  end
  for _, name in ipairs(graph.order) do
    if baseY[name] == nil then
      return nil
    end
  end
  -- Start one logical corridor pixel before the rounded warm-start edge;
  -- the fixed +2 native-art phase below then stays aligned after reflow.
  local left = math.max(24, math.floor(minX + 0.5) - 1)
  local rightMargin = math.max(24, math.floor(baseW - maxRight + 0.5))

  local rank, maxRank = stats.rank, stats.maxRank
  local spilled, spillSteps, chainMember = {}, {}, {}
  for _, name in ipairs(graph.order) do
    if rank[name] >= maxRank - 1 and #(graph.nodes[name].parents or {}) >= 2 then
      spilled[name] = true
      spillSteps[name] = 1
    end
  end
  for _, rawChain in ipairs(graph.chains or {}) do
    local chain = rawChain.nodes or rawChain
    local first
    for _, name in ipairs(chain) do
      chainMember[name] = true
    end
    for i, name in ipairs(chain) do
      if spilled[name] then
        first = i
        break
      end
    end
    if first then
      for i = first, #chain do
        spilled[chain[i]] = true
        spillSteps[chain[i]] = 1
      end
    end
  end

  -- Spread independent late leaves across later rank columns by minimizing
  -- repeated parent fans and terminal-column load, never by edge-name order.
  local fanLoad, columnLoad = {}, {}
  for _, rawChain in ipairs(graph.chains or {}) do
    local chain = rawChain.nodes or rawChain
    local first
    for i, name in ipairs(chain) do
      if spilled[name] then
        first = i
        break
      end
    end
    if first then
      local head = chain[first]
      local dest = rank[head] + 1
      for _, parent in ipairs(graph.nodes[head].parents or {}) do
        fanLoad[parent] = fanLoad[parent] or {}
        fanLoad[parent][dest] = (fanLoad[parent][dest] or 0) + 1
      end
      columnLoad[dest] = (columnLoad[dest] or 0) + 1
    end
  end
  local leaves = {}
  for _, name in ipairs(graph.order) do
    if
      spilled[name]
      and not chainMember[name]
      and rank[name] >= maxRank - 2
      and #(graph.nodes[name].children or {}) == 0
    then
      leaves[#leaves + 1] = name
    end
  end
  table.sort(leaves, function(a, b)
    local pa, pb = graph.nodes[a].parents or {}, graph.nodes[b].parents or {}
    if #pa ~= #pb then
      return #pa > #pb
    end
    local function parentCenter(name)
      local total, count = 0, 0
      for _, parent in ipairs(graph.nodes[name].parents or {}) do
        total = total + (baseY[parent] or 0)
        count = count + 1
      end
      return count > 0 and total / count or math.huge
    end
    local ca, cb = parentCenter(a), parentCenter(b)
    if ca ~= cb then
      return ca < cb
    end
    return orderIndex[a] < orderIndex[b]
  end)
  for _, name in ipairs(leaves) do
    local first, last = rank[name] + 1, math.min(maxRank + 1, rank[name] + 2)
    local best, bestScore = first, math.huge
    for c = first, last do
      local score = (columnLoad[c] or 0) * 0.25
      for _, parent in ipairs(graph.nodes[name].parents or {}) do
        score = score + ((fanLoad[parent] or {})[c] or 0)
      end
      if score < bestScore then
        best, bestScore = c, score
      end
    end
    spillSteps[name] = best - rank[name]
    columnLoad[best] = (columnLoad[best] or 0) + #(graph.nodes[name].parents or {})
    for _, parent in ipairs(graph.nodes[name].parents or {}) do
      fanLoad[parent] = fanLoad[parent] or {}
      fanLoad[parent][best] = (fanLoad[parent][best] or 0) + 1
    end
  end

  local column = {}
  for _, name in ipairs(graph.order) do
    column[name] = rank[name] + (spillSteps[name] or 0)
  end
  for _, rawChain in ipairs(graph.chains or {}) do
    local chain = rawChain.nodes or rawChain
    local first
    for i, name in ipairs(chain) do
      if spilled[name] then
        first = i
        break
      end
    end
    if first then
      for i = first + 1, #chain do
        local prior, name = chain[i - 1], chain[i]
        column[name] = math.max(column[name], column[prior] + 1)
      end
    end
  end
  local columns = maxRank + 2
  for _, name in ipairs(graph.order) do
    columns = math.max(columns, column[name] + 1)
  end
  if columns < 2 then
    return nil
  end
  local pitch = (width - left - rightMargin - buttonW) / (columns - 1)
  if pitch < buttonW + 16 then
    return nil
  end

  local unitOf, units = {}, {}
  for _, rawChain in ipairs(graph.chains or {}) do
    local chain = rawChain.nodes or rawChain
    local first
    for i, name in ipairs(chain) do
      if spilled[name] then
        first = i
        break
      end
    end
    if first then
      local unit = { members = {}, key = chain[first], baseRow = baseY[chain[first]] * factor }
      for i = first, #chain do
        local name = chain[i]
        unit.members[#unit.members + 1] = name
        unitOf[name] = unit
      end
      units[#units + 1] = unit
    end
  end
  for _, name in ipairs(graph.order) do
    if spilled[name] and not unitOf[name] then
      local unit = { members = { name }, key = name, baseRow = baseY[name] * factor }
      unitOf[name] = unit
      units[#units + 1] = unit
    end
  end
  if #units == 0 then
    return nil
  end
  for _, unit in ipairs(units) do
    unit.parents = {}
    local inside = {}
    for _, name in ipairs(unit.members) do
      inside[name] = true
    end
    for _, name in ipairs(unit.members) do
      for _, parent in ipairs(graph.nodes[name].parents or {}) do
        if not inside[parent] then
          unit.parents[#unit.parents + 1] = parent
        end
      end
    end
  end

  local rows, rowSeen = {}, {}
  for _, name in ipairs(graph.order) do
    local key = math.floor(baseY[name] * factor + 0.5)
    if not rowSeen[key] then
      rows[#rows + 1] = key
      rowSeen[key] = true
    end
  end
  table.sort(rows)
  if #rows < #units then
    return nil
  end
  local function scheduleCost(unit, y)
    local total = 0
    for _, parent in ipairs(unit.parents) do
      total = total + math.abs(y - baseY[parent] * factor)
      if
        #(graph.nodes[parent].children or {}) >= 4 and math.abs(y - baseY[parent] * factor) < 1
      then
        total = total + 10000
      end
    end
    local inside = {}
    for _, name in ipairs(unit.members) do
      inside[name] = true
    end
    for _, name in ipairs(graph.order) do
      if
        not spilled[name]
        and column[name] == column[unit.key]
        and math.abs(y - baseY[name] * factor) < buttonH + 8
      then
        total = total + 100000
      end
    end
    return total + 0.25 * math.abs(y - unit.baseRow)
  end

  local assignedRows = {}
  if #units <= 14 and #rows <= 16 then
    local memo, choice = {}, {}
    local function solve(i, mask)
      if i > #units then
        return 0
      end
      local key = i .. ":" .. mask
      if memo[key] ~= nil then
        return memo[key]
      end
      local best = math.huge
      for r = 1, #rows do
        local bit = 2 ^ (r - 1)
        if math.floor(mask / bit) % 2 == 0 then
          local score = scheduleCost(units[i], rows[r]) + solve(i + 1, mask + bit)
          if score < best then
            best = score
            choice[key] = r
          end
        end
      end
      memo[key] = best
      return best
    end
    solve(1, 0)
    local mask = 0
    for i = 1, #units do
      local key = i .. ":" .. mask
      local r = choice[key]
      if not r then
        return nil
      end
      assignedRows[units[i]] = rows[r]
      mask = mask + 2 ^ (r - 1)
    end
  else
    -- A bounded greedy assignment is a safe fallback for exceptionally wide
    -- rank schedules; every resulting card still faces the strict validators.
    local used = {}
    for _, unit in ipairs(units) do
      local best, bestScore
      for _, row in ipairs(rows) do
        if not used[row] then
          local score = scheduleCost(unit, row)
          if not bestScore or score < bestScore then
            best, bestScore = row, score
          end
        end
      end
      if not best then
        return nil
      end
      assignedRows[unit] = best
      used[best] = true
    end
  end

  local yOf = {}
  for _, name in ipairs(graph.order) do
    yOf[name] = baseY[name] * factor
  end
  for unit, y in pairs(assignedRows) do
    for _, name in ipairs(unit.members) do
      yOf[name] = y
    end
  end
  local buttons, buttonOf = {}, {}
  for _, name in ipairs(graph.order) do
    local button = {
      type = name,
      x = math.floor(left + column[name] * pitch + 0.5) + 2,
      y = math.floor(yOf[name] + 0.5),
    }
    buttons[#buttons + 1] = button
    buttonOf[name] = button
  end
  return {
    buttons = buttons,
    width = width,
    height = height,
    scale = scale,
    column = column,
    columns = columns,
    rowUnits = #units,
    buttonOf = buttonOf,
    baseW = baseW,
    baseH = baseH,
    viewportW = viewportW,
    viewportH = viewportH,
  }
end

local function routeDense(graph, placement, geometry)
  local options = copyOptions(geometry)
  options.width, options.height = placement.width, placement.height
  options.scale = placement.scale
  options.viewportW, options.viewportH = placement.viewportW, placement.viewportH
  options.defaultW, options.defaultH = placement.baseW, placement.baseH
  options.pipeHalfWidth = (geometry.pipeHalfWidth or 4) + 9
  options.cornerHalfW = (geometry.cornerHalfW or 16) + 3
  options.cornerHalfH = (geometry.cornerHalfH or 21) + 9
  options.padding = geometry.padding or 24
  options.underpassHalfGap = geometry.underpassHalfGap or 10
  options.maxPortPairs = 8
  options.maxSearchStates = 3000
  options.provenNonplanar = type(PromotionNonplanarCertificate) == "function"
      and PromotionNonplanarCertificate(graph) ~= nil
    or false
  local edgeCount = 0
  for _, name in ipairs(graph.order) do
    edgeCount = edgeCount + #(graph.nodes[name].parents or {})
  end
  options.readabilityCrossingBudget = geometry.readabilityCrossingBudget or 2 * edgeCount
  options.allowReadabilityCrossings = options.readabilityCrossingBudget > 0
  options.seededRoutes = nil
  options.routeOrder = nil
  local layout = PromotionLayoutRoute(graph, placement.buttons, options)
  layout.method = "dense-degree-spill"
  return layout, options
end

function PromotionDenseLayoutSolve(graph, geometry, warmStart)
  local stats = denseGraphMetrics(graph)
  if not stats or type(PromotionLayoutRoute) ~= "function" then
    return nil
  end
  local placement = makePlacement(graph, stats, geometry, warmStart)
  if not placement then
    return nil
  end
  local layout, routeOpts = routeDense(graph, placement, geometry)
  local accepted, rendered, native = checkCandidate(graph, layout, geometry)
  if accepted and rendered and native then
    return layout
  end

  local best = layout
  local bestScore = layoutScore(best, accepted, rendered, native)
  local missing = {}
  local graphOrder = {}
  for i, name in ipairs(graph.order) do
    graphOrder[name] = i
  end
  for _, child in ipairs(graph.order) do
    for _, parent in ipairs(graph.nodes[child].parents or {}) do
      if not edgePresent(layout.routes, parent, child) then
        missing[#missing + 1] = { parent = parent, child = child }
      end
    end
  end
  local attempts = 0
  for _, edge in ipairs(missing) do
    local candidates = {}
    for i, route in ipairs(layout.routes or {}) do
      if route.child == edge.child or route.parent == edge.parent then
        local length = 0
        for k = 1, #(route.points or {}) - 1 do
          local a, b = route.points[k], route.points[k + 1]
          length = length + math.abs(a.x - b.x) + math.abs(a.y - b.y)
        end
        candidates[#candidates + 1] = {
          index = i,
          route = route,
          score = route.child == edge.child and 0 or 1,
          length = length,
        }
      end
    end
    table.sort(candidates, function(a, b)
      if a.score ~= b.score then
        return a.score < b.score
      end
      if a.length ~= b.length then
        return a.length > b.length
      end
      local ap, bp =
        graphOrder[a.route.parent] or math.huge, graphOrder[b.route.parent] or math.huge
      if ap ~= bp then
        return ap < bp
      end
      local ac, bc = graphOrder[a.route.child] or math.huge, graphOrder[b.route.child] or math.huge
      return ac < bc
    end)
    for _, item in ipairs(candidates) do
      if attempts >= 5 then
        break
      end
      attempts = attempts + 1
      local trialOpts = copyOptions(routeOpts)
      trialOpts.fanTrunks = false
      trialOpts.rootMergeFirst = false
      trialOpts.seededRoutes = {}
      for i, route in ipairs(layout.routes or {}) do
        if i ~= item.index then
          trialOpts.seededRoutes[#trialOpts.seededRoutes + 1] = cloneRoute(route)
        end
      end
      trialOpts.routeOrder = { edge, { parent = item.route.parent, child = item.route.child } }
      local trial = PromotionLayoutRoute(graph, placement.buttons, trialOpts)
      trial.method = "dense-ripup"
      local check, clear, pipe = checkCandidate(graph, trial, geometry)
      local score = layoutScore(trial, check, clear, pipe)
      if score > bestScore then
        best, bestScore = trial, score
      end
      if check and clear and pipe then
        return trial
      end
    end
    if attempts >= 5 then
      break
    end
  end
  -- Keep a complete, card-clear route set for the chooser's existing bounded
  -- local repair pass; this can repair near-pipe checks without re-solving.
  return best
end

return { eligible = PromotionDenseLayoutEligible, solve = PromotionDenseLayoutSolve }
