-- Geometry reuse and crossing presentation. No game state or UI controls here.
local cache, cacheAccessOrder, cacheHitCount, layoutSolveCount = {}, 0, 0, 0
local LAYOUT_CACHE_LIMIT = 48
local function encodeKeyPart(v)
  local s = tostring(v or "")
  return #s .. ":" .. s
end
local EMPTY_LIST = {}
local function sortedCopy(values)
  -- Callers only iterate the result. Zero/one-item lists are already sorted.
  if not values then
    return EMPTY_LIST
  end
  if #values < 2 then
    return values
  end
  local out = {}
  for _, value in ipairs(values or {}) do
    out[#out + 1] = value
  end
  table.sort(out)
  return out
end
function PromotionLayoutKey(graph, geometry)
  local out = { "presentation-v4-dense-fallback" }
  for _, name in ipairs(sortedCopy(graph.order)) do
    out[#out + 1] = encodeKeyPart(name)
    local node = graph.nodes[name]
    out[#out + 1] = encodeKeyPart(node.name) .. encodeKeyPart(node.family)
    for _, p in ipairs(sortedCopy(node.parents)) do
      out[#out + 1] = encodeKeyPart(p)
    end
    out[#out + 1] = ";" .. encodeKeyPart(node.requiredPrereq)
    for _, p in ipairs(sortedCopy(node.orPrereqs)) do
      out[#out + 1] = encodeKeyPart(p)
    end
  end
  out[#out + 1] = "roots"
  for _, name in ipairs(sortedCopy(graph.roots)) do
    out[#out + 1] = encodeKeyPart(name)
  end
  local chains = {}
  for _, chain in ipairs(graph.chains or {}) do
    local members = chain.nodes or chain
    local parts = {}
    for _, name in ipairs(members) do
      parts[#parts + 1] = encodeKeyPart(name)
    end
    chains[#chains + 1] = table.concat(parts, "|")
  end
  table.sort(chains)
  for _, chain in ipairs(chains) do
    out[#out + 1] = "chain" .. chain
  end
  local keys = {}
  for k, v in pairs(geometry) do
    if type(v) == "number" or type(v) == "string" or type(v) == "boolean" then
      keys[#keys + 1] = k
    end
  end
  table.sort(keys)
  for _, k in ipairs(keys) do
    out[#out + 1] = encodeKeyPart(k) .. encodeKeyPart(geometry[k])
  end
  return table.concat(out, "|")
end

-- Run the exact LR planarity test on the effective prerequisite graph. This
-- remains correct when a mod adds promotions or changes Zulu prerequisites.
function PromotionNonplanarCertificate(graph)
  if type(PromotionPlanarEmbedding) ~= "function" then
    return nil
  end
  local _, reason, status = PromotionPlanarEmbedding(graph, false)
  if status ~= "nonplanar" then
    return nil
  end
  return { kind = "lr_nonplanar", reason = reason }
end

local function between(v, a, b)
  return v > math.min(a, b) + 0.01 and v < math.max(a, b) - 0.01
end
local function cross(a, b, c, d)
  if a.y == b.y and c.x == d.x and between(c.x, a.x, b.x) and between(a.y, c.y, d.y) then
    return c.x, a.y
  end
  if a.x == b.x and c.y == d.y and between(a.x, c.x, d.x) and between(c.y, a.y, b.y) then
    return a.x, c.y
  end
end
local function distance(a, b)
  return math.abs(a.x - b.x) + math.abs(a.y - b.y)
end

-- The logical tree may be fitted, but its painted cards have a fixed width.
-- Centering each card on its logical rectangle preserves top/bottom ports;
-- only left/right endpoints and the body-height top/bottom contacts move.
function PromotionPaintedRoutes(layout, buttonW, buttonH, cardW)
  if
    type(layout) ~= "table"
    or type(layout.buttons) ~= "table"
    or type(buttonW) ~= "number"
    or type(buttonH) ~= "number"
    or type(cardW) ~= "number"
  then
    return nil, nil, "rendered card geometry is unavailable"
  end
  local scale = layout.scale or 1
  local portraitH = buttonH == 46 and 45 or buttonH == 60 and 64 or buttonH
  local bodyH = buttonH == 60 and 48 or portraitH - 2
  local ringInset = buttonH == 46 and 2 or 8
  local cards, byType, routes = {}, {}, {}
  local function pixel(v)
    return math.floor(v + 0.5)
  end
  for _, button in ipairs(layout.buttons) do
    local x = pixel(button.x * scale + (buttonW * scale - cardW) / 2)
    local y = pixel(button.y * scale + (buttonH * scale - portraitH) / 2)
    local card = {
      type = button.type,
      x = x,
      y = buttonH == 46 and y - 1 or y,
      right = x + cardW,
      bottom = y + portraitH,
      bodyTop = buttonH == 46 and y or y + pixel((portraitH - bodyH) / 2),
      bodyBottom = buttonH == 46 and y + 43 or y + pixel((portraitH - bodyH) / 2) + bodyH,
      logical = button,
    }
    cards[#cards + 1] = card
    byType[button.type] = card
  end
  local function append(route)
    local copy =
      { parent = route.parent, child = route.child, dim = route.dim, gaps = {}, points = {} }
    for _, gap in ipairs(route.gaps or {}) do
      copy.gaps[#copy.gaps + 1] = { segment = gap.segment, from = gap.from, to = gap.to }
    end
    for _, point in ipairs(route.points or {}) do
      copy.points[#copy.points + 1] = { x = point.x, y = point.y }
    end
    local p = copy.points
    if #p < 2 then
      return nil, "painted route has fewer than two points"
    end
    local parent, child = byType[route.parent], byType[route.child]
    local function move(point, neighbor, card)
      local b = card.logical
      if (point.y == b.y or point.y == b.y + buttonH) and point.x == neighbor.x then
        local portX = pixel(point.x * scale)
        if portX < card.x + 2 or portX > card.right - 2 then
          return false, "top/bottom pipe misses fixed card: " .. card.type
        end
      end
      if point.x == b.x and point.y == neighbor.y then
        point.x = (card.x + ringInset) / scale
      elseif point.x == b.x + buttonW and point.y == neighbor.y then
        point.x = card.right / scale
      elseif point.y == b.y and point.x == neighbor.x then
        point.y = card.bodyTop / scale
      elseif point.y == b.y + buttonH and point.x == neighbor.x then
        point.y = card.bodyBottom / scale
      end
      return true
    end
    if parent then
      local old = p[1].x == p[2].x and math.abs(p[2].y - p[1].y) or math.abs(p[2].x - p[1].x)
      local okay, reason = move(p[1], p[2], parent)
      if not okay then
        return nil, reason
      end
      local new = p[1].x == p[2].x and math.abs(p[2].y - p[1].y) or math.abs(p[2].x - p[1].x)
      for _, gap in ipairs(copy.gaps) do
        if gap.segment == 1 then
          gap.from = gap.from + new - old
          gap.to = gap.to + new - old
        end
      end
    end
    if child then
      local okay, reason = move(p[#p], p[#p - 1], child)
      if not okay then
        return nil, reason
      end
    end
    routes[#routes + 1] = copy
    return true
  end
  for _, route in ipairs(layout.sourceRoutes or {}) do
    local okay, reason = append(route)
    if not okay then
      return nil, nil, reason
    end
  end
  for _, route in ipairs(layout.routes or {}) do
    local okay, reason = append(route)
    if not okay then
      return nil, nil, reason
    end
  end
  return routes, cards
end

-- Reject routes hidden behind another painted card and native-art junctions
-- invalidated by the last few pixels of port adjustment.
function PromotionRenderedCardClear(layout, buttonW, buttonH, cardW)
  cardW = cardW or 160
  local audited = type(layout) == "table" and layout.paintedAudit
  if
    audited
    and audited.buttonW == buttonW
    and audited.buttonH == buttonH
    and audited.cardW == cardW
  then
    return audited.ok, audited.reason
  end
  local routes, cards, reason = PromotionPaintedRoutes(layout, buttonW, buttonH, cardW)
  if not routes then
    return false, reason
  end
  local function finish(ok, detail)
    layout.paintedAudit =
      { buttonW = buttonW, buttonH = buttonH, cardW = cardW, ok = ok, reason = detail }
    if ok then
      layout.paintedRoutes = routes
      layout.paintedCards = cards
    end
    return ok, detail
  end
  local scale = layout.scale or 1
  for _, card in ipairs(cards) do
    if
      card.x < 0
      or card.y < 0
      or (layout.width and card.right > layout.width * scale + 0.01)
      or (layout.height and card.bottom > layout.height * scale + 0.01)
    then
      return finish(false, "painted card exceeds fixed canvas: " .. card.type)
    end
  end
  if type(PipeManagerValidateNetwork) == "function" then
    local okay, nativeReason =
      PipeManagerValidateNetwork(routes, { scale = scale, nativeArt = scale < 0.999 })
    if not okay then
      return finish(false, "painted pipe: " .. tostring(nativeReason))
    end
  end
  local pad = 4
  for _, route in ipairs(routes) do
    for segment = 1, #(route.points or {}) - 1 do
      local a, b = route.points[segment], route.points[segment + 1]
      local ax, ay, bx, by = a.x * scale, a.y * scale, b.x * scale, b.y * scale
      for _, card in ipairs(cards) do
        if
          not (card.type == route.parent and segment == 1)
          and not (card.type == route.child and segment == #route.points - 1)
        then
          local touches = false
          if ay == by then
            touches = ay > card.y - pad
              and ay < card.bottom + pad
              and math.max(ax, bx) > card.x - pad
              and math.min(ax, bx) < card.right + pad
          elseif ax == bx then
            touches = ax > card.x - pad
              and ax < card.right + pad
              and math.max(ay, by) > card.y - pad
              and math.min(ay, by) < card.bottom + pad
          end
          if touches then
            return finish(false, route.parent .. " -> " .. route.child .. " near " .. card.type)
          end
        end
      end
    end
  end
  return finish(true)
end

-- Center the *rendered* diagram inside the visible tree panel. The solver's
-- coordinates and all relative card/pipe positions stay untouched, including
-- the cached and reviewed layouts. A little clearance covers the native pipe
-- artwork around its centerline, so a tall tree remains within the viewport.
function PromotionTreeVerticalOffset(
  layout,
  viewportH,
  buttonW,
  buttonH,
  cardW,
  routes,
  sourceTargetY
)
  if not layout or type(viewportH) ~= "number" or viewportH <= 0 then
    return 0
  end
  local cards = layout.paintedCards
  if not cards then
    local _, paintedCards = PromotionPaintedRoutes(layout, buttonW, buttonH, cardW)
    cards = paintedCards
  end
  if not cards or #cards == 0 then
    return 0
  end
  local scale = layout.scale or 1
  local top, bottom = math.huge, -math.huge
  for _, card in ipairs(cards) do
    top = math.min(top, card.y)
    bottom = math.max(bottom, card.bottom)
  end
  local function includeRoutes(list)
    for _, route in ipairs(list or {}) do
      for _, point in ipairs(route.points or {}) do
        local y = point.y * scale
        -- Native TechBranches elbows reach 26px above a contact point;
        -- TechBranchH reaches 31px below it. Their fixed-size artwork is not
        -- scaled down with the logical tree at every junction.
        top = math.min(top, y - 26)
        bottom = math.max(bottom, y + 31)
      end
    end
  end
  if routes or layout.paintedRoutes then
    -- Painted routes already contain both prerequisites and source feeds.
    includeRoutes(routes or layout.paintedRoutes)
  else
    includeRoutes(layout.routes)
    includeRoutes(layout.sourceRoutes)
  end
  if layout.source then
    top = math.min(top, layout.source.y * scale - 26)
    bottom = math.max(bottom, layout.source.y * scale + 31)
  end
  local clearance = 8
  if bottom - top + 2 * clearance >= viewportH then
    return 0
  end
  -- Translate the whole tree, without changing its internal layout, when its
  -- source can meet the sidebar centre while all painted bounds still fit.
  if sourceTargetY and layout.source then
    local aligned = sourceTargetY - layout.source.y * scale
    if aligned >= clearance - top and aligned <= viewportH - clearance - bottom then
      return aligned
    end
  end
  local desired = math.floor((viewportH - top - bottom) / 2 + 0.5)
  return math.max(clearance - top, math.min(desired, viewportH - clearance - bottom))
end

function PromotionPrepareUnderpasses(layout, graph, geometry)
  layout.underpasses = {}
  layout.underpassOrientation = {}
  layout.nonplanarCertificate = PromotionNonplanarCertificate(graph)
  local routes = {}
  for _, r in ipairs(layout.routes or {}) do
    routes[#routes + 1] = r
  end
  for _, r in ipairs(layout.sourceRoutes or {}) do
    routes[#routes + 1] = r
  end
  for _, r in ipairs(routes) do
    r.gaps = {}
  end
  local crossings = 0
  -- Bring each underpass run two rendered pixels closer to the overpass.
  -- Gaps are stored in logical coordinates, while the requested clearance
  -- change is in screen pixels and must survive uniformly fitted layouts.
  local halfGap = (geometry.underpassHalfGap or 10) - 2 / (layout.scale or 1)
  local underAtPoint = {}
  local function endpointClearance(horizontal, x, y)
    local nearest = math.huge
    for _, route in ipairs(routes) do
      for k = 1, #route.points - 1 do
        local a, b = route.points[k], route.points[k + 1]
        if
          (horizontal and a.y == b.y and a.y == y)
          or (not horizontal and a.x == b.x and a.x == x)
        then
          nearest = math.min(
            nearest,
            horizontal and math.min(math.abs(x - a.x), math.abs(x - b.x))
              or math.min(math.abs(y - a.y), math.abs(y - b.y))
          )
        end
      end
    end
    return nearest
  end
  for i = 1, #routes do
    for j = i + 1, #routes do
      local r, s = routes[i], routes[j]
      for ri = 1, #r.points - 1 do
        for si = 1, #s.points - 1 do
          local a, b, c, d = r.points[ri], r.points[ri + 1], s.points[si], s.points[si + 1]
          local x, y = cross(a, b, c, d)
          if x then
            crossings = crossings + 1
            if
              layout.nonplanarCertificate
              or (
                type(geometry.readabilityCrossingBudget) == "number"
                and geometry.readabilityCrossingBudget > 0
              )
            then
              local under, over, index, first, last = r, s, ri, a, b
              local horizontalRoute, horizontalIndex, hFirst, hLast
              local verticalRoute, verticalIndex, vFirst, vLast
              if a.y == b.y then
                horizontalRoute, horizontalIndex, hFirst, hLast = r, ri, a, b
                verticalRoute, verticalIndex, vFirst, vLast = s, si, c, d
              else
                horizontalRoute, horizontalIndex, hFirst, hLast = s, si, c, d
                verticalRoute, verticalIndex, vFirst, vLast = r, ri, a, b
              end
              local pointKey = x .. "|" .. y
              local horizontalUnder = underAtPoint[pointKey]
              if horizontalUnder == nil then
                horizontalUnder = layout.underpassOverrides and layout.underpassOverrides[pointKey]
                if horizontalUnder == nil then
                  horizontalUnder = endpointClearance(true, x, y) > endpointClearance(false, x, y)
                end
                underAtPoint[pointKey] = horizontalUnder
                layout.underpassOrientation[pointKey] = horizontalUnder
              end
              if horizontalUnder then
                under, over, index, first, last =
                  horizontalRoute, verticalRoute, horizontalIndex, hFirst, hLast
              else
                under, over, index, first, last =
                  verticalRoute, horizontalRoute, verticalIndex, vFirst, vLast
              end
              local at = distance(first, { x = x, y = y })
              local length = distance(first, last)
              local from, to = math.max(0, at - halfGap), math.min(length, at + halfGap)
              -- Several logical edges may share one visible overpass. Keep
              -- every crossing record, but cut its physical gap only once.
              local alreadyCut = false
              for _, gap in ipairs(under.gaps) do
                if gap.segment == index and gap.from == from and gap.to == to then
                  alreadyCut = true
                  break
                end
              end
              if not alreadyCut then
                under.gaps[#under.gaps + 1] = { segment = index, from = from, to = to }
              end
              layout.underpasses[#layout.underpasses + 1] = {
                x = x,
                y = y,
                under = { parent = under.parent, child = under.child },
                over = { parent = over.parent, child = over.child },
              }
            end
          end
        end
      end
    end
  end
  layout.crossings = crossings
  return layout
end
-- A right/up/right route is monotone; right/up/left doubles back on X.
-- Score both axes so changing the dominant orientation does not hide detours.
function PromotionRouteReadability(layout)
  local score = {
    backtrackingRoutes = 0,
    axisReversals = 0,
    backtrackingPixels = 0,
    bends = 0,
    totalLength = 0,
  }
  local all = {}
  for _, route in ipairs(layout.routes or {}) do
    all[#all + 1] = route
  end
  for _, route in ipairs(layout.sourceRoutes or {}) do
    all[#all + 1] = route
  end
  for _, route in ipairs(all) do
    local points = route.points or {}
    local sx, sy, lastAxis, reversals, length = 0, 0, nil, 0, 0
    for i = 2, #points do
      local dx, dy = points[i].x - points[i - 1].x, points[i].y - points[i - 1].y
      local axis
      if math.abs(dx) > 0.001 then
        local sign = dx > 0 and 1 or -1
        if sx ~= 0 and sign ~= sx then
          reversals = reversals + 1
        end
        sx, axis = sign, "x"
      end
      if math.abs(dy) > 0.001 then
        local sign = dy > 0 and 1 or -1
        if sy ~= 0 and sign ~= sy then
          reversals = reversals + 1
        end
        sy, axis = sign, "y"
      end
      if axis and lastAxis and axis ~= lastAxis then
        score.bends = score.bends + 1
      end
      if axis then
        lastAxis = axis
      end
      length = length + math.abs(dx) + math.abs(dy)
    end
    if reversals > 0 then
      score.backtrackingRoutes = score.backtrackingRoutes + 1
    end
    score.axisReversals = score.axisReversals + reversals
    if #points >= 2 then
      local first, last = points[1], points[#points]
      score.backtrackingPixels = score.backtrackingPixels
        + math.max(0, (length - math.abs(last.x - first.x) - math.abs(last.y - first.y)) / 2)
    end
    score.totalLength = score.totalLength + length
  end
  return score
end

-- Verify the finished geometry independently of the solver's own scores.
function PromotionCheckLayout(graph, layout, geometry)
  PromotionPrepareUnderpasses(layout, graph, geometry)
  local checkGeometry = {}
  for k, v in pairs(geometry) do
    checkGeometry[k] = v
  end
  checkGeometry.defaultW = geometry.defaultW or geometry.viewportW
  checkGeometry.defaultH = geometry.defaultH or geometry.viewportH
  layout.solverViolations = layout.solverViolations or layout.violations or {}
  layout.violations = {}
  for _, issue in ipairs(layout.solverViolations) do
    layout.violations[#layout.violations + 1] = issue
  end
  local accepted, issues = PromotionLayoutAccept(graph, layout, checkGeometry)
  layout.acceptanceIssues = issues
  for _, issue in ipairs(issues) do
    layout.violations[#layout.violations + 1] = issue.code .. ": " .. issue.detail
  end
  if accepted and PipeManagerValidateNetwork then
    local routes = {}
    for _, route in ipairs(layout.sourceRoutes or {}) do
      routes[#routes + 1] = route
    end
    for _, route in ipairs(layout.routes or {}) do
      routes[#routes + 1] = route
    end
    local nativeOkay, nativeReason =
      PipeManagerValidateNetwork(routes, { scale = layout.scale, nativeArt = layout.scale < 0.999 })
    if not nativeOkay then
      local originalOverrides = {}
      for key, value in pairs(layout.underpassOverrides or {}) do
        originalOverrides[key] = value
      end
      local orientation = {}
      local sites = {}
      for key, value in pairs(layout.underpassOrientation or {}) do
        orientation[key] = value
        sites[#sites + 1] = key
      end
      table.sort(sites)
      for i = 1, math.min(#sites, 24) do
        local overrides = {}
        for key, value in pairs(originalOverrides) do
          overrides[key] = value
        end
        overrides[sites[i]] = not orientation[sites[i]]
        layout.underpassOverrides = overrides
        PromotionPrepareUnderpasses(layout, graph, geometry)
        local geometryOkay, trialIssues = PromotionLayoutAccept(graph, layout, checkGeometry)
        if geometryOkay then
          local pipeOkay = PipeManagerValidateNetwork(
            routes,
            { scale = layout.scale, nativeArt = layout.scale < 0.999 }
          )
          if pipeOkay then
            nativeOkay = true
            layout.acceptanceIssues = trialIssues
            break
          end
        end
      end
      if not nativeOkay then
        layout.underpassOverrides = originalOverrides
        PromotionPrepareUnderpasses(layout, graph, geometry)
      end
    end
    if not nativeOkay then
      layout.violations[#layout.violations + 1] = "native_art: " .. tostring(nativeReason)
    end
  end
  layout.valid = accepted and #layout.violations == 0
  if accepted then
    layout.readability = PromotionRouteReadability(layout)
  end
  return layout.valid
end
-- All candidates face the same independent acceptance gate. For a proved
-- nonplanar graph, fewer crossings outrank area, as agreed in the design review.
function PromotionLayoutBetter(candidate, current)
  if not current then
    return true
  end
  if candidate.crossings ~= current.crossings then
    return (candidate.crossings or 0) < (current.crossings or 0)
  end
  local candidateArea, currentArea =
    candidate.width * candidate.height, current.width * current.height
  if math.abs(candidateArea - currentArea) > 0.01 then
    return candidateArea < currentArea
  end
  local a, b =
    candidate.readability or PromotionRouteReadability(candidate),
    current.readability or PromotionRouteReadability(current)
  for _, key in ipairs({
    "backtrackingRoutes",
    "axisReversals",
    "backtrackingPixels",
    "bends",
    "totalLength",
  }) do
    if math.abs(a[key] - b[key]) > 0.001 then
      return a[key] < b[key]
    end
  end
  return false
end
local function cloneTable(value)
  if type(value) ~= "table" then
    return value
  end
  local out = {}
  for key, item in pairs(value) do
    out[key] = cloneTable(item)
  end
  return out
end

-- A single incoming edge should meet the centre of a card's left/right side
-- when the surrounding geometry permits it. Keep the original port whenever
-- the centred alternative fails the same independent artwork checks.
local function centerUnoccupiedPorts(graph, layout, geometry)
  if not layout or not layout.valid then
    return layout
  end
  local current = layout
  local cards = {}
  for _, card in ipairs(layout.buttons or {}) do
    cards[card.type] = card
  end
  for index, route in ipairs(layout.routes or {}) do
    local card = cards[route.child]
    local node = graph.nodes[route.child]
    local points = route.points or {}
    if card and node and #(node.parents or {}) == 1 and #points >= 3 then
      local last, prior = points[#points], points[#points - 1]
      local horizontal = prior.y == last.y and prior.x ~= last.x
      local side = last.x == card.x or last.x == card.x + geometry.buttonW
      local center = math.floor(card.y + geometry.buttonH / 2 + 0.5)
      if horizontal and side and math.abs(last.y - center) >= 3 then
        local trial = cloneTable(current)
        local altered = trial.routes[index].points
        altered[#altered].y = center
        altered[#altered - 1].y = center
        if
          PromotionCheckLayout(graph, trial, geometry)
          and (
            type(PromotionRenderedCardClear) ~= "function"
            or PromotionRenderedCardClear(trial, geometry.buttonW, geometry.buttonH, 160)
          )
        then
          current = trial
        end
      end
    end
  end
  return current
end
-- A bounded geometry nudge can clear a close pair of otherwise complete
-- routes without changing card placement, graph identity or canvas size.
local function repairRouteClearance(graph, layout, geometry)
  if
    not layout
    or layout.valid
    or not layout.stats
    or layout.stats.edges ~= layout.stats.routed
    or #(layout.solverViolations or {}) > 0
  then
    return layout
  end
  local current = layout
  for _ = 1, 2 do
    local implicated = {}
    for _, issue in ipairs(current.acceptanceIssues or {}) do
      if
        issue.code == "near_pipe"
        or issue.code == "corner_pipe_art"
        or issue.code == "false_junction"
        or issue.code == "pipe_card_art"
      then
        for index, route in ipairs(current.routes or {}) do
          local label = route.parent .. " -> " .. route.child
          if issue.detail:find(label, 1, true) then
            implicated[index] = true
          end
        end
      end
    end
    for _, issue in ipairs(current.violations or {}) do
      local axis, fixed, low, high = issue:match(
        "native_art: network segment too short for native junction art at ([HV]) ([%d%.%-]+):([%d%.%-]+)%.%.([%d%.%-]+)"
      )
      fixed, low, high = tonumber(fixed), tonumber(low), tonumber(high)
      if axis and fixed and low and high then
        for index, route in ipairs(current.routes or {}) do
          for k = 1, #route.points - 1 do
            local a, b = route.points[k], route.points[k + 1]
            if
              (
                axis == "V"
                and a.x == b.x
                and a.x == fixed
                and math.max(a.y, b.y) >= low
                and math.min(a.y, b.y) <= high
              )
              or (
                axis == "H"
                and a.y == b.y
                and a.y == fixed
                and math.max(a.x, b.x) >= low
                and math.min(a.x, b.x) <= high
              )
            then
              implicated[index] = true
            end
          end
        end
      end
    end
    local indices = {}
    for index in pairs(implicated) do
      indices[#indices + 1] = index
    end
    table.sort(indices)
    local improved = nil
    local tried = 0
    local buttonOf = {}
    for _, button in ipairs(current.buttons or {}) do
      buttonOf[button.type] = button
    end
    for _, index in ipairs(indices) do
      local route = current.routes[index]
      for _, which in ipairs({ "source", "target" }) do
        local points = route.points
        local first, last, card
        if which == "source" then
          first, last, card = 1, 2, buttonOf[route.parent]
        else
          first, last, card = #points - 1, #points, buttonOf[route.child]
        end
        if card then
          local horizontal = points[first].y == points[last].y
          local vertical = points[first].x == points[last].x
          for _, delta in ipairs({ -16, 16, -8, 8 }) do
            if tried >= (geometry.maxRepairTrials or 32) then
              break
            end
            local candidate = horizontal and points[first].y + delta
              or vertical and points[first].x + delta
            local low = horizontal and card.y + 8 or card.x + 8
            local high = horizontal and card.y + geometry.buttonH - 8
              or card.x + geometry.buttonW - 8
            if candidate and candidate >= low and candidate <= high then
              tried = tried + 1
              local variant = cloneTable(current)
              local altered = variant.routes[index].points
              if horizontal then
                altered[first].y = candidate
                altered[last].y = candidate
              else
                altered[first].x = candidate
                altered[last].x = candidate
              end
              if PromotionCheckLayout(graph, variant, geometry) then
                return variant
              end
              if
                #variant.violations < #current.violations
                and (not improved or #variant.violations < #improved.violations)
              then
                improved = variant
              end
            end
          end
        end
      end
      for segment = 2, #route.points - 2 do
        local a, b = route.points[segment], route.points[segment + 1]
        for _, delta in ipairs({ -8, 8, -16, 16, -24, 24, -32, 32 }) do
          if tried >= (geometry.maxRepairTrials or 32) then
            break
          end
          tried = tried + 1
          local variant = cloneTable(current)
          local points = variant.routes[index].points
          if a.x == b.x then
            points[segment].x = points[segment].x + delta
            points[segment + 1].x = points[segment + 1].x + delta
          elseif a.y == b.y then
            points[segment].y = points[segment].y + delta
            points[segment + 1].y = points[segment + 1].y + delta
          end
          local okay = PromotionCheckLayout(graph, variant, geometry)
          if okay then
            return variant
          end
          if
            #variant.violations < #current.violations
            and (not improved or #variant.violations < #improved.violations)
          then
            improved = variant
          end
        end
      end
      local parent, child = buttonOf[route.parent], buttonOf[route.child]
      if parent and child and parent.x + geometry.buttonW + 48 <= child.x then
        local sx, sy =
          parent.x + geometry.buttonW, math.floor(parent.y + geometry.buttonH / 2 + 0.5)
        local tx, ty = child.x, math.floor(child.y + geometry.buttonH / 2 + 0.5)
        local gap = tx - sx
        for _, fraction in ipairs({ 0.5, 0.33, 0.67 }) do
          local lane = math.floor(sx + gap * fraction + 0.5)
          local variant = cloneTable(current)
          variant.routes[index].points = {
            { x = sx, y = sy },
            { x = lane, y = sy },
            { x = lane, y = ty },
            { x = tx, y = ty },
          }
          if PromotionCheckLayout(graph, variant, geometry) then
            return variant
          end
        end
      end
    end
    if not improved then
      break
    end
    current = improved
  end
  -- Move a shared first trunk as one object. Nudging only one member would
  -- split a legitimate common source and create a false junction.
  local groups = {}
  for index, route in ipairs(current.routes or {}) do
    local p = route.points or {}
    if #p >= 4 and p[2].x == p[3].x then
      local key = route.parent .. "|" .. p[1].x .. "|" .. p[1].y .. "|" .. p[2].x
      local group = groups[key] or {}
      group[#group + 1] = index
      groups[key] = group
    end
  end
  local keys = {}
  for key, group in pairs(groups) do
    if #group >= 2 then
      keys[#keys + 1] = key
    end
  end
  table.sort(keys)
  for _, key in ipairs(keys) do
    for _, delta in ipairs({ -8, 8, -16, 16, -24, 24, -32, 32 }) do
      local variant = cloneTable(current)
      for _, index in ipairs(groups[key]) do
        local points = variant.routes[index].points
        points[2].x = points[2].x + delta
        points[3].x = points[3].x + delta
      end
      if PromotionCheckLayout(graph, variant, geometry) then
        return variant
      end
      if #variant.violations < #current.violations then
        current = variant
      end
    end
  end
  return current
end
function PromotionLayoutChoose(graph, geometry)
  -- Reviewed layouts are executable geometry, not preview-only images.
  -- Their graph signature must match, and they face the same independent
  -- geometry/native-art gate before any live controls are drawn.
  if type(PromotionReviewedLayout) == "function" then
    local built, reviewed, reviewGeometry, reviewName =
      pcall(PromotionReviewedLayout, graph, geometry)
    if built and reviewed then
      local checked, accepted = pcall(PromotionCheckLayout, graph, reviewed, reviewGeometry)
      if checked and accepted and type(PromotionRenderedCardClear) == "function" then
        local painted, clear =
          pcall(PromotionRenderedCardClear, reviewed, geometry.buttonW, geometry.buttonH, 160)
        accepted = painted and clear == true
      end
      if checked and accepted then
        reviewed.method = "reviewed"
        reviewed.reviewName = reviewName
        return reviewed
      end
      print("Promotion Tree reviewed layout rejected: " .. tostring(reviewName))
      for _, issue in ipairs(reviewed.violations or {}) do
        print("Promotion Tree: " .. tostring(issue))
      end
    end
  end
  local builders = {}
  local function add(name, solve)
    if type(solve) == "function" then
      builders[#builders + 1] = { name = name, solve = solve }
    end
  end
  if #(graph.roots or {}) >= 6 and #graph.roots * 2 > #graph.order then
    add("sparse", PromotionLayoutSolveSparse)
  end
  local genericFirst = #graph.order <= 18
  if genericFirst then
    add("layered", PromotionLayoutSolve)
  end
  if geometry.provenNonplanar then
    add("planarized", PromotionLayoutSolveNonplanar)
  else
    add("planar", PromotionLayoutSolvePlanar)
  end
  if not genericFirst then
    add("layered", PromotionLayoutSolve)
  end
  local best, failed
  for _, builder in ipairs(builders) do
    local ok, candidate, reason = pcall(builder.solve, graph, geometry)
    if ok and candidate then
      candidate.method = builder.name
      local checked, accepted = pcall(PromotionCheckLayout, graph, candidate, geometry)
      if checked and not accepted then
        local repaired, variant = pcall(repairRouteClearance, graph, candidate, geometry)
        if repaired and variant then
          candidate = variant
          accepted = variant.valid
        end
      end
      local rendered = true
      if checked and accepted and type(PromotionRenderedCardClear) == "function" then
        local ok, clear =
          pcall(PromotionRenderedCardClear, candidate, geometry.buttonW, geometry.buttonH, 160)
        rendered = ok and clear == true
        if not rendered then
          accepted = false
        end
      end
      if checked and accepted then
        if PromotionLayoutBetter(candidate, best) then
          best = candidate
        end
        local lowerBound = geometry.provenNonplanar and 1 or 0
        if
          best.crossings == lowerBound
          and best.width * best.height <= geometry.viewportW * geometry.viewportH + 0.01
          and (best.readability or PromotionRouteReadability(best)).backtrackingRoutes == 0
        then
          return best
        end
      elseif not checked then
        candidate = {
          buttons = {},
          routes = {},
          sourceRoutes = {},
          valid = false,
          violations = { builder.name .. " validation failed: " .. tostring(accepted) },
        }
      elseif not rendered then
        candidate.valid = false
        candidate.violations = candidate.violations or {}
        candidate.violations[#candidate.violations + 1] =
          "rendered_card_clear: candidate failed fixed-card/native clearance"
      end
      if
        not candidate.valid and (not failed or #(candidate.routes or {}) > #(failed.routes or {}))
      then
        failed = candidate
      end
    elseif not failed then
      failed = {
        buttons = {},
        routes = {},
        sourceRoutes = {},
        valid = false,
        violations = { builder.name .. " layout failed: " .. tostring(ok and reason or candidate) },
      }
    end
  end
  -- Try the expensive rank/degrees fallback only after ordinary builders fail.
  -- Its warm-start rows come from the best partial candidate, and its bounded
  -- reflow/rip-up still passes the same semantic, native and painted-card gates.
  if
    (not best or not best.valid)
    and type(PromotionDenseLayoutEligible) == "function"
    and type(PromotionDenseLayoutSolve) == "function"
  then
    local eligibleOk, eligible = pcall(PromotionDenseLayoutEligible, graph)
    if eligibleOk and eligible then
      local ok, candidate, reason =
        pcall(PromotionDenseLayoutSolve, graph, geometry, failed or best)
      if ok and candidate then
        candidate.method = "dense-degree-spill"
        local checked, accepted = pcall(PromotionCheckLayout, graph, candidate, geometry)
        if checked and not accepted then
          local repaired, variant = pcall(repairRouteClearance, graph, candidate, geometry)
          if repaired and variant then
            candidate = variant
            accepted = variant.valid
          end
        end
        local rendered = true
        if checked and accepted and type(PromotionRenderedCardClear) == "function" then
          local paintOk, clear =
            pcall(PromotionRenderedCardClear, candidate, geometry.buttonW, geometry.buttonH, 160)
          rendered = paintOk and clear == true
          if not rendered then
            accepted = false
          end
        end
        if checked and accepted and rendered then
          return candidate
        end
        if not checked then
          candidate = {
            buttons = {},
            routes = {},
            sourceRoutes = {},
            valid = false,
            violations = { "dense validation failed: " .. tostring(accepted) },
          }
        else
          candidate.valid = false
          candidate.violations = candidate.violations or {}
          if not rendered then
            candidate.violations[#candidate.violations + 1] =
              "rendered_card_clear: dense candidate failed fixed-card/native clearance"
          end
          if not ok then
            candidate.violations[#candidate.violations + 1] = "dense fallback failed: "
              .. tostring(reason)
          end
        end
        if not failed or #(candidate.routes or {}) > #(failed.routes or {}) then
          failed = candidate
        end
      end
    end
  end
  return best or failed
end
function PromotionLayoutCached(graph, geometry)
  local key = PromotionLayoutKey(graph, geometry)
  cacheAccessOrder = cacheAccessOrder + 1
  if cache[key] then
    cache[key].used = cacheAccessOrder
    cacheHitCount = cacheHitCount + 1
    return cache[key].layout, true
  end
  local solveGeometry = {}
  for k, v in pairs(geometry) do
    solveGeometry[k] = v
  end
  solveGeometry.defaultW = geometry.defaultW or geometry.viewportW
  solveGeometry.defaultH = geometry.defaultH or geometry.viewportH
  solveGeometry.provenNonplanar = PromotionNonplanarCertificate(graph) ~= nil
  -- A bounded readability allowance is a graph-wide policy, set before any
  -- candidate is seen. The chooser still minimizes crossings before area.
  local edges = 0
  for _, name in ipairs(graph.order) do
    edges = edges + #(graph.nodes[name].parents or {})
  end
  if solveGeometry.readabilityCrossingBudget == nil then
    solveGeometry.readabilityCrossingBudget = 2 * edges
  end
  solveGeometry.allowReadabilityCrossings = solveGeometry.readabilityCrossingBudget > 0
  local layout = PromotionLayoutChoose(graph, solveGeometry)
  if not layout then
    return nil, false
  end
  if layout.valid and layout.method ~= "reviewed" then
    layout = centerUnoccupiedPorts(graph, layout, solveGeometry)
  end
  layoutSolveCount = layoutSolveCount + 1
  local size, oldestKey, oldestAccessOrder = 0, nil, math.huge
  for k, entry in pairs(cache) do
    size = size + 1
    if entry.used < oldestAccessOrder then
      oldestKey, oldestAccessOrder = k, entry.used
    end
  end
  if size >= LAYOUT_CACHE_LIMIT then
    cache[oldestKey] = nil
  end
  cache[key] = { layout = layout, used = cacheAccessOrder }
  return layout, false
end
function PromotionLayoutCacheStats()
  return { hits = cacheHitCount, solves = layoutSolveCount }
end
function PromotionLayoutCacheClear()
  cache = {}
  cacheAccessOrder, cacheHitCount, layoutSolveCount = 0, 0, 0
end

-- The unit/class box is fixed to the left panel while the promotion geometry
-- is fitted inside the right viewport. Add its visual stem only after fitting
-- so no prerequisite, solver placement, or cache key depends on sidebar art.
function PromotionUnitSourceBridge(layout, originX, originY, boxRight, boxCentreY, boxHeight)
  if not layout or not layout.source or not layout.sourceRoutes or #layout.sourceRoutes == 0 then
    return nil
  end
  local scale = layout.scale or 1
  local sx, sy = layout.source.x, layout.source.y
  local bx = (boxRight - originX) / scale
  local by = (boxCentreY - originY) / scale
  if bx >= sx then
    return nil
  end
  local points = { { x = bx, y = by }, { x = sx, y = by } }
  if by ~= sy then
    points[#points + 1] = { x = sx, y = sy }
  end
  return { parent = "__PROMOTION_SOURCE__", child = "__PROMOTION_BOX__", points = points }
end
