-- Promotion tree geometry. This module deliberately has no Civ V dependencies.
-- Buttons are top-left rectangles. Routes are complete orthogonal centre lines;
-- the renderer may cut an underpass gap without changing their provenance.

local abs, max, min, floor = math.abs, math.max, math.min, math.floor
local function round(x)
  return floor(x + 0.5)
end
local function copy(t)
  local out = {}
  for i = 1, #t do
    out[i] = t[i]
  end
  return out
end
local function sortedKeys(t)
  local out = {}
  for k in pairs(t) do
    out[#out + 1] = k
  end
  table.sort(out)
  return out
end
local function edgeKey(a, b)
  return a .. "\001" .. b
end

local function graphData(graph)
  assert(type(graph) == "table" and type(graph.nodes) == "table", "promotion graph required")
  local names = graph.order and copy(graph.order) or sortedKeys(graph.nodes)
  table.sort(names)
  local seen, indegree, children, parents = {}, {}, {}, {}
  for i = 1, #names do
    local name = names[i]
    assert(type(name) == "string" and graph.nodes[name], "unknown promotion in graph order")
    assert(not seen[name], "duplicate promotion " .. name)
    seen[name], indegree[name], children[name], parents[name] = true, 0, {}, {}
  end
  local edges, edgeSeen = {}, {}
  for i = 1, #names do
    local child = names[i]
    local node = graph.nodes[child]
    local ps = node.parents or {}
    for j = 1, #ps do
      local parent = ps[j]
      assert(seen[parent], "dangling prerequisite " .. tostring(parent) .. " -> " .. child)
      local key = edgeKey(parent, child)
      assert(not edgeSeen[key], "duplicate prerequisite " .. parent .. " -> " .. child)
      edgeSeen[key] = true
      edges[#edges + 1] = { parent = parent, child = child, key = key }
      parents[child][#parents[child] + 1] = parent
      children[parent][#children[parent] + 1] = child
      indegree[child] = indegree[child] + 1
    end
  end
  table.sort(edges, function(a, b)
    return a.key < b.key
  end)
  for i = 1, #names do
    table.sort(parents[names[i]])
    table.sort(children[names[i]])
  end
  -- Kahn's traversal is both a cycle diagnostic and a stable longest-path rank.
  local queue, rank = {}, {}
  for i = 1, #names do
    if indegree[names[i]] == 0 then
      queue[#queue + 1] = names[i]
      rank[names[i]] = 0
    end
  end
  local head = 1
  while head <= #queue do
    local node = queue[head]
    head = head + 1
    for i = 1, #children[node] do
      local child = children[node][i]
      rank[child] = max(rank[child] or 0, rank[node] + 1)
      indegree[child] = indegree[child] - 1
      if indegree[child] == 0 then
        queue[#queue + 1] = child
      end
    end
  end
  assert(#queue == #names, "cyclic promotion prerequisites")
  return {
    names = names,
    edges = edges,
    parents = parents,
    children = children,
    rank = rank,
  }
end

local function expandLongEdges(data)
  local layers, segments, adjacent = {}, {}, {}
  local last = 0
  for i = 1, #data.names do
    local name = data.names[i]
    local r = data.rank[name]
    last = max(last, r)
    layers[r] = layers[r] or {}
    layers[r][#layers[r] + 1] = name
  end
  for i = 1, #data.edges do
    local edge = data.edges[i]
    local ra, rb = data.rank[edge.parent], data.rank[edge.child]
    local previous = edge.parent
    for r = ra + 1, rb do
      local nextNode = edge.child
      if r < rb then
        nextNode = "\002" .. i .. ":" .. r
        layers[r] = layers[r] or {}
        layers[r][#layers[r] + 1] = nextNode
      end
      segments[r - 1] = segments[r - 1] or {}
      segments[r - 1][#segments[r - 1] + 1] = { previous, nextNode }
      adjacent[previous] = adjacent[previous] or { prev = {}, next = {} }
      adjacent[nextNode] = adjacent[nextNode] or { prev = {}, next = {} }
      local a, b = adjacent[previous].next, adjacent[nextNode].prev
      a[#a + 1], b[#b + 1] = nextNode, previous
      previous = nextNode
    end
  end
  for r = 0, last do
    layers[r] = layers[r] or {}
    table.sort(layers[r])
  end
  return layers, segments, adjacent, last
end

local function orderScore(layers, segments, last)
  local positions, count = {}, 0
  for r = 0, last do
    for i = 1, #layers[r] do
      positions[layers[r][i]] = i
    end
  end
  for r = 0, last - 1 do
    local seg = segments[r] or {}
    for i = 1, #seg do
      local a, b = seg[i][1], seg[i][2]
      for j = i + 1, #seg do
        local c, d = seg[j][1], seg[j][2]
        if
          a ~= c
          and b ~= d
          and (positions[a] - positions[c]) * (positions[b] - positions[d]) < 0
        then
          count = count + 1
        end
      end
    end
  end
  return count
end

-- Swapping two nodes in rank r can change crossings only on the two
-- boundaries touching r. Re-score those boundaries instead of rebuilding the
-- complete expanded graph for every adjacent-swap attempt.
local function boundaryScore(layers, segments, r, last)
  if r < 0 or r >= last then
    return 0
  end
  local positions = {}
  for i = 1, #layers[r] do
    positions[layers[r][i]] = i
  end
  for i = 1, #layers[r + 1] do
    positions[layers[r + 1][i]] = i
  end
  local seg = segments[r] or {}
  local count = 0
  for i = 1, #seg do
    local a, b = seg[i][1], seg[i][2]
    for j = i + 1, #seg do
      local c, d = seg[j][1], seg[j][2]
      if
        a ~= c
        and b ~= d
        and (positions[a] - positions[c]) * (positions[b] - positions[d]) < 0
      then
        count = count + 1
      end
    end
  end
  return count
end

local function minimizeLayerCrossings(data, seed)
  local layers, segments, adjacent, last = expandLongEdges(data)
  for r = 0, last do
    if seed % 2 == 0 then
      table.sort(layers[r], function(a, b)
        return a > b
      end)
    end
  end
  local best, bestScore = nil, math.huge
  for sweep = 1, 6 do
    local forward = sweep % 2 == 1
    local from, to, step = forward and 1 or last - 1, forward and last or 0, forward and 1 or -1
    for r = from, to, step do
      local neighbour = r - step
      local pos, old = {}, {}
      for i = 1, #layers[neighbour] do
        pos[layers[neighbour][i]] = i
      end
      for i = 1, #layers[r] do
        old[layers[r][i]] = i
      end
      local scores = {}
      for i = 1, #layers[r] do
        local node = layers[r][i]
        local links = adjacent[node] and (forward and adjacent[node].prev or adjacent[node].next)
          or {}
        local vals = {}
        for j = 1, #links do
          vals[#vals + 1] = pos[links[j]]
        end
        table.sort(vals)
        if #vals == 0 then
          scores[node] = old[node]
        elseif seed < 2 then
          local sum = 0
          for j = 1, #vals do
            sum = sum + vals[j]
          end
          scores[node] = sum / #vals
        else
          scores[node] = (vals[floor((#vals + 1) / 2)] + vals[floor((#vals + 2) / 2)]) / 2
        end
      end
      table.sort(layers[r], function(a, b)
        if scores[a] ~= scores[b] then
          return scores[a] < scores[b]
        end
        if old[a] ~= old[b] then
          return old[a] < old[b]
        end
        return a < b
      end)
    end
    -- Each swap sees both incident boundaries. No swap is retained on a tie.
    for pass = 1, 2 do
      local changed = false
      for r = 0, last do
        local line = layers[r]
        for i = 1, #line - 1 do
          local before = boundaryScore(layers, segments, r - 1, last)
            + boundaryScore(layers, segments, r, last)
          line[i], line[i + 1] = line[i + 1], line[i]
          local after = boundaryScore(layers, segments, r - 1, last)
            + boundaryScore(layers, segments, r, last)
          if after < before then
            changed = true
          else
            line[i], line[i + 1] = line[i + 1], line[i]
          end
        end
      end
      if not changed then
        break
      end
    end
    local score = orderScore(layers, segments, last)
    if score < bestScore then
      bestScore, best = score, {}
      for r = 0, last do
        best[r] = copy(layers[r])
      end
    end
  end
  local real = {}
  for r = 0, last do
    real[r] = {}
    for i = 1, #best[r] do
      local name = best[r][i]
      if data.rank[name] ~= nil then
        real[r][#real[r] + 1] = name
      end
    end
  end
  return real, bestScore, last
end

local function fitPositions(wanted, separation, lower, upper)
  local count = #wanted
  if count == 0 then
    return {}
  end
  local out = {}
  for i = 1, count do
    out[i] = wanted[i]
  end
  for i = 2, count do
    out[i] = max(out[i], out[i - 1] + separation)
  end
  for i = count - 1, 1, -1 do
    out[i] = min(out[i], out[i + 1] - separation)
  end
  if out[1] < lower then
    local delta = lower - out[1]
    for i = 1, count do
      out[i] = out[i] + delta
    end
  end
  if out[count] > upper then
    local delta = out[count] - upper
    for i = 1, count do
      out[i] = out[i] - delta
    end
  end
  return out
end

local function placePromotionCards(data, layerOrder, last, width, height, routeOptions, chains)
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local pipe = routeOptions.pipeHalfWidth or 8
  local margin = max(28, (routeOptions.cornerHalfH or 21) + pipe + 5)
  local sourceReserve = 52
  local separation = cardHeight + max(12, 2 * pipe + 4)
  local rankCount = last + 1
  local minimumWidth = rankCount * cardWidth
    + (rankCount - 1) * (2 * (routeOptions.cornerHalfW or 16) + 2 * pipe + 4)
    + 2 * margin
    + sourceReserve
  local warnings = {}
  if minimumWidth > width then
    warnings[#warnings + 1] = "ranks require "
      .. round(minimumWidth)
      .. " px of logical width; available "
      .. round(width)
  end
  local widest = 0
  for r = 0, last do
    widest = max(widest, #layerOrder[r])
  end
  local minimumHeight = widest * cardHeight + (widest - 1) * max(12, 2 * pipe + 4) + 2 * margin
  if minimumHeight > height then
    warnings[#warnings + 1] = "densest rank requires "
      .. round(minimumHeight)
      .. " px of logical height; available "
      .. round(height)
  end
  local leftReserve = margin + sourceReserve
  local gap = rankCount > 1
      and (width - leftReserve - margin - rankCount * cardWidth) / (rankCount - 1)
    or 0
  gap = min(240, gap)
  local contentW = rankCount * cardWidth + (rankCount - 1) * gap
  local left = leftReserve + max(0, width - leftReserve - margin - contentW) / 2
  local xy = {}
  for r = 0, last do
    local line = layerOrder[r]
    local n = #line
    for i = 1, n do
      local y = (height - cardHeight) / 2
      if n > 1 then
        y = margin + (i - 1) * (height - 2 * margin - cardHeight) / (n - 1)
      end
      xy[line[i]] = { x = round(left + r * (cardWidth + gap)), y = round(y) }
    end
  end
  -- Relax sparse ranks toward their neighbours, preserving order and clearance.
  for pass = 1, 5 do
    local forward = pass % 2 == 1
    local from, to, step = forward and 0 or last, forward and last or 0, forward and 1 or -1
    for r = from, to, step do
      local line, wanted = layerOrder[r], {}
      for i = 1, #line do
        local node, sum, count = line[i], 0, 0
        local links = forward and data.parents[node] or data.children[node]
        for j = 1, #links do
          sum, count = sum + xy[links[j]].y, count + 1
        end
        if count == 0 then
          wanted[i] = xy[node].y
        else
          wanted[i] = 0.75 * sum / count + 0.25 * xy[node].y
        end
      end
      local fitted = fitPositions(wanted, separation, margin, height - margin - cardHeight)
      for i = 1, #line do
        xy[line[i]].y = round(fitted[i])
      end
    end
  end
  -- A validated family chain is a rigid horizontal row in this left-to-right
  -- candidate. The global group order prevents columns from disagreeing about
  -- which chain is above another. Constraint rows may be reused in columns
  -- that have no shared cards, so sparse trees do not waste vertical space.
  local groupOf, members = {}, {}
  for i = 1, #(chains or {}) do
    local chain = chains[i].nodes or chains[i]
    if #chain > 1 then
      local id = "chain:" .. i
      members[id] = {}
      for j = 1, #chain do
        local name = chain[j]
        assert(xy[name], "chain names unknown promotion " .. tostring(name))
        assert(not groupOf[name], "promotion belongs to two rank chains: " .. name)
        groupOf[name] = id
        members[id][#members[id] + 1] = name
        if j > 1 then
          assert(
            data.rank[chain[j - 1]] < data.rank[name],
            "rank chain is not in prerequisite order"
          )
        end
      end
    end
  end
  for i = 1, #data.names do
    local name = data.names[i]
    if not groupOf[name] then
      groupOf[name] = "single:" .. name
      members[groupOf[name]] = { name }
    end
  end
  local groups, desired = sortedKeys(members), {}
  for i = 1, #groups do
    local id, total = groups[i], 0
    for j = 1, #members[id] do
      total = total + xy[members[id][j]].y
    end
    desired[id] = total / #members[id]
  end
  table.sort(groups, function(a, b)
    if desired[a] ~= desired[b] then
      return desired[a] < desired[b]
    end
    return a < b
  end)
  local globalIndex = {}
  for i = 1, #groups do
    globalIndex[groups[i]] = i
  end
  local before, row = {}, {}
  for i = 1, #groups do
    before[groups[i]], row[groups[i]] = {}, 0
  end
  for r = 0, last do
    local line = copy(layerOrder[r])
    table.sort(line, function(a, b)
      local ia, ib = globalIndex[groupOf[a]], globalIndex[groupOf[b]]
      if ia ~= ib then
        return ia < ib
      end
      return a < b
    end)
    for i = 2, #line do
      local first, second = groupOf[line[i - 1]], groupOf[line[i]]
      if first ~= second then
        before[second][first] = true
      end
    end
  end
  -- If a future mandatory prerequisite pushes consecutive family ranks into
  -- nonadjacent columns, reserve their horizontal corridor from other cards.
  for i = 1, #groups do
    local chainGroup = groups[i]
    if chainGroup:sub(1, 6) == "chain:" then
      local lo, hi = math.huge, -math.huge
      for j = 1, #members[chainGroup] do
        local r = data.rank[members[chainGroup][j]]
        lo, hi = min(lo, r), max(hi, r)
      end
      for j = 1, #groups do
        local other = groups[j]
        if other ~= chainGroup then
          local intervenes = false
          for k = 1, #members[other] do
            local r = data.rank[members[other][k]]
            if r > lo and r < hi then
              intervenes = true
              break
            end
          end
          if intervenes then
            if globalIndex[other] < globalIndex[chainGroup] then
              before[chainGroup][other] = true
            else
              before[other][chainGroup] = true
            end
          end
        end
      end
    end
  end
  local lastRow = 0
  for i = 1, #groups do
    local id = groups[i]
    for prior in pairs(before[id]) do
      row[id] = max(row[id], row[prior] + 1)
    end
    lastRow = max(lastRow, row[id])
  end
  local available = height - 2 * margin - cardHeight
  local rowPitch = lastRow > 0 and available / lastRow or 0
  if lastRow > 0 and rowPitch < separation then
    warnings[#warnings + 1] = "rigid rank chains need "
      .. round(lastRow * separation + cardHeight + 2 * margin)
      .. " px of logical height"
  end
  for i = 1, #groups do
    local id = groups[i]
    local y = round(margin + (lastRow == 0 and available / 2 or row[id] * rowPitch))
    for j = 1, #members[id] do
      xy[members[id][j]].y = y
    end
  end
  local buttons = {}
  for i = 1, #data.names do
    local name = data.names[i]
    buttons[#buttons + 1] = { type = name, x = xy[name].x, y = xy[name].y }
  end
  return buttons, warnings
end

-- Geometric helpers for the separate routing and audit stage.
local function related(a, b)
  return a.parent == b.parent or a.child == b.child
end
local function sidePoint(button, side, cardWidth, cardHeight, preferred, inset)
  inset = inset or 0
  local function clamp(x, lo, hi)
    return max(lo, min(hi, x))
  end
  if side == "R" then
    return {
      x = button.x + cardWidth,
      y = clamp(
        preferred or button.y + cardHeight / 2,
        button.y + inset,
        button.y + cardHeight - inset
      ),
    },
      1,
      0
  end
  if side == "L" then
    return {
      x = button.x,
      y = clamp(
        preferred or button.y + cardHeight / 2,
        button.y + inset,
        button.y + cardHeight - inset
      ),
    },
      -1,
      0
  end
  if side == "B" then
    return {
      x = clamp(
        preferred or button.x + cardWidth / 2,
        button.x + inset,
        button.x + cardWidth - inset
      ),
      y = button.y + cardHeight,
    },
      0,
      1
  end
  return {
    x = clamp(
      preferred or button.x + cardWidth / 2,
      button.x + inset,
      button.x + cardWidth - inset
    ),
    y = button.y,
  },
    0,
    -1
end
local function rectangleHitsSegment(p, q, b, padX, padY, cardWidth, cardHeight)
  local left, right = b.x - padX, b.x + cardWidth + padX
  local top, bottom = b.y - padY, b.y + cardHeight + padY
  if p.y == q.y then
    return p.y > top and p.y < bottom and max(p.x, q.x) > left and min(p.x, q.x) < right
  end
  if p.x == q.x then
    return p.x > left and p.x < right and max(p.y, q.y) > top and min(p.y, q.y) < bottom
  end
  return true
end
local function segmentsOf(points)
  local out = {}
  local start = 0
  for i = 1, #points - 1 do
    if points[i].x ~= points[i + 1].x or points[i].y ~= points[i + 1].y then
      out[#out + 1] = { points[i], points[i + 1], start = start }
      start = start + abs(points[i].x - points[i + 1].x) + abs(points[i].y - points[i + 1].y)
    end
  end
  return out, start
end
local function positionAt(points, distance)
  local left = distance
  for i = 1, #points - 1 do
    local a, b = points[i], points[i + 1]
    local length = abs(a.x - b.x) + abs(a.y - b.y)
    if left <= length then
      if length == 0 then
        return { x = a.x, y = a.y }
      end
      return {
        x = a.x + (b.x - a.x) * left / length,
        y = a.y + (b.y - a.y) * left / length,
      }
    end
    left = left - length
  end
  return points[#points]
end
local function commonPrefix(a, b)
  if a[1].x ~= b[1].x or a[1].y ~= b[1].y then
    return 0
  end
  local cuts, distanceA, distanceB = { 0 }, 0, 0
  for i = 1, #a - 1 do
    distanceA = distanceA + abs(a[i].x - a[i + 1].x) + abs(a[i].y - a[i + 1].y)
    cuts[#cuts + 1] = distanceA
  end
  for i = 1, #b - 1 do
    distanceB = distanceB + abs(b[i].x - b[i + 1].x) + abs(b[i].y - b[i + 1].y)
    cuts[#cuts + 1] = distanceB
  end
  local limit = min(distanceA, distanceB)
  cuts[#cuts + 1] = limit
  table.sort(cuts)
  local good = 0
  for i = 1, #cuts do
    local d = cuts[i]
    if d > limit then
      break
    end
    local p, q = positionAt(a, d), positionAt(b, d)
    if abs(p.x - q.x) > 0.001 or abs(p.y - q.y) > 0.001 then
      break
    end
    good = d
  end
  return good
end
local function reversePoints(points)
  local out = {}
  for i = #points, 1, -1 do
    out[#out + 1] = points[i]
  end
  return out
end
local function onSharedRun(a, b, sa, sb, lo, hi, prefix, suffix, totalA, totalB)
  local function distance(segment, p)
    return segment.start + abs(p.x - segment[1].x) + abs(p.y - segment[1].y)
  end
  local a0, a1 = distance(sa, lo), distance(sa, hi)
  local b0, b1 = distance(sb, lo), distance(sb, hi)
  if a0 > a1 then
    a0, a1 = a1, a0
  end
  if b0 > b1 then
    b0, b1 = b1, b0
  end
  if
    a.parent == b.parent
    and a1 <= prefix
    and b1 <= prefix
    and abs(a0 - b0) < 0.001
    and abs(a1 - b1) < 0.001
  then
    return true
  end
  if
    a.child == b.child
    and totalA - a0 <= suffix
    and totalB - b0 <= suffix
    and abs((totalA - a0) - (totalB - b0)) < 0.001
    and abs((totalA - a1) - (totalB - b1)) < 0.001
  then
    return true
  end
  return false
end
local function routeInteractions(a, b)
  local as, totalA = segmentsOf(a.points)
  local bs, totalB = segmentsOf(b.points)
  local prefix = a.parent == b.parent and commonPrefix(a.points, b.points) or 0
  local suffix = a.child == b.child
      and commonPrefix(reversePoints(a.points), reversePoints(b.points))
    or 0
  local crossings, overlaps = 0, 0
  for i = 1, #as do
    local sa = as[i]
    local p, q = sa[1], sa[2]
    for j = 1, #bs do
      local sb = bs[j]
      local u, v = sb[1], sb[2]
      if p.y == q.y and u.y == v.y and p.y == u.y then
        local low = max(min(p.x, q.x), min(u.x, v.x))
        local high = min(max(p.x, q.x), max(u.x, v.x))
        if high >= low then
          if
            not onSharedRun(
              a,
              b,
              sa,
              sb,
              { x = low, y = p.y },
              { x = high, y = p.y },
              prefix,
              suffix,
              totalA,
              totalB
            )
          then
            overlaps = overlaps + 1
          end
        end
      elseif p.x == q.x and u.x == v.x and p.x == u.x then
        local low = max(min(p.y, q.y), min(u.y, v.y))
        local high = min(max(p.y, q.y), max(u.y, v.y))
        if high >= low then
          if
            not onSharedRun(
              a,
              b,
              sa,
              sb,
              { x = p.x, y = low },
              { x = p.x, y = high },
              prefix,
              suffix,
              totalA,
              totalB
            )
          then
            overlaps = overlaps + 1
          end
        end
      else
        local h1, h2, vert1, vert2
        if p.y == q.y then
          h1, h2, vert1, vert2 = p, q, u, v
        else
          h1, h2, vert1, vert2 = u, v, p, q
        end
        if
          min(h1.x, h2.x) <= vert1.x
          and vert1.x <= max(h1.x, h2.x)
          and min(vert1.y, vert2.y) <= h1.y
          and h1.y <= max(vert1.y, vert2.y)
        then
          local at = { x = vert1.x, y = h1.y }
          if
            at.x > min(h1.x, h2.x)
            and at.x < max(h1.x, h2.x)
            and at.y > min(vert1.y, vert2.y)
            and at.y < max(vert1.y, vert2.y)
          then
            crossings = crossings + 1
          elseif not onSharedRun(a, b, sa, sb, at, at, prefix, suffix, totalA, totalB) then
            overlaps = overlaps + 1 -- false junction
          end
        end
      end
    end
  end
  return crossings, overlaps
end

local function buildRoutingGrid(buttons, width, height, routeOptions)
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local half = routeOptions.pipeHalfWidth or 8
  local cx, cy = routeOptions.cornerHalfW or 16, routeOptions.cornerHalfH or 21
  -- The native renderer trims 21 logical pixels from every elbow arm.
  local stubX, stubY = max(24, cx + half + 3), max(24, cy + half + 3)
  local insetX, insetY = max(cx, half) + 2, max(cy, half) + 2
  local xs, ys =
    { [round(insetX)] = true, [round(width - insetX)] = true },
    { [round(insetY)] = true, [round(height - insetY)] = true }
  local function put(set, v, high)
    v = round(v)
    if v >= 0 and v <= high then
      set[v] = true
    end
  end
  for _, b in ipairs(buttons) do
    local x, y = b.x, b.y
    for _, v in ipairs({
      x,
      x + cardWidth,
      x + cardWidth / 2,
      x - cx - half - 3,
      x + cardWidth + cx + half + 3,
      x - stubX,
      x + cardWidth + stubX,
    }) do
      put(xs, v, width)
    end
    for _, v in ipairs({
      y,
      y + cardHeight,
      y + cardHeight / 2,
      y - cy - half - 3,
      y + cardHeight + cy + half + 3,
      y - stubY,
      y + cardHeight + stubY,
    }) do
      put(ys, v, height)
    end
  end
  if routeOptions.sourcePoint then
    put(xs, routeOptions.sourcePoint.x, width)
    put(ys, routeOptions.sourcePoint.y, height)
  end
  local function subdivide(set, high, pitch)
    local list = sortedKeys(set)
    for i = 1, #list - 1 do
      local distance = list[i + 1] - list[i]
      local count = math.ceil(distance / pitch)
      for j = 1, count - 1 do
        put(set, list[i] + distance * j / count, high)
      end
    end
  end
  subdivide(xs, width, routeOptions.gridPitch or 40)
  subdivide(ys, height, routeOptions.gridPitch or 40)
  local xlist, ylist = sortedKeys(xs), sortedKeys(ys)
  local xmap, ymap = {}, {}
  for i = 1, #xlist do
    xmap[xlist[i]] = i
  end
  for i = 1, #ylist do
    ymap[ylist[i]] = i
  end
  local nx, ny = #xlist, #ylist
  local function idx(ix, iy)
    return (iy - 1) * nx + ix
  end
  local free, turn, hfree, vfree = {}, {}, {}, {}
  for iy = 1, ny do
    for ix = 1, nx do
      local id, x, y = idx(ix, iy), xlist[ix], ylist[iy]
      free[id], turn[id] = true, true
      if x < half or x > width - half or y < half or y > height - half then
        free[id] = false
      end
      if x < cx or x > width - cx or y < cy or y > height - cy then
        turn[id] = false
      end
      for _, b in ipairs(buttons) do
        if
          x > b.x - half - 1
          and x < b.x + cardWidth + half + 1
          and y > b.y - half - 1
          and y < b.y + cardHeight + half + 1
        then
          free[id] = false
        end
        if
          x > b.x - cx
          and x < b.x + cardWidth + cx
          and y > b.y - cy
          and y < b.y + cardHeight + cy
        then
          turn[id] = false
        end
      end
      if ix < nx then
        local p, q = { x = x, y = y }, { x = xlist[ix + 1], y = y }
        hfree[id] = true
        for _, b in ipairs(buttons) do
          if rectangleHitsSegment(p, q, b, half + 1, half + 1, cardWidth, cardHeight) then
            hfree[id] = false
            break
          end
        end
      end
      if iy < ny then
        local p, q = { x = x, y = y }, { x = x, y = ylist[iy + 1] }
        vfree[id] = true
        for _, b in ipairs(buttons) do
          if rectangleHitsSegment(p, q, b, half + 1, half + 1, cardWidth, cardHeight) then
            vfree[id] = false
            break
          end
        end
      end
    end
  end
  return {
    xs = xlist,
    ys = ylist,
    xm = xmap,
    ym = ymap,
    nx = nx,
    ny = ny,
    index = idx,
    free = free,
    turn = turn,
    hfree = hfree,
    vfree = vfree,
    stubX = stubX,
    stubY = stubY,
  }
end

local function heapPush(heap, key, value)
  local keys, values = heap.keys, heap.values
  local i = heap.size + 1
  heap.size = i
  while i > 1 do
    local p = floor(i / 2)
    if keys[p] <= key then
      break
    end
    keys[i], values[i], i = keys[p], values[p], p
  end
  keys[i], values[i] = key, value
end
local function heapPop(heap)
  local keys, values = heap.keys, heap.values
  local resultKey, resultValue = keys[1], values[1]
  local tailKey, tailValue = keys[heap.size], values[heap.size]
  heap.size = heap.size - 1
  if heap.size > 0 then
    local i = 1
    while 2 * i <= heap.size do
      local c = 2 * i
      if c + 1 <= heap.size and keys[c + 1] < keys[c] then
        c = c + 1
      end
      if keys[c] >= tailKey then
        break
      end
      keys[i], values[i], i = keys[c], values[c], c
    end
    keys[i], values[i] = tailKey, tailValue
  end
  return resultKey, resultValue
end

local function occupancyPenalty(occupancy, id, edge, forbid)
  local list = occupancy[id]
  if not list then
    return 0
  end
  for i = 1, #list do
    if not related(list[i], edge) then
      if forbid then
        return math.huge
      else
        return 1
      end
    end
  end
  return 0
end

local SEARCH_MOVES = { { -1, 0, 2 }, { 1, 0, 1 }, { 0, -1, 4 }, { 0, 1, 3 } }

local function guideDistance(guide, x, y)
  if not guide then
    return 0
  end
  local points = guide.points or guide
  local best = math.huge
  for i = 1, #points - 1 do
    local a, b = points[i], points[i + 1]
    local dx, dy
    if a.y == b.y then
      dx = max(min(a.x, b.x) - x, x - max(a.x, b.x), 0)
      dy = abs(y - a.y)
    elseif a.x == b.x then
      dx = abs(x - a.x)
      dy = max(min(a.y, b.y) - y, y - max(a.y, b.y), 0)
    else
      dx, dy = abs(x - a.x), abs(y - a.y)
    end
    best = min(best, dx + dy)
  end
  return best == math.huge and 0 or best
end

local function findShortestRoute(grid, occupancy, edge, start, goal, options, guide)
  local startColumn, startRow = grid.xm[start.x], grid.ym[start.y]
  local goalColumn, goalRow = grid.xm[goal.x], grid.ym[goal.y]
  if not startColumn or not startRow or not goalColumn or not goalRow then
    return nil
  end
  local startNode, goalNode = grid.index(startColumn, startRow), grid.index(goalColumn, goalRow)
  if not grid.free[startNode] or not grid.free[goalNode] then
    return nil
  end
  -- Four signed directions matter: treating E and W as the same state permits
  -- an immediate reversal whose collapsed polyline becomes a tiny hairpin.
  local function encodeSearchState(node, direction)
    return (node - 1) * 4 + direction
  end
  local initialState = encodeSearchState(startNode, start.direction)
  local scratch = grid.searchScratch
  if not scratch then
    scratch = {
      distance = {},
      previous = {},
      stamp = {},
      generation = 0,
      heap = { keys = {}, values = {}, size = 0 },
    }
    grid.searchScratch = scratch
  end
  scratch.generation = scratch.generation + 1
  local generation = scratch.generation
  local distance, previous, stamp, heap =
    scratch.distance, scratch.previous, scratch.stamp, scratch.heap
  heap.size = 0
  distance[initialState], previous[initialState], stamp[initialState] = 0, nil, generation
  local function heuristic(column, row)
    return abs(grid.xs[column] - goal.x) + abs(grid.ys[row] - goal.y)
  end
  heapPush(heap, heuristic(startColumn, startRow), initialState)
  local goalState, bestCost = nil, math.huge
  local explored, limit = 0, options.maxSearchStates or 18000
  local minimumHorizontalLeg = options.minHorizontalLeg or 42
  local minimumVerticalLeg = options.minVerticalLeg or 42
  local horizontalEdgePenalties, verticalEdgePenalties, horizontalNodePenalties, verticalNodePenalties =
    {}, {}, {}, {}
  local function cachedPenalty(map, cache, id)
    local value = cache[id]
    if value == nil then
      value = occupancyPenalty(map, id, edge, false)
      cache[id] = value
    end
    return value
  end
  while heap.size > 0 and explored < limit do
    local itemKey, stateID = heapPop(heap)
    local node = floor((stateID - 1) / 4) + 1
    local direction = (stateID - 1) % 4 + 1
    local column = (node - 1) % grid.nx + 1
    local row = floor((node - 1) / grid.nx) + 1
    local pathCost = distance[stateID]
    if itemKey <= pathCost + heuristic(column, row) + 0.0001 then
      explored = explored + 1
      if node == goalNode then
        -- The last grid node may bend into the target port. A turn there is
        -- legal only when the full native elbow footprint clears every card.
        -- Keep searching other approaches instead of returning a clipped
        -- cheapest path that routePrerequisite must discard afterward.
        if direction == goal.direction or grid.turn[node] then
          local final = pathCost + (direction ~= goal.direction and 24 or 0)
          if final < bestCost then
            bestCost, goalState = final, stateID
          end
        end
        if heap.size == 0 or heap.keys[1] >= bestCost then
          break
        end
      else
        for moveIndex = 1, 4 do
          local dx, dy, nextDirection =
            SEARCH_MOVES[moveIndex][1], SEARCH_MOVES[moveIndex][2], SEARCH_MOVES[moveIndex][3]
          local reversal = (direction == 1 and nextDirection == 2)
            or (direction == 2 and nextDirection == 1)
            or (direction == 3 and nextDirection == 4)
            or (direction == 4 and nextDirection == 3)
          if not reversal and (nextDirection == direction or grid.turn[node]) then
            local runColumn, runRow = column, row
            local runLength, runCost = 0, 0
            while true do
              local nextColumn, nextRow = runColumn + dx, runRow + dy
              if nextColumn < 1 or nextColumn > grid.nx or nextRow < 1 or nextRow > grid.ny then
                break
              end
              local previousColumn, previousRow = runColumn, runRow
              runColumn, runRow = nextColumn, nextRow
              local nextNode = grid.index(runColumn, runRow)
              local horizontal = nextDirection == 1 or nextDirection == 2
              local edgeId = horizontal and grid.index(min(previousColumn, runColumn), previousRow)
                or grid.index(previousColumn, min(previousRow, runRow))
              local traversable = horizontal and grid.hfree[edgeId] or grid.vfree[edgeId]
              local edgeOcc = horizontal and occupancy.hEdge or occupancy.vEdge
              local opposite = horizontal and occupancy.vNode or occupancy.hNode
              local overlap = cachedPenalty(
                edgeOcc,
                horizontal and horizontalEdgePenalties or verticalEdgePenalties,
                edgeId
              )
              if not traversable or not grid.free[nextNode] or overlap > 0 then
                break
              end
              runLength = runLength
                + (
                  horizontal and abs(grid.xs[runColumn] - grid.xs[previousColumn])
                  or abs(grid.ys[runRow] - grid.ys[previousRow])
                )
              do
                local cross = cachedPenalty(
                  opposite,
                  horizontal and verticalNodePenalties or horizontalNodePenalties,
                  nextNode
                )
                runCost = runCost + cross * (options.crossingPenalty or 20000)
                runCost = runCost + overlap * (options.overlapPenalty or 4000)
                if guide then
                  local stepLength = horizontal
                      and abs(grid.xs[runColumn] - grid.xs[previousColumn])
                    or abs(grid.ys[runRow] - grid.ys[previousRow])
                  runCost = runCost
                    + (options.guideWeight or 0.5)
                      * guideDistance(guide, grid.xs[runColumn], grid.ys[runRow])
                      * stepLength
                      / (options.gridPitch or 40)
                end
                if
                  (goalColumn >= startColumn and dx < 0) or (goalColumn < startColumn and dx > 0)
                then
                  runCost = runCost
                    + (horizontal and abs(grid.xs[runColumn] - grid.xs[previousColumn]) or 0)
                      * 0.5
                end
              end
              local isGoal = nextNode == goalNode
              local minimum = (nextDirection == 1 or nextDirection == 2) and minimumHorizontalLeg
                or minimumVerticalLeg
              local canStop = (runLength >= minimum or (isGoal and nextDirection == goal.direction))
                and (isGoal or grid.turn[nextNode])
              if canStop then
                local candidate = pathCost
                  + runLength
                  + runCost
                  + (nextDirection ~= direction and 24 or 0)
                local nextStateID = encodeSearchState(nextNode, nextDirection)
                if
                  candidate
                  < (stamp[nextStateID] == generation and distance[nextStateID] or math.huge)
                then
                  distance[nextStateID], previous[nextStateID], stamp[nextStateID] =
                    candidate, stateID, generation
                  heapPush(heap, candidate + heuristic(runColumn, runRow), nextStateID)
                end
              end
            end
          end
        end
      end
    end
  end
  if not goalState then
    return nil, explored
  end
  local reverse = {}
  local stateID = goalState
  while stateID do
    local node = floor((stateID - 1) / 4) + 1
    local column = (node - 1) % grid.nx + 1
    local row = floor((node - 1) / grid.nx) + 1
    reverse[#reverse + 1] = { x = grid.xs[column], y = grid.ys[row] }
    stateID = previous[stateID]
  end
  local points = {}
  for i = #reverse, 1, -1 do
    points[#points + 1] = reverse[i]
  end
  return points, explored
end

local function simplify(points)
  local out = {}
  for i = 1, #points do
    local p = points[i]
    if #out == 0 or p.x ~= out[#out].x or p.y ~= out[#out].y then
      while #out >= 2 do
        local a, b = out[#out - 1], out[#out]
        if
          (a.x == b.x and b.x == p.x and (b.y - a.y) * (p.y - b.y) > 0)
          or (a.y == b.y and b.y == p.y and (b.x - a.x) * (p.x - b.x) > 0)
        then
          out[#out] = nil
        else
          break
        end
      end
      out[#out + 1] = p
    end
  end
  return out
end
local function segmentGap(a, b, c, d)
  local dx = max(min(a.x, b.x) - max(c.x, d.x), min(c.x, d.x) - max(a.x, b.x), 0)
  local dy = max(min(a.y, b.y) - max(c.y, d.y), min(c.y, d.y) - max(a.y, b.y), 0)
  return math.sqrt(dx * dx + dy * dy)
end
local function routeSelfClear(points, routeOptions)
  local half = routeOptions.pipeHalfWidth or 8
  for i = 1, #points - 1 do
    local a, b = points[i], points[i + 1]
    local length = abs(a.x - b.x) + abs(a.y - b.y)
    local horizontal = a.y == b.y
    local endpointLeg = i == 1 or i == #points - 1
    local minimum = endpointLeg and 21 or 42
    if #points > 2 and length < minimum then
      return false, "short bend leg"
    end
    if i > 1 then
      local previous = points[i - 1]
      if
        (previous.x == a.x and a.x == b.x and (a.y - previous.y) * (b.y - a.y) < 0)
        or (previous.y == a.y and a.y == b.y and (a.x - previous.x) * (b.x - a.x) < 0)
      then
        return false, "pipe backtrack"
      end
    end
    for j = i + 2, #points - 1 do
      if segmentGap(a, b, points[j], points[j + 1]) <= 2 * half then
        return false, "pipe self-contact"
      end
    end
  end
  return true
end

-- The shortest-path grid checks turns in its interior, but a port stub can
-- turn at its first grid node. Check the complete simplified path before
-- accepting it so the native elbow artwork cannot clip a nearby card.
local function routeBendsClear(points, buttons, routeOptions)
  local cornerX, cornerY = routeOptions.cornerHalfW or 16, routeOptions.cornerHalfH or 21
  local width = routeOptions.width or routeOptions.defaultW or routeOptions.viewportW or 1638
  local height = routeOptions.height or routeOptions.defaultH or routeOptions.viewportH or 1040
  for i = 2, #points - 1 do
    local prev, bend, nextPoint = points[i - 1], points[i], points[i + 1]
    if (prev.x == bend.x) ~= (bend.x == nextPoint.x) then
      if
        bend.x < cornerX
        or bend.x > width - cornerX
        or bend.y < cornerY
        or bend.y > height - cornerY
      then
        return false
      end
      for j = 1, #buttons do
        local card = buttons[j]
        if
          bend.x + cornerX >= card.x
          and bend.x - cornerX <= card.x + routeOptions.buttonW
          and bend.y + cornerY >= card.y
          and bend.y - cornerY <= card.y + routeOptions.buttonH
        then
          return false
        end
      end
    end
  end
  return true
end

local function rootSourcePaths(graph, buttonOf, routeOptions, width, height)
  if routeOptions.includeSource == false then
    return nil, {}
  end
  local roots = {}
  local rootSet = {}
  for i = 1, #(graph.roots or {}) do
    rootSet[graph.roots[i]] = true
  end
  for name, button in pairs(buttonOf) do
    if rootSet[name] or (not graph.roots and #(graph.nodes[name].parents or {}) == 0) then
      roots[#roots + 1] = {
        name = name,
        button = button,
        cy = round(button.y + routeOptions.buttonH / 2),
      }
    end
  end
  table.sort(roots, function(a, b)
    if a.cy ~= b.cy then
      return a.cy < b.cy
    end
    return a.name < b.name
  end)
  if #roots == 0 then
    return nil, {}
  end
  local cx = routeOptions.cornerHalfW or 16
  local pipe = routeOptions.pipeHalfWidth or 8
  local source = routeOptions.sourcePoint
    or { x = max(24, cx + pipe + 2), y = roots[floor((#roots + 1) / 2)].cy }
  local routes = {}
  for i = 1, #roots do
    local root = roots[i]
    local points = { { x = source.x, y = source.y } }
    if root.cy ~= source.y then
      points[#points + 1] = { x = source.x, y = root.cy }
    end
    points[#points + 1] = { x = root.button.x, y = root.cy }
    routes[#routes + 1] = { parent = "__PROMOTION_SOURCE__", child = root.name, points = points }
  end
  return source, routes
end

local function addOccupancy(occ, grid, route)
  local points = route.points
  local function add(t, id)
    t[id] = t[id] or {}
    t[id][#t[id] + 1] = route
  end
  for i = 1, #points - 1 do
    local a, b = points[i], points[i + 1]
    if a.y == b.y then
      local iy = grid.ym[a.y]
      local x1, x2 = grid.xm[min(a.x, b.x)], grid.xm[max(a.x, b.x)]
      if iy and x1 and x2 then
        for ix = x1, x2 - 1 do
          add(occ.hEdge, grid.index(ix, iy))
        end
        for ix = x1, x2 do
          add(occ.hNode, grid.index(ix, iy))
        end
      end
    elseif a.x == b.x then
      local ix = grid.xm[a.x]
      local y1, y2 = grid.ym[min(a.y, b.y)], grid.ym[max(a.y, b.y)]
      if ix and y1 and y2 then
        for iy = y1, y2 - 1 do
          add(occ.vEdge, grid.index(ix, iy))
        end
        for iy = y1, y2 do
          add(occ.vNode, grid.index(ix, iy))
        end
      end
    end
  end
end

local function candidatePairs(a, b, cardWidth, cardHeight, maxPairs)
  local acx, acy = a.x + cardWidth / 2, a.y + cardHeight / 2
  local bcx, bcy = b.x + cardWidth / 2, b.y + cardHeight / 2
  local pairs = {}
  for _, source in ipairs({ "R", "B", "T", "L" }) do
    for _, target in ipairs({ "L", "T", "B", "R" }) do
      local pa = sidePoint(a, source, cardWidth, cardHeight)
      local pb = sidePoint(b, target, cardWidth, cardHeight)
      local score = abs(pa.x - pb.x) + abs(pa.y - pb.y)
      if source == "R" and target == "L" and bcx > acx then
        score = score - 90
      end
      if source == "B" and target == "T" and bcy > acy then
        score = score - 75
      end
      if source == "T" and target == "B" and bcy < acy then
        score = score - 75
      end
      if source == "L" and target == "R" and bcx < acx then
        score = score - 75
      end
      pairs[#pairs + 1] = { source, target, score }
    end
  end
  table.sort(pairs, function(p, q)
    if p[3] ~= q[3] then
      return p[3] < q[3]
    end
    return p[1] .. p[2] < q[1] .. q[2]
  end)
  local out = {}
  for i = 1, min(#pairs, maxPairs or 5) do
    out[i] = pairs[i]
  end
  return out
end

local function routePrerequisite(edge, buttonOf, buttons, grid, occupancy, accepted, routeOptions)
  local a, b = buttonOf[edge.parent], buttonOf[edge.child]
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local best, bestKey, explored = nil, nil, 0
  local fallback, fallbackKey
  local guide = routeOptions.guideMap and routeOptions.guideMap[edge.key]
  local portPairs = candidatePairs(a, b, cardWidth, cardHeight, routeOptions.maxPortPairs)
  local function sharedJunctionsClear(route)
    for _, prior in ipairs(accepted) do
      if route.parent == prior.parent and #route.points > 2 and #prior.points > 2 then
        local u, v = route.points[2], prior.points[2]
        if
          (u.x == v.x or u.y == v.y)
          and abs(u.x - v.x) + abs(u.y - v.y) > 0
          and abs(u.x - v.x) + abs(u.y - v.y) < 42
        then
          return false
        end
      end
      if route.child == prior.child and #route.points > 2 and #prior.points > 2 then
        local u, v = route.points[#route.points - 1], prior.points[#prior.points - 1]
        if
          (u.x == v.x or u.y == v.y)
          and abs(u.x - v.x) + abs(u.y - v.y) > 0
          and abs(u.x - v.x) + abs(u.y - v.y) < 42
        then
          return false
        end
      end
    end
    return true
  end
  local function crossingsRenderable(route)
    local clearance = (routeOptions.underpassHalfGap or 10) + 21
    local function axisClearance(horizontal, x, y)
      local nearest = math.huge
      local function inspect(other)
        for k = 1, #other.points - 1 do
          local u, v = other.points[k], other.points[k + 1]
          if
            (horizontal and u.y == v.y and u.y == y)
            or (not horizontal and u.x == v.x and u.x == x)
          then
            nearest = min(
              nearest,
              horizontal and min(abs(x - u.x), abs(x - v.x)) or min(abs(y - u.y), abs(y - v.y))
            )
          end
        end
      end
      inspect(route)
      for _, other in ipairs(accepted) do
        inspect(other)
      end
      return nearest
    end
    for _, prior in ipairs(accepted) do
      for k = 1, #route.points - 1 do
        local p, q = route.points[k], route.points[k + 1]
        for j = 1, #prior.points - 1 do
          local u, v = prior.points[j], prior.points[j + 1]
          local h1, h2, v1, v2
          if p.y == q.y and u.x == v.x then
            h1, h2, v1, v2 = p, q, u, v
          elseif p.x == q.x and u.y == v.y then
            h1, h2, v1, v2 = u, v, p, q
          end
          if
            h1
            and v1.x > min(h1.x, h2.x)
            and v1.x < max(h1.x, h2.x)
            and h1.y > min(v1.y, v2.y)
            and h1.y < max(v1.y, v2.y)
          then
            local x, y = v1.x, h1.y
            if max(axisClearance(true, x, y), axisClearance(false, x, y)) < clearance then
              return false
            end
          end
        end
      end
    end
    return true
  end
  local function artworkClear(route)
    if routeOptions.provenNonplanar then
      return true
    end
    local pipe = routeOptions.pipeHalfWidth or 8
    local reachX = (routeOptions.cornerHalfW or 16) + pipe
    local reachY = (routeOptions.cornerHalfH or 21) + pipe
    local function bentPoint(points, i)
      local a, p, b = points[i - 1], points[i], points[i + 1]
      return (a.x == p.x) ~= (p.x == b.x)
    end
    local function strokeHitsBox(a, b, p)
      if a.y == b.y then
        return a.y >= p.y - reachY
          and a.y <= p.y + reachY
          and max(min(a.x, b.x), p.x - reachX) <= min(max(a.x, b.x), p.x + reachX)
      end
      return a.x >= p.x - reachX
        and a.x <= p.x + reachX
        and max(min(a.y, b.y), p.y - reachY) <= min(max(a.y, b.y), p.y + reachY)
    end
    for _, prior in ipairs(accepted) do
      if not related(route, prior) then
        for i = 1, #route.points - 1 do
          local a, b = route.points[i], route.points[i + 1]
          for j = 1, #prior.points - 1 do
            local c, d = prior.points[j], prior.points[j + 1]
            local ax0, ax1 = min(a.x, b.x), max(a.x, b.x)
            local ay0, ay1 = min(a.y, b.y), max(a.y, b.y)
            local bx0, bx1 = min(c.x, d.x), max(c.x, d.x)
            local by0, by1 = min(c.y, d.y), max(c.y, d.y)
            local dx = max(ax0 - bx1, bx0 - ax1, 0)
            local dy = max(ay0 - by1, by0 - ay1, 0)
            if dx * dx + dy * dy <= 4 * pipe * pipe then
              local crossing = false
              if a.y == b.y and c.x == d.x then
                crossing = c.x > ax0 and c.x < ax1 and a.y > by0 and a.y < by1
              elseif a.x == b.x and c.y == d.y then
                crossing = a.x > bx0 and a.x < bx1 and c.y > ay0 and c.y < ay1
              end
              if not crossing then
                return false
              end
            end
          end
        end
        for i = 2, #route.points - 1 do
          if bentPoint(route.points, i) then
            for j = 1, #prior.points - 1 do
              if strokeHitsBox(prior.points[j], prior.points[j + 1], route.points[i]) then
                return false
              end
            end
          end
        end
        for i = 2, #prior.points - 1 do
          if bentPoint(prior.points, i) then
            for j = 1, #route.points - 1 do
              if strokeHitsBox(route.points[j], route.points[j + 1], prior.points[i]) then
                return false
              end
            end
          end
        end
      end
    end
    return true
  end
  -- Most promotion edges need only a straight run or one ordinary dogleg.
  -- Try those bounded constructions before searching the entire routing grid.
  -- The same collision checks used for searched paths still apply.
  local function directCandidate(raw, permitCrossings)
    local route = { parent = edge.parent, child = edge.child, points = simplify(raw) }
    if
      not artworkClear(route)
      or not sharedJunctionsClear(route)
      or not routeSelfClear(route.points, routeOptions)
      or not routeBendsClear(route.points, buttons, routeOptions)
    then
      return nil
    end
    for k = 1, #route.points - 1 do
      local u, v = route.points[k], route.points[k + 1]
      if u.x ~= v.x and u.y ~= v.y then
        return nil
      end
      for _, card in ipairs(buttons) do
        if
          not (card.type == edge.parent and k == 1)
          and not (card.type == edge.child and k == #route.points - 1)
          and rectangleHitsSegment(
            u,
            v,
            card,
            routeOptions.pipeHalfWidth or 8,
            routeOptions.pipeHalfWidth or 8,
            cardWidth,
            cardHeight
          )
        then
          return nil
        end
      end
    end
    local totalCrossings = 0
    for _, prior in ipairs(accepted) do
      local crossings, overlaps = routeInteractions(route, prior)
      if overlaps > 0 or (crossings > 0 and not permitCrossings) then
        return nil
      end
      totalCrossings = totalCrossings + crossings
    end
    if totalCrossings > 0 and not crossingsRenderable(route) then
      return nil
    end
    return route, totalCrossings
  end
  local function consider(raw)
    local route = directCandidate(raw, false)
    if route then
      return route
    end
    if routeOptions.allowReadabilityCrossings then
      local crossed, count = directCandidate(raw, true)
      if crossed and count > 0 then
        local length = 0
        for k = 1, #crossed.points - 1 do
          length = length
            + abs(crossed.points[k].x - crossed.points[k + 1].x)
            + abs(crossed.points[k].y - crossed.points[k + 1].y)
        end
        local score = count * 100000 + length + 24 * (#crossed.points - 2)
        if not fallbackKey or score < fallbackKey then
          fallback, fallbackKey = crossed, score
        end
      end
    end
  end
  for i = 1, #portPairs do
    local sside, tside = portPairs[i][1], portPairs[i][2]
    local inset = min(cardWidth, cardHeight) / 2 - 1
    inset = min(inset, max(5, (routeOptions.pipeHalfWidth or 8) + 3))
    local sharedSource = (routeOptions.outdegree[edge.parent] or 0) > 1
    local sourcePreferred = (sside == "R" or sside == "L")
        and (sharedSource and a.y + cardHeight / 2 or b.y + cardHeight / 2)
      or (sharedSource and a.x + cardWidth / 2 or b.x + cardWidth / 2)
    local p, sdx, sdy = sidePoint(a, sside, cardWidth, cardHeight, sourcePreferred, inset)
    local sharedTarget = (routeOptions.indegree[edge.child] or 0) > 1
    local targetPreferred = (tside == "R" or tside == "L")
        and (sharedTarget and b.y + cardHeight / 2 or p.y)
      or (sharedTarget and b.x + cardWidth / 2 or p.x)
    local q, tdx, tdy = sidePoint(b, tside, cardWidth, cardHeight, targetPreferred, inset)
    if (sside == "R" or sside == "L") and (tside == "R" or tside == "L") then
      if not sharedSource then
        p, sdx, sdy = sidePoint(a, sside, cardWidth, cardHeight, q.y, inset)
      end
      if not sharedTarget then
        q, tdx, tdy = sidePoint(b, tside, cardWidth, cardHeight, p.y, inset)
      end
    elseif (sside == "T" or sside == "B") and (tside == "T" or tside == "B") then
      if not sharedSource then
        p, sdx, sdy = sidePoint(a, sside, cardWidth, cardHeight, q.x, inset)
      end
      if not sharedTarget then
        q, tdx, tdy = sidePoint(b, tside, cardWidth, cardHeight, p.x, inset)
      end
    end
    local function nearest(list, value, lo, hi)
      local best, distance = nil, math.huge
      for j = 1, #list do
        local v = list[j]
        if v >= lo and v <= hi and abs(v - value) < distance then
          best, distance = v, abs(v - value)
        end
      end
      return best
    end
    local sourceHorizontal = sdx ~= 0
    local targetHorizontal = tdx ~= 0
    if sourceHorizontal and targetHorizontal and not sharedSource and not sharedTarget then
      local common = nearest(
        grid.ys,
        (p.y + q.y) / 2,
        max(a.y, b.y) + inset,
        min(a.y + cardHeight, b.y + cardHeight) - inset
      )
      if common then
        p.y, q.y = common, common
      end
    elseif
      not sourceHorizontal
      and not targetHorizontal
      and not sharedSource
      and not sharedTarget
    then
      local common = nearest(
        grid.xs,
        (p.x + q.x) / 2,
        max(a.x, b.x) + inset,
        min(a.x + cardWidth, b.x + cardWidth) - inset
      )
      if common then
        p.x, q.x = common, common
      end
    end
    if sourceHorizontal then
      p.y = nearest(grid.ys, p.y, a.y + inset, a.y + cardHeight - inset)
        or round(a.y + cardHeight / 2)
    else
      p.x = nearest(grid.xs, p.x, a.x + inset, a.x + cardWidth - inset)
        or round(a.x + cardWidth / 2)
    end
    if targetHorizontal then
      q.y = nearest(grid.ys, q.y, b.y + inset, b.y + cardHeight - inset)
        or round(b.y + cardHeight / 2)
    else
      q.x = nearest(grid.xs, q.x, b.x + inset, b.x + cardWidth - inset)
        or round(b.x + cardWidth / 2)
    end
    local start = {
      x = round(p.x + sdx * grid.stubX),
      y = round(p.y + sdy * grid.stubY),
      direction = sdx > 0 and 1 or sdx < 0 and 2 or sdy > 0 and 3 or 4,
    }
    local goal = {
      x = round(q.x + tdx * grid.stubX),
      y = round(q.y + tdy * grid.stubY),
      direction = tdx < 0 and 1 or tdx > 0 and 2 or tdy < 0 and 3 or 4,
    }
    p, q = { x = round(p.x), y = round(p.y) }, { x = round(q.x), y = round(q.y) }
    local stubsClear = true
    for _, other in ipairs(buttons) do
      if
        other.type ~= edge.parent
        and rectangleHitsSegment(
          p,
          start,
          other,
          routeOptions.pipeHalfWidth or 8,
          routeOptions.pipeHalfWidth or 8,
          cardWidth,
          cardHeight
        )
      then
        stubsClear = false
      end
      if
        other.type ~= edge.child
        and rectangleHitsSegment(
          goal,
          q,
          other,
          routeOptions.pipeHalfWidth or 8,
          routeOptions.pipeHalfWidth or 8,
          cardWidth,
          cardHeight
        )
      then
        stubsClear = false
      end
    end
    if stubsClear then
      local simple
      if sdx ~= 0 and tdx ~= 0 and sdx > 0 and tdx < 0 and p.x < q.x then
        if p.y == q.y then
          simple = consider({ p, q })
        end
        if not simple then
          local middle = (p.x + q.x) / 2
          local tracks = {
            round(middle),
            round(p.x + max(42, grid.stubX)),
            round(q.x - max(42, grid.stubX)),
          }
          for _, x in ipairs(tracks) do
            if x > p.x + 21 and x < q.x - 21 then
              simple = consider({ p, { x = x, y = p.y }, { x = x, y = q.y }, q })
              if simple then
                break
              end
            end
          end
        end
      elseif sdy ~= 0 and tdy ~= 0 and p.x == q.x then
        simple = consider({ p, q })
      elseif sdx ~= 0 and tdy ~= 0 then
        simple = consider({ p, { x = q.x, y = p.y }, q })
      elseif sdy ~= 0 and tdx ~= 0 then
        simple = consider({ p, { x = p.x, y = q.y }, q })
      end
      if simple then
        return simple, explored
      end
      local middle, visited =
        findShortestRoute(grid, occupancy, edge, start, goal, routeOptions, guide)
      explored = explored + (visited or 0)
      if middle then
        local points = { p }
        for j = 1, #middle do
          points[#points + 1] = middle[j]
        end
        points[#points + 1] = q
        local route = { parent = edge.parent, child = edge.child, points = simplify(points) }
        local selfClear = routeSelfClear(route.points, routeOptions)
        if
          selfClear
          and artworkClear(route)
          and sharedJunctionsClear(route)
          and routeBendsClear(route.points, buttons, routeOptions)
        then
          local crosses, overlaps, incidentOverlap = 0, 0, false
          for j = 1, #accepted do
            local c, o = routeInteractions(route, accepted[j])
            crosses, overlaps = crosses + c, overlaps + o
            if
              o > 0
              and (route.parent == accepted[j].child or route.child == accepted[j].parent)
            then
              incidentOverlap = true
            end
          end
          if
            not incidentOverlap
            and overlaps == 0
            and (crosses == 0 or crossingsRenderable(route))
          then
            local length = 0
            for j = 1, #route.points - 1 do
              local u, v = route.points[j], route.points[j + 1]
              length = length + abs(u.x - v.x) + abs(u.y - v.y)
            end
            local deviation = 0
            if guide then
              for j = 1, #route.points do
                deviation = deviation + guideDistance(guide, route.points[j].x, route.points[j].y)
              end
            end
            local key = overlaps * 10000000
              + crosses * 1000000
              + deviation * (routeOptions.guideCandidateWeight or 4)
              + length
              + 24 * (#route.points - 2)
              + i
            if not bestKey or key < bestKey then
              best, bestKey = route, key
            end
            if crosses == 0 and i >= 2 then
              break
            end
          end
        end
      end
    end
  end
  return best or fallback, explored
end

local function layoutScoreLessThan(a, b)
  if not b then
    return true
  end
  local aMissing = a.stats.edges - a.stats.routed
  local bMissing = b.stats.edges - b.stats.routed
  if aMissing ~= bMissing then
    return aMissing < bMissing
  end
  if #a.violations ~= #b.violations then
    return #a.violations < #b.violations
  end
  if a.crossings ~= b.crossings then
    return a.crossings < b.crossings
  end
  if a.scale ~= b.scale then
    return a.scale > b.scale
  end
  return (a.stats.length or math.huge) < (b.stats.length or math.huge)
end

-- Route caller-supplied positions; also used by independent planar placement.
function PromotionLayoutRoute(graph, buttons, geometry)
  local routeOptions = {}
  for k, v in pairs(geometry or {}) do
    routeOptions[k] = v
  end
  assert(routeOptions.buttonW and routeOptions.buttonH, "buttonW and buttonH required")
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local data = graphData(graph)
  local width = routeOptions.width or routeOptions.defaultW or routeOptions.viewportW or 1638
  local height = routeOptions.height or routeOptions.defaultH or routeOptions.viewportH or 1040
  local buttonOf, orderedButtons = {}, {}
  for i = 1, #buttons do
    local b = buttons[i]
    assert(
      data.rank[b.type] ~= nil and not buttonOf[b.type],
      "unknown or duplicate promotion button " .. tostring(b.type)
    )
    buttonOf[b.type] = { type = b.type, x = round(b.x), y = round(b.y) }
  end
  for i = 1, #data.names do
    local name = data.names[i]
    assert(buttonOf[name], "missing promotion button " .. name)
    orderedButtons[i] = buttonOf[name]
  end
  local source, sourceRoutes
  if routeOptions.sourceRoutes then
    source, sourceRoutes = routeOptions.sourcePoint, copy(routeOptions.sourceRoutes)
  else
    source, sourceRoutes = rootSourcePaths(graph, buttonOf, routeOptions, width, height)
  end
  routeOptions.sourcePoint = source
  if routeOptions.maxPortPairs == nil then
    routeOptions.maxPortPairs = routeOptions.provenNonplanar and 4 or (#data.edges > 25 and 3 or 4)
  end
  if routeOptions.maxSearchStates == nil then
    routeOptions.maxSearchStates = routeOptions.provenNonplanar and 1200 or 800
  end
  if routeOptions.crossingPenalty == nil then
    routeOptions.crossingPenalty = routeOptions.provenNonplanar and 250 or 20000
  end
  if routeOptions.shortFirst == nil then
    routeOptions.shortFirst = true
  end
  routeOptions.indegree, routeOptions.outdegree = {}, {}
  for i = 1, #data.names do
    local name = data.names[i]
    routeOptions.indegree[name] = #data.parents[name]
    routeOptions.outdegree[name] = #data.children[name]
  end
  if routeOptions.guideRoutes then
    routeOptions.guideMap = {}
    if routeOptions.guideRoutes[1] then
      for i = 1, #routeOptions.guideRoutes do
        local guide = routeOptions.guideRoutes[i]
        routeOptions.guideMap[edgeKey(guide.parent, guide.child)] = guide
      end
    else
      for key, guide in pairs(routeOptions.guideRoutes) do
        routeOptions.guideMap[key] = guide
      end
    end
  end
  local grid = buildRoutingGrid(orderedButtons, width, height, routeOptions)
  local edgeOf = {}
  for i = 1, #data.edges do
    edgeOf[data.edges[i].key] = data.edges[i]
  end
  local seeds, seeded = {}, {}
  for i = 1, #(routeOptions.seededRoutes or {}) do
    local route = routeOptions.seededRoutes[i]
    local key = edgeKey(route.parent, route.child)
    assert(edgeOf[key] and not seeded[key], "seed route is not a unique prerequisite")
    seeded[key] = true
    seeds[#seeds + 1] = route
  end
  -- Long edges from a root into a multi-parent merge are easily fenced out by
  -- later fan trunks. Give the most constrained of these edges first access to
  -- the canvas, then let the ordinary router use its occupied corridors.
  if routeOptions.rootMergeFirst ~= false then
    local rootSet = {}
    for _, root in ipairs(graph.roots or {}) do
      rootSet[root] = true
    end
    local early = {}
    for _, edge in ipairs(data.edges) do
      if rootSet[edge.parent] and #data.parents[edge.child] >= 2 and not seeded[edge.key] then
        local a, b = buttonOf[edge.parent], buttonOf[edge.child]
        local span = abs(a.x - b.x) + abs(a.y - b.y)
        if span > 3 * (cardWidth + cardHeight) then
          early[#early + 1] = { edge = edge, span = span }
        end
      end
    end
    table.sort(early, function(a, b)
      if a.span ~= b.span then
        return a.span > b.span
      end
      return a.edge.key < b.edge.key
    end)
    local firstOccupancy = { hEdge = {}, vEdge = {}, hNode = {}, vNode = {} }
    local firstAccepted = {}
    for _, route in ipairs(sourceRoutes) do
      firstAccepted[#firstAccepted + 1] = route
      addOccupancy(firstOccupancy, grid, route)
    end
    for _, route in ipairs(seeds) do
      firstAccepted[#firstAccepted + 1] = route
      addOccupancy(firstOccupancy, grid, route)
    end
    for i = 1, math.min(#early, 2) do
      local edge = early[i].edge
      local route = routePrerequisite(
        edge,
        buttonOf,
        orderedButtons,
        grid,
        firstOccupancy,
        firstAccepted,
        routeOptions
      )
      if route then
        seeds[#seeds + 1] = route
        seeded[edge.key] = true
        firstAccepted[#firstAccepted + 1] = route
        addOccupancy(firstOccupancy, grid, route)
      end
    end
  end
  -- Reserve a common departure rail for unusually wide fans. Independent
  -- shortest paths tend to fence one another out on these graphs. Candidate
  -- lanes come from the measured free grid and pass the same card/pipe checks
  -- as ordinary routes; no class or promotion identity is involved.
  if routeOptions.fanTrunks ~= false then
    for _, parent in ipairs(data.names) do
      local children = data.children[parent] or {}
      if #children >= 6 then
        local a = buttonOf[parent]
        local eligible, minChildX = {}, math.huge
        for _, child in ipairs(children) do
          local b = buttonOf[child]
          if b.x > a.x + cardWidth + 84 and not seeded[edgeKey(parent, child)] then
            eligible[#eligible + 1] = child
            minChildX = min(minChildX, b.x)
          end
        end
        if #eligible >= 4 then
          local bestBundle, bestCount, bestLength = nil, 0, math.huge
          local py = round(a.y + cardHeight / 2)
          for _, lane in ipairs(grid.xs) do
            if lane > a.x + cardWidth + 28 and lane < minChildX - 28 then
              local bundle, length = {}, 0
              for _, child in ipairs(eligible) do
                local b = buttonOf[child]
                local cy = round(b.y + cardHeight / 2)
                local route = {
                  parent = parent,
                  child = child,
                  points = simplify({
                    { x = a.x + cardWidth, y = py },
                    { x = lane, y = py },
                    { x = lane, y = cy },
                    { x = b.x, y = cy },
                  }),
                }
                local okay = routeSelfClear(route.points, routeOptions)
                  and routeBendsClear(route.points, orderedButtons, routeOptions)
                if okay then
                  for k = 1, #route.points - 1 do
                    local u, v = route.points[k], route.points[k + 1]
                    for _, card in ipairs(orderedButtons) do
                      if
                        not (card.type == parent and k == 1)
                        and not (card.type == child and k == #route.points - 1)
                        and rectangleHitsSegment(
                          u,
                          v,
                          card,
                          routeOptions.pipeHalfWidth or 8,
                          routeOptions.pipeHalfWidth or 8,
                          cardWidth,
                          cardHeight
                        )
                      then
                        okay = false
                        break
                      end
                    end
                    if not okay then
                      break
                    end
                  end
                end
                if okay then
                  for _, prior in ipairs(bundle) do
                    local crosses, overlaps = routeInteractions(route, prior)
                    if crosses > 0 or overlaps > 0 then
                      okay = false
                      break
                    end
                  end
                end
                if okay then
                  for _, prior in ipairs(sourceRoutes) do
                    local crosses, overlaps = routeInteractions(route, prior)
                    if crosses > 0 or overlaps > 0 then
                      okay = false
                      break
                    end
                  end
                end
                if okay then
                  for _, prior in ipairs(seeds) do
                    local crosses, overlaps = routeInteractions(route, prior)
                    if crosses > 0 or overlaps > 0 then
                      okay = false
                      break
                    end
                  end
                end
                if okay then
                  bundle[#bundle + 1] = route
                  for k = 1, #route.points - 1 do
                    length = length
                      + abs(route.points[k].x - route.points[k + 1].x)
                      + abs(route.points[k].y - route.points[k + 1].y)
                  end
                end
              end
              if #bundle > bestCount or (#bundle == bestCount and length < bestLength) then
                bestBundle, bestCount, bestLength = bundle, #bundle, length
              end
            end
          end
          if bestCount >= 3 then
            for _, route in ipairs(bestBundle) do
              seeds[#seeds + 1] = route
              seeded[edgeKey(route.parent, route.child)] = true
            end
          end
        end
      end
    end
  end
  local order = copy(data.edges)
  if routeOptions.routeOrder then
    local priority = {}
    for i = 1, #routeOptions.routeOrder do
      local pair = routeOptions.routeOrder[i]
      priority[edgeKey(pair.parent, pair.child)] = i
    end
    table.sort(order, function(a, b)
      local pa, pb = priority[a.key] or math.huge, priority[b.key] or math.huge
      if pa ~= pb then
        return pa < pb
      end
      return a.key < b.key
    end)
  else
    table.sort(order, function(a, b)
      local pa, pb = buttonOf[a.parent], buttonOf[b.parent]
      local ca, cb = buttonOf[a.child], buttonOf[b.child]
      local da = abs(pa.x - ca.x) + abs(pa.y - ca.y)
      local db = abs(pb.x - cb.x) + abs(pb.y - cb.y)
      if da ~= db then
        if routeOptions.shortFirst then
          return da < db
        end
        return da > db
      end
      return a.key < b.key
    end)
  end
  local occupancy = { hEdge = {}, vEdge = {}, hNode = {}, vNode = {} }
  local accepted, missing, visited = {}, {}, 0
  local routedSoFar = {}
  for i = 1, #sourceRoutes do
    routedSoFar[#routedSoFar + 1] = sourceRoutes[i]
    addOccupancy(occupancy, grid, sourceRoutes[i])
  end
  for i = 1, #seeds do
    accepted[#accepted + 1] = seeds[i]
    routedSoFar[#routedSoFar + 1] = seeds[i]
    addOccupancy(occupancy, grid, seeds[i])
  end
  for i = 1, #order do
    local edge = order[i]
    if not seeded[edge.key] then
      local route, count = routePrerequisite(
        edge,
        buttonOf,
        orderedButtons,
        grid,
        occupancy,
        routedSoFar,
        routeOptions
      )
      visited = visited + count
      if route then
        accepted[#accepted + 1] = route
        routedSoFar[#routedSoFar + 1] = route
        addOccupancy(occupancy, grid, route)
      else
        missing[#missing + 1] = edge
      end
    end
  end
  table.sort(accepted, function(a, b)
    return edgeKey(a.parent, a.child) < edgeKey(b.parent, b.child)
  end)
  local violations, crossingCount, overlapCount, length = {}, 0, 0, 0
  local overlapDetails = {}
  for i = 1, #missing do
    violations[#violations + 1] = "unrouted: " .. missing[i].parent .. " -> " .. missing[i].child
  end
  local pipe = routeOptions.pipeHalfWidth or 8
  local cornerX, cornerY = routeOptions.cornerHalfW or 16, routeOptions.cornerHalfH or 21
  for i = 1, #orderedButtons do
    local b = orderedButtons[i]
    if
      b.x < 0
      or b.y < 0
      or b.x + routeOptions.buttonW > width
      or b.y + routeOptions.buttonH > height
    then
      violations[#violations + 1] = "button outside canvas: " .. b.type
    end
    for j = i + 1, #orderedButtons do
      local c = orderedButtons[j]
      if
        b.x < c.x + routeOptions.buttonW
        and c.x < b.x + routeOptions.buttonW
        and b.y < c.y + routeOptions.buttonH
        and c.y < b.y + routeOptions.buttonH
      then
        violations[#violations + 1] = "button overlap: " .. b.type .. ", " .. c.type
      end
    end
    local open = false
    for _, side in ipairs({ "L", "R", "T", "B" }) do
      local clear = true
      for j = 1, #orderedButtons do
        local c = orderedButtons[j]
        if c ~= b then
          if
            side == "L"
            and c.x + routeOptions.buttonW <= b.x
            and b.x - c.x - routeOptions.buttonW < routeOptions.buttonH
            and c.y < b.y + routeOptions.buttonH
            and b.y < c.y + routeOptions.buttonH
          then
            clear = false
          end
          if
            side == "R"
            and c.x >= b.x + routeOptions.buttonW
            and c.x - b.x - routeOptions.buttonW < routeOptions.buttonH
            and c.y < b.y + routeOptions.buttonH
            and b.y < c.y + routeOptions.buttonH
          then
            clear = false
          end
          if
            side == "T"
            and c.y + routeOptions.buttonH <= b.y
            and b.y - c.y - routeOptions.buttonH < routeOptions.buttonH
            and c.x < b.x + routeOptions.buttonW
            and b.x < c.x + routeOptions.buttonW
          then
            clear = false
          end
          if
            side == "B"
            and c.y >= b.y + routeOptions.buttonH
            and c.y - b.y - routeOptions.buttonH < routeOptions.buttonH
            and c.x < b.x + routeOptions.buttonW
            and b.x < c.x + routeOptions.buttonW
          then
            clear = false
          end
        end
      end
      if clear then
        open = true
        break
      end
    end
    if not open then
      violations[#violations + 1] = "no open side: " .. b.type
    end
  end
  local allRoutes = copy(accepted)
  for i = 1, #sourceRoutes do
    allRoutes[#allRoutes + 1] = sourceRoutes[i]
  end
  for i = 1, #allRoutes do
    local route = allRoutes[i]
    local clear, why = routeSelfClear(route.points, routeOptions)
    if not clear then
      violations[#violations + 1] = why .. ": " .. route.parent .. " -> " .. route.child
    end
    for k = 1, #route.points do
      local p = route.points[k]
      if
        k > 1
        and k < #route.points
        and (p.x < pipe or p.x > width - pipe or p.y < pipe or p.y > height - pipe)
      then
        violations[#violations + 1] = "native pipe outside canvas: "
          .. route.parent
          .. " -> "
          .. route.child
      end
      if k > 1 and k < #route.points then
        local a, b = route.points[k - 1], route.points[k + 1]
        local isBend = (a.x == p.x) ~= (p.x == b.x)
        if isBend then
          if p.x < cornerX or p.x > width - cornerX or p.y < cornerY or p.y > height - cornerY then
            violations[#violations + 1] = "native elbow outside canvas: "
              .. route.parent
              .. " -> "
              .. route.child
          end
          for j = 1, #orderedButtons do
            local card = orderedButtons[j]
            if
              p.x + cornerX >= card.x
              and p.x - cornerX <= card.x + routeOptions.buttonW
              and p.y + cornerY >= card.y
              and p.y - cornerY <= card.y + routeOptions.buttonH
            then
              violations[#violations + 1] = "native elbow touches button: "
                .. route.parent
                .. " -> "
                .. route.child
                .. " at "
                .. card.type
            end
          end
        end
      end
    end
    for k = 1, #route.points - 1 do
      local a, b = route.points[k], route.points[k + 1]
      length = length + abs(a.x - b.x) + abs(a.y - b.y)
      if a.x ~= b.x and a.y ~= b.y then
        violations[#violations + 1] = "nonorthogonal route: "
          .. route.parent
          .. " -> "
          .. route.child
      end
      if
        min(a.x, b.x) < 0
        or max(a.x, b.x) > width
        or min(a.y, b.y) < 0
        or max(a.y, b.y) > height
      then
        violations[#violations + 1] = "route outside canvas: "
          .. route.parent
          .. " -> "
          .. route.child
      end
      for j = 1, #orderedButtons do
        local card = orderedButtons[j]
        if rectangleHitsSegment(a, b, card, 0, 0, routeOptions.buttonW, routeOptions.buttonH) then
          violations[#violations + 1] = "route enters button: "
            .. route.parent
            .. " -> "
            .. route.child
            .. " through "
            .. card.type
        elseif
          not (
            (card.type == route.parent and k == 1)
            or (card.type == route.child and k == #route.points - 1)
          )
          and rectangleHitsSegment(
            a,
            b,
            card,
            pipe,
            pipe,
            routeOptions.buttonW,
            routeOptions.buttonH
          )
        then
          violations[#violations + 1] = "route through button: "
            .. route.parent
            .. " -> "
            .. route.child
            .. " through "
            .. card.type
        end
      end
    end
    for j = i + 1, #allRoutes do
      local c, o = routeInteractions(route, allRoutes[j])
      crossingCount, overlapCount = crossingCount + c, overlapCount + o
      if o > 0 and #overlapDetails < 32 then
        overlapDetails[#overlapDetails + 1] = route.parent
          .. " -> "
          .. route.child
          .. " with "
          .. allRoutes[j].parent
          .. " -> "
          .. allRoutes[j].child
          .. " ("
          .. o
          .. ")"
      end
    end
  end
  if overlapCount > 0 then
    violations[#violations + 1] = "unrelated pipe overlaps: " .. overlapCount
  end
  if
    crossingCount > (routeOptions.readabilityCrossingBudget or 0)
    and not routeOptions.provenNonplanar
  then
    violations[#violations + 1] = "unproven crossings: " .. crossingCount
  end
  local result = {
    buttons = orderedButtons,
    routes = accepted,
    source = source,
    sourceRoutes = sourceRoutes,
    width = width,
    height = height,
    scale = routeOptions.scale
      or min((routeOptions.viewportW or width) / width, (routeOptions.viewportH or height) / height),
    crossings = crossingCount,
    violations = violations,
    stats = {
      edges = #data.edges,
      routed = #accepted,
      roots = #sourceRoutes,
      routeStates = visited,
      gridNodes = grid.nx * grid.ny,
      length = length,
      overlaps = overlapCount,
      overlapDetails = overlapDetails,
    },
  }
  -- A late edge can be fenced out by an earlier route. Give the first missing
  -- prerequisite first access to the corridors, with one bounded reroute.
  local ripups = routeOptions.maxRipups
  if ripups == nil then
    ripups = 1
  end
  if #missing > 0 and ripups > 0 then
    local retryOpts = {}
    for k, v in pairs(routeOptions) do
      retryOpts[k] = v
    end
    retryOpts.maxRipups = ripups - 1
    retryOpts.routeOrder = { missing[1] }
    for i = 1, #order do
      if order[i].key ~= missing[1].key then
        retryOpts.routeOrder[#retryOpts.routeOrder + 1] = order[i]
      end
    end
    local retry = PromotionLayoutRoute(graph, orderedButtons, retryOpts)
    retry.stats.ripups = (retry.stats.ripups or 0) + 1
    if layoutScoreLessThan(retry, result) then
      return retry
    end
  end
  return result
end

-- Bounded, deterministic baseline candidate. A constructive planar-placement
-- module may call PromotionLayoutRoute directly with a stronger embedding.
function PromotionLayoutSolve(graph, geometry)
  local routeOptions = geometry or {}
  local timer = routeOptions.profile and os and os.clock
  local stage = { order = 0, placement = 0, routing = 0, audit = 0 }
  local stageStart = timer and timer()
  assert(routeOptions.buttonW and routeOptions.buttonH, "buttonW and buttonH required")
  local data = graphData(graph)
  local defaultW = routeOptions.defaultW or routeOptions.viewportW or 1638
  local defaultH = routeOptions.defaultH or routeOptions.viewportH or 1040
  local candidates = {}
  for seed = 1, 4 do
    local order, estimate, last = minimizeLayerCrossings(data, seed)
    candidates[#candidates + 1] = { order = order, estimate = estimate, last = last, seed = seed }
  end
  if timer then
    stage.order = timer() - stageStart
  end
  table.sort(candidates, function(a, b)
    if a.estimate ~= b.estimate then
      return a.estimate < b.estimate
    end
    return a.seed < b.seed
  end)
  local best, examined = nil, 0
  local plans = {
    { candidate = candidates[1], factor = 1 },
    { candidate = candidates[2], factor = 1 },
    { candidate = candidates[1], factor = math.sqrt(1.5), compress = true },
    { candidate = candidates[1], factor = math.sqrt(1.5) },
  }
  for pi = 1, min(#plans, routeOptions.maxCandidates or 4) do
    local candidate, factor = plans[pi].candidate, plans[pi].factor
    -- Exact proportional dimensions preserve both aspect and the area cap;
    -- only the coordinates of individual controls are rounded to pixels.
    local width, height = defaultW * factor, defaultH * factor
    stageStart = timer and timer()
    local buttons, warnings = placePromotionCards(
      data,
      candidate.order,
      candidate.last,
      width,
      height,
      routeOptions,
      graph.chains
    )
    if timer then
      stage.placement = stage.placement + timer() - stageStart
    end
    if plans[pi].compress then
      local margin =
        max(28, (routeOptions.cornerHalfH or 21) + (routeOptions.pipeHalfWidth or 8) + 5)
      local left = margin + 52
      local sx = (defaultW - left - margin - routeOptions.buttonW)
        / (width - left - margin - routeOptions.buttonW)
      local sy = (defaultH - 2 * margin - routeOptions.buttonH)
        / (height - 2 * margin - routeOptions.buttonH)
      for _, button in ipairs(buttons) do
        button.x = round(left + (button.x - left) * sx)
        button.y = round(margin + (button.y - margin) * sy)
      end
      width, height = defaultW, defaultH
      factor = 1
    end
    local routeOpts = {}
    for k, v in pairs(routeOptions) do
      routeOpts[k] = v
    end
    routeOpts.width, routeOpts.height = width, height
    routeOpts.defaultW, routeOpts.defaultH = defaultW, defaultH
    routeOpts.viewportW = routeOptions.viewportW or defaultW
    routeOpts.viewportH = routeOptions.viewportH or defaultH
    routeOpts.scale = 1 / factor
    stageStart = timer and timer()
    local result = PromotionLayoutRoute(graph, buttons, routeOpts)
    if timer then
      stage.routing = stage.routing + timer() - stageStart
    end
    for i = 1, #warnings do
      result.violations[#result.violations + 1] = warnings[i]
    end
    result.stats.orderCrossings = candidate.estimate
    result.stats.orderSeed = candidate.seed
    examined = examined + 1
    -- Score the geometry that can actually be drawn. A centerline-only
    -- success may still have colliding native elbows or crowded cards;
    -- it must not hide a valid later placement from the presentation layer.
    if type(PromotionCheckLayout) == "function" then
      stageStart = timer and timer()
      PromotionCheckLayout(graph, result, routeOpts)
      if timer then
        stage.audit = stage.audit + timer() - stageStart
      end
    end
    local resultAccepted = result.valid == true
    local bestAccepted = best and best.valid == true
    if
      not best
      or (resultAccepted and not bestAccepted)
      or (resultAccepted == bestAccepted and layoutScoreLessThan(result, best))
    then
      best = result
    end
    if best.valid ~= false and #best.violations == 0 and best.crossings == 0 and factor == 1 then
      best.stats.candidates = examined
      if timer then
        best.stats.stage = stage
      end
      return best
    end
    if pi == 1 and best.valid and (best.stats.routeStates or 0) >= 5000 then
      -- A complete first candidate has already consumed substantial search
      -- work. Keep that audited diagram instead of repeating a similarly
      -- expensive order variant merely to chase a minor score difference.
      best.stats.candidates = examined
      if timer then
        best.stats.stage = stage
      end
      return best
    end
    if pi >= 2 and best.valid and best.scale == 1 then
      -- Default-canvas orders have been considered. A larger logical canvas
      -- is reserved for cases the normal viewport cannot validate.
      best.stats.candidates = examined
      if timer then
        best.stats.stage = stage
      end
      return best
    end
  end
  best.stats.candidates = examined
  if timer then
    best.stats.stage = stage
  end
  return best
end

-- Sparse forests with many independent entry promotions use the horizontal
-- canvas rather than stacking every root in one tall column. Each connected
-- component must be a simple path; branching forests use the full solver.
function PromotionLayoutSolveSparse(graph, geometry)
  local roots = graph.roots or {}
  if #roots < 6 or #roots * 2 <= #graph.order then
    return nil
  end
  local routeOptions = {}
  for key, value in pairs(geometry or {}) do
    routeOptions[key] = value
  end
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local width, height =
    routeOptions.defaultW or routeOptions.viewportW, routeOptions.defaultH or routeOptions.viewportH
  if not cardWidth or not cardHeight or not width or not height then
    return nil
  end
  local seen, singles, lines = {}, {}, {}
  for _, root in ipairs(roots) do
    local line, node = {}, root
    while node do
      if seen[node] or not graph.nodes[node] then
        return nil
      end
      seen[node] = true
      line[#line + 1] = node
      local children = graph.nodes[node].children or {}
      if #children > 1 then
        return nil
      end
      if #children == 1 and #(graph.nodes[children[1]].parents or {}) ~= 1 then
        return nil
      end
      node = children[1]
    end
    if #line == 1 then
      singles[#singles + 1] = line[1]
    else
      lines[#lines + 1] = line
    end
  end
  if #singles + #lines ~= #roots then
    return nil
  end
  for _, name in ipairs(graph.order) do
    if not seen[name] then
      return nil
    end
  end
  table.sort(singles)
  table.sort(lines, function(a, b)
    return a[1] < b[1]
  end)
  local columns = math.min(3, math.max(1, #singles))
  if #singles < 3 then
    return nil
  end
  local singletonRows = math.ceil(#singles / columns)
  local rows = singletonRows + #lines
  local margin = max(28, (routeOptions.cornerHalfH or 21) + (routeOptions.pipeHalfWidth or 8) + 5)
  -- Isolated roots have only one source rail. Their rows need enough room
  -- for native junction art, but not the larger gutter used by busy rows.
  local pitchY = cardHeight + 20
  if rows > 1 then
    pitchY = min(pitchY, (height - 2 * margin - cardHeight) / (rows - 1))
  end
  if pitchY < cardHeight + 2 * (routeOptions.pipeHalfWidth or 8) + 4 then
    return nil
  end
  local pitchX = cardWidth + 60
  local maxColumns = columns
  for _, line in ipairs(lines) do
    maxColumns = max(maxColumns, #line)
  end
  local firstX = margin + 52
  if maxColumns > 1 then
    pitchX = min(pitchX, (width - margin - firstX - cardWidth) / (maxColumns - 1))
  end
  if pitchX < cardWidth + cardHeight then
    return nil
  end
  local firstY = round(margin + 50)
  local rowY = {}
  local extraGap = max(0, 84 - pitchY)
  local breakRow = #lines > 0 and singletonRows or math.floor(rows / 2)
  for row = 1, singletonRows do
    rowY[row] =
      round(firstY + (row - 1) * pitchY + (#lines == 0 and row > breakRow and extraGap or 0))
  end
  local chainPitch = cardHeight + 19
  for i = 1, #lines do
    rowY[singletonRows + i] = round(rowY[singletonRows] + pitchY + extraGap + (i - 1) * chainPitch)
  end
  if rowY[rows] + cardHeight > height - margin then
    return nil
  end
  local buttons, rootColumn = {}, {}
  local function put(name, column, row)
    local button = { type = name, x = round(firstX + (column - 1) * pitchX), y = rowY[row] }
    buttons[#buttons + 1] = button
    return button
  end
  for i, name in ipairs(singles) do
    local column = math.floor((i - 1) / singletonRows) + 1
    local row = (i - 1) % singletonRows + 1
    rootColumn[name] = { column = column, row = row, button = put(name, column, row) }
  end
  for i, line in ipairs(lines) do
    local row = singletonRows + i
    for column, name in ipairs(line) do
      local button = put(name, column, row)
      if column == 1 then
        rootColumn[name] = { column = column, row = row, button = button }
      end
    end
  end
  local source = {
    x = round(firstX - 28),
    y = round((rowY[breakRow] + rowY[breakRow + 1]) / 2 + cardHeight / 2),
  }
  local sourceRoutes = {}
  for _, root in ipairs(roots) do
    local placed = assert(rootColumn[root])
    local card = placed.button
    local cy = round(card.y + cardHeight / 2)
    local points = { { x = source.x, y = source.y } }
    if placed.column == 1 then
      if cy ~= source.y then
        points[#points + 1] = { x = source.x, y = cy }
      end
      points[#points + 1] = { x = card.x, y = cy }
    else
      local approach = round(card.x - 28)
      points[#points + 1] = { x = approach, y = source.y }
      points[#points + 1] = { x = approach, y = cy }
      points[#points + 1] = { x = card.x, y = cy }
    end
    sourceRoutes[#sourceRoutes + 1] =
      { parent = "__PROMOTION_SOURCE__", child = root, points = points }
  end
  routeOptions.width, routeOptions.height, routeOptions.scale = width, height, 1
  routeOptions.sourcePoint, routeOptions.sourceRoutes = source, sourceRoutes
  return PromotionLayoutRoute(graph, buttons, routeOptions)
end

local function inferredSides(guide)
  local points = guide and (guide.points or guide)
  if not points or #points < 2 then
    return nil
  end
  local first, second = points[1], points[2]
  local before, last = points[#points - 1], points[#points]
  local source = second.x > first.x and "R"
    or second.x < first.x and "L"
    or second.y > first.y and "B"
    or "T"
  local target = last.x < before.x and "R"
    or last.x > before.x and "L"
    or last.y < before.y and "B"
    or "T"
  return source, target
end

local function projectedPathClear(points, parent, child, buttons, routeOptions)
  local path = simplify(points)
  if #path < 2 then
    return false
  end
  if not routeSelfClear(path, routeOptions) then
    return false
  end
  local cardWidth, cardHeight = routeOptions.buttonW, routeOptions.buttonH
  local pipe = routeOptions.pipeHalfWidth or 4
  local cornerX, cornerY = routeOptions.cornerHalfW or 16, routeOptions.cornerHalfH or 21
  for i = 1, #path do
    local p = path[i]
    if
      p.x < pipe
      or p.x > routeOptions.width - pipe
      or p.y < pipe
      or p.y > routeOptions.height - pipe
    then
      return false
    end
    if i > 1 and i < #path then
      local a, b = path[i - 1], path[i + 1]
      if (a.x == p.x) ~= (p.x == b.x) then
        if
          p.x < cornerX
          or p.x > routeOptions.width - cornerX
          or p.y < cornerY
          or p.y > routeOptions.height - cornerY
        then
          return false
        end
        for _, card in ipairs(buttons) do
          if
            p.x + cornerX >= card.x
            and p.x - cornerX <= card.x + cardWidth
            and p.y + cornerY >= card.y
            and p.y - cornerY <= card.y + cardHeight
          then
            return false
          end
        end
      end
    end
  end
  for i = 1, #path - 1 do
    local a, b = path[i], path[i + 1]
    if a.x ~= b.x and a.y ~= b.y then
      return false
    end
    for _, card in ipairs(buttons) do
      if rectangleHitsSegment(a, b, card, 0, 0, cardWidth, cardHeight) then
        return false
      end
      local attached = (card.type == parent and i == 1) or (card.type == child and i == #path - 1)
      if not attached and rectangleHitsSegment(a, b, card, pipe, pipe, cardWidth, cardHeight) then
        return false
      end
    end
  end
  return true, path
end

local function projectGuideRoute(guide, placement, buttons, routeOptions, reserved)
  local parent, child = guide.parent, guide.child
  local macroFromSide, macroToSide = inferredSides(guide)
  local fromSide, toSide = macroFromSide, macroToSide
  local assignment = routeOptions.portAssignment
    and (
      routeOptions.portAssignment[edgeKey(parent, child)]
      or routeOptions.portAssignment[parent .. "\002" .. child]
    )
  if assignment then
    fromSide = assignment.sourceSide or assignment.parentSide or fromSide
    toSide = assignment.targetSide or assignment.childSide or toSide
  end
  if not fromSide or not toSide then
    return nil
  end
  local fromPort = assignment and assignment.sourcePort
    or (placement.ports[parent] and placement.ports[parent][fromSide])
  local toPort = assignment and assignment.targetPort
    or (placement.ports[child] and placement.ports[child][toSide])
  if not fromPort or not toPort then
    return nil
  end
  local fromBox = placement.blockBoxes[placement.member[parent]]
  local toBox = placement.blockBoxes[placement.member[child]]
  if not fromBox or not toBox then
    return nil
  end
  local p = { x = round(fromPort.x), y = round(fromPort.y) }
  local q = { x = round(toPort.x), y = round(toPort.y) }
  local horizontal = (fromSide == "R" or fromSide == "L") and (toSide == "R" or toSide == "L")
  local vertical = (fromSide == "T" or fromSide == "B") and (toSide == "T" or toSide == "B")
  local xGap = routeOptions.guidePortOffsetX or 24
  local yGap = routeOptions.guidePortOffsetY or 24
  local sourceLane = assignment and (assignment.sourceLane or assignment.laneIndex) or 0
  local targetLane = assignment and (assignment.targetLane or assignment.laneIndex) or 0
  local laneIndex = sourceLane
  local lanePitch = assignment and assignment.lanePitch or routeOptions.lanePitch or 8
  local candidates, macroCandidates = {}, {}
  -- A block guide is an actual embedding corridor, not merely a hint about
  -- which two blocks are near each other. Reanchor its first and last legs to
  -- card ports while retaining the intervening face route. This also lets an
  -- end card use its block-end side, where a long-side rank-port assignment
  -- would needlessly pass through the adjacent chain card.
  if
    guide.points
    and #guide.points >= 3
    and macroFromSide
    and macroToSide
    and placement.ports[parent]
    and placement.ports[child]
  then
    local macroPoints = {}
    for i, point in ipairs(guide.points) do
      macroPoints[i] = { x = point.x, y = point.y }
    end
    local macro = simplify(macroPoints)
    if #macro >= 3 then
      -- Macro solvers usually clear card rectangles but not the wider native
      -- elbow art. Push an outer-face lane just beyond that extra envelope.
      local left, right, top, bottom = math.huge, -math.huge, math.huge, -math.huge
      for _, card in ipairs(buttons) do
        left = min(left, card.x)
        right = max(right, card.x + routeOptions.buttonW)
        top = min(top, card.y)
        bottom = max(bottom, card.y + routeOptions.buttonH)
      end
      local safeX = (routeOptions.cornerHalfW or 16) + 2
      local safeY = (routeOptions.cornerHalfH or 21) + 2
      for i = 2, #macro - 1 do
        local v = macro[i]
        if v.x > right and v.x < right + safeX then
          v.x = right + safeX
        elseif v.x < left and v.x > left - safeX then
          v.x = left - safeX
        end
        if v.y > bottom and v.y < bottom + safeY then
          v.y = bottom + safeY
        elseif v.y < top and v.y > top - safeY then
          v.y = top - safeY
        end
      end
      local sourcePort = assignment
          and assignment.sourceSide == macroFromSide
          and assignment.sourcePort
        or placement.ports[parent][macroFromSide]
      local targetPort = assignment
          and assignment.targetSide == macroToSide
          and assignment.targetPort
        or placement.ports[child][macroToSide]
      if sourcePort and targetPort then
        local a = { x = round(sourcePort.x), y = round(sourcePort.y) }
        local z = { x = round(targetPort.x), y = round(targetPort.y) }
        local first, last = macro[2], macro[#macro - 1]
        if
          macroFromSide == macroToSide
          and #macro == 4
          and (macroFromSide == "R" or macroFromSide == "L")
          and abs(macro[2].x - macro[3].x) < 0.001
        then
          local sourceCard, targetCard
          for _, card in ipairs(buttons) do
            if card.type == parent then
              sourceCard = card
              break
            end
          end
          for _, card in ipairs(buttons) do
            if card.type == child then
              targetCard = card
              break
            end
          end
          local sy = round(macro[1].y)
          if
            sourceCard
            and sy >= sourceCard.y + 6
            and sy <= sourceCard.y + routeOptions.buttonH - 6
          then
            a.y = sy
          end
          local lane = round(macro[2].x)
          macroCandidates[#macroCandidates + 1] = {
            a,
            { x = lane, y = a.y },
            { x = lane, y = z.y },
            z,
          }
          -- A macro route ending at the corner of a block can be rerouted to
          -- the adjacent card edge if the nominal side is hidden by a nearby
          -- card. The added halo must still clear the full native elbow.
          if targetCard and abs(macro[#macro].y - targetCard.y) <= 8 then
            local halo = targetCard.y - (routeOptions.cornerHalfH or 21) - 3
            local inset = 24
            local tx = macroToSide == "R" and targetCard.x + routeOptions.buttonW - inset
              or targetCard.x + inset
            macroCandidates[#macroCandidates + 1] = {
              a,
              { x = lane, y = a.y },
              { x = lane, y = halo },
              { x = tx, y = halo },
              { x = tx, y = targetCard.y },
            }
          elseif targetCard and abs(macro[#macro].y - targetCard.y - routeOptions.buttonH) <= 8 then
            local halo = targetCard.y + routeOptions.buttonH + (routeOptions.cornerHalfH or 21) + 3
            local inset = 24
            local tx = macroToSide == "R" and targetCard.x + routeOptions.buttonW - inset
              or targetCard.x + inset
            macroCandidates[#macroCandidates + 1] = {
              a,
              { x = lane, y = a.y },
              { x = lane, y = halo },
              { x = tx, y = halo },
              { x = tx, y = targetCard.y + routeOptions.buttonH },
            }
          end
        elseif
          macroFromSide == macroToSide
          and #macro == 4
          and (macroFromSide == "T" or macroFromSide == "B")
          and abs(macro[2].y - macro[3].y) < 0.001
        then
          local sourceCard
          for _, card in ipairs(buttons) do
            if card.type == parent then
              sourceCard = card
              break
            end
          end
          local sx = round(macro[1].x)
          if
            sourceCard
            and sx >= sourceCard.x + 6
            and sx <= sourceCard.x + routeOptions.buttonW - 6
          then
            a.x = sx
          end
          local lane = round(macro[2].y)
          macroCandidates[#macroCandidates + 1] = {
            a,
            { x = a.x, y = lane },
            { x = z.x, y = lane },
            z,
          }
        end
        local path = { a }
        if macroFromSide == "L" or macroFromSide == "R" then
          path[#path + 1] = { x = round(first.x), y = a.y }
        else
          path[#path + 1] = { x = a.x, y = round(first.y) }
        end
        for i = 2, #macro - 1 do
          path[#path + 1] = { x = round(macro[i].x), y = round(macro[i].y) }
        end
        if macroToSide == "L" or macroToSide == "R" then
          path[#path + 1] = { x = round(last.x), y = z.y }
        else
          path[#path + 1] = { x = z.x, y = round(last.y) }
        end
        path[#path + 1] = z
        macroCandidates[#macroCandidates + 1] = path
      end
    end
  end
  -- For two-block guides with facing side ports, a near-row alignment can
  -- leave less than one native turn diameter between the two bends. Slide a
  -- port along its own card edge; the relationship between promotions does
  -- not prescribe a center-of-side attachment.
  if
    (macroFromSide == "L" and macroToSide == "R")
    or (macroFromSide == "R" and macroToSide == "L")
  then
    local u = placement.ports[parent][macroFromSide]
    local v = placement.ports[child][macroToSide]
    local card = nil
    for _, b in ipairs(buttons) do
      if b.type == parent then
        card = b
        break
      end
    end
    if u and v and card and abs(u.y - v.y) < 46 then
      local desired = round(v.y + (u.y >= v.y and 46 or -46))
      if desired >= card.y + 6 and desired <= card.y + routeOptions.buttonH - 6 then
        local start = { x = round(u.x), y = desired }
        local finish = { x = round(v.x), y = round(v.y) }
        local lane = round((start.x + finish.x) / 2)
        macroCandidates[#macroCandidates + 1] =
          { start, { x = lane, y = start.y }, { x = lane, y = finish.y }, finish }
      end
    end
  end
  if horizontal then
    if assignment and assignment.sourceLane and assignment.targetLane then
      local sx = fromSide == "R" and round(fromBox.x + fromBox.w + xGap + sourceLane * lanePitch)
        or round(fromBox.x - xGap - sourceLane * lanePitch)
      local tx = toSide == "R" and round(toBox.x + toBox.w + xGap + targetLane * lanePitch)
        or round(toBox.x - xGap - targetLane * lanePitch)
      sx = assignment.sourceTrackX or assignment.trackX or sx
      tx = assignment.targetTrackX or assignment.trackX or tx
      if sx == tx then
        candidates[#candidates + 1] = { p, { x = sx, y = p.y }, { x = tx, y = q.y }, q }
      else
        local mids = { round((p.y + q.y) / 2) }
        if guide.points[3] then
          mids[#mids + 1] = round(guide.points[3].y)
        end
        for i = 1, #mids do
          local mid = mids[i]
          candidates[#candidates + 1] = {
            p,
            { x = sx, y = p.y },
            { x = sx, y = mid },
            { x = tx, y = mid },
            { x = tx, y = q.y },
            q,
          }
        end
      end
    elseif fromSide == "R" and toSide == "R" then
      for _, extra in ipairs({ 0, 24, 48 }) do
        local lane = round(
          max(fromBox.x + fromBox.w, toBox.x + toBox.w) + xGap + laneIndex * lanePitch + extra
        )
        if assignment and assignment.trackX then
          lane = assignment.trackX
        end
        candidates[#candidates + 1] = { p, { x = lane, y = p.y }, { x = lane, y = q.y }, q }
      end
    elseif fromSide == "L" and toSide == "L" then
      for _, extra in ipairs({ 0, 24, 48 }) do
        local lane = round(min(fromBox.x, toBox.x) - xGap - laneIndex * lanePitch - extra)
        if assignment and assignment.trackX then
          lane = assignment.trackX
        end
        candidates[#candidates + 1] = { p, { x = lane, y = p.y }, { x = lane, y = q.y }, q }
      end
    else
      local left, right
      if fromSide == "R" then
        left = fromBox.x + fromBox.w + xGap
        right = toBox.x - xGap
      else
        left = toBox.x + toBox.w + xGap
        right = fromBox.x - xGap
      end
      if p.y == q.y then
        candidates[#candidates + 1] = { p, q }
      end
      if left <= right then
        local guideX = guide.points[2] and guide.points[2].x or (left + right) / 2
        local lane = round(max(left, min(right, guideX + laneIndex * lanePitch)))
        if assignment and assignment.trackX then
          lane = assignment.trackX
        end
        candidates[#candidates + 1] = { p, { x = lane, y = p.y }, { x = lane, y = q.y }, q }
      end
    end
  elseif vertical then
    if assignment and assignment.sourceLane and assignment.targetLane then
      local sy = fromSide == "B" and round(fromBox.y + fromBox.h + yGap + sourceLane * lanePitch)
        or round(fromBox.y - yGap - sourceLane * lanePitch)
      local ty = toSide == "B" and round(toBox.y + toBox.h + yGap + targetLane * lanePitch)
        or round(toBox.y - yGap - targetLane * lanePitch)
      sy = assignment.sourceTrackY or assignment.trackY or sy
      ty = assignment.targetTrackY or assignment.trackY or ty
      if sy == ty then
        candidates[#candidates + 1] = { p, { x = p.x, y = sy }, { x = q.x, y = ty }, q }
      else
        local mids = { round((p.x + q.x) / 2) }
        if guide.points[3] then
          mids[#mids + 1] = round(guide.points[3].x)
        end
        for i = 1, #mids do
          local mid = mids[i]
          candidates[#candidates + 1] = {
            p,
            { x = p.x, y = sy },
            { x = mid, y = sy },
            { x = mid, y = ty },
            { x = q.x, y = ty },
            q,
          }
        end
      end
    elseif fromSide == "B" and toSide == "B" then
      for _, extra in ipairs({ 0, 24, 48 }) do
        local lane = round(
          max(fromBox.y + fromBox.h, toBox.y + toBox.h) + yGap + laneIndex * lanePitch + extra
        )
        if assignment and assignment.trackY then
          lane = assignment.trackY
        end
        candidates[#candidates + 1] = { p, { x = p.x, y = lane }, { x = q.x, y = lane }, q }
      end
    elseif fromSide == "T" and toSide == "T" then
      for _, extra in ipairs({ 0, 24, 48 }) do
        local lane = round(min(fromBox.y, toBox.y) - yGap - laneIndex * lanePitch - extra)
        if assignment and assignment.trackY then
          lane = assignment.trackY
        end
        candidates[#candidates + 1] = { p, { x = p.x, y = lane }, { x = q.x, y = lane }, q }
      end
    else
      local top, bottom
      if fromSide == "B" then
        top = fromBox.y + fromBox.h + yGap
        bottom = toBox.y - yGap
      else
        top = toBox.y + toBox.h + yGap
        bottom = fromBox.y - yGap
      end
      if p.x == q.x then
        candidates[#candidates + 1] = { p, q }
      end
      if top <= bottom then
        local guideY = guide.points[2] and guide.points[2].y or (top + bottom) / 2
        local lane = round(max(top, min(bottom, guideY + laneIndex * lanePitch)))
        if assignment and assignment.trackY then
          lane = assignment.trackY
        end
        candidates[#candidates + 1] = { p, { x = p.x, y = lane }, { x = q.x, y = lane }, q }
      end
    end
  else
    if fromSide == "R" or fromSide == "L" then
      candidates[#candidates + 1] = { p, { x = q.x, y = p.y }, q }
      for _, extra in ipairs({ 0, 24, 48 }) do
        local laneX = fromSide == "R"
            and round(fromBox.x + fromBox.w + xGap + sourceLane * lanePitch + extra)
          or round(fromBox.x - xGap - sourceLane * lanePitch - extra)
        local haloY = toSide == "B"
            and round(
              max(fromBox.y + fromBox.h, toBox.y + toBox.h) + yGap + targetLane * lanePitch + extra
            )
          or round(min(fromBox.y, toBox.y) - yGap - targetLane * lanePitch - extra)
        if assignment and assignment.sourceTrackX then
          laneX = assignment.sourceTrackX
        end
        if assignment and assignment.targetTrackY then
          haloY = assignment.targetTrackY
        end
        candidates[#candidates + 1] =
          { p, { x = laneX, y = p.y }, { x = laneX, y = haloY }, { x = q.x, y = haloY }, q }
      end
    else
      candidates[#candidates + 1] = { p, { x = p.x, y = q.y }, q }
      for _, extra in ipairs({ 0, 24, 48 }) do
        local haloY = fromSide == "B"
            and round(fromBox.y + fromBox.h + yGap + sourceLane * lanePitch + extra)
          or round(fromBox.y - yGap - sourceLane * lanePitch - extra)
        local laneX = toSide == "R"
            and round(
              max(fromBox.x + fromBox.w, toBox.x + toBox.w) + xGap + targetLane * lanePitch + extra
            )
          or round(min(fromBox.x, toBox.x) - xGap - targetLane * lanePitch - extra)
        if assignment and assignment.sourceTrackY then
          haloY = assignment.sourceTrackY
        end
        if assignment and assignment.targetTrackX then
          laneX = assignment.targetTrackX
        end
        candidates[#candidates + 1] =
          { p, { x = p.x, y = haloY }, { x = laneX, y = haloY }, { x = laneX, y = q.y }, q }
      end
    end
  end
  for i = 1, #macroCandidates do
    candidates[#candidates + 1] = macroCandidates[i]
  end
  for i = 1, #candidates do
    local ok, path = projectedPathClear(candidates[i], parent, child, buttons, routeOptions)
    if ok then
      local route = { parent = parent, child = child, points = path }
      local clear = true
      for j = 1, #(reserved or {}) do
        local crossing, overlap = routeInteractions(route, reserved[j])
        if crossing > 0 or overlap > 0 then
          clear = false
          break
        end
      end
      if clear then
        return route
      end
    end
  end
  return nil
end

local function projectSourceRoute(root, guide, placement, buttons, routeOptions, reserved)
  local source = placement.sourcePoint
  local _, side = inferredSides(guide)
  local assignment = routeOptions.portAssignment
    and (
      routeOptions.portAssignment[edgeKey("__PROMOTION_SOURCE__", root)]
      or routeOptions.portAssignment["__PROMOTION_SOURCE__\002" .. root]
    )
  if assignment then
    side = assignment.targetSide or assignment.childSide or side
  end
  if not side or not placement.ports[root] then
    return nil
  end
  local q0 = assignment and assignment.targetPort or placement.ports[root][side]
  local p = { x = round(source.x), y = round(source.y) }
  local q = { x = round(q0.x), y = round(q0.y) }
  local box = placement.blockBoxes[placement.member[root]]
  local xGap, yGap = routeOptions.guidePortOffsetX or 24, routeOptions.guidePortOffsetY or 24
  local laneIndex = assignment and (assignment.laneIndex or assignment.targetLane) or 0
  local lanePitch = assignment and assignment.lanePitch or routeOptions.lanePitch or 8
  local candidates = {}
  if #guide.points >= 3 then
    local endPoint = guide.points[#guide.points]
    local card
    for _, b in ipairs(buttons) do
      if b.type == root then
        card = b
        break
      end
    end
    if card and abs(endPoint.y - box.y) <= 2 then
      local tx = endPoint.x >= card.x + routeOptions.buttonW / 2
          and card.x + routeOptions.buttonW - 24
        or card.x + 24
      local lane = card.y - (routeOptions.cornerHalfH or 21) - 3
      candidates[#candidates + 1] =
        { p, { x = p.x, y = lane }, { x = tx, y = lane }, { x = tx, y = card.y } }
    elseif card and abs(endPoint.y - box.y - box.h) <= 2 then
      local tx = endPoint.x >= card.x + routeOptions.buttonW / 2
          and card.x + routeOptions.buttonW - 24
        or card.x + 24
      local lane = card.y + routeOptions.buttonH + (routeOptions.cornerHalfH or 21) + 3
      candidates[#candidates + 1] = {
        p,
        { x = p.x, y = lane },
        { x = tx, y = lane },
        { x = tx, y = card.y + routeOptions.buttonH },
      }
    end
  end
  local maxBottom, minTop = -math.huge, math.huge
  for _, otherBox in pairs(placement.blockBoxes) do
    maxBottom = max(maxBottom, otherBox.y + otherBox.h)
    minTop = min(minTop, otherBox.y)
  end
  if side == "L" or side == "R" then
    local lane = side == "L" and round(box.x - xGap - laneIndex * lanePitch)
      or round(box.x + box.w + xGap + laneIndex * lanePitch)
    if assignment and assignment.trackX then
      lane = assignment.trackX
    end
    candidates[#candidates + 1] = { p, { x = lane, y = p.y }, { x = lane, y = q.y }, q }
    candidates[#candidates + 1] = { p, { x = p.x, y = q.y }, q }
  else
    local lane = side == "T" and round(box.y - yGap - laneIndex * lanePitch)
      or round(box.y + box.h + yGap + laneIndex * lanePitch)
    if assignment and assignment.trackY then
      lane = assignment.trackY
    end
    candidates[#candidates + 1] = { p, { x = p.x, y = lane }, { x = q.x, y = lane }, q }
    candidates[#candidates + 1] = { p, { x = q.x, y = p.y }, q }
  end
  -- A rank at the interior of a horizontal family must enter through the
  -- block's top or bottom halo, not through its adjacent family card.
  if
    (side == "T" or side == "B")
    and placement.blocks
    and placement.blocks[placement.member[root]]
    and placement.blocks[placement.member[root]].orientation == "h"
  then
    local haloY = side == "T" and round(box.y - yGap) or round(box.y + box.h + yGap)
    table.insert(candidates, 1, { p, { x = p.x, y = haloY }, { x = q.x, y = haloY }, q })
  end
  -- Retain an outer-face SP guide when a direct corridor meets another block.
  -- Reanchor its final lane to the native-clear face of the actual root card.
  if #guide.points >= 4 then
    local original = {}
    for i = 1, #guide.points do
      original[i] = { x = round(guide.points[i].x), y = round(guide.points[i].y) }
    end
    original[1] = { x = p.x, y = p.y }
    original[#original] = { x = q.x, y = q.y }
    if side == "L" or side == "R" then
      local lane = side == "L" and round(box.x - xGap) or round(box.x + box.w + xGap)
      original[#original - 1].x = lane
      original[#original - 1].y = q.y
      if #original >= 5 then
        original[#original - 2].x = lane
      end
    else
      local lane = side == "T" and round(box.y - yGap) or round(box.y + box.h + yGap)
      original[#original - 1].y = lane
      original[#original - 1].x = q.x
      if #original >= 5 then
        original[#original - 2].y = lane
      end
    end
    local bottomLane = round(maxBottom + yGap)
    local topLane = round(minTop - yGap)
    for i = 2, #original - 2 do
      if original[i].y > routeOptions.height - (routeOptions.cornerHalfH or 21) then
        original[i].y = bottomLane
      elseif original[i].y < (routeOptions.cornerHalfH or 21) then
        original[i].y = topLane
      end
    end
    candidates[#candidates + 1] = original
  end
  for i = 1, #candidates do
    local ok, path =
      projectedPathClear(candidates[i], "__PROMOTION_SOURCE__", root, buttons, routeOptions)
    if ok then
      local route = { parent = "__PROMOTION_SOURCE__", child = root, points = path }
      local clear = true
      for j = 1, #(reserved or {}) do
        local crossing, overlap = routeInteractions(route, reserved[j])
        if crossing > 0 or overlap > 0 then
          clear = false
          break
        end
      end
      if clear then
        return route
      end
    end
  end
  return nil
end

function PromotionLayoutProjectGuideCheck(guide, placement, geometry)
  local routeOptions = {}
  for k, v in pairs(geometry or {}) do
    routeOptions[k] = v
  end
  local factor = min(max(1, math.sqrt(placement.requiredAreaRatio or 1)), math.sqrt(1.5))
  routeOptions.width = (routeOptions.defaultW or routeOptions.viewportW or 1630) * factor
  routeOptions.height = (routeOptions.defaultH or routeOptions.viewportH or 1000) * factor
  local buttons = {}
  for i, card in ipairs(placement.buttons) do
    buttons[i] = { type = card.type, x = round(card.x), y = round(card.y) }
  end
  if guide.parent == "__PROMOTION_SOURCE__" then
    return projectSourceRoute(guide.child, guide, placement, buttons, routeOptions)
  end
  return projectGuideRoute(guide, placement, buttons, routeOptions)
end

-- Project a contracted series-parallel block drawing onto exact rank-card
-- ports. Successful native-safe paths are seeds; the guided router handles
-- the remaining edges without changing the block placement or edge meaning.
function PromotionLayoutProjectBlocks(graph, placement, embeddingOrGeometry, maybeGeometry)
  assert(
    type(PlanarPromotionBlockGuides) == "function",
    "PlanarPromotionBlockGuides must be loaded"
  )
  local embedding = maybeGeometry and embeddingOrGeometry or nil
  local geometry = maybeGeometry or embeddingOrGeometry
  local routeOptions = {}
  for k, v in pairs(geometry or {}) do
    routeOptions[k] = v
  end
  routeOptions.embedding = embedding
  local defaultW = routeOptions.defaultW or routeOptions.viewportW or 1630
  local defaultH = routeOptions.defaultH or routeOptions.viewportH or 1000
  local factor = max(1, math.sqrt(placement.requiredAreaRatio or 1))
  factor = min(factor, math.sqrt(1.5))
  routeOptions.width, routeOptions.height = defaultW * factor, defaultH * factor
  routeOptions.scale = 1 / factor
  routeOptions.sourcePoint =
    { x = round(placement.sourcePoint.x), y = round(placement.sourcePoint.y) }
  routeOptions.guideRoutes, routeOptions.seededRoutes = {}, {}
  local guides, rootGuides = PlanarPromotionBlockGuides(graph, placement)
  -- Contracted-grid placements may have fractional coordinates. All native
  -- controls and route ports snap to pixels, so every clearance check must
  -- use that same snapped card geometry.
  local buttons, buttonOf = {}, {}
  for i, card in ipairs(placement.buttons) do
    buttons[i] = { type = card.type, x = round(card.x), y = round(card.y) }
  end
  for i = 1, #buttons do
    buttonOf[buttons[i].type] = buttons[i]
  end
  local projected, reserved, projectionConflicts = 0, {}, {}
  -- Family links are direct and own their rank corridor before any branches.
  for _, child in ipairs(graph.order) do
    for _, parent in ipairs(graph.nodes[child].parents or {}) do
      if placement.member[parent] == placement.member[child] then
        local a, b = buttonOf[parent], buttonOf[child]
        local route
        if a.x + routeOptions.buttonW <= b.x then
          local y = round(a.y + routeOptions.buttonH / 2)
          route = {
            parent = parent,
            child = child,
            points = {
              { x = round(a.x + routeOptions.buttonW), y = y },
              { x = round(b.x), y = y },
            },
          }
        elseif b.x + routeOptions.buttonW <= a.x then
          local y = round(a.y + routeOptions.buttonH / 2)
          route = {
            parent = parent,
            child = child,
            points = {
              { x = round(a.x), y = y },
              { x = round(b.x + routeOptions.buttonW), y = y },
            },
          }
        elseif a.y + routeOptions.buttonH <= b.y then
          local x = round(a.x + routeOptions.buttonW / 2)
          route = {
            parent = parent,
            child = child,
            points = {
              { x = x, y = round(a.y + routeOptions.buttonH) },
              { x = x, y = round(b.y) },
            },
          }
        elseif b.y + routeOptions.buttonH <= a.y then
          local x = round(a.x + routeOptions.buttonW / 2)
          route = {
            parent = parent,
            child = child,
            points = {
              { x = x, y = round(a.y) },
              { x = x, y = round(b.y + routeOptions.buttonH) },
            },
          }
        end
        if route then
          routeOptions.seededRoutes[#routeOptions.seededRoutes + 1] = route
          reserved[#reserved + 1] = route
          projected = projected + 1
        end
      end
    end
  end
  local sources, failedSources = {}, {}
  for _, root in ipairs(graph.roots or {}) do
    local route = rootGuides[root]
      and projectSourceRoute(root, rootGuides[root], placement, buttons, routeOptions, reserved)
    local clear = route ~= nil
    if route then
      for i = 1, #reserved do
        local crossing, overlap = routeInteractions(route, reserved[i])
        if crossing > 0 or overlap > 0 then
          clear = false
          projectionConflicts[#projectionConflicts + 1] = "source -> "
            .. root
            .. " conflicts with "
            .. reserved[i].parent
            .. " -> "
            .. reserved[i].child
            .. " (cross="
            .. crossing
            .. ", overlap="
            .. overlap
            .. ")"
          break
        end
      end
    end
    if clear then
      sources[#sources + 1] = route
      reserved[#reserved + 1] = route
    else
      failedSources[#failedSources + 1] = root
    end
  end
  if #failedSources == 0 then
    routeOptions.sourceRoutes = sources
  end
  -- A projected external edge is a seed only when its complete route preserves
  -- the corridors already claimed by family links and the common source.
  for _, child in ipairs(graph.order) do
    for _, parent in ipairs(graph.nodes[child].parents or {}) do
      if placement.member[parent] ~= placement.member[child] then
        local key = edgeKey(parent, child)
        local guide = guides[key]
        local route = guide and projectGuideRoute(guide, placement, buttons, routeOptions, reserved)
        local clear = route ~= nil
        if not route and guide then
          projectionConflicts[#projectionConflicts + 1] = parent
            .. " -> "
            .. child
            .. " has no native-clear direct projection"
        end
        if route then
          for i = 1, #reserved do
            local crossing, overlap = routeInteractions(route, reserved[i])
            if crossing > 0 or overlap > 0 then
              clear = false
              projectionConflicts[#projectionConflicts + 1] = parent
                .. " -> "
                .. child
                .. " conflicts with "
                .. reserved[i].parent
                .. " -> "
                .. reserved[i].child
                .. " (cross="
                .. crossing
                .. ", overlap="
                .. overlap
                .. ")"
              break
            end
          end
        end
        if clear then
          routeOptions.seededRoutes[#routeOptions.seededRoutes + 1] = route
          reserved[#reserved + 1] = route
          projected = projected + 1
        elseif guide then
          routeOptions.guideRoutes[key] = guide
        end
      end
    end
  end
  if routeOptions.projectOnly then
    local edgeCount = 0
    for _, child in ipairs(graph.order) do
      edgeCount = edgeCount + #(graph.nodes[child].parents or {})
    end
    return {
      buttons = buttons,
      routes = routeOptions.seededRoutes,
      source = routeOptions.sourcePoint,
      sourceRoutes = sources,
      width = routeOptions.width,
      height = routeOptions.height,
      scale = routeOptions.scale,
      crossings = 0,
      violations = {},
      stats = {
        edges = edgeCount,
        routed = projected,
        roots = #(graph.roots or {}),
        projected = projected,
        projectedSource = #sources,
        projectConflicts = projectionConflicts,
        unprojected = edgeCount - projected,
        sourceFailures = failedSources,
      },
    }
  end
  local layout = PromotionLayoutRoute(graph, buttons, routeOptions)
  layout.stats.projected = projected
  layout.stats.projectedSource = #sources
  layout.stats.projectConflicts = projectionConflicts
  if (placement.requiredAreaRatio or 1) > 1.5 + 0.000001 then
    layout.violations[#layout.violations + 1] = "block placement exceeds proportional canvas cap"
  end
  if #failedSources > 0 then
    layout.violations[#layout.violations + 1] = "block source projection failed for "
      .. table.concat(failedSources, ", ")
  end
  return layout
end

-- A metric realization of the fixed orthogonal shape already knows which
-- exact promotion owns each endpoint. Keep those face routes intact, adding
-- only the direct internal links of contracted rank families.
function PromotionLayoutFromOrthogonalPlacement(graph, placement, geometry)
  local routeOptions = {}
  for k, v in pairs(geometry or {}) do
    routeOptions[k] = v
  end
  assert(routeOptions.buttonW and routeOptions.buttonH, "buttonW and buttonH required")
  local defaultW = routeOptions.defaultW or routeOptions.viewportW or 1630
  local defaultH = routeOptions.defaultH or routeOptions.viewportH or 1000
  local buttons, buttonOf, routes, sourceRoutes, violations = {}, {}, {}, {}, {}
  for _, card in ipairs(placement.buttons or {}) do
    local b = { type = card.type, x = round(card.x), y = round(card.y) }
    buttons[#buttons + 1], buttonOf[b.type] = b, b
  end
  local function directFamily(parent, child)
    local a, b = buttonOf[parent], buttonOf[child]
    if not a or not b then
      return nil
    end
    local w, h = routeOptions.buttonW, routeOptions.buttonH
    if a.x + w <= b.x and a.y == b.y then
      local y = round(a.y + h / 2)
      return { { x = a.x + w, y = y }, { x = b.x, y = y } }
    elseif b.x + w <= a.x and a.y == b.y then
      local y = round(a.y + h / 2)
      return { { x = a.x, y = y }, { x = b.x + w, y = y } }
    elseif a.y + h <= b.y and a.x == b.x then
      local x = round(a.x + w / 2)
      return { { x = x, y = a.y + h }, { x = x, y = b.y } }
    elseif b.y + h <= a.y and a.x == b.x then
      local x = round(a.x + w / 2)
      return { { x = x, y = a.y }, { x = x, y = b.y + h } }
    end
    return nil
  end
  local expected, found, familyLinks = {}, {}, {}
  for _, entry in ipairs(graph.chains or {}) do
    local family = entry.nodes or entry
    for i = 2, #family do
      familyLinks[edgeKey(family[i - 1], family[i])] = true
    end
  end
  for _, child in ipairs(graph.order) do
    for _, parent in ipairs(graph.nodes[child].parents or {}) do
      local key = edgeKey(parent, child)
      expected[key] = true
      if familyLinks[key] then
        local path = directFamily(parent, child)
        if path then
          routes[#routes + 1] = { parent = parent, child = child, points = path }
          found[key] = true
        else
          violations[#violations + 1] = "family link not straight: " .. parent .. " -> " .. child
        end
      end
    end
  end
  local source = placement.sourcePoint
      and { x = round(placement.sourcePoint.x), y = round(placement.sourcePoint.y) }
    or nil
  local roots = {}
  if graph.roots then
    for _, root in ipairs(graph.roots) do
      roots[root] = true
    end
  else
    for _, name in ipairs(graph.order) do
      if #(graph.nodes[name].parents or {}) == 0 then
        roots[name] = true
      end
    end
  end
  local function attached(point, name)
    local card = buttonOf[name]
    if not card or not point then
      return false
    end
    local left, right = card.x, card.x + routeOptions.buttonW
    local top, bottom = card.y, card.y + routeOptions.buttonH
    return ((point.x == left or point.x == right) and point.y >= top and point.y <= bottom)
      or ((point.y == top or point.y == bottom) and point.x >= left and point.x <= right)
  end
  local sourceFound = {}
  for _, record in
    ipairs((placement.abstract and placement.abstract.routes) or placement.routes or {})
  do
    local path = {}
    for _, point in ipairs(record.points or {}) do
      path[#path + 1] = { x = round(point.x), y = round(point.y) }
    end
    path = simplify(path)
    local route = {
      parent = record.parent,
      child = record.child,
      points = path,
      gaps = record.gaps,
    }
    if #path < 2 then
      violations[#violations + 1] = "shape route has fewer than two points: "
        .. tostring(record.parent)
        .. " -> "
        .. tostring(record.child)
    end
    if record.parent == "__PROMOTION_SOURCE__" then
      if roots[record.child] and not sourceFound[record.child] then
        sourceRoutes[#sourceRoutes + 1] = route
        sourceFound[record.child] = true
        if not source or not path[1] or path[1].x ~= source.x or path[1].y ~= source.y then
          violations[#violations + 1] = "source route has a different origin: " .. record.child
        end
        if not attached(path[#path], record.child) then
          violations[#violations + 1] = "source route misses root card: " .. record.child
        end
      else
        violations[#violations + 1] = "duplicate or invented source route: "
          .. tostring(record.child)
      end
    else
      local key = edgeKey(record.parent, record.child)
      if expected[key] and not found[key] then
        routes[#routes + 1] = route
        found[key] = true
        if not attached(path[1], record.parent) or not attached(path[#path], record.child) then
          violations[#violations + 1] = "shape route misses card boundary: "
            .. record.parent
            .. " -> "
            .. record.child
        end
      else
        violations[#violations + 1] = "duplicate or invented shape route: "
          .. tostring(record.parent)
          .. " -> "
          .. tostring(record.child)
      end
    end
  end
  for key in pairs(expected) do
    if not found[key] then
      violations[#violations + 1] = "missing shape route: " .. key
    end
  end
  for root in pairs(roots) do
    if not sourceFound[root] then
      violations[#violations + 1] = "missing shape source route: " .. root
    end
  end
  if not source then
    violations[#violations + 1] = "shape has no source point"
  end
  local requiredFactor = math.sqrt(max(1, placement.requiredAreaRatio or 1))
  for _, card in ipairs(buttons) do
    requiredFactor = max(
      requiredFactor,
      (card.x + routeOptions.buttonW) / defaultW,
      (card.y + routeOptions.buttonH) / defaultH
    )
  end
  for _, route in ipairs(routes) do
    for _, point in ipairs(route.points) do
      requiredFactor = max(requiredFactor, point.x / defaultW, point.y / defaultH)
    end
  end
  for _, route in ipairs(sourceRoutes) do
    for _, point in ipairs(route.points) do
      requiredFactor = max(requiredFactor, point.x / defaultW, point.y / defaultH)
    end
  end
  local factor = min(requiredFactor, math.sqrt(1.5))
  routeOptions.width, routeOptions.height = defaultW * factor, defaultH * factor
  routeOptions.scale = 1 / factor
  routeOptions.sourcePoint, routeOptions.sourceRoutes = source, sourceRoutes
  routeOptions.seededRoutes, routeOptions.maxRipups = routes, 0
  local result = PromotionLayoutRoute(graph, buttons, routeOptions)
  for _, reason in ipairs(violations) do
    result.violations[#result.violations + 1] = reason
  end
  result.stats.shapeRoutes = #routes
  result.stats.shapeSourceRoutes = #sourceRoutes
  return result
end

function PromotionLayoutScoreAssignment(graph, placement, embedding, geometry, assignment)
  local routeOptions = {}
  for k, v in pairs(geometry or {}) do
    routeOptions[k] = v
  end
  routeOptions.portAssignment = assignment
  routeOptions.projectOnly = true
  local layout = PromotionLayoutProjectBlocks(graph, placement, embedding, routeOptions)
  return layout.stats.projected, layout.stats.projectedSource, layout
end

return {
  solve = PromotionLayoutSolve,
  route = PromotionLayoutRoute,
  projectBlocks = PromotionLayoutProjectBlocks,
  fromOrthogonalPlacement = PromotionLayoutFromOrthogonalPlacement,
  projectGuideCheck = PromotionLayoutProjectGuideCheck,
  scoreAssignment = PromotionLayoutScoreAssignment,
}
