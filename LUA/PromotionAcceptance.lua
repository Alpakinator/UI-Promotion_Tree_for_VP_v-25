-- Independent acceptance gate for the final, logical promotion-tree geometry.
-- Routes are complete centre lines even where the renderer cuts underpass gaps.
-- All dimensions are logical canvas pixels; native shaded-pipe envelopes are
-- supplied through geometry. No Civ V globals or layout-solver internals are used.

local SOURCE = "__PROMOTION_SOURCE__"
local EPS = 0.0000001
local abs, min, max, sqrt = math.abs, math.min, math.max, math.sqrt

local function isFiniteNumber(v)
  return type(v) == "number" and v == v and abs(v) < math.huge
end

local function nearlyEqual(a, b)
  return abs(a - b) <= EPS
end
local function edgeKey(a, b)
  return a .. "\001" .. b
end
local function isFinitePoint(v)
  return type(v) == "table" and isFiniteNumber(v.x) and isFiniteNumber(v.y)
end
local function samePosition(a, b)
  return nearlyEqual(a.x, b.x) and nearlyEqual(a.y, b.y)
end
local function distance(a, b)
  local dx, dy = a.x - b.x, a.y - b.y
  return sqrt(dx * dx + dy * dy)
end
local function rectanglesOverlap(a, b, touching)
  if touching then
    return a.x0 <= b.x1 + EPS and b.x0 <= a.x1 + EPS and a.y0 <= b.y1 + EPS and b.y0 <= a.y1 + EPS
  end
  return a.x0 < b.x1 - EPS and b.x0 < a.x1 - EPS and a.y0 < b.y1 - EPS and b.y0 < a.y1 - EPS
end
local function expandRectangle(r, dx, dy)
  dy = dy or dx
  return { x0 = r.x0 - dx, y0 = r.y0 - dy, x1 = r.x1 + dx, y1 = r.y1 + dy }
end
local function onBoundary(p, r)
  return (
    p.x >= r.x0 - EPS
    and p.x <= r.x1 + EPS
    and (nearlyEqual(p.y, r.y0) or nearlyEqual(p.y, r.y1))
  )
    or (
      p.y >= r.y0 - EPS
      and p.y <= r.y1 + EPS
      and (nearlyEqual(p.x, r.x0) or nearlyEqual(p.x, r.x1))
    )
end

local function segment(a, b, routeIndex, index, start)
  local horizontal = nearlyEqual(a.y, b.y)
  return {
    a = a,
    b = b,
    route = routeIndex,
    index = index,
    start = start,
    horizontal = horizontal,
    length = abs(a.x - b.x) + abs(a.y - b.y),
    x0 = min(a.x, b.x),
    y0 = min(a.y, b.y),
    x1 = max(a.x, b.x),
    y1 = max(a.y, b.y),
  }
end
local function segmentContainsPoint(s, p)
  return p.x >= s.x0 - EPS
    and p.x <= s.x1 + EPS
    and p.y >= s.y0 - EPS
    and p.y <= s.y1 + EPS
    and (s.horizontal and nearlyEqual(p.y, s.a.y) or nearlyEqual(p.x, s.a.x))
end
local function distanceAlongRouteAt(s, p)
  return s.start + abs(p.x - s.a.x) + abs(p.y - s.a.y)
end
local function rectangleSeparation(a, b)
  local dx = max(a.x0 - b.x1, b.x0 - a.x1, 0)
  local dy = max(a.y0 - b.y1, b.y0 - a.y1, 0)
  return sqrt(dx * dx + dy * dy)
end

-- Closed segment/rectangle intersection as a normalized parameter interval.
local function segmentRectClip(s, r)
  local dx, dy = s.b.x - s.a.x, s.b.y - s.a.y
  local lo, hi = 0, 1
  local bounds =
    { { -dx, s.a.x - r.x0 }, { dx, r.x1 - s.a.x }, { -dy, s.a.y - r.y0 }, { dy, r.y1 - s.a.y } }
  for i = 1, #bounds do
    local p, q = bounds[i][1], bounds[i][2]
    if nearlyEqual(p, 0) then
      if q < -EPS then
        return nil
      end
    else
      local t = q / p
      if p < 0 then
        lo = max(lo, t)
      else
        hi = min(hi, t)
      end
      if lo > hi + EPS then
        return nil
      end
    end
  end
  return lo, hi
end

local function routePosition(route, d, backwards)
  local points = route.points
  local rem = d
  for i = 1, #points - 1 do
    local a, b
    if backwards then
      a, b = points[#points - i + 1], points[#points - i]
    else
      a, b = points[i], points[i + 1]
    end
    local length = abs(a.x - b.x) + abs(a.y - b.y)
    if length > EPS and rem <= length + EPS then
      local t = max(0, min(1, rem / length))
      return { x = a.x + t * (b.x - a.x), y = a.y + t * (b.y - a.y) }
    end
    rem = rem - length
  end
  return backwards and points[1] or points[#points]
end

local function sharedLength(a, b, backwards)
  local ap = backwards and a.points[#a.points] or a.points[1]
  local bp = backwards and b.points[#b.points] or b.points[1]
  if not samePosition(ap, bp) then
    return 0
  end
  local stop = min(a.total, b.total)
  local cuts, da, db = { stop }, 0, 0
  for i = 1, #a.points - 1 do
    local x, y
    if backwards then
      x, y = a.points[#a.points - i + 1], a.points[#a.points - i]
    else
      x, y = a.points[i], a.points[i + 1]
    end
    da = da + abs(x.x - y.x) + abs(x.y - y.y)
    if da <= stop + EPS then
      cuts[#cuts + 1] = da
    end
  end
  for i = 1, #b.points - 1 do
    local x, y
    if backwards then
      x, y = b.points[#b.points - i + 1], b.points[#b.points - i]
    else
      x, y = b.points[i], b.points[i + 1]
    end
    db = db + abs(x.x - y.x) + abs(x.y - y.y)
    if db <= stop + EPS then
      cuts[#cuts + 1] = db
    end
  end
  table.sort(cuts)
  local good = 0
  for i = 1, #cuts do
    local d = cuts[i]
    if d > good + EPS then
      if distance(routePosition(a, d, backwards), routePosition(b, d, backwards)) > EPS then
        break
      end
      good = d
    end
  end
  return good
end

local function sharedStroke(a, b, s, t, p, q, pre, suf)
  local sa0, sa1 = distanceAlongRouteAt(s, p), distanceAlongRouteAt(s, q)
  local sb0, sb1 = distanceAlongRouteAt(t, p), distanceAlongRouteAt(t, q)
  if sa0 > sa1 then
    sa0, sa1 = sa1, sa0
  end
  if sb0 > sb1 then
    sb0, sb1 = sb1, sb0
  end
  if
    a.parent == b.parent
    and sa1 <= pre + EPS
    and sb1 <= pre + EPS
    and nearlyEqual(sa0, sb0)
    and nearlyEqual(sa1, sb1)
  then
    return true
  end
  if
    a.child == b.child
    and a.total - sa0 <= suf + EPS
    and b.total - sb0 <= suf + EPS
    and nearlyEqual(a.total - sa0, b.total - sb0)
    and nearlyEqual(a.total - sa1, b.total - sb1)
  then
    return true
  end
  return false
end

local function joinPoints(a, b, pre, suf)
  local result = {}
  if a.parent == b.parent and samePosition(a.points[1], b.points[1]) then
    result[#result + 1] = routePosition(a, pre, false)
  end
  if a.child == b.child and samePosition(a.points[#a.points], b.points[#b.points]) then
    result[#result + 1] = routePosition(a, suf, true)
  end
  return result
end

local function contactNearJunction(a, b, join, reach)
  local samples = {}
  if a.horizontal == b.horizontal then
    local alo, ahi = a.horizontal and a.x0 or a.y0, a.horizontal and a.x1 or a.y1
    local blo, bhi = b.horizontal and b.x0 or b.y0, b.horizontal and b.x1 or b.y1
    local low, high = max(alo, blo), min(ahi, bhi)
    if low <= high + EPS then
      for _, v in ipairs({ low, high }) do
        local p = a.horizontal and { x = v, y = a.a.y } or { x = a.a.x, y = v }
        local q = b.horizontal and { x = v, y = b.a.y } or { x = b.a.x, y = v }
        samples[#samples + 1] = { p, q }
      end
    else
      local va, vb
      if ahi < blo then
        va, vb = ahi, blo
      else
        va, vb = alo, bhi
      end
      samples[1] = {
        a.horizontal and { x = va, y = a.a.y } or { x = a.a.x, y = va },
        b.horizontal and { x = vb, y = b.a.y } or { x = b.a.x, y = vb },
      }
    end
  else
    local h, v = a, b
    if not h.horizontal then
      h, v = b, a
    end
    samples[1] = {
      { x = min(max(v.a.x, h.x0), h.x1), y = h.a.y },
      { x = v.a.x, y = min(max(h.a.y, v.y0), v.y1) },
    }
  end
  for i = 1, #samples do
    if
      distance(samples[i][1], join) > reach + EPS or distance(samples[i][2], join) > reach + EPS
    then
      return false
    end
  end
  return true
end

-- A certificate names all nine internally vertex-disjoint paths of a K3,3
-- subdivision using real graph edges. A Boolean "nonplanar" flag is not proof.
local function isCertificateValid(cert, edges)
  if
    type(cert) ~= "table"
    or cert.kind ~= "k33_subdivision"
    or type(cert.left) ~= "table"
    or type(cert.right) ~= "table"
    or type(cert.paths) ~= "table"
    or #cert.left ~= 3
    or #cert.right ~= 3
    or #cert.paths ~= 9
  then
    return false
  end
  local branches, left, right = {}, {}, {}
  for i = 1, 3 do
    local a, b = cert.left[i], cert.right[i]
    if type(a) ~= "string" or type(b) ~= "string" or branches[a] or branches[b] or a == b then
      return false
    end
    branches[a], branches[b], left[a], right[b] = true, true, true, true
  end
  local undirected = {}
  for key, e in pairs(edges) do
    undirected[edgeKey(e.parent, e.child)] = true
    undirected[edgeKey(e.child, e.parent)] = true
  end
  local usedPairs, usedInner = {}, {}
  for i = 1, 9 do
    local path = cert.paths[i]
    if
      type(path) ~= "table"
      or type(path.nodes) ~= "table"
      or #path.nodes < 2
      or not left[path.from]
      or not right[path.to]
      or path.nodes[1] ~= path.from
      or path.nodes[#path.nodes] ~= path.to
    then
      return false
    end
    local pair = edgeKey(path.from, path.to)
    if usedPairs[pair] then
      return false
    end
    usedPairs[pair] = true
    local localSeen = {}
    for j = 1, #path.nodes do
      local name = path.nodes[j]
      if type(name) ~= "string" or localSeen[name] then
        return false
      end
      localSeen[name] = true
      if j > 1 and j < #path.nodes then
        if branches[name] or usedInner[name] then
          return false
        end
        usedInner[name] = true
      end
      if j > 1 and not undirected[edgeKey(path.nodes[j - 1], name)] then
        return false
      end
    end
  end
  for a in pairs(left) do
    for b in pairs(right) do
      if not usedPairs[edgeKey(a, b)] then
        return false
      end
    end
  end
  return true
end

function PromotionLayoutAccept(graph, layout, geometry)
  local issues = {}
  local function add(code, detail)
    if #issues < 256 then
      issues[#issues + 1] = { code = code, detail = detail }
    end
  end
  if
    type(graph) ~= "table"
    or type(layout) ~= "table"
    or type(geometry) ~= "table"
    or type(graph.nodes) ~= "table"
    or type(graph.roots) ~= "table"
    or type(graph.chains) ~= "table"
    or type(layout.buttons) ~= "table"
    or type(layout.routes) ~= "table"
    or type(layout.sourceRoutes) ~= "table"
  then
    add("schema", "graph, layout, buttons, routes, sourceRoutes and geometry are required")
    return false, issues
  end
  if graph.invalid then
    add("invalid_graph", "graph extraction reported invalid prerequisites")
  end
  if type(layout.violations) == "table" and #layout.violations > 0 then
    add("solver_violation", "layout solver reported " .. #layout.violations .. " violation(s)")
  end
  local cardWidth, cardHeight, pipeHalfWidth =
    geometry.buttonW, geometry.buttonH, geometry.pipeHalfWidth
  local width, height, scale = layout.width, layout.height, layout.scale
  local baseW, baseH =
    geometry.defaultW or geometry.baseWidth, geometry.defaultH or geometry.baseHeight
  local viewW, viewH = geometry.viewportW or baseW, geometry.viewportH or baseH
  if
    not (
      isFiniteNumber(cardWidth)
      and cardWidth > 0
      and isFiniteNumber(cardHeight)
      and cardHeight > 0
      and isFiniteNumber(pipeHalfWidth)
      and pipeHalfWidth > 0
      and isFiniteNumber(width)
      and width > 0
      and isFiniteNumber(height)
      and height > 0
      and isFiniteNumber(scale)
      and scale > 0
      and isFiniteNumber(baseW)
      and baseW > 0
      and isFiniteNumber(baseH)
      and baseH > 0
      and isFiniteNumber(viewW)
      and viewW > 0
      and isFiniteNumber(viewH)
      and viewH > 0
    )
  then
    add("schema", "finite positive button, pipe, canvas and scale dimensions are required")
    return false, issues
  end
  local cornerX, cornerY =
    geometry.cornerReachX or pipeHalfWidth, geometry.cornerReachY or pipeHalfWidth
  local joinReach = geometry.joinReach or max(cornerX, cornerY, 2 * pipeHalfWidth)
  local capReach = geometry.capReach or 0
  local openDistance = geometry.openSideDistance or cardHeight
  if
    not (
      isFiniteNumber(cornerX)
      and cornerX > 0
      and isFiniteNumber(cornerY)
      and cornerY > 0
      and isFiniteNumber(joinReach)
      and joinReach > 0
      and isFiniteNumber(capReach)
      and capReach >= 0
      and isFiniteNumber(openDistance)
      and openDistance > 0
    )
  then
    add("schema", "invalid native-art clearance dimensions")
    return false, issues
  end
  if width < baseW - EPS or height < baseH - EPS then
    add("canvas_shrink", "logical canvas is smaller than baseline")
  end
  if width * height > 1.5 * baseW * baseH + 0.000001 * baseW * baseH then
    add("canvas_area", "logical canvas exceeds 150% of baseline area")
  end
  if abs(width / baseW - height / baseH) > max(1 / baseW, 1 / baseH) + 0.000001 then
    add("canvas_aspect", "canvas aspect ratio changed")
  end
  local expectedScale = min(viewW / width, viewH / height)
  if abs(scale - expectedScale) > 0.002 then
    add("canvas_scale", "reported zoom differs from uniform fit scale")
  end

  local names, nodeSet, edges, indegree = {}, {}, {}, {}
  if type(graph.order) == "table" then
    for i = 1, #graph.order do
      if type(graph.order[i]) ~= "string" or graph.order[i] == "" then
        add("graph_schema", "graph order contains a non-promotion ID")
        return false, issues
      end
      names[i] = graph.order[i]
    end
  else
    for name in pairs(graph.nodes) do
      if type(name) ~= "string" or name == "" then
        add("graph_schema", "graph nodes contain a non-promotion ID")
        return false, issues
      end
      names[#names + 1] = name
    end
    table.sort(names)
  end
  for i = 1, #names do
    local name = names[i]
    if type(name) ~= "string" or not graph.nodes[name] or nodeSet[name] then
      add("duplicate_node", "invalid or repeated promotion in graph order")
    else
      nodeSet[name], indegree[name] = true, 0
    end
  end
  for name in pairs(graph.nodes) do
    if not nodeSet[name] then
      add("missing_graph_node", "graph order omits " .. tostring(name))
    end
  end
  for i = 1, #names do
    local child = names[i]
    local node = graph.nodes[child]
    if type(node) == "table" then
      if node.parents ~= nil and type(node.parents) ~= "table" then
        add("graph_schema", child .. " parents are not an array")
      else
        for _, parent in ipairs(node.parents or {}) do
          if type(parent) ~= "string" or not nodeSet[parent] then
            add("dangling_graph_edge", tostring(parent) .. " -> " .. child .. " lacks a graph node")
          else
            local key = edgeKey(parent, child)
            if edges[key] then
              add("duplicate_graph_edge", parent .. " -> " .. child)
            else
              edges[key] = { parent = parent, child = child }
              indegree[child] = indegree[child] + 1
            end
          end
        end
      end
    end
  end
  local roots, actualRoots = {}, {}
  for _, root in ipairs(graph.roots or {}) do
    if type(root) ~= "string" or not nodeSet[root] or roots[root] then
      add("invalid_root", tostring(root))
    else
      roots[root] = true
    end
  end
  for name in pairs(nodeSet) do
    if indegree[name] == 0 then
      actualRoots[name] = true
    end
  end
  for name in pairs(actualRoots) do
    if not roots[name] then
      add("root_mismatch", "missing graph root " .. name)
    end
  end
  for name in pairs(roots) do
    if not actualRoots[name] then
      add("root_mismatch", "extra graph root " .. tostring(name))
    end
  end
  local remaining, outgoing, queue, nodeCount = {}, {}, {}, 0
  for name in pairs(nodeSet) do
    remaining[name] = indegree[name]
    outgoing[name] = {}
    nodeCount = nodeCount + 1
    if remaining[name] == 0 then
      queue[#queue + 1] = name
    end
  end
  for _, e in pairs(edges) do
    outgoing[e.parent][#outgoing[e.parent] + 1] = e.child
  end
  local head, visited = 1, 0
  while head <= #queue do
    local name = queue[head]
    head = head + 1
    visited = visited + 1
    for _, child in ipairs(outgoing[name]) do
      remaining[child] = remaining[child] - 1
      if remaining[child] == 0 then
        queue[#queue + 1] = child
      end
    end
  end
  if visited ~= nodeCount then
    add("graph_cycle", "prerequisite graph contains a cycle")
  end

  local buttons = {}
  for i = 1, #layout.buttons do
    local b = layout.buttons[i]
    if
      type(b) ~= "table"
      or type(b.type) ~= "string"
      or b.type == ""
      or not isFiniteNumber(b.x)
      or not isFiniteNumber(b.y)
    then
      add("button_schema", "invalid promotion button " .. i)
    else
      if buttons[b.type] then
        add("duplicate_button", "duplicate card " .. b.type)
      end
      buttons[b.type] = { x0 = b.x, y0 = b.y, x1 = b.x + cardWidth, y1 = b.y + cardHeight }
      if
        b.x < -EPS
        or b.y < -EPS
        or b.x + cardWidth > width + EPS
        or b.y + cardHeight > height + EPS
      then
        add("button_outside_canvas", b.type)
      end
    end
  end
  for name in pairs(nodeSet) do
    if not buttons[name] then
      add("missing_button", name)
    end
  end
  for name in pairs(buttons) do
    if not nodeSet[name] then
      add("extra_button", name)
    end
  end
  for i = 1, #names do
    local a = buttons[names[i]]
    if a then
      for j = i + 1, #names do
        local b = buttons[names[j]]
        if b and rectanglesOverlap(a, b, true) then
          add("box_box", names[i] .. " and " .. names[j] .. " touch or overlap")
        end
      end
    end
  end
  local chainOwner = {}
  for chainIndex, chain in ipairs(graph.chains or {}) do
    if type(chain) ~= "table" or #chain < 2 then
      add("invalid_chain", "short family chain")
    else
      local validChain = true
      for i = 1, #chain do
        if type(chain[i]) ~= "string" or chain[i] == "" then
          validChain = false
        end
      end
      if not validChain then
        add("invalid_chain", "family chain contains a non-promotion ID")
      else
        local first = buttons[chain[1]]
        local row, col, forward, reverse = first ~= nil, first ~= nil, true, true
        local seen = {}
        for i = 1, #chain do
          if not nodeSet[chain[i]] or seen[chain[i]] then
            add("invalid_chain", "unknown or repeated rank in family")
          end
          if chainOwner[chain[i]] then
            add("overlapping_chains", tostring(chain[i]) .. " belongs to two families")
          end
          chainOwner[chain[i]] = chainIndex
          seen[chain[i]] = true
          local card = buttons[chain[i]]
          if card and first then
            row = row and nearlyEqual(card.y0, first.y0)
            col = col and nearlyEqual(card.x0, first.x0)
          else
            row, col = false, false
          end
          if i > 1 then
            if not edges[edgeKey(chain[i - 1], chain[i])] then
              add("chain_not_edge", chain[i - 1] .. " -> " .. chain[i])
            end
            local before = buttons[chain[i - 1]]
            if before and card then
              local d = row and card.x0 - before.x0 or card.y0 - before.y0
              if d <= EPS then
                forward = false
              end
              if d >= -EPS then
                reverse = false
              end
            end
          end
        end
        if not ((row or col) and (forward or reverse)) then
          add("chain_alignment", "family ranks are not on one ordered axis")
        else
          for i = 1, #chain - 1 do
            local a, b = buttons[chain[i]], buttons[chain[i + 1]]
            if a and b then
              local corridor
              if row then
                corridor = { x0 = min(a.x1, b.x1), x1 = max(a.x0, b.x0), y0 = a.y0, y1 = a.y1 }
              else
                corridor = { x0 = a.x0, x1 = a.x1, y0 = min(a.y1, b.y1), y1 = max(a.y0, b.y0) }
              end
              if corridor.x1 > corridor.x0 + EPS and corridor.y1 > corridor.y0 + EPS then
                for name, card in pairs(buttons) do
                  if not seen[name] and rectanglesOverlap(corridor, card, false) then
                    add("chain_intervening_card", name .. " between ranks")
                  end
                end
              end
            end
          end
        end
      end
    end
  end
  for name, r in pairs(buttons) do
    local blocked = {}
    for other, q in pairs(buttons) do
      if other ~= name then
        local vertical = min(q.y1, r.y1) - max(q.y0, r.y0) > EPS
        local horizontal = min(q.x1, r.x1) - max(q.x0, r.x0) > EPS
        if vertical and q.x0 >= r.x1 - EPS and q.x0 - r.x1 < openDistance - EPS then
          blocked.right = true
        end
        if vertical and q.x1 <= r.x0 + EPS and r.x0 - q.x1 < openDistance - EPS then
          blocked.left = true
        end
        if horizontal and q.y0 >= r.y1 - EPS and q.y0 - r.y1 < openDistance - EPS then
          blocked.bottom = true
        end
        if horizontal and q.y1 <= r.y0 + EPS and r.y0 - q.y1 < openDistance - EPS then
          blocked.top = true
        end
      end
    end
    if blocked.left and blocked.right and blocked.top and blocked.bottom then
      add("no_open_side", name .. " is enclosed on four sides")
    end
  end

  local source = layout.source
  if not isFinitePoint(source) then
    add("source_schema", "one finite common source point is required")
    return false, issues
  end
  if
    source.x < pipeHalfWidth - EPS
    or source.y < pipeHalfWidth - EPS
    or source.x > width - pipeHalfWidth + EPS
    or source.y > height - pipeHalfWidth + EPS
  then
    add("source_outside_canvas", "common source lacks native-art clearance")
  end
  local routes, routeSet, prereqSet, sourceSet = {}, {}, {}, {}
  local function ingest(raw, sourceRoute)
    for i = 1, #raw do
      local r = raw[i]
      if
        type(r) ~= "table"
        or type(r.parent) ~= "string"
        or r.parent == ""
        or type(r.child) ~= "string"
        or r.child == ""
        or r.parent == r.child
        or type(r.points) ~= "table"
        or #r.points < 2
      then
        add("route_schema", "route " .. i .. " has invalid endpoints or points")
      else
        local key = edgeKey(r.parent, r.child)
        if routeSet[key] then
          add("duplicate_route", r.parent .. " -> " .. r.child)
        end
        routeSet[key] = true
        if sourceRoute then
          sourceSet[key] = true
        else
          prereqSet[key] = true
        end
        local valid = true
        for j = 1, #r.points do
          if not isFinitePoint(r.points[j]) then
            valid = false
          end
        end
        if not valid then
          add("route_schema", "route " .. i .. " has a non-finite point")
        else
          local route = {
            parent = r.parent,
            child = r.child,
            points = r.points,
            gaps = r.gaps or {},
            segments = {},
            total = 0,
          }
          local index = #routes + 1
          for j = 1, #r.points - 1 do
            local a, b = r.points[j], r.points[j + 1]
            if samePosition(a, b) then
              add("zero_segment", r.parent .. " -> " .. r.child)
            elseif not (nearlyEqual(a.x, b.x) or nearlyEqual(a.y, b.y)) then
              add("diagonal_segment", r.parent .. " -> " .. r.child)
            else
              local s = segment(a, b, index, j, route.total)
              route.segments[#route.segments + 1] = s
              route.total = route.total + s.length
            end
          end
          for j = 1, #r.points do
            local p = r.points[j]
            if
              p.x < pipeHalfWidth - EPS
              or p.y < pipeHalfWidth - EPS
              or p.x > width - pipeHalfWidth + EPS
              or p.y > height - pipeHalfWidth + EPS
            then
              local attached = (j == 1 and buttons[r.parent] and onBoundary(p, buttons[r.parent]))
                or (j == #r.points and buttons[r.child] and onBoundary(p, buttons[r.child]))
              if not attached then
                add("pipe_outside_canvas", r.parent .. " -> " .. r.child)
              end
            end
          end
          if r.parent == SOURCE then
            if not samePosition(r.points[1], source) then
              add("source_port", "root feed does not begin at common source")
            end
          elseif buttons[r.parent] and not onBoundary(r.points[1], buttons[r.parent]) then
            add("source_port", r.parent .. " route begins away from parent boundary")
          end
          if buttons[r.child] and not onBoundary(r.points[#r.points], buttons[r.child]) then
            add("target_port", r.child .. " route ends away from card boundary")
          end
          routes[#routes + 1] = route
        end
      end
    end
  end
  ingest(layout.routes, false)
  ingest(layout.sourceRoutes, true)
  for key, e in pairs(edges) do
    if not prereqSet[key] then
      add("missing_route", e.parent .. " -> " .. e.child)
    end
  end
  for key in pairs(prereqSet) do
    if not edges[key] then
      add("invented_route", "route has no prerequisite edge")
    end
  end
  for root in pairs(roots) do
    if not sourceSet[edgeKey(SOURCE, root)] then
      add("missing_source_route", root)
    end
  end
  for key in pairs(sourceSet) do
    local okay = false
    for root in pairs(roots) do
      if key == edgeKey(SOURCE, root) then
        okay = true
      end
    end
    if not okay then
      add("invented_source_route", "source route does not lead to a root")
    end
  end

  for i = 1, #routes do
    local r = routes[i]
    for j = 1, #r.segments do
      local s = r.segments[j]
      for k = j + 1, #r.segments do
        local t = r.segments[k]
        if t.index == s.index + 1 then
          if s.horizontal == t.horizontal and rectangleSeparation(s, t) <= EPS then
            local lo, hi
            if s.horizontal then
              lo, hi = max(s.x0, t.x0), min(s.x1, t.x1)
            else
              lo, hi = max(s.y0, t.y0), min(s.y1, t.y1)
            end
            if hi > lo + EPS then
              add("self_backtrack", r.parent .. " -> " .. r.child)
            end
          end
        elseif rectangleSeparation(s, t) <= 2 * pipeHalfWidth + EPS then
          add("self_pipe_art", r.parent .. " -> " .. r.child)
        end
      end
      for name, card in pairs(buttons) do
        local lo, hi = segmentRectClip(s, card)
        if lo then
          local ownStart = name == r.parent and s.index == 1 and hi <= EPS
          local ownEnd = name == r.child and s.index == #r.points - 1 and lo >= 1 - EPS
          if not ownStart and not ownEnd then
            add("pipe_through_card", r.parent .. " -> " .. r.child .. " through " .. name)
          end
        end
        local attached = (name == r.parent and s.index == 1)
          or (name == r.child and s.index == #r.points - 1)
        if not attached and segmentRectClip(s, expandRectangle(card, pipeHalfWidth)) then
          add("pipe_card_art", r.parent .. " -> " .. r.child .. " near " .. name)
        end
      end
    end
    for j = 2, #r.points - 1 do
      local p, a, b = r.points[j], r.points[j - 1], r.points[j + 1]
      if nearlyEqual(a.x, p.x) ~= nearlyEqual(p.x, b.x) then
        local art =
          { x0 = p.x - cornerX, y0 = p.y - cornerY, x1 = p.x + cornerX, y1 = p.y + cornerY }
        for name, card in pairs(buttons) do
          if rectanglesOverlap(art, card, true) then
            add("corner_card_art", r.parent .. " -> " .. r.child .. " near " .. name)
          end
        end
        local pipeArt = expandRectangle(art, pipeHalfWidth)
        for _, s in ipairs(r.segments) do
          if s.index ~= j - 1 and s.index ~= j and segmentRectClip(s, pipeArt) then
            add("self_corner_pipe_art", r.parent .. " -> " .. r.child)
            break
          end
        end
      end
    end
  end

  local crossings = {}
  for i = 1, #routes do
    for j = i + 1, #routes do
      local a, b = routes[i], routes[j]
      local pre = a.parent == b.parent and sharedLength(a, b, false) or 0
      local suf = a.child == b.child and sharedLength(a, b, true) or 0
      local joins = joinPoints(a, b, pre, suf)
      local function nearJoin(s, t)
        for k = 1, #joins do
          if contactNearJunction(s, t, joins[k], joinReach) then
            return true
          end
        end
        return false
      end
      for _, s in ipairs(a.segments) do
        for _, t in ipairs(b.segments) do
          if rectangleSeparation(s, t) <= 2 * pipeHalfWidth + EPS then
            if s.horizontal == t.horizontal then
              local lo, hi
              if s.horizontal then
                lo, hi = max(s.x0, t.x0), min(s.x1, t.x1)
              else
                lo, hi = max(s.y0, t.y0), min(s.y1, t.y1)
              end
              local sep = s.horizontal and abs(s.a.y - t.a.y) or abs(s.a.x - t.a.x)
              if hi >= lo - EPS and sep <= EPS then
                local p = s.horizontal and { x = lo, y = s.a.y } or { x = s.a.x, y = lo }
                local q = s.horizontal and { x = hi, y = s.a.y } or { x = s.a.x, y = hi }
                if not sharedStroke(a, b, s, t, p, q, pre, suf) then
                  add(
                    hi > lo + EPS and "unrelated_collinear_overlap" or "false_junction",
                    a.parent .. " -> " .. a.child .. " with " .. b.parent .. " -> " .. b.child
                  )
                end
              elseif not nearJoin(s, t) then
                add(
                  "near_pipe",
                  a.parent .. " -> " .. a.child .. " near " .. b.parent .. " -> " .. b.child
                )
              end
            else
              local h, v = s, t
              if not h.horizontal then
                h, v = t, s
              end
              local p = { x = v.a.x, y = h.a.y }
              if segmentContainsPoint(h, p) and segmentContainsPoint(v, p) then
                local hInterior = not samePosition(p, h.a) and not samePosition(p, h.b)
                local vInterior = not samePosition(p, v.a) and not samePosition(p, v.b)
                if hInterior and vInterior then
                  crossings[#crossings + 1] = { x = p.x, y = p.y, first = i, second = j }
                elseif not sharedStroke(a, b, s, t, p, p, pre, suf) then
                  add(
                    "false_junction",
                    a.parent .. " -> " .. a.child .. " with " .. b.parent .. " -> " .. b.child
                  )
                end
              elseif not nearJoin(s, t) then
                add(
                  "near_pipe",
                  a.parent .. " -> " .. a.child .. " near " .. b.parent .. " -> " .. b.child
                )
              end
            end
          end
        end
      end
      -- Native elbow artwork has a larger footprint than the straight centerline.
      for _, pair in ipairs({ { a, b }, { b, a } }) do
        local owner, other = pair[1], pair[2]
        for at = 2, #owner.points - 1 do
          local p, before, after = owner.points[at], owner.points[at - 1], owner.points[at + 1]
          if nearlyEqual(before.x, p.x) ~= nearlyEqual(p.x, after.x) then
            local footprint = {
              x0 = p.x - cornerX - pipeHalfWidth,
              y0 = p.y - cornerY - pipeHalfWidth,
              x1 = p.x + cornerX + pipeHalfWidth,
              y1 = p.y + cornerY + pipeHalfWidth,
            }
            local hit = false
            for _, s in ipairs(other.segments) do
              if segmentRectClip(s, footprint) then
                hit = true
                break
              end
            end
            if hit then
              local ownerDist = 0
              for k = 1, at - 1 do
                local q, r = owner.points[k], owner.points[k + 1]
                ownerDist = ownerDist + abs(q.x - r.x) + abs(q.y - r.y)
              end
              local sharedSource = a.parent == b.parent and ownerDist <= pre + EPS
              local sharedTarget = a.child == b.child and owner.total - ownerDist <= suf + EPS
              local commonJoin = false
              for k = 1, #joins do
                if distance(p, joins[k]) <= joinReach + EPS then
                  for _, s in ipairs(other.segments) do
                    if segmentContainsPoint(s, joins[k]) then
                      commonJoin = true
                      break
                    end
                  end
                end
              end
              if not (sharedSource or sharedTarget or commonJoin) then
                add(
                  "corner_pipe_art",
                  owner.parent .. " -> " .. owner.child .. " near another route"
                )
              end
            end
          end
        end
      end
    end
  end
  if layout.crossings ~= nil and layout.crossings ~= #crossings then
    add("crossing_count", "reported crossing count differs from logical geometry")
  end
  local cert = layout.nonplanarCertificate
    or graph.nonplanarCertificate
    or geometry.nonplanarCertificate
  -- A reviewed readability tradeoff is separate from topological necessity.
  -- The caller supplies its explicit budget; a candidate cannot grant itself one.
  local budget = geometry.readabilityCrossingBudget or 0
  if type(budget) ~= "number" or budget < 0 or budget % 1 ~= 0 or budget == math.huge then
    add("crossing_budget", "readability crossing budget must be a nonnegative integer")
    budget = 0
  end
  local provedNonplanar = isCertificateValid(cert, edges)
  if
    not provedNonplanar
    and type(cert) == "table"
    and cert.kind == "lr_nonplanar"
    and type(PromotionPlanarEmbedding) == "function"
  then
    local _, _, status = PromotionPlanarEmbedding(graph, false)
    provedNonplanar = status == "nonplanar"
  end
  if #crossings > budget and not provedNonplanar then
    add(
      "unproven_crossing",
      #crossings
        .. " logical crossing(s) exceed the readability budget and lack a valid certificate"
    )
  end
  local records = layout.underpasses or {}
  if type(records) ~= "table" then
    add("underpass_schema", "underpasses must be an array")
    records = {}
  end
  local usedRecords, usedGaps = {}, {}
  for _, crossing in ipairs(crossings) do
    local a, b = routes[crossing.first], routes[crossing.second]
    local matches = {}
    for k = 1, #records do
      local rec = records[k]
      if
        type(rec) == "table"
        and type(rec.under) == "table"
        and type(rec.over) == "table"
        and isFiniteNumber(rec.x)
        and isFiniteNumber(rec.y)
        and type(rec.under.parent) == "string"
        and type(rec.under.child) == "string"
        and type(rec.over.parent) == "string"
        and type(rec.over.child) == "string"
        and nearlyEqual(rec.x, crossing.x)
        and nearlyEqual(rec.y, crossing.y)
      then
        local under = edgeKey(rec.under.parent, rec.under.child)
        local over = edgeKey(rec.over.parent, rec.over.child)
        local ka, kb = edgeKey(a.parent, a.child), edgeKey(b.parent, b.child)
        if (under == ka and over == kb) or (under == kb and over == ka) then
          matches[#matches + 1] =
            { record = k, under = under == ka and crossing.first or crossing.second }
        end
      end
    end
    if #matches ~= 1 then
      add("missing_underpass", "crossing needs exactly one matching underpass record")
    else
      local matched = matches[1]
      usedRecords[matched.record] = true
      local route = routes[matched.under]
      local pointAtCross = { x = crossing.x, y = crossing.y }
      local found = false
      if type(route.gaps) == "table" then
        for k = 1, #route.gaps do
          local gap = route.gaps[k]
          if
            type(gap) == "table"
            and isFiniteNumber(gap.segment)
            and isFiniteNumber(gap.from)
            and isFiniteNumber(gap.to)
            and gap.to > gap.from + EPS
          then
            for _, s in ipairs(route.segments) do
              if s.index == gap.segment and segmentContainsPoint(s, pointAtCross) then
                local localD = distanceAlongRouteAt(s, pointAtCross) - s.start
                if
                  gap.from <= localD - (pipeHalfWidth + capReach) + EPS
                  and localD + (pipeHalfWidth + capReach) <= gap.to + EPS
                then
                  found = true
                  usedGaps[matched.under .. ":" .. k] = true
                end
              end
            end
          end
        end
      end
      if not found then
        add("missing_gap", "under-route gap does not clear crossing artwork")
      end
    end
  end
  for k = 1, #records do
    if not usedRecords[k] then
      add("extra_underpass", "record has no logical crossing")
    end
  end
  for i = 1, #routes do
    local r = routes[i]
    if type(r.gaps) ~= "table" then
      add("gap_schema", "route gaps must be an array")
    else
      for k = 1, #r.gaps do
        local gap = r.gaps[k]
        local s = type(gap) == "table" and r.segments[gap.segment or 0] or nil
        if
          not (
            s
            and isFiniteNumber(gap.from)
            and isFiniteNumber(gap.to)
            and gap.from >= -EPS
            and gap.to <= s.length + EPS
            and gap.to > gap.from + EPS
          )
        then
          add("gap_schema", "gap lies outside its one-based route segment")
        elseif not usedGaps[i .. ":" .. k] then
          add("extra_gap", "gap has no recorded crossing")
        end
      end
    end
  end
  return #issues == 0, issues
end
