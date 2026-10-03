-- One-edge neighbors for promotion-tree hover. The graph comes from the same
-- prerequisite data as the routes, including alternative prerequisite edges.
function PromotionHoverRelated(graph, promotionType)
  local nodes = graph and graph.nodes or {}
  if not nodes[promotionType] then
    return {}
  end
  local related = { [promotionType] = true }
  for _, direction in ipairs({ "parents", "children" }) do
    for _, neighbor in ipairs(nodes[promotionType][direction] or {}) do
      if nodes[neighbor] then
        related[neighbor] = true
      end
    end
  end
  return related
end
