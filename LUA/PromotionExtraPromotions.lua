-- Promotions held by a selected unit that do not have a card in its displayed
-- promotion graph. The UI can use IconAtlas/PortraitIndex for the native icon
-- and Tooltip for the complete localized hover text.
--
-- PromotionExtraPromotions(unit, graph) returns an array sorted by localized
-- name, with Type as a stable tie-breaker. Each entry contains:
--   Type, ID, PortraitIndex, IconAtlas, Name, Help, Tooltip
function PromotionExtraPromotions(pUnit, graph)
  local result = {}
  if not pUnit or not pUnit.IsHasPromotion or not GameInfo or not GameInfo.UnitPromotions then
    return result
  end

  local graphNodes = graph and graph.nodes or {}
  local function localize(key)
    if key == nil then
      return ""
    end
    if Locale and Locale.ConvertTextKey then
      return Locale.ConvertTextKey(key)
    end
    return tostring(key)
  end

  for promotion in GameInfo.UnitPromotions() do
    if promotion.Type and not graphNodes[promotion.Type] and pUnit:IsHasPromotion(promotion.ID) then
      local name = localize(promotion.Description or promotion.Type)
      local help = localize(promotion.Help)
      local color = promotion.PortraitIndex == 57 and "[COLOR_RED]" or "[COLOR_YELLOW]"
      local tooltip = color .. name .. "[ENDCOLOR]"
      if help ~= "" then
        tooltip = tooltip .. ": " .. help
      end

      result[#result + 1] = {
        Type = promotion.Type,
        ID = promotion.ID,
        PortraitIndex = promotion.PortraitIndex,
        IconAtlas = promotion.IconAtlas,
        Name = name,
        Help = help,
        Tooltip = tooltip,
      }
    end
  end

  table.sort(result, function(a, b)
    if a.Name ~= b.Name then
      return a.Name < b.Name
    end
    return a.Type < b.Type
  end)
  return result
end
