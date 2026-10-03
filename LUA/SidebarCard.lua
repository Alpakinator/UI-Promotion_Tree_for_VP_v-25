-- Native Tw Cen MT glyph advances (ASCII 32..126) used only to choose line
-- breaks. The game still renders the original 18px/20px/24px font atlas itself.
local GLYPH_ADVANCES = {
  [18] = "0503061209151203050509110406040910090909100909090909040511111107181109101007071411030709071411140914090908101118100909050905080906091007090907090804040704110809100906060408081209090806090611",
  [20] = "0504071311171303050609120406051011111110111111101111050612121208201210121208081511040710081513161016100909121220111110051006091007111107111007110905050904140910111106070509091310100807110712",
  [24] = "0705081612211604060611170507051213141413131313141213050617171709241512151510101815060914091916181218121211141524131412071207111208131310131209131005051006161012131308080610111612121108140817",
}

local function measuredTextWidth(text, glyphAdvances)
  local total = 0
  for i = 1, #text do
    local byte = text:byte(i)
    local slot = (byte - 32) * 2 + 1
    total = total
      + (byte >= 32 and byte <= 126 and tonumber(glyphAdvances:sub(slot, slot + 1)) or 12)
  end
  return total
end

function SidebarClassDisplayName(name)
  if type(name) ~= "string" then
    return name
  end
  return (name:gsub("%s+—%s+", " "))
end

function SidebarCardWrapName(name, font, maxWidth)
  if type(name) ~= "string" then
    return name
  end
  local glyphAdvances = GLYPH_ADVANCES[font]
  if
    not glyphAdvances
    or type(maxWidth) ~= "number"
    or maxWidth <= 0
    or measuredTextWidth(name, glyphAdvances) <= maxWidth
  then
    return name
  end
  local lines, line = {}, ""
  for word in name:gmatch("%S+") do
    local candidate = line == "" and word or line .. " " .. word
    if line ~= "" and measuredTextWidth(candidate, glyphAdvances) > maxWidth then
      lines[#lines + 1] = line
      line = word
    else
      line = candidate
    end
  end
  if line ~= "" then
    lines[#lines + 1] = line
  end
  return table.concat(lines, "[NEWLINE]")
end

-- Resolve the representative unit's native flag atlas exactly as the original
-- mod did. Use its native 32px cell without resampling.
function SidebarClassFlag(unit)
  if not unit or not unit.UnitFlagAtlas or unit.UnitFlagIconOffset == nil then
    return nil
  end
  local offset = tonumber(unit.UnitFlagIconOffset)
  if not offset or offset < 0 then
    return nil
  end
  for row in
    DB.Query(
      "SELECT * FROM IconTextureAtlases WHERE Atlas = ? ORDER BY IconSize DESC",
      unit.UnitFlagAtlas
    )
  do
    local size = tonumber(row.IconSize)
    local columns, rows = tonumber(row.IconsPerRow), tonumber(row.IconsPerColumn)
    if
      size == 32
      and columns
      and columns > 0
      and rows
      and offset < columns * rows
      and row.Filename
    then
      local candidate = {
        texture = row.Filename,
        size = size,
        x = (offset % columns) * size,
        y = math.floor(offset / columns) * size,
      }
      return candidate
    end
  end
  return nil
end
