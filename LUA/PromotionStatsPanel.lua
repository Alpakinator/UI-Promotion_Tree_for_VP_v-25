-- Presentation only: never changes a unit or promotion ownership.
PromotionStatsPanel = {}
local function valueWithStatIcon(row)
  local value = row.value
  if not row.icon or type(value) ~= "string" then
    return value
  end
  local number, rest = value:match("^([+-]?%d+%.?%d*%%?)(.*)$")
  if number then
    return number .. " " .. row.icon .. rest
  end
  -- Conditional modifiers have no separate base value: place the glyph
  -- after their number, outside its color span; parentheses remain neutral.
  value = value:gsub("([+-]?%d+%.?%d*%%?)(%[ENDCOLOR%])(%))", function(amount, ending, closing)
    return amount .. ending .. " " .. row.icon .. closing
  end)
  return (
    value:gsub("([+-]?%d+%.?%d*%%?)(%))", function(amount, closing)
      return amount .. " " .. row.icon .. closing
    end)
  )
end

function PromotionStatsPanel.New(controls)
  local sectionManager = InstanceManager:new("UnitStatsSection", "Root", controls.UnitStatsStack)
  local collapsedSections, currentSections, boundSections = {}, {}, {}
  local viewportHeight = nil
  local panel = {}

  function panel:Render(nextSections)
    currentSections = nextSections or currentSections
    local visibleSectionCount, sectionOrderChanged = 0, false
    for _, section in ipairs(currentSections) do
      if #section.rows > 0 then
        visibleSectionCount = visibleSectionCount + 1
        if
          not boundSections[visibleSectionCount]
          or boundSections[visibleSectionCount].key ~= section.key
        then
          sectionOrderChanged = true
        end
      end
    end
    sectionOrderChanged = sectionOrderChanged or visibleSectionCount ~= #boundSections
    if sectionOrderChanged then
      sectionManager:ResetInstances()
      boundSections = {}
    end

    local scroll = controls.UnitStatsScroll:GetScrollValue() or 0
    local nextViewportHeight = controls.UnitStatsScroll:GetSizeY()
    local requiresLayout = sectionOrderChanged or viewportHeight ~= nextViewportHeight
    viewportHeight = nextViewportHeight
    local index = 0
    for _, section in ipairs(currentSections) do
      if #section.rows > 0 then
        index = index + 1
        local key = section.key
        local canCollapse = key ~= "core"
        local sectionState = boundSections[index]
        if not sectionState then
          sectionState = { key = key, controls = sectionManager:GetInstance() }
          boundSections[index] = sectionState
          sectionState.controls.Heading:RegisterCallback(Mouse.eLClick, function()
            if canCollapse then
              collapsedSections[key] = not collapsedSections[key]
              panel:Render()
            end
          end)
        end
        local sectionControls = sectionState.controls
        local header = (canCollapse and (collapsedSections[key] and "+ " or "− ") or "")
          .. section.title
        if sectionState.header ~= header then
          sectionControls.HeadingText:SetText(header)
          sectionState.header = header
        end
        local lines = {}
        for _, row in ipairs(section.rows) do
          local value = valueWithStatIcon(row)
          lines[#lines + 1] = row.label .. (value and value ~= "" and ": " .. value or "")
        end
        local body = table.concat(lines, "[NEWLINE]")
        if sectionState.body ~= body then
          sectionControls.Body:SetText(body)
          sectionState.body = body
        end
        local hidden = collapsedSections[key] == true
        if sectionState.hidden ~= hidden then
          sectionControls.Body:SetHide(hidden)
          sectionState.hidden = hidden
        end
        local sectionHeight = 28 + (hidden and 0 or sectionControls.Body:GetSizeY()) + 6
        if sectionState.height ~= sectionHeight then
          sectionControls.Root:SetSizeY(sectionHeight)
          sectionState.height = sectionHeight
          requiresLayout = true
        end
      end
    end
    -- Text with unchanged height needs no stack/scroll layout. This preserves
    -- native controls and callbacks across ordinary value-only hover updates.
    if requiresLayout then
      controls.UnitStatsStack:CalculateSize()
      controls.UnitStatsStack:ReprocessAnchoring()
      controls.UnitStatsScroll:CalculateInternalSize()
      controls.UnitStatsScroll:SetScrollValue(scroll)
    end
  end

  function panel:Reset()
    collapsedSections = {}
    controls.UnitStatsScroll:SetScrollValue(0)
  end
  return panel
end
