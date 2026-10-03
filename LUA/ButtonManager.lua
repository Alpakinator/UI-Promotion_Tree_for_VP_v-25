-- Explicit per-control scaling; resizing a Civ V parent does not scale children.
local instanceManager, iconSize, templateWidth, templateHeight, layoutScale, usesSmallCards
local CARD_WIDTH = 160
local WHITE = Color(1, 1, 1, 1)
local BLUE_FOCUSED = Color(0.22, 0.62, 1, 1)
local BLUE_NEIGHBOR = Color(0.34, 0.72, 1, 1)
local PULSE_FOCUSED = Color(0.30, 0.64, 1, 1)
local PULSE_NEIGHBOR = Color(0.40, 0.72, 1, 1)
local function pixel(v)
  return math.floor(v + 0.5)
end
local function setScaledWidthAndNativeHeight(control, width, height)
  if control then
    control:SetSizeVal(pixel(width * layoutScale), pixel(height))
  end
end
-- Advance widths from the game's TwCenMT18 glyph atlas, ASCII 32..126.
-- This is only used to choose a word break; the engine still draws the font.
local GLYPH_ADVANCES_16 =
  "0403061109141103040408110406040809090908090809080809040410111006161008101007071309030708061210130813070807091016090909040804080805090907090905090704040703110709090905060407071108080706090610"
local GLYPH_ADVANCES_18 =
  "0503061209151203050509110406040910090909100909090909040511111107181109101007071411030709071411140914090908101118100909050905080906091007090907090804040704110809100906060408081209090806090611"
local function textWidth(text, glyphAdvances)
  local width = 0
  for i = 1, #text do
    local code = text:byte(i)
    local offset = (code - 32) * 2 + 1
    width = width
      + (code >= 32 and code <= 126 and tonumber(glyphAdvances:sub(offset, offset + 1)) or 5)
  end
  return width
end
function ButtonManagerGetCardWidth()
  return CARD_WIDTH
end
function ButtonManagerDisplayName(name)
  if type(name) ~= "string" then
    return name
  end
  local width = CARD_WIDTH - (usesSmallCards and 48 + 5 or 58 + 2)
  local glyphAdvances = usesSmallCards and GLYPH_ADVANCES_16 or GLYPH_ADVANCES_18
  if textWidth(name, glyphAdvances) <= width then
    return name
  end
  local words = {}
  for word in name:gmatch("%S+") do
    words[#words + 1] = word
  end
  local best, balance
  for split = 1, #words - 1 do
    local left = table.concat(words, " ", 1, split)
    local right = table.concat(words, " ", split + 1)
    local leftWidth, rightWidth = textWidth(left, glyphAdvances), textWidth(right, glyphAdvances)
    if leftWidth <= width and rightWidth <= width then
      local difference = math.abs(leftWidth - rightWidth)
      if not balance or difference < balance then
        best, balance = left .. "[NEWLINE]" .. right, difference
      end
    end
  end
  return best or name
end
function ButtonManagerInit(instanceName, rootControl, parentControl)
  instanceManager = InstanceManager:new(instanceName, rootControl, parentControl)
  local instance = instanceManager:GetInstance()
  local dimensions = instance.ButtonBox:GetSize()
  templateWidth, templateHeight = dimensions.x, dimensions.y
  iconSize = instance.Portrait:GetSizeX()
  usesSmallCards = instanceName == "ButtonInstanceSmall"
  layoutScale = 1
  instanceManager:ResetInstances()
  return templateWidth, templateHeight
end
function ButtonManagerReset()
  if instanceManager then
    instanceManager:ResetInstances()
  end
end
function ButtonManagerSetScale(value)
  assert(
    type(value) == "number" and value >= 1 / math.sqrt(1.5) - 0.00001 and value <= 1,
    "Promotion scale exceeds the accepted area limit"
  )
  layoutScale = value
end
function ButtonManagerGetButton(x, y, tooltip, atlas, index, tech)
  local button = instanceManager:GetInstance()
  button._promotionHighlight = nil -- recycled controls have just been reinitialized
  -- Align the native portrait's centre with the routed card centre. A pipe
  -- entering at the logical left port then meets the round frame at its
  -- centre-left point even when only the card width is fitted.
  button.ButtonBox:SetOffsetVal(
    pixel(x + (templateWidth * layoutScale - CARD_WIDTH) / 2),
    pixel(y + (templateHeight * layoutScale - iconSize) / 2)
  )
  button.Button:SetOffsetVal(0, 0)
  local cardWidth = CARD_WIDTH
  -- Hide the rounded leading edge of every text panel beneath the flag.
  local bodyLeft = pixel(iconSize / 2) - 4
  local bodyWidth = math.max(1, cardWidth - bodyLeft)
  -- The native ring and the Grid9 styles have different transparent insets.
  -- Calibrate the gold/green fill and dark frame independently to the ring's
  -- visible top and bottom pixels; never resize the portrait itself.
  local unavailableHeight = usesSmallCards and 46 or 50
  local unavailableTop = usesSmallCards and -1 or 7
  local earnedHeight = usesSmallCards and 44 or 51
  -- Grid9Green8 has an 8px corner; Grid9Frame has a 16px corner. With their
  -- top edges equal, the green arc sticks 1–3px outside the gold arc. Inset
  -- only the fill's top by 2px and retain its bottom/right edges.
  local availableHeight = usesSmallCards and 41 or 49
  local earnedTop = usesSmallCards and -1 or 6
  local availableTop = earnedTop + 2
  for _, key in ipairs({ "ButtonBox", "Button" }) do
    button[key]:SetSizeVal(cardWidth, iconSize)
  end
  button.Earnt:SetSizeVal(bodyWidth, earnedHeight)
  button.Earnt:SetOffsetVal(bodyLeft, earnedTop)
  button.Available:SetSizeVal(bodyWidth, availableHeight)
  button.Available:SetOffsetVal(bodyLeft, availableTop)
  button.Unavailable:SetSizeVal(bodyWidth, unavailableHeight)
  button.Unavailable:SetOffsetVal(bodyLeft, unavailableTop)
  if button.EarnedShine then
    button.EarnedShine:SetSizeVal(bodyWidth, earnedHeight)
  end
  button.EarnedFrame:SetSizeVal(bodyWidth + 4, earnedHeight)
  button.EarnedHoverFrame:SetSizeVal(bodyWidth + 4, earnedHeight)
  -- The frame keeps its previous absolute top and bottom while the native
  -- green corner sits two pixels deeper within it.
  button.AvailableFrame:SetSizeVal(bodyWidth + 4, availableHeight + 4)
  button.UnavailableFrame:SetSizeVal(bodyWidth + 4, usesSmallCards and unavailableHeight or 53)
  button.AvailableFrame:SetOffsetVal(0, 0)
  -- Extend the large dark fill upward by two pixels, preserving the frame
  -- and label positions despite the changed parent centre.
  button.UnavailableFrame:SetOffsetVal(0, usesSmallCards and 0 or 1)
  for _, key in ipairs({ "EarnedFrame", "EarnedHoverFrame", "AvailableFrame", "UnavailableFrame" }) do
    button[key]:SetColor(WHITE)
  end
  button.EarnedFrame:SetHide(false)
  button.EarnedHoverFrame:SetHide(true)
  for _, spec in ipairs({
    { "Earnt", earnedHeight },
    { "Available", availableHeight },
    { "Unavailable", unavailableHeight },
  }) do
    local pulse = button[spec[1] .. "Pulse"]
    local fill = button[spec[1] .. "PulseFill"]
    pulse:SetOffsetVal(0, 2)
    pulse:SetSizeVal(bodyWidth, spec[2] - 5)
    fill:SetSizeVal(bodyWidth, spec[2] - 5)
    pulse:SetHide(true)
  end
  -- ScrollAnim keeps its original draw bounds after SetSizeVal in Civ V and
  -- paints past a fitted card. The Gold8 state already has its own sheen.
  if button.EarnedShine then
    button.EarnedShine:SetHide(true)
  end
  -- The visible ring occupies about 56px from the portrait's left edge;
  -- starting text at 58px leaves its shadow clear and preserves word space.
  local labelLeft = usesSmallCards and 48 or 58
  -- Civ V ships discrete font faces, not an arbitrary font-size setter.
  -- Keep the nearest readable native face and constrain its measured line width.
  local font = usesSmallCards and 16 or 18
  for _, kind in ipairs({ "Earnt", "Available", "Unavailable" }) do
    for _, suffix in ipairs({ "Name", "GlowName" }) do
      local label = button[kind .. suffix]
      if label then
        -- Insetting Available changes its centre by one pixel; keep the
        -- label on its original screen row.
        local labelOffsetY = (usesSmallCards and kind ~= "Unavailable" and 1 or 0)
          - (kind == "Available" and 1 or 0)
          + (not usesSmallCards and kind == "Unavailable" and 1 or 0)
        label:SetOffsetVal(labelLeft - bodyLeft, labelOffsetY)
        label:SetFontByName("TwCenMT" .. font)
        label:SetTruncateWidth(cardWidth - labelLeft - (usesSmallCards and 5 or 2))
        label:SetHide(suffix == "GlowName")
      end
    end
  end
  button.Button:SetToolTipString(tooltip)
  button.Button:ClearCallback(Mouse.eLClick)
  button.Button:SetVoid1(-1)
  local hooked = IconHookup(index, iconSize, atlas, button.Portrait) == true
  button.PortraitFrame:SetHide(not hooked)
  -- The original mod displays the available 45px/64px artwork at native
  -- size. Zoom affects placement, while the full card width and portrait
  -- remain fixed so every promotion uses the same line lengths and ports.
  button.PortraitFrame:SetSizeVal(iconSize, iconSize)
  button.PortraitFrame:SetAlpha(1)
  button.PortraitFrame:SetColor(WHITE)
  button.Portrait:SetSizeVal(iconSize, iconSize)
  button.Portrait:SetAlpha(1)
  button.Portrait:SetColor(WHITE)
  if tech and GameInfo.Technologies[tech] then
    button.ReqTech:SetHide(false)
    button.ReqTech:SetToolTipString(Locale.ConvertTextKey(GameInfo.Technologies[tech].Description))
  else
    button.ReqTech:SetHide(true)
  end
  setScaledWidthAndNativeHeight(button.ReqTech, 24, 24)
  -- The large portrait container extends below its text frame. Keep the
  -- native circular badge inside that frame, independent of tree fitting.
  button.ReqTech:SetOffsetVal(2, usesSmallCards and 8 or 14)
  button.ReqTech:SetFontByName("TwCenMT16")
  return button
end

function ButtonManagerSetHighlightState(button, state)
  button.highlightState = state
end

function ButtonManagerSetHighlight(button, highlighted, focused)
  -- This is the only writer of hover styling after GetButton initializes it.
  -- Most cards keep the same state when the pointer moves to a neighbor.
  local state = highlighted and (focused and 2 or 1) or 0
  if button._promotionHighlight == state then
    return
  end
  button._promotionHighlight = state
  local tint = highlighted and (focused and BLUE_FOCUSED or BLUE_NEIGHBOR) or WHITE
  for _, key in ipairs({ "EarnedHoverFrame", "AvailableFrame", "UnavailableFrame" }) do
    button[key]:SetColor(tint)
  end
  button.EarnedFrame:SetHide(highlighted)
  button.EarnedHoverFrame:SetHide(not highlighted)
  if button.PortraitFrame then
    button.PortraitFrame:SetColor(tint)
  end
  for _, kind in ipairs({ "Earnt", "Available", "Unavailable" }) do
    button[kind .. "Pulse"]:SetHide(not highlighted)
    button[kind .. "PulseFill"]:SetColor(focused and PULSE_FOCUSED or PULSE_NEIGHBOR)
    local normal = button[kind .. "Name"]
    local glow = button[kind .. "GlowName"]
    if normal and glow then
      normal:SetHide(highlighted)
      glow:SetHide(not highlighted)
    end
  end
end
