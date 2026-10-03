-- Small native-control helpers shared by the tree UI.
function SetWidth(control, width)
  control:SetSizeX(width)
end

function SetHeight(control, height)
  control:SetSizeY(height)
end

function OffsetAgain(control)
  -- Retain the native reanchoring workaround: setting the same offset alone
  -- does not always dirty a resized control's layout in Civ V.
  local x, y = control:GetOffsetVal()
  control:SetOffsetVal(x + 10, y + 10)
  control:SetOffsetVal(x, y)
end
