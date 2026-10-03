-- A lightweight, non-gameplay promotion planner for the combat-class view.
-- It uses the graph's explicit AND/OR prerequisite metadata; graph.parents is
-- only the union used for drawing and must not be treated as an AND clause.

PromotionClassPlanner = PromotionClassPlanner or {}

local Planner = PromotionClassPlanner

local function prerequisitesSatisfied(plan, promotionType, selected)
  local node = plan.nodes[promotionType]
  if not node then
    return false
  end

  -- PromotionPrereq is mandatory. Out-of-graph prerequisites count only when
  -- BuildPromotionGraph explicitly reports that its source (the class default
  -- unit or the inspected unit) already satisfies them.
  local required = node.requiredPrereq
  if required then
    if plan.inGraph[required] then
      if
        not selected[required]
        and not plan.granted[required]
        and not plan.externalSources[required]
      then
        return false
      end
    elseif not plan.externalSources[required] then
      return false
    end
  end

  -- PromotionPrereqOr1..9 form one alternative clause. Only known satisfied
  -- external source promotions satisfy an out-of-graph alternative.
  local alternatives = node.orPrereqs or {}
  if #alternatives == 0 then
    return true
  end
  for i = 1, #alternatives do
    local candidate = alternatives[i]
    if
      (plan.inGraph[candidate] and (selected[candidate] or plan.granted[candidate]))
      or plan.externalSources[candidate]
    then
      return true
    end
  end
  return false
end

function Planner.New(graph)
  graph = graph or { order = {}, nodes = {} }
  local plan = {
    graph = graph,
    order = graph.order or {},
    nodes = graph.nodes or {},
    externalSources = graph.externalSources or {},
    granted = graph.grantedPromotions or {},
    inGraph = {},
    selected = {},
    selectedCount = 0,
  }
  for i = 1, #plan.order do
    plan.inGraph[plan.order[i]] = true
  end
  return plan
end

function Planner.CanChoose(plan, promotionType)
  if
    not plan
    or plan.selected[promotionType]
    or plan.granted[promotionType]
    or not plan.inGraph[promotionType]
  then
    return false
  end
  return prerequisitesSatisfied(plan, promotionType, plan.selected)
end

-- Returns a state map containing exactly "selected", "available", or
-- "locked" for every card. The UI maps selected to earned/gold, available to
-- green, and locked to the dark default treatment.
function Planner.States(plan)
  local states = {}
  if not plan then
    return states
  end
  for i = 1, #plan.order do
    local promotionType = plan.order[i]
    if plan.granted[promotionType] or plan.selected[promotionType] then
      states[promotionType] = "selected"
    elseif prerequisitesSatisfied(plan, promotionType, plan.selected) then
      states[promotionType] = "available"
    else
      states[promotionType] = "locked"
    end
  end
  return states
end

-- Clicking a chosen prerequisite removes it and any selected promotions that
-- become illegal as a result. The fixed-point pass respects OR clauses: a
-- child remains selected if another selected alternative still satisfies it.
-- Returns (changed, removedTypes, reason).
function Planner.Toggle(plan, promotionType)
  if not plan or not plan.inGraph[promotionType] then
    return false, {}, "unknown promotion"
  end
  if plan.granted[promotionType] then
    return false, {}, "starting promotion"
  end

  if not plan.selected[promotionType] then
    if not Planner.CanChoose(plan, promotionType) then
      return false, {}, "promotion is not available"
    end
    plan.selected[promotionType] = true
    plan.selectedCount = plan.selectedCount + 1
    return true, { promotionType }
  end

  plan.selected[promotionType] = nil
  plan.selectedCount = plan.selectedCount - 1
  local removed = { promotionType }
  local changed = true
  while changed do
    changed = false
    for i = 1, #plan.order do
      local candidate = plan.order[i]
      if
        plan.selected[candidate] and not prerequisitesSatisfied(plan, candidate, plan.selected)
      then
        plan.selected[candidate] = nil
        plan.selectedCount = plan.selectedCount - 1
        removed[#removed + 1] = candidate
        changed = true
      end
    end
  end
  return true, removed
end

function Planner.Reset(plan)
  if not plan then
    return 0
  end
  plan.selected = {}
  plan.selectedCount = 0
  return 0
end

function Planner.SelectedCount(plan)
  return plan and plan.selectedCount or 0
end

-- Mirrors CvUnit::experienceNeeded in the Vox Populi DLL. For promotionCount
-- promotions from the initial level 1, the threshold is evaluated at level
-- promotionCount (0 promotions costs 0 XP; 1 costs one level threshold).
-- DLL order matters: player modifier rounds up first, game-speed scaling then
-- truncates to an integer.
function Planner.ExperienceRequired(promotionCount, baseXP, playerModifier, gameSpeedPercent)
  local count = math.max(0, math.floor(tonumber(promotionCount) or 0))
  if count == 0 then
    return 0
  end
  baseXP = tonumber(baseXP) or 10
  playerModifier = tonumber(playerModifier) or 0
  gameSpeedPercent = tonumber(gameSpeedPercent) or 100

  local multiplier = count * (count + 1) / 2
  local xp = baseXP * multiplier
  if playerModifier ~= 0 then
    xp = math.ceil(xp * (100 + playerModifier) / 100)
  end
  return math.floor(xp * gameSpeedPercent / 100)
end

local function readBaseXP()
  if GameDefines and tonumber(GameDefines.EXPERIENCE_PER_LEVEL) then
    return tonumber(GameDefines.EXPERIENCE_PER_LEVEL)
  end
  if DB and DB.Query then
    local ok, rows = pcall(function()
      return DB.Query("SELECT Value FROM GlobalDefines WHERE Name = 'EXPERIENCE_PER_LEVEL' LIMIT 1")
    end)
    if ok and rows then
      for row in rows do
        if tonumber(row.Value) then
          return tonumber(row.Value)
        end
      end
    end
  end
  return 10
end

-- Read the same live settings the DLL uses so the class estimate follows the
-- current game speed and player's level-XP modifier.
function Planner.ExperienceParameters(playerID)
  local parameters = { baseXP = readBaseXP(), playerModifier = 0, gameSpeedPercent = 100 }
  local activePlayerID = playerID
  if activePlayerID == nil and Game and Game.GetActivePlayer then
    activePlayerID = Game.GetActivePlayer()
  end
  local player = Players and activePlayerID ~= nil and Players[activePlayerID]
  if player and player.GetLevelExperienceModifier then
    local ok, value = pcall(player.GetLevelExperienceModifier, player)
    if ok and tonumber(value) then
      parameters.playerModifier = tonumber(value)
    end
  end

  local speedType = Game and Game.GetGameSpeedType and Game.GetGameSpeedType()
  local speed = speedType ~= nil
    and GameInfo
    and GameInfo.GameSpeeds
    and GameInfo.GameSpeeds[speedType]
  if speed and tonumber(speed.ExperiencePercent) then
    parameters.gameSpeedPercent = tonumber(speed.ExperiencePercent)
  end
  return parameters
end

function Planner.ExperienceForPlan(plan, playerID)
  local parameters = Planner.ExperienceParameters(playerID)
  return Planner.ExperienceRequired(
    Planner.SelectedCount(plan),
    parameters.baseXP,
    parameters.playerModifier,
    parameters.gameSpeedPercent
  )
end
