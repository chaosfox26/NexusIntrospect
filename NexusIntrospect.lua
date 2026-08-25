-----------------------------------------------------------------------------------------------
-- NexusIntrospect  —  Copyright (c) 2026 chaosfox26 (Nexus Unleashed).  ALL RIGHTS RESERVED.
--
-- PROPRIETARY AND CONFIDENTIAL. This addon is NOT open source and is NOT covered by the MIT
-- license that applies to the NexusUnleashed engine. It is an original, independently authored
-- work. No license is granted to copy, modify, distribute, sublicense, reverse-engineer, or
-- create derivative works, in whole or in part, without the express prior written permission of
-- the copyright holder. Bundled with the NexusUnleashed server for use ON Nexus Unleashed realms
-- only; all other rights are reserved.
-----------------------------------------------------------------------------------------------
-- NexusIntrospect
--
-- Asks the client what it knows, so nothing has to be guessed or taken from a wiki scrape that may
-- be several patches off 16042. The client shipped WITH 16042: where it and any other source
-- disagree, the client is right by definition.
--
-- READ ONLY. It reads names and values. It calls nothing it finds and changes nothing.
--
--   /nuintro          summary of what has been captured
--   /nuintro api      enumerate namespaces, Unit methods and enum tables
--   /nuintro events   which event names were observed being registered
--   /nuability        this character's spell list, points, spec, innate abilities
--   /nuamp            every Eldan Augmentation the client knows
--   /nutier           tier level requirements, and every tier of every ability
--   /nuitem <text>    search every item by name, via the client
--   /nunear [radius]  every unit near you and its activation state - why a prop is not interactive
--   /nucalc [label]   WHAT THE GAME ITSELF CALCULATES: every stat as value/rating/percent,
--                     which is the client rating conversion with softcaps included, plus the
--                     damage it computes from them. Accumulates across runs - label each one.
--   /nucalc diff A B  the scaling itself: (dDamage / dAssaultPower) per ability, computed from two
--                     labelled captures. No table lookup - the level term cancels in the subtraction.
--   /nustat           the combat stat block - Assault/Support Power and the rest. The tooltip
--                     damage numbers are computed FROM these, so they are meaningless without it.
--   /nuui [filter]    every library and function the client exposes, walked from _G rather than a
--                     hand-kept list, with anything save-shaped tagged. Plus every addon and
--                     whether it has OnSave at all. This is the client half of "why didn't it
--                     save" - M7's unhandled-packet log is the server half.
--   /nuall [radius] [text]
--                     all of the above, staggered, plus telemetry watch and the sprint probe.
--                     A leading number is the nearby-scan radius, 1 to 3000; the rest is the item
--                     search. "/nuall 3000 hoverboard" does both.
--   /reloadui         flush everything to disk for monitor M11
--
-- Rewritten clean after six rounds of string patching left it failing to load entirely - every
-- slash command reported "unknown command". A file assembled by repeated search-and-replace reads
-- fine at a glance and stops working, which is its own lesson: past a couple of edits, rewrite.
-----------------------------------------------------------------------------------------------

require "Window"
require "GameLib"
require "Apollo"

local NexusIntrospect = {}
local PREFIX = "NUINTRO"

-- The API scan, the enum dump and the UI map describe the BUILD, not the character. They are byte for
-- byte the same on every character - and SavedVariables are per character, so every new character was
-- re-capturing and re-serialising all three from scratch. Measured on a 954 KB save: enums 196 KB, api
-- 118 KB, ui 95 KB - 409 KB, 43% of the file, identical to the copy already captured and committed.
--
-- That cost is paid on every /reloadui, which is what made reloads take a visible minute while rolling
-- one character per class.
--
-- Set true to capture them again - after a client patch, or if the committed copy is lost. Nothing else
-- changes: abilities, AMPs, tiers and everything else per-character are unaffected.
local CAPTURE_BUILD_INVARIANT = false

-- Every call into the client is wrapped: an accessor absent on this build must return nil, never
-- take the addon down. A dead addon reports nothing at all.
local function Try(fn, ...)
    if type(fn) ~= "function" then return nil end
    local ok, res = pcall(fn, ...)
    if ok then return res end
    return nil
end

-- Scan radius, held to 1..3000. Below 1 sweeps nothing at all.
--
-- The ceiling is a guard against a number that reads wider than it measures, NOT a claim that 3000
-- units are visible. The sweep can only report units the client has been told about, so past the
-- client's own tracking distance a larger radius returns an identical set while looking like a
-- broader search. Raised from 1500 on request; if a 3000 sweep ever returns the same count as a
-- 1500 one from the same spot, that ceiling is above the real limit and the number is decoration.
--
-- Declared HERE, at the top, and not beside the nearby-scan code that mostly uses it: EnableAll is
-- defined earlier in this file, and a local declared after a function is not in that function's
-- lexical scope - it would resolve as a nil global and blow up only when someone typed /nuall 500.
local function Clamp(n)
    n = tonumber(n) or 30
    if n < 1 then return 1 end
    if n > 3000 then return 3000 end
    return math.floor(n)
end

-- Does this object actually have that method, asked without calling it. Try() cannot answer this:
-- it collapses "no such method" and "method returned nil" into the same nil, and those two are a
-- probe bug and a server bug respectively.
--
-- Declared UP HERE with the other helpers, not beside the nearby-scan code that first needed it.
-- It was originally defined at the bottom of the file and CollectStats - defined hundreds of lines
-- earlier - referenced it, which in Lua resolves to a nil global and fails only when the command is
-- actually typed. That is the second time this exact mistake was made in this file; helpers belong
-- at the top, without exception.
local function Has(obj, sName)
    local ok, fn = pcall(function() return obj[sName] end)
    return (ok and type(fn) == "function") or false
end

-- ---------------------------------------------------------------------------------------------
-- THE 202. Which entries in the ability book are actually class abilities.
--
-- Settled 2026-08-14 against 18 Action Set Builder screenshots (all 3 tabs, all 6 classes) plus the
-- player naming the ones no screenshot shows:
--
--     202 = 192 tiered (32 per class, identical for all six) + 10 class innates
--     Warrior 34  Engineer 34  Stalker 35  Medic 33  Esper 33  Spellslinger 33
--
-- The discriminator is TIER COUNT, not name and not id. Across all 220 captured rows the values are
-- exactly 9 (192 rows) and 1 (28 rows) with nothing in between, so `#tTiers == 9` separates real
-- class abilities from basic attacks, Punch, mounts and toggles with no judgement call.
--
-- A rule beats a hardcoded id list here: it cannot go stale against a table edit, and it SELF-CHECKS
-- - any class that does not yield exactly 32 means the rule or the capture is wrong, and /nuscale
-- cover says so out loud instead of quietly exporting 31.
--
-- The innates are the exception and must be named, because seven of them are tier-1 entries that the
-- rule above deliberately excludes, and THREE are not returned by AbilityBook.GetAbilitiesList at
-- all. Those three cannot be recovered from the ability list by any rule whatsoever; they are listed
-- so their absence is reported as a known gap rather than looking like a complete capture.
--
-- I reported the class ability count as 220, then 208, then 192 before this settled. Every one of
-- those came from counting rows the API returned and calling them abilities.
-- ---------------------------------------------------------------------------------------------
local CLASS_TIER_COUNT = 9

local CLASS_INNATE_NAMES = {
    ["Stance: Onslaught"]  = "warrior",
    ["Stance: Juggernaut"] = "warrior",
    ["Mode: Provoke"]      = "engineer",
    ["Mode: Eradicate"]    = "engineer",
    ["Nano Skin: Lethal"]  = "stalker",
    ["Nano Skin: Evasive"] = "stalker",
    ["Nano Skin: Agile"]   = "stalker",
    -- these three are NOT returned by GetAbilitiesList on any character captured so far
    ["Energize"]           = "medic",
    ["Spectral Form"]      = "esper",
    ["Spell Surge"]        = "spellslinger",
}

-- AbilityBook.GetAbilitiesList takes an eSpellType (Spell.CodeEnumSpellTag). This addon called it
-- with NO argument for its whole life, which returns one default slice - and three class innates
-- (Medic Energize, Esper Spectral Form, Spellslinger Spell Surge) never appeared in any capture.
-- That was recorded as "the API does not return them", which was true of the CALL BEING MADE and not
-- necessarily true of the API.
--
-- Found by checking every namespace call this addon makes against the client's own Lua API reference
-- (docs/reference-data/apollo-api-surface.tsv): four AbilityBook names it calls are not in that
-- surface at all. That is the Apollo.GetAddons mistake, repeated four more times and undetected for
-- the same reason - a call that returns nil is indistinguishable from a thing that is not there.
--
-- So: union across every tag, keyed by ability id. If those three innates are reachable from Lua at
-- all they are reachable here, and if they still do not appear then that is a far stronger finding
-- than the one it replaces.
local function AllAbilities()
    local byId, order = {}, {}
    local function absorb(list)
        if type(list) ~= "table" then return end
        for _, a in ipairs(list) do
            local id = a.nId or a.nSpellId
            if id ~= nil and byId[id] == nil then
                byId[id] = a
                order[#order + 1] = id
            end
        end
    end

    absorb(Try(AbilityBook.GetAbilitiesList))          -- the historical no-arg call, kept so nothing is lost

    local tags = Try(function() return Spell.CodeEnumSpellTag end)
    if type(tags) == "table" then
        for _, v in pairs(tags) do
            if type(v) == "number" then
                absorb(Try(AbilityBook.GetAbilitiesList, v))
            end
        end
    end

    local out = {}
    for _, id in ipairs(order) do out[#out + 1] = byId[id] end
    return out
end

-- returns: isClassAbility, kind ("tiered" | "innate" | nil)
local function ClassAbilityKind(nTiers, sName)
    if nTiers == CLASS_TIER_COUNT then return true, "tiered" end
    if sName ~= nil and CLASS_INNATE_NAMES[sName] ~= nil then return true, "innate" end
    return false, nil
end

-- Flatten any value to k=v pairs so an unknown shape still yields its contents. The field names on
-- 16042 are not known in advance, and dropping what was not expected is how data goes missing.
--
-- Descends TWO levels and handles USERDATA, not just tables. The earlier version stopped at one
-- level and ignored userdata entirely, so a nested spell object or tooltip - exactly where an AMP's
-- name and power cost are likely to live - was silently absent. An absent field reads as "this data
-- does not exist" rather than "this reader did not look".
local function Flat(v, depth)
    depth = depth or 0
    local tv = type(v)

    if tv == "string" or tv == "number" or tv == "boolean" then return tostring(v) end
    if v == nil then return "" end

    -- userdata: ask it the usual questions rather than skipping it
    if tv == "userdata" then
        local bits = {}
        -- GetFlavor is DEPRECATED on 16042 and complains loudly - the client says to use GetTooltips.
        -- Probing an accessor by name is cheap, but probing a deprecated one is not free: it produced
        -- a visible Lua error mid-capture. Only current names belong in this list.
        for _, getter in ipairs({ "GetName", "GetId", "GetTooltips" }) do
            local ok, fn = pcall(function() return v[getter] end)
            if ok and type(fn) == "function" then
                local ok2, res = pcall(fn, v)
                if ok2 and res ~= nil and res ~= "" then
                    table.insert(bits, getter:gsub("^Get", "") .. "=" .. tostring(res))
                end
            end
        end
        return (#bits > 0) and ("<" .. table.concat(bits, " ") .. ">") or "<userdata>"
    end

    if tv ~= "table" then return "<" .. tv .. ">" end
    if depth > 2 then return "{...}" end

    local bits = {}
    pcall(function()
        for k, val in pairs(v) do
            local t2 = type(val)
            if t2 == "string" or t2 == "number" or t2 == "boolean" then
                table.insert(bits, tostring(k) .. "=" .. tostring(val))
            elseif t2 == "userdata" or t2 == "table" then
                local inner = Flat(val, depth + 1)
                if inner ~= "" and inner ~= "{...}" then
                    table.insert(bits, tostring(k) .. "{" .. inner .. "}")
                end
            end
        end
    end)
    table.sort(bits)
    return table.concat(bits, " ")
end

function NexusIntrospect:new(o)
    o = o or {}
    setmetatable(o, self)
    self.__index = self
    return o
end

function NexusIntrospect:Init()
    Apollo.RegisterAddon(self, false, "", {})
end

function NexusIntrospect:OnSave(eLevel)
    -- Save at ACCOUNT level: our realm currently sends a blank realm name, so the client can't
    -- build the per-CHARACTER save path (it needs account/realm/char) and character-level saves
    -- silently vanish. Account-level persists here. Revert to Character once the realm-name bug is fixed.
    local ok, want = pcall(function() return GameLib.CodeEnumAddonSaveLevel.Account end)
    if ok and want ~= nil and eLevel ~= want then return nil end
    return {
        version   = 2,
        -- omitted unless CAPTURE_BUILD_INVARIANT: 43% of the save, identical on every character
        api       = CAPTURE_BUILD_INVARIANT and (self.tApi or {}) or nil,
        enums     = CAPTURE_BUILD_INVARIANT and (self.tEnums or {}) or nil,
        events    = self.tSeenEvents or {},
        addons    = self.tAddons or {},
        catalog   = self.tCatalog or {},
        snaps     = self.tSnaps or {},
        abilities = self.tAbilities or {},
        amps      = self.tAmps or {},
        tiers     = self.tTiers or {},
        near      = self.tNear or {},
        stats     = self.tStats or {},
        calc      = self.tCalc or {},
        scale     = self.tScale or {},
        scaled    = self.tScaleSolved or {},
        apideep   = self.tApiDeep or {},
        ui        = CAPTURE_BUILD_INVARIANT and (self.tUi or {}) or nil,
    }
end

function NexusIntrospect:OnRestore(eLevel, tData)
    if type(tData) ~= "table" then return end
    self.tApi        = tData.api or {}
    self.tEnums      = tData.enums or {}
    self.tSeenEvents = tData.events or {}
    self.tAddons     = tData.addons or {}
    self.tCatalog    = tData.catalog or {}
    self.tSnaps      = tData.snaps or {}
    self.tAbilities  = tData.abilities or {}
    self.tAmps       = tData.amps or {}
    self.tTiers      = tData.tiers or {}
    self.tNear       = tData.near or {}
    self.tStats      = tData.stats or {}
    self.tCalc       = tData.calc or {}
    -- kept across reloads on purpose: the whole method is comparing captures taken minutes apart
    -- with a stat change and a /reloadui in between, so dropping them at load would erase the
    -- baseline every time the player reloaded to write the next one.
    self.tScale      = tData.scale or {}
    self.tScaleSolved = tData.scaled or {}
    self.tApiDeep    = tData.apideep or {}
    self.tUi         = tData.ui or {}
end

function NexusIntrospect:OnLoad()
    self.tApi        = self.tApi or {}
    self.tEnums      = self.tEnums or {}
    self.tSeenEvents = self.tSeenEvents or {}
    self.tAddons     = self.tAddons or {}
    self.tCatalog    = self.tCatalog or {}
    self.tSnaps      = self.tSnaps or {}
    self.tAbilities  = self.tAbilities or {}
    self.tAmps       = self.tAmps or {}
    self.tTiers      = self.tTiers or {}
    self.tNear       = self.tNear or {}
    self.tStats      = self.tStats or {}
    self.tCalc       = self.tCalc or {}
    self.tScale      = self.tScale or {}
    self.tScaleSolved = self.tScaleSolved or {}
    self.tApiDeep    = self.tApiDeep or {}
    self.tUi         = self.tUi or {}

    -- live units are NOT restored: a unit handle from a previous session is a dangling reference,
    -- and a stale handle answers questions with old data rather than failing, which is worse
    self.tLiveUnits  = {}

    Apollo.RegisterEventHandler("UnitCreated",   "OnUnitCreated",   self)
    Apollo.RegisterEventHandler("UnitDestroyed", "OnUnitDestroyed", self)

    Apollo.RegisterSlashCommand("nucalc",     "OnCalcSlash",    self)
    Apollo.RegisterSlashCommand("nuscale",    "OnScaleSlash",   self)
    Apollo.RegisterSlashCommand("nuapi",      "OnApiSlash",     self)
    Apollo.RegisterSlashCommand("nustat",     "OnStatSlash",    self)
    Apollo.RegisterSlashCommand("nuui",       "OnUiSlash",      self)
    Apollo.RegisterSlashCommand("nunear",     "OnNearSlash",    self)
    Apollo.RegisterSlashCommand("nuintro",   "OnSlash",        self)
    Apollo.RegisterSlashCommand("nuability", "OnAbilitySlash", self)
    Apollo.RegisterSlashCommand("nuamp",     "OnAmpSlash",     self)
    Apollo.RegisterSlashCommand("nutier",    "OnTierSlash",    self)
    Apollo.RegisterSlashCommand("nuitem",    "OnItemSlash",    self)
    Apollo.RegisterSlashCommand("nuall",     "OnAllSlash",     self)
    Apollo.RegisterSlashCommand("nusnap",    "OnSnapSlash",    self)

    self:HookEvents()

    Print(PREFIX .. " loaded. /nuall to capture everything, /reloadui to send it.")
end

-- Record every event name anything registers for. Whatever the stock UI registers exists on this
-- build by definition, which turns guessed handler names into a verified list.
--
-- Guarded by a GLOBAL flag rather than instance state: /reloadui builds a new instance, and without
-- this the wrapper wraps the previous wrapper, one layer deeper on every reload.
function NexusIntrospect:HookEvents()
    if _G.__NuIntroHooked then return end

    local original = Apollo.RegisterEventHandler
    if type(original) ~= "function" then return end

    local seen = self.tSeenEvents
    Apollo.RegisterEventHandler = function(sEvent, sFunction, tAddon, ...)
        if type(sEvent) == "string" then seen[sEvent] = (seen[sEvent] or 0) + 1 end
        return original(sEvent, sFunction, tAddon, ...)
    end

    _G.__NuIntroHooked = true
end

function NexusIntrospect:Count(t)
    local n = 0
    for _ in pairs(t or {}) do n = n + 1 end
    return n
end

-----------------------------------------------------------------------------------------------
-- API surface
-----------------------------------------------------------------------------------------------

local NAMESPACES = {
    "GameLib", "Apollo", "ChatSystemLib", "Unit", "Item", "Spell", "Quest",
    "AbilityBook", "ActionSetLib", "CombatFloater", "CraftingLib", "GroupLib",
    "HousingLib", "MatchingGame", "PlayerPathLib", "Money", "Sound", "Tooltip",
    "AccountItemLib", "AchievementsLib", "AttributeMilestonesLib", "BankLib",
    "ChallengesLib", "CommunicatorLib", "CSIsLib", "DatacubeLib", "FriendshipLib",
    "GuildLib", "MailSystemLib", "MarketplaceLib", "PetCustomizationLib",
    "PublicEventsLib", "QuestLib", "RewardTrackLib", "StorefrontLib", "TradeskillLib",
}

function NexusIntrospect:Enumerate(sName, tbl, bValues)
    if type(tbl) ~= "table" then return end

    local fns, vals = {}, {}
    pcall(function()
        for k, v in pairs(tbl) do
            local key, tv = tostring(k), type(v)
            if tv == "function" then
                table.insert(fns, key)
            elseif bValues and (tv == "number" or tv == "string") then
                table.insert(vals, key .. "=" .. tostring(v))
            elseif tv == "table" then
                local sub = {}
                pcall(function()
                    for k2, v2 in pairs(v) do
                        if type(v2) == "number" or type(v2) == "string" then
                            table.insert(sub, tostring(k2) .. "=" .. tostring(v2))
                        end
                    end
                end)
                if #sub > 0 then
                    table.sort(sub)
                    self.tEnums[sName .. "." .. key] = sub
                end
            end
        end
    end)

    table.sort(fns)
    table.sort(vals)
    self.tApi[sName] = { functions = fns, values = vals }
end

function NexusIntrospect:ScanApi()
    self.tApi, self.tEnums = {}, {}

    -- walking 112 namespaces to then discard the result is pure cost on every reload
    if not CAPTURE_BUILD_INVARIANT then
        Print(PREFIX .. " api/enums skipped - build-invariant, already captured (see CAPTURE_BUILD_INVARIANT)")
        return
    end

    for _, name in ipairs(NAMESPACES) do
        local tbl = _G[name]
        if tbl ~= nil then self:Enumerate(name, tbl, true) end
    end

    -- instance methods live on the metatable, which is where the real Unit surface is
    local unit = Try(GameLib.GetPlayerUnit)
    if unit then
        local mt = getmetatable(unit)
        if mt and type(mt.__index) == "table" then
            self:Enumerate("UnitInstance", mt.__index, false)
        end
    end

    -- Apollo.GetAddons DOES NOT EXIST on 16042 - see the note in DumpUi. This list was silently
    -- empty every run since it was written and still counted as captured. /nuui does the real
    -- enumeration now; this records honestly that it is not the place to look.
    self.tAddons = { "see UIADDON rows from /nuui - Apollo.GetAddons does not exist on this build" }
end

-----------------------------------------------------------------------------------------------
-- abilities, amps, tiers
-----------------------------------------------------------------------------------------------


-- ---------------------------------------------------------------------------------------------
-- /nustat - the character's combat stat block.
--
-- WHY THIS EXISTS. The tier and ability captures carry the client's own damage numbers - "Deals 129
-- physical damage", "1PP: 764 dmg". Those are NOT constants. The client computes them from the
-- character's Assault Power and Support Power, so a tooltip figure is a number with no denominator
-- unless the stats that produced it are captured at the same moment.
--
-- Every accessor below was read from the client's own Unit metatable by /nuui, not guessed. Anything
-- absent on this build returns nil through Try and is simply skipped.
--
-- Paired with DumpAbilities on purpose: a damage number and the stats behind it belong in the same
-- capture, because a stat block taken minutes later describes a different character.
-- ---------------------------------------------------------------------------------------------

local STAT_ACCESSORS = {
    "GetAssaultPower", "GetSupportPower", "GetAssaultRating", "GetSupportRating",
    "GetAssaultAndSupportPowerSoftcap", "GetLevel", "GetEffectiveItemLevel",
    "GetHealth", "GetMaxHealth", "GetShieldCapacity", "GetShieldCapacityMax",
    "GetCritChance", "GetCritRating", "GetCritRatingPercent",
    "GetCritSeverity", "GetCritSeverityRating", "GetCritSeverityRatingPercent",
    "GetCriticalMitigation", "GetCriticalMitigationRating",
    "GetArmorPierce", "GetArmorPierceRating", "GetArmorPierceRatingPercent",
    "GetStrikethroughChance", "GetStrikethroughRating", "GetStrikethroughRatingPercent",
    "GetDeflectChance", "GetDeflectRating", "GetDeflectCritChance", "GetDeflectCritRating",
    "GetMultiHitChance", "GetMultiHitAmount", "GetMultiHitRating", "GetMultiHitAmountRating",
    "GetPhysicalMitigationRating", "GetTechMitigationRating", "GetMagicMitigationRating",
    "GetPhysicalMitigationRatingPercent", "GetTechMitigationRatingPercent",
    "GetMagicMitigationRatingPercent",
    "GetGlanceRating", "GetGlanceAmountRating", "GetIntensityRating", "GetVigor", "GetVigorRating",
    "GetLifestealRating", "GetDamageReflectChance", "GetDamageReflectAmount",
    "GetInterruptArmorValue", "GetInterruptArmorMax", "GetIgnoreShieldBase",
    "GetShieldMitigationPct", "GetShieldRegenPct",
    "GetPvPOffenseRating", "GetPvPDefenseRating", "GetPvPDamageI", "GetPvPDamageO",
}

-- =============================================================================================
-- /nuapi - the whole Apollo surface, walked rather than listed.
--
-- ScanApi iterates NAMESPACES, a hand-written list of 112 names. Such a list can only ever find what
-- somebody already knew to name, and it has failed in exactly that way before: this addon called
-- Apollo.GetAddons for weeks, recorded zero addons every run, and counted it as a capture - because
-- a name in a list is indistinguishable from a name that exists.
--
-- So this walks _G itself and reports what it finds AGAINST that list. Anything in the "unlisted"
-- column is API the project did not know it had.
--
-- Three surfaces, and only the first is reachable from _G:
--
--   1. NAMESPACE tables   GameLib, AbilityBook, ... - globals holding functions
--   2. INSTANCE methods   live on an object's metatable, not in any global. The Unit surface (95
--                         stat accessors) is here, and so is every Item, Spell and Window method.
--                         Invisible unless you hold an instance and read its metatable.
--   3. ENUM tables        nested tables of constants - the values every API argument expects
--
-- debug.getinfo is tried for parameter counts. Where it is unavailable the row says `sig=unknown`
-- rather than defaulting to zero: "takes no arguments" and "could not tell" are opposite facts, and
-- a confidently wrong signature is worse than an absent one.
-- =============================================================================================
function NexusIntrospect:DumpApi(sFilter)
    sFilter = (sFilter ~= nil and sFilter ~= "") and tostring(sFilter):lower() or nil

    local out  = {}
    local seen = {}                 -- table identity -> path, so a shared table is not walked twice
    local nFns, nTables, nEnumVals, nInstance = 0, 0, 0, 0

    local known = {}
    for _, n in ipairs(NAMESPACES or {}) do known[n] = true end

    local function Signature(fn)
        local info = Try(function()
            if debug == nil or debug.getinfo == nil then return nil end
            return debug.getinfo(fn, "u")
        end)
        if info == nil then return "sig=unknown" end
        return string.format("params=%s vararg=%s", tostring(info.nparams), tostring(info.isvararg))
    end

    local function Walk(sPath, tbl, depth)
        if type(tbl) ~= "table" or depth > 2 then return end
        if seen[tbl] then return end
        seen[tbl] = sPath

        local fns, enums, subs = {}, {}, {}
        pcall(function()
            for k, v in pairs(tbl) do
                local key = tostring(k)
                local tv  = type(v)
                if tv == "function" then
                    fns[#fns + 1] = key .. " " .. Signature(v)
                elseif tv == "number" or tv == "string" or tv == "boolean" then
                    enums[#enums + 1] = key .. "=" .. tostring(v)
                elseif tv == "table" then
                    subs[#subs + 1] = { key, v }
                end
            end
        end)

        table.sort(fns)
        table.sort(enums)

        if #fns > 0 or #enums > 0 then
            nTables   = nTables + 1
            nFns      = nFns + #fns
            nEnumVals = nEnumVals + #enums
            for _, f in ipairs(fns) do
                out[#out + 1] = string.format("APIFN|%s|%s", sPath, f)
            end
            -- enum values on ONE row per table: a 300-value enum as 300 rows drowns the save file
            if #enums > 0 then
                out[#out + 1] = string.format("APIENUM|%s|%s", sPath, table.concat(enums, " "))
            end
        end

        for _, pair in ipairs(subs) do
            Walk(sPath .. "." .. pair[1], pair[2], depth + 1)
        end
    end

    -- surfaces 1 and 3: everything reachable from the global table
    local roots = {}
    pcall(function()
        for k, v in pairs(_G) do
            if type(v) == "table" and tostring(k) ~= "_G" then roots[#roots + 1] = tostring(k) end
        end
    end)
    table.sort(roots)

    local nUnlisted = 0
    for _, name in ipairs(roots) do
        if sFilter == nil or name:lower():find(sFilter, 1, true) then
            if not known[name] then
                nUnlisted = nUnlisted + 1
                out[#out + 1] = string.format("APIUNLISTED|%s|not in the hand-written NAMESPACES list", name)
            end
            Walk(name, _G[name], 1)
        end
    end

    -- surface 2: instance metatables. Each probe is a live object obtained from the API; its methods
    -- exist nowhere in _G. Where an object cannot be obtained the row says so - an empty surface and
    -- an unobtainable object are different findings and must not read the same.
    local probes = {
        { "Unit",   function() return Try(GameLib.GetPlayerUnit) end },
        { "Target", function() return Try(GameLib.GetTargetUnit) end },
        { "Spell",  function()
                local l = Try(AbilityBook.GetAbilitiesList)
                if type(l) == "table" and l[1] and l[1].tTiers and l[1].tTiers[1] then
                    return l[1].tTiers[1].splObject
                end
                return nil
            end },
        { "Item",   function()
                local u = Try(GameLib.GetPlayerUnit)
                if u == nil then return nil end
                local inv = Try(u.GetInventoryItems, u)
                if type(inv) == "table" and inv[1] then return inv[1].itemInBag end
                return nil
            end },
        { "Window", function() return Try(Apollo.FindWindowByName, "NexusIntrospectProbe") end },
        { "XmlDoc", function() return Try(XmlDoc.CreateFromTable, { "Form" }) end },
        -- GetAllEpisodes/GetEpisode, not GetActiveQuests - the latter was my own invention and would
        -- have reported "no instance available" forever while looking like the quest surface HAD
        -- been checked. Exactly the failure this whole pass was written to find, committed by me
        -- an hour after writing the tool that finds it.
        { "Quest",  function()
                local eps = Try(QuestLib.GetAllEpisodes)
                if type(eps) ~= "table" then return nil end
                for _, ep in ipairs(eps) do
                    local qs = Try(ep.GetAllQuests, ep)
                    if type(qs) == "table" and qs[1] then return qs[1] end
                end
                return nil
            end },
    }

    for _, p in ipairs(probes) do
        if sFilter == nil or p[1]:lower():find(sFilter, 1, true) then
            local obj = p[2]()
            if obj == nil then
                out[#out + 1] = string.format("APIPROBE|%s|no instance available right now - surface NOT read", p[1])
            else
                local mt  = Try(getmetatable, obj)
                local idx = (type(mt) == "table") and mt.__index or nil
                if type(idx) == "table" then
                    local before = nFns
                    Walk(p[1] .. "Instance", idx, 1)
                    nInstance = nInstance + (nFns - before)
                    out[#out + 1] = string.format("APIPROBE|%s|instance surface read from metatable", p[1])
                else
                    -- userdata behind a C __index: the methods exist but cannot be enumerated from
                    -- Lua. Recorded, because reporting "no methods" here would simply be false.
                    out[#out + 1] = string.format("APIPROBE|%s|__index is %s, not enumerable from Lua",
                        p[1], type(idx))
                end
            end
        end
    end

    self.tApiDeep = out

    Print(string.format("%s api: %d functions across %d tables, %d enum values, %d instance methods",
        PREFIX, nFns, nTables, nEnumVals, nInstance))
    Print(string.format("%s      %d global tables walked, %d NOT in the hand-written list",
        PREFIX, #roots, nUnlisted))
    Print(PREFIX .. " /reloadui to write it. /nuapi <filter> narrows to matching names.")
end

function NexusIntrospect:OnApiSlash(cmd, args)
    self:DumpApi(tostring(args or ""))
end

function NexusIntrospect:CollectStats()
    local out  = {}
    local unit = Try(GameLib.GetPlayerUnit)
    if unit == nil then
        table.insert(out, "STAT|ERROR|no player unit")
        return out
    end

    local n = 0
    for _, name in ipairs(STAT_ACCESSORS) do
        if Has(unit, name) then
            local v = Try(unit[name], unit)
            if v ~= nil then
                n = n + 1
                table.insert(out, string.format("STAT|%s|%s", name:gsub("^Get", ""), Flat(v)))
            end
        else
            -- absent is worth recording: it separates "this build has no such stat" from "it read nil"
            table.insert(out, string.format("STATMISSING|%s", name))
        end
    end

    -- GetBasicStats returns the block the character sheet shows, whatever shape it has on this build
    local basic = Try(unit.GetBasicStats, unit)
    if basic ~= nil then table.insert(out, "STATBLOCK|" .. Flat(basic)) end

    table.insert(out, string.format("STATCOUNT|%d read of %d asked", n, #STAT_ACCESSORS))
    return out
end

function NexusIntrospect:OnStatSlash()
    self.tStats = self:CollectStats()
    local n = 0
    for _, r in ipairs(self.tStats) do if r:find("^STAT|") then n = n + 1 end end
    Print(string.format("%s stat block: %d values. /reloadui to write it.", PREFIX, n))
    for i = 1, math.min(#self.tStats, 6) do Print("  " .. self.tStats[i]) end
end


-- ---------------------------------------------------------------------------------------------
-- /nucalc - the stat calculator. One JOINED row per ability: its damage numbers next to the stats
-- that produced them.
--
-- WHY JOINED. /nuability and /nustat already capture both, but as separate sections of the same
-- file. That is fine for one capture and useless for a sweep: to recover how damage scales you need
-- N readings of the SAME ability at DIFFERENT Assault Power, and every reading must carry its own
-- stats or the pairing is guesswork after the fact.
--
-- HOW TO USE IT. Vary one thing, capture, repeat:
--     naked        -> /nucalc -> /reloadui
--     one weapon   -> /nucalc -> /reloadui
--     full gear    -> /nucalc -> /reloadui
-- Three rows per ability at three Assault Powers. The coefficient falls straight out of the deltas,
-- because everything else about the character is unchanged.
--
-- The damage figures are PARSED OUT of the tooltip as numbers rather than left as prose, so the
-- result is arithmetic-ready. The raw text is kept alongside, because a parser that quietly drops a
-- format it did not expect is worse than no parser at all.
-- ---------------------------------------------------------------------------------------------

-- Every number the tooltip states, tagged with what it is. Damage AND healing AND shielding -
-- the first version matched only damage words, so every support ability read as "no numbers" and
-- an entire category went untested while looking merely uninteresting.
--
-- Support abilities matter doubly here: they scale off SupportPower, and a character whose AP and
-- SP are equal cannot distinguish the two. Only a healer with differing values can.
local function TooltipNumbers(sText)
    if type(sText) ~= "string" then return {}, {} end
    local nums, kinds = {}, {}
    local function grab(pat, kind)
        for n in sText:gmatch(pat) do
            nums[#nums + 1] = n; kinds[#kinds + 1] = kind
        end
    end
    grab("(%d+)%s*[Dd][Mm][Gg]", "dmg")
    grab("(%d+)%s+[a-z]*%s*damage", "dmg")
    grab("[Hh]eals?%s+[a-z ]-(%d+)", "heal")
    grab("(%d+)%s+health", "heal")
    grab("[Ss]hields?%s+[a-z ]-(%d+)", "shield")
    grab("(%d+)%s+shield", "shield")
    return nums, kinds
end

-- kept so existing callers keep working; damage only
local function DamageNumbers(sText)
    local nums, kinds = TooltipNumbers(sText)
    local out = {}
    for i, n in ipairs(nums) do if kinds[i] == "dmg" then out[#out + 1] = n end end
    return out
end

-- The stats that come as a TRIPLET: a value, the rating behind it, and the percent that rating
-- converts to. That conversion is THE GAME DOING THE MATHS ITSELF and handing back the answer,
-- softcaps included. Reading all three columns beats deriving a curve from deltas, because it is
-- the client arithmetic rather than an approximation of it, and a single capture already contains
-- one point on every curve.
--
-- Names come from the Unit metatable as enumerated by /nuui, not from documentation. A nil slot
-- means that stat has no accessor of that shape on this build, which is itself worth recording.
local STAT_TRIPLETS = {
    { "Crit",               "GetCritChance",          "GetCritRating",              "GetCritRatingPercent" },
    { "CritSeverity",       "GetCritSeverity",        "GetCritSeverityRating",      "GetCritSeverityRatingPercent" },
    { "CritMitigation",     "GetCriticalMitigation",  "GetCriticalMitigationRating","GetCriticalMitigationRatingPercent" },
    { "ArmorPierce",        "GetArmorPierce",         "GetArmorPierceRating",       "GetArmorPierceRatingPercent" },
    { "Strikethrough",      "GetStrikethroughChance", "GetStrikethroughRating",     "GetStrikethroughRatingPercent" },
    { "Deflect",            "GetDeflectChance",       "GetDeflectRating",           "GetDeflectRatingPercent" },
    { "DeflectCrit",        "GetDeflectCritChance",   "GetDeflectCritRating",       "GetDeflectCritRatingPercent" },
    { "MultiHit",           "GetMultiHitChance",      "GetMultiHitRating",          "GetMultiHitRatingPercent" },
    { "MultiHitAmount",     "GetMultiHitAmount",      "GetMultiHitAmountRating",    "GetMultiHitAmountRatingPercent" },
    { "Glance",             "GetGlanceChance",        "GetGlanceRating",            "GetGlanceRatingPercent" },
    { "GlanceAmount",       "GetGlanceAmount",        "GetGlanceAmountRating",      "GetGlanceAmountRatingPercent" },
    { "Intensity",          nil,                      "GetIntensityRating",         "GetIntensityRatingPercent" },
    { "Vigor",              "GetVigor",               "GetVigorRating",             "GetVigorRatingPercent" },
    { "Lifesteal",          nil,                      "GetLifestealRating",         "GetLifestealRatingPercent" },
    { "FocusRegen",         nil,                      nil,                          "GetFocusRegenRatingPercent" },
    { "PhysicalMitigation", "GetPhysicalMitigation",  "GetPhysicalMitigationRating","GetPhysicalMitigationRatingPercent" },
    { "TechMitigation",     "GetTechMitigation",      "GetTechMitigationRating",    "GetTechMitigationRatingPercent" },
    { "MagicMitigation",    "GetMagicMitigation",     "GetMagicMitigationRating",   "GetMagicMitigationRatingPercent" },
    { "DamageReflect",      "GetDamageReflectChance", "GetDamageReflectRating",     "GetDamageReflectRatingPercent" },
    { "DamageReflectAmt",   "GetDamageReflectAmount", "GetDamageReflectAmountRating","GetDamageReflectAmountRatingPercent" },
    { "PvPOffense",         nil,                      "GetPvPOffenseRating",        "GetPvPOffenseRatingPercent" },
    { "PvPDefense",         nil,                      "GetPvPDefenseRating",        "GetPvPDefenseRatingPercent" },
    { "CCDuration",         nil,                      nil,                          "GetCCDurationRatingPercent" },
    -- both appear on the character sheet and were absent from this list until a screenshot showed
    -- them; the accessor names are guesses and will simply read empty if wrong, which is visible
    { "Tenacity",           "GetTenacity",            nil,                          nil },
    { "Toughness",          "GetToughness",           nil,                          nil },
    -- Everything below appears on the character sheet and was missing from this list. Names are the
    -- obvious ones and are NOT verified; a wrong name reads empty and is visible as such, which is
    -- the point of recording STATMISSING rather than skipping silently.
    { "Hope",               "GetHope",                nil,                          nil },
    { "CooldownReduction",  "GetCooldownReductionModifier", nil,                    nil },
    { "FocusPool",          "GetMaxFocus",            nil,                          nil },
    { "Focus",              "GetFocus",               nil,                          nil },
    { "FocusRecoveryCombat","GetFocusRegenInCombat",  nil,                          nil },
    { "FocusRecoveryIdle",  "GetFocusRegenNonCombat", nil,                          nil },
    { "FocusCostModifier",  "GetFocusCostModifier",   nil,                          nil },
    { "ShieldMitigation",   "GetShieldMitigationPct", nil,                          nil },
    { "ShieldRegen",        "GetShieldRegenPct",      nil,                          nil },
    { "ShieldReboot",       "GetShieldRebootTime",    nil,                          nil },
    { "ShieldTick",         "GetShieldTickTime",      nil,                          nil },
    { "PvPHealingIn",       "GetPvPHealingI",         nil,                          nil },
    { "PvPHealingOut",      "GetPvPHealingO",         nil,                          nil },
}

function NexusIntrospect:DumpCalc(sLabel)
    sLabel = (sLabel ~= nil and sLabel ~= "") and tostring(sLabel) or "unlabelled"

    local unit = Try(GameLib.GetPlayerUnit)
    if unit == nil then
        Print(PREFIX .. " no player unit")
        return
    end

    -- Several of these return a TABLE, not a number - GetCritChance and friends hand back a struct.
    -- tostring() on that yields "table: 0000011D038D4E40", a pointer address, which is worse than no
    -- reading because it looks like data. Caught by comparing a capture against the character sheet:
    -- the sheet said Deflect Chance 5.00% and the capture said a memory address.
    local function Stat(name)
        if name == nil or not Has(unit, name) then return "" end
        local v = Try(unit[name], unit)
        if v == nil then return "" end
        if type(v) == "table" or type(v) == "userdata" then return Flat(v) end
        return tostring(v)
    end

    local rows = {}

    -- what the game itself converts: value, rating, percent
    local nTrip = 0
    for _, t in ipairs(STAT_TRIPLETS) do
        local val, rating, pct = Stat(t[2]), Stat(t[3]), Stat(t[4])
        if val == "" and rating == "" and pct == "" then
            -- nothing read at all: either the stat does not exist on this build or every accessor
            -- name in this row is wrong. Both are worth seeing; neither should look like a zero.
            table.insert(rows, string.format("CONVERTMISSING|%s|%s", sLabel, t[1]))
        end

        if val ~= "" or rating ~= "" or pct ~= "" then
            nTrip = nTrip + 1
            table.insert(rows, string.format("CONVERT|%s|%s|value=%s|rating=%s|percent=%s",
                sLabel, t[1], val, rating, pct))
        end
    end

    -- the power figures the damage coefficients multiply, and the softcap the client applies
    local ctx = string.format(
        "AP=%s SP=%s ARating=%s SRating=%s Softcap=%s Level=%s ItemLevel=%s",
        Stat("GetAssaultPower"), Stat("GetSupportPower"),
        Stat("GetAssaultRating"), Stat("GetSupportRating"),
        Stat("GetAssaultAndSupportPowerSoftcap"),
        Stat("GetLevel"), Stat("GetEffectiveItemLevel"))
    table.insert(rows, string.format("CALCCTX|%s|%s", sLabel, ctx))

    -- and the damage the client computes FROM all of it, so input and output sit in one row
    local nAb, nDmg = 0, 0
    local list = Try(AbilityBook.GetAbilitiesList)
    if type(list) == "table" then
        for _, a in ipairs(list) do
            pcall(function()
                local id   = a.nId or a.nSpellId
                local cur  = a.nCurrentTier or 1
                local tier = a.tTiers and a.tTiers[cur]
                if tier == nil then return end

                nAb = nAb + 1
                local desc = tier.strTierBonusDescription or tier.strDescription or ""
                local nums, kinds = TooltipNumbers(desc)
                if #nums > 0 then nDmg = nDmg + 1 end

                local name = "?"
                if tier.splObject then name = Try(tier.splObject.GetName, tier.splObject) or "?" end

                -- raw text kept on purpose: a parser that silently drops an unexpected format is
                -- worse than no parser, because the row still looks like a reading
                -- PER-ABILITY ARITHMETIC, done here so every row carries its own answer rather
                -- than needing a join afterwards.
                --
                -- These are RATIOS, not coefficients, and the distinction matters. The real model is
                -- value = AssaultPower*c1 + Level*c2, which is two unknowns; one capture cannot
                -- separate them. perAP and perLevel are each the whole value divided by one input,
                -- so they are only the true coefficient when the other term is zero. Named as ratios
                -- so nobody reads them as something they are not.
                --
                -- ratios is the useful one for a multi-value tooltip: Mind Burst reads
                -- 751,1502,2252,3004,3754 and the ratio line says 1,2,3,4,5 - the ability scales
                -- linearly per resource point, visible without any table lookup.
                local calc = "-"
                if #nums > 0 then
                    local apN  = tonumber(Stat("GetAssaultPower")) or 0
                    local spN  = tonumber(Stat("GetSupportPower")) or 0
                    local lvlN = tonumber(Stat("GetLevel")) or 0
                    local v1   = tonumber(nums[1]) or 0

                    local ratios = {}
                    for _, nv in ipairs(nums) do
                        local x = tonumber(nv) or 0
                        ratios[#ratios + 1] = (v1 > 0) and string.format("%.2f", x / v1) or "-"
                    end

                    calc = string.format("perAP=%s perSP=%s perLevel=%s ratios=%s",
                        (apN  > 0) and string.format("%.4f", v1 / apN)  or "-",
                        (spN  > 0) and string.format("%.4f", v1 / spN)  or "-",
                        (lvlN > 0) and string.format("%.4f", v1 / lvlN) or "-",
                        table.concat(ratios, ","))
                end

                table.insert(rows, string.format("CALC|%s|%s|%s|tier=%s|nums=%s|kinds=%s|%s|%s|raw=%s",
                    sLabel, tostring(id), name, tostring(cur),
                    (#nums > 0) and table.concat(nums, ",") or "-",
                    (#kinds > 0) and table.concat(kinds, ",") or "-",
                    calc,
                    ctx, (desc:gsub("%s+", " "))))
            end)
        end
    end

    self.tCalc = self.tCalc or {}
    for _, r in ipairs(rows) do table.insert(self.tCalc, r) end

    Print(string.format("%s calc '%s': %d stat conversions, %d abilities, %d with damage. AP=%s",
        PREFIX, sLabel, nTrip, nAb, nDmg, Stat("GetAssaultPower")))
    Print(PREFIX .. " /reloadui to write it. Change gear and run again for a second point.")
end

-- ---------------------------------------------------------------------------------------------
-- /nucalc diff <labelA> <labelB>
--
-- The scaling, derived by the addon with no table lookup at all. Two captures of the SAME character
-- at DIFFERENT Assault Power give, per ability:
--
--     coefficient = (damage_B - damage_A) / (AP_B - AP_A)
--
-- Everything else about the character is unchanged between the two, so the level term and every
-- other contribution cancels out of the subtraction. That is why the naked/geared pair is the whole
-- experiment: one capture cannot separate two unknowns, two captures make the AP term the only
-- thing that moved.
--
-- Refuses rather than guesses when the powers are equal: a zero denominator is not a coefficient of
-- zero, it is no measurement, and the two must never look alike.
-- ---------------------------------------------------------------------------------------------
function NexusIntrospect:CalcDiff(sA, sB)
    local function parse(label)
        local ability, ap, lvl = {}, nil, nil
        for _, row in ipairs(self.tCalc or {}) do
            local lbl, ctxAP = row:match("^CALCCTX|([^|]+)|AP=([%d%.%-]+)")
            if lbl == label and ctxAP then
                ap  = tonumber(ctxAP)
                lvl = tonumber(row:match("Level=(%d+)") or "")
            end

            local l2, id, name, nums = row:match("^CALC|([^|]+)|(%d+)|([^|]*)|tier=%d+|nums=([^|]*)")
            if l2 == label and nums and nums ~= "-" then
                local first = nums:match("^(%d+)")
                if first then ability[id] = { name = name, value = tonumber(first) } end
            end
        end
        return ability, ap, lvl
    end

    local a, apA, lvlA = parse(sA)
    local b, apB, lvlB = parse(sB)

    if apA == nil or apB == nil then
        Print(string.format("%s diff: missing capture - '%s' AP=%s, '%s' AP=%s",
            PREFIX, sA, tostring(apA), sB, tostring(apB)))
        return
    end

    local dAP  = apB - apA
    local dLvl = (lvlB or 0) - (lvlA or 0)

    if dAP == 0 and dLvl == 0 then
        Print(string.format("%s diff: both captures are at AP=%s level=%s. Nothing varied, so nothing"
            .. " can be measured.", PREFIX, tostring(apA), tostring(lvlA)))
        return
    end

    -- BOTH moved. damage = AP*c1 + Level*c2, so a single subtraction gives one equation in two
    -- unknowns and CANNOT be divided out. Reporting dDamage/dAP here would silently attribute the
    -- level term to Assault Power and produce a confident wrong coefficient.
    --
    -- The deltas are still recorded, because a third capture at another level closes the system:
    -- two independent equations, two unknowns, solvable outside the game.
    local bSolvable = (dLvl == 0)
    if not bSolvable then
        Print(string.format("%s diff: LEVEL ALSO CHANGED (%s -> %s). Both terms moved, so no single"
            .. " coefficient can be divided out of one pair.", PREFIX, tostring(lvlA), tostring(lvlB)))
        Print(PREFIX .. "   deltas are still written. Capture a THIRD level and the system is solvable.")
    end

    Print(string.format("%s scaling from '%s' (AP=%s) to '%s' (AP=%s), dAP=%s",
        PREFIX, sA, tostring(apA), sB, tostring(apB), tostring(dAP)))

    local n = 0
    for id, ra in pairs(a) do
        local rb = b[id]
        if rb then
            local dDmg = rb.value - ra.value
            n = n + 1

            if bSolvable then
                local coeff = dDmg / dAP
                table.insert(self.tCalc, string.format(
                    "SCALE|%s->%s|%s|%s|dDmg=%s|dAP=%s|dLvl=0|perAP=%.4f",
                    sA, sB, id, ra.name, tostring(dDmg), tostring(dAP), coeff))
                if n <= 10 then
                    Print(string.format("   %-24s %s -> %s  = %.4f per AP",
                        ra.name, ra.value, rb.value, coeff))
                end
            else
                -- no perAP field at all, deliberately: an absent number cannot be misread, a wrong
                -- one can
                table.insert(self.tCalc, string.format(
                    "SCALEPAIR|%s->%s|%s|%s|dDmg=%s|dAP=%s|dLvl=%s|from=%s|to=%s",
                    sA, sB, id, ra.name, tostring(dDmg), tostring(dAP), tostring(dLvl),
                    tostring(ra.value), tostring(rb.value)))
                if n <= 10 then
                    Print(string.format("   %-24s %s -> %s  (dDmg=%s dAP=%s dLvl=%s)",
                        ra.name, ra.value, rb.value, tostring(dDmg), tostring(dAP), tostring(dLvl)))
                end
            end
        end
    end

    Print(string.format("%s %d abilities compared. SCALE rows written - /reloadui to save.", PREFIX, n))
end

function NexusIntrospect:OnCalcSlash(cmd, args)
    args = tostring(args or "")
    local a, b = args:match("^%s*diff%s+(%S+)%s+(%S+)")
    if a then return self:CalcDiff(a, b) end
    self:DumpCalc(args)
end

-- =============================================================================================
-- /nuscale - per-ability scaling against EVERY stat, individually.
--
-- /nucalc diff answers one question well: how much damage one point of Assault Power buys. It
-- cannot answer it for Support Power, Crit Severity or anything else, because the naked/geared pair
-- moves a dozen stats at once and a difference across that pair cannot say which of them did the
-- work. Attributing the whole change to whichever stat you happened to be thinking about is how you
-- get a confident wrong coefficient.
--
-- So this captures the FULL stat vector next to every ability's numbers, and the solver only reports
-- a coefficient for stat S from a pair of captures in which S is the ONLY stat that moved. Where
-- nothing isolates S it says so - `nomeasurement` and `confounded` are distinct outcomes and neither
-- is written as zero. A zero coefficient means "this ability does not scale with that stat", which
-- is a real and useful finding; it must never be produced by absence of evidence.
--
-- Isolating one stat is what the server-side `!entity setprop <stat> <value>` command is for:
-- gear cannot move one stat alone, a GM command can. Tooltips recompute client-side from the stat
-- values the server pushes, which is the same path that produced the AP=225 -> 751 verification.
--
-- Restricted to the 202 by ClassAbilityKind. Every tier is captured, not just the equipped one -
-- tiers have their own coefficients, and capturing tier 4 only tells you about tier 4.
--
-- Usage:
--   /nuscale <label>      capture at the current stats, e.g. /nuscale base
--   /nuscale cover        did we get all 202, and which are missing
--   /nuscale solve        per ability, per tier, per stat: the coefficient or why there isn't one
--   /nuscale plan         which stat to move next to unlock the most unmeasured coefficients
--   /nuscale list         labels captured so far
-- =============================================================================================

-- Every numeric stat the client will hand over, as an ordered name->number map. Non-numeric readings
-- are dropped HERE rather than at solve time: a stat that reads as a table cannot be differenced, and
-- carrying it forward as a string only to discard it later hides that fact from `cover`.
function NexusIntrospect:ScaleStatVector(unit)
    local t, order = {}, {}
    local function put(sName, v)
        if v == nil then return end
        local n = tonumber(v)
        if n == nil then return end
        if t[sName] == nil then order[#order + 1] = sName end
        t[sName] = n
    end
    local function read(sAccessor)
        if sAccessor == nil or not Has(unit, sAccessor) then return nil end
        return Try(unit[sAccessor], unit)
    end

    -- the two the damage model is known to use, plus the ratings behind them and the softcap that
    -- bends the conversion. Level is in here because it is a term in the verified formula.
    put("AssaultPower",  read("GetAssaultPower"))
    put("SupportPower",  read("GetSupportPower"))
    put("AssaultRating", read("GetAssaultRating"))
    put("SupportRating", read("GetSupportRating"))
    put("PowerSoftcap",  read("GetAssaultAndSupportPowerSoftcap"))
    put("Level",         read("GetLevel"))
    put("ItemLevel",     read("GetEffectiveItemLevel"))

    -- and everything else the character sheet shows, value/rating/percent apiece. Whether any of
    -- these enters a tooltip number is exactly the open question - that is why they are all here
    -- rather than only the ones I expect to matter.
    for _, trip in ipairs(STAT_TRIPLETS) do
        put(trip[1] .. ".value",   read(trip[2]))
        put(trip[1] .. ".rating",  read(trip[3]))
        put(trip[1] .. ".percent", read(trip[4]))
    end

    return t, order
end

function NexusIntrospect:DumpScale(sLabel)
    sLabel = (sLabel ~= nil and sLabel ~= "") and tostring(sLabel):gsub("[|%s]", "_") or "unlabelled"

    local unit = Try(GameLib.GetPlayerUnit)
    if unit == nil then Print(PREFIX .. " no player unit") return end

    local list = AllAbilities()
    if type(list) ~= "table" or #list == 0 then
        Print(PREFIX .. " AllAbilities returned nothing - nothing captured")
        return
    end

    self.tScale = self.tScale or {}

    -- one context row per capture; every SCALE row below refers to it by label rather than
    -- repeating 100 stat values 1,800 times
    local stats, order = self:ScaleStatVector(unit)
    local parts = {}
    for _, k in ipairs(order) do parts[#parts + 1] = string.format("%s=%s", k, tostring(stats[k])) end
    table.insert(self.tScale, string.format("SCALECTX|%s|%s", sLabel, table.concat(parts, " ")))

    local nTiered, nInnate, nRows, nWithNums = 0, 0, 0, 0
    local seen = {}

    for _, a in ipairs(list) do
        pcall(function()
            local id     = a.nId or a.nSpellId
            local nTiers = (a.tTiers and #a.tTiers) or 0
            local name   = "?"
            local cur    = a.nCurrentTier or 1
            if a.tTiers and a.tTiers[cur] and a.tTiers[cur].splObject then
                name = Try(a.tTiers[cur].splObject.GetName, a.tTiers[cur].splObject) or "?"
            end

            local bClass, sKind = ClassAbilityKind(nTiers, name)
            if not bClass then return end
            if sKind == "tiered" then nTiered = nTiered + 1 else nInnate = nInnate + 1 end
            seen[name] = sKind

            -- EVERY tier, not just the equipped one
            for iTier = 1, nTiers do
                local tier = a.tTiers[iTier]
                if tier ~= nil then
                    local desc = tier.strTierBonusDescription or tier.strDescription or ""
                    local nums, kinds = TooltipNumbers(desc)
                    if #nums > 0 then nWithNums = nWithNums + 1 end
                    nRows = nRows + 1
                    table.insert(self.tScale, string.format("SCALE|%s|%s|%s|%s|tier=%d|nums=%s|kinds=%s",
                        sLabel, tostring(id), name, sKind, iTier,
                        (#nums > 0) and table.concat(nums, ",") or "-",
                        (#kinds > 0) and table.concat(kinds, ",") or "-"))
                end
            end
        end)
    end

    -- the innates the API does not return. Recorded per capture so a later reader can see this was
    -- checked and came up empty, rather than inferring it from a missing row.
    for sName, sClass in pairs(CLASS_INNATE_NAMES) do
        if seen[sName] == nil then
            table.insert(self.tScale, string.format("SCALEABSENT|%s|%s|%s", sLabel, sName, sClass))
        end
    end

    Print(string.format("%s scale '%s': %d tiered + %d innate abilities, %d tier rows (%d with numbers), %d stats",
        PREFIX, sLabel, nTiered, nInnate, nRows, nWithNums, #order))
    if nTiered ~= 32 then
        Print(string.format("%s WARNING: expected 32 tiered abilities for a class, got %d", PREFIX, nTiered))
    end
    Print(PREFIX .. " /reloadui to write it, then move ONE stat and capture again.")
end

-- Parse the stored rows back into a usable shape. Kept separate so cover/solve/plan all read the
-- same interpretation of the save rather than each re-deriving it slightly differently.
function NexusIntrospect:ScaleParse()
    local ctx, vals, labels, absent = {}, {}, {}, {}
    for _, row in ipairs(self.tScale or {}) do
        local lbl, rest = row:match("^SCALECTX|([^|]+)|(.*)$")
        if lbl then
            local m = {}
            for k, v in rest:gmatch("(%S+)=(%S+)") do m[k] = tonumber(v) end
            if ctx[lbl] == nil then labels[#labels + 1] = lbl end
            ctx[lbl] = m
        else
            local l2, id, name, kind, tier, nums = row:match("^SCALE|([^|]+)|([^|]+)|([^|]+)|([^|]+)|tier=(%d+)|nums=([^|]*)")
            if l2 then
                local first = nums:match("^(%d+)")
                if first then
                    local key = id .. "|" .. name .. "|" .. tier .. "|" .. kind
                    vals[key] = vals[key] or {}
                    vals[key][l2] = tonumber(first)
                end
            else
                local l3, n3 = row:match("^SCALEABSENT|([^|]+)|([^|]+)")
                if l3 then absent[n3] = true end
            end
        end
    end
    return ctx, vals, labels, absent
end

-- Stats are not independent columns, and treating them as if they were makes this tool useless in
-- exactly the case that already works.
--
-- AssaultPower IS AssaultRating x 0.25 (GameFormula 1266). Every triplet's .value and .percent are
-- likewise computed by the client from its .rating. So moving ONE thing moves two or three columns,
-- and a naive "exactly one column changed" test would report `confounded` for the cleanest
-- experiment available - the one whose answer is already verified against the client.
--
-- The unit of independence is therefore the DRIVER, not the column. Isolation is judged in drivers;
-- slopes are still reported per column, because "damage per point of AssaultPower" and "damage per
-- point of AssaultRating" are both true and differ by exactly the 0.25 conversion.
local function StatDriver(sName)
    local base = sName:match("^(.-)%.[a-z]+$")
    if base then return base end                       -- Crit.value / Crit.rating / Crit.percent -> Crit
    if sName == "AssaultPower"  or sName == "AssaultRating" then return "Assault" end
    if sName == "SupportPower"  or sName == "SupportRating" then return "Support" end
    return sName
end

-- Which stats differ between two captures, by how much, and how many INDEPENDENT things moved.
local function StatDelta(a, b)
    local moved, deltas, drivers = {}, {}, {}
    local nDrivers = 0
    for k, v in pairs(b) do
        local prev = a[k]
        if prev ~= nil and prev ~= v then
            moved[#moved + 1] = k
            deltas[k] = v - prev
            local d = StatDriver(k)
            if drivers[d] == nil then
                drivers[d] = true
                nDrivers = nDrivers + 1
            end
        end
    end
    table.sort(moved)
    return moved, deltas, nDrivers, drivers
end

function NexusIntrospect:ScaleSolve()
    local ctx, vals, labels = self:ScaleParse()
    if #labels < 2 then
        Print(string.format("%s need at least 2 captures to solve, have %d. Capture, move ONE stat, capture again.",
            PREFIX, #labels))
        return
    end

    -- pairs of captures separated by exactly one stat. These are the only pairs that can attribute
    -- a change to a specific stat; everything else is recorded as confounded.
    local clean, confounded = {}, {}
    for i = 1, #labels do
        for j = 1, #labels do
            if i ~= j then
                local moved, deltas, nDrivers = StatDelta(ctx[labels[i]], ctx[labels[j]])
                if nDrivers == 1 then
                    -- one independent thing moved, so every column it moved is attributable
                    for _, s in ipairs(moved) do
                        clean[s] = clean[s] or {}
                        table.insert(clean[s], { a = labels[i], b = labels[j], d = deltas[s] })
                    end
                elseif nDrivers > 1 then
                    for _, s in ipairs(moved) do
                        confounded[s] = confounded[s] or {}
                        confounded[s][nDrivers] = table.concat(moved, "+")
                    end
                end
            end
        end
    end

    local out = {}
    local nSolved, nConf, nNone = 0, 0, 0

    local statNames = {}
    for _, l in ipairs(labels) do
        for k in pairs(ctx[l]) do statNames[k] = true end
    end
    local statList = {}
    for k in pairs(statNames) do statList[#statList + 1] = k end
    table.sort(statList)

    for key, byLabel in pairs(vals) do
        local id, name, tier, kind = key:match("^([^|]+)|([^|]+)|([^|]+)|([^|]+)$")
        for _, s in ipairs(statList) do
            local pairsFor = clean[s]
            if pairsFor ~= nil then
                local slopes = {}
                for _, p in ipairs(pairsFor) do
                    local va, vb = byLabel[p.a], byLabel[p.b]
                    if va ~= nil and vb ~= nil and p.d ~= 0 then
                        slopes[#slopes + 1] = (vb - va) / p.d
                    end
                end
                if #slopes > 0 then
                    local lo, hi, sum = slopes[1], slopes[1], 0
                    for _, v in ipairs(slopes) do
                        if v < lo then lo = v end
                        if v > hi then hi = v end
                        sum = sum + v
                    end
                    nSolved = nSolved + 1
                    -- spread is the honesty column: a coefficient averaged over pairs that disagree
                    -- is not one coefficient, it is a sign the relationship is not linear here
                    table.insert(out, string.format("SCALED|%s|%s|%s|tier=%s|%s|coef=%.6f|n=%d|spread=%.6f",
                        id, name, kind, tier, s, sum / #slopes, #slopes, hi - lo))
                end
            elseif confounded[s] ~= nil then
                nConf = nConf + 1
                local with = "?"
                for _, v in pairs(confounded[s]) do with = v break end
                table.insert(out, string.format("SCALED|%s|%s|%s|tier=%s|%s|confounded|movedWith=%s",
                    id, name, kind, tier, s, with))
            else
                nNone = nNone + 1
                table.insert(out, string.format("SCALED|%s|%s|%s|tier=%s|%s|nomeasurement",
                    id, name, kind, tier, s))
            end
        end
    end

    self.tScaleSolved = out
    Print(string.format("%s solve: %d coefficients, %d confounded, %d unmeasured, across %d captures",
        PREFIX, nSolved, nConf, nNone, #labels))
    Print(PREFIX .. " /nuscale plan says which stat to move next. /reloadui to write SCALED rows.")
end

function NexusIntrospect:ScaleCover()
    local ctx, vals, labels, absent = self:ScaleParse()
    local tiered, innate = {}, {}
    for key in pairs(vals) do
        local _, name, _, kind = key:match("^([^|]+)|([^|]+)|([^|]+)|([^|]+)$")
        if kind == "tiered" then tiered[name] = true else innate[name] = true end
    end
    local nT, nI = 0, 0
    for _ in pairs(tiered) do nT = nT + 1 end
    for _ in pairs(innate) do nI = nI + 1 end

    Print(string.format("%s cover: %d captures | %d tiered (expect 32) | %d innate", PREFIX, #labels, nT, nI))
    if nT ~= 32 then
        Print(string.format("%s   MISMATCH: a class has exactly 32 tiered abilities, this reads %d", PREFIX, nT))
    end
    for sName, sClass in pairs(CLASS_INNATE_NAMES) do
        if innate[sName] == nil and absent[sName] then
            Print(string.format("%s   absent from API (known): %s (%s)", PREFIX, sName, sClass))
        end
    end
    Print(PREFIX .. "   note: 202 is the ALL-SIX-CLASSES total; one character can only ever show its own ~33-35.")
end

-- The point of this one: after a capture or two, say what to do next rather than leaving the player
-- to guess which of ~100 stats is still unmeasured.
function NexusIntrospect:ScalePlan()
    local ctx, vals, labels = self:ScaleParse()
    if #labels == 0 then Print(PREFIX .. " no captures yet - run /nuscale base") return end

    local isolated = {}
    for i = 1, #labels do
        for j = 1, #labels do
            if i ~= j then
                local moved, _, nDrivers = StatDelta(ctx[labels[i]], ctx[labels[j]])
                if nDrivers == 1 then
                    for _, s in ipairs(moved) do isolated[s] = true end
                end
            end
        end
    end

    -- Work in drivers, and name the property that can actually be SET. AssaultPower is not settable
    -- - it is computed from AssaultRating - so suggesting it would be an instruction that cannot be
    -- followed. Ratings are the real handles.
    local todoSet, nIsolated = {}, 0
    for _ in pairs(isolated) do nIsolated = nIsolated + 1 end
    for k in pairs(ctx[labels[#labels]]) do
        local d = StatDriver(k)
        if not isolated[k] and todoSet[d] == nil then todoSet[d] = true end
    end

    local todo = {}
    for d in pairs(todoSet) do todo[#todo + 1] = d end
    table.sort(todo)

    local function SettableName(sDriver)
        if sDriver == "Assault" then return "AssaultRating" end
        if sDriver == "Support" then return "SupportRating" end
        if sDriver == "Level" or sDriver == "ItemLevel" or sDriver == "PowerSoftcap" then return nil end
        return "Rating" .. sDriver   -- the enum is mostly Rating<Stat>; !entity setprop suggests near matches
    end

    Print(string.format("%s plan: %d columns isolated, %d drivers still unmeasured. Next:",
        PREFIX, nIsolated, #todo))
    local shown = 0
    for _, d in ipairs(todo) do
        local prop = SettableName(d)
        if prop ~= nil and shown < 12 then
            shown = shown + 1
            Print(string.format("%s   !entity setprop %s <newvalue>   then  /reloadui  then  /nuscale %s",
                PREFIX, prop, d))
        end
    end
    Print(PREFIX .. "   change ONE and only one between captures - the solver refuses to attribute otherwise.")
    if #todo > shown then Print(string.format("%s   ... and %d more drivers", PREFIX, #todo - shown)) end
end

function NexusIntrospect:OnScaleSlash(cmd, args)
    args = tostring(args or ""):match("^%s*(.-)%s*$")
    if args == "solve" then return self:ScaleSolve() end
    if args == "cover" then return self:ScaleCover() end
    if args == "plan"  then return self:ScalePlan()  end
    if args == "list" then
        local _, _, labels = self:ScaleParse()
        Print(string.format("%s %d captures: %s", PREFIX, #labels, table.concat(labels, ", ")))
        return
    end
    self:DumpScale(args)
end

function NexusIntrospect:DumpAbilities()
    local out = {}

    -- The stats that produced the damage numbers below, captured in the same breath. Stored in its
    -- own table AS WELL as inlined here: inline keeps the pairing obvious to anyone reading one
    -- capture, the table makes it extractable without parsing the ability rows.
    self.tStats = self:CollectStats()
    for _, row in ipairs(self.tStats) do table.insert(out, row) end

    -- GetAbilityPoints and GetTotalAbilityPoints DO NOT EXIST. They were printed as nil every run
    -- since this line was written. The real names, from the client's own API reference, are
    -- GetAvailablePower / GetTotalPower - and GetTotalPower is the direct answer to the open
    -- question of how many AMP points a level 50 character has (the client UI reads 47; our server
    -- formula produces 41). Asking the client beats deriving the progression.
    table.insert(out, string.format("ampAvailable=%s ampTotal=%s ampLockedIn=%s spec=%s unlockedSpecs=%s",
        tostring(Try(AbilityBook.GetAvailablePower)),
        tostring(Try(AbilityBook.GetTotalPower)),
        tostring(Try(AbilityBook.GetAvailableLockedInPower)),
        tostring(Try(AbilityBook.GetCurrentSpec)),
        tostring(Try(AbilityBook.GetNumUnlockedSpecs))))

    -- the tier ladder, straight from the client rather than inferred from TIERREQ rows
    local tierReq = Try(AbilityBook.GetSpellTierLevelRequirements)
    if type(tierReq) == "table" then
        local parts = {}
        for i, lvl in ipairs(tierReq) do parts[#parts + 1] = string.format("%d=%s", i, tostring(lvl)) end
        table.insert(out, "TIERLEVELREQ|" .. table.concat(parts, " "))
    end

    local list = AllAbilities()
    if type(list) ~= "table" then
        table.insert(out, "AllAbilities returned " .. type(list))
    else
        table.insert(out, "abilities=" .. tostring(#list))
        for _, a in ipairs(list) do
            pcall(function()
                local id, cur = a.nId or a.nSpellId, a.nCurrentTier
                local tiers = a.tTiers and #a.tTiers or 0
                local name = "?"
                if a.tTiers and a.tTiers[cur or 1] and a.tTiers[cur or 1].splObject then
                    name = a.tTiers[cur or 1].splObject:GetName() or "?"
                end
                table.insert(out, string.format("ABILITY|%s|%s|tier=%s/%s|active=%s|%s",
                    tostring(id), tostring(name), tostring(cur), tostring(tiers),
                    tostring(a.bIsActive), Flat(a)))
            end)
        end
    end

    -- GetNumClassInnateAbilitySpells and GetClassInnateAbilitySpells are NOT in the client's API
    -- surface either. Both were called and both returned nil every run, so "innateCount=nil" was
    -- recorded as a reading rather than as a missing accessor. Kept, but labelled: if these ever do
    -- return something the row proves it, and if they do not the row says which names were tried.
    table.insert(out, string.format("INNATEPROBE|GetNumClassInnateAbilitySpells=%s|GetClassInnateAbilitySpells=%s|not in the client API reference; innates now come from AllAbilities() across every spell tag",
        tostring(Try(AbilityBook.GetNumClassInnateAbilitySpells)),
        type(Try(AbilityBook.GetClassInnateAbilitySpells))))

    self.tAbilities = out
    Print(string.format("%s abilities: %d lines", PREFIX, #out))
    for i = 1, math.min(#out, 6) do Print("   " .. out[i]) end
end

-- GetEldanAugmentationData returned a boolean when called with no arguments, which means it takes
-- some. No addon in the local corpus calls it and the decompiled client does not name it, so the
-- signature is discovered the same way everything else was tonight: by asking the client and
-- recording what comes back, rather than guessing and reporting the guess as fact.
function NexusIntrospect:DumpAmps()
    local out = {}
    local spec = Try(AbilityBook.GetCurrentSpec)

    table.insert(out, string.format("currentSpec=%s unlockedSpecs=%s respecCost=%s",
        tostring(spec), tostring(Try(AbilityBook.GetNumUnlockedSpecs)),
        tostring(Try(AbilityBook.GetEldanAugmentationRespecCost))))

    -- probe: no args, then 0..4, then (spec, 0..2). Record the SHAPE of every reply.
    local probes = {
        { label = "()",        args = {} },
        { label = "(0)",       args = { 0 } },
        { label = "(1)",       args = { 1 } },
        { label = "(2)",       args = { 2 } },
        { label = "(3)",       args = { 3 } },
        { label = "(4)",       args = { 4 } },
        { label = "(spec)",    args = { spec } },
        { label = "(spec,0)",  args = { spec, 0 } },
        { label = "(spec,1)",  args = { spec, 1 } },
        { label = "(0,true)",  args = { 0, true } },
        { label = "(true)",    args = { true } },
    }

    local best, bestLabel, bestCount = nil, nil, 0
    for _, pr in ipairs(probes) do
        local res = Try(AbilityBook.GetEldanAugmentationData, unpack(pr.args))
        local tr  = type(res)

        -- COUNT WITH pairs, NOT #. The length operator only sees a table's array part, so a table
        -- keyed by amp id reads as empty when it is full. Reporting that as "count=0" would have
        -- looked exactly like "this spec has no AMPs" - a plausible empty result, which is the most
        -- expensive kind of wrong answer.
        local n = 0
        if tr == "table" then pcall(function() for _ in pairs(res) do n = n + 1 end end) end

        table.insert(out, string.format("PROBE|GetEldanAugmentationData%s -> %s%s",
            pr.label, tr, (tr == "table") and (" entries=" .. tostring(n)) or (" value=" .. tostring(res))))
        if tr == "table" and n > (bestCount or 0) then best, bestLabel, bestCount = res, pr.label, n end
    end

    if best then
        table.insert(out, string.format("USING %s with %d entries", tostring(bestLabel), bestCount))
        -- pairs, not ipairs, for the same reason
        pcall(function()
            for k, amp in pairs(best) do
                table.insert(out, string.format("AMP|%s|%s", tostring(k), Flat(amp)))
            end
        end)
    else
        table.insert(out, "no argument shape returned a table - see the PROBE lines")
    end

    -- Every spec index up to 10, not just the count GetNumUnlockedSpecs reports. That returned 4 and
    -- I read it as "there are four" - UNLOCKED is not TOTAL. The AMP window shows SIX categories
    -- (Assault, Hybrid A/S, Support, Hybrid S/U, Utility, Hybrid A/U), so probing to the reported
    -- count would have missed two outright.
    --
    -- ONE ROW PER AUGMENT. Every bubble and every padlock in that window is an augment with its own
    -- state, and flattening the whole array into a single line truncates it - which reads as "there
    -- are only a few" rather than "the rest did not fit". Grid position is kept because it is what
    -- lets a row be matched back to a node on screen.
    for iSpec = 1, 10 do
        local d = Try(AbilityBook.GetEldanAugmentationData, iSpec)
        if type(d) == "table" then

            -- categories: the six hexagon segments, with power spent and tier reached
            if type(d.tCategories) == "table" then
                local nCat = 0
                pcall(function()
                    for key, cat in pairs(d.tCategories) do
                        nCat = nCat + 1
                        table.insert(out, string.format("CATEGORY|spec=%d|key=%s|%s",
                            iSpec, tostring(key), Flat(cat)))
                    end
                end)
                table.insert(out, string.format("SPEC%d categories=%d", iSpec, nCat))
            end

            -- augments: every node, selected or locked or merely available
            if type(d.tAugments) == "table" then
                local nAug, nUnlocked = 0, 0
                pcall(function()
                    for key, aug in pairs(d.tAugments) do
                        nAug = nAug + 1
                        if aug.bUnlocked then nUnlocked = nUnlocked + 1 end
                        -- cost and name pulled to the front under whichever key the build uses,
                        -- so a row is readable without parsing the flatten. The full flatten still
                        -- follows, because these guesses may all miss.
                        local cost = aug.nPowerCost or aug.nCost or aug.nPower or aug.nAmpPower
                        local nm   = aug.strName or aug.strTitle
                        if not nm and aug.splAugment then
                            nm = Try(aug.splAugment.GetName, aug.splAugment)
                        end
                        table.insert(out, string.format("AUGMENT|spec=%d|key=%s|cost=%s|name=%s|%s",
                            iSpec, tostring(key), tostring(cost), tostring(nm), Flat(aug)))
                    end
                end)
                table.insert(out, string.format("SPEC%d augments=%d unlocked=%d",
                    iSpec, nAug, nUnlocked))
            end

            -- anything else the structure carries that is neither of those two
            pcall(function()
                for key, v in pairs(d) do
                    if key ~= "tCategories" and key ~= "tAugments" then
                        table.insert(out, string.format("SPECFIELD|spec=%d|%s=%s",
                            iSpec, tostring(key), (type(v) == "table") and Flat(v) or tostring(v)))
                    end
                end
            end)
        end
    end

    local reset = Try(AbilityBook.GetEldanAugmentationResetData)
    if type(reset) == "table" then table.insert(out, "RESET|" .. Flat(reset)) end

    self.tAmps = out
    Print(string.format("%s amps: %d lines", PREFIX, #out))
    for i = 1, math.min(#out, 14) do Print("   " .. out[i]) end
end

function NexusIntrospect:DumpTiers()
    local out = {}

    local req = Try(AbilityBook.GetSpellTierLevelRequirements)
    if type(req) == "table" then
        table.insert(out, "tierLevelRequirements=" .. tostring(#req))
        for i, r in ipairs(req) do
            table.insert(out, string.format("TIERREQ|%d|%s", i, Flat(r)))
        end
    else
        table.insert(out, "GetSpellTierLevelRequirements returned " .. type(req))
    end

    -- every tier of every ability with the real spell id behind it. This is the part a wiki scrape
    -- gets wrong: tier-scaled spell ids move between patches.
    local list = Try(AbilityBook.GetAbilitiesList)
    if type(list) == "table" then
        for _, a in ipairs(list) do
            pcall(function()
                if not a.tTiers then return end
                local id = a.nId or a.nSpellId
                for idx, tier in ipairs(a.tTiers) do
                    local nm, sid
                    if tier.splObject then
                        nm  = Try(tier.splObject.GetName, tier.splObject)
                        sid = Try(tier.splObject.GetId, tier.splObject)
                    end
                    table.insert(out, string.format("TIER|%s|%d|spell=%s|%s|%s",
                        tostring(id), idx, tostring(sid), tostring(nm), Flat(tier)))
                end
            end)
        end
    end

    self.tTiers = out
    Print(string.format("%s tiers: %d lines", PREFIX, #out))
    for i = 1, math.min(#out, 6) do Print("   " .. out[i]) end
end

-----------------------------------------------------------------------------------------------
-- item catalog
-----------------------------------------------------------------------------------------------

local CATALOG_MAX   = 90000
local CATALOG_CHUNK = 1500

function NexusIntrospect:StartCatalog(sSearch)
    if not sSearch or sSearch == "" then
        Print(PREFIX .. " usage: /nuitem hoverboard")
        return
    end

    self.sSearch  = sSearch:lower()
    self.nAt      = 1
    self.tCatalog = {}

    if not self.catalogTimer then
        self.catalogTimer = ApolloTimer.Create(0.05, true, "OnCatalogTimer", self)
    end
    self.catalogTimer:Start()
    Print(string.format("%s scanning items for '%s'...", PREFIX, sSearch))
end

function NexusIntrospect:OnCatalogTimer()
    local stop = math.min(self.nAt + CATALOG_CHUNK, CATALOG_MAX)

    for id = self.nAt, stop do
        local item = Try(Item.GetDataFromId, id)
        if item then
            local name = Try(item.GetName, item)
            if name and tostring(name):lower():find(self.sSearch, 1, true) then
                table.insert(self.tCatalog, string.format("%d = %s", id, tostring(name)))
            end
        end
    end

    self.nAt = stop + 1
    if self.nAt >= CATALOG_MAX then
        self.catalogTimer:Stop()
        Print(string.format("%s found %d item(s). /reloadui to send.", PREFIX, #self.tCatalog))
        for i = 1, math.min(#self.tCatalog, 12) do Print("   " .. self.tCatalog[i]) end
    end
end

-----------------------------------------------------------------------------------------------
-- /nuall, staggered
-----------------------------------------------------------------------------------------------

-- /nuall [radius] [item search]
--
-- A leading number is the scan radius for the nearby sweep, anything after it is the item search,
-- so "/nuall 500 hoverboard" means both. Without a number the radius stays at whatever was last
-- used, which makes a repeat run repeat the same sweep rather than silently narrowing it.
function NexusIntrospect:EnableAll(sArgs)
    sArgs = tostring(sArgs or "")

    local sRadius, sRest = sArgs:match("^%s*(%d+)%s*(.*)$")
    if sRadius then
        self.nAllRadius   = Clamp(tonumber(sRadius))
        self.sPendingItem = sRest
    else
        self.nAllRadius   = self.nAllRadius or 30
        self.sPendingItem = sArgs
    end

    Print(string.format("%s ==== ARMING (staggered), scan radius %d ====", PREFIX, self.nAllRadius))
    self.nStage = 0

    if not self.stageTimer then
        self.stageTimer = ApolloTimer.Create(3.0, true, "OnStageTimer", self)
    end
    self.stageTimer:Start()
    self:OnStageTimer()
end

-- Staggered because firing the api scan, three dumps, an item scan and a ten-per-second probe in
-- one instant floods everything at once, and the probe out-writes the rest by an order of magnitude.
function NexusIntrospect:OnStageTimer()
    self.nStage = (self.nStage or 0) + 1

    if self.nStage == 1 then
        self:ScanApi()

        -- The UI map is a property of the BUILD, not of this session - it is identical every run,
        -- so recapturing it on every /nuall would add the same thousands of rows to every save for
        -- nothing. Captured once, then left alone. "/nuui" re-runs it on demand if that is wanted.
        if CAPTURE_BUILD_INVARIANT and #(self.tUi or {}) == 0 then
            self:DumpUi()
        end

        Print(string.format("%s  [1/5] api: %d namespaces, %d enums, ui rows %d",
            PREFIX, self:Count(self.tApi), self:Count(self.tEnums), #(self.tUi or {})))

    elseif self.nStage == 2 then
        self:DumpAbilities()
        self:DumpAmps()
        self:DumpTiers()
        local nStat = 0
        for _, r in ipairs(self.tStats or {}) do if r:find("^STAT|") then nStat = nStat + 1 end end
        Print(string.format("%s  [2/5] abilities, amps, tiers + %d combat stats captured", PREFIX, nStat))

    elseif self.nStage == 3 then
        -- deliberately its own stage rather than bolted onto another: the sweep is a snapshot of
        -- where the player is standing AT THAT MOMENT, so it wants a known point in the sequence
        self:DumpNear(self.nAllRadius)
        Print(PREFIX .. "  [3/5] nearby units captured")

    elseif self.nStage == 4 then
        local tel = Try(Apollo.GetAddon, "NexusTelemetry")
        if tel then
            pcall(function() tel.bWatch = true; tel.tLast = {}; tel.bCaptureAllChat = true end)
            Print(PREFIX .. "  [4/5] telemetry watch ON (incl. all chat)")
        else
            Print(PREFIX .. "  [4/5] telemetry addon NOT FOUND")
        end

    else
        local tel = Try(Apollo.GetAddon, "NexusTelemetry")
        if tel then
            pcall(function() tel:StartSprintProbe(60) end)
            Print(PREFIX .. "  [5/5] sprint probe armed 60s - hold Shift and run NOW")
        end
        if self.sPendingItem and self.sPendingItem ~= "" then
            self:StartCatalog(self.sPendingItem)
        end
        self.stageTimer:Stop()
        Print(PREFIX .. " ==== ARMED. Play, then /reloadui ====")
    end
end

-----------------------------------------------------------------------------------------------
-- commands
-----------------------------------------------------------------------------------------------


-----------------------------------------------------------------------------------------------
-- SNAPSHOT  (/nusnap <label>)
--
-- Captures abilities, AMPs and points under a label, so two captures either side of an action can
-- be diffed instead of compared by eye. A single "after" reading tells you the state; a pair tells
-- you what the action actually CHANGED, which is the question worth asking of a command like
-- !character level 50.
-----------------------------------------------------------------------------------------------

function NexusIntrospect:Snapshot(sLabel)
    sLabel = (sLabel ~= nil and sLabel ~= "") and sLabel or "snap"

    self.tSnaps = self.tSnaps or {}

    local unit = Try(GameLib.GetPlayerUnit)
    local snap = {
        label     = sLabel,
        level     = unit and Try(unit.GetBasicStats, unit) and "see stats" or nil,
        spec      = Try(AbilityBook.GetCurrentSpec),
        specs     = Try(AbilityBook.GetNumUnlockedSpecs),
        power     = Try(AbilityBook.GetTotalPower),
        available = Try(AbilityBook.GetAvailablePower),
        lockedIn  = Try(AbilityBook.GetAvailableLockedInPower),
        respec    = Try(AbilityBook.GetEldanAugmentationRespecCost),
        abilities = {},
        amps      = {},
    }

    -- ability tiers, the thing a level change should move
    local list = Try(AbilityBook.GetAbilitiesList)
    if type(list) == "table" then
        for _, a in ipairs(list) do
            pcall(function()
                snap.abilities[tostring(a.nId or a.nSpellId)] =
                    string.format("%s/%s", tostring(a.nCurrentTier), tostring(a.tTiers and #a.tTiers or 0))
            end)
        end
    end

    -- amps taken, by id, so a change in selection is visible
    local d = Try(AbilityBook.GetEldanAugmentationData, Try(AbilityBook.GetCurrentSpec) or 1)
    if type(d) == "table" and type(d.tAugments) == "table" then
        pcall(function()
            for _, aug in pairs(d.tAugments) do
                if aug.nId then
                    snap.amps[tostring(aug.nId)] = string.format("cost=%s unlocked=%s",
                        tostring(aug.nPowerCost), tostring(aug.bUnlocked))
                end
            end
        end)
    end

    -- vitals and the resources, since a level change moves those too
    if unit then
        snap.health    = Try(unit.GetHealth, unit)
        snap.healthMax = Try(unit.GetMaxHealth, unit)
        snap.shield    = Try(unit.GetShieldCapacity, unit)
        snap.r0        = Try(unit.GetResource, unit, 0)
        snap.r7        = Try(unit.GetResource, unit, 7)
    end

    table.insert(self.tSnaps, snap)

    local nAb, nAmp = 0, 0
    for _ in pairs(snap.abilities) do nAb = nAb + 1 end
    for _ in pairs(snap.amps) do nAmp = nAmp + 1 end

    Print(string.format("%s snapshot '%s': %d abilities, %d amps, power=%s available=%s hp=%s",
        PREFIX, sLabel, nAb, nAmp, tostring(snap.power), tostring(snap.available), tostring(snap.health)))
end

-- ---------------------------------------------------------------------------------------------
-- Nearby units, and specifically WHY something the player is standing on is not interactive.
--
-- There is no "units in range" call on this build. The client only tells an addon about a unit
-- through UnitCreated, so the live set has to be maintained by hooking that pair of events - which
-- is how every nameplate addon on 16042 does it, and the reason this is event driven rather than a
-- lookup.
--
-- The field this exists for is GetActivationState. A pad the player can see is world geometry and
-- is drawn whether or not anything lives on it; whether the client offers an interact prompt is
-- decided by the activation state the SERVER sent for the unit standing on that geometry. That
-- gives three answers which look identical in game and need completely different fixes:
--
--   no unit at all            nothing is spawned - the entity row is missing from the world data
--   unit, empty activation    spawned, but the server never flagged it activatable
--   unit, activation present  the client had everything it needed and still refused
--
-- Reporting "the teleporter is broken" cannot distinguish those. This can.
-- ---------------------------------------------------------------------------------------------

function NexusIntrospect:OnUnitCreated(unit)
    if unit == nil then return end
    local id = Try(unit.GetId, unit)
    if id ~= nil then self.tLiveUnits[id] = unit end
end

function NexusIntrospect:OnUnitDestroyed(unit)
    if unit == nil then return end
    local id = Try(unit.GetId, unit)
    if id ~= nil then self.tLiveUnits[id] = nil end
end

local function Dist(a, b)
    if type(a) ~= "table" or type(b) ~= "table" then return nil end
    if a.x == nil or b.x == nil then return nil end
    local dx, dy, dz = a.x - b.x, (a.y or 0) - (b.y or 0), a.z - b.z
    return math.sqrt(dx * dx + dy * dy + dz * dz)
end

function NexusIntrospect:DumpNear(nRadius)
    nRadius = Clamp(nRadius)

    local player = Try(GameLib.GetPlayerUnit)
    if player == nil then
        Print(PREFIX .. " no player unit - are you loaded in?")
        return
    end

    local myPos = Try(player.GetPosition, player)
    local found, scanned = {}, 0

    for id, unit in pairs(self.tLiveUnits) do
        scanned = scanned + 1

        -- a tracked handle can outlive the unit; ask before trusting it
        if Try(unit.IsValid, unit) ~= false then
            local pos  = Try(unit.GetPosition, unit)
            local dist = Dist(myPos, pos)

            if dist ~= nil and dist <= nRadius then
                table.insert(found, {
                    id         = id,
                    name       = Try(unit.GetName, unit),
                    unitType   = Try(unit.GetType, unit),
                    -- the whole point of the command
                    activation = Flat(Try(unit.GetActivationState, unit)),
                    -- everything else that could gate an interact prompt
                    -- GetInteractType does not exist in the client binary; the real names are
                    -- GetInteractHintArrowObject and GameLib.GetInteractiveUnit. Reading the
                    -- former, which is the per-unit one.
                    interact   = Flat(Try(unit.GetInteractHintArrowObject, unit)),
                    rewards    = Flat(Try(unit.GetRewardInfo, unit)),

                    -- DOES THE ACCESSOR EXIST, asked separately from what it returned.
                    --
                    -- Flat(nil) is "", and Try() turns both "no such method" and "returned nil"
                    -- into nil - so an empty activation string cannot distinguish "this unit has
                    -- no activation" from "this build has no such call". The first is a server
                    -- bug worth chasing; the second is my probe being wrong. The first read of
                    -- this command reported empty activation on the teleporter AND on the player,
                    -- which is the signature of the second, so the two questions get asked apart.
                    hasActivation = Has(unit, "GetActivationState"),
                    hasInteract   = Has(unit, "GetInteractHintArrowObject"),
                    hasRewards    = Has(unit, "GetRewardInfo"),
                    disp       = Try(unit.GetDispositionTo, unit, player),
                    faction    = Try(unit.GetFaction, unit),
                    targetable = Try(unit.IsValid, unit),
                    dead       = Try(unit.IsDead, unit),
                    creatureId = Try(unit.GetCreatureId, unit),
                    dist       = string.format("%.1f", dist),
                    pos        = pos and string.format("%.1f,%.1f,%.1f",
                                     pos.x or 0, pos.y or 0, pos.z or 0) or "",
                })
            end
        end
    end

    table.sort(found, function(l, r) return tonumber(l.dist) < tonumber(r.dist) end)

    table.insert(self.tNear, {
        when    = tostring(Try(GameLib.GetGameTime) or ""),
        radius  = nRadius,
        myPos   = myPos and string.format("%.1f,%.1f,%.1f",
                      myPos.x or 0, myPos.y or 0, myPos.z or 0) or "",
        scanned = scanned,
        units   = found,
    })

    Print(string.format("%s %d unit(s) within %.0f of you, %d tracked in all.",
        PREFIX, #found, nRadius, scanned))

    for i = 1, math.min(#found, 8) do
        local u = found[i]
        -- hasFn is printed next to the value on purpose: activation=[] hasFn=false is a probe that
        -- found nothing to ask, activation=[] hasFn=true is a unit that genuinely has no activation
        Print(string.format("  %sm  %s  type=%s  activation=[%s] hasFn=%s",
            u.dist, tostring(u.name), tostring(u.unitType),
            tostring(u.activation), tostring(u.hasActivation)))
    end

    if scanned == 0 then
        -- units that already existed when the addon loaded never fired UnitCreated, so an empty
        -- set means the tracker started late, NOT that the area is empty. Say so, because
        -- "0 units" read as an answer would point at exactly the wrong bug.
        Print(PREFIX .. " nothing tracked yet - walk out of range and back so UnitCreated fires.")
    end

    Print(PREFIX .. " /reloadui to write it to disk.")
end

function NexusIntrospect:OnNearSlash(cmd, args)
    self:DumpNear(args)
end

-- ---------------------------------------------------------------------------------------------
-- /nuui - map the whole UI surface, and specifically what tries to PERSIST.
--
-- This deliberately does NOT use the curated NAMESPACES list that ScanApi walks. That list is 35
-- libraries somebody thought to write down, and "every UI function the game knows" cannot be
-- answered from a list maintained by hand - the one that matters will be the one nobody added. So
-- this walks _G instead and finds libraries whether or not anyone remembered them.
--
-- The save angle is the whole point. Every time "it does not save" has been chased on this server
-- it has been the same shape: the client sends something and the server has no handler, so the
-- value is accepted in the UI and silently gone next login. The away and busy messages on opcode
-- 0x03B7 were exactly that, fixed earlier tonight. Tagging save-shaped calls gives the CLIENT half
-- of a cross-reference; M7's unhandled-packet log is the SERVER half. A save-shaped call plus a
-- GAP line for the opcode it sends is not a suspicion, it is the bug, located.
-- ---------------------------------------------------------------------------------------------

-- Substrings that suggest a call changes state rather than reads it. Deliberately broad: a false
-- positive costs one line in a list, a false negative hides the exact call we are hunting.
local SAVE_SHAPED = {
    "save", "store", "persist", "commit", "apply", "submit", "confirm", "set",
    "update", "request", "send", "change", "toggle", "select", "equip", "swap", "add", "remove",
}

local function SaveHint(sName)
    local low = sName:lower()
    for _, hint in ipairs(SAVE_SHAPED) do
        if low:find(hint, 1, true) then return hint end
    end
    return nil
end

-- A library with more functions than this gets truncated. The cap exists so one enormous table
-- cannot crowd out every other library in the save file - but it is ANNOUNCED in the output, never
-- silent, because a truncated list that looks complete is how "this function does not exist" gets
-- concluded about a function that does.
local UI_FN_CAP = 300

function NexusIntrospect:DumpUi(sFilter)
    sFilter = (sFilter or ""):lower()

    local out  = {}
    local nLib, nFn, nSave, nCut = 0, 0, 0, 0

    local names = {}
    pcall(function()
        for k, v in pairs(_G) do
            if type(k) == "string" and type(v) == "table" then table.insert(names, k) end
        end
    end)
    table.sort(names)

    for _, sLib in ipairs(names) do
        if sFilter == "" or sLib:lower():find(sFilter, 1, true) then
            local fns = {}
            pcall(function()
                for k, v in pairs(_G[sLib]) do
                    if type(k) == "string" and type(v) == "function" then table.insert(fns, k) end
                end
            end)

            if #fns > 0 then
                nLib = nLib + 1
                table.sort(fns)
                table.insert(out, string.format("UILIB|%s|%d", sLib, #fns))

                for i, sFn in ipairs(fns) do
                    if i > UI_FN_CAP then
                        table.insert(out, string.format("UITRUNCATED|%s|%d of %d shown",
                            sLib, UI_FN_CAP, #fns))
                        nCut = nCut + 1
                        break
                    end
                    nFn = nFn + 1
                    local hint = SaveHint(sFn)
                    if hint then
                        nSave = nSave + 1
                        table.insert(out, string.format("UISAVE|%s|%s|%s", sLib, sFn, hint))
                    else
                        table.insert(out, string.format("UIFN|%s|%s", sLib, sFn))
                    end
                end
            end
        end
    end

    -- Which addons can persist anything at all. An addon with no OnSave keeps nothing across a
    -- reload BY DESIGN, so "it did not save" is expected there and is not worth chasing.
    --
    -- NOT Apollo.GetAddons - THAT CALL DOES NOT EXIST on 16042. This command's own output proved
    -- it: Apollo exposes GetAddon, GetAddonInfo, GetAddonPods and RegisterAddon, and no plural
    -- form. Try() returned nil, "or {}" made it an empty table, and the loop ran zero times while
    -- reporting nothing wrong. ScanApi has used the same non-existent call since it was written,
    -- so its addon list has been silently empty the whole time and still read as captured.
    --
    -- So this walks _G for addon-SHAPED tables instead: an addon registers itself and carries
    -- OnLoad, and the two save hooks are what the question is actually about. That can miss an
    -- addon that keeps itself out of _G - stated here rather than discovered later, because the
    -- previous version of this comment would have been "enumerates every addon".
    local nAddon = 0
    for _, sLib in ipairs(names) do
        local t = _G[sLib]
        local bLoad    = Has(t, "OnLoad")
        local bSave    = Has(t, "OnSave")
        local bRestore = Has(t, "OnRestore")
        if bLoad or bSave or bRestore then
            nAddon = nAddon + 1
            table.insert(out, string.format("UIADDON|%s|OnLoad=%s|OnSave=%s|OnRestore=%s",
                sLib, tostring(bLoad), tostring(bSave), tostring(bRestore)))
        end
    end
    if nAddon == 0 then
        -- never report silence as a result
        table.insert(out, "UIADDON|NONE FOUND|the _G walk matched nothing addon-shaped")
    end

    self.tUi = out

    Print(string.format("%s UI map: %d libraries, %d functions, %d save-shaped, %d addon-shaped.",
        PREFIX, nLib, nFn, nSave, nAddon))
    if nCut > 0 then
        Print(string.format("%s  %d library(s) truncated at %d - see UITRUNCATED rows.",
            PREFIX, nCut, UI_FN_CAP))
    end
    Print(PREFIX .. " /reloadui to write it to disk.")
end

function NexusIntrospect:OnUiSlash(cmd, args)
    self:DumpUi(args)
end

function NexusIntrospect:OnSnapSlash(cmd, args)
    self:Snapshot(args)
end

function NexusIntrospect:OnAbilitySlash()
    self:DumpAbilities()
end

function NexusIntrospect:OnAmpSlash()
    self:DumpAmps()
end

function NexusIntrospect:OnTierSlash()
    self:DumpTiers()
end

function NexusIntrospect:OnItemSlash(cmd, args)
    self:StartCatalog(args)
end

function NexusIntrospect:OnAllSlash(cmd, args)
    self:EnableAll(args)
end

function NexusIntrospect:OnSlash(cmd, args)
    args = (args or ""):lower()

    if args == "api" then
        self:ScanApi()
        Print(string.format("%s %d namespaces, %d enums, %d addons",
            PREFIX, self:Count(self.tApi), self:Count(self.tEnums), #self.tAddons))

    elseif args == "events" then
        Print(string.format("%s %d distinct events observed", PREFIX, self:Count(self.tSeenEvents)))

    else
        Print(string.format("%s api=%d enums=%d events=%d abilities=%d amps=%d tiers=%d catalog=%d",
            PREFIX, self:Count(self.tApi), self:Count(self.tEnums), self:Count(self.tSeenEvents),
            #self.tAbilities, #self.tAmps, #self.tTiers, #self.tCatalog))
        Print(PREFIX .. " /reloadui writes it all to disk.")
    end
end

local NexusIntrospectInst = NexusIntrospect:new()
NexusIntrospectInst:Init()
