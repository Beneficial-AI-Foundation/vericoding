-- <vc-preamble>
def KnownMonsters := [
    "werewolf", "vampire", "wendigo", "shapeshifter", "angel", "demon",
    "ghost", "dragon", "djinn", "pagan god", "leviathan", "ghoul",
    "jefferson starship", "reaper", "rugaru", "skinwalker", "phoenix", "witch"
]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bob (s : String) : String := sorry

theorem always_returns_string_with_idjits (s : String) :
  let result := bob s
  result.endsWith ", idjits!" := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_monsters_get_specific_response (monster : String) :
  monster ∈ KnownMonsters →
  let result := bob monster
  result ≠ "I have friggin no idea yet, idjits!" ∧
  result.endsWith ", idjits!" := by sorry

theorem unknown_monsters_get_default_response (s : String) :
  s ∉ KnownMonsters →
  bob s = "I have friggin no idea yet, idjits!" := by sorry

theorem similar_monsters_same_killing_method_werewolf_shapeshifter :
  let werewolfResult := bob "werewolf"
  let shapeshifterResult := bob "shapeshifter"
  werewolfResult.startsWith "Silver knife" ∧
  shapeshifterResult.startsWith "Silver knife" := by sorry
-- </vc-theorems>