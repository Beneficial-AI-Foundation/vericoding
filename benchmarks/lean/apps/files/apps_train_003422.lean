def KnownMonsters := [
    "werewolf", "vampire", "wendigo", "shapeshifter", "angel", "demon",
    "ghost", "dragon", "djinn", "pagan god", "leviathan", "ghoul",
    "jefferson starship", "reaper", "rugaru", "skinwalker", "phoenix", "witch"
]

-- <vc-helpers>
-- </vc-helpers>

def bob (s : String) : String := sorry

theorem always_returns_string_with_idjits (s : String) :
  let result := bob s
  result.endsWith ", idjits!" := by sorry

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

/-
info: 'Behead it with a machete, idjits!'
-/
-- #guard_msgs in
-- #eval bob "vampire"

/-
info: 'It depends on which one it is, idjits!'
-/
-- #guard_msgs in
-- #eval bob "pagan god"

/-
info: 'I have friggin no idea yet, idjits!'
-/
-- #guard_msgs in
-- #eval bob "werepuppy"

-- Apps difficulty: introductory
-- Assurance level: unguarded