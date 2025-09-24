-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def char_attribute : Int → CharAttribute := sorry

theorem char_attribute_types (score : Int) :
  let result := char_attribute score
  0 ≤ score → score ≤ 100 →
  True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spell_level_constraints (score : Int) :
  let result := char_attribute score
  0 ≤ score → score ≤ 100 →
  (score = 0 → result.maximum_spell_level = -1) ∧
  (score ≠ 0 → 
    let modifier := score / 2 - 5
    result.maximum_spell_level ≤ 9 ∧
    (modifier < 0 → result.maximum_spell_level = -1) ∧
    (score ≥ 10 → result.maximum_spell_level ≤ score - 10)) := sorry

theorem extra_spells_properties (score : Int) :
  let result := char_attribute score 
  0 ≤ score → score ≤ 100 →
  result.extra_spells.length ≤ 9 ∧
  (∀ x ∈ result.extra_spells, x > 0) ∧
  (∀ i j, i < j → j < result.extra_spells.length → 
    match result.extra_spells.get? i, result.extra_spells.get? j with
    | some x, some y => x ≥ y
    | _, _ => true) := sorry

/-
info: {'modifier': 0, 'maximum_spell_level': -1, 'extra_spells': []}
-/
-- #guard_msgs in
-- #eval char_attribute 0

/-
info: {'modifier': 0, 'maximum_spell_level': 0, 'extra_spells': []}
-/
-- #guard_msgs in
-- #eval char_attribute 10

/-
info: {'modifier': 5, 'maximum_spell_level': 9, 'extra_spells': [2, 1, 1, 1, 1]}
-/
-- #guard_msgs in
-- #eval char_attribute 20
-- </vc-theorems>