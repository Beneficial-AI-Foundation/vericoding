-- <vc-helpers>
-- </vc-helpers>

def switch_lights (input : List Nat) : List Nat := sorry

theorem switch_lights_binary_only {states : List Nat} 
  (h : ∀ x ∈ states, x = 0 ∨ x = 1) : 
  let result := switch_lights states
  (∀ x ∈ result, x = 0 ∨ x = 1) ∧ result.length = states.length := sorry

theorem switch_lights_preserves_input {states : List Nat}
  (h : ∀ x ∈ states, x = 0 ∨ x = 1) :
  switch_lights states ≠ states := sorry

theorem switch_lights_empty :
  switch_lights [] = [] := sorry

/-
info: [0, 1, 0, 1, 0]
-/
-- #guard_msgs in
-- #eval switch_lights [1, 1, 1, 1, 1]

/-
info: [0, 0]
-/
-- #guard_msgs in
-- #eval switch_lights [0, 0]

/-
info: [1, 1, 1, 0, 0, 1, 1, 0]
-/
-- #guard_msgs in
-- #eval switch_lights [1, 0, 0, 1, 0, 1, 0, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded