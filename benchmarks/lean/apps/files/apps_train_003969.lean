-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Movement := List (Int × Nat × Nat)

def solomonsQuest (moves : Movement) : Int × Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solomons_quest_outputs_pair (moves : Movement) :
  ∃ x y : Int, solomonsQuest moves = (x, y) := sorry

theorem solomons_quest_valid_output (moves : Movement) :
  let result := solomonsQuest moves
  (result.1 : Int) = result.1 ∧ (result.2 : Int) = result.2 := sorry

/-
info: [346, 40]
-/
-- #guard_msgs in
-- #eval solomons_quest [[1, 3, 5], [2, 0, 10], [-3, 1, 4], [4, 2, 4], [1, 1, 5], [-3, 0, 12], [2, 1, 12], [-2, 2, 6]]

/-
info: [68, 800]
-/
-- #guard_msgs in
-- #eval solomons_quest [[4, 0, 8], [2, 1, 2], [1, 0, 5], [-3, 3, 16], [2, 2, 2], [-1, 1, 7], [0, 0, 5], [-4, 3, 14]]

/-
info: [-600, -244]
-/
-- #guard_msgs in
-- #eval solomons_quest [[1, 1, 20], [1, 2, 30], [1, 3, 8], [1, 0, 2], [1, 1, 6], [1, 2, 4], [1, 3, 6], [-7, 0, 100]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded