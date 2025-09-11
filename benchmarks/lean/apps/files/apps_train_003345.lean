-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flipping_game (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flipping_game_result_bounded (nums: List Nat) :
  nums.all (fun x => x = 0 ∨ x = 1) →
  flipping_game nums ≤ nums.length := by
  sorry

theorem flipping_game_result_range (nums: List Nat) :
  nums.all (fun x => x = 0 ∨ x = 1) →
  0 ≤ flipping_game nums ∧ flipping_game nums ≤ nums.length := by
  sorry

theorem flipping_game_all_zeros (n: Nat) :
  let zeros := List.replicate n 0
  flipping_game zeros = zeros.length := by
  sorry

theorem flipping_game_basic_cases :
  flipping_game [0] = 1 ∧
  flipping_game [0,0] = 2 ∧
  flipping_game [1,0,0] = 3 := by
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval flipping_game [1, 0, 0, 1, 0, 0]

/-
info: 4
-/
-- #guard_msgs in
-- #eval flipping_game [1, 0, 0, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval flipping_game [1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded