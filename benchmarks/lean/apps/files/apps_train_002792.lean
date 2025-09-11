-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List Int) (div : Int) : List Int := sorry

theorem solve_output_length {nums : List Int} {div : Int} (h : div > 0) :
  (solve nums div).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_elements_geq_input {nums : List Int} {div : Int} (h : div > 0) :
  ∀ (i : Nat), i < nums.length → 
    ((solve nums div).get ⟨i, by sorry⟩) ≥ (nums.get ⟨i, by sorry⟩) := sorry

theorem solve_diff_less_than_div {nums : List Int} {div : Int} (h : div > 0) :
  ∀ (i : Nat), i < nums.length →
    ((solve nums div).get ⟨i, by sorry⟩) - (nums.get ⟨i, by sorry⟩) < div := sorry

theorem solve_div_one {nums : List Int} :
  solve nums 1 = nums := sorry

theorem solve_empty {div : Int} (h : div > 0) :
  solve [] div = [] := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve [2, 7, 5, 9, 100, 34, 32, 0] 3

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve [] 2

/-
info: expected3
-/
-- #guard_msgs in
-- #eval solve [1000, 999, 998, 997] 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded