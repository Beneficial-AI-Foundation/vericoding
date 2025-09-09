def min_moves_to_equal (nums : List Int) : Nat :=
  sorry

def abs (x : Int) : Nat :=
  sorry

def sort (nums : List Int) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def median (nums : List Int) : Int :=
  sorry

theorem min_moves_non_negative (nums : List Int) : 
  0 ≤ min_moves_to_equal nums := sorry

theorem min_moves_equal_median (nums : List Int) (h : nums ≠ []) : 
  min_moves_to_equal nums = nums.foldl (fun acc x => acc + abs (x - median nums)) 0 := sorry

theorem identical_nums_zero_moves (n : Int) (nums : List Int) (h : ∀ x ∈ nums, x = n) :
  min_moves_to_equal nums = 0 := sorry

theorem order_invariant (nums : List Int) :
  min_moves_to_equal nums = min_moves_to_equal (sort nums) := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_moves_to_equal [1, 2, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_moves_to_equal [1, 1, 1]

/-
info: 16
-/
-- #guard_msgs in
-- #eval min_moves_to_equal [1, 10, 2, 9]

-- Apps difficulty: interview
-- Assurance level: unguarded