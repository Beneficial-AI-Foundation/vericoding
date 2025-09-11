-- <vc-preamble>
def find_length_of_lcis (nums : List Int) : Nat := sorry

theorem lcis_length_properties (nums : List Int) : 
  let result := find_length_of_lcis nums
  result ≥ 0 ∧ 
  result ≤ nums.length ∧
  (nums.length = 0 → result = 0) ∧ 
  (nums.length > 0 → result ≥ 1) := sorry

def is_strictly_increasing (nums : List Int) (i : Nat) : Bool :=
  i > 0 && i < nums.length && nums[i]! > nums[i-1]!
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_max_increasing (nums : List Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 3
-/
-- #guard_msgs in
-- #eval find_length_of_lcis [1, 3, 5, 4, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_length_of_lcis [2, 2, 2, 2, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_length_of_lcis [1, 3, 5, 7]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible