def find_smallest_divisor (nums : List Nat) (threshold : Nat) : Nat :=
  sorry

def ceil_div (a b : Nat) : Nat :=
  (a + b - 1) / b

-- <vc-helpers>
-- </vc-helpers>

def list_max (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => List.foldl max x xs

theorem single_element_case {nums : List Nat} {threshold : Nat} 
  (h1 : nums.length = 1) 
  (h2 : threshold > 0)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000000)
  (h4 : threshold ≤ 1000000) :
  find_smallest_divisor nums threshold = ceil_div nums[0] threshold :=
sorry

theorem result_bounded {nums : List Nat} {threshold : Nat}
  (h1 : nums.length > 0)
  (h2 : nums.length ≤ 10)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100)
  (h4 : 1 ≤ threshold ∧ threshold ≤ 100) :
  1 ≤ find_smallest_divisor nums threshold ∧ 
  find_smallest_divisor nums threshold ≤ list_max nums :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_smallest_divisor [1, 2, 5, 9] 6

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_smallest_divisor [2, 3, 5, 7, 11] 11

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_smallest_divisor [19] 5

-- Apps difficulty: interview
-- Assurance level: unguarded