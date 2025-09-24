-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x :: xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def house_numbers_sum (nums : List Nat) : Nat := sorry

theorem house_numbers_sum_non_negative {nums : List Nat} (h : 0 ∈ nums) :
  house_numbers_sum nums ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem house_numbers_sum_ignore_after_zero {nums modified : List Nat} 
  (h : 0 ∈ nums)
  (h2 : modified.take (nums.indexOf 0 + 1) = nums.take (nums.indexOf 0 + 1)) :
  house_numbers_sum modified = house_numbers_sum nums := sorry

theorem house_numbers_sum_ones (n : Nat) :
  house_numbers_sum (List.replicate n 1 ++ [0]) = n := sorry

theorem house_numbers_sum_zero :
  house_numbers_sum [0] = 0 := sorry

theorem house_numbers_sum_zero_prefix :
  house_numbers_sum [0, 1, 2, 3] = 0 := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval house_numbers_sum [5, 1, 2, 3, 0, 1, 5, 0, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval house_numbers_sum [0, 1, 2, 3]

/-
info: 13
-/
-- #guard_msgs in
-- #eval house_numbers_sum [4, 2, 1, 6, 0, 3, 2]
-- </vc-theorems>