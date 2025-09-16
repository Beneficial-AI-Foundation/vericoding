-- <vc-preamble>
def get_num (arr : List Nat) : List Nat := sorry
def is_prime (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum (l : List Nat) (h : l.length > 0) : Nat := sorry
def product (l : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_num_basic_properties {arr : List Nat} (h1 : arr.length > 0) 
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 20) :
  let result := get_num arr
  result.length = 4 ∧ 
  result[0]! = product arr ∧
  result[2]! = minimum arr h1 ∧
  result[3]! = result[0]! / result[2]! := sorry

theorem get_num_small_factors {arr : List Nat}
  (h1 : 2 ≤ arr.length ∧ arr.length ≤ 3)
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 7) :
  let result := get_num arr
  result[0]! > 0 ∧
  result[1]! ≥ 0 ∧
  result[2]! ≤ minimum arr (by exact Nat.zero_lt_of_lt h1.left) ∧ 
  result[0]! % result[2]! = 0 := sorry

/-
info: [150, 11, 2, 75]
-/
-- #guard_msgs in
-- #eval get_num [2, 3, 5, 5]

/-
info: [378, 15, 2, 189]
-/
-- #guard_msgs in
-- #eval get_num [2, 3, 3, 3, 7]

/-
info: [23400, 71, 2, 11700]
-/
-- #guard_msgs in
-- #eval get_num [2, 13, 2, 5, 2, 5, 3, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded