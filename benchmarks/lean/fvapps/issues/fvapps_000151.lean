-- <vc-preamble>
def List.sum (l: List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def makesquare (nums: List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem makesquare_min_length 
  (nums: List Nat) (h: nums.length < 4) : 
  makesquare nums = false := 
  sorry

theorem makesquare_sum_not_div_four
  (nums: List Nat) (h: (List.sum nums % 4) ≠ 0) :
  makesquare nums = false := 
  sorry

theorem makesquare_element_too_large 
  (nums: List Nat) (h: ∃ x ∈ nums, x > List.sum nums / 4) :
  makesquare nums = false :=
  sorry

theorem makesquare_equal_elements 
  (n: Nat) (nums: List Nat) 
  (h1: nums.length % 4 = 0)
  (h2: ∀ x ∈ nums, x = n) :
  makesquare nums = true :=
  sorry 

theorem makesquare_identical_elements
  (n: Nat) :
  makesquare [n,n,n,n] = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval makesquare [1, 1, 2, 2, 2]

/-
info: False
-/
-- #guard_msgs in
-- #eval makesquare [3, 3, 3, 3, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval makesquare [1, 2, 3, 4, 5]
-- </vc-theorems>