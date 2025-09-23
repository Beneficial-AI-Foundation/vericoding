-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | h::t => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_divisible_by_length (nums: List Nat) (h: nums.length > 0) :
  solution nums % nums.length = 0 :=
sorry

theorem solution_gcd_divides_all (nums: List Nat) (h: nums.length > 0) :
  ∀ n ∈ nums, n % (solution nums / nums.length) = 0 :=
sorry

theorem solution_identical_elements (n: Nat) (len: Nat) (h: len > 0) :
  solution (List.replicate len n) = n * len :=
sorry

theorem solution_single_element (n: Nat) :
  solution [n] = n :=
sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval solution [6, 9, 21]

/-
info: 12
-/
-- #guard_msgs in
-- #eval solution [30, 12]

/-
info: 12
-/
-- #guard_msgs in
-- #eval solution [4, 16, 24]
-- </vc-theorems>