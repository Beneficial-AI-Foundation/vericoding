-- <vc-preamble>
def List.minimum (l : List Nat) : Nat := 
  sorry

def List.sort (l: List Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_common_divisors (nums: List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_common_divisors_contains_prime_factors {nums: List Nat} 
  (h1: nums.length ≥ 2)
  (h2: ∀ n ∈ nums, n ≥ 1 ∧ n ≤ 100) :
  ∀ i: Nat, 2 ≤ i ∧ i ≤ List.minimum nums → 
  (∀ n ∈ nums, n % i = 0) →
  (∀ j, 2 ≤ j ∧ j < i → i % j ≠ 0) →
  i ∈ find_common_divisors nums :=
sorry

theorem find_common_divisors_sorted {nums: List Nat}
  (h1: nums.length ≥ 2)
  (h2: ∀ n ∈ nums, n ≥ 2 ∧ n ≤ 1000) :
  find_common_divisors nums = List.sort (find_common_divisors nums) :=
sorry

theorem find_common_divisors_greater_than_one {nums: List Nat}
  (h1: nums.length ≥ 2)
  (h2: ∀ n ∈ nums, n ≥ 2 ∧ n ≤ 1000) :
  ∀ x ∈ find_common_divisors nums, x > 1 :=
sorry

theorem find_common_divisors_bounded_by_min {nums: List Nat}
  (h1: nums.length ≥ 2)
  (h2: ∀ n ∈ nums, n ≥ 2 ∧ n ≤ 1000) :
  ∀ x ∈ find_common_divisors nums, x ≤ List.minimum nums :=
sorry

/-
info: [2, 4]
-/
-- #guard_msgs in
-- #eval find_common_divisors [38, 6, 34]

/-
info: [2, 3, 6]
-/
-- #guard_msgs in
-- #eval find_common_divisors [12, 18, 24]

/-
info: [5]
-/
-- #guard_msgs in
-- #eval find_common_divisors [10, 15, 20]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded