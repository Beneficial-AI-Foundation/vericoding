def is_prime (n : Nat) : Bool := sorry

def find_max_prime_factor (nums : List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def get_prime_factors_count (nums : List Nat) : List (Nat × Nat) := sorry

theorem result_is_prime_factor 
  (nums : List Nat) 
  (h1 : ∀ x ∈ nums, x ≥ 2 ∧ x ≤ 10000) 
  (h2 : nums.length > 0) :
  let result := find_max_prime_factor nums
  let factors := get_prime_factors_count nums
  ∃ freq, (result, freq) ∈ factors := sorry

theorem all_same_prime
  (nums : List Nat)
  (h : ∀ x ∈ nums, x = 2)
  (h2 : nums.length > 0) :
  find_max_prime_factor nums = 2 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_max_prime_factor [3, 2, 15, 6, 8, 5, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_prime_factor [4, 8, 12, 15]

/-
info: 11
-/
-- #guard_msgs in
-- #eval find_max_prime_factor [3, 5, 7, 11]

-- Apps difficulty: interview
-- Assurance level: unguarded