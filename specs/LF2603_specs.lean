-- <vc-preamble>
def largest_arrangement (nums : List Nat) : Nat :=
  sorry

@[simp]

def numDigits (n : Nat) : Nat :=
  sorry

@[simp]

def getDigits (n : Nat) : List Nat :=
  sorry

@[simp]

def sumList (xs : List Nat) : Nat :=
  sorry

@[simp]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDigits (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_arrangement_length_preservation
  (nums : List Nat)
  (h : nums.length > 0)
  (h2 : ∀ n ∈ nums, n ≤ 999) :
  numDigits (largest_arrangement nums) = sumList (nums.map numDigits)
  := sorry

theorem largest_arrangement_uses_same_digits
  (nums : List Nat)
  (h : nums.length > 0)
  (h2 : ∀ n ∈ nums, n ≤ 999) :
  ∀ d, countDigits d = countDigits d →
  (d ∈ getDigits (largest_arrangement nums) ↔ d ∈ (nums.map getDigits).join)
  := sorry

theorem largest_arrangement_is_nat
  (nums : List Nat) 
  (h : nums.length > 0)
  (h2 : ∀ n ∈ nums, n ≤ 999) :
  largest_arrangement nums ≥ 0
  := sorry

theorem largest_arrangement_greater_than_components
  (nums : List Nat)
  (h : nums.length > 1)
  (h2 : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 999) :
  ∀ n ∈ nums, largest_arrangement nums ≥ n
  := sorry

/-
info: 8504145
-/
-- #guard_msgs in
-- #eval largest_arrangement [4, 50, 8, 145]

/-
info: 7440
-/
-- #guard_msgs in
-- #eval largest_arrangement [4, 40, 7]

/-
info: 95655021
-/
-- #guard_msgs in
-- #eval largest_arrangement [5, 2, 1, 9, 50, 56]
-- </vc-theorems>