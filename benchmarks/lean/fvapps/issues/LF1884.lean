-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem valid_fibonacci_sequences 
  (nums: List Nat)
  (h1: nums.length ≥ 3)
  (h2: nums.length ≤ 10) 
  (h3: ∀ n ∈ nums, isValidInt n)
  (h4: isFibonacciSequence nums) :
  let s := sequenceToString nums
  let result := splitFibonacci s
  (result.length ≥ 3 ∧ 
   isFibonacciSequence result ∧
   sequenceToString result = s ∧
   ∀ x ∈ result, isValidInt x) :=
  sorry

theorem arbitrary_strings
  (s: String)
  (h1: s.length ≥ 1)
  (h2: s.length ≤ 20)
  (h3: ∀ c ∈ s.data, c.isDigit) :
  let result := splitFibonacci s
  (result = [] ∨ 
   (result.length ≥ 3 ∧
    isFibonacciSequence result ∧
    sequenceToString result = s ∧
    ∀ x ∈ result, isValidInt x)) :=
  sorry

theorem single_digits
  (d: Nat)
  (h1: d ≥ 1)
  (h2: d ≤ 9) :
  splitFibonacci (toString d) = [] :=
  sorry

/-
info: [123, 456, 579]
-/
-- #guard_msgs in
-- #eval split_fibonacci "123456579"

/-
info: [1, 1, 2, 3, 5, 8, 13]
-/
-- #guard_msgs in
-- #eval split_fibonacci "11235813"

/-
info: []
-/
-- #guard_msgs in
-- #eval split_fibonacci "112358130"
-- </vc-theorems>