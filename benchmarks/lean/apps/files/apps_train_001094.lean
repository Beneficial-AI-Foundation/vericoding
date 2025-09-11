-- <vc-preamble>
def find_frequent_numbers (n : Nat) (k : Nat) (arr : List Nat) : List Nat :=
  sorry

def count {α} [BEq α] (as : List α) (a : α) : Nat :=
  sorry

def isSorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueSort (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem frequent_numbers_properties 
  (n : Nat) (k : Nat) (arr : List Nat) 
  (h1 : n = arr.length)
  (h2 : k ≤ 19)
  (h3 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 20) :
  let result := find_frequent_numbers n k arr
  -- Result contains only numbers appearing more than k times
  ∀ num ∈ result, count arr num > k
  -- All numbers appearing more than k times are in result  
  ∧ ∀ num ∈ arr, count arr num > k → num ∈ result
  -- Result is sorted
  ∧ isSorted result
  -- All result elements exist in input array
  ∧ ∀ num ∈ result, num ∈ arr :=
  sorry

theorem k_zero_returns_unique
  (n : Nat) (arr : List Nat)
  (h1 : n = arr.length)
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 20) :
  find_frequent_numbers n 0 arr = uniqueSort arr :=
  sorry

theorem large_k_returns_empty
  (n : Nat) (k extra : Nat) (arr : List Nat)
  (h1 : n = arr.length)
  (h2 : k = n + extra)
  (h3 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 20) :
  find_frequent_numbers n k arr = [] :=
  sorry

/-
info: [2, 5]
-/
-- #guard_msgs in
-- #eval find_frequent_numbers 5 1 [5, 2, 1, 2, 5]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval find_frequent_numbers 6 2 [1, 1, 1, 2, 2, 3]

/-
info: [1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval find_frequent_numbers 4 0 [4, 2, 3, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded