-- <vc-preamble>
def isSorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_frequent_numbers (n : Nat) (k : Nat) (arr : List Nat) : List Nat :=
  sorry

def count {α} [BEq α] (as : List α) (a : α) : Nat :=
  sorry

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

  ∀ num ∈ result, count arr num > k

  ∧ ∀ num ∈ arr, count arr num > k → num ∈ result

  ∧ isSorted result

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
-- </vc-theorems>