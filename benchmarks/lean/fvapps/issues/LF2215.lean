-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_seconds_to_nondecreasing (n : Nat) (arr : Array Int) : Nat := sorry

theorem already_nondecreasing {n : Nat} {arr : Array Int} 
  (h1 : n ≥ 2)
  (h2 : n ≤ 100)
  (h3 : arr.size = n)
  (h4 : ∀ i j, i < j → j < n → arr[i]! ≤ arr[j]!) 
  : min_seconds_to_nondecreasing n arr = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_valid {n : Nat} {arr : Array Int}
  (h1 : arr.size = n)
  (h2 : n ≥ 2)
  (h3 : n ≤ 100)
  (h4 : ∀ x, x ∈ arr.data → -1000 ≤ x ∧ x ≤ 1000)
  : let result := min_seconds_to_nondecreasing n arr
    result ≥ 0 ∧ ∀ i j, i < j → j < n → arr[i]! ≤ arr[j]! := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_seconds_to_nondecreasing 4 #[1, 7, 6, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_seconds_to_nondecreasing 5 #[1, 2, 3, 4, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_seconds_to_nondecreasing 2 #[0, -4]
-- </vc-theorems>