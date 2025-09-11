-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_subsequence_removal (n : Nat) (arr : List Nat) : Nat := sorry

def is_increasing (lst : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_bounds (n : Nat) (arr : List Nat) : 
  arr.length = n →
  let result := solve_subsequence_removal n arr
  result ≥ 0 ∧ result ≤ n * (n+1) / 2 := sorry

theorem strictly_increasing_sequence (n : Nat) :
  n > 0 →
  let arr := List.range n 
  solve_subsequence_removal n arr = n * (n+1) / 2 - 1 := sorry

theorem duplicate_elements (n : Nat) (arr : List Nat) :
  n > 0 →
  let all_ones := List.replicate n 1
  let result := solve_subsequence_removal n all_ones
  result ≥ 0 ∧ result ≤ n * (n+1) / 2 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_subsequence_removal 3 [1, 1, 2]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_subsequence_removal 4 [2, 4, 3, 5]

/-
info: 14
-/
-- #guard_msgs in
-- #eval solve_subsequence_removal 5 [1, 2, 3, 4, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded