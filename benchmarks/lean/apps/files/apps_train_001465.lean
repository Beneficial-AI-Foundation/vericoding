-- <vc-helpers>
-- </vc-helpers>

def find_longest_xor_subsequence (n : Nat) (arr : List Nat) : Nat :=
  sorry

theorem length_bounds (n : Nat) (arr : List Nat) (h : arr.length = n) (h1 : n > 0) :
  let result := find_longest_xor_subsequence n arr
  1 ≤ result ∧ result ≤ n :=
  sorry

theorem same_values_equal_length (n : Nat) (arr : List Nat) (h : arr.length = n) (h1 : n > 0) :
  let first := arr.head?
  let repeated := List.replicate n (first.get!)
  find_longest_xor_subsequence n repeated = n :=
  sorry

theorem all_zeros_case (n : Nat) (arr : List Nat) (h : arr.length = n) (h1 : n > 0) :
  let zeros := List.replicate n 0
  find_longest_xor_subsequence n zeros = n :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_longest_xor_subsequence 8 [1, 200, 3, 0, 400, 4, 1, 7]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_longest_xor_subsequence 4 [1, 2, 3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_longest_xor_subsequence 3 [5, 5, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded