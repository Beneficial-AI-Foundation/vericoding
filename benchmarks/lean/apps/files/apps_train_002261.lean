-- <vc-helpers>
-- </vc-helpers>

def find_max_three_block_palindrome (n : Nat) (arr : List Nat) : Nat := sorry

theorem output_bounded_by_input_length 
  (n : Nat) (arr : List Nat) (h1 : 1 ≤ n) (h2 : n ≤ 100) (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) :
  let result := find_max_three_block_palindrome n arr
  1 ≤ result ∧ result ≤ n := sorry

theorem palindrome_length_at_least_max_count
  (n : Nat) (arr : List Nat) (h1 : 1 ≤ n) (h2 : n ≤ 100) (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) :
  let result := find_max_three_block_palindrome n arr
  let max_count := (List.foldl (fun acc x => max acc (arr.filter (· = x)).length) 0 arr)
  result ≥ max_count := sorry

theorem all_same_number_gives_full_length
  (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 100) :
  let arr := List.replicate n 1
  find_max_three_block_palindrome n arr = n := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_max_three_block_palindrome 8 [1, 1, 2, 2, 3, 2, 1, 1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_three_block_palindrome 4 [1, 10, 10, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_three_block_palindrome 3 [1, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded