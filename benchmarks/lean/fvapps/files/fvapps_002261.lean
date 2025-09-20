-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_three_block_palindrome (n : Nat) (arr : List Nat) : Nat := sorry

theorem output_bounded_by_input_length 
  (n : Nat) (arr : List Nat) (h1 : 1 ≤ n) (h2 : n ≤ 100) (h3 : arr.length = n)
  (h4 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) :
  let result := find_max_three_block_palindrome n arr
  1 ≤ result ∧ result ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>