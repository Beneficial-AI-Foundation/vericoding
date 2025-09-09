-- <vc-helpers>
-- </vc-helpers>

def find_max_palindrome_subsequence (n : Nat) (arr : List Nat) : Nat :=
sorry

theorem palindrome_subsequence_properties (arr : List Nat) (n : Nat)
  (h : n = arr.length) (h2 : arr.length > 0) (h3 : ∀ x ∈ arr, x ≤ 200) :
  let result := find_max_palindrome_subsequence n arr
  (result ≥ 0 ∧ 
   result ≤ n ∧
   (arr.length = 1 → result = 1)) :=
sorry

theorem palindrome_subsequence_identical_elements (arr : List Nat) (n : Nat) 
  (h : n = arr.length) (h2 : arr.length > 0) (h3 : ∀ x ∈ arr, x ≤ 200) :
  let identical_arr := List.replicate n (arr.head!)
  (find_max_palindrome_subsequence n identical_arr = n) :=
sorry

theorem palindrome_subsequence_reversed (arr : List Nat) (n : Nat)
  (h : n = arr.length) (h2 : arr.length > 0) (h3 : ∀ x ∈ arr, x ≤ 200) :
  find_max_palindrome_subsequence n arr = 
  find_max_palindrome_subsequence n arr.reverse :=
sorry

theorem palindrome_subsequence_alternating (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  let arr := List.range n |>.map (fun i => (i % 2) + 1)
  (find_max_palindrome_subsequence n arr ≥ n/2 + n%2) :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_max_palindrome_subsequence 8 [1, 1, 2, 2, 3, 2, 1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_palindrome_subsequence 3 [1, 3, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_palindrome_subsequence 4 [1, 10, 10, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded