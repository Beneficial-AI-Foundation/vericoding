-- <vc-helpers>
-- </vc-helpers>

def palindrome (start_num : Int) (size : Int) : List Int := sorry

def isPalindrome (n : Int) : Bool := sorry

theorem palindrome_empty_size :
  ∀ start_num : Int, palindrome start_num 0 = [] := sorry

theorem palindrome_valid_size :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size > 0 →
  List.length (palindrome start_num size) = size := sorry

theorem palindrome_elements_are_ints :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size > 0 →
  ∀ x, x ∈ palindrome start_num size → x ∈ palindrome start_num size := sorry

theorem palindrome_elements_are_palindromes :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size > 0 →
  ∀ x, x ∈ palindrome start_num size → isPalindrome x = true := sorry

theorem palindrome_elements_ordered :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size > 0 →
  ∀ i j, i < j → 
  i < List.length (palindrome start_num size) → 
  j < List.length (palindrome start_num size) →
  (palindrome start_num size).get ⟨i, sorry⟩ ≤ (palindrome start_num size).get ⟨j, sorry⟩ := sorry

theorem palindrome_elements_minimum :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size > 0 →
  ∀ x, x ∈ palindrome start_num size → x ≥ max start_num 11 := sorry

theorem palindrome_invalid_negative_num :
  ∀ start_num size : Int,
  start_num < 0 →
  size ≥ 0 →
  palindrome start_num size = [] := sorry

theorem palindrome_invalid_negative_size :
  ∀ start_num size : Int,
  start_num ≥ 0 →
  size < 0 →
  palindrome start_num size = [] := sorry

/-
info: [11, 22, 33, 44]
-/
-- #guard_msgs in
-- #eval palindrome 6 4

/-
info: [77]
-/
-- #guard_msgs in
-- #eval palindrome 75 1

/-
info: [101, 111]
-/
-- #guard_msgs in
-- #eval palindrome 101 2

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval palindrome "ACCDDCCA" 3

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval palindrome 773 "1551"

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval palindrome -4505 15

-- Apps difficulty: introductory
-- Assurance level: unguarded