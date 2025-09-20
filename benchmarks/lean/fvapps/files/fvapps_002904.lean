-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome (start_num : Int) (size : Int) : List Int := sorry

def isPalindrome (n : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>