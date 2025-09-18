-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_digit_to_word (n : Nat) : String := sorry

def numbers_of_letters (n : Nat) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_digit_to_word_returns_valid_word 
  (n : Nat) (h : n ≤ 9) : 
  convert_digit_to_word n ∈ ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"] := sorry

-- Removed the string type check since it's implicit in Lean's type system

theorem numbers_of_letters_returns_nonempty
  (n : Nat) (h : n ≤ 999) : 
  numbers_of_letters n ≠ [] := sorry

theorem numbers_of_letters_ends_with_four
  (n : Nat) (h : n ≤ 999) :
  numbers_of_letters n ≠ [] → 
  List.getLast (numbers_of_letters n) (by exact numbers_of_letters_returns_nonempty n h) = "four" := sorry

theorem numbers_of_letters_length_bounded
  (n : Nat) (h : n ≤ 999) :
  (numbers_of_letters n).length ≤ 10 := sorry

theorem numbers_of_letters_first_element
  (n : Nat) (h : n ≤ 999) :
  numbers_of_letters n ≠ [] → 
  (numbers_of_letters n).head! = convert_digit_to_word n := sorry
-- </vc-theorems>