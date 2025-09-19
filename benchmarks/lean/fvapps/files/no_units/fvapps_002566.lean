-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat := 
  s.data.filter (·= c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubstring (pattern : String) (s : String) : Bool := sorry

def number2words (n : Nat) : String := sorry

-- All outputs are strings containing only letters, spaces, and hyphens
-- </vc-definitions>

-- <vc-theorems>
theorem number2words_valid_chars (n : Nat) (h : n ≤ 999999) :
  ∃ s, number2words n = s ∧ 
  (∀ c ∈ s.data, c.isAlpha ∨ c = ' ' ∨ c = '-') := sorry

-- Numbers 0-19 are written as single words without spaces or hyphens 

theorem small_numbers_single_word (n : Nat) (h : n ≤ 19) :
  ∀ c ∈ (number2words n).data, c.isAlpha := sorry

-- Numbers 20-99: if multiple of 10 then no hyphen, else exactly one hyphen

theorem two_digit_numbers (n : Nat) (h1 : 20 ≤ n) (h2 : n ≤ 99) :
  if n % 10 = 0 
  then ∀ c ∈ (number2words n).data, c ≠ '-'
  else countChar (number2words n) '-' = 1 := sorry

-- Numbers 100-999 contain "hundred" and have one space if multiple of 100

theorem hundreds (n : Nat) (h1 : 100 ≤ n) (h2 : n ≤ 999) :
  isSubstring "hundred" (number2words n) ∧
  (if n % 100 = 0 
   then countChar (number2words n) ' ' = 1
   else True) := sorry

-- Numbers 1000-999999 contain exactly one "thousand"

theorem thousands (n : Nat) (h1 : 1000 ≤ n) (h2 : n ≤ 999999) :
  isSubstring "thousand" (number2words n) ∧
  countChar (number2words n) 't' = 1 := sorry

-- Zero is written as "zero"

theorem zero : number2words 0 = "zero" := sorry
-- </vc-theorems>