-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_interesting (number : Nat) (awesome_phrases : Array Nat) : Nat :=
  sorry

def isPalindrome (n : Nat) : Bool :=
  sorry

def isRoundNumber (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_interesting_result_valid (n : Nat) (phrases : Array Nat) :
  let result := is_interesting n phrases
  result = 0 ∨ result = 1 ∨ result = 2 :=
sorry

theorem small_numbers_boring (n : Nat) (h : n < 98) :
  is_interesting n #[] = 0 :=
sorry

theorem awesome_phrases_direct_match (n : Nat) (phrases : Array Nat)
  (h1 : n ≥ 100) (h2 : phrases.contains n = true) :
  is_interesting n phrases = 2 :=
sorry

theorem awesome_phrases_nearby_match (n : Nat) (phrases : Array Nat)
  (h1 : n ≥ 98) (h2 : phrases.contains (n + 1) = true ∨ phrases.contains (n + 2) = true) :
  is_interesting n phrases ≥ 1 :=
sorry

theorem palindrome_direct_match (n : Nat) (h1 : n ≥ 100)
  (h2 : isPalindrome n = true) :
  is_interesting n #[] = 2 :=
sorry

theorem palindrome_nearby_match (n : Nat) (h1 : n ≥ 98)
  (h2 : isPalindrome (n + 1) = true ∨ isPalindrome (n + 2) = true)
  (h3 : n + 1 ≥ 100 ∨ n + 2 ≥ 100) :
  is_interesting n #[] ≥ 1 :=
sorry

theorem incrementing_sequences (n : Nat)
  (h : n = 123 ∨ n = 234 ∨ n = 345 ∨ n = 456 ∨ n = 567 ∨ n = 678 ∨ n = 789 ∨ n = 890) :
  is_interesting n #[] = 2 :=
sorry

theorem decrementing_sequences (n : Nat)
  (h : n = 987 ∨ n = 876 ∨ n = 765 ∨ n = 654 ∨ n = 543 ∨ n = 432 ∨ n = 321) :
  is_interesting n #[] = 2 :=
sorry
-- </vc-theorems>