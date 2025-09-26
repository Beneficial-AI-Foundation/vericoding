-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome (s : String) : Bool :=
sorry

def isPalindromePair (s1 s2 : String) : Bool :=
sorry

def palindromePairs (words : List String) : List (Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_pairs_valid_indices
  (words : List String) (result : List (Nat × Nat))
  (h : result = palindromePairs words) :
  ∀ pair, pair ∈ result →
    pair.1 < words.length ∧
    pair.2 < words.length ∧
    pair.1 ≠ pair.2 :=
sorry

theorem palindrome_pairs_forms_palindrome
  (words : List String) (result : List (Nat × Nat))
  (h : result = palindromePairs words) :
  ∀ pair, pair ∈ result →
    palindrome (words[pair.1]! ++ words[pair.2]!) :=
sorry

theorem palindrome_pairs_complete
  (words : List String) (result : List (Nat × Nat))
  (h : result = palindromePairs words) :
  ∀ i j, i < words.length → j < words.length → i ≠ j →
    palindrome (words[i]! ++ words[j]!) →
    (i,j) ∈ result :=
sorry

theorem palindrome_pairs_unique
  (words : List String) (result : List (Nat × Nat))
  (h : result = palindromePairs words) :
  ∀ p1 p2, p1 ∈ result → p2 ∈ result → p1 = p2 ∨ p1.1 ≠ p2.1 ∨ p1.2 ≠ p2.2 :=
sorry
-- </vc-theorems>