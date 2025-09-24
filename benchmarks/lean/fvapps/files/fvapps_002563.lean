-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prime_string (s : String) : Bool := sorry

theorem prime_string_empty_or_single {s : String} (h : s.length ≤ 1) :
  prime_string s = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_string_repeated {s : String} (h : s.length ≥ 1) :
  prime_string (s ++ s ++ s) = false := sorry

theorem prime_string_self_concat {s : String} (h : s.length ≥ 1) :
  prime_string s = true ↔ 
  ∀ (i : Nat), 0 < i → i < (s ++ s).length → 
    (s ++ s).data[i]! ≠ s.data[0]! := sorry

theorem prime_string_palindrome {s : String} 
  (h1 : s.length > 1)
  (h2 : ∀ (i : Nat), i < s.length → 
    s.data[i]! = s.data[s.length - 1 - i]!) :
  prime_string (s ++ s) = false := sorry
-- </vc-theorems>