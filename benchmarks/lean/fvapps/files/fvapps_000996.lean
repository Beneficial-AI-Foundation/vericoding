-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def periodicPalindrome (n p : Nat) : String := sorry

def string_slice (s : String) (start len : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_for_small_period (n p : Nat) 
  (h1 : p ≤ 2) : periodicPalindrome n p = "impossible" := sorry

theorem output_length {n p : Nat} (result : String)
  (h : result = periodicPalindrome n p)
  (h1 : p > 2) :
  result.length = (n / p) * p := sorry

theorem is_periodic {n p : Nat} (result : String)
  (h : result = periodicPalindrome n p)
  (h1 : p > 2)
  (h2 : result.length ≥ p) :
  ∀ i, i + p ≤ result.length → 
    string_slice result i p = string_slice result 0 p := sorry

theorem period_is_palindrome {n p : Nat} (result : String)
  (h : result = periodicPalindrome n p)
  (h1 : p > 2) :
  string_slice result 0 p = String.mk (string_slice result 0 p).data.reverse := sorry

theorem uses_only_a_b {n p : Nat} (result : String)
  (h : result = periodicPalindrome n p)
  (h1 : p > 2)
  (c : Char) :
  c ∈ result.data → c = 'a' ∨ c = 'b' := sorry
-- </vc-theorems>