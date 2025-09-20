-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_string (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_digits_returns_length 
  (s : String)
  (h : ∀ c ∈ s.data, c.isUpper) :
  process_string s = s.length := by sorry

theorem single_digit
  (n : Nat)
  (h : n < 10) :
  process_string (toString n) = n := by sorry

theorem two_digits
  (n : Nat) 
  (h1 : n ≥ 10)
  (h2 : n < 100) :
  process_string (toString n) = n := by sorry

theorem many_digits
  (n : Nat)
  (h1 : n ≥ 100)
  (h2 : n < 10000) :
  process_string (toString n) = n := by sorry

theorem mixed_string
  (s : String)
  (n : Nat)
  (h1 : ∀ c ∈ s.data, c.isUpper)
  (h2 : n > 0)
  (h3 : n < 1000000) :
  process_string (s ++ toString n) = n := by sorry

theorem special_case :
  process_string "C0D3C43F" = 3943 := by sorry
-- </vc-theorems>