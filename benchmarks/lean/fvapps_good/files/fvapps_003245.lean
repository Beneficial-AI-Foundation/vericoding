-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_palindrome (s : String) : String := sorry

def is_palindrome (s : String) : Bool := sorry

-- Result should be palindrome and contain input as prefix
-- </vc-definitions>

-- <vc-theorems>
theorem build_palindrome_valid (s : String) (h : s.length > 0) :
  let result := build_palindrome s
  is_palindrome result ∧ result.startsWith s := sorry

-- Result length should be at most double input length  

theorem build_palindrome_minimal (s : String) (h : s.length > 0) :
  (build_palindrome s).length ≤ 2 * s.length := sorry

-- Already palindrome string should be unchanged

theorem build_palindrome_idempotent (s : String) (h₁ : s.length > 0) (h₂ : is_palindrome s) :
  build_palindrome s = s := sorry
-- </vc-theorems>