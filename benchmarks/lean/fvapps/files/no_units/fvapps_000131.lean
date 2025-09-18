-- <vc-preamble>
def balanced_string (s : String) : Int := sorry

def has_equal_quarters (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_char (s : String) (c : Char) : Nat := sorry

theorem invalid_length_returns_negative {s : String} :
  (s.length % 4 ≠ 0) → balanced_string s = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_within_bounds {s : String} :
  balanced_string s ≠ -1 →
  0 ≤ balanced_string s ∧ balanced_string s ≤ s.length := sorry
-- </vc-theorems>