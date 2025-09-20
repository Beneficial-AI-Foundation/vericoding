-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_string_length (s : String) : Nat :=
  sorry

def reverseString (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_string_length_non_negative (s : String) (h : s.length > 0) :
  min_string_length s ≥ 0 :=
sorry

theorem min_string_length_upper_bound (s : String) (h : s.length > 0) :
  min_string_length s ≤ s.length :=
sorry

theorem min_string_length_same_char (s : String) (h : s.length > 0)
  (h' : ∀ (i j : String.Pos), s.get i = s.get j) :
  min_string_length s ≤ 1 :=
sorry

theorem min_string_length_palindrome (s : String) (h : s.length > 0) :
  min_string_length s = min_string_length (reverseString s) :=
sorry
-- </vc-theorems>