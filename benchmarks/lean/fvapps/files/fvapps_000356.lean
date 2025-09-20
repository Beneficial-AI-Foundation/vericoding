-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique_letter_string (s : String) : Nat :=
sorry

def string_reverse (s : String) : String :=
sorry

def string_append_char (s : String) (c : Char) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_letter_string_positive (s : String) (h : s.length > 0) :
  unique_letter_string s > 0 :=
sorry

theorem unique_letter_string_reverse_invariant (s : String) (h : s.length > 0) :
  unique_letter_string s = unique_letter_string (string_reverse s) :=
sorry

theorem unique_letter_string_monotone (s : String) (h : s.length > 0)
  (h1 : 0 < s.length) :
  unique_letter_string (string_append_char s (s.get 0)) > unique_letter_string s :=
sorry

theorem unique_letter_string_bounded (s : String) (h : s.length > 0) :
  unique_letter_string s < 1000000007 :=
sorry

theorem unique_letter_string_single_char (s : String) (h : s.length = 1) :
  unique_letter_string s = 1 :=
sorry
-- </vc-theorems>