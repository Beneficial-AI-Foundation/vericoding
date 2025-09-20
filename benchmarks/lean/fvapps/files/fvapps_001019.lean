-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestValidPrefix (s : String) : Nat :=
  sorry

def isValid (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative (s : String) :
  longestValidPrefix s ≥ 0 :=
sorry

theorem result_not_exceed_length (s : String) :
  longestValidPrefix s ≤ String.length s :=
sorry

theorem result_is_even (s : String) :
  longestValidPrefix s % 2 = 0 :=
sorry

theorem next_char_makes_invalid (s : String) :
  longestValidPrefix s < String.length s →
  let withNext := s.take (longestValidPrefix s + 1)
  ¬isValid withNext :=
sorry

theorem perfect_pairs_full_length (n : Nat) :
  let s := String.mk (List.append (List.replicate n '<') (List.replicate n '>'))
  longestValidPrefix s = 2 * n :=
sorry

theorem empty_string_zero :
  longestValidPrefix "" = 0 :=
sorry

theorem single_right_zero :
  longestValidPrefix ">" = 0 :=
sorry

theorem single_left_zero :
  longestValidPrefix "<" = 0 :=
sorry
-- </vc-theorems>