-- <vc-preamble>
def count_possible_strings (n : Nat) (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

theorem count_possible_strings_short_input (n : Nat) (s : String) :
  n ≤ s.length → count_possible_strings n s = 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_possible_strings_long_input (n : Nat) (s : String) :
  n > s.length → count_possible_strings n s > 0 :=
sorry

theorem count_possible_strings_monotone_in_string_length (s : String) :
  let n := s.length + 2
  count_possible_strings n s > count_possible_strings n (s.append "a") :=
sorry
-- </vc-theorems>