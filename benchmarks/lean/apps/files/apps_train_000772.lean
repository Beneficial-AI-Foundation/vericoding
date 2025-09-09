def count_possible_strings (n : Nat) (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

theorem count_possible_strings_short_input (n : Nat) (s : String) :
  n ≤ s.length → count_possible_strings n s = 0 :=
sorry

theorem count_possible_strings_long_input (n : Nat) (s : String) :
  n > s.length → count_possible_strings n s > 0 :=
sorry

theorem count_possible_strings_monotone_in_string_length (s : String) :
  let n := s.length + 2
  count_possible_strings n s > count_possible_strings n (s.append "a") :=
sorry

/-
info: 1326
-/
-- #guard_msgs in
-- #eval count_possible_strings 3 "a"

/-
info: 76
-/
-- #guard_msgs in
-- #eval count_possible_strings 3 "ab"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible