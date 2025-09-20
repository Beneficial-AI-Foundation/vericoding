-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_counter (s : String) (c : Char) : Nat := sorry

theorem string_counter_equals_manual_sum (s : String) (c : Char) :
  string_counter s c = (s.data.filter (· = c)).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_counter_empty (c : Char) : 
  string_counter "" c = 0 := sorry 

theorem string_counter_repeated (c : Char) (n : Nat) :
  string_counter (String.mk (List.replicate n c)) c = n := sorry

theorem string_counter_nonnegative (s : String) (c : Char) :
  string_counter s c ≥ 0 := sorry

theorem string_counter_absent_char (s : String) (c : Char) :
  s.data.all (· ≠ c) → string_counter s c = 0 := sorry
-- </vc-theorems>