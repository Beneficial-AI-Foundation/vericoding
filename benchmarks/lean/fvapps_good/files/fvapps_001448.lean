-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_string_chars (s : String) (n : Nat) (chars : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_chars_check {test_str chars_str : String} {n : Nat}
  (h1 : test_str.length > 0)
  (h2 : chars_str.length > 0) 
  (h3 : ∃ c ∈ test_str.data, c ∉ chars_str.data) :
  check_string_chars test_str test_str.length chars_str = 0 :=
sorry

theorem empty_string_check {chars : String}
  (h : chars.length > 0) :
  check_string_chars "" 0 chars = 1 := 
sorry

theorem empty_chars_check {s : String} 
  (h : s.length > 0) :
  check_string_chars s s.length "" = 0 :=
sorry
-- </vc-theorems>